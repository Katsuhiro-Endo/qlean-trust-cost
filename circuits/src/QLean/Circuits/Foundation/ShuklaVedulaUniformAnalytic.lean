import QLean.Circuits.Foundation.ControlledCircuitCompilerAnalytic
import QLean.Circuits.Foundation.UniformPreparationAnalytic

/-!
# Width-only Shukla--Vedula uniform-preparation plan

This module records the source-order, width-only construction independently
of circuit syntax.  It is a distinct implementation family from the existing
`2 * width` selector-plus-scratch rotation-tree compiler, while sharing the
same independent uniform target state.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Finite wire interval in increasing little-endian order. -/
def widthOnlyWireInterval (width lower upper : Nat) : List (Fin width) :=
  (List.range' lower (upper - lower)).filterMap fun wire =>
    if inside : wire < width then some ⟨wire, inside⟩ else none

/-- An empty or reversed numeric interval contains no wires. -/
@[simp] theorem widthOnlyWireInterval_eq_nil_of_upper_le
    (width lower upper : Nat) (upperLe : upper ≤ lower) :
    widthOnlyWireInterval width lower upper = [] := by
  simp [widthOnlyWireInterval, Nat.sub_eq_zero_of_le upperLe]

/-- Under the width bound, the interval exposes its least wire followed by
the interval with incremented lower endpoint. -/
theorem widthOnlyWireInterval_cons
    (width lower upper : Nat) (lowerLt : lower < upper)
    (upperLeWidth : upper ≤ width) :
    widthOnlyWireInterval width lower upper =
      ⟨lower, lowerLt.trans_le upperLeWidth⟩ ::
        widthOnlyWireInterval width (lower + 1) upper := by
  have lengthStep : upper - lower = upper - (lower + 1) + 1 := by omega
  unfold widthOnlyWireInterval
  rw [lengthStep, List.range'_succ]
  simp only [List.filterMap_cons]
  simp only [show lower < width by omega, dite_true]

/-- Set-bit positions of a natural count in increasing order, truncated to
the declared register width. -/
def widthOnlyUniformOneLocations (width count : Nat) : List (Fin width) :=
  (List.finRange width).filter fun wire => count.testBit wire.val

/-- Under the strict capacity bound, every binary one-location is an actual
wire.  This typed view preserves the increasing `Nat.bitIndices` source order
without a later truncation argument. -/
def widthOnlyUniformOneLocationsOfStrictBound
    (width count : Nat) (strictBound : count < 2 ^ width) : List (Fin width) :=
  count.bitIndices.attach.map fun bit =>
    ⟨bit.1, by
      have powerLe : 2 ^ bit.1 ≤ count :=
        Nat.two_pow_le_of_mem_bitIndices bit.2
      by_contra notBelow
      have widthLe : width ≤ bit.1 := Nat.le_of_not_gt notBelow
      have powerMonotone : 2 ^ width ≤ 2 ^ bit.1 :=
        Nat.pow_le_pow_right (by decide) widthLe
      omega⟩

/-- Forgetting the Fin proofs in the strict-bound view recovers the canonical
increasing binary one-location list exactly. -/
@[simp] theorem widthOnlyUniformOneLocationsOfStrictBound_values
    (width count : Nat) (strictBound : count < 2 ^ width) :
    (widthOnlyUniformOneLocationsOfStrictBound width count strictBound).map
        Fin.val = count.bitIndices := by
  simp [widthOnlyUniformOneLocationsOfStrictBound]

/-- Exact half of a symbolic angle. -/
def AngleExpr.half (angle : AngleExpr) : AngleExpr :=
  .div angle (.rational 2 1 (by decide))

/-- Four-source-leaf decomposition of one controlled Ry. -/
def controlledRySourcePlan {width : Nat}
    (control target : Fin width) (angle : AngleExpr) :
    List (ExternallyControlledPrimitivePlan width) :=
  if different : control ≠ target then [
    .ry angle.half target,
    .cnot control target different,
    .ry (.neg angle.half) target,
    .cnot control target different]
  else []

/-- Seven-source-leaf controlled-H decomposition. -/
def controlledHadamardSourcePlan {width : Nat}
    (control target : Fin width) :
    List (ExternallyControlledPrimitivePlan width) :=
  if different : control ≠ target then [
    .h target,
    .cnot control target different,
    .h target,
    .ry controlledHadamardQuarterAngle target,
    .cnot control target different,
    .ry (.neg controlledHadamardQuarterAngle) target,
    .cnot control target different]
  else []

/-- A zero-controlled H is X-conjugation of the positive controlled-H source
decomposition. -/
def zeroControlledHadamardSourcePlan {width : Nat}
    (zeroControl target : Fin width) :
    List (ExternallyControlledPrimitivePlan width) :=
  [.x zeroControl] ++ controlledHadamardSourcePlan zeroControl target ++
    [.x zeroControl]

/-- A zero-controlled Ry is X-conjugation of the positive controlled-Ry
source decomposition. -/
def zeroControlledRySourcePlan {width : Nat}
    (zeroControl target : Fin width) (angle : AngleExpr) :
    List (ExternallyControlledPrimitivePlan width) :=
  [.x zeroControl] ++ controlledRySourcePlan zeroControl target angle ++
    [.x zeroControl]

/-- Negative Shukla--Vedula split angle
`-2 * arccos (sqrt (left / (left + right)))`. -/
def shuklaVedulaNegativeSplitAngle (left right : Nat) : AngleExpr :=
  .neg (uniformSplitAngle left right)

/-- The cosine coefficient of the negative split angle is the finalized-block
square-root ratio. -/
theorem cos_half_shuklaVedulaNegativeSplitAngle
    (left right : Nat) (positive : 0 < left + right) :
    Real.cos
        ((shuklaVedulaNegativeSplitAngle left right).uniformValue / 2) =
      Real.sqrt ((left : ℝ) / (left + right : ℝ)) := by
  rw [shuklaVedulaNegativeSplitAngle, AngleExpr.uniformValue,
    AngleExpr.eval_neg]
  rw [show -(uniformSplitAngle left right).eval (fun _ => 0) / 2 =
      -((uniformSplitAngle left right).eval (fun _ => 0) / 2) by ring,
    Real.cos_neg]
  exact cos_half_uniformSplitAngle (fun _ => 0) left right positive

/-- The sign already present in the local `Ry` action cancels the negative
split angle and yields the next-active-block square-root ratio. -/
theorem neg_sin_half_shuklaVedulaNegativeSplitAngle
    (left right : Nat) (positive : 0 < left + right) :
    -Real.sin
        ((shuklaVedulaNegativeSplitAngle left right).uniformValue / 2) =
      Real.sqrt ((right : ℝ) / (left + right : ℝ)) := by
  rw [shuklaVedulaNegativeSplitAngle, AngleExpr.uniformValue,
    AngleExpr.eval_neg]
  rw [show -(uniformSplitAngle left right).eval (fun _ => 0) / 2 =
      -((uniformSplitAngle left right).eval (fun _ => 0) / 2) by ring,
    Real.sin_neg, neg_neg]
  exact sin_half_uniformSplitAngle (fun _ => 0) left right positive

/-- The two reciprocal square-root ratios cancel for positive natural
arguments. -/
theorem sqrt_ratio_mul_sqrt_reverse
    (left total : Nat) (leftPositive : 0 < left)
    (totalPositive : 0 < total) :
    Real.sqrt ((left : ℝ) / total) *
        Real.sqrt ((total : ℝ) / left) = 1 := by
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ left),
    Real.sqrt_div (by positivity : (0 : ℝ) ≤ total)]
  have leftSqrtPositive : 0 < Real.sqrt (left : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast leftPositive)
  have totalSqrtPositive : 0 < Real.sqrt (total : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast totalPositive)
  field_simp

/-- Adjacent square-root ratios telescope through a positive middle and base
denominator. -/
theorem sqrt_ratio_mul_sqrt_ratio
    (part total base : Nat) (totalPositive : 0 < total)
    (basePositive : 0 < base) :
    Real.sqrt ((part : ℝ) / total) *
        Real.sqrt ((total : ℝ) / base) =
      Real.sqrt ((part : ℝ) / base) := by
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ part),
    Real.sqrt_div (by positivity : (0 : ℝ) ≤ total),
    Real.sqrt_div (by positivity : (0 : ℝ) ≤ part)]
  have totalSqrtPositive : 0 < Real.sqrt (total : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast totalPositive)
  have baseSqrtPositive : 0 < Real.sqrt (base : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast basePositive)
  field_simp

/-- The product of `gap` Hadamard normalizations turns a block normalized by
`left` into the same block normalized by `left * 2^gap`. -/
theorem inverseSqrtTwoPow_mul_sqrt_ratio
    (left right gap : Nat) (leftPositive : 0 < left) :
    (1 / Real.sqrt 2 : ℝ) ^ gap *
        Real.sqrt ((right : ℝ) / left) =
      Real.sqrt ((right : ℝ) / (left * 2 ^ gap : Nat)) := by
  have sqrtTwoPow :
      Real.sqrt ((2 : ℝ) ^ gap) = (Real.sqrt 2) ^ gap := by
    induction gap with
    | zero => simp
    | succ gap inductionHypothesis =>
        rw [pow_succ, Real.sqrt_mul (by positivity), inductionHypothesis,
          pow_succ]
  have leftSqrtPositive : 0 < Real.sqrt (left : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast leftPositive)
  have twoSqrtPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  calc
    (1 / Real.sqrt 2 : ℝ) ^ gap *
        Real.sqrt ((right : ℝ) / left) =
        (1 / (Real.sqrt 2) ^ gap) *
          (Real.sqrt (right : ℝ) / Real.sqrt (left : ℝ)) := by
      rw [one_div_pow, Real.sqrt_div (by positivity : (0 : ℝ) ≤ right)]
    _ = Real.sqrt (right : ℝ) /
        (Real.sqrt (left : ℝ) * (Real.sqrt 2) ^ gap) := by
      field_simp
    _ = Real.sqrt (right : ℝ) /
        Real.sqrt ((left * 2 ^ gap : Nat) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ left), sqrtTwoPow]
    _ = Real.sqrt ((right : ℝ) / (left * 2 ^ gap : Nat)) := by
      rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ right)]

/-- Repeated Hadamard normalization equals the inverse square root of the
corresponding power-of-two block size. -/
theorem inverseSqrtTwoPow_eq_inverseSqrt_pow (gap : Nat) :
    (1 / Real.sqrt 2 : ℝ) ^ gap =
      1 / Real.sqrt (2 ^ gap : Nat) := by
  have sqrtTwoPow :
      Real.sqrt ((2 : ℝ) ^ gap) = (Real.sqrt 2) ^ gap := by
    induction gap with
    | zero => simp
    | succ gap inductionHypothesis =>
        rw [pow_succ, Real.sqrt_mul (by positivity), inductionHypothesis,
          pow_succ]
  rw [one_div_pow]
  rw [show ((2 ^ gap : Nat) : ℝ) = (2 : ℝ) ^ gap by norm_cast,
    sqrtTwoPow]

/-- Normalizing a total-to-block square-root ratio by the total square root is
the inverse square root of the block. -/
theorem sqrt_total_div_block_div_sqrt_total
    (block total : Nat) (blockPositive : 0 < block)
    (totalPositive : 0 < total) :
    Real.sqrt ((total : ℝ) / block) / Real.sqrt total =
      1 / Real.sqrt block := by
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ total)]
  have blockSqrtPositive : 0 < Real.sqrt (block : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast blockPositive)
  have totalSqrtPositive : 0 < Real.sqrt (total : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast totalPositive)
  field_simp

/-- The finalized branch coefficient of one tail split is exactly the target
uniform amplitude factor. -/
theorem shuklaVedulaFinalizedCoefficient
    (left right validCount : Nat) (leftPositive : 0 < left)
    (totalPositive : 0 < left + right) :
    Real.cos
          ((shuklaVedulaNegativeSplitAngle left right).uniformValue / 2) *
        (Real.sqrt (((left + right : Nat) : ℝ) / left) /
          Real.sqrt validCount) =
      1 / Real.sqrt validCount := by
  rw [cos_half_shuklaVedulaNegativeSplitAngle left right totalPositive,
    ← Nat.cast_add]
  calc
    Real.sqrt ((left : ℝ) / (left + right : Nat)) *
        (Real.sqrt (((left + right : Nat) : ℝ) / left) /
          Real.sqrt validCount) =
        (Real.sqrt ((left : ℝ) / (left + right : Nat)) *
          Real.sqrt (((left + right : Nat) : ℝ) / left)) /
            Real.sqrt validCount := by ring
    _ = 1 / Real.sqrt validCount := by
      rw [sqrt_ratio_mul_sqrt_reverse left (left + right) leftPositive
        totalPositive]

/-- After the interval Hadamards, the active branch coefficient is normalized
by the next power-of-two block size. -/
theorem shuklaVedulaNextActiveCoefficient
    (left right gap validCount : Nat) (leftPositive : 0 < left)
    (totalPositive : 0 < left + right) :
    (1 / Real.sqrt 2 : ℝ) ^ gap *
        (-Real.sin
            ((shuklaVedulaNegativeSplitAngle left right).uniformValue / 2) *
          (Real.sqrt (((left + right : Nat) : ℝ) / left) /
            Real.sqrt validCount)) =
      Real.sqrt ((right : ℝ) / (left * 2 ^ gap : Nat)) /
        Real.sqrt validCount := by
  rw [neg_sin_half_shuklaVedulaNegativeSplitAngle left right totalPositive,
    ← Nat.cast_add]
  calc
    (1 / Real.sqrt 2 : ℝ) ^ gap *
        (Real.sqrt ((right : ℝ) / (left + right : Nat)) *
          (Real.sqrt (((left + right : Nat) : ℝ) / left) /
            Real.sqrt validCount)) =
        ((1 / Real.sqrt 2 : ℝ) ^ gap *
          (Real.sqrt ((right : ℝ) / (left + right : Nat)) *
            Real.sqrt (((left + right : Nat) : ℝ) / left))) /
              Real.sqrt validCount := by ring
    _ = ((1 / Real.sqrt 2 : ℝ) ^ gap *
          Real.sqrt ((right : ℝ) / left)) /
            Real.sqrt validCount := by
      rw [sqrt_ratio_mul_sqrt_ratio right (left + right) left totalPositive
        leftPositive]
    _ = Real.sqrt ((right : ℝ) / (left * 2 ^ gap : Nat)) /
          Real.sqrt validCount := by
      rw [inverseSqrtTwoPow_mul_sqrt_ratio left right gap leftPositive]

/-- Remaining source-order stages after the first two nonzero binary digits
of the count have been initialized. -/
def shuklaVedulaUniformTailPlan {width : Nat}
    (validCount accumulated : Nat) :
    List (Fin width) → List (ExternallyControlledPrimitivePlan width)
  | current :: next :: rest =>
      let block := 2 ^ current.val
      let remaining := validCount - accumulated
      let angle := shuklaVedulaNegativeSplitAngle block (remaining - block)
      zeroControlledRySourcePlan current next angle ++
        (widthOnlyWireInterval width current.val next.val).flatMap
          (zeroControlledHadamardSourcePlan next) ++
        shuklaVedulaUniformTailPlan validCount (accumulated + block)
          (next :: rest)
  | _ => []
termination_by locations => locations.length

/-- Width-only source-order Shukla--Vedula primitive plan.

* zero or one emitted set-bit gives the empty/power-of-two H prefix;
* two or more set bits follow the exact X/H/Ry/zero-control order of the
  standard source construction;
* every emitted leaf belongs to the externally controllable primitive family.
-/
def shuklaVedulaWidthOnlyUniformPlan
    (parameters : UniformPreparationParameters) :
    List (ExternallyControlledPrimitivePlan parameters.width) :=
  if full : parameters.validCount = 2 ^ parameters.width then
    (widthOnlyWireInterval parameters.width 0 parameters.width).map
      ExternallyControlledPrimitivePlan.h
  else
    let strictBound : parameters.validCount < 2 ^ parameters.width :=
      lt_of_le_of_ne parameters.validCountLeCapacity full
    match widthOnlyUniformOneLocationsOfStrictBound parameters.width
        parameters.validCount strictBound with
    | [] => []
    | [only] =>
        (widthOnlyWireInterval parameters.width 0 only.val).map
          ExternallyControlledPrimitivePlan.h
    | first :: second :: rest =>
        let firstBlock := 2 ^ first.val
        let initialAngle := shuklaVedulaNegativeSplitAngle firstBlock
          (parameters.validCount - firstBlock)
        (second :: rest).map ExternallyControlledPrimitivePlan.x ++
          (widthOnlyWireInterval parameters.width 0 first.val).map
            ExternallyControlledPrimitivePlan.h ++
          [.ry initialAngle second] ++
          (widthOnlyWireInterval parameters.width first.val second.val).flatMap
            (zeroControlledHadamardSourcePlan second) ++
          shuklaVedulaUniformTailPlan parameters.validCount firstBlock
            (second :: rest)

/-- The inverse source-order plan used by an externally controlled inverse
call. -/
def shuklaVedulaWidthOnlyUniformInversePlan
    (parameters : UniformPreparationParameters) :
    List (ExternallyControlledPrimitivePlan parameters.width) :=
  ExternallyControlledPrimitivePlan.inversePlan
    (shuklaVedulaWidthOnlyUniformPlan parameters)

/-- A local two-wire operator that applies `localOperator` exactly when the
control bit is zero. -/
def localZeroControlledOperator (localOperator : Matrix Bool Bool ℂ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun output input =>
    if output.1 ≠ input.1 then 0
    else if input.1 then
      if output.2 = input.2 then 1 else 0
    else localOperator output.2 input.2

/-- Independent arbitrary-width embedding of a zero-controlled local
one-wire operator. -/
def embedZeroControlledSingleQubitOperator {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ) : Operator (QubitBasis qubits) :=
  embedTwoQubitOperator control target different
    (localZeroControlledOperator localOperator)

/-- One aligned binary block in the width-only construction.  Wires below
`lower` are free; at and above `lower`, exactly the wires listed in `suffix`
are true. -/
structure ShuklaVedulaBlockSpec (width : Nat) where
  lower : Fin width
  suffix : List (Fin width)

/-- Direct basis predicate for one binary block. -/
def ShuklaVedulaBlockSpec.Matches {width : Nat}
    (spec : ShuklaVedulaBlockSpec width) (basis : QubitBasis width) : Prop :=
  ∀ wire, spec.lower.val ≤ wire.val →
    basis wire = decide (wire ∈ spec.suffix)

/-- A block predicate reads its lower wire as false when that wire is not in
the stored higher suffix. -/
theorem ShuklaVedulaBlockSpec.matches_lower_false {width : Nat}
    (spec : ShuklaVedulaBlockSpec width) (basis : QubitBasis width)
    (matching : spec.Matches basis) (lowerOutside : spec.lower ∉ spec.suffix) :
    basis spec.lower = false := by
  rw [matching spec.lower (Nat.le_refl _)]
  simp [lowerOutside]

/-- A listed suffix wire is true whenever it is at or above the free-block
boundary. -/
theorem ShuklaVedulaBlockSpec.matches_suffix_true {width : Nat}
    (spec : ShuklaVedulaBlockSpec width) (basis : QubitBasis width)
    (matching : spec.Matches basis) (wire : Fin width)
    (member : wire ∈ spec.suffix) (above : spec.lower.val ≤ wire.val) :
    basis wire = true := by
  rw [matching wire above]
  simp [member]

/-- Wires below a block boundary do not affect membership in that block. -/
theorem ShuklaVedulaBlockSpec.matches_update_below {width : Nat}
    (spec : ShuklaVedulaBlockSpec width) (basis : QubitBasis width)
    (target : Fin width) (value : Bool) (below : target.val < spec.lower.val) :
    spec.Matches (Function.update basis target value) ↔ spec.Matches basis := by
  constructor <;> intro matching wire above
  · have different : wire ≠ target := by
      intro equal
      subst wire
      omega
    simpa [Function.update, different] using matching wire above
  · have different : wire ≠ target := by
      intro equal
      subst wire
      omega
    simpa [Function.update, different] using matching wire above

/-- A binary block boundary may also equal `width`, in which case no wire is
fixed and the block is the whole basis.  This boundary form is convenient for
the full-capacity all-H branch. -/
structure ShuklaVedulaBoundaryBlockSpec (width : Nat) where
  boundary : Nat
  boundaryLe : boundary ≤ width
  suffix : List (Fin width)

/-- Wires below `boundary` are free; all wires at or above it are fixed to the
listed binary suffix. -/
def ShuklaVedulaBoundaryBlockSpec.Matches {width : Nat}
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (basis : QubitBasis width) : Prop :=
  ∀ wire, spec.boundary ≤ wire.val →
    basis wire = decide (wire ∈ spec.suffix)

/-- Constant-amplitude state supported on one suffix-defined binary block. -/
def shuklaVedulaBoundaryBlockState {width : Nat}
    (spec : ShuklaVedulaBoundaryBlockSpec width) (amplitude : ℂ) :
    State (QubitBasis width) := by
  classical
  exact fun basis => if spec.Matches basis then amplitude else 0

/-- Advancing a nonterminal boundary by one frees exactly the old boundary
wire and preserves the fixed higher suffix. -/
def ShuklaVedulaBoundaryBlockSpec.advance {width : Nat}
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (notTerminal : spec.boundary < width) :
    ShuklaVedulaBoundaryBlockSpec width where
  boundary := spec.boundary + 1
  boundaryLe := notTerminal
  suffix := spec.suffix

/-- Change only the fixed higher suffix of a boundary block. -/
def ShuklaVedulaBoundaryBlockSpec.withSuffix {width : Nat}
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (suffix : List (Fin width)) : ShuklaVedulaBoundaryBlockSpec width where
  boundary := spec.boundary
  boundaryLe := spec.boundaryLe
  suffix := suffix

/-- Change only the free-block boundary while retaining the fixed suffix. -/
def ShuklaVedulaBoundaryBlockSpec.withBoundary {width : Nat}
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (boundary : Nat) (boundaryLe : boundary ≤ width) :
    ShuklaVedulaBoundaryBlockSpec width where
  boundary := boundary
  boundaryLe := boundaryLe
  suffix := spec.suffix

/-- Sum of the binary block sizes carried by an increasing list of one-bit
locations. -/
def shuklaVedulaLocationPowerSum {width : Nat}
    (locations : List (Fin width)) : Nat :=
  (locations.map fun wire => 2 ^ wire.val).sum

/-- The binary one-locations of the power sum recover any strictly increasing
typed location list. -/
theorem shuklaVedulaLocationPowerSum_bitIndices {width : Nat}
    (locations : List (Fin width))
    (sorted : locations.Pairwise fun left right => left.val < right.val) :
    (shuklaVedulaLocationPowerSum locations).bitIndices =
      locations.map Fin.val := by
  unfold shuklaVedulaLocationPowerSum
  rw [show locations.map (fun wire => 2 ^ wire.val) =
      (locations.map Fin.val).map (fun value => 2 ^ value) by
    simp [List.map_map]]
  apply Nat.bitIndices_sum_map_two_pow
  rw [List.sortedLT_iff_pairwise]
  simpa only [List.pairwise_map] using sorted

/-- The attached strict-bound location view carries exactly the original
natural count as its binary power sum. -/
theorem shuklaVedulaLocationPowerSum_oneLocationsOfStrictBound
    (width count : Nat) (strictBound : count < 2 ^ width) :
    shuklaVedulaLocationPowerSum
        (widthOnlyUniformOneLocationsOfStrictBound width count strictBound) =
      count := by
  unfold shuklaVedulaLocationPowerSum
  calc
    ((widthOnlyUniformOneLocationsOfStrictBound width count strictBound).map
        (fun wire => 2 ^ wire.val)).sum =
        (((widthOnlyUniformOneLocationsOfStrictBound width count strictBound).map
          Fin.val).map (fun value => 2 ^ value)).sum := by
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro wire _
      rfl
    _ = (count.bitIndices.map fun value => 2 ^ value).sum := by
      rw [widthOnlyUniformOneLocationsOfStrictBound_values]
    _ = count := Nat.sum_map_two_pow_bitIndices count

/-- If every location is at or above `boundary`, the location power sum is a
multiple of `2^boundary`. -/
theorem shuklaVedulaLocationPowerSum_factor
    {width : Nat} (boundary : Nat) (locations : List (Fin width))
    (above : ∀ wire, wire ∈ locations → boundary ≤ wire.val) :
    shuklaVedulaLocationPowerSum locations =
      2 ^ boundary *
        (locations.map fun wire => 2 ^ (wire.val - boundary)).sum := by
  induction locations with
  | nil => simp [shuklaVedulaLocationPowerSum]
  | cons wire rest inductionHypothesis =>
      have wireAbove : boundary ≤ wire.val := above wire (by simp)
      have restAbove : ∀ item, item ∈ rest → boundary ≤ item.val := by
        intro item member
        exact above item (by simp [member])
      rw [show shuklaVedulaLocationPowerSum (wire :: rest) =
          2 ^ wire.val + shuklaVedulaLocationPowerSum rest by
        simp [shuklaVedulaLocationPowerSum]]
      rw [inductionHypothesis restAbove]
      simp only [List.map_cons, List.sum_cons]
      have powFactor :
          2 ^ wire.val = 2 ^ boundary * 2 ^ (wire.val - boundary) := by
        calc
          2 ^ wire.val = 2 ^ (boundary + (wire.val - boundary)) := by
            congr 1
            omega
          _ = 2 ^ boundary * 2 ^ (wire.val - boundary) := by rw [pow_add]
      rw [powFactor]
      ring

/-- The aligned block whose free low wires stop at `current` and whose fixed
higher one-bits are exactly `rest`. -/
def shuklaVedulaLocationBlockSpec {width : Nat}
    (current : Fin width) (rest : List (Fin width)) :
    ShuklaVedulaBoundaryBlockSpec width where
  boundary := current.val
  boundaryLe := current.isLt.le
  suffix := rest

/-- Disjoint binary-block presentation of the uniform state carried by an
increasing list of one-bit locations. -/
def shuklaVedulaUniformBlockSum {width validCount : Nat} :
    List (Fin width) → State (QubitBasis width)
  | [] => 0
  | current :: rest =>
      shuklaVedulaBoundaryBlockState
          (shuklaVedulaLocationBlockSpec current rest)
          ((1 / Real.sqrt validCount : ℝ) : ℂ) +
        shuklaVedulaUniformBlockSum (validCount := validCount) rest

/-- Computational basis whose true wires are exactly `locations`. -/
def shuklaVedulaSuffixBasis {width : Nat}
    (locations : List (Fin width)) : QubitBasis width :=
  fun wire => decide (wire ∈ locations)

/-- Boundary-zero block fixing the entire register to one exactly on the
listed suffix wires. -/
def shuklaVedulaZeroBoundaryBlockSpec {width : Nat}
    (locations : List (Fin width)) : ShuklaVedulaBoundaryBlockSpec width where
  boundary := 0
  boundaryLe := Nat.zero_le width
  suffix := locations

/-- A source-order list of distinct X actions toggles exactly its listed
wires. -/
theorem foldl_xorWire_true_eq {width : Nat}
    (locations : List (Fin width)) (nodup : locations.Nodup)
    (input : QubitBasis width) :
    locations.foldl (fun state wire => xorWire wire true state) input =
      fun wire => input wire != decide (wire ∈ locations) := by
  induction locations generalizing input with
  | nil => simp
  | cons head rest inductionHypothesis =>
      have headOutside : head ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      rw [List.foldl_cons, inductionHypothesis restNodup]
      funext wire
      by_cases equal : wire = head
      · subst wire
        simp [xorWire, headOutside]
      · simp [xorWire, equal]

/-- Applying the distinct source-order X actions to the all-zero basis gives
the suffix basis. -/
theorem foldl_xorWire_true_zero_eq_suffixBasis {width : Nat}
    (locations : List (Fin width)) (nodup : locations.Nodup) :
    locations.foldl (fun state wire => xorWire wire true state)
        (fun _ => false) =
      shuklaVedulaSuffixBasis locations := by
  rw [foldl_xorWire_true_eq locations nodup]
  funext wire
  simp [shuklaVedulaSuffixBasis]

/-- State invariant after some low binary blocks have been finalized.

Writing `remaining = validCount - accumulated` and `block = 2^current`,
the already-finalized interval `[remaining, validCount)` has the final
amplitude.  The active interval `[remaining - block, remaining)` carries the
remaining norm and is ready for the next zero-controlled split. -/
def shuklaVedulaIntermediateState
    (parameters : UniformPreparationParameters)
    (accumulated : Nat) (current : Fin parameters.width) :
    State (QubitBasis parameters.width) :=
  fun basis =>
    let index := qubitBasisLittleEndianIndex parameters.width basis
    let remaining := parameters.validCount - accumulated
    let block := 2 ^ current.val
    if remaining ≤ index ∧ index < parameters.validCount then
      (1 / Real.sqrt parameters.validCount : ℂ)
    else if remaining - block ≤ index ∧ index < remaining then
      ((Real.sqrt ((remaining : ℝ) / (block : ℝ)) /
        Real.sqrt parameters.validCount : ℝ) : ℂ)
    else 0

/-- When the active block exhausts the remaining count, the invariant is
exactly the independent uniform target state. -/
theorem shuklaVedulaIntermediateState_eq_uniformTarget_of_remaining_eq_block
    (parameters : UniformPreparationParameters)
    (accumulated : Nat) (current : Fin parameters.width)
    (remainingEq : parameters.validCount - accumulated = 2 ^ current.val) :
    shuklaVedulaIntermediateState parameters accumulated current =
      uniformPreparationTargetState parameters := by
  funext basis
  let index := qubitBasisLittleEndianIndex parameters.width basis
  let block := 2 ^ current.val
  have remainingEqBlock :
      parameters.validCount - accumulated = block := by
    simpa [block] using remainingEq
  have blockPositive : (0 : ℝ) < block := by
    exact_mod_cast (pow_pos (by omega : 0 < (2 : Nat)) current.val)
  have blockLeValidCount : block ≤ parameters.validCount := by
    rw [← remainingEqBlock]
    exact Nat.sub_le _ _
  have activeAmplitude :
      Real.sqrt ((block : ℝ) / (block : ℝ)) /
        Real.sqrt parameters.validCount =
      1 / Real.sqrt parameters.validCount := by
    norm_num [ne_of_gt blockPositive]
  unfold shuklaVedulaIntermediateState uniformPreparationTargetState
  change (if parameters.validCount - accumulated ≤ index ∧
      index < parameters.validCount then _
    else if parameters.validCount - accumulated - block ≤ index ∧
      index < parameters.validCount - accumulated then _ else _) =
    (if index < parameters.validCount then _ else _)
  rw [remainingEqBlock]
  by_cases inTarget : index < parameters.validCount
  · rw [if_pos inTarget]
    by_cases finalized : block ≤ index
    · rw [if_pos ⟨finalized, inTarget⟩]
      norm_cast
    · have active : block - block ≤ index ∧ index < block := by
        exact ⟨by omega, Nat.lt_of_not_ge finalized⟩
      have notFinalized : ¬(block ≤ index ∧ index < parameters.validCount) :=
        fun pair => finalized pair.1
      rw [if_neg notFinalized, if_pos active]
      exact_mod_cast (show
        Real.sqrt ((block : ℝ) / ((2 ^ current.val : Nat) : ℝ)) /
            Real.sqrt parameters.validCount =
          1 / Real.sqrt parameters.validCount by
        rw [show (2 ^ current.val : Nat) = block by rfl]
        exact activeAmplitude)
  · have notFinalized : ¬(block ≤ index ∧ index < parameters.validCount) :=
      fun pair => inTarget pair.2
    have notActive : ¬(block - block ≤ index ∧ index < block) := by
      intro active
      apply inTarget
      exact active.2.trans_le blockLeValidCount
    rw [if_neg notFinalized, if_neg notActive, if_neg inTarget]

end

end VerifiedCircuitCore
