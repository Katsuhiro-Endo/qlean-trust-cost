import QLean.Generator.Analysis.QEncoding
import QLean.Circuits.Foundation.MultiControlledRotation
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2
import QLean.Circuits.Foundation.FiniteGateExport
import QLean.Circuits.Foundation.QubitBasisEncoding

/-!
# Finite preparation from sparse rational configuration amplitudes

This is a numerical gate generator, not a correspondence theorem.  A sparse
list is used so producing the gate word does not enumerate the complete Q
matrix or every legal configuration.  Repeated configuration entries are
summed before branch masses and signs are computed.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.FiniteRationalConfigurationPreparation

open ProbabilityGeneratorQProof
open VerifiedCircuitCore
open VerifiedCircuitCore.ControlledCircuitCompilerV2

structure SparseInitial (parameters : QParameters) where
  entries : List (QConfiguration parameters × ℚ)

/-- Canonical finite presentation of a rational scientific initial vector.
The proof path may enumerate its approved amplitude function here, while a
numerical caller may retain a sparse list. Both are consumed by the same
preparation constructor below; this adapter asserts no numerical accuracy. -/
noncomputable def SparseInitial.ofAmplitude {p : QParameters}
    (amplitude : QConfiguration p → ℚ) : SparseInitial p :=
  { entries := (Finset.univ.toList : List (QConfiguration p)).map
      fun configuration => (configuration, amplitude configuration) }

def SparseInitial.amplitude {p : QParameters}
    (input : SparseInitial p) (configuration : QConfiguration p) : ℚ :=
  (input.entries.map fun entry =>
    if entry.1 = configuration then entry.2 else 0).sum

/-- The proof-side finite presentation retains every approved initial
amplitude exactly.  This is an input-data equality, not a statement about
the numerical circuit's denotation. -/
theorem SparseInitial.amplitude_ofAmplitude {p : QParameters}
    (amplitude : QConfiguration p → ℚ)
    (configuration : QConfiguration p) :
    (SparseInitial.ofAmplitude amplitude).amplitude configuration =
      amplitude configuration := by
  classical
  simp [SparseInitial.amplitude, SparseInitial.ofAmplitude]

def SparseInitial.support {p : QParameters}
    (input : SparseInitial p) : List (QConfiguration p) :=
  (input.entries.map Prod.fst).eraseDups

def encodedBit {p : QParameters} (configuration : QConfiguration p)
    (position : Nat) : Bool :=
  if within : position < p.systemWidth then
    delimiterEncoding configuration ⟨position, within⟩
  else false

def matchesPrefix {p : QParameters} (configuration : QConfiguration p)
    (depth pattern : Nat) : Bool :=
  (List.range depth).all fun position =>
    encodedBit configuration position == pattern.testBit position

theorem matchesPrefix_succ {p : QParameters}
    (configuration : QConfiguration p) (depth pattern : Nat) :
    matchesPrefix configuration (depth + 1) pattern =
      (matchesPrefix configuration depth pattern &&
        (encodedBit configuration depth == pattern.testBit depth)) := by
  simp [matchesPrefix, List.range_succ, List.all_append]

/-- The little-endian number represented by the first `depth` delimiter
bits.  Its construction takes time proportional to `depth`, not `2^depth`.
The numerical path may thus enumerate only prefixes that occur in its sparse
initial list. -/
def prefixPattern {p : QParameters} (configuration : QConfiguration p)
    (depth : Nat) : Nat :=
  qubitBasisLittleEndianIndex depth fun bit =>
    encodedBit configuration bit.val

theorem prefixPattern_lt {p : QParameters}
    (configuration : QConfiguration p) (depth : Nat) :
    prefixPattern configuration depth < 2 ^ depth :=
  qubitBasisLittleEndianIndex_lt _

theorem prefixPattern_testBit {p : QParameters}
    (configuration : QConfiguration p) {depth : Nat} (bit : Fin depth) :
    (prefixPattern configuration depth).testBit bit.val =
      encodedBit configuration bit.val := by
  simp [prefixPattern]

theorem prefixPattern_full_injective {p : QParameters} :
    Function.Injective (fun configuration : QConfiguration p =>
      prefixPattern configuration p.systemWidth) := by
  intro left right equal
  apply delimiterEncoding_injective
  funext bit
  have atBit := congrArg (fun code : Nat => code.testBit bit.val) equal
  simpa [prefixPattern_testBit, encodedBit, bit.isLt] using atBit

theorem matchesPrefix_true_iff_prefixPattern {p : QParameters}
    (configuration : QConfiguration p) (depth pattern : Nat)
    (patternBound : pattern < 2 ^ depth) :
    matchesPrefix configuration depth pattern = true ↔
      pattern = prefixPattern configuration depth := by
  constructor
  · intro matched
    apply Nat.eq_of_testBit_eq
    intro bit
    by_cases inside : bit < depth
    · have clause := (List.all_eq_true.mp matched) bit
        (List.mem_range.mpr inside)
      have same : encodedBit configuration bit = pattern.testBit bit := by
        cases encoded : encodedBit configuration bit <;>
          cases coded : pattern.testBit bit <;>
          simp_all [matchesPrefix]
      calc
        pattern.testBit bit = encodedBit configuration bit := same.symm
        _ = (prefixPattern configuration depth).testBit bit :=
          (prefixPattern_testBit configuration ⟨bit, inside⟩).symm
    · have widthLe : depth ≤ bit := Nat.le_of_not_gt inside
      have patternAtBit : pattern < 2 ^ bit :=
        lt_of_lt_of_le patternBound
          (Nat.pow_le_pow_right (by decide) widthLe)
      have prefixAtBit : prefixPattern configuration depth < 2 ^ bit :=
        lt_of_lt_of_le (prefixPattern_lt configuration depth)
          (Nat.pow_le_pow_right (by decide) widthLe)
      rw [Nat.testBit_eq_false_of_lt patternAtBit,
        Nat.testBit_eq_false_of_lt prefixAtBit]
  · intro same
    subst pattern
    unfold matchesPrefix
    apply List.all_eq_true.mpr
    intro bit member
    have bitBound : bit < depth := List.mem_range.mp member
    rw [prefixPattern_testBit configuration ⟨bit, bitBound⟩]
    simp

/-- The active prefix list is bounded by the sparse support length even at
large physical data width. -/
def SparseInitial.activePatterns {p : QParameters}
    (input : SparseInitial p) (depth : Nat) : List Nat :=
  (input.support.map fun configuration =>
    prefixPattern configuration depth).eraseDups

theorem testBit_add_pow_of_lt (depth pattern position : Nat)
    (patternBound : pattern < 2 ^ depth) (positionBound : position < depth) :
    (pattern + 2 ^ depth).testBit position = pattern.testBit position := by
  rw [show pattern + 2 ^ depth = 2 ^ depth * 1 + pattern by ring]
  rw [Nat.testBit_two_pow_mul_add _ patternBound]
  simp [positionBound]

theorem testBit_add_pow_at (depth pattern : Nat)
    (patternBound : pattern < 2 ^ depth) :
    (pattern + 2 ^ depth).testBit depth = true := by
  rw [show pattern + 2 ^ depth = 2 ^ depth * 1 + pattern by ring]
  rw [Nat.testBit_two_pow_mul_add _ patternBound]
  simp

theorem matchesPrefix_add_pow {p : QParameters}
    (configuration : QConfiguration p) (depth pattern : Nat)
    (patternBound : pattern < 2 ^ depth) :
    matchesPrefix configuration depth (pattern + 2 ^ depth) =
      matchesPrefix configuration depth pattern := by
  unfold matchesPrefix
  have equalAll : ∀ positions : List Nat,
      (∀ position ∈ positions, position < depth) →
      positions.all (fun position =>
        encodedBit configuration position ==
          (pattern + 2 ^ depth).testBit position) =
      positions.all (fun position =>
        encodedBit configuration position == pattern.testBit position) := by
    intro positions within
    induction positions with
    | nil => rfl
    | cons position rest ih =>
        have positionBound : position < depth := within position (by simp)
        have restWithin : ∀ value ∈ rest, value < depth := by
          intro value member
          exact within value (by simp [member])
        simp only [List.all_cons]
        rw [testBit_add_pow_of_lt depth pattern position patternBound positionBound,
          ih restWithin]
  exact equalAll (List.range depth) (by
    intro position member
    exact List.mem_range.mp member)

theorem matchesPrefix_left_child {p : QParameters}
    (configuration : QConfiguration p) (depth pattern : Nat)
    (patternBound : pattern < 2 ^ depth) :
    matchesPrefix configuration (depth + 1) pattern =
      (matchesPrefix configuration depth pattern &&
        !encodedBit configuration depth) := by
  rw [matchesPrefix_succ, Nat.testBit_lt_two_pow patternBound]
  cases encodedBit configuration depth <;> simp

theorem matchesPrefix_right_child {p : QParameters}
    (configuration : QConfiguration p) (depth pattern : Nat)
    (patternBound : pattern < 2 ^ depth) :
    matchesPrefix configuration (depth + 1) (pattern + 2 ^ depth) =
      (matchesPrefix configuration depth pattern &&
        encodedBit configuration depth) := by
  rw [matchesPrefix_succ, matchesPrefix_add_pow configuration depth pattern
    patternBound, testBit_add_pow_at depth pattern patternBound]
  simp

def SparseInitial.branchMass {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat) : ℚ :=
  input.support.foldl
    (fun total configuration =>
      if matchesPrefix configuration depth pattern then
        total + (input.amplitude configuration) ^ 2
      else total) 0

/-- The existing computational accumulator equals a finite sum. The
preparation angles and emitted gate syntax are left unchanged. -/
theorem SparseInitial.branchMass_eq_sum {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat) :
    input.branchMass depth pattern =
      (input.support.map fun configuration =>
        if matchesPrefix configuration depth pattern then
          (input.amplitude configuration) ^ 2 else 0).sum := by
  let f : QConfiguration p → ℚ := fun configuration =>
    if matchesPrefix configuration depth pattern then
      (input.amplitude configuration) ^ 2 else 0
  have folds : ∀ configurations : List (QConfiguration p), ∀ total : ℚ,
      configurations.foldl (fun acc configuration => acc + f configuration) total =
        total + (configurations.map f).sum := by
    intro configurations
    induction configurations with
    | nil => intro total; simp
    | cons configuration rest ih =>
        intro total
        change rest.foldl (fun acc configuration => acc + f configuration)
            (total + f configuration) =
          total + (f configuration + (rest.map f).sum)
        rw [ih]
        ring
  have step :
      (fun total configuration =>
        if matchesPrefix configuration depth pattern then
          total + (input.amplitude configuration) ^ 2 else total) =
      (fun total configuration => total + f configuration) := by
    funext total configuration
    dsimp [f]
    split_ifs <;> simp
  change _ = (input.support.map f).sum
  rw [SparseInitial.branchMass, step, folds]
  simp

/-- An omitted sparse prefix has zero mass.  This is a property of the
finite input data used by the generator, not a numerical-output guarantee. -/
theorem SparseInitial.branchMass_eq_zero_of_not_mem_activePatterns
    {p : QParameters} (input : SparseInitial p) (depth pattern : Nat)
    (patternBound : pattern < 2 ^ depth)
    (absent : pattern ∉ input.activePatterns depth) :
    input.branchMass depth pattern = 0 := by
  rw [SparseInitial.branchMass_eq_sum]
  have noMatch : ∀ configuration ∈ input.support,
      matchesPrefix configuration depth pattern = false := by
    intro configuration member
    have present : prefixPattern configuration depth ∈ input.activePatterns depth := by
      simp only [SparseInitial.activePatterns, List.mem_eraseDups, List.mem_map]
      exact ⟨configuration, member, rfl⟩
    cases matched : matchesPrefix configuration depth pattern with
    | false => rfl
    | true =>
        have equal := (matchesPrefix_true_iff_prefixPattern
          configuration depth pattern patternBound).mp matched
        exact False.elim (absent (equal ▸ present))
  have mapZero :
      (input.support.map fun configuration =>
        if matchesPrefix configuration depth pattern then
          (input.amplitude configuration) ^ 2 else (0 : ℚ)) =
      input.support.map (fun _ => (0 : ℚ)) := by
    apply List.map_congr_left
    intro configuration member
    simp [noMatch configuration member]
  rw [mapZero]
  simp

/-- Every branch mass is nonnegative. This is an algebraic property of the
common preparation input, not a numerical-output accuracy certificate. -/
theorem SparseInitial.branchMass_nonneg {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat) :
    0 ≤ input.branchMass depth pattern := by
  rw [SparseInitial.branchMass_eq_sum]
  have nonnegSum : ∀ configurations : List (QConfiguration p),
      0 ≤ (configurations.map fun configuration =>
        if matchesPrefix configuration depth pattern then
          (input.amplitude configuration) ^ 2 else 0).sum := by
    intro configurations
    induction configurations with
    | nil => simp
    | cons configuration rest ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_nonneg (by split_ifs <;> positivity) ih
  exact nonnegSum input.support

/-- Refining a prefix cannot increase its mass. This supplies the interval
condition needed for the exact controlled-rotation angle on the theory path.
It does not assert anything about an external QSP phase word. -/
theorem SparseInitial.branchMass_succ_le {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat) :
    input.branchMass (depth + 1) pattern ≤ input.branchMass depth pattern := by
  rw [SparseInitial.branchMass_eq_sum, SparseInitial.branchMass_eq_sum]
  have each : ∀ configuration : QConfiguration p,
      (if matchesPrefix configuration (depth + 1) pattern then
        (input.amplitude configuration) ^ 2 else 0) ≤
      (if matchesPrefix configuration depth pattern then
        (input.amplitude configuration) ^ 2 else 0) := by
    intro configuration
    by_cases child : matchesPrefix configuration (depth + 1) pattern = true
    · have parent : matchesPrefix configuration depth pattern = true := by
        cases parentValue : matchesPrefix configuration depth pattern with
        | false => simp [matchesPrefix_succ, parentValue] at child
        | true => rfl
      simp [child, parent]
    · have childFalse : matchesPrefix configuration (depth + 1) pattern = false :=
        by
          cases childValue : matchesPrefix configuration (depth + 1) pattern with
          | false => rfl
          | true => exact False.elim (child childValue)
      simp [childFalse]
      split_ifs <;> positivity
  have sums : ∀ configurations : List (QConfiguration p),
      (configurations.map fun configuration =>
        if matchesPrefix configuration (depth + 1) pattern then
          (input.amplitude configuration) ^ 2 else 0).sum ≤
      (configurations.map fun configuration =>
        if matchesPrefix configuration depth pattern then
          (input.amplitude configuration) ^ 2 else 0).sum := by
    intro configurations
    induction configurations with
    | nil => simp
    | cons configuration rest ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add (each configuration) ih
  exact sums input.support

/-- The two next-bit branches partition a prefix mass.  In particular the
right-child mass used by a state-preparation proof is the parent mass minus
the left-child mass, with no assumption on the sparse input list. -/
theorem SparseInitial.branchMass_children {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat)
    (patternBound : pattern < 2 ^ depth) :
    input.branchMass (depth + 1) pattern +
      input.branchMass (depth + 1) (pattern + 2 ^ depth) =
        input.branchMass depth pattern := by
  rw [SparseInitial.branchMass_eq_sum, SparseInitial.branchMass_eq_sum,
    SparseInitial.branchMass_eq_sum]
  have each : ∀ configuration : QConfiguration p,
      (if matchesPrefix configuration (depth + 1) pattern then
        (input.amplitude configuration) ^ 2 else 0) +
      (if matchesPrefix configuration (depth + 1) (pattern + 2 ^ depth) then
        (input.amplitude configuration) ^ 2 else 0) =
      (if matchesPrefix configuration depth pattern then
        (input.amplitude configuration) ^ 2 else 0) := by
    intro configuration
    rw [matchesPrefix_left_child configuration depth pattern patternBound,
      matchesPrefix_right_child configuration depth pattern patternBound]
    cases parent : matchesPrefix configuration depth pattern <;>
      cases bit : encodedBit configuration depth <;> simp
  have sums : ∀ configurations : List (QConfiguration p),
      (configurations.map fun configuration =>
        if matchesPrefix configuration (depth + 1) pattern then
          (input.amplitude configuration) ^ 2 else 0).sum +
      (configurations.map fun configuration =>
        if matchesPrefix configuration (depth + 1) (pattern + 2 ^ depth) then
          (input.amplitude configuration) ^ 2 else 0).sum =
      (configurations.map fun configuration =>
        if matchesPrefix configuration depth pattern then
          (input.amplitude configuration) ^ 2 else 0).sum := by
    intro configurations
    induction configurations with
    | nil => simp
    | cons configuration rest ih =>
        simp only [List.map_cons, List.sum_cons]
        calc
          _ =
              ((if matchesPrefix configuration (depth + 1) pattern then
                  (input.amplitude configuration) ^ 2 else 0) +
               (if matchesPrefix configuration (depth + 1) (pattern + 2 ^ depth)
                then (input.amplitude configuration) ^ 2 else 0)) +
              ((rest.map fun configuration =>
                  if matchesPrefix configuration (depth + 1) pattern then
                    (input.amplitude configuration) ^ 2 else 0).sum +
               (rest.map fun configuration =>
                  if matchesPrefix configuration (depth + 1) (pattern + 2 ^ depth)
                  then (input.amplitude configuration) ^ 2 else 0).sum) := by
                ring
          _ = _ := by rw [each configuration, ih]
  exact sums input.support

theorem SparseInitial.branchMass_children_zero_of_parent_zero {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat)
    (patternBound : pattern < 2 ^ depth)
    (parentZero : input.branchMass depth pattern = 0) :
    input.branchMass (depth + 1) pattern = 0 ∧
      input.branchMass (depth + 1) (pattern + 2 ^ depth) = 0 := by
  have partition := input.branchMass_children depth pattern patternBound
  have leftNonneg := input.branchMass_nonneg (depth + 1) pattern
  have rightNonneg := input.branchMass_nonneg (depth + 1)
    (pattern + 2 ^ depth)
  constructor <;> linarith

/-- The root of the prefix tree carries the squared mass of every distinct
configuration presented by the sparse input. -/
theorem SparseInitial.branchMass_root {p : QParameters}
    (input : SparseInitial p) :
    input.branchMass 0 0 =
      (input.support.map fun configuration =>
        (input.amplitude configuration) ^ 2).sum := by
  rw [SparseInitial.branchMass_eq_sum]
  simp [matchesPrefix]

/-- The theoretical finite presentation visits every configuration once. -/
theorem SparseInitial.support_ofAmplitude {p : QParameters}
    (amplitude : QConfiguration p → ℚ) :
    (SparseInitial.ofAmplitude amplitude).support =
      (Finset.univ.toList : List (QConfiguration p)) := by
  classical
  have eraseDups_of_nodup : ∀ configurations : List (QConfiguration p),
      configurations.Nodup → configurations.eraseDups = configurations := by
    intro configurations nodup
    induction configurations with
    | nil => rfl
    | cons configuration rest ih =>
        have separation := List.nodup_cons.mp nodup
        have filter_id :
            (rest.filter fun value => !value == configuration) = rest := by
          apply List.filter_eq_self.mpr
          intro value member
          have different : value ≠ configuration := by
            intro equal
            exact separation.1 (equal ▸ member)
          have coeDifferent : value.1 ≠ configuration.1 :=
            fun equal => different (Subtype.ext equal)
          simpa using coeDifferent
        rw [List.eraseDups_cons, filter_id, ih separation.2]
  simpa [SparseInitial.support, SparseInitial.ofAmplitude, List.map_map,
    Function.comp_def] using
    (eraseDups_of_nodup (Finset.univ.toList : List (QConfiguration p))
      (Finset.nodup_toList Finset.univ))

/-- The root mass of the theoretical adapter is exactly the squared mass of
its approved rational initial vector.  This does not certify an externally
supplied numerical phase program. -/
theorem SparseInitial.branchMass_root_ofAmplitude {p : QParameters}
    (amplitude : QConfiguration p → ℚ) :
    (SparseInitial.ofAmplitude amplitude).branchMass 0 0 =
      ∑ configuration : QConfiguration p, (amplitude configuration) ^ 2 := by
  classical
  rw [SparseInitial.branchMass_root, SparseInitial.support_ofAmplitude]
  simp [SparseInitial.amplitude_ofAmplitude]

/-- At a complete delimiter code the theoretical sparse presentation has
exactly one configuration, so its leaf mass is that amplitude squared. -/
theorem SparseInitial.branchMass_leaf_ofAmplitude {p : QParameters}
    (amplitude : QConfiguration p → ℚ)
    (configuration : QConfiguration p) :
    (SparseInitial.ofAmplitude amplitude).branchMass p.systemWidth
        (prefixPattern configuration p.systemWidth) =
      (amplitude configuration) ^ 2 := by
  classical
  have patternBound := prefixPattern_lt configuration p.systemWidth
  have ownMatch : matchesPrefix configuration p.systemWidth
      (prefixPattern configuration p.systemWidth) = true :=
    (matchesPrefix_true_iff_prefixPattern configuration p.systemWidth
      (prefixPattern configuration p.systemWidth) patternBound).mpr rfl
  calc
    _ = ∑ candidate : QConfiguration p,
          if matchesPrefix candidate p.systemWidth
              (prefixPattern configuration p.systemWidth) then
            (amplitude candidate) ^ 2 else 0 := by
          rw [SparseInitial.branchMass_eq_sum,
            SparseInitial.support_ofAmplitude]
          simp [SparseInitial.amplitude_ofAmplitude]
    _ = (amplitude configuration) ^ 2 := by
      have sumSingle :
          (∑ candidate : QConfiguration p,
            if matchesPrefix candidate p.systemWidth
                (prefixPattern configuration p.systemWidth) then
              (amplitude candidate) ^ 2 else 0) =
            (if matchesPrefix configuration p.systemWidth
                (prefixPattern configuration p.systemWidth) then
              (amplitude configuration) ^ 2 else 0) := by
        apply Finset.sum_eq_single configuration
        · intro candidate _ different
          have absent : matchesPrefix candidate p.systemWidth
              (prefixPattern configuration p.systemWidth) = false := by
            cases matched : matchesPrefix candidate p.systemWidth
                (prefixPattern configuration p.systemWidth) with
            | false => rfl
            | true =>
                have codeEqual :=
                  (matchesPrefix_true_iff_prefixPattern candidate p.systemWidth
                    (prefixPattern configuration p.systemWidth)
                    patternBound).mp matched
                exact False.elim (different
                  (prefixPattern_full_injective codeEqual.symm))
          simp [absent]
        · intro absent
          exact False.elim (absent (Finset.mem_univ configuration))
      simpa [ownMatch] using sumSingle

/-- The approved theoretical adapter has a nonempty root whenever its
scientific initial vector has a nonzero configuration amplitude. -/
theorem SparseInitial.branchMass_root_pos_ofAmplitude {p : QParameters}
    (amplitude : QConfiguration p → ℚ)
    (configuration : QConfiguration p)
    (nonzero : amplitude configuration ≠ 0) :
    0 < (SparseInitial.ofAmplitude amplitude).branchMass 0 0 := by
  rw [SparseInitial.branchMass_root_ofAmplitude]
  have termPos : 0 < amplitude configuration ^ 2 := by
    positivity
  have termLe : amplitude configuration ^ 2 ≤
      ∑ value : QConfiguration p, (amplitude value) ^ 2 := by
    exact Finset.single_le_sum (fun value _ => sq_nonneg _) (Finset.mem_univ _)
  exact lt_of_lt_of_le termPos termLe

def rationalAngle (value : ℚ) : AngleExpr :=
  .rational value.num value.den (by exact value.den_pos)

theorem rationalAngle_uniformValue (value : ℚ) :
    (rationalAngle value).uniformValue = (value : ℝ) := by
  simp [rationalAngle, AngleExpr.uniformValue, AngleExpr.eval, Rat.cast_def]

def SparseInitial.branchAngle {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat) : AngleExpr :=
  let parent := input.branchMass depth pattern
  if parent = 0 then rationalAngle 0
  else
    let left := input.branchMass (depth + 1) pattern
    .mul (rationalAngle 2)
      (.acos (.sqrt (.div (rationalAngle left) (rationalAngle parent))))

/-- On a nonempty parent branch, the emitted angle has exactly the intended
mass-ratio value. This is a local preparation fact for the theoretical
`bPlus` bridge, not a QSP or numerical-circuit accuracy theorem. -/
theorem SparseInitial.branchAngle_uniformValue_of_pos {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat)
    (parentPos : 0 < input.branchMass depth pattern) :
    (input.branchAngle depth pattern).uniformValue =
      2 * Real.arccos (Real.sqrt
        (((input.branchMass (depth + 1) pattern : ℚ) : ℝ) /
          ((input.branchMass depth pattern : ℚ) : ℝ))) := by
  simp [SparseInitial.branchAngle, ne_of_gt parentPos,
    AngleExpr.uniformValue, AngleExpr.eval, rationalAngle, Rat.cast_def]

theorem SparseInitial.cos_half_branchAngle {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat)
    (parentPos : 0 < input.branchMass depth pattern) :
    Real.cos ((input.branchAngle depth pattern).uniformValue / 2) =
      Real.sqrt
        (((input.branchMass (depth + 1) pattern : ℚ) : ℝ) /
          ((input.branchMass depth pattern : ℚ) : ℝ)) := by
  rw [input.branchAngle_uniformValue_of_pos depth pattern parentPos]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  apply Real.cos_arccos
  · exact le_trans (by norm_num) (Real.sqrt_nonneg _)
  · rw [Real.sqrt_le_one]
    have parentPositive :
        (0 : ℝ) < ((input.branchMass depth pattern : ℚ) : ℝ) := by
      exact_mod_cast parentPos
    rw [div_le_one parentPositive]
    exact_mod_cast input.branchMass_succ_le depth pattern

theorem SparseInitial.sin_half_branchAngle {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat)
    (parentPos : 0 < input.branchMass depth pattern) :
    Real.sin ((input.branchAngle depth pattern).uniformValue / 2) =
      Real.sqrt (1 -
        (((input.branchMass (depth + 1) pattern : ℚ) : ℝ) /
          ((input.branchMass depth pattern : ℚ) : ℝ))) := by
  rw [input.branchAngle_uniformValue_of_pos depth pattern parentPos]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.sin_arccos]
  congr 1
  have numeratorNonnegative :
      (0 : ℝ) ≤ ((input.branchMass (depth + 1) pattern : ℚ) : ℝ) := by
    exact_mod_cast input.branchMass_nonneg (depth + 1) pattern
  have denominatorPositive :
      (0 : ℝ) < ((input.branchMass depth pattern : ℚ) : ℝ) := by
    exact_mod_cast parentPos
  rw [Real.sq_sqrt
    (div_nonneg numeratorNonnegative (le_of_lt denominatorPositive))]

/-- The right-branch rotation weight is the square root of its own mass
ratio. This is the induction equation needed when the common preparer is
instantiated with the approved theoretical initial state. -/
theorem SparseInitial.sin_half_branchAngle_eq_right_mass {p : QParameters}
    (input : SparseInitial p) (depth pattern : Nat)
    (patternBound : pattern < 2 ^ depth)
    (parentPos : 0 < input.branchMass depth pattern) :
    Real.sin ((input.branchAngle depth pattern).uniformValue / 2) =
      Real.sqrt
        (((input.branchMass (depth + 1) (pattern + 2 ^ depth) : ℚ) : ℝ) /
          ((input.branchMass depth pattern : ℚ) : ℝ)) := by
  rw [input.sin_half_branchAngle depth pattern parentPos]
  congr 1
  have partition :
      ((input.branchMass (depth + 1) pattern : ℚ) : ℝ) +
        ((input.branchMass (depth + 1) (pattern + 2 ^ depth) : ℚ) : ℝ) =
          ((input.branchMass depth pattern : ℚ) : ℝ) := by
    exact_mod_cast input.branchMass_children depth pattern patternBound
  have denominatorPos :
      (0 : ℝ) < ((input.branchMass depth pattern : ℚ) : ℝ) := by
    exact_mod_cast parentPos
  field_simp [ne_of_gt denominatorPos]
  linarith

/-- A caller-independent finite wire placement.  The scientific builder below
chooses this placement from its history register rather than requiring the
numerical user to supply a prepared circuit. -/
structure PreparationPlacement (p : QParameters) (qubits : Nat) where
  data : Fin p.systemWidth → Fin qubits
  scratch : List (Fin qubits)
  phase : Fin qubits

def prefixControlsAt {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (depth : Fin p.systemWidth) (pattern : Nat) :
    List (Fin qubits × Bool) :=
  (List.finRange depth.val).map fun bit =>
    (placement.data ⟨bit.val, by omega⟩, pattern.testBit bit.val)

def configurationControlsAt {p : QParameters} {qubits : Nat}
    (placement : PreparationPlacement p qubits)
    (configuration : QConfiguration p) : List (Fin qubits × Bool) :=
  (List.finRange p.systemWidth).map fun bit =>
    (placement.data bit, delimiterEncoding configuration bit)

/-- Apply the same sparse configuration preparation only on the selected
history branch.  The all-zero extension branch is left untouched.  The
caller supplies a branch wire disjoint from the data and work placement. -/
def SparseInitial.circuitAtWhen {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) : Circuit (PrimitiveGate qubits) :=
  let magnitudes := Circuit.sequence <|
    (List.finRange p.systemWidth).map fun depth =>
      Circuit.sequence <|
        (input.activePatterns depth.val).map fun pattern =>
          Circuit.boolMultiControlledRy
            ((branch, true) :: prefixControlsAt placement depth pattern)
            placement.scratch (placement.data depth)
            (input.branchAngle depth.val pattern)
  let signs := Circuit.sequence <|
    (input.support.filter fun configuration => input.amplitude configuration < 0).map
      fun configuration =>
        Circuit.boolMultiControlledRy
          ((branch, true) :: configurationControlsAt placement configuration)
          placement.scratch placement.phase (.mul (rationalAngle 2) .pi)
  .seq magnitudes signs

/-- A finite bPlus preparation body. The branch Hadamard gives equal
extension/history weights; the configuration circuit acts only on the history
branch. The theoretical proof path still needs to be connected to this body
and proved correct against the independent bPlus state. No such claim is made
for numerical-provider output. -/
def SparseInitial.bPlusPreparation {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) : NormalizedCircuit qubits where
  circuit := .seq (.gate (.h branch)) (input.circuitAtWhen placement branch)
  normalized := by
    intro gate _
    cases gate <;> trivial

theorem SparseInitial.bPlusPreparation_circuit
    {p : QParameters} {qubits : Nat}
    (input : SparseInitial p) (placement : PreparationPlacement p qubits)
    (branch : Fin qubits) :
    (input.bPlusPreparation placement branch).circuit =
      .seq (.gate (.h branch)) (input.circuitAtWhen placement branch) := rfl

end QLean.Circuits.FiniteRationalConfigurationPreparation
