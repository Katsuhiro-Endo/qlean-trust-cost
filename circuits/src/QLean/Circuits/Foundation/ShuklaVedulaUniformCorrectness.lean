import QLean.Circuits.Foundation.ShuklaVedulaUniform
import QLean.Circuits.Foundation.UniformPreparationCorrectness

/-!
# Width-only Shukla--Vedula state semantics

This module proves the state-level transport from the source-faithful strict
operator to the independent uniform target.  The first reusable boundary
reduces an arbitrary-width embedded local action to its two local input bits.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Conjugating a positive local control by `X` on the control wire changes
the condition from one to zero.  This is a fixed two-wire identity; all
arbitrary-width results below use it only through the embedding homomorphism.
-/
theorem localOnControlX_mul_localControlled_mul_localOnControlX
    (localOperator : Matrix Bool Bool ℂ) :
    localOnControl localX * localControlledOperator localOperator *
        localOnControl localX =
      localZeroControlledOperator localOperator := by
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  fin_cases outputControl <;> fin_cases outputTarget <;>
    fin_cases inputControl <;> fin_cases inputTarget <;>
    simp [localOnControl, localX, localControlledOperator,
      localZeroControlledOperator, Matrix.mul_apply, Fintype.sum_prod_type]

/-- The source-order four-leaf decomposition has the direct controlled-Ry
operator semantics. -/
theorem sourcePlanOperator_controlledRySourcePlan
    {width : Nat} (control target : Fin width) (different : control ≠ target)
    (angle : AngleExpr) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledRySourcePlan control target angle) =
      embedControlledSingleQubitOperator control target different
        (localRy angle.uniformValue) := by
  calc
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledRySourcePlan control target angle) =
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.controlledRyMacroExpansion control target different angle) := by
      unfold Circuit.controlledRyMacroExpansion
      rw [Circuit.denote_fromList_eq_operatorSequence]
      simp [controlledRySourcePlan, different,
        ExternallyControlledPrimitivePlan.sourcePlanOperator,
        ExternallyControlledPrimitivePlan.sourceOperator,
        primitiveGateOperatorWithSymbols, AngleExpr.half, Circuit.halfAngle,
        AngleExpr.eval, reversibleAnalyticCnotOperator]
    _ = embedControlledSingleQubitOperator control target different
        (localRy angle.uniformValue) :=
      Circuit.controlledRyMacroExpansion_operator control target different angle

/-- The source-order seven-leaf decomposition has the direct controlled-H
operator semantics. -/
theorem sourcePlanOperator_controlledHadamardSourcePlan
    {width : Nat} (control target : Fin width) (different : control ≠ target) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledHadamardSourcePlan control target) =
      embedControlledSingleQubitOperator control target different localH := by
  let spec : ControlledHadamardSpecialAngleSpec width :=
    { control := control, target := target, different := different }
  calc
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledHadamardSourcePlan control target) =
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (controlledHadamardSpecialAngleCircuit spec) := by
      rw [controlledHadamardSpecialAngleCircuit,
        controlledRyZSevenGateCircuit, controlledHadamardSevenGateCircuit,
        Circuit.denote_fromList_eq_operatorSequence]
      simp [controlledHadamardSourcePlan, spec,
        ExternallyControlledPrimitivePlan.sourcePlanOperator,
        ExternallyControlledPrimitivePlan.sourceOperator,
        primitiveGateOperatorWithSymbols,
        reversibleAnalyticCnotOperator,
        ControlledHadamardSpecialAngleSpec.toRyZ,
        controlledHadamardQuarterAngle, different]
    _ = controlledHadamardSpecialAngleOperator spec :=
      (controlledHadamardSpecialAngleExactOperatorComponent
        (fun _ => 0) spec).correct
    _ = embedControlledSingleQubitOperator control target different localH := rfl

/-- The zero-controlled Ry source stream is exactly the direct zero-control
embedding. -/
theorem sourcePlanOperator_zeroControlledRySourcePlan
    {width : Nat} (control target : Fin width) (different : control ≠ target)
    (angle : AngleExpr) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (zeroControlledRySourcePlan control target angle) =
      embedZeroControlledSingleQubitOperator control target different
        (localRy angle.uniformValue) := by
  rw [zeroControlledRySourcePlan,
    ExternallyControlledPrimitivePlan.sourcePlanOperator, List.map_append,
    operatorSequence_append, List.map_append, operatorSequence_append]
  simp only [List.map_singleton, operatorSequence,
    ExternallyControlledPrimitivePlan.sourceOperator, Matrix.one_mul]
  change embedSingleQubitOperator control localX *
      (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledRySourcePlan control target angle) *
        embedSingleQubitOperator control localX) = _
  rw [sourcePlanOperator_controlledRySourcePlan control target different angle,
    ← mul_assoc]
  rw [← embedTwoQubitOperator_localOnControl control target different localX]
  unfold embedControlledSingleQubitOperator
  rw [← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul]
  exact congrArg (embedTwoQubitOperator control target different)
    (localOnControlX_mul_localControlled_mul_localOnControlX
      (localRy angle.uniformValue))

/-- The zero-controlled H source stream is exactly the direct zero-control
embedding. -/
theorem sourcePlanOperator_zeroControlledHadamardSourcePlan
    {width : Nat} (control target : Fin width) (different : control ≠ target) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (zeroControlledHadamardSourcePlan control target) =
      embedZeroControlledSingleQubitOperator control target different localH := by
  rw [zeroControlledHadamardSourcePlan,
    ExternallyControlledPrimitivePlan.sourcePlanOperator, List.map_append,
    operatorSequence_append, List.map_append, operatorSequence_append]
  simp only [List.map_singleton, operatorSequence,
    ExternallyControlledPrimitivePlan.sourceOperator, Matrix.one_mul]
  change embedSingleQubitOperator control localX *
      (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledHadamardSourcePlan control target) *
        embedSingleQubitOperator control localX) = _
  rw [sourcePlanOperator_controlledHadamardSourcePlan control target different,
    ← mul_assoc]
  rw [← embedTwoQubitOperator_localOnControl control target different localX]
  unfold embedControlledSingleQubitOperator
  rw [← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul]
  exact congrArg (embedTwoQubitOperator control target different)
    (localOnControlX_mul_localControlled_mul_localOnControlX localH)

/-- Source-plan products split across append in execution order. -/
theorem ExternallyControlledPrimitivePlan.sourcePlanOperator_append
    {width : Nat} (symbolValue : String → ℝ)
    (first second : List (ExternallyControlledPrimitivePlan width)) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator symbolValue
        (first ++ second) =
      ExternallyControlledPrimitivePlan.sourcePlanOperator symbolValue second *
        ExternallyControlledPrimitivePlan.sourcePlanOperator symbolValue first := by
  simp [ExternallyControlledPrimitivePlan.sourcePlanOperator,
    List.map_append, operatorSequence_append]

/-- A source-order list of X leaves is the deterministic fold of the direct
wire-XOR actions. -/
theorem sourcePlanOperator_x_map {width : Nat}
    (locations : List (Fin width)) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (locations.map ExternallyControlledPrimitivePlan.x) =
      deterministicOperator fun input =>
        locations.foldl (fun state wire => xorWire wire true state) input := by
  have leafOperator (wire : Fin width) :
      ExternallyControlledPrimitivePlan.sourceOperator (fun _ => 0)
          (.x wire) =
        deterministicOperator (xorWire wire true) := by
    change primitiveGateOperatorWithSymbols (fun _ => 0) (.x wire) = _
    exact primitiveXOperator_eq_deterministicOperator (fun _ => 0) wire
  unfold ExternallyControlledPrimitivePlan.sourcePlanOperator
  have mappedOperators :
      (locations.map ExternallyControlledPrimitivePlan.x).map
          (ExternallyControlledPrimitivePlan.sourceOperator (fun _ => 0)) =
        (locations.map fun wire => xorWire wire true).map
          deterministicOperator := by
    induction locations with
    | nil => rfl
    | cons head rest inductionHypothesis =>
        simp only [List.map_cons]
        rw [leafOperator, inductionHypothesis]
  have foldMapped (input : QubitBasis width) :
      (locations.map fun wire => xorWire wire true).foldl
          (fun state action => action state) input =
        locations.foldl (fun state wire => xorWire wire true state) input := by
    clear mappedOperators leafOperator
    induction locations generalizing input with
    | nil => rfl
    | cons head rest inductionHypothesis =>
        simp only [List.map_cons, List.foldl_cons]
        exact inductionHypothesis (xorWire head true input)
  rw [mappedOperators, operatorSequence_deterministicOperator]
  congr 1
  funext input
  exact foldMapped input

/-- The source-order X prefix maps the all-zero ket to the basis fixed by its
distinct location list. -/
theorem applyOperator_sourcePlanOperator_x_map_zeroKet
    {width : Nat} (locations : List (Fin width)) (nodup : locations.Nodup) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          (locations.map ExternallyControlledPrimitivePlan.x))
        (basisKet (fun _ => false : QubitBasis width)) =
      basisKet (shuklaVedulaSuffixBasis locations) := by
  rw [sourcePlanOperator_x_map, applyOperator_deterministicOperator_basisKet,
    foldl_xorWire_true_zero_eq_suffixBasis locations nodup]

/-- A boundary-zero singleton block state is exactly its suffix basis ket. -/
theorem shuklaVedulaBoundaryBlockState_zeroBoundary_eq_basisKet
    {width : Nat} (locations : List (Fin width)) :
    shuklaVedulaBoundaryBlockState
        (shuklaVedulaZeroBoundaryBlockSpec locations) 1 =
      basisKet (shuklaVedulaSuffixBasis locations) := by
  funext basis
  by_cases equal : basis = shuklaVedulaSuffixBasis locations
  · have matching :
        (shuklaVedulaZeroBoundaryBlockSpec locations).Matches basis := by
      intro wire _
      rw [equal]
      rfl
    subst basis
    simp [shuklaVedulaBoundaryBlockState, basisKet, matching]
  · have notMatching :
        ¬(shuklaVedulaZeroBoundaryBlockSpec locations).Matches basis := by
      intro matching
      apply equal
      funext wire
      exact matching wire (Nat.zero_le _)
    simp [shuklaVedulaBoundaryBlockState, basisKet, equal, notMatching]

/-- Combining the preceding two facts presents the X prefix result directly
as a boundary block state. -/
theorem applyOperator_sourcePlanOperator_x_map_zeroKet_eq_blockState
    {width : Nat} (locations : List (Fin width)) (nodup : locations.Nodup) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          (locations.map ExternallyControlledPrimitivePlan.x))
        (basisKet (fun _ => false : QubitBasis width)) =
      shuklaVedulaBoundaryBlockState
        (shuklaVedulaZeroBoundaryBlockSpec locations) 1 := by
  rw [applyOperator_sourcePlanOperator_x_map_zeroKet locations nodup,
    shuklaVedulaBoundaryBlockState_zeroBoundary_eq_basisKet]

/-- Applying an embedded one-wire operator to an arbitrary state is exactly
the two-term local input-bit sum. -/
theorem applyOperator_embedSingleQubitOperator_state
    {qubits : Nat} (target : Fin qubits)
    (localOperator : Matrix Bool Bool ℂ)
    (state : State (QubitBasis qubits)) (output : QubitBasis qubits) :
    applyOperator (embedSingleQubitOperator target localOperator) state output =
      ∑ inputBit : Bool,
        localOperator (output target) inputBit *
          state (replaceQubitWire output target inputBit) := by
  unfold applyOperator Matrix.mulVec dotProduct
  change (∑ input,
      embedSingleQubitOperator target localOperator output input *
        state input) = _
  rw [show (∑ input,
      embedSingleQubitOperator target localOperator output input * state input) =
        ∑ pair : Bool × ({wire : Fin qubits // wire ≠ target} → Bool),
          embedSingleQubitOperator target localOperator output
              ((splitWireEquiv target).symm pair) *
            state ((splitWireEquiv target).symm pair) by
    exact ((splitWireEquiv target).symm.sum_comp fun input =>
      embedSingleQubitOperator target localOperator output input *
        state input).symm]
  simp_rw [Fintype.sum_prod_type]
  simp [embedSingleQubitOperator_apply,
    agreesExcept_splitWireEquiv_symm_iff, splitWireEquiv_symm_target,
    ← replaceQubitWire_eq_splitWireEquiv_symm]

/-- Setting a zero little-endian wire adds exactly its binary place value. -/
theorem qubitBasisLittleEndianIndex_replace_true_of_false
    {qubits : Nat} (basis : QubitBasis qubits) (target : Fin qubits)
    (targetFalse : basis target = false) :
    qubitBasisLittleEndianIndex qubits
        (replaceQubitWire basis target true) =
      qubitBasisLittleEndianIndex qubits basis + 2 ^ target.val := by
  induction qubits with
  | zero => exact Fin.elim0 target
  | succ qubits inductionHypothesis =>
      revert targetFalse
      refine Fin.cases ?_ (fun inner => ?_) target
      · intro targetFalse
        have headFalse : basis 0 = false := by simpa using targetFalse
        simp [qubitBasisLittleEndianIndex, replaceQubitWire, headFalse,
          Nat.bit]
      · intro targetFalse
        let tail : QubitBasis qubits := fun wire => basis wire.succ
        have tailFalse : tail inner = false := by
          simpa [tail] using targetFalse
        have tailIndex := inductionHypothesis tail inner tailFalse
        have headPreserved :
            replaceQubitWire basis inner.succ true 0 = basis 0 := by
          exact replaceQubitWire_outside basis inner.succ 0 true
            (Ne.symm (Fin.succ_ne_zero inner))
        have tailReplaced :
            (fun wire =>
              replaceQubitWire basis inner.succ true wire.succ) =
              replaceQubitWire tail inner true := by
          funext wire
          simp [replaceQubitWire, tail]
        simp only [qubitBasisLittleEndianIndex]
        rw [headPreserved, tailReplaced, tailIndex]
        simp [Nat.bit, Nat.pow_succ]
        simp only [tail]
        cases basis 0 <;> simp <;> omega

/-- Clearing a one little-endian wire removes exactly its binary place value. -/
theorem qubitBasisLittleEndianIndex_replace_false_of_true
    {qubits : Nat} (basis : QubitBasis qubits) (target : Fin qubits)
    (targetTrue : basis target = true) :
    qubitBasisLittleEndianIndex qubits basis =
      qubitBasisLittleEndianIndex qubits
          (replaceQubitWire basis target false) +
        2 ^ target.val := by
  induction qubits with
  | zero => exact Fin.elim0 target
  | succ qubits inductionHypothesis =>
      revert targetTrue
      refine Fin.cases ?_ (fun inner => ?_) target
      · intro targetTrue
        have headTrue : basis 0 = true := by simpa using targetTrue
        simp [qubitBasisLittleEndianIndex, replaceQubitWire, headTrue,
          Nat.bit]
      · intro targetTrue
        let tail : QubitBasis qubits := fun wire => basis wire.succ
        have tailTrue : tail inner = true := by
          simpa [tail] using targetTrue
        have tailIndex := inductionHypothesis tail inner tailTrue
        have headPreserved :
            replaceQubitWire basis inner.succ false 0 = basis 0 := by
          exact replaceQubitWire_outside basis inner.succ 0 false
            (Ne.symm (Fin.succ_ne_zero inner))
        have tailReplaced :
            (fun wire =>
              replaceQubitWire basis inner.succ false wire.succ) =
              replaceQubitWire tail inner false := by
          funext wire
          simp [replaceQubitWire, tail]
        simp only [qubitBasisLittleEndianIndex]
        rw [headPreserved, tailReplaced, tailIndex]
        simp [Nat.bit, Nat.pow_succ]
        simp only [tail]
        cases basis 0 <;> simp <;> omega

/-- Replacing the current boundary wire by zero turns the old fixed-zero
block predicate into the predicate with that wire freed. -/
theorem ShuklaVedulaBoundaryBlockSpec.matches_replace_false_iff_advance
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (notTerminal : spec.boundary < width) (target : Fin width)
    (targetAtBoundary : target.val = spec.boundary)
    (targetOutside : target ∉ spec.suffix) (output : QubitBasis width) :
    spec.Matches (replaceQubitWire output target false) ↔
      (spec.advance notTerminal).Matches output := by
  constructor
  · intro matching wire above
    change spec.boundary + 1 ≤ wire.val at above
    have wireDifferent : wire ≠ target := by
      intro equal
      subst wire
      omega
    have oldAbove : spec.boundary ≤ wire.val := by omega
    have result := matching wire oldAbove
    rw [replaceQubitWire_outside output target wire false wireDifferent] at result
    exact result
  · intro matching wire above
    by_cases equal : wire = target
    · subst wire
      simp [replaceQubitWire, targetOutside]
    · have newAbove : spec.boundary + 1 ≤ wire.val := by
        have notEqualValue : wire.val ≠ target.val := by
          intro equalValue
          exact equal (Fin.ext equalValue)
        omega
      rw [replaceQubitWire_outside output target wire false equal]
      exact matching wire newAbove

/-- Setting a fixed-zero boundary wire to one cannot satisfy the old block
predicate. -/
theorem ShuklaVedulaBoundaryBlockSpec.not_matches_replace_true
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (target : Fin width) (targetAtBoundary : target.val = spec.boundary)
    (targetOutside : target ∉ spec.suffix) (output : QubitBasis width) :
    ¬ spec.Matches (replaceQubitWire output target true) := by
  intro matching
  have atTarget := matching target (by omega)
  simp [targetOutside] at atTarget

/-- One Hadamard on the current fixed-zero boundary wire frees that wire and
divides the block amplitude by `sqrt 2`. -/
theorem applyOperator_embedHadamard_boundaryBlockState
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (notTerminal : spec.boundary < width) (target : Fin width)
    (targetAtBoundary : target.val = spec.boundary)
    (targetOutside : target ∉ spec.suffix) (amplitude : ℂ) :
    applyOperator (embedSingleQubitOperator target localH)
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState (spec.advance notTerminal)
        (((1 / Real.sqrt 2 : ℝ) : ℂ) * amplitude) := by
  funext output
  rw [applyOperator_embedSingleQubitOperator_state]
  have falseMatch :=
    spec.matches_replace_false_iff_advance notTerminal target
      targetAtBoundary targetOutside output
  have trueNotMatch :=
    spec.not_matches_replace_true target targetAtBoundary targetOutside output
  by_cases advanced : (spec.advance notTerminal).Matches output
  · have falseMatches :
        spec.Matches (replaceQubitWire output target false) :=
      falseMatch.mpr advanced
    simp [shuklaVedulaBoundaryBlockState, localH, falseMatches, trueNotMatch,
      advanced]
  · have falseNotMatch :
        ¬ spec.Matches (replaceQubitWire output target false) :=
      fun matching => advanced (falseMatch.mp matching)
    simp [shuklaVedulaBoundaryBlockState, localH, falseNotMatch, trueNotMatch,
      advanced]

/-- A consecutive source-order interval of unconditional Hadamards frees all
wires from `lower` up to `upper`. -/
theorem applyOperator_hadamardInterval_boundaryBlockState
    {width : Nat} (lower upper gap : Nat) (upperValue : upper = lower + gap)
    (upperLeWidth : upper ≤ width)
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (boundaryEq : spec.boundary = lower)
    (suffixAbove : ∀ wire, wire ∈ spec.suffix → upper ≤ wire.val)
    (amplitude : ℂ) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          ((widthOnlyWireInterval width lower upper).map
            ExternallyControlledPrimitivePlan.h))
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState
        (spec.withBoundary upper upperLeWidth)
        (((((1 / Real.sqrt 2 : ℝ) : ℂ) ^ gap) * amplitude)) := by
  induction gap generalizing lower spec amplitude with
  | zero =>
      have upperLower : upper = lower := by omega
      have sameSpec : spec.withBoundary upper upperLeWidth = spec := by
        cases spec
        simp_all [ShuklaVedulaBoundaryBlockSpec.withBoundary]
      have intervalNil : widthOnlyWireInterval width lower upper = [] :=
        widthOnlyWireInterval_eq_nil_of_upper_le width lower upper (by omega)
      rw [sameSpec, intervalNil]
      simp [ExternallyControlledPrimitivePlan.sourcePlanOperator,
        operatorSequence, applyOperator]
  | succ gap inductionHypothesis =>
      have lowerLtUpper : lower < upper := by omega
      let target : Fin width := ⟨lower, lowerLtUpper.trans_le upperLeWidth⟩
      have intervalCons :
          widthOnlyWireInterval width lower upper =
            target :: widthOnlyWireInterval width (lower + 1) upper := by
        exact widthOnlyWireInterval_cons width lower upper lowerLtUpper
          upperLeWidth
      have targetAtBoundary : target.val = spec.boundary := by
        simp [target, boundaryEq]
      have targetOutside : target ∉ spec.suffix := by
        intro member
        have above := suffixAbove target member
        simp [target] at above
        omega
      have notTerminal : spec.boundary < width := by
        rw [boundaryEq]
        exact lowerLtUpper.trans_le upperLeWidth
      rw [intervalCons, List.map_cons]
      rw [show .h target ::
          (widthOnlyWireInterval width (lower + 1) upper).map
              ExternallyControlledPrimitivePlan.h =
            [.h target] ++
              (widthOnlyWireInterval width (lower + 1) upper).map
                ExternallyControlledPrimitivePlan.h by rfl,
        ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
        applyOperator_mul]
      rw [show ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          [.h target] = embedSingleQubitOperator target localH by
        simp [ExternallyControlledPrimitivePlan.sourcePlanOperator,
          ExternallyControlledPrimitivePlan.sourceOperator, operatorSequence]]
      rw [applyOperator_embedHadamard_boundaryBlockState spec notTerminal target
        targetAtBoundary targetOutside amplitude]
      have nextUpperValue : upper = (lower + 1) + gap := by omega
      have nextBoundary : (spec.advance notTerminal).boundary = lower + 1 := by
        simp [ShuklaVedulaBoundaryBlockSpec.advance, boundaryEq]
      have recursive := inductionHypothesis (lower + 1) nextUpperValue
        (spec.advance notTerminal) nextBoundary suffixAbove
        ((((1 / Real.sqrt 2 : ℝ) : ℂ) * amplitude))
      simpa [ShuklaVedulaBoundaryBlockSpec.advance,
        ShuklaVedulaBoundaryBlockSpec.withBoundary, pow_succ, mul_assoc]
        using recursive

/-- The source-order X suffix followed by the initial unconditional Hadamard
interval creates the normalized first active binary block. -/
theorem applyOperator_shuklaVedulaInitialPrefix_zeroKet
    {width : Nat} (first second : Fin width) (rest : List (Fin width))
    (sorted : (first :: second :: rest).Pairwise fun left right =>
      left.val < right.val) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          ((second :: rest).map ExternallyControlledPrimitivePlan.x ++
            (widthOnlyWireInterval width 0 first.val).map
              ExternallyControlledPrimitivePlan.h))
        (basisKet (fun _ => false : QubitBasis width)) =
      shuklaVedulaBoundaryBlockState
        (shuklaVedulaLocationBlockSpec first (second :: rest))
        ((((1 / Real.sqrt 2 : ℝ) : ℂ) ^ first.val)) := by
  have tailSorted :
      (second :: rest).Pairwise fun left right => left.val < right.val :=
    (List.pairwise_cons.mp sorted).2
  have tailNodup : (second :: rest).Nodup := by
    exact tailSorted.imp fun less equal => by
      subst_vars
      omega
  have suffixAbove : ∀ wire, wire ∈ second :: rest → first.val ≤ wire.val := by
    intro wire member
    exact ((List.pairwise_cons.mp sorted).1 wire member).le
  rw [ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
    applyOperator_mul,
    applyOperator_sourcePlanOperator_x_map_zeroKet_eq_blockState
      (second :: rest) tailNodup]
  have intervalResult :=
    applyOperator_hadamardInterval_boundaryBlockState
      0 first.val first.val (by omega) first.isLt.le
      (shuklaVedulaZeroBoundaryBlockSpec (second :: rest)) rfl suffixAbove
      (1 : ℂ)
  simpa [shuklaVedulaLocationBlockSpec,
    shuklaVedulaZeroBoundaryBlockSpec,
    ShuklaVedulaBoundaryBlockSpec.withBoundary] using intervalResult

/-- The first active block coefficient can be expressed in the normalization
form expected by the direct initial split theorem. -/
theorem applyOperator_shuklaVedulaInitialPrefix_zeroKet_normalized
    {width validCount : Nat} (validCountPositive : 0 < validCount)
    (first second : Fin width) (rest : List (Fin width))
    (sorted : (first :: second :: rest).Pairwise fun left right =>
      left.val < right.val) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          ((second :: rest).map ExternallyControlledPrimitivePlan.x ++
            (widthOnlyWireInterval width 0 first.val).map
              ExternallyControlledPrimitivePlan.h))
        (basisKet (fun _ => false : QubitBasis width)) =
      shuklaVedulaBoundaryBlockState
        (shuklaVedulaLocationBlockSpec first (second :: rest))
        ((Real.sqrt
            ((validCount : ℝ) / (2 ^ first.val : Nat)) /
          Real.sqrt validCount : ℝ) : ℂ) := by
  rw [applyOperator_shuklaVedulaInitialPrefix_zeroKet first second rest sorted]
  have blockPositive : 0 < 2 ^ first.val :=
    pow_pos (by omega : 0 < (2 : Nat)) first.val
  have realAmplitude :
      (1 / Real.sqrt 2 : ℝ) ^ first.val =
        Real.sqrt ((validCount : ℝ) / (2 ^ first.val : Nat)) /
          Real.sqrt validCount := by
    rw [inverseSqrtTwoPow_eq_inverseSqrt_pow]
    exact (sqrt_total_div_block_div_sqrt_total (2 ^ first.val) validCount
      blockPositive validCountPositive).symm
  rw [show (((1 / Real.sqrt 2 : ℝ) : ℂ) ^ first.val) =
      ((Real.sqrt ((validCount : ℝ) / (2 ^ first.val : Nat)) /
        Real.sqrt validCount : ℝ) : ℂ) by
    exact_mod_cast realAmplitude]

/-- A block fixing `target` to one cannot contain an output where that wire is
zero. -/
theorem ShuklaVedulaBoundaryBlockSpec.not_matches_of_target_false
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (target : Fin width) (targetAbove : spec.boundary ≤ target.val)
    (targetMember : target ∈ spec.suffix) (output : QubitBasis width)
    (targetFalse : output target = false) : ¬ spec.Matches output := by
  intro matching
  have atTarget := matching target targetAbove
  simp [targetMember, targetFalse] at atTarget

/-- A block fixing `target` to zero cannot contain an output where that wire is
one. -/
theorem ShuklaVedulaBoundaryBlockSpec.not_matches_of_target_true
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (target : Fin width) (targetAbove : spec.boundary ≤ target.val)
    (targetOutside : target ∉ spec.suffix) (output : QubitBasis width)
    (targetTrue : output target = true) : ¬ spec.Matches output := by
  intro matching
  have atTarget := matching target targetAbove
  simp [targetOutside, targetTrue] at atTarget

/-- When `target` is currently zero, setting it to one changes a block with
suffix `target :: rest` into the otherwise identical block with suffix
`rest`. -/
theorem ShuklaVedulaBoundaryBlockSpec.matches_replace_true_iff_withoutTarget
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (target : Fin width) (rest : List (Fin width))
    (suffixEq : spec.suffix = target :: rest)
    (targetOutsideRest : target ∉ rest) (output : QubitBasis width)
    (targetFalse : output target = false) :
    spec.Matches (replaceQubitWire output target true) ↔
      (spec.withSuffix rest).Matches output := by
  constructor
  · intro matching wire above
    by_cases equal : wire = target
    · subst wire
      simp [ShuklaVedulaBoundaryBlockSpec.withSuffix, targetOutsideRest,
        targetFalse]
    · have result := matching wire above
      rw [replaceQubitWire_outside output target wire true equal] at result
      change output wire = decide (wire ∈ rest)
      simpa [suffixEq, equal] using result
  · intro matching wire above
    by_cases equal : wire = target
    · subst wire
      simp [replaceQubitWire, suffixEq]
    · rw [replaceQubitWire_outside output target wire true equal]
      have result := matching wire above
      rw [suffixEq]
      change output wire = decide (wire ∈ rest) at result
      simpa [equal] using result

/-- A local Ry acting on a suffix wire that is fixed to one splits one binary
block into the unchanged suffix block and the otherwise identical zero-suffix
block. -/
theorem applyOperator_embedRy_boundaryBlockState_target_mem
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (target : Fin width) (rest : List (Fin width))
    (targetAbove : spec.boundary ≤ target.val)
    (suffixEq : spec.suffix = target :: rest)
    (targetOutsideRest : target ∉ rest) (angle : ℝ) (amplitude : ℂ) :
    applyOperator (embedSingleQubitOperator target (localRy angle))
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState spec
          (((Real.cos (angle / 2) : ℝ) : ℂ) * amplitude) +
        shuklaVedulaBoundaryBlockState (spec.withSuffix rest)
          (((-Real.sin (angle / 2) : ℝ) : ℂ) * amplitude) := by
  funext output
  rw [applyOperator_embedSingleQubitOperator_state]
  rw [Fintype.sum_bool]
  have targetMember : target ∈ spec.suffix := by simp [suffixEq]
  by_cases outputTrue : output target = true
  ·
    have withoutFalse := (spec.withSuffix rest).not_matches_of_target_true
      target targetAbove targetOutsideRest output outputTrue
    have replaceTrue : replaceQubitWire output target true = output := by
      simpa [outputTrue] using replaceQubitWire_self output target
    have replaceFalseNot :
        ¬ spec.Matches (replaceQubitWire output target false) :=
      spec.not_matches_of_target_false target targetAbove targetMember _ (by simp)
    rw [replaceTrue]
    simp [shuklaVedulaBoundaryBlockState, localRy, outputTrue,
      replaceFalseNot, withoutFalse]
  · have outputFalse : output target = false := by
      exact Bool.eq_false_of_not_eq_true outputTrue
    have oldFalse := spec.not_matches_of_target_false target targetAbove
      targetMember output outputFalse
    have replaceFalse : replaceQubitWire output target false = output := by
      simpa [outputFalse] using replaceQubitWire_self output target
    have replaceTrue := spec.matches_replace_true_iff_withoutTarget target rest
      suffixEq targetOutsideRest output outputFalse
    by_cases without : (spec.withSuffix rest).Matches output
    · simp [shuklaVedulaBoundaryBlockState, localRy, outputFalse, replaceFalse,
        replaceTrue, oldFalse, without]
    · simp [shuklaVedulaBoundaryBlockState, localRy, outputFalse, replaceFalse,
        replaceTrue, oldFalse, without]

/-- A zero-controlled local embedding has the expected sparse one-target
matrix entries. -/
theorem embedZeroControlledSingleQubitOperator_apply_sparse
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ) (output input : QubitBasis qubits) :
    embedZeroControlledSingleQubitOperator control target different
        localOperator output input =
      if agreesExcept target output input then
        if input control then
          if output target = input target then 1 else 0
        else localOperator (output target) (input target)
      else 0 := by
  unfold embedZeroControlledSingleQubitOperator
  rw [embedTwoQubitOperator_apply]
  by_cases outside : agreesExceptTwo control target output input
  · by_cases controlEqual : output control = input control
    · have targetAgreement : agreesExcept target output input := by
        intro wire wireDifferent
        by_cases isControl : wire = control
        · simpa [isControl] using controlEqual
        · exact outside wire isControl wireDifferent
      simp [outside, localZeroControlledOperator, targetAgreement,
        controlEqual]
    · have notTargetAgreement : ¬agreesExcept target output input := by
        intro agreement
        exact controlEqual (agreement control different)
      simp [outside, localZeroControlledOperator, notTargetAgreement,
        controlEqual]
  · have notTargetAgreement : ¬agreesExcept target output input := by
      intro agreement
      apply outside
      intro wire firstDifferent secondDifferent
      exact agreement wire secondDifferent
    simp [outside, notTargetAgreement]

/-- Applying a zero-controlled local operator is a two-term target sum when
the output control is zero, and leaves the state unchanged otherwise. -/
theorem applyOperator_embedZeroControlledSingleQubitOperator_state
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ)
    (state : State (QubitBasis qubits)) (output : QubitBasis qubits) :
    applyOperator
        (embedZeroControlledSingleQubitOperator control target different
          localOperator) state output =
      if output control then state output
      else ∑ inputBit : Bool,
        localOperator (output target) inputBit *
          state (replaceQubitWire output target inputBit) := by
  unfold applyOperator Matrix.mulVec dotProduct
  change (∑ input,
      embedZeroControlledSingleQubitOperator control target different
          localOperator output input * state input) = _
  rw [show (∑ input,
      embedZeroControlledSingleQubitOperator control target different
          localOperator output input * state input) =
        ∑ pair : Bool × ({wire : Fin qubits // wire ≠ target} → Bool),
          embedZeroControlledSingleQubitOperator control target different
              localOperator output ((splitWireEquiv target).symm pair) *
            state ((splitWireEquiv target).symm pair) by
    exact ((splitWireEquiv target).symm.sum_comp fun input =>
      embedZeroControlledSingleQubitOperator control target different
          localOperator output input * state input).symm]
  simp_rw [Fintype.sum_prod_type]
  simp [embedZeroControlledSingleQubitOperator_apply_sparse,
    agreesExcept_splitWireEquiv_symm_iff, splitWireEquiv_symm_target,
    ← replaceQubitWire_eq_splitWireEquiv_symm,
    replaceQubitWire_outside _ _ _ _ different]

/-- A zero-controlled local action is the identity on a binary block whose
control wire is fixed to one. -/
theorem applyOperator_embedZeroControlled_boundaryBlockState_control_true
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (control target : Fin width) (different : control ≠ target)
    (controlAbove : spec.boundary ≤ control.val)
    (controlMember : control ∈ spec.suffix)
    (localOperator : Matrix Bool Bool ℂ) (amplitude : ℂ) :
    applyOperator
        (embedZeroControlledSingleQubitOperator control target different
          localOperator)
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState spec amplitude := by
  funext output
  rw [applyOperator_embedZeroControlledSingleQubitOperator_state]
  by_cases controlValue : output control = true
  · simp [controlValue]
  · have controlFalse : output control = false :=
      Bool.eq_false_of_not_eq_true controlValue
    have outputOutside : ¬ spec.Matches output :=
      spec.not_matches_of_target_false control controlAbove controlMember
        output controlFalse
    have replacedOutside : ∀ inputBit : Bool,
        ¬ spec.Matches (replaceQubitWire output target inputBit) := by
      intro inputBit
      apply spec.not_matches_of_target_false control controlAbove
        controlMember
      rw [replaceQubitWire_outside output target control inputBit different]
      exact controlFalse
    rw [if_neg controlValue, Fintype.sum_bool]
    simp [shuklaVedulaBoundaryBlockState, outputOutside,
      replacedOutside false, replacedOutside true]

/-- On a binary block whose control wire is fixed to zero, a zero-controlled
local action agrees with the corresponding unconditional local embedding. -/
theorem applyOperator_embedZeroControlled_boundaryBlockState_control_false
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (control target : Fin width) (different : control ≠ target)
    (controlAbove : spec.boundary ≤ control.val)
    (controlOutside : control ∉ spec.suffix)
    (localOperator : Matrix Bool Bool ℂ) (amplitude : ℂ) :
    applyOperator
        (embedZeroControlledSingleQubitOperator control target different
          localOperator)
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      applyOperator (embedSingleQubitOperator target localOperator)
        (shuklaVedulaBoundaryBlockState spec amplitude) := by
  funext output
  rw [applyOperator_embedZeroControlledSingleQubitOperator_state,
    applyOperator_embedSingleQubitOperator_state]
  by_cases controlValue : output control = true
  · have outputOutside : ¬ spec.Matches output :=
      spec.not_matches_of_target_true control controlAbove controlOutside
        output controlValue
    have replacedOutside : ∀ inputBit : Bool,
        ¬ spec.Matches (replaceQubitWire output target inputBit) := by
      intro inputBit
      apply spec.not_matches_of_target_true control controlAbove controlOutside
      rw [replaceQubitWire_outside output target control inputBit different]
      exact controlValue
    rw [if_pos controlValue, Fintype.sum_bool]
    simp [shuklaVedulaBoundaryBlockState, outputOutside,
      replacedOutside false, replacedOutside true]
  · rw [if_neg controlValue]

/-- Zero-controlled Hadamard frees the current fixed-zero boundary when its
control is another fixed-zero wire. -/
theorem applyOperator_embedZeroControlledHadamard_boundaryBlockState
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (notTerminal : spec.boundary < width)
    (control target : Fin width) (different : control ≠ target)
    (controlAbove : spec.boundary ≤ control.val)
    (controlOutside : control ∉ spec.suffix)
    (targetAtBoundary : target.val = spec.boundary)
    (targetOutside : target ∉ spec.suffix) (amplitude : ℂ) :
    applyOperator
        (embedZeroControlledSingleQubitOperator control target different localH)
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState (spec.advance notTerminal)
        (((1 / Real.sqrt 2 : ℝ) : ℂ) * amplitude) := by
  rw [applyOperator_embedZeroControlled_boundaryBlockState_control_false
    spec control target different controlAbove controlOutside]
  exact applyOperator_embedHadamard_boundaryBlockState spec notTerminal target
    targetAtBoundary targetOutside amplitude

/-- Zero-controlled Ry splits an active fixed-zero-control block exactly as
the corresponding unconditional embedded rotation. -/
theorem applyOperator_embedZeroControlledRy_boundaryBlockState_target_mem
    {width : Nat} (spec : ShuklaVedulaBoundaryBlockSpec width)
    (control target : Fin width) (different : control ≠ target)
    (controlAbove : spec.boundary ≤ control.val)
    (controlOutside : control ∉ spec.suffix)
    (targetAbove : spec.boundary ≤ target.val)
    (rest : List (Fin width)) (suffixEq : spec.suffix = target :: rest)
    (targetOutsideRest : target ∉ rest) (angle : ℝ) (amplitude : ℂ) :
    applyOperator
        (embedZeroControlledSingleQubitOperator control target different
          (localRy angle))
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState spec
          (((Real.cos (angle / 2) : ℝ) : ℂ) * amplitude) +
        shuklaVedulaBoundaryBlockState (spec.withSuffix rest)
          (((-Real.sin (angle / 2) : ℝ) : ℂ) * amplitude) := by
  rw [applyOperator_embedZeroControlled_boundaryBlockState_control_false
    spec control target different controlAbove controlOutside]
  exact applyOperator_embedRy_boundaryBlockState_target_mem spec target rest
    targetAbove suffixEq targetOutsideRest angle amplitude

/-- A consecutive source-order interval of zero-controlled Hadamards frees
exactly the wires from `lower` up to (but excluding) `control`. -/
theorem applyOperator_zeroControlledHadamardInterval_boundaryBlockState
    {width : Nat} (control : Fin width) (lower gap : Nat)
    (controlValue : control.val = lower + gap)
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (boundaryEq : spec.boundary = lower)
    (controlOutside : control ∉ spec.suffix)
    (suffixAbove : ∀ wire, wire ∈ spec.suffix → control.val ≤ wire.val)
    (amplitude : ℂ) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          ((widthOnlyWireInterval width lower control.val).flatMap
            (zeroControlledHadamardSourcePlan control)))
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState
          (spec.withBoundary control.val control.isLt.le)
          (((((1 / Real.sqrt 2 : ℝ) : ℂ) ^ gap) * amplitude)) := by
  induction gap generalizing lower spec amplitude with
  | zero =>
      have controlLower : control.val = lower := by simpa using controlValue
      have boundaryControl : spec.boundary = control.val := by
        calc
          spec.boundary = lower := boundaryEq
          _ = control.val := controlLower.symm
      subst lower
      have sameSpec :
          spec.withBoundary control.val control.isLt.le = spec := by
        cases spec
        simp_all [ShuklaVedulaBoundaryBlockSpec.withBoundary]
      have intervalNil :
          widthOnlyWireInterval width spec.boundary control.val = [] :=
        widthOnlyWireInterval_eq_nil_of_upper_le width spec.boundary
          control.val (by omega)
      rw [sameSpec]
      rw [intervalNil]
      simp [ExternallyControlledPrimitivePlan.sourcePlanOperator,
        operatorSequence, applyOperator]
  | succ gap inductionHypothesis =>
      have lowerLtControl : lower < control.val := by omega
      let target : Fin width := ⟨lower, lowerLtControl.trans control.isLt⟩
      have intervalCons :
          widthOnlyWireInterval width lower control.val =
            target :: widthOnlyWireInterval width (lower + 1) control.val := by
        exact widthOnlyWireInterval_cons width lower control.val
          lowerLtControl control.isLt.le
      have different : control ≠ target := by
        intro equal
        have values := congrArg Fin.val equal
        simp [target] at values
        omega
      have targetAtBoundary : target.val = spec.boundary := by
        simp [target, boundaryEq]
      have notTerminal : spec.boundary < width := by
        rw [boundaryEq]
        exact lowerLtControl.trans control.isLt
      have controlAbove : spec.boundary ≤ control.val := by
        rw [boundaryEq]
        omega
      have targetOutside : target ∉ spec.suffix := by
        intro member
        have above := suffixAbove target member
        simp [target] at above
        omega
      rw [intervalCons, List.flatMap_cons,
        ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
        applyOperator_mul,
        sourcePlanOperator_zeroControlledHadamardSourcePlan control target
          different,
        applyOperator_embedZeroControlledHadamard_boundaryBlockState spec
          notTerminal control target different controlAbove controlOutside
          targetAtBoundary targetOutside amplitude]
      have nextControlValue : control.val = (lower + 1) + gap := by omega
      have nextBoundary :
          (spec.advance notTerminal).boundary = lower + 1 := by
        simp [ShuklaVedulaBoundaryBlockSpec.advance, boundaryEq]
      have recursive := inductionHypothesis (lower + 1) nextControlValue
        (spec.advance notTerminal) nextBoundary controlOutside suffixAbove
        ((((1 / Real.sqrt 2 : ℝ) : ℂ) * amplitude))
      simpa [ShuklaVedulaBoundaryBlockSpec.advance,
        ShuklaVedulaBoundaryBlockSpec.withBoundary, pow_succ, mul_assoc]
        using recursive

/-- A source-order interval of zero-controlled Hadamards is the identity on a
block whose common control wire is fixed to one. -/
theorem applyOperator_zeroControlledHadamardInterval_boundaryBlockState_control_true
    {width : Nat} (control : Fin width) (lower gap : Nat)
    (controlValue : control.val = lower + gap)
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (controlAbove : spec.boundary ≤ control.val)
    (controlMember : control ∈ spec.suffix)
    (amplitude : ℂ) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          ((widthOnlyWireInterval width lower control.val).flatMap
            (zeroControlledHadamardSourcePlan control)))
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState spec amplitude := by
  induction gap generalizing lower with
  | zero =>
      have controlLower : control.val = lower := by simpa using controlValue
      subst lower
      rw [widthOnlyWireInterval_eq_nil_of_upper_le width control.val
        control.val (Nat.le_refl _)]
      simp [ExternallyControlledPrimitivePlan.sourcePlanOperator,
        operatorSequence, applyOperator]
  | succ gap inductionHypothesis =>
      have lowerLtControl : lower < control.val := by omega
      let target : Fin width := ⟨lower, lowerLtControl.trans control.isLt⟩
      have intervalCons :
          widthOnlyWireInterval width lower control.val =
            target :: widthOnlyWireInterval width (lower + 1) control.val := by
        exact widthOnlyWireInterval_cons width lower control.val
          lowerLtControl control.isLt.le
      have different : control ≠ target := by
        intro equal
        have values := congrArg Fin.val equal
        simp [target] at values
        omega
      rw [intervalCons, List.flatMap_cons,
        ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
        applyOperator_mul,
        sourcePlanOperator_zeroControlledHadamardSourcePlan control target
          different,
        applyOperator_embedZeroControlled_boundaryBlockState_control_true
          spec control target different controlAbove controlMember localH
          amplitude]
      exact inductionHypothesis (lower + 1) (by omega)

/-- One source-order tail head splits the active block, leaves the finalized
`current` block in place, and expands the next active block up to `next`. -/
theorem applyOperator_shuklaVedulaTailHead_boundaryBlockState
    {width : Nat} (current next : Fin width)
    (currentBeforeNext : current.val < next.val)
    (rest : List (Fin width))
    (nextOutsideRest : next ∉ rest)
    (restAbove : ∀ wire, wire ∈ rest → next.val ≤ wire.val)
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (boundaryEq : spec.boundary = current.val)
    (suffixEq : spec.suffix = next :: rest)
    (currentOutside : current ∉ spec.suffix)
    (angle : AngleExpr) (amplitude : ℂ) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          (zeroControlledRySourcePlan current next angle ++
            (widthOnlyWireInterval width current.val next.val).flatMap
              (zeroControlledHadamardSourcePlan next)))
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState spec
          (((Real.cos (angle.uniformValue / 2) : ℝ) : ℂ) * amplitude) +
        shuklaVedulaBoundaryBlockState
          ((spec.withSuffix rest).withBoundary next.val next.isLt.le)
          (((((1 / Real.sqrt 2 : ℝ) : ℂ) ^
              (next.val - current.val))) *
            (((-Real.sin (angle.uniformValue / 2) : ℝ) : ℂ) * amplitude)) := by
  have different : current ≠ next := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  have currentAbove : spec.boundary ≤ current.val := by omega
  have nextAbove : spec.boundary ≤ next.val := by omega
  have nextMember : next ∈ spec.suffix := by simp [suffixEq]
  have activeBoundary : (spec.withSuffix rest).boundary = current.val := by
    simp [ShuklaVedulaBoundaryBlockSpec.withSuffix, boundaryEq]
  rw [ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
    applyOperator_mul,
    sourcePlanOperator_zeroControlledRySourcePlan current next different angle,
    applyOperator_embedZeroControlledRy_boundaryBlockState_target_mem spec
      current next different currentAbove currentOutside nextAbove rest suffixEq
      nextOutsideRest angle.uniformValue amplitude,
    applyOperator_add,
    applyOperator_zeroControlledHadamardInterval_boundaryBlockState_control_true
      next current.val (next.val - current.val)
      (by omega) spec nextAbove nextMember,
    applyOperator_zeroControlledHadamardInterval_boundaryBlockState
      next current.val (next.val - current.val)
      (by omega) (spec.withSuffix rest) activeBoundary nextOutsideRest restAbove]

/-- A tail head is the identity on any already-finalized block that fixes both
its current and next control wires to one. -/
theorem applyOperator_shuklaVedulaTailHead_boundaryBlockState_controls_true
    {width : Nat} (current next : Fin width)
    (currentBeforeNext : current.val < next.val)
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (currentAbove : spec.boundary ≤ current.val)
    (nextAbove : spec.boundary ≤ next.val)
    (currentMember : current ∈ spec.suffix)
    (nextMember : next ∈ spec.suffix)
    (angle : AngleExpr) (amplitude : ℂ) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          (zeroControlledRySourcePlan current next angle ++
            (widthOnlyWireInterval width current.val next.val).flatMap
              (zeroControlledHadamardSourcePlan next)))
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState spec amplitude := by
  have different : current ≠ next := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  rw [ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
    applyOperator_mul,
    sourcePlanOperator_zeroControlledRySourcePlan current next different angle,
    applyOperator_embedZeroControlled_boundaryBlockState_control_true spec
      current next different currentAbove currentMember
      (localRy angle.uniformValue) amplitude,
    applyOperator_zeroControlledHadamardInterval_boundaryBlockState_control_true
      next current.val (next.val - current.val) (by omega) spec nextAbove
      nextMember]

/-- The complete remaining tail plan is the identity on a finalized block
whose fixed-one suffix contains every remaining tail control. -/
theorem applyOperator_shuklaVedulaUniformTailPlan_boundaryBlockState_controls_true
    {width : Nat} (validCount accumulated : Nat)
    (locations : List (Fin width))
    (sorted : locations.Pairwise fun left right => left.val < right.val)
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (controlsAbove : ∀ wire, wire ∈ locations → spec.boundary ≤ wire.val)
    (controlsMember : ∀ wire, wire ∈ locations → wire ∈ spec.suffix)
    (amplitude : ℂ) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          (shuklaVedulaUniformTailPlan validCount accumulated locations))
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState spec amplitude := by
  induction locations generalizing accumulated with
  | nil =>
      simp [shuklaVedulaUniformTailPlan,
        ExternallyControlledPrimitivePlan.sourcePlanOperator,
        operatorSequence, applyOperator]
  | cons current locations inductionHypothesis =>
      cases locations with
      | nil =>
          simp [shuklaVedulaUniformTailPlan,
            ExternallyControlledPrimitivePlan.sourcePlanOperator,
            operatorSequence, applyOperator]
      | cons next rest =>
          have pairwise := List.pairwise_cons.mp sorted
          have currentBeforeNext : current.val < next.val :=
            pairwise.1 next (by simp)
          have tailSorted :
              (next :: rest).Pairwise fun left right => left.val < right.val :=
            pairwise.2
          have currentAbove : spec.boundary ≤ current.val :=
            controlsAbove current (by simp)
          have nextAbove : spec.boundary ≤ next.val :=
            controlsAbove next (by simp)
          have currentMember : current ∈ spec.suffix :=
            controlsMember current (by simp)
          have nextMember : next ∈ spec.suffix :=
            controlsMember next (by simp)
          have tailAbove : ∀ wire, wire ∈ next :: rest →
              spec.boundary ≤ wire.val := by
            intro wire member
            exact controlsAbove wire (by simp [member])
          have tailMember : ∀ wire, wire ∈ next :: rest →
              wire ∈ spec.suffix := by
            intro wire member
            exact controlsMember wire (by simp [member])
          rw [shuklaVedulaUniformTailPlan,
            ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
            ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
            applyOperator_mul, applyOperator_mul]
          rw [sourcePlanOperator_zeroControlledRySourcePlan current next
              (by intro equal; have values := congrArg Fin.val equal; omega),
            applyOperator_embedZeroControlled_boundaryBlockState_control_true
              spec current next
              (by intro equal; have values := congrArg Fin.val equal; omega)
              currentAbove currentMember,
            applyOperator_zeroControlledHadamardInterval_boundaryBlockState_control_true
              next current.val (next.val - current.val) (by omega) spec
              nextAbove nextMember]
          exact inductionHypothesis (accumulated + 2 ^ current.val) tailSorted
            tailAbove tailMember

/-- The first direct `Ry` split has the same block action as a recursive tail
head, except that the split itself is unconditional. -/
theorem applyOperator_shuklaVedulaInitialHead_boundaryBlockState
    {width : Nat} (current next : Fin width)
    (currentBeforeNext : current.val < next.val)
    (rest : List (Fin width))
    (nextOutsideRest : next ∉ rest)
    (restAbove : ∀ wire, wire ∈ rest → next.val ≤ wire.val)
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (boundaryEq : spec.boundary = current.val)
    (suffixEq : spec.suffix = next :: rest)
    (angle : AngleExpr) (amplitude : ℂ) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          ([.ry angle next] ++
            (widthOnlyWireInterval width current.val next.val).flatMap
              (zeroControlledHadamardSourcePlan next)))
        (shuklaVedulaBoundaryBlockState spec amplitude) =
      shuklaVedulaBoundaryBlockState spec
          (((Real.cos (angle.uniformValue / 2) : ℝ) : ℂ) * amplitude) +
        shuklaVedulaBoundaryBlockState
          ((spec.withSuffix rest).withBoundary next.val next.isLt.le)
          (((((1 / Real.sqrt 2 : ℝ) : ℂ) ^
              (next.val - current.val))) *
            (((-Real.sin (angle.uniformValue / 2) : ℝ) : ℂ) * amplitude)) := by
  have nextAbove : spec.boundary ≤ next.val := by omega
  have nextMember : next ∈ spec.suffix := by simp [suffixEq]
  have activeBoundary : (spec.withSuffix rest).boundary = current.val := by
    simp [ShuklaVedulaBoundaryBlockSpec.withSuffix, boundaryEq]
  rw [ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
    applyOperator_mul]
  rw [show ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
      [.ry angle next] =
        embedSingleQubitOperator next (localRy angle.uniformValue) by
      simp [ExternallyControlledPrimitivePlan.sourcePlanOperator,
        ExternallyControlledPrimitivePlan.sourceOperator, operatorSequence,
        AngleExpr.uniformValue],
    applyOperator_embedRy_boundaryBlockState_target_mem spec next rest
      nextAbove suffixEq nextOutsideRest angle.uniformValue amplitude,
    applyOperator_add,
    applyOperator_zeroControlledHadamardInterval_boundaryBlockState_control_true
      next current.val (next.val - current.val) (by omega) spec nextAbove
      nextMember,
    applyOperator_zeroControlledHadamardInterval_boundaryBlockState
      next current.val (next.val - current.val) (by omega)
      (spec.withSuffix rest) activeBoundary nextOutsideRest restAbove]

/-- Specializing the first direct split to the negative split angle produces
one finalized uniform block and the normalized active block consumed by the
recursive tail theorem. -/
theorem applyOperator_shuklaVedulaInitialHead_boundaryBlockState_normalized
    {width : Nat} (current next : Fin width)
    (currentBeforeNext : current.val < next.val)
    (rest : List (Fin width))
    (nextOutsideRest : next ∉ rest)
    (restAbove : ∀ wire, wire ∈ rest → next.val ≤ wire.val)
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (boundaryEq : spec.boundary = current.val)
    (suffixEq : spec.suffix = next :: rest)
    (left right validCount : Nat) (leftPositive : 0 < left)
    (totalPositive : 0 < left + right) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          ([.ry (shuklaVedulaNegativeSplitAngle left right) next] ++
            (widthOnlyWireInterval width current.val next.val).flatMap
              (zeroControlledHadamardSourcePlan next)))
        (shuklaVedulaBoundaryBlockState spec
          ((Real.sqrt (((left + right : Nat) : ℝ) / left) /
            Real.sqrt validCount : ℝ) : ℂ)) =
      shuklaVedulaBoundaryBlockState spec
          ((1 / Real.sqrt validCount : ℝ) : ℂ) +
        shuklaVedulaBoundaryBlockState
          ((spec.withSuffix rest).withBoundary next.val next.isLt.le)
          ((Real.sqrt
              ((right : ℝ) /
                (left * 2 ^ (next.val - current.val) : Nat)) /
            Real.sqrt validCount : ℝ) : ℂ) := by
  rw [applyOperator_shuklaVedulaInitialHead_boundaryBlockState current next
    currentBeforeNext rest nextOutsideRest restAbove spec boundaryEq suffixEq]
  have finalizedCoefficient :
      (((Real.cos
          ((shuklaVedulaNegativeSplitAngle left right).uniformValue / 2) : ℝ) :
            ℂ) *
        ((Real.sqrt (((left + right : Nat) : ℝ) / left) /
          Real.sqrt validCount : ℝ) : ℂ)) =
        ((1 / Real.sqrt validCount : ℝ) : ℂ) := by
    norm_cast
    exact shuklaVedulaFinalizedCoefficient left right validCount leftPositive
      totalPositive
  have activeCoefficient :
      (((((1 / Real.sqrt 2 : ℝ) : ℂ) ^
            (next.val - current.val))) *
        (((-Real.sin
          ((shuklaVedulaNegativeSplitAngle left right).uniformValue / 2) : ℝ) :
            ℂ) *
          ((Real.sqrt (((left + right : Nat) : ℝ) / left) /
            Real.sqrt validCount : ℝ) : ℂ))) =
        ((Real.sqrt
            ((right : ℝ) /
              (left * 2 ^ (next.val - current.val) : Nat)) /
          Real.sqrt validCount : ℝ) : ℂ) := by
    norm_cast
    exact shuklaVedulaNextActiveCoefficient left right
      (next.val - current.val) validCount leftPositive totalPositive
  rw [finalizedCoefficient, activeCoefficient]

/-- Specializing the tail head to the negative split angle gives the final
uniform amplitude on the completed block and the correctly normalized next
active block. -/
theorem applyOperator_shuklaVedulaTailHead_boundaryBlockState_normalized
    {width : Nat} (current next : Fin width)
    (currentBeforeNext : current.val < next.val)
    (rest : List (Fin width))
    (nextOutsideRest : next ∉ rest)
    (restAbove : ∀ wire, wire ∈ rest → next.val ≤ wire.val)
    (spec : ShuklaVedulaBoundaryBlockSpec width)
    (boundaryEq : spec.boundary = current.val)
    (suffixEq : spec.suffix = next :: rest)
    (currentOutside : current ∉ spec.suffix)
    (left right validCount : Nat) (leftPositive : 0 < left)
    (totalPositive : 0 < left + right) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          (zeroControlledRySourcePlan current next
              (shuklaVedulaNegativeSplitAngle left right) ++
            (widthOnlyWireInterval width current.val next.val).flatMap
              (zeroControlledHadamardSourcePlan next)))
        (shuklaVedulaBoundaryBlockState spec
          ((Real.sqrt (((left + right : Nat) : ℝ) / left) /
            Real.sqrt validCount : ℝ) : ℂ)) =
      shuklaVedulaBoundaryBlockState spec
          ((1 / Real.sqrt validCount : ℝ) : ℂ) +
        shuklaVedulaBoundaryBlockState
          ((spec.withSuffix rest).withBoundary next.val next.isLt.le)
          ((Real.sqrt
              ((right : ℝ) /
                (left * 2 ^ (next.val - current.val) : Nat)) /
            Real.sqrt validCount : ℝ) : ℂ) := by
  rw [applyOperator_shuklaVedulaTailHead_boundaryBlockState current next
    currentBeforeNext rest nextOutsideRest restAbove spec boundaryEq suffixEq
    currentOutside (shuklaVedulaNegativeSplitAngle left right)]
  have finalizedCoefficient :
      (((Real.cos
          ((shuklaVedulaNegativeSplitAngle left right).uniformValue / 2) : ℝ) :
            ℂ) *
        ((Real.sqrt (((left + right : Nat) : ℝ) / left) /
          Real.sqrt validCount : ℝ) : ℂ)) =
        ((1 / Real.sqrt validCount : ℝ) : ℂ) := by
    norm_cast
    exact shuklaVedulaFinalizedCoefficient left right validCount leftPositive
      totalPositive
  have activeCoefficient :
      (((((1 / Real.sqrt 2 : ℝ) : ℂ) ^
            (next.val - current.val))) *
        (((-Real.sin
          ((shuklaVedulaNegativeSplitAngle left right).uniformValue / 2) : ℝ) :
            ℂ) *
          ((Real.sqrt (((left + right : Nat) : ℝ) / left) /
            Real.sqrt validCount : ℝ) : ℂ))) =
        ((Real.sqrt
            ((right : ℝ) /
              (left * 2 ^ (next.val - current.val) : Nat)) /
          Real.sqrt validCount : ℝ) : ℂ) := by
    norm_cast
    exact shuklaVedulaNextActiveCoefficient left right
      (next.val - current.val) validCount leftPositive totalPositive
  rw [finalizedCoefficient, activeCoefficient]

/-- Starting from the normalized active block, the recursive tail plan emits
one final uniform block per increasing one-bit location. -/
theorem applyOperator_shuklaVedulaUniformTailPlan_activeBlock
    {width : Nat} (validCount accumulated : Nat)
    (current : Fin width) (rest : List (Fin width))
    (sorted : (current :: rest).Pairwise fun left right =>
      left.val < right.val)
    (powerSum : shuklaVedulaLocationPowerSum (current :: rest) =
      validCount - accumulated) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          (shuklaVedulaUniformTailPlan validCount accumulated
            (current :: rest)))
        (shuklaVedulaBoundaryBlockState
          (shuklaVedulaLocationBlockSpec current rest)
          ((Real.sqrt
              (((validCount - accumulated : Nat) : ℝ) /
                (2 ^ current.val : Nat)) /
            Real.sqrt validCount : ℝ) : ℂ)) =
      shuklaVedulaUniformBlockSum (validCount := validCount)
        (current :: rest) := by
  induction rest generalizing current accumulated with
  | nil =>
      have remainingEq : validCount - accumulated = 2 ^ current.val := by
        simpa [shuklaVedulaLocationPowerSum] using powerSum.symm
      have blockPositive : (0 : ℝ) < (2 ^ current.val : Nat) := by
        exact_mod_cast (pow_pos (by omega : 0 < (2 : Nat)) current.val)
      have amplitudeEq :
          Real.sqrt
                (((validCount - accumulated : Nat) : ℝ) /
                  (2 ^ current.val : Nat)) /
              Real.sqrt validCount =
            1 / Real.sqrt validCount := by
        rw [remainingEq]
        norm_num [ne_of_gt blockPositive]
      have amplitudeEqComplex :
          ((Real.sqrt
                (((validCount - accumulated : Nat) : ℝ) /
                  (2 ^ current.val : Nat)) /
              Real.sqrt validCount : ℝ) : ℂ) =
            ((1 / Real.sqrt validCount : ℝ) : ℂ) := by
        norm_cast
      rw [amplitudeEqComplex]
      simp [shuklaVedulaUniformTailPlan,
        ExternallyControlledPrimitivePlan.sourcePlanOperator,
        operatorSequence, applyOperator, shuklaVedulaUniformBlockSum]
  | cons next rest inductionHypothesis =>
      have pairwise := List.pairwise_cons.mp sorted
      have currentBeforeNext : current.val < next.val :=
        pairwise.1 next (by simp)
      have tailSorted :
          (next :: rest).Pairwise fun left right => left.val < right.val :=
        pairwise.2
      let block := 2 ^ current.val
      let remaining := validCount - accumulated
      have blockPositive : 0 < block := by
        exact pow_pos (by omega : 0 < (2 : Nat)) current.val
      have powerSumStep :
          block + shuklaVedulaLocationPowerSum (next :: rest) = remaining := by
        simpa [shuklaVedulaLocationPowerSum, block, remaining] using powerSum
      have blockLeRemaining : block ≤ remaining := by omega
      have remainingPositive : 0 < remaining :=
        lt_of_lt_of_le blockPositive blockLeRemaining
      have totalEq : block + (remaining - block) = remaining := by omega
      have recursiveRemaining :
          validCount - (accumulated + block) = remaining - block := by
        dsimp [remaining]
        omega
      have recursivePowerSum :
          shuklaVedulaLocationPowerSum (next :: rest) =
            validCount - (accumulated + block) := by
        rw [recursiveRemaining]
        omega
      have blockTimesGap :
          block * 2 ^ (next.val - current.val) = 2 ^ next.val := by
        dsimp [block]
        rw [← pow_add]
        congr 1
        omega
      have nextOutsideRest : next ∉ rest := by
        intro member
        have strict := (List.pairwise_cons.mp tailSorted).1 next member
        omega
      have restAbove : ∀ wire, wire ∈ rest → next.val ≤ wire.val := by
        intro wire member
        exact ((List.pairwise_cons.mp tailSorted).1 wire member).le
      let spec := shuklaVedulaLocationBlockSpec current (next :: rest)
      have boundaryEq : spec.boundary = current.val := rfl
      have suffixEq : spec.suffix = next :: rest := rfl
      have currentOutside : current ∉ spec.suffix := by
        intro member
        have strict := pairwise.1 current member
        omega
      have headResult :=
        applyOperator_shuklaVedulaTailHead_boundaryBlockState_normalized
          current next currentBeforeNext rest nextOutsideRest restAbove spec
          boundaryEq suffixEq currentOutside block (remaining - block)
          validCount blockPositive (by omega)
      have planEq :
          shuklaVedulaUniformTailPlan validCount accumulated
              (current :: next :: rest) =
            (zeroControlledRySourcePlan current next
                (shuklaVedulaNegativeSplitAngle block (remaining - block)) ++
              (widthOnlyWireInterval width current.val next.val).flatMap
                (zeroControlledHadamardSourcePlan next)) ++
              shuklaVedulaUniformTailPlan validCount
                (accumulated + block) (next :: rest) := by
        simp [shuklaVedulaUniformTailPlan, block, remaining,
          List.append_assoc]
      rw [planEq,
        ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
        applyOperator_mul]
      have normalizedInput :
          ((Real.sqrt
              (((validCount - accumulated : Nat) : ℝ) /
                (2 ^ current.val : Nat)) /
            Real.sqrt validCount : ℝ) : ℂ) =
          ((Real.sqrt (((block + (remaining - block) : Nat) : ℝ) / block) /
            Real.sqrt validCount : ℝ) : ℂ) := by
        rw [totalEq]
      rw [normalizedInput, headResult, applyOperator_add]
      have controlsAbove : ∀ wire, wire ∈ next :: rest →
          spec.boundary ≤ wire.val := by
        intro wire member
        exact (pairwise.1 wire member).le
      have controlsMember : ∀ wire, wire ∈ next :: rest →
          wire ∈ spec.suffix := by
        intro wire member
        exact member
      rw [applyOperator_shuklaVedulaUniformTailPlan_boundaryBlockState_controls_true
          validCount (accumulated + block) (next :: rest) tailSorted spec
          controlsAbove controlsMember]
      have recursiveResult := inductionHypothesis
        (accumulated + block) next tailSorted recursivePowerSum
      have activeSpec :
          ((spec.withSuffix rest).withBoundary next.val next.isLt.le) =
            shuklaVedulaLocationBlockSpec next rest := by
        rfl
      rw [activeSpec, blockTimesGap, ← recursiveRemaining, recursiveResult]
      rfl

/-- A location block is exactly the half-open numeric interval beginning at
the power sum of its higher one-bit suffix. -/
theorem shuklaVedulaLocationBlockSpec_matches_iff_index_interval
    {width : Nat} (current : Fin width) (rest : List (Fin width))
    (sorted : (current :: rest).Pairwise fun left right =>
      left.val < right.val)
    (basis : QubitBasis width) :
    (shuklaVedulaLocationBlockSpec current rest).Matches basis ↔
      shuklaVedulaLocationPowerSum rest ≤
          qubitBasisLittleEndianIndex width basis ∧
        qubitBasisLittleEndianIndex width basis <
          shuklaVedulaLocationPowerSum rest + 2 ^ current.val := by
  let index := qubitBasisLittleEndianIndex width basis
  let base := shuklaVedulaLocationPowerSum rest
  let power := 2 ^ current.val
  have pairwise := List.pairwise_cons.mp sorted
  have restSorted : rest.Pairwise fun left right => left.val < right.val :=
    pairwise.2
  have restAbove : ∀ wire, wire ∈ rest → current.val ≤ wire.val := by
    intro wire member
    exact (pairwise.1 wire member).le
  have baseBits : base.bitIndices = rest.map Fin.val := by
    exact shuklaVedulaLocationPowerSum_bitIndices rest restSorted
  have baseBitEq (wire : Fin width) :
      base.testBit wire.val = decide (wire ∈ rest) := by
    have bitIff : base.testBit wire.val = true ↔ wire ∈ rest := by
      rw [← Nat.mem_bitIndices, baseBits]
      constructor
      · intro member
        rcases List.mem_map.mp member with ⟨item, itemMember, itemValue⟩
        have itemEq : item = wire := Fin.ext itemValue
        simpa [itemEq] using itemMember
      · intro member
        exact List.mem_map.mpr ⟨wire, member, rfl⟩
    by_cases member : wire ∈ rest
    · have bitTrue := bitIff.mpr member
      simp [member, bitTrue]
    · have bitNotTrue : base.testBit wire.val ≠ true := by
        intro bitTrue
        exact member (bitIff.mp bitTrue)
      have bitFalse : base.testBit wire.val = false :=
        Bool.eq_false_of_not_eq_true bitNotTrue
      simp [member, bitFalse]
  let factor :=
    (rest.map fun wire => 2 ^ (wire.val - current.val)).sum
  have baseEq : base = power * factor := by
    exact shuklaVedulaLocationPowerSum_factor current.val rest restAbove
  have powerPositive : 0 < power :=
    pow_pos (by omega : 0 < (2 : Nat)) current.val
  have baseDiv : base / power = factor := by
    rw [baseEq]
    exact Nat.mul_div_cancel_left factor powerPositive
  have divEq_iff_matches :
      index / power = base / power ↔
        (shuklaVedulaLocationBlockSpec current rest).Matches basis := by
    constructor
    · intro divEq wire above
      have currentLeWire : current.val ≤ wire.val := by
        simpa [shuklaVedulaLocationBlockSpec] using above
      let offset := wire.val - current.val
      have valueEq : current.val + offset = wire.val := by
        dsimp [offset]
        omega
      have shiftedEq : index >>> current.val = base >>> current.val := by
        simpa [Nat.shiftRight_eq_div_pow, power] using divEq
      have shiftedBitEq := congrArg (fun value => value.testBit offset) shiftedEq
      have indexBit : index.testBit wire.val = basis wire := by
        dsimp [index]
        exact qubitBasisLittleEndianIndex_testBit basis wire
      have originalBitEq : index.testBit wire.val = base.testBit wire.val := by
        calc
          index.testBit wire.val = index.testBit (current.val + offset) := by
            rw [valueEq]
          _ = (index >>> current.val).testBit offset := by
            rw [Nat.testBit_shiftRight]
          _ = (base >>> current.val).testBit offset := shiftedBitEq
          _ = base.testBit (current.val + offset) :=
            Nat.testBit_shiftRight base
          _ = base.testBit wire.val := by rw [valueEq]
      rw [← indexBit, originalBitEq, baseBitEq]
      rfl
    · intro matching
      have shiftedEq : index >>> current.val = base >>> current.val := by
        apply Nat.eq_of_testBit_eq
        intro offset
        let value := current.val + offset
        by_cases inside : value < width
        · let wire : Fin width := ⟨value, inside⟩
          have indexBit : index.testBit value = basis wire := by
            dsimp [index, wire, value]
            exact qubitBasisLittleEndianIndex_testBit basis wire
          have blockBit : basis wire = decide (wire ∈ rest) := by
            exact matching wire (by
              simp [shuklaVedulaLocationBlockSpec, wire, value])
          have baseBit : base.testBit value = decide (wire ∈ rest) := by
            simpa [wire, value] using baseBitEq wire
          calc
            (index >>> current.val).testBit offset =
                index.testBit value := Nat.testBit_shiftRight index
            _ = basis wire := indexBit
            _ = decide (wire ∈ rest) := blockBit
            _ = base.testBit value := baseBit.symm
            _ = (base >>> current.val).testBit offset :=
              (Nat.testBit_shiftRight base).symm
        · have widthLeValue : width ≤ value := Nat.le_of_not_gt inside
          have indexBound : index < 2 ^ value := by
            exact lt_of_lt_of_le (qubitBasisLittleEndianIndex_lt basis)
              (Nat.pow_le_pow_right (by decide) widthLeValue)
          have indexFalse : index.testBit value = false :=
            Nat.testBit_lt_two_pow indexBound
          have baseNotTrue : base.testBit value ≠ true := by
            intro bitTrue
            have valueMember : value ∈ rest.map Fin.val := by
              rw [← baseBits]
              exact Nat.mem_bitIndices.mpr bitTrue
            rcases List.mem_map.mp valueMember with ⟨wire, _, wireValue⟩
            have wireBelow : wire.val < width := wire.isLt
            omega
          have baseFalse : base.testBit value = false :=
            Bool.eq_false_of_not_eq_true baseNotTrue
          rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight,
            indexFalse, baseFalse]
      simpa [Nat.shiftRight_eq_div_pow, power] using shiftedEq
  constructor
  · intro matching
    have divEq := divEq_iff_matches.mpr matching
    have indexDiv : index / power = factor := by rw [divEq, baseDiv]
    have indexDecomposition := Nat.mod_add_div index power
    have remainderBound := Nat.mod_lt index powerPositive
    have indexEq : index = base + index % power := by
      rw [indexDiv] at indexDecomposition
      rw [baseEq]
      omega
    dsimp [index, base, power] at indexEq remainderBound ⊢
    omega
  · intro interval
    have lower : factor * power ≤ index := by
      rw [Nat.mul_comm, ← baseEq]
      exact interval.1
    have upper : index < (factor + 1) * power := by
      rw [Nat.add_mul, one_mul, Nat.mul_comm factor power, ← baseEq]
      exact interval.2
    have indexDiv : index / power = factor :=
      Nat.div_eq_of_lt_le lower upper
    apply divEq_iff_matches.mp
    rw [indexDiv, baseDiv]

/-- The disjoint block sum is the constant-amplitude state on the initial
numeric interval determined by the location power sum. -/
theorem shuklaVedulaUniformBlockSum_apply
    {width validCount : Nat} (locations : List (Fin width))
    (sorted : locations.Pairwise fun left right => left.val < right.val)
    (basis : QubitBasis width) :
    shuklaVedulaUniformBlockSum (validCount := validCount) locations basis =
      if qubitBasisLittleEndianIndex width basis <
          shuklaVedulaLocationPowerSum locations then
        ((1 / Real.sqrt validCount : ℝ) : ℂ)
      else 0 := by
  classical
  induction locations with
  | nil => simp [shuklaVedulaUniformBlockSum,
      shuklaVedulaLocationPowerSum]
  | cons current rest inductionHypothesis =>
      have pairwise := List.pairwise_cons.mp sorted
      have restSorted : rest.Pairwise fun left right => left.val < right.val :=
        pairwise.2
      have recursive := inductionHypothesis restSorted
      let index := qubitBasisLittleEndianIndex width basis
      let base := shuklaVedulaLocationPowerSum rest
      let power := 2 ^ current.val
      have powerPositive : 0 < power :=
        pow_pos (by omega : 0 < (2 : Nat)) current.val
      have blockIff :=
        shuklaVedulaLocationBlockSpec_matches_iff_index_interval current rest
          sorted basis
      have blockIffLet :
          (shuklaVedulaLocationBlockSpec current rest).Matches basis ↔
            base ≤ index ∧ index < base + power := by
        simpa [index, base, power] using blockIff
      simp only [shuklaVedulaUniformBlockSum, Pi.add_apply,
        shuklaVedulaBoundaryBlockState]
      rw [recursive]
      change (if (shuklaVedulaLocationBlockSpec current rest).Matches basis
          then ((1 / Real.sqrt validCount : ℝ) : ℂ) else 0) +
          (if index < base then ((1 / Real.sqrt validCount : ℝ) : ℂ) else 0) =
        (if index < power + base then
          ((1 / Real.sqrt validCount : ℝ) : ℂ) else 0)
      rw [blockIffLet]
      by_cases belowBase : index < base
      · have outsideBlock : ¬(base ≤ index ∧ index < base + power) := by omega
        have belowTotal : index < power + base := by omega
        simp [belowBase, outsideBlock, belowTotal]
      · have baseLe : base ≤ index := Nat.le_of_not_gt belowBase
        by_cases belowTotal : index < power + base
        · have insideBlock : base ≤ index ∧ index < base + power := by omega
          simp [belowBase, belowTotal, insideBlock]
        · have outsideBlock : ¬(base ≤ index ∧ index < base + power) := by
            omega
          simp [belowBase, belowTotal, outsideBlock]

/-- For a strict-bound count, the attached one-location block sum is exactly
the independent uniform target state. -/
theorem shuklaVedulaUniformBlockSum_oneLocations_eq_target
    (parameters : UniformPreparationParameters)
    (strictBound : parameters.validCount < 2 ^ parameters.width) :
    shuklaVedulaUniformBlockSum (validCount := parameters.validCount)
        (widthOnlyUniformOneLocationsOfStrictBound parameters.width
          parameters.validCount strictBound) =
      uniformPreparationTargetState parameters := by
  funext basis
  let locations := widthOnlyUniformOneLocationsOfStrictBound parameters.width
    parameters.validCount strictBound
  have values := widthOnlyUniformOneLocationsOfStrictBound_values
    parameters.width parameters.validCount strictBound
  have sorted : locations.Pairwise fun left right => left.val < right.val := by
    have valueSorted :
        (locations.map Fin.val).Pairwise fun left right => left < right := by
      rw [values]
      exact Nat.bitIndices_sorted.pairwise
    simpa only [List.pairwise_map] using valueSorted
  rw [shuklaVedulaUniformBlockSum_apply locations sorted basis]
  rw [shuklaVedulaLocationPowerSum_oneLocationsOfStrictBound]
  rfl

/-- The complete source-order plan for a strict-bound count with at least two
nonzero binary digits maps the all-zero ket to its disjoint uniform block
sum.  This theorem keeps the implementation product and independent block
target separate until the final equality. -/
theorem applyOperator_shuklaVedulaExpandedThreeOrMorePlan_zeroKet
    {width validCount : Nat} (validCountPositive : 0 < validCount)
    (first second : Fin width) (rest : List (Fin width))
    (sorted : (first :: second :: rest).Pairwise fun left right =>
      left.val < right.val)
    (powerSum : shuklaVedulaLocationPowerSum (first :: second :: rest) =
      validCount) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          (((second :: rest).map ExternallyControlledPrimitivePlan.x ++
              (widthOnlyWireInterval width 0 first.val).map
                ExternallyControlledPrimitivePlan.h) ++
            ([.ry
                (shuklaVedulaNegativeSplitAngle (2 ^ first.val)
                  (validCount - 2 ^ first.val)) second] ++
              (widthOnlyWireInterval width first.val second.val).flatMap
                (zeroControlledHadamardSourcePlan second)) ++
            shuklaVedulaUniformTailPlan validCount (2 ^ first.val)
              (second :: rest)))
        (basisKet (fun _ => false : QubitBasis width)) =
      shuklaVedulaUniformBlockSum (validCount := validCount)
        (first :: second :: rest) := by
  let firstBlock := 2 ^ first.val
  let remaining := validCount - firstBlock
  let firstSpec := shuklaVedulaLocationBlockSpec first (second :: rest)
  have pairwise := List.pairwise_cons.mp sorted
  have firstBeforeSecond : first.val < second.val :=
    pairwise.1 second (by simp)
  have tailSorted :
      (second :: rest).Pairwise fun left right => left.val < right.val :=
    pairwise.2
  have nextOutsideRest : second ∉ rest := by
    intro member
    have strict := (List.pairwise_cons.mp tailSorted).1 second member
    omega
  have restAbove : ∀ wire, wire ∈ rest → second.val ≤ wire.val := by
    intro wire member
    exact ((List.pairwise_cons.mp tailSorted).1 wire member).le
  have powerSumStep :
      firstBlock + shuklaVedulaLocationPowerSum (second :: rest) =
        validCount := by
    simpa [shuklaVedulaLocationPowerSum, firstBlock] using powerSum
  have firstBlockPositive : 0 < firstBlock := by
    exact pow_pos (by omega : 0 < (2 : Nat)) first.val
  have firstBlockLe : firstBlock ≤ validCount := by omega
  have totalEq : firstBlock + remaining = validCount := by
    dsimp [remaining]
    omega
  have tailPowerSum :
      shuklaVedulaLocationPowerSum (second :: rest) =
        validCount - firstBlock := by omega
  have blockTimesGap :
      firstBlock * 2 ^ (second.val - first.val) = 2 ^ second.val := by
    dsimp [firstBlock]
    rw [← pow_add]
    congr 1
    omega
  have prefixResult :=
    applyOperator_shuklaVedulaInitialPrefix_zeroKet_normalized
      validCountPositive first second rest sorted
  have headResult :=
    applyOperator_shuklaVedulaInitialHead_boundaryBlockState_normalized
      first second firstBeforeSecond rest nextOutsideRest restAbove firstSpec
      rfl rfl firstBlock remaining validCount firstBlockPositive (by omega)
  rw [ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
    applyOperator_mul,
    ExternallyControlledPrimitivePlan.sourcePlanOperator_append,
    applyOperator_mul,
    prefixResult]
  have prefixAmplitude :
      ((Real.sqrt ((validCount : ℝ) / firstBlock) /
        Real.sqrt validCount : ℝ) : ℂ) =
      ((Real.sqrt (((firstBlock + remaining : Nat) : ℝ) / firstBlock) /
        Real.sqrt validCount : ℝ) : ℂ) := by
    rw [totalEq]
  rw [prefixAmplitude, headResult, applyOperator_add]
  have controlsAbove : ∀ wire, wire ∈ second :: rest →
      firstSpec.boundary ≤ wire.val := by
    intro wire member
    exact (pairwise.1 wire member).le
  have controlsMember : ∀ wire, wire ∈ second :: rest →
      wire ∈ firstSpec.suffix := by
    intro wire member
    exact member
  rw [applyOperator_shuklaVedulaUniformTailPlan_boundaryBlockState_controls_true
      validCount firstBlock (second :: rest) tailSorted firstSpec
      controlsAbove controlsMember]
  have activeSpec :
      ((firstSpec.withSuffix rest).withBoundary second.val second.isLt.le) =
        shuklaVedulaLocationBlockSpec second rest := by
    rfl
  rw [activeSpec, blockTimesGap]
  rw [applyOperator_shuklaVedulaUniformTailPlan_activeBlock validCount
    firstBlock second rest tailSorted tailPowerSum]
  rfl

/-- For a strict power-of-two count, the initial Hadamard prefix alone
prepares the independent uniform target. -/
theorem applyOperator_shuklaVedulaPowerOfTwoPrefix_zeroKet
    (parameters : UniformPreparationParameters)
    (only : Fin parameters.width)
    (countEq : parameters.validCount = 2 ^ only.val) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          ((widthOnlyWireInterval parameters.width 0 only.val).map
            ExternallyControlledPrimitivePlan.h))
        (basisKet (fun _ => false : QubitBasis parameters.width)) =
      uniformPreparationTargetState parameters := by
  have intervalResult :=
    applyOperator_hadamardInterval_boundaryBlockState
      0 only.val only.val (by omega) only.isLt.le
      (shuklaVedulaZeroBoundaryBlockSpec ([] : List (Fin parameters.width)))
      rfl (by simp [shuklaVedulaZeroBoundaryBlockSpec]) (1 : ℂ)
  rw [show
      shuklaVedulaBoundaryBlockState
          ((shuklaVedulaZeroBoundaryBlockSpec
            ([] : List (Fin parameters.width))).withBoundary only.val
              only.isLt.le)
          ((((1 / Real.sqrt 2 : ℝ) : ℂ) ^ only.val) * 1) =
        shuklaVedulaBoundaryBlockState
          (shuklaVedulaLocationBlockSpec only [])
          ((1 / Real.sqrt parameters.validCount : ℝ) : ℂ) by
    rw [mul_one]
    have realAmplitude := inverseSqrtTwoPow_eq_inverseSqrt_pow only.val
    rw [countEq]
    exact congrArg (fun amplitude : ℂ =>
      shuklaVedulaBoundaryBlockState
        (shuklaVedulaLocationBlockSpec only []) amplitude)
      (by exact_mod_cast realAmplitude)] at intervalResult
  have zeroKetEq :
      basisKet (fun _ => false : QubitBasis parameters.width) =
        shuklaVedulaBoundaryBlockState
          (shuklaVedulaZeroBoundaryBlockSpec
            ([] : List (Fin parameters.width))) 1 := by
    rw [shuklaVedulaBoundaryBlockState_zeroBoundary_eq_basisKet]
    congr 1
  rw [zeroKetEq]
  rw [intervalResult]
  calc
    shuklaVedulaBoundaryBlockState
        (shuklaVedulaLocationBlockSpec only [])
        ((1 / Real.sqrt parameters.validCount : ℝ) : ℂ) =
        shuklaVedulaUniformBlockSum
          (validCount := parameters.validCount) [only] := by
      simp [shuklaVedulaUniformBlockSum]
    _ = uniformPreparationTargetState parameters := by
      funext basis
      rw [shuklaVedulaUniformBlockSum_apply [only] (by simp) basis]
      simp [shuklaVedulaLocationPowerSum, countEq,
        uniformPreparationTargetState]

/-- At full capacity, the all-H branch prepares the uniform state on every
computational basis vector. -/
theorem applyOperator_shuklaVedulaFullCapacityPlan_zeroKet
    (parameters : UniformPreparationParameters)
    (full : parameters.validCount = 2 ^ parameters.width) :
    applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          ((widthOnlyWireInterval parameters.width 0 parameters.width).map
            ExternallyControlledPrimitivePlan.h))
        (basisKet (fun _ => false : QubitBasis parameters.width)) =
      uniformPreparationTargetState parameters := by
  let initialSpec :=
    shuklaVedulaZeroBoundaryBlockSpec
      ([] : List (Fin parameters.width))
  let terminalSpec := initialSpec.withBoundary parameters.width (Nat.le_refl _)
  have intervalResult :=
    applyOperator_hadamardInterval_boundaryBlockState
      0 parameters.width parameters.width (by omega) (Nat.le_refl _)
      initialSpec rfl
      (by simp [initialSpec, shuklaVedulaZeroBoundaryBlockSpec]) (1 : ℂ)
  rw [show initialSpec.withBoundary parameters.width (Nat.le_refl _) =
      terminalSpec by rfl] at intervalResult
  have zeroKetEq :
      basisKet (fun _ => false : QubitBasis parameters.width) =
        shuklaVedulaBoundaryBlockState initialSpec 1 := by
    dsimp [initialSpec]
    rw [shuklaVedulaBoundaryBlockState_zeroBoundary_eq_basisKet]
    congr 1
  rw [zeroKetEq]
  change applyOperator
      (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        ((widthOnlyWireInterval parameters.width 0 parameters.width).map
          ExternallyControlledPrimitivePlan.h))
      (shuklaVedulaBoundaryBlockState initialSpec 1) = _
  rw [intervalResult]
  funext basis
  have matching : terminalSpec.Matches basis := by
    intro wire above
    have impossible : ¬ parameters.width ≤ wire.val := by omega
    exact (impossible above).elim
  have inside :
      qubitBasisLittleEndianIndex parameters.width basis <
        parameters.validCount := by
    rw [full]
    exact qubitBasisLittleEndianIndex_lt basis
  have realAmplitude := inverseSqrtTwoPow_eq_inverseSqrt_pow parameters.width
  simp only [shuklaVedulaBoundaryBlockState, matching, if_true, mul_one,
    uniformPreparationTargetState, inside]
  exact_mod_cast (show
    (1 / Real.sqrt 2 : ℝ) ^ parameters.width =
      1 / Real.sqrt parameters.validCount by
    rw [realAmplitude, full])

/-- The independent strict full-space target of the width-only source plan
prepares the uniform target on the all-zero input for every admissible count. -/
theorem applyOperator_shuklaVedulaWidthOnlyUniformStrictOperator_zeroKet
    (parameters : UniformPreparationParameters) :
    applyOperator
        (shuklaVedulaWidthOnlyUniformStrictOperator (fun _ => 0) parameters)
        (basisKet (fun _ => false : QubitBasis parameters.width)) =
      uniformPreparationTargetState parameters := by
  unfold shuklaVedulaWidthOnlyUniformStrictOperator
  by_cases full : parameters.validCount = 2 ^ parameters.width
  · simp only [shuklaVedulaWidthOnlyUniformPlan, full, dif_pos]
    exact applyOperator_shuklaVedulaFullCapacityPlan_zeroKet parameters full
  · let strictBound : parameters.validCount < 2 ^ parameters.width :=
      lt_of_le_of_ne parameters.validCountLeCapacity full
    let locations := widthOnlyUniformOneLocationsOfStrictBound
      parameters.width parameters.validCount strictBound
    have locationsPower : shuklaVedulaLocationPowerSum locations =
        parameters.validCount := by
      exact shuklaVedulaLocationPowerSum_oneLocationsOfStrictBound
        parameters.width parameters.validCount strictBound
    have locationValues : locations.map Fin.val =
        parameters.validCount.bitIndices := by
      exact widthOnlyUniformOneLocationsOfStrictBound_values
        parameters.width parameters.validCount strictBound
    have locationsSorted :
        locations.Pairwise fun left right => left.val < right.val := by
      have valueSorted :
          (locations.map Fin.val).Pairwise fun left right => left < right := by
        rw [locationValues]
        exact Nat.bitIndices_sorted.pairwise
      simpa only [List.pairwise_map] using valueSorted
    simp only [shuklaVedulaWidthOnlyUniformPlan, full]
    change applyOperator
        (ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
          (match locations with
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
                (widthOnlyWireInterval parameters.width first.val
                  second.val).flatMap
                    (zeroControlledHadamardSourcePlan second) ++
                shuklaVedulaUniformTailPlan parameters.validCount firstBlock
                  (second :: rest)))
        (basisKet (fun _ => false : QubitBasis parameters.width)) =
      uniformPreparationTargetState parameters
    cases locationsEq : locations with
    | nil =>
        have validCountZero : parameters.validCount = 0 := by
          rw [← locationsPower, locationsEq]
          rfl
        have positive := parameters.validCountPositive
        omega
    | cons first tail =>
        cases tailEq : tail with
        | nil =>
            have countEq : parameters.validCount = 2 ^ first.val := by
              rw [← locationsPower, locationsEq, tailEq]
              simp [shuklaVedulaLocationPowerSum]
            simpa [locationsEq, tailEq] using
              applyOperator_shuklaVedulaPowerOfTwoPrefix_zeroKet parameters
                first countEq
        | cons second rest =>
            have sortedCase :
                (first :: second :: rest).Pairwise fun left right =>
                  left.val < right.val := by
              simpa [locationsEq, tailEq] using locationsSorted
            have powerCase :
                shuklaVedulaLocationPowerSum (first :: second :: rest) =
                  parameters.validCount := by
              simpa [locationsEq, tailEq] using locationsPower
            have expanded :=
              applyOperator_shuklaVedulaExpandedThreeOrMorePlan_zeroKet
                parameters.validCountPositive first second rest sortedCase
                  powerCase
            have blockTarget :=
              shuklaVedulaUniformBlockSum_oneLocations_eq_target parameters
                strictBound
            change shuklaVedulaUniformBlockSum (validCount :=
                parameters.validCount) locations =
              uniformPreparationTargetState parameters at blockTarget
            rw [locationsEq, tailEq] at blockTarget
            simpa [locationsEq, tailEq, List.append_assoc] using
              expanded.trans blockTarget

/-- The public source-order primitive circuit prepares the independent
uniform target on the all-zero input.  The first edge uses the public
full-space Exact child contract; only the second edge specializes its
independent strict target to the all-zero state. -/
theorem shuklaVedulaWidthOnlyUniformCircuit_correct_state
    (parameters : UniformPreparationParameters) :
    applyOperator
        ((shuklaVedulaWidthOnlyUniformCircuit parameters).denote
          (primitiveGateOperatorWithSymbols (qubits := parameters.width) (fun _ => 0)))
        (basisKet (fun _ => false : QubitBasis parameters.width)) =
      uniformPreparationTargetState parameters := by
  have operatorCorrect :
      (shuklaVedulaWidthOnlyUniformCircuit parameters).denote
          (primitiveGateOperatorWithSymbols (qubits := parameters.width) (fun _ => 0)) =
        shuklaVedulaWidthOnlyUniformStrictOperator (fun _ => 0) parameters := by
    rw [← shuklaVedulaWidthOnlyUniformFullExactOperatorComponent_circuit,
      ← shuklaVedulaWidthOnlyUniformFullExactOperatorComponent_target]
    exact (shuklaVedulaWidthOnlyUniformFullExactOperatorComponent
      (fun _ => 0) parameters).correct
  calc
    applyOperator
        ((shuklaVedulaWidthOnlyUniformCircuit parameters).denote
          (primitiveGateOperatorWithSymbols (qubits := parameters.width) (fun _ => 0)))
        (basisKet (fun _ => false : QubitBasis parameters.width)) =
      applyOperator
        (shuklaVedulaWidthOnlyUniformStrictOperator (fun _ => 0) parameters)
        (basisKet (fun _ => false : QubitBasis parameters.width)) :=
      congrArg (fun operator => applyOperator operator
        (basisKet (fun _ => false : QubitBasis parameters.width)))
        operatorCorrect
    _ = uniformPreparationTargetState parameters :=
      applyOperator_shuklaVedulaWidthOnlyUniformStrictOperator_zeroKet
        parameters

/-- Source-faithful width-only Shukla--Vedula state-preparation contract. -/
def shuklaVedulaWidthOnlyUniformStatePreparationComponent
    (parameters : UniformPreparationParameters) :
    StatePreparationComponent
      (Gate := PrimitiveGate parameters.width)
      (basis := QubitBasis parameters.width)
      (primitiveGateOperatorWithSymbols (qubits := parameters.width) (fun _ => 0)) where
  circuit := shuklaVedulaWidthOnlyUniformCircuit parameters
  initialState := basisKet (fun _ => false : QubitBasis parameters.width)
  targetState := uniformPreparationTargetState parameters
  correct := shuklaVedulaWidthOnlyUniformCircuit_correct_state parameters

end

end VerifiedCircuitCore
