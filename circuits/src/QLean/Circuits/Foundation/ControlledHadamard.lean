import QLean.Circuits.Foundation.ControlledHadamardAnalytic
import QLean.Circuits.Foundation.ConstructionMultiControlledRotationCorrectness
import QLean.Circuits.Foundation.PhaseShiftMacros

/-!
# 7 gate controlled-H compilerとsemantic作用

固定二wire局所等式を証明し、任意幅では既存のinjective局所作用素埋込み則だけで
strict compiler積を直接semantic targetへ同定する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- target上の`H-CNOT-H`局所積はcontrolled-Zである。 -/
theorem local_h_cnot_h_eq_controlledZ :
    localOnTarget localH * localCnotOperator * localOnTarget localH =
      localControlledOperator localZ := by
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases outputTarget <;>
    cases inputControl <;> cases inputTarget <;>
    simp [localOnTarget, localH, localCnotOperator, localControlledOperator,
      localZ, Matrix.mul_apply, Matrix.kronecker, Fintype.sum_prod_type]
  all_goals
    have sqrtTwoPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have sqrtTwoNonzero : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt sqrtTwoPositive
    have sqrtTwoSquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    ring_nf
    simp [sqrtTwoSquare]

set_option maxHeartbeats 800000 in
/-- controlled局所作用素は局所作用素積を保存する。 -/
theorem localControlledOperator_mul
    (left right : Matrix Bool Bool ℂ) :
    localControlledOperator left * localControlledOperator right =
      localControlledOperator (left * right) := by
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases outputTarget <;>
    cases inputControl <;> cases inputTarget <;>
    simp [localControlledOperator, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Fixed 2×2 entry used by the arbitrary-width original-basis amplitude theorem. -/
@[simp] theorem localRy_mul_localZ_apply_false_false (angle : ℝ) :
    (localRy (2 * angle) * localZ) false false = Real.cos angle := by
  simp [localRy, localZ, Matrix.mul_apply]

/-- Fixed 2×2 entry used by the arbitrary-width flipped-basis amplitude theorem. -/
@[simp] theorem localRy_mul_localZ_apply_true_false (angle : ℝ) :
    (localRy (2 * angle) * localZ) true false = Real.sin angle := by
  simp [localRy, localZ, Matrix.mul_apply]

set_option maxHeartbeats 800000 in
/-- 7局所作用のstrict積は直接semantic controlled作用に一致する。 -/
theorem controlledHadamardSevenGateLocalProduct_eq_semantic
    (quarterAngle : ℝ) :
    controlledHadamardSevenGateLocalProduct quarterAngle =
      localControlledOperator (localRy (2 * quarterAngle) * localZ) := by
  unfold controlledHadamardSevenGateLocalProduct
  have controlledRy := local_controlledRy_decomposition (2 * quarterAngle)
  simp only [show -(2 * quarterAngle) / 2 = -quarterAngle by ring,
    show (2 * quarterAngle) / 2 = quarterAngle by ring] at controlledRy
  calc
    (localCnotOperator * localOnTarget (localRy (-quarterAngle)) *
          localCnotOperator * localOnTarget (localRy quarterAngle)) *
        (localOnTarget localH * localCnotOperator * localOnTarget localH) =
        localControlledOperator (localRy (2 * quarterAngle)) *
        localControlledOperator localZ := by
          rw [controlledRy, local_h_cnot_h_eq_controlledZ]
    _ = localControlledOperator (localRy (2 * quarterAngle) * localZ) :=
      localControlledOperator_mul _ _

/-- 7基本gateからなる正本AST。 -/
def controlledHadamardSevenGateCircuit {qubits : Nat}
    (spec : ControlledHadamardSevenGateSpec qubits) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.fromList [
    .h spec.target,
    .cnot spec.control spec.target spec.different,
    .h spec.target,
    .ry spec.quarterAngle spec.target,
    .cnot spec.control spec.target spec.different,
    .ry (.neg spec.quarterAngle) spec.target,
    .cnot spec.control spec.target spec.different]

/-- 二wire局所埋込みは実行順作用素列の積を保存する。 -/
theorem embedTwoQubitOperator_operatorSequence {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target) :
    ∀ operators : List (Matrix (Bool × Bool) (Bool × Bool) ℂ),
      operatorSequence
          (operators.map (embedTwoQubitOperator control target different)) =
        embedTwoQubitOperator control target different
          (operatorSequence operators)
  | [] => by
      unfold operatorSequence embedTwoQubitOperator
      simp
  | first :: rest => by
      simp only [List.map_cons, operatorSequence,
        embedTwoQubitOperator_operatorSequence control target different rest]
      rw [← embedTwoQubitOperator_mul]

/-- 7 gate ASTは回路非依存なstrict作用素積に厳密一致する。 -/
theorem controlledHadamardSevenGateCircuit_strict_correct {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledHadamardSevenGateSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledHadamardSevenGateCircuit spec) =
      controlledHadamardSevenGateStrictOperator symbolValue spec := by
  rw [controlledHadamardSevenGateCircuit, Circuit.denote_fromList_eq_operatorSequence]
  simp only [List.map_cons, List.map_nil, primitiveGateOperatorWithSymbols,
    AngleExpr.eval_neg]
  rw [show deterministicOperator
      (fun input => xorWire spec.target (input spec.control) input) =
      analyticCnotOperator spec.control spec.target by rfl]
  rw [analyticCnotOperator_eq_embedTwo_localCnot
    spec.control spec.target spec.different]
  rw [
    ← embedTwoQubitOperator_localOnTarget spec.control spec.target spec.different
      localH,
    ← embedTwoQubitOperator_localOnTarget spec.control spec.target spec.different
      (localRy (spec.quarterAngle.eval symbolValue)),
    ← embedTwoQubitOperator_localOnTarget spec.control spec.target spec.different
      (localRy (-(spec.quarterAngle.eval symbolValue)))]
  change operatorSequence
      (([
        localOnTarget localH,
        localCnotOperator,
        localOnTarget localH,
        localOnTarget (localRy (spec.quarterAngle.eval symbolValue)),
        localCnotOperator,
        localOnTarget (localRy (-(spec.quarterAngle.eval symbolValue))),
        localCnotOperator] :
        List (Matrix (Bool × Bool) (Bool × Bool) ℂ)).map
          (embedTwoQubitOperator spec.control spec.target spec.different)) =
    embedTwoQubitOperator spec.control spec.target spec.different
      (controlledHadamardSevenGateLocalProduct
        (spec.quarterAngle.eval symbolValue))
  rw [embedTwoQubitOperator_operatorSequence]
  apply congrArg (embedTwoQubitOperator spec.control spec.target spec.different)
  simp [controlledHadamardSevenGateLocalProduct, operatorSequence, mul_assoc]

set_option maxHeartbeats 800000 in
/-- 任意wire上のstrict作用素積は直接semantic targetに一致する。 -/
theorem controlledHadamardSevenGateStrictOperator_eq_semantic {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledHadamardSevenGateSpec qubits) :
    controlledHadamardSevenGateStrictOperator symbolValue spec =
      controlledHadamardSemanticOperator symbolValue spec := by
  unfold controlledHadamardSevenGateStrictOperator
  rw [controlledHadamardSevenGateLocalProduct_eq_semantic]
  rfl

/-- 7 gate compilerを直接semantic targetへ結ぶ公開Exact component。 -/
def controlledHadamardSevenGateComponent {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledHadamardSevenGateSpec qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := controlledHadamardSevenGateCircuit spec
  target := controlledHadamardSemanticOperator symbolValue spec
  correct := (controlledHadamardSevenGateCircuit_strict_correct symbolValue spec).trans
    (controlledHadamardSevenGateStrictOperator_eq_semantic symbolValue spec)

/-- 任意のcontrolled局所作用素の行列要素をtarget一wireの疎な式で読む。 -/
theorem embedControlledSingleQubitOperator_apply_sparse
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ) (output input : QubitBasis qubits) :
    embedControlledSingleQubitOperator control target different localOperator
        output input =
      if agreesExcept target output input then
        if input control then localOperator (output target) (input target)
        else if output target = input target then 1 else 0
      else 0 := by
  unfold embedControlledSingleQubitOperator
  rw [embedTwoQubitOperator_apply]
  by_cases outside : agreesExceptTwo control target output input
  · by_cases controlEqual : output control = input control
    · have targetAgreement : agreesExcept target output input := by
        intro wire wireDifferent
        by_cases isControl : wire = control
        · simpa [isControl] using controlEqual
        · exact outside wire isControl wireDifferent
      simp [outside, localControlledOperator, targetAgreement, controlEqual]
    · have notTargetAgreement : ¬agreesExcept target output input := by
        intro agreement
        exact controlEqual (agreement control different)
      simp [outside, localControlledOperator, notTargetAgreement, controlEqual]
  · have notTargetAgreement : ¬agreesExcept target output input := by
      intro agreement
      apply outside
      intro wire firstDifferent secondDifferent
      exact agreement wire secondDifferent
    simp [outside, notTargetAgreement]

/-- Ordinary wire control is exactly the predicate-control specialization. -/
theorem embedControlledSingleQubitOperator_eq_predicateControlled
    {qubits : Nat} (control target : Fin qubits)
    (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ) :
    embedControlledSingleQubitOperator control target different localOperator =
      predicateControlledSingleQubitOperator
        (fun basis => basis control) target localOperator := by
  funext output input
  rw [embedControlledSingleQubitOperator_apply_sparse]
  rw [predicateControlledSingleQubitOperator_apply]
  have decisionEq :
      agreesExceptDecidable target output input =
        predicateControlledAgreesExceptDecidable target output input :=
    Subsingleton.elim _ _
  rw [decisionEq]

/-- 7 gate semantic targetの任意幅行列要素はtarget一wireの疎な局所式である。 -/
theorem controlledHadamardSemanticOperator_apply_sparse
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : ControlledHadamardSevenGateSpec qubits)
    (output input : QubitBasis qubits) :
    controlledHadamardSemanticOperator symbolValue spec output input =
      if agreesExcept spec.target output input then
        if input spec.control then
          (localRy (2 * spec.quarterAngle.eval symbolValue) * localZ)
            (output spec.target) (input spec.target)
        else if output spec.target = input spec.target then 1 else 0
      else 0 := by
  exact embedControlledSingleQubitOperator_apply_sparse
    spec.control spec.target spec.different _ output input

/-- target外一致とtarget値一致を合わせると全基底一致になる。 -/
theorem eq_iff_agreesExcept_and_target_eq
    {qubits : Nat} (target : Fin qubits) (output input : QubitBasis qubits) :
    output = input ↔
      agreesExcept target output input ∧ output target = input target := by
  constructor
  · intro equal
    subst output
    exact ⟨by simp [agreesExcept], rfl⟩
  · intro conditions
    funext wire
    by_cases isTarget : wire = target
    · simpa [isTarget] using conditions.2
    · exact conditions.1 wire isTarget

/-- control=false入力ではsemantic targetの全行列列が恒等列である。 -/
theorem controlledHadamardSemanticOperator_apply_control_false
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : ControlledHadamardSevenGateSpec qubits)
    (output input : QubitBasis qubits) (controlFalse : input spec.control = false) :
    controlledHadamardSemanticOperator symbolValue spec output input =
      if output = input then 1 else 0 := by
  rw [controlledHadamardSemanticOperator_apply_sparse]
  by_cases outside : agreesExcept spec.target output input
  · by_cases targetEqual : output spec.target = input spec.target
    · have equal := (eq_iff_agreesExcept_and_target_eq spec.target output input).2
        ⟨outside, targetEqual⟩
      subst output
      simp [agreesExcept, controlFalse]
    · have different : output ≠ input := by
        intro equal
        exact targetEqual (congrFun equal spec.target)
      simp [outside, targetEqual, controlFalse, different]
  · have different : output ≠ input := by
      intro equal
      subst output
      exact outside (by simp [agreesExcept])
    simp [outside, different]

/-- control=true,target=false入力の元basis振幅は`cos h`である。 -/
theorem controlledHadamardSemanticOperator_amplitude_original
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : ControlledHadamardSevenGateSpec qubits)
    (input : QubitBasis qubits) (controlTrue : input spec.control = true)
    (targetFalse : input spec.target = false) :
    controlledHadamardSemanticOperator symbolValue spec input input =
      Real.cos (spec.quarterAngle.eval symbolValue) := by
  rw [controlledHadamardSemanticOperator_apply_sparse]
  simp [agreesExcept, controlTrue, targetFalse]

/-- control=true,target=false入力のtarget反転basis振幅は`sin h`である。 -/
theorem controlledHadamardSemanticOperator_amplitude_flipped
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : ControlledHadamardSevenGateSpec qubits)
    (input : QubitBasis qubits) (controlTrue : input spec.control = true)
    (targetFalse : input spec.target = false) :
    controlledHadamardSemanticOperator symbolValue spec
        (xorWire spec.target true input) input =
      Real.sin (spec.quarterAngle.eval symbolValue) := by
  rw [controlledHadamardSemanticOperator_apply_sparse]
  have outside : agreesExcept spec.target
      (xorWire spec.target true input) input := by
    intro wire different
    simp [xorWire, different]
  have controlPreserved :
      xorWire spec.target true input spec.control = input spec.control := by
    simp [xorWire, spec.different]
  simp [outside, controlTrue, targetFalse]

/-! ## 任意角RyZ族とHadamard特殊角の公開API分離 -/

/-- 任意四分角`h`を受け取る7-gate controlled-`(Ry(2h)·Z)`正本AST。 -/
def controlledRyZSevenGateCircuit {qubits : Nat}
    (spec : ControlledRyZSevenGateSpec qubits) :
    Circuit (PrimitiveGate qubits) :=
  controlledHadamardSevenGateCircuit spec

/-- 任意角7-gate ASTをstrict局所積へ結ぶ。 -/
theorem controlledRyZSevenGateCircuit_strict_correct {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRyZSevenGateSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledRyZSevenGateCircuit spec) =
      controlledRyZSevenGateStrictOperator symbolValue spec :=
  controlledHadamardSevenGateCircuit_strict_correct symbolValue spec

/-- 任意角strict積は直接controlled-RyZ semantic targetに一致する。 -/
theorem controlledRyZSevenGateStrictOperator_eq_semantic {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRyZSevenGateSpec qubits) :
    controlledRyZSevenGateStrictOperator symbolValue spec =
      controlledRyZSemanticOperator symbolValue spec := by
  exact controlledHadamardSevenGateStrictOperator_eq_semantic symbolValue spec

/-- 任意角controlled-RyZ 7-gate compilerの公開Exact component。 -/
def controlledRyZSevenGateExactOperatorComponent {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRyZSevenGateSpec qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := controlledRyZSevenGateCircuit spec
  target := controlledRyZSemanticOperator symbolValue spec
  correct := (controlledRyZSevenGateCircuit_strict_correct symbolValue spec).trans
    (controlledRyZSevenGateStrictOperator_eq_semantic symbolValue spec)

/-- 任意角controlled-RyZ componentは全作用素ユニタリ契約も持つ。 -/
def controlledRyZSevenGateUnitaryExactOperatorComponent {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRyZSevenGateSpec qubits) :
    UnitaryExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  ExactOperatorComponent.toUnitary
    (primitiveGateOperatorWithSymbols_mem_unitaryGroup symbolValue)
    (controlledRyZSevenGateExactOperatorComponent symbolValue spec)

/-- Hadamard特殊角`π/4`のRyZ局所作用は厳密にHadamardである。 -/
theorem localRy_pi_div_two_mul_localZ_eq_localH :
    localRy (2 * (Real.pi / 4)) * localZ = localH := by
  ext output input
  cases output <;> cases input <;>
    simp [localRy, localZ, localH, Matrix.mul_apply,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
  all_goals
    have sqrtTwoPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have sqrtTwoNonzero : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt sqrtTwoPositive
    have sqrtTwoSquare : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    ring_nf
    simp [sqrtTwoSquare]

/-- Hadamard特殊角を評価すると`π/4`になる。 -/
@[simp] theorem controlledHadamardQuarterAngle_eval
    (symbolValue : String → ℝ) :
    controlledHadamardQuarterAngle.eval symbolValue = Real.pi / 4 := by
  simp [controlledHadamardQuarterAngle, AngleExpr.eval]

/-- Hadamard特殊角のgeneric RyZ targetは直接controlled-H targetに一致する。 -/
theorem controlledRyZSemanticOperator_specialAngle_eq_hadamard
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : ControlledHadamardSpecialAngleSpec qubits) :
    controlledRyZSemanticOperator symbolValue spec.toRyZ =
      controlledHadamardSpecialAngleOperator spec := by
  unfold controlledRyZSemanticOperator controlledHadamardSpecialAngleOperator
    ControlledHadamardSpecialAngleSpec.toRyZ
  rw [controlledHadamardQuarterAngle_eval,
    localRy_pi_div_two_mul_localZ_eq_localH]

/-- Hadamard特殊角7-gate compilerの正本AST。 -/
def controlledHadamardSpecialAngleCircuit {qubits : Nat}
    (spec : ControlledHadamardSpecialAngleSpec qubits) :
    Circuit (PrimitiveGate qubits) :=
  controlledRyZSevenGateCircuit spec.toRyZ

/-- Hadamard特殊角7-gate compilerを直接controlled-Hへ結ぶExact component。 -/
def controlledHadamardSpecialAngleExactOperatorComponent {qubits : Nat}
    (symbolValue : String → ℝ)
    (spec : ControlledHadamardSpecialAngleSpec qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := controlledHadamardSpecialAngleCircuit spec
  target := controlledHadamardSpecialAngleOperator spec
  correct :=
    (controlledRyZSevenGateExactOperatorComponent symbolValue spec.toRyZ).correct.trans
      (controlledRyZSemanticOperator_specialAngle_eq_hadamard symbolValue spec)

/-- Hadamard特殊角componentも全作用素ユニタリ契約を持つ。 -/
def controlledHadamardSpecialAngleUnitaryExactOperatorComponent {qubits : Nat}
    (symbolValue : String → ℝ)
    (spec : ControlledHadamardSpecialAngleSpec qubits) :
    UnitaryExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  ExactOperatorComponent.toUnitary
    (primitiveGateOperatorWithSymbols_mem_unitaryGroup symbolValue)
    (controlledHadamardSpecialAngleExactOperatorComponent symbolValue spec)

end

end VerifiedCircuitCore

namespace VerifiedCircuitCore

noncomputable section

section NormalizedMacro

/-- The existing controlled-H source order, exposed as a normalized macro
surface.  Its seven leaves are all in the final six-constructor language. -/
def controlledHadamardNormalizedMacroCircuit {qubits : Nat}
    (spec : ControlledHadamardSevenGateSpec qubits) :
    Circuit (PrimitiveGate qubits) :=
  controlledHadamardSevenGateCircuit spec

theorem controlledHadamardNormalizedMacroCircuit_usesOnlyNormalizedPrimitives
    {qubits : Nat} (spec : ControlledHadamardSevenGateSpec qubits) :
    ∀ gate ∈ (controlledHadamardNormalizedMacroCircuit spec).flatten,
      IsNormalizedPrimitive gate := by
  intro gate member
  simp [controlledHadamardNormalizedMacroCircuit,
    controlledHadamardSevenGateCircuit] at member
  rcases member with h | h | h | h | h | h | h <;>
    subst gate <;> simp [IsNormalizedPrimitive]

theorem controlledHadamardNormalizedMacroCircuit_source_order
    {qubits : Nat} (spec : ControlledHadamardSevenGateSpec qubits) :
    controlledHadamardNormalizedMacroCircuit spec =
      controlledHadamardSevenGateCircuit spec := rfl

theorem controlledHadamardNormalizedMacroCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : ControlledHadamardSevenGateSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledHadamardNormalizedMacroCircuit spec) =
      controlledHadamardSemanticOperator symbolValue spec := by
  exact (controlledHadamardSevenGateCircuit_strict_correct
    symbolValue spec).trans
      (controlledHadamardSevenGateStrictOperator_eq_semantic symbolValue spec)

end NormalizedMacro

end

end VerifiedCircuitCore
