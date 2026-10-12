import QLean.Circuits.Foundation.PhaseShiftMacros
import QLean.Circuits.Foundation.ConstructionMultiControlledRotationCorrectness

/-!
# Exact normalized macros for one-control rotations

The migration language no longer admits PrimitiveGate.controlledRy or
PrimitiveGate.controlledRz as output leaves.  This module gives those two
operations a shared, typed macro boundary: an independently specified
controlled-rotation operator and a primitive circuit over the normalized six
leaf language.  A scientific rotation occurrence therefore stays one macro
occurrence even when its lowering contains multiple primitive Ry leaves.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Typed input for the normalized one-control Ry macro. -/
structure ControlledRySpec (qubits : Nat) where
  angle : AngleExpr
  control : Fin qubits
  target : Fin qubits
  different : control ≠ target

/-- Typed input for the normalized one-control Rz macro. -/
structure ControlledRzSpec (qubits : Nat) where
  angle : AngleExpr
  control : Fin qubits
  target : Fin qubits
  different : control ≠ target

/-- Symbolic half angle shared by the controlled phase-shift decompositions. -/
def controlledRotationHalfAngle (angle : AngleExpr) : AngleExpr :=
  .div angle (.const 2)

@[simp] theorem controlledRotationHalfAngle_eval
    (symbolValue : String → ℝ) (angle : AngleExpr) :
    (controlledRotationHalfAngle angle).eval symbolValue =
      angle.eval symbolValue / 2 := by
  simp [controlledRotationHalfAngle, AngleExpr.eval]

/-- The normalized four-leaf source-order implementation of controlled Ry. -/
def controlledRyMacroCircuit {qubits : Nat}
    (spec : ControlledRySpec qubits) : Circuit (PrimitiveGate qubits) :=
  Circuit.controlledRyMacroExpansion
    spec.control spec.target spec.different spec.angle

/--
The normalized four-leaf source-order implementation of controlled Rz.
It is P(θ/2) on the target, CNOT, P(-θ/2) on the target, CNOT.
-/
def controlledRzMacroCircuit {qubits : Nat}
    (spec : ControlledRzSpec qubits) : Circuit (PrimitiveGate qubits) :=
  Circuit.fromList [
    .phaseShift (controlledRotationHalfAngle spec.angle) spec.target,
    .cnot spec.control spec.target spec.different,
    .phaseShift (.neg (controlledRotationHalfAngle spec.angle)) spec.target,
    .cnot spec.control spec.target spec.different]

/-- Independent semantic target of the controlled Ry macro. -/
def controlledRyMacroOperator {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRySpec qubits) :
    Operator (QubitBasis qubits) :=
  embedControlledSingleQubitOperator spec.control spec.target spec.different
    (localRy (spec.angle.eval symbolValue))

/-- Independent semantic target of the controlled Rz macro. -/
def controlledRzMacroOperator {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRzSpec qubits) :
    Operator (QubitBasis qubits) :=
  embedControlledSingleQubitOperator spec.control spec.target spec.different
    (localRz (spec.angle.eval symbolValue))

/-- Syntactic output contract for a controlled-rotation macro lowering. -/
def ControlledRotationMacroUsesOnlyNormalizedPrimitives {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits)) : Prop :=
  ∀ gate, gate ∈ circuit.flatten → IsNormalizedPrimitive gate

theorem controlledRyMacroCircuit_usesOnlyNormalizedPrimitives
    {qubits : Nat} (spec : ControlledRySpec qubits) :
    ControlledRotationMacroUsesOnlyNormalizedPrimitives
      (controlledRyMacroCircuit spec) := by
  simp [ControlledRotationMacroUsesOnlyNormalizedPrimitives,
    controlledRyMacroCircuit, Circuit.controlledRyMacroExpansion,
    IsNormalizedPrimitive]

theorem controlledRzMacroCircuit_usesOnlyNormalizedPrimitives
    {qubits : Nat} (spec : ControlledRzSpec qubits) :
    ControlledRotationMacroUsesOnlyNormalizedPrimitives
      (controlledRzMacroCircuit spec) := by
  simp [ControlledRotationMacroUsesOnlyNormalizedPrimitives,
    controlledRzMacroCircuit, IsNormalizedPrimitive]

/-- The local normalized controlled-Rz expansion is strict, not projective. -/
theorem local_controlledRz_decomposition (angle : ℝ) :
    localCnotOperator * localOnTarget (localPhaseShift (-(angle / 2))) *
        localCnotOperator * localOnTarget (localPhaseShift (angle / 2)) =
      localControlledOperator (localRz angle) := by
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases outputTarget <;>
    cases inputControl <;> cases inputTarget <;>
    simp [localCnotOperator, localOnTarget, localControlledOperator,
      localPhaseShift, localPhase, localRz, Matrix.mul_apply,
      Matrix.kronecker, Fintype.sum_prod_type]
  all_goals
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    ring_nf

/-- Strict normalized lowering correctness for controlled Ry. -/
theorem controlledRyMacroCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ) (spec : ControlledRySpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledRyMacroCircuit spec) =
      controlledRyMacroOperator symbolValue spec := by
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (Circuit.controlledRyMacroExpansion
        spec.control spec.target spec.different spec.angle) =
    embedControlledSingleQubitOperator spec.control spec.target spec.different
      (localRy (spec.angle.eval symbolValue))
  simp only [Circuit.controlledRyMacroExpansion, Circuit.fromList, Circuit.denote,
    primitiveGateOperatorWithSymbols, Circuit.halfAngle, AngleExpr.eval, Matrix.one_mul]
  rw [show deterministicOperator
      (fun input => xorWire spec.target (input spec.control) input) =
        analyticCnotOperator spec.control spec.target by rfl]
  rw [analyticCnotOperator_eq_embedTwo_localCnot
    spec.control spec.target spec.different]
  rw [← embedTwoQubitOperator_localOnTarget spec.control spec.target spec.different,
    ← embedTwoQubitOperator_localOnTarget spec.control spec.target spec.different]
  rw [← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul,
    ← embedTwoQubitOperator_mul]
  unfold embedControlledSingleQubitOperator
  apply congrArg (embedTwoQubitOperator spec.control spec.target spec.different)
  convert local_controlledRy_decomposition (spec.angle.eval symbolValue) using 1
  norm_num
  ring_nf

/-- Strict normalized lowering correctness for controlled Rz. -/
theorem controlledRzMacroCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ) (spec : ControlledRzSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledRzMacroCircuit spec) =
      controlledRzMacroOperator symbolValue spec := by
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (Circuit.fromList [
        .phaseShift (controlledRotationHalfAngle spec.angle) spec.target,
        .cnot spec.control spec.target spec.different,
        .phaseShift (.neg (controlledRotationHalfAngle spec.angle)) spec.target,
        .cnot spec.control spec.target spec.different]) =
    embedControlledSingleQubitOperator spec.control spec.target spec.different
      (localRz (spec.angle.eval symbolValue))
  simp only [Circuit.fromList, Circuit.denote, primitiveGateOperatorWithSymbols,
    controlledRotationHalfAngle_eval, AngleExpr.eval_neg, Matrix.one_mul]
  rw [show deterministicOperator
      (fun input => xorWire spec.target (input spec.control) input) =
        analyticCnotOperator spec.control spec.target by rfl]
  rw [analyticCnotOperator_eq_embedTwo_localCnot
    spec.control spec.target spec.different]
  rw [← embedTwoQubitOperator_localOnTarget spec.control spec.target spec.different,
    ← embedTwoQubitOperator_localOnTarget spec.control spec.target spec.different]
  rw [← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul,
    ← embedTwoQubitOperator_mul]
  unfold embedControlledSingleQubitOperator
  apply congrArg (embedTwoQubitOperator spec.control spec.target spec.different)
  exact local_controlledRz_decomposition (spec.angle.eval symbolValue)

theorem controlledRyMacroOperator_mem_unitaryGroup
    {qubits : Nat} (symbolValue : String → ℝ) (spec : ControlledRySpec qubits) :
    controlledRyMacroOperator symbolValue spec ∈
      Matrix.unitaryGroup (QubitBasis qubits) ℂ := by
  exact embedControlledSingleQubitOperator_mem_unitaryGroup
    spec.control spec.target spec.different _
    (localRy_mem_unitaryGroup (spec.angle.eval symbolValue))

theorem controlledRzMacroOperator_mem_unitaryGroup
    {qubits : Nat} (symbolValue : String → ℝ) (spec : ControlledRzSpec qubits) :
    controlledRzMacroOperator symbolValue spec ∈
      Matrix.unitaryGroup (QubitBasis qubits) ℂ := by
  exact embedControlledSingleQubitOperator_mem_unitaryGroup
    spec.control spec.target spec.different _
    (localRz_mem_unitaryGroup (spec.angle.eval symbolValue))

def controlledRyMacroExactComponent {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRySpec qubits) :
    ExactOperatorComponent (basis := QubitBasis qubits)
      (primitiveGateOperatorWithSymbols symbolValue) where
  circuit := controlledRyMacroCircuit spec
  target := controlledRyMacroOperator symbolValue spec
  correct := controlledRyMacroCircuit_denote_eq symbolValue spec

def controlledRzMacroExactComponent {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRzSpec qubits) :
    ExactOperatorComponent (basis := QubitBasis qubits)
      (primitiveGateOperatorWithSymbols symbolValue) where
  circuit := controlledRzMacroCircuit spec
  target := controlledRzMacroOperator symbolValue spec
  correct := controlledRzMacroCircuit_denote_eq symbolValue spec

end

end VerifiedCircuitCore
