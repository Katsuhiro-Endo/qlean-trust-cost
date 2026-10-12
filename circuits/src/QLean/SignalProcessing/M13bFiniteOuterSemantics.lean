import QLean.SignalProcessing.M13bFiniteOuterCompiler
import QLean.SignalProcessing.M13bConjugateControlledCompute
import QLean.SignalProcessing.M13bControlXStateSemantics
import QLean.SignalProcessing.M13bHadamardTrueStateSemantics
import QLean.SignalProcessing.M13bHermitianSuccessReflection

/-! Semantics of the finite outer compiler at an abstract register width.
The inner circuits are arbitrary: no equality with a legacy preparation
unitary, and no scientific source record, is required. -/

set_option autoImplicit false
set_option warningAsError true

namespace M13bFiniteOuterSemantics

open VerifiedCircuitCore M13bFiniteOuterCompiler
open M13bExternallyControlledCompute M13bControlledStateSemantics

noncomputable section

/-- A short action vocabulary keeps concrete register widths out of the
elaboration of the generic external-control and outer-composition proofs. -/
def circuitAction {n : Nat} (symbols : String → ℝ)
    (circuit : Circuit (PrimitiveGate n)) (state : State (QubitBasis n)) :
    State (QubitBasis n) :=
  applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbols) circuit) state

/-- The clean-control compiler implements the controlled denotation of its
actual input circuit.  The reflexive child component only supplies that
circuit to the already verified leaf-wise compiler; it is not a scientific
correctness assumption. -/
theorem controlled_apply_clean {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (valid : plan.layout.CleanWorkValid)
    (circuit : Circuit (PrimitiveGate n)) (state : State (QubitBasis (n + 3)))
    (inside : state ∈ SubspaceMapComponent.basisSpan
      (externallyControlledCleanWorkPredicate valid)) :
    circuitAction symbols (plan.controlled circuit) state =
      applyOperator (externallyControlledWireLiftOperator plan.layout
        (Circuit.denote (primitiveGateOperatorWithSymbols symbols) circuit)) state := by
  let child : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := n) symbols) :=
    { circuit := circuit
      target := Circuit.denote (primitiveGateOperatorWithSymbols symbols) circuit
      correct := rfl }
  let certificate : ExternallyControlledPrimitiveCircuitCertificate circuit :=
    ⟨by intro gate _; exact primitiveGate_externally_controllable gate⟩
  let component := externallyControlledCleanSubspaceMapComponentOfExact
    symbols plan.layout valid child certificate
  have circuit_eq : component.circuit = plan.controlled circuit := by
    rw [externallyControlledCleanSubspaceMapComponentOfExact_circuit]
    rfl
  have input_eq : component.inputSubspace = SubspaceMapComponent.basisSpan
      (externallyControlledCleanWorkPredicate valid) :=
    externallyControlledCleanSubspaceMapComponentOfExact_inputSubspace
      symbols plan.layout valid child certificate
  have target_eq : component.target = externallyControlledWireLiftOperator plan.layout
      (Circuit.denote (primitiveGateOperatorWithSymbols symbols) circuit) := by
    rw [externallyControlledCleanSubspaceMapComponentOfExact_target,
      ExternallyControlledPrimitivePlan.semanticPlanOperator_eq_controlledWireLift,
      ExternallyControlledPrimitiveCircuitCertificate.sourcePlanOperator_eq_component_target
        symbols child certificate]
  have correct := component.correct state (input_eq.symm ▸ inside)
  simpa only [circuit_eq, target_eq, circuitAction] using correct

theorem controlled_apply_canonical {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (circuit : Circuit (PrimitiveGate n)) (bit : Bool) (state : State (QubitBasis n)) :
    circuitAction symbols (plan.controlled circuit) (m13bControlledState n bit state) =
      applyOperator (externallyControlledWireLiftOperator (m13bExternalControlLayout n)
        (Circuit.denote (primitiveGateOperatorWithSymbols symbols) circuit))
          (m13bControlledState n bit state) := by
  let canonical : Plan n := { plan with layout := m13bExternalControlLayout n }
  have same : plan.controlled circuit = canonical.controlled circuit := by
    unfold Plan.controlled
    rw [layout]
  rw [same]
  exact controlled_apply_clean symbols canonical (m13bExternalControlCleanWorkValid n)
    circuit _ (m13bControlledState_mem_clean n bit state)

theorem controlled_apply_false {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (circuit : Circuit (PrimitiveGate n)) (state : State (QubitBasis n)) :
    circuitAction symbols (plan.controlled circuit) (m13bControlledState n false state) =
      m13bControlledState n false state := by
  rw [controlled_apply_canonical symbols plan layout circuit false state]
  exact M13bConjugateControlledCompute.controlledLift_apply_control_zero_state n _ state

theorem controlled_apply_true {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (circuit : Circuit (PrimitiveGate n)) (state : State (QubitBasis n)) :
    circuitAction symbols (plan.controlled circuit) (m13bControlledState n true state) =
      m13bControlledState n true (circuitAction symbols circuit state) := by
  rw [controlled_apply_canonical symbols plan layout circuit true state]
  exact M13bConjugateControlledCompute.controlledLift_apply_control_one_state n _ state

/-- The selector used by `Plan.hermitianCompute`, with both inner circuits
left explicit.  Its second branch need not be the adjoint of the first. -/
def selector {n : Nat} (plan : Plan n)
    (original conjugate : Circuit (PrimitiveGate n)) :
    Circuit (PrimitiveGate (n + 3)) :=
  Circuit.sequence [.gate (.x plan.layout.control), plan.controlled original,
    .gate (.x plan.layout.control), plan.controlled conjugate]

theorem selector_apply_false {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (original conjugate : Circuit (PrimitiveGate n)) (state : State (QubitBasis n)) :
    circuitAction symbols (selector plan original conjugate)
        (m13bControlledState n false state) =
      m13bControlledState n false (circuitAction symbols original state) := by
  simp only [circuitAction, selector, Circuit.sequence, Circuit.denote, applyOperator_mul]
  rw [layout, M13bControlXStateSemantics.controlX_state_false]
  rw [show applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.controlled original)) _ = _ from
    controlled_apply_true symbols plan layout original state]
  rw [M13bControlXStateSemantics.controlX_state_true]
  rw [show applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.controlled conjugate)) _ = _ from
    controlled_apply_false symbols plan layout conjugate _]
  exact Matrix.one_mulVec _

theorem selector_apply_true {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (original conjugate : Circuit (PrimitiveGate n)) (state : State (QubitBasis n)) :
    circuitAction symbols (selector plan original conjugate)
        (m13bControlledState n true state) =
      m13bControlledState n true (circuitAction symbols conjugate state) := by
  simp only [circuitAction, selector, Circuit.sequence, Circuit.denote, applyOperator_mul]
  rw [layout, M13bControlXStateSemantics.controlX_state_true]
  rw [show applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.controlled original)) _ = _ from
    controlled_apply_false symbols plan layout original state]
  rw [M13bControlXStateSemantics.controlX_state_false]
  rw [show applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.controlled conjugate)) _ = _ from
    controlled_apply_true symbols plan layout conjugate state]
  exact Matrix.one_mulVec _

theorem circuitAction_add {n : Nat} (symbols : String → ℝ)
    (circuit : Circuit (PrimitiveGate n)) (a b : State (QubitBasis n)) :
    circuitAction symbols circuit (a + b) =
      circuitAction symbols circuit a + circuitAction symbols circuit b :=
  applyOperator_add _ a b

theorem circuitAction_smul {n : Nat} (symbols : String → ℝ)
    (circuit : Circuit (PrimitiveGate n)) (coefficient : ℂ) (state : State (QubitBasis n)) :
    circuitAction symbols circuit (coefficient • state) =
      coefficient • circuitAction symbols circuit state :=
  applyOperator_smul _ coefficient state

theorem circuitAction_sub {n : Nat} (symbols : String → ℝ)
    (circuit : Circuit (PrimitiveGate n)) (a b : State (QubitBasis n)) :
    circuitAction symbols circuit (a - b) =
      circuitAction symbols circuit a - circuitAction symbols circuit b := by
  exact Matrix.mulVec_sub _ a b

theorem circuitAction_sequence_three {n : Nat} (symbols : String → ℝ)
    (a b c : Circuit (PrimitiveGate n)) (state : State (QubitBasis n)) :
    circuitAction symbols (Circuit.sequence [a, b, c]) state =
      circuitAction symbols c (circuitAction symbols b (circuitAction symbols a state)) := by
  simp [circuitAction, Circuit.sequence, Circuit.denote, applyOperator_mul]

def hadamardFalseState (n : Nat) (state : State (QubitBasis n)) :
    State (QubitBasis (n + 3)) :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • m13bControlledState n false state +
    ((1 / Real.sqrt 2 : ℝ) : ℂ) • m13bControlledState n true state

def hadamardTrueState (n : Nat) (state : State (QubitBasis n)) :
    State (QubitBasis (n + 3)) :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • m13bControlledState n false state -
    ((1 / Real.sqrt 2 : ℝ) : ℂ) • m13bControlledState n true state

/-- Independent, coherent two-branch action of the Hadamard selector. -/
def hermitianOutput (n : Nat) (original conjugate : State (QubitBasis n)) :
    State (QubitBasis (n + 3)) :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • hadamardFalseState n original +
    ((1 / Real.sqrt 2 : ℝ) : ℂ) • hadamardTrueState n conjugate

theorem hadamard_apply_false (symbols : String → ℝ) (n : Nat)
    (state : State (QubitBasis n)) :
    circuitAction symbols (.gate (.h (m13bExternalControlLayout n).control))
        (m13bControlledState n false state) = hadamardFalseState n state :=
  M13bHadamardStateSemantics.cleanControlH_actual_apply_control_false_state symbols n state

theorem hadamard_apply_true (symbols : String → ℝ) (n : Nat)
    (state : State (QubitBasis n)) :
    circuitAction symbols (.gate (.h (m13bExternalControlLayout n).control))
        (m13bControlledState n true state) = hadamardTrueState n state :=
  M13bHadamardTrueStateSemantics.cleanControlH_actual_apply_control_true_state symbols n state

/-- Both controlled branches of the actual finite compiler are retained.
No property of the inner word beyond its actual action is used here. -/
theorem hermitianCompute_apply_false {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (state : State (QubitBasis n)) :
    circuitAction symbols (plan.hermitianCompute program)
        (m13bControlledState n false state) =
      hermitianOutput n
        (circuitAction symbols (plan.word program) state)
        (circuitAction symbols (plan.word
          (M13bConjugatePhaseWord.conjugatePhaseProgram119 program)) state) := by
  change circuitAction symbols (Circuit.sequence [
    .gate (.h plan.layout.control),
    selector plan (plan.word program)
      (plan.word (M13bConjugatePhaseWord.conjugatePhaseProgram119 program)),
    .gate (.h plan.layout.control)]) _ = _
  rw [circuitAction_sequence_three, layout, hadamard_apply_false]
  unfold hadamardFalseState
  rw [circuitAction_add, circuitAction_smul, circuitAction_smul,
    selector_apply_false symbols plan layout,
    selector_apply_true symbols plan layout,
    circuitAction_add, circuitAction_smul, circuitAction_smul,
    hadamard_apply_false, hadamard_apply_true]
  rfl

/-- The second input-control sector is also included; this is needed to
transport the full two-control frame, not just one selected source vector. -/
theorem hermitianCompute_apply_true {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (state : State (QubitBasis n)) :
    circuitAction symbols (plan.hermitianCompute program)
        (m13bControlledState n true state) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) • hadamardFalseState n
        (circuitAction symbols (plan.word program) state) -
      ((1 / Real.sqrt 2 : ℝ) : ℂ) • hadamardTrueState n
        (circuitAction symbols (plan.word
          (M13bConjugatePhaseWord.conjugatePhaseProgram119 program)) state) := by
  change circuitAction symbols (Circuit.sequence [
    .gate (.h plan.layout.control),
    selector plan (plan.word program)
      (plan.word (M13bConjugatePhaseWord.conjugatePhaseProgram119 program)),
    .gate (.h plan.layout.control)]) _ = _
  rw [circuitAction_sequence_three, layout, hadamard_apply_true]
  unfold hadamardTrueState
  rw [circuitAction_sub, circuitAction_smul, circuitAction_smul,
    selector_apply_false symbols plan layout,
    selector_apply_true symbols plan layout,
    circuitAction_sub, circuitAction_smul, circuitAction_smul,
    hadamard_apply_false, hadamard_apply_true]
  rfl

theorem successReflection_apply_false {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (angle : AngleExpr) (angle_value : angle.eval symbols = Real.pi)
    (state : State (QubitBasis n)) :
    circuitAction symbols (plan.successReflection angle)
        (m13bControlledState n false state) =
      m13bControlledState n false (circuitAction symbols
        (plan.word [.projectorPhase .target angle]) state) := by
  simp only [circuitAction, Plan.successReflection, Circuit.sequence,
    Circuit.denote, applyOperator_mul]
  rw [layout, M13bControlXStateSemantics.controlX_state_false]
  rw [show applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.controlled (plan.word [.projectorPhase .target angle]))) _ = _ from
    controlled_apply_true symbols plan layout _ state]
  rw [M13bControlXStateSemantics.controlX_state_true]
  simp only [show applyOperator (1 : Operator (QubitBasis (n + 3))) = id from
    funext (fun _ => Matrix.one_mulVec _)]
  have gate_eq : primitiveGateOperatorWithSymbols symbols
      (.phaseShift angle (m13bExternalControlLayout n).control) =
      primitiveGateOperatorWithSymbols symbols
        (.phaseShift (.const Real.pi) (m13bExternalControlLayout n).control) := by
    simp only [primitiveGateOperatorWithSymbols, angle_value, AngleExpr.eval]
  rw [gate_eq]
  exact M13bHermitianSuccessReflection.externalControlPiPhase119_apply_control_false
    symbols n _

theorem successReflection_apply_true {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (angle : AngleExpr) (angle_value : angle.eval symbols = Real.pi)
    (state : State (QubitBasis n)) :
    circuitAction symbols (plan.successReflection angle)
        (m13bControlledState n true state) = -m13bControlledState n true state := by
  simp only [circuitAction, Plan.successReflection, Circuit.sequence,
    Circuit.denote, applyOperator_mul]
  rw [layout, M13bControlXStateSemantics.controlX_state_true]
  rw [show applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.controlled (plan.word [.projectorPhase .target angle]))) _ = _ from
    controlled_apply_false symbols plan layout _ state]
  rw [M13bControlXStateSemantics.controlX_state_false]
  simp only [show applyOperator (1 : Operator (QubitBasis (n + 3))) = id from
    funext (fun _ => Matrix.one_mulVec _)]
  have gate_eq : primitiveGateOperatorWithSymbols symbols
      (.phaseShift angle (m13bExternalControlLayout n).control) =
      primitiveGateOperatorWithSymbols symbols
        (.phaseShift (.const Real.pi) (m13bExternalControlLayout n).control) := by
    simp only [primitiveGateOperatorWithSymbols, angle_value, AngleExpr.eval]
  rw [gate_eq]
  exact M13bHermitianSuccessReflection.externalControlPiPhase119_apply_control_true
    symbols n state

/-- Exact outer assembly semantics for the common compiler, rather than a
rewrite to a separately built legacy circuit. -/
theorem compile_denotation {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (angle : AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbols) (plan.compile program angle) =
      star (Circuit.denote (primitiveGateOperatorWithSymbols symbols)
        (plan.hermitianCompute program)) *
      Circuit.denote (primitiveGateOperatorWithSymbols symbols) (plan.successReflection angle) *
      Circuit.denote (primitiveGateOperatorWithSymbols symbols) (plan.hermitianCompute program) := by
  unfold Plan.compile outerFromComputeAndReflection
  simp only [Circuit.sequence, Circuit.denote, one_mul]
  rw [Circuit.denote_reverse PrimitiveGate.inverse
    (primitiveGateOperatorWithSymbols symbols) (primitiveGateOperator_inverse symbols)]
  simp only [Matrix.star_eq_conjTranspose]

end
end M13bFiniteOuterSemantics
