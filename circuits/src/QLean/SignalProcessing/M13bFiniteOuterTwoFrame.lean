import QLean.SignalProcessing.M13bFiniteOuterCompiler
import QLean.SignalProcessing.NativeQSPWitnessTwoFrameModel

/-! A source-order two-frame theorem for any finite outer QSP plan.  The
plan's actual signal and phase circuits appear in the four hypotheses; no
circuit semantics or polynomial response is inserted by fiat. -/

set_option autoImplicit false
set_option warningAsError true

namespace M13bFiniteOuterTwoFrame

open VerifiedCircuitCore
open M13bFiniteOuterCompiler
open NativeFixedPointPrimitive
open NativeQSPWitnessTransferModel
open NativeQSPWitnessTwoFrameModel
open SpectralSamplingProof.Analytic

noncomputable section

def activeFrame {n : Nat}
    (sourceFrame targetFrame : Matrix (QubitBasis n) (Fin 2) ℂ) :
    ActiveFrame → Matrix (QubitBasis n) (Fin 2) ℂ
  | .source => sourceFrame
  | .target => targetFrame

def realStepOperator {n : Nat} (plan : Plan n)
    (step : FixedPointRoleAwarePhaseStep) : Operator (QubitBasis n) :=
  Circuit.denote (primitiveGateOperatorWithSymbols (fun _ : String => 0))
    (plan.step (PhaseProgramStep.ofReal step))

def realOperatorWord {n : Nat} (plan : Plan n)
    (steps : List FixedPointRoleAwarePhaseStep) : Operator (QubitBasis n) :=
  operatorSequence (steps.map (realStepOperator plan))

/-- Delay the finite-basis typeclass construction until the abstract register
widths have been fixed; concrete scientific widths are not unfolded here. -/
def wireLiftDenotation {innerQubits outerQubits : Nat}
    (inner : Circuit (PrimitiveGate innerQubits))
    (placement : Fin innerQubits ↪ Fin outerQubits) :
    Operator (QubitBasis outerQubits) :=
  wireLiftOperator placement
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ : String => 0)) inner)

def circuitDenotation {n : Nat} (circuit : Circuit (PrimitiveGate n)) :
    Operator (QubitBasis n) :=
  Circuit.denote (primitiveGateOperatorWithSymbols (fun _ : String => 0)) circuit

def frameLeftProduct {n : Nat} (operator : Operator (QubitBasis n))
    (frame : Matrix (QubitBasis n) (Fin 2) ℂ) :
    Matrix (QubitBasis n) (Fin 2) ℂ :=
  operator * frame

def frameRightProduct {n : Nat} (frame : Matrix (QubitBasis n) (Fin 2) ℂ)
    (transfer : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (QubitBasis n) (Fin 2) ℂ :=
  frame * transfer

/-- A forward query whose plan field is a wire-mapped inner signal denotes
the corresponding wire lift.  This lemma is independent of the scientific
parameter expressions used to construct the plan. -/
theorem realStepOperator_signal_forward_wireLift
    {innerQubits outerQubits : Nat}
    (plan : Plan outerQubits)
    (inner : Circuit (PrimitiveGate innerQubits))
    (placement : Fin innerQubits ↪ Fin outerQubits)
    (signalField : plan.signalCircuit =
      inner.mapGates (PrimitiveGate.mapWires placement)) :
    realStepOperator plan (.signal .forward) =
      wireLiftDenotation inner placement := by
  unfold realStepOperator Plan.step
  rw [signalField]
  unfold wireLiftDenotation
  exact denote_mapPrimitiveWires_eq_wireLiftOperator
    (fun _ : String => 0) placement inner

/-- The inverse query is the adjoint of the same actual, mapped signal. -/
theorem realStepOperator_signal_adjoint_wireLift
    {innerQubits outerQubits : Nat}
    (plan : Plan outerQubits)
    (inner : Circuit (PrimitiveGate innerQubits))
    (placement : Fin innerQubits ↪ Fin outerQubits)
    (signalField : plan.signalCircuit =
      inner.mapGates (PrimitiveGate.mapWires placement)) :
    realStepOperator plan (.signal .adjoint) =
      star (wireLiftDenotation inner placement) := by
  unfold realStepOperator Plan.step
  change Circuit.denote (primitiveGateOperatorWithSymbols (fun _ : String => 0))
      (plan.signalCircuit.reverse PrimitiveGate.inverse) = _
  rw [Circuit.denote_reverse PrimitiveGate.inverse
    (primitiveGateOperatorWithSymbols (fun _ : String => 0))
    (primitiveGateOperator_inverse (fun _ : String => 0))]
  rw [signalField]
  unfold wireLiftDenotation
  exact congrArg star (denote_mapPrimitiveWires_eq_wireLiftOperator
    (fun _ : String => 0) placement inner)

/-- Both phase roles evaluate the plan's actual image-phase circuit at the
same real angle; the corresponding concrete circuits can be rewritten later
without expanding their finite-basis denotation. -/
theorem realStepOperator_source_phase_of_circuit
    {n : Nat} (plan : Plan n) (angle : ℝ)
    (circuit : Circuit (PrimitiveGate n))
    (phaseField : plan.sourcePhase (.const angle) = circuit) :
    realStepOperator plan (.projectorPhase .source angle) =
      circuitDenotation circuit := by
  unfold realStepOperator Plan.step circuitDenotation
  exact congrArg (Circuit.denote
    (primitiveGateOperatorWithSymbols (fun _ : String => 0))) phaseField

theorem realStepOperator_target_phase_of_circuit
    {n : Nat} (plan : Plan n) (angle : ℝ)
    (circuit : Circuit (PrimitiveGate n))
    (phaseField : plan.targetPhase (.const angle) = circuit) :
    realStepOperator plan (.projectorPhase .target angle) =
      circuitDenotation circuit := by
  unfold realStepOperator Plan.step circuitDenotation
  exact congrArg (Circuit.denote
    (primitiveGateOperatorWithSymbols (fun _ : String => 0))) phaseField

/-- Only the four physical one-step equations are needed for an arbitrary
well-formed source-order word. -/
structure PlanTwoFrameWitness {n : Nat} (plan : Plan n)
    (successProbability : ℝ)
    (sourceFrame targetFrame : Matrix (QubitBasis n) (Fin 2) ℂ) : Prop where
  forward :
    realStepOperator plan (.signal .forward) * sourceFrame =
      targetFrame * fixedPointSignalTransferMatrix successProbability .forward
  adjoint :
    realStepOperator plan (.signal .adjoint) * targetFrame =
      sourceFrame * fixedPointSignalTransferMatrix successProbability .adjoint
  source_phase : ∀ angle : ℝ,
    realStepOperator plan (.projectorPhase .source angle) * sourceFrame =
      sourceFrame * fixedPointProjectorTransferMatrix .source angle
  target_phase : ∀ angle : ℝ,
    realStepOperator plan (.projectorPhase .target angle) * targetFrame =
      targetFrame * fixedPointProjectorTransferMatrix .target angle

theorem PlanTwoFrameWitness.ofWrapped {n : Nat} (plan : Plan n)
    (successProbability : ℝ)
    (sourceFrame targetFrame : Matrix (QubitBasis n) (Fin 2) ℂ)
    (forward : frameLeftProduct (realStepOperator plan (.signal .forward)) sourceFrame =
      frameRightProduct targetFrame
        (fixedPointSignalTransferMatrix successProbability .forward))
    (adjoint : frameLeftProduct (realStepOperator plan (.signal .adjoint)) targetFrame =
      frameRightProduct sourceFrame
        (fixedPointSignalTransferMatrix successProbability .adjoint))
    (sourcePhase : ∀ angle : ℝ,
      frameLeftProduct (realStepOperator plan (.projectorPhase .source angle)) sourceFrame =
        frameRightProduct sourceFrame (fixedPointProjectorTransferMatrix .source angle))
    (targetPhase : ∀ angle : ℝ,
      frameLeftProduct (realStepOperator plan (.projectorPhase .target angle)) targetFrame =
        frameRightProduct targetFrame (fixedPointProjectorTransferMatrix .target angle)) :
    PlanTwoFrameWitness plan successProbability sourceFrame targetFrame := by
  exact ⟨forward, adjoint, sourcePhase, targetPhase⟩

theorem step_intertwines {n : Nat} (plan : Plan n)
    (successProbability : ℝ)
    (sourceFrame targetFrame : Matrix (QubitBasis n) (Fin 2) ℂ)
    (physical : PlanTwoFrameWitness plan successProbability sourceFrame targetFrame)
    (current next : ActiveFrame) (step : FixedPointRoleAwarePhaseStep)
    (transition : frameAfter current step = some next) :
    realStepOperator plan step * activeFrame sourceFrame targetFrame current =
      activeFrame sourceFrame targetFrame next *
        fixedPointRoleAwareStepTransferMatrix successProbability step := by
  cases current with
  | source =>
      cases step with
      | signal direction =>
          cases direction <;> simp [frameAfter] at transition
          cases transition
          exact physical.forward
      | projectorPhase role angle =>
          cases role <;> simp [frameAfter] at transition
          cases transition
          exact physical.source_phase angle
  | target =>
      cases step with
      | signal direction =>
          cases direction <;> simp [frameAfter] at transition
          cases transition
          exact physical.adjoint
      | projectorPhase role angle =>
          cases role <;> simp [frameAfter] at transition
          cases transition
          exact physical.target_phase angle

/-- The source-order physical word has the independently defined abstract
two-frame transfer response, provided the four circuit equations hold. -/
theorem realOperatorWord_intertwines {n : Nat} (plan : Plan n)
    (successProbability : ℝ)
    (sourceFrame targetFrame : Matrix (QubitBasis n) (Fin 2) ℂ)
    (physical : PlanTwoFrameWitness plan successProbability sourceFrame targetFrame)
    {initial final : ActiveFrame} {steps : List FixedPointRoleAwarePhaseStep}
    (wellFormed : FrameWord initial steps final) :
    realOperatorWord plan steps * activeFrame sourceFrame targetFrame initial =
      activeFrame sourceFrame targetFrame final *
        abstractTransferWord successProbability steps := by
  induction wellFormed with
  | nil frame =>
      change 1 * activeFrame sourceFrame targetFrame frame =
        activeFrame sourceFrame targetFrame frame * 1
      simp
  | @cons current next final step rest transition remaining ih =>
      calc
        (realOperatorWord plan rest * realStepOperator plan step) *
            activeFrame sourceFrame targetFrame current =
          realOperatorWord plan rest *
            (realStepOperator plan step * activeFrame sourceFrame targetFrame current) :=
            Matrix.mul_assoc _ _ _
        _ = realOperatorWord plan rest *
            (activeFrame sourceFrame targetFrame next *
              fixedPointRoleAwareStepTransferMatrix successProbability step) := by
              rw [step_intertwines plan successProbability sourceFrame targetFrame
                physical current next step transition]
        _ = (realOperatorWord plan rest * activeFrame sourceFrame targetFrame next) *
            fixedPointRoleAwareStepTransferMatrix successProbability step :=
            (Matrix.mul_assoc _ _ _).symm
        _ = (activeFrame sourceFrame targetFrame final *
            abstractTransferWord successProbability rest) *
              fixedPointRoleAwareStepTransferMatrix successProbability step := by
              rw [ih]
        _ = activeFrame sourceFrame targetFrame final *
            (abstractTransferWord successProbability rest *
              fixedPointRoleAwareStepTransferMatrix successProbability step) :=
            Matrix.mul_assoc _ _ _

/-- The image-phase compiler respects expression evaluation.  This is an
internal generator theorem, not an extra scientific-input assumption. -/
structure PlanPhaseEvaluation {n : Nat} (plan : Plan n) : Prop where
  source : ∀ angle : AngleExpr,
    circuitDenotation (plan.sourcePhase angle) =
      circuitDenotation (plan.sourcePhase (.const (angle.eval (fun _ : String => 0))))
  target : ∀ angle : AngleExpr,
    circuitDenotation (plan.targetPhase angle) =
      circuitDenotation (plan.targetPhase (.const (angle.eval (fun _ : String => 0))))

theorem step_denotation_eval {n : Nat} (plan : Plan n)
    (evaluation : PlanPhaseEvaluation plan) (step : PhaseProgramStep) :
    circuitDenotation (plan.step step) =
      realStepOperator plan (step.eval (fun _ : String => 0)) := by
  cases step with
  | signal direction => cases direction <;> rfl
  | projectorPhase role angle =>
      cases role with
      | source => exact evaluation.source angle
      | target => exact evaluation.target angle

/-- This also handles the `.neg` expressions generated by the conjugate
branch; no syntactic identification with a real constant is required. -/
theorem word_denotation_eval {n : Nat} (plan : Plan n)
    (evaluation : PlanPhaseEvaluation plan) (program : List PhaseProgramStep) :
    circuitDenotation (plan.word program) =
      realOperatorWord plan (program.map (PhaseProgramStep.eval (fun _ : String => 0))) := by
  unfold circuitDenotation Plan.word realOperatorWord
  rw [Circuit.denote_sequence_eq_operatorSequence]
  induction program with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.map_cons, operatorSequence] at ih ⊢
      rw [ih]
      exact congrArg (fun operator =>
        operatorSequence (List.map (realStepOperator plan)
          (List.map (PhaseProgramStep.eval (fun _ : String => 0)) rest)) * operator)
        (step_denotation_eval plan evaluation step)

end
end M13bFiniteOuterTwoFrame
