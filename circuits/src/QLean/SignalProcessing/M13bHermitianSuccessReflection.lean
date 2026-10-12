import QLean.SignalProcessing.M13bConjugateControlledCompute
import QLean.SignalProcessing.M13bControlXStateSemantics

set_option autoImplicit false

namespace M13bHermitianSuccessReflection

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness

noncomputable section

noncomputable def externalControlPiPhase119
    (_symbolValue : String → ℝ) (n : Nat) : Circuit (PrimitiveGate (n + 3)) :=
  .gate (.phaseShift (.const Real.pi)
    (M13bExternallyControlledCompute.m13bExternalControlLayout n).control)

theorem controlledState_zero_at_wrong_control
    (n : Nat) (controlValue : Bool) (state : State (QubitBasis n))
    (output : QubitBasis (n + 3))
    (wrong : output (M13bExternallyControlledCompute.m13bExternalControlLayout n).control ≠
      controlValue) :
    M13bControlledStateSemantics.m13bControlledState n controlValue state output = 0 := by
  unfold M13bControlledStateSemantics.m13bControlledState fixedOutsideStateEmbedding
  apply if_neg
  intro outsideEqual
  let layout := M13bExternallyControlledCompute.m13bExternalControlLayout n
  let controlOutside : OutsideWire layout.placement := ⟨layout.control, by
    intro source
    exact (layout.control_ne_placed source).symm⟩
  have atControl := congrFun outsideEqual controlOutside
  have outputControl : output layout.control = controlValue := by
    have layoutControl : layout.control =
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control := rfl
    simpa [restrictToOutsideWires, M13bExternallyControlledCompute.m13bControlOutside,
      controlOutside, layoutControl] using atControl
  exact wrong (by simpa [layout] using outputControl)

theorem externalControlPiPhase119_apply_control_false
    (symbolValue : String → ℝ) (n : Nat) (state : State (QubitBasis n)) :
    applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (externalControlPiPhase119 symbolValue n))
      (M13bControlledStateSemantics.m13bControlledState n false state) =
      M13bControlledStateSemantics.m13bControlledState n false state := by
  unfold externalControlPiPhase119
  change applyOperator
      (embedSingleQubitOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
        (localPhaseShift Real.pi))
      (M13bControlledStateSemantics.m13bControlledState n false state) = _
  unfold M13bControlledStateSemantics.m13bControlledState
  funext output
  rw [applyOperator_embedSingleQubitOperator_state, Fintype.sum_bool]
  by_cases outputTrue : output
      (M13bExternallyControlledCompute.m13bExternalControlLayout n).control = true
  · have replaceTrue : replaceQubitWire output
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control true = output := by
      simpa [outputTrue] using replaceQubitWire_self output
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
    rw [replaceTrue]
    have outputZero := controlledState_zero_at_wrong_control n false state output (by simp [outputTrue])
    change fixedOutsideStateEmbedding
      (M13bExternallyControlledCompute.m13bExternalControlLayout n).placement
      (M13bExternallyControlledCompute.m13bControlOutside n false) state output = 0 at outputZero
    simp only [localPhaseShift, localPhase, outputTrue]
    rw [outputZero]
    norm_num
  · have outputFalse : output
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control = false :=
      Bool.eq_false_of_not_eq_true outputTrue
    have replaceFalse : replaceQubitWire output
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control false = output := by
      simpa [outputFalse] using replaceQubitWire_self output
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
    rw [replaceFalse]
    simp [localPhaseShift, localPhase, outputFalse]

theorem externalControlPiPhase119_apply_control_true
    (symbolValue : String → ℝ) (n : Nat) (state : State (QubitBasis n)) :
    applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (externalControlPiPhase119 symbolValue n))
      (M13bControlledStateSemantics.m13bControlledState n true state) =
      - M13bControlledStateSemantics.m13bControlledState n true state := by
  unfold externalControlPiPhase119
  change applyOperator
      (embedSingleQubitOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
        (localPhaseShift Real.pi))
      (M13bControlledStateSemantics.m13bControlledState n true state) = _
  unfold M13bControlledStateSemantics.m13bControlledState
  funext output
  rw [applyOperator_embedSingleQubitOperator_state, Fintype.sum_bool]
  by_cases outputTrue : output
      (M13bExternallyControlledCompute.m13bExternalControlLayout n).control = true
  · have replaceTrue : replaceQubitWire output
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control true = output := by
      simpa [outputTrue] using replaceQubitWire_self output
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
    rw [replaceTrue]
    have hpi : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
      rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring]
      exact Complex.exp_pi_mul_I
    simp only [localPhaseShift, localPhase, outputTrue]
    rw [hpi]
    norm_num
  · have outputFalse : output
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control = false :=
      Bool.eq_false_of_not_eq_true outputTrue
    have replaceFalse : replaceQubitWire output
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control false = output := by
      simpa [outputFalse] using replaceQubitWire_self output
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control
    rw [replaceFalse]
    have outputZero := controlledState_zero_at_wrong_control n true state output (by simp [outputFalse])
    change fixedOutsideStateEmbedding
      (M13bExternallyControlledCompute.m13bExternalControlLayout n).placement
      (M13bExternallyControlledCompute.m13bControlOutside n true) state output = 0 at outputZero
    simp only [localPhaseShift, localPhase, outputFalse]
    rw [outputZero]
    norm_num
    exact outputZero

end

end M13bHermitianSuccessReflection
