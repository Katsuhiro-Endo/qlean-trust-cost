import QLean.SignalProcessing.M13bHadamardBasisSemanticVerification

/-!
# M13b: physical external-control Hadamard semantics

This public module exposes the verified action of the actual primitive
Hadamard on the compiler-clean external-control block.  It is deliberately
separate from the selector algebra: the result is a full-state equality for
the gate that occurs in the emitted `H--selector--H` circuit.
-/

set_option autoImplicit false

namespace M13bHadamardStateSemantics

open VerifiedCircuitCore

noncomputable section

theorem controlHadamard_state_false
    (n : Nat) (state : State (QubitBasis n)) :
    applyOperator
      (embedSingleQubitOperator
        (M13bExternallyControlledCompute.m13bExternalControlLayout n).control localH)
      (M13bControlledStateSemantics.m13bControlledState n false state) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n false state +
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n true state :=
  M13bHadamardBasisSemanticVerification.m13bHadamard_state_false n state

/-- The actual primitive gate stored in the clean component has precisely the
same coherent action; no abstract denotation is substituted for the circuit. -/
theorem cleanControlH_actual_apply_control_false_state
    (symbolValue : String → ℝ) (n : Nat) (state : State (QubitBasis n)) :
    applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (M13bExternallyControlledCompute.m13bCleanControlHComponent
        symbolValue n).circuit)
      (M13bControlledStateSemantics.m13bControlledState n false state) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n false state +
      ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        M13bControlledStateSemantics.m13bControlledState n true state := by
  exact controlHadamard_state_false n state

end

end M13bHadamardStateSemantics
