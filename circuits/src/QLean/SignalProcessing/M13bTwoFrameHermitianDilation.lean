import QLean.SignalProcessing.M13bControlXStateSemantics

/-!
# M13b: physical two-frame Hermitian dilation

For a non-normal signal word `U`, the Hermitian dilation relevant to the
strict singular-pair witness is not `H * diag(U,U†) * H` on one common frame.
It is the off-diagonal control dilation: the existing clean selector followed
by one physical control `X`.  Its two invariant branches carry the distinct
source and target frames.
-/

set_option autoImplicit false

namespace M13bTwoFrameHermitianDilation

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness

noncomputable section

/-- Lift a two-column physical frame into one explicit external-control
branch, retaining the two compiler work wires in their fixed clean state. -/
def controlledFrame119 (n : Nat) (controlValue : Bool)
    (frame : Matrix (QubitBasis n) (Fin 2) ℂ) :
    Matrix (QubitBasis (n + 3)) (Fin 2) ℂ :=
  fun output column =>
    M13bControlledStateSemantics.m13bControlledState n controlValue
      (fun input => frame input column) output

/-- Fixed-outside control embedding is linear in the frame columns, so it
commutes with the transfer matrices used by the strict two-frame witness. -/
theorem controlledFrame119_mul (n : Nat) (controlValue : Bool)
    (frame : Matrix (QubitBasis n) (Fin 2) ℂ)
    (transfer : Matrix (Fin 2) (Fin 2) ℂ) :
    controlledFrame119 n controlValue (frame * transfer) =
      controlledFrame119 n controlValue frame * transfer := by
  classical
  ext output column
  have state_expand :
      (fun input => (frame * transfer) input column) =
        ∑ coordinate : Fin 2, transfer coordinate column •
          (fun input => frame input coordinate) := by
    funext input
    change (∑ coordinate : Fin 2, frame input coordinate *
        transfer coordinate column) =
      ∑ coordinate : Fin 2, transfer coordinate column * frame input coordinate
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  unfold controlledFrame119
  rw [state_expand]
  simp only [Matrix.mul_apply]
  unfold M13bControlledStateSemantics.m13bControlledState
  rw [fixedOutsideStateEmbedding_finset_sum119]
  simp_rw [fixedOutsideStateEmbedding_smul119]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

end

end M13bTwoFrameHermitianDilation
