import QLean.SignalProcessing.M13bGramBoundaryWitness
import QLean.SignalProcessing.M13bUnitaritySemanticVerification

set_option autoImplicit false

namespace M13bGramBoundaryTransferUnitary

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness
open SpectralSamplingProof.Analytic
open NativeQSPWitnessTransferModel

/-- At the Gram boundary `p = 1`, the forward signal transfer is the
coordinate swap.  Its unitarity is therefore a closed `Fin 2` calculation,
with no strict-singular-pair hypothesis. -/
theorem boundary_signal_forward_unitary :
    Matrix.conjTranspose (fixedPointSignalTransferMatrix 1 .forward) *
      fixedPointSignalTransferMatrix 1 .forward = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [fixedPointSignalTransferMatrix, fixedPointSourceAmplitude,
      fixedPointTargetAmplitude, Matrix.conjTranspose_apply, Matrix.mul_apply]

theorem boundary_signal_adjoint_unitary :
    Matrix.conjTranspose (fixedPointSignalTransferMatrix 1 .adjoint) *
      fixedPointSignalTransferMatrix 1 .adjoint = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [fixedPointSignalTransferMatrix, fixedPointSourceAmplitude,
      fixedPointTargetAmplitude, Matrix.conjTranspose_apply, Matrix.mul_apply]

theorem boundary_transfer_step_unitary (step : FixedPointRoleAwarePhaseStep) :
    Matrix.conjTranspose (fixedPointRoleAwareStepTransferMatrix 1 step) *
      fixedPointRoleAwareStepTransferMatrix 1 step = 1 := by
  cases step with
  | signal direction =>
      cases direction
      · exact boundary_signal_forward_unitary
      · exact boundary_signal_adjoint_unitary
  | projectorPhase role angle =>
      exact M13bUnitaritySemanticVerification.phase_transfer_unitary role angle

theorem boundary_transfer_word_unitary (steps : List FixedPointRoleAwarePhaseStep) :
    Matrix.conjTranspose (abstractTransferWord 1 steps) *
      abstractTransferWord 1 steps = 1 := by
  induction steps with
  | nil => simp [abstractTransferWord, VerifiedCircuitCore.operatorSequence]
  | cons first rest ih =>
      change Matrix.conjTranspose
          (abstractTransferWord 1 rest * fixedPointRoleAwareStepTransferMatrix 1 first) *
          (abstractTransferWord 1 rest * fixedPointRoleAwareStepTransferMatrix 1 first) = 1
      rw [Matrix.conjTranspose_mul]
      calc
        (Matrix.conjTranspose (fixedPointRoleAwareStepTransferMatrix 1 first) *
          Matrix.conjTranspose (abstractTransferWord 1 rest)) *
          (abstractTransferWord 1 rest * fixedPointRoleAwareStepTransferMatrix 1 first) =
          Matrix.conjTranspose (fixedPointRoleAwareStepTransferMatrix 1 first) *
            (Matrix.conjTranspose (abstractTransferWord 1 rest) *
              abstractTransferWord 1 rest) *
            fixedPointRoleAwareStepTransferMatrix 1 first := by noncomm_ring
        _ = Matrix.conjTranspose (fixedPointRoleAwareStepTransferMatrix 1 first) *
            fixedPointRoleAwareStepTransferMatrix 1 first := by rw [ih]; simp
        _ = 1 := boundary_transfer_step_unitary first

end M13bGramBoundaryTransferUnitary
