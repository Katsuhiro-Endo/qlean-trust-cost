import QLean.SignalProcessing.NativeConcreteP18QSPWitness

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace M13bUnitaritySemanticVerification

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness
open SpectralSamplingProof.Analytic
open NativeQSPWitnessTransferModel

theorem phase_transfer_unitary (role : FixedPointProjectorRole) (angle : ℝ) :
    Matrix.conjTranspose (fixedPointProjectorTransferMatrix role angle) *
      fixedPointProjectorTransferMatrix role angle = 1 := by
  have hphase :
      (starRingEnd ℂ) (Complex.exp (Complex.I * (angle : ℂ))) *
        Complex.exp (Complex.I * (angle : ℂ)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have hstar :
        (starRingEnd ℂ) (Complex.I * (angle : ℂ)) =
          -(Complex.I * (angle : ℂ)) := by
      simp
    rw [hstar]
    have hzero :
        -(Complex.I * (angle : ℂ)) + Complex.I * (angle : ℂ) = 0 := by
      ring
    rw [hzero, Complex.exp_zero]
  ext row column
  cases role <;> fin_cases row <;> fin_cases column <;>
    simp [fixedPointProjectorTransferMatrix, fixedPointSourceIndex,
      fixedPointTargetIndex, Matrix.mul_apply, hphase]

theorem strict_signal_forward_unitary
    {source : ExecutableHistoryExecutableHistory.AlignedCommonSource119}
    {assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source}
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    Matrix.conjTranspose
        (fixedPointSignalTransferMatrix (pair.sigma ^ 2) .forward) *
      fixedPointSignalTransferMatrix (pair.sigma ^ 2) .forward = 1 := by
  rw [← strictPair_forward_transfer119 pair]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [NativeSingularPairTwoFrame.singularTransferMatrix,
      Matrix.conjTranspose_apply, Matrix.mul_apply]
  · norm_cast
    nlinarith [pair.completion]
  · ring
  · ring
  · norm_cast
    nlinarith [pair.completion]

theorem strict_signal_adjoint_unitary
    {source : ExecutableHistoryExecutableHistory.AlignedCommonSource119}
    {assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source}
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    Matrix.conjTranspose
        (fixedPointSignalTransferMatrix (pair.sigma ^ 2) .adjoint) *
      fixedPointSignalTransferMatrix (pair.sigma ^ 2) .adjoint = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [fixedPointSignalTransferMatrix, fixedPointSourceAmplitude_strictPair119 pair,
      fixedPointTargetAmplitude_strictPair119 pair,
      Matrix.conjTranspose_apply, Matrix.mul_apply]
  · norm_cast
    nlinarith [pair.completion]
  · ring
  · ring
  · norm_cast
    nlinarith [pair.completion]

theorem strict_transfer_step_unitary
    {source : ExecutableHistoryExecutableHistory.AlignedCommonSource119}
    {assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source}
    (pair : ExecutableP18StrictSingularPair119 source assumptions)
    (step : FixedPointRoleAwarePhaseStep) :
    Matrix.conjTranspose
        (fixedPointRoleAwareStepTransferMatrix (pair.sigma ^ 2) step) *
      fixedPointRoleAwareStepTransferMatrix (pair.sigma ^ 2) step = 1 := by
  cases step with
  | signal direction =>
      cases direction
      · exact strict_signal_forward_unitary pair
      · exact strict_signal_adjoint_unitary pair
  | projectorPhase role angle =>
      exact phase_transfer_unitary role angle

theorem strict_transfer_word_unitary
    {source : ExecutableHistoryExecutableHistory.AlignedCommonSource119}
    {assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source}
    (pair : ExecutableP18StrictSingularPair119 source assumptions)
    (steps : List FixedPointRoleAwarePhaseStep) :
    Matrix.conjTranspose (abstractTransferWord (pair.sigma ^ 2) steps) *
      abstractTransferWord (pair.sigma ^ 2) steps = 1 := by
  induction steps with
  | nil => simp [abstractTransferWord, VerifiedCircuitCore.operatorSequence]
  | cons first rest ih =>
      change Matrix.conjTranspose
          (abstractTransferWord (pair.sigma ^ 2) rest *
            fixedPointRoleAwareStepTransferMatrix (pair.sigma ^ 2) first) *
          (abstractTransferWord (pair.sigma ^ 2) rest *
            fixedPointRoleAwareStepTransferMatrix (pair.sigma ^ 2) first) = 1
      rw [Matrix.conjTranspose_mul]
      calc
        (Matrix.conjTranspose
            (fixedPointRoleAwareStepTransferMatrix (pair.sigma ^ 2) first) *
          Matrix.conjTranspose (abstractTransferWord (pair.sigma ^ 2) rest)) *
          (abstractTransferWord (pair.sigma ^ 2) rest *
            fixedPointRoleAwareStepTransferMatrix (pair.sigma ^ 2) first) =
          Matrix.conjTranspose
              (fixedPointRoleAwareStepTransferMatrix (pair.sigma ^ 2) first) *
            (Matrix.conjTranspose (abstractTransferWord (pair.sigma ^ 2) rest) *
              abstractTransferWord (pair.sigma ^ 2) rest) *
            fixedPointRoleAwareStepTransferMatrix (pair.sigma ^ 2) first := by
            noncomm_ring
        _ = Matrix.conjTranspose
              (fixedPointRoleAwareStepTransferMatrix (pair.sigma ^ 2) first) *
            fixedPointRoleAwareStepTransferMatrix (pair.sigma ^ 2) first := by
            rw [ih]
            simp
        _ = 1 := strict_transfer_step_unitary pair first

end M13bUnitaritySemanticVerification
