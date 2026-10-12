import QLean.SignalProcessing.QSPDefaultPhaseProvider
import VerifiedMath.Quantum.QSPWordShape

/-! The generic provider uses the prescribed degree. Only the phase values
are chosen by the QSP existence theorem; the alternating shape is fixed. -/

set_option autoImplicit false
set_option warningAsError true

namespace VerifiedMath.Quantum.QSP

open SpectralSamplingProof.Analytic

theorem alternatingWord_shape (angles : List ℝ) (offset : Nat) :
    (((phaseScheduleProofsWordToFixed037 (alternatingAnglesWord037Aux offset angles)).map
      roleStepToGeneric).map Step.shape) = alternatingShapeFrom offset angles.length := by
  induction angles generalizing offset with
  | nil => rfl
  | cons angle rest ih =>
      cases rest with
      | nil =>
          by_cases even : offset % 2 = 0 <;>
            simp [alternatingAnglesWord037Aux, phaseScheduleProofsWordToFixed037,
              phaseScheduleProofsStepToFixed037, phaseScheduleProofsRoleToFixed037,
              roleStepToGeneric, Step.shape, alternatingShapeFrom, even]
      | cons next tail =>
          have restShape := ih (offset + 1)
          by_cases even : offset % 2 = 0 <;>
            simpa [alternatingAnglesWord037Aux, phaseScheduleProofsWordToFixed037,
              phaseScheduleProofsStepToFixed037, phaseScheduleProofsRoleToFixed037,
              phaseScheduleProofsDirectionToFixed037, JenningsHistory.alternatingDirection,
              roleStepToGeneric, Step.shape, alternatingShapeFrom, even] using restShape

theorem defaultPhaseProvider_odd_shape (request : AdmissibleRealPolynomial)
    (oddDegree : request.degree % 2 = 1) :
    (defaultPhaseProvider request).map Step.shape = alternatingShapeFrom 0 (request.degree + 1) := by
  rw [defaultPhaseProvider_odd_steps request oddDegree]
  unfold approvedOddPhysicalWord alternatingFixedWord037 alternatingAnglesWord037
  rw [alternatingWord_shape, liftFirstAngles037_length, approvedOddAngles_length]

theorem defaultPhaseProvider_finite_odd_shape (request : FinitePolynomialRequest)
    (oddDegree : request.degree % 2 = 1) :
    (defaultPhaseProvider request).map Step.shape = request.expectedShape :=
  defaultPhaseProvider_odd_shape request.approved oddDegree

end VerifiedMath.Quantum.QSP
