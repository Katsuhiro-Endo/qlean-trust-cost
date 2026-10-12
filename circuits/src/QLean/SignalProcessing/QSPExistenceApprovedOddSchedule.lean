import QLean.SignalProcessing.QSPExistenceApprovedSchedule

/-!
The application-independent signed-polynomial input produces a physically
alternating, phase-compensated word when its degree is odd.  This module does
not refer to a Q matrix, history register, or kernel reflection.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore
open JenningsHistory
open NativeQSPWitnessTwoFrameModel
open NativeConcreteP18QSPWitness

noncomputable section

def approvedOddShapedWord
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1) :
    ShapedQSPWordSynthesis040 (GeneralRealQSPPolynomial127.ofApproved input) := by
  exact approvedShapedWord input (by omega)

def approvedOddAngles
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1) : List ℝ :=
  let shaped := approvedOddShapedWord input oddDegree
  compensatedFirstAngles042 shaped.angles (oddAngleSum037 shaped.angles)

theorem approvedOddAngles_ge_two
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1) :
    2 ≤ (approvedOddAngles input oddDegree).length := by
  unfold approvedOddAngles
  rw [compensatedFirstAngles042_length]
  exact (approvedOddShapedWord input oddDegree).angles_ge_two

theorem approvedOddAngles_length
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1) :
    (approvedOddAngles input oddDegree).length = input.degree + 1 := by
  unfold approvedOddAngles
  rw [compensatedFirstAngles042_length]
  simpa [GeneralRealQSPPolynomial127.ofApproved] using
    shapedAngles_length042 (GeneralRealQSPPolynomial127.ofApproved input)
      (approvedOddShapedWord input oddDegree)

def approvedOddPhaseSchedule
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1) :
    PhaseSchedule (approvedOddAngles input oddDegree).length :=
  phaseScheduleOfAngles037 (approvedOddAngles input oddDegree)
    (approvedOddAngles_ge_two input oddDegree)

def approvedOddPhysicalWord
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1) :
    List FixedPointRoleAwarePhaseStep :=
  alternatingFixedWord037 (liftFirstAngles037 (approvedOddAngles input oddDegree))

theorem approvedOddPhysicalWord_eq_general
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1) :
    approvedOddPhysicalWord input oddDegree =
      approvedPhysicalWord input (by omega) := by
  rfl

theorem approvedOddPhysicalWord_frame
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1) :
    FrameWord .source (approvedOddPhysicalWord input oddDegree) .target := by
  have hlen :
      (liftFirstAngles037 (approvedOddAngles input oddDegree)).length =
        input.degree + 1 := by
    rw [liftFirstAngles037_length, approvedOddAngles_length]
  have hend :
      alternatingFinalFrame119
          (liftFirstAngles037 (approvedOddAngles input oddDegree)).length =
        .target := by
    rw [hlen]
    have heven : (input.degree + 1) % 2 = 0 := by omega
    simp [alternatingFinalFrame119, heven]
  simpa [approvedOddPhysicalWord, hend] using
    alternatingFixedWord037_frameWord119
      (liftFirstAngles037 (approvedOddAngles input oddDegree))

theorem approvedOddPhaseSchedule_response
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1)
    (x : ℝ) (lower : -1 ≤ x) (upper : x ≤ 1) :
    (scheduleResponse (approvedOddPhaseSchedule input oddDegree) x).re =
      input.singularValueResponse x := by
  have hodd : (GeneralRealQSPPolynomial127.ofApproved input).degree % 2 = 1 :=
    oddDegree
  have h := compensatedScheduleResponse_real042
    (GeneralRealQSPPolynomial127.ofApproved input)
    (approvedOddShapedWord input oddDegree) hodd x lower upper
  simpa [approvedOddPhaseSchedule, approvedOddAngles,
    GeneralRealQSPPolynomial127.ofApproved,
    VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial.singularValueResponse] using h

/-- The very framed physical word has the approved scalar response on the
nonnegative singular-value domain.  The success probability is `1 - x²`;
the result is not obtained by identifying a probability with a signed x. -/
theorem approvedOddPhysicalWord_response
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1)
    (x : ℝ) (nonnegative : 0 ≤ x) (atMostOne : x ≤ 1) :
    ((fixedPointSourceOrderTransferMatrix (1 - x ^ 2)
        (approvedOddPhysicalWord input oddDegree)).mulVec sourceBasis 0).re =
      input.singularValueResponse x := by
  have h := approvedOddPhaseSchedule_response input oddDegree x
    (by linarith) atMostOne
  unfold approvedOddPhaseSchedule at h
  unfold scheduleResponse at h
  rw [phaseWord_schedule_matrix_eq_alternating037 nonnegative atMostOne
    (approvedOddAngles input oddDegree)
    (approvedOddAngles_ge_two input oddDegree)] at h
  exact h

theorem approvedOddPhysicalWord_hermitianizedResponse
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1)
    (x : ℝ) (nonnegative : 0 ≤ x) (atMostOne : x ≤ 1) :
    2 * ((fixedPointSourceOrderTransferMatrix (1 - x ^ 2)
        (approvedOddPhysicalWord input oddDegree)).mulVec sourceBasis 0).re ^ 2 - 1 =
      input.hermitianizedResponse x := by
  rw [approvedOddPhysicalWord_response input oddDegree x nonnegative atMostOne]
  rfl

end

end SpectralSamplingProof.Analytic
