import QLean.SignalProcessing.QSPExistenceSignedEndpointSchedule
import QLean.SignalProcessing.NativeConcreteP18QSPWitness

/-!
# Parity-generic physical QSP schedule

The human-facing polynomial is defined on `[-1,1]` and is even or odd
according to its declared degree.  The physical singular-value variable is
only `x ∈ [0,1]`.  A positive-degree request is compiled to an alternating
two-frame word.  Even degree ends in the source frame, odd degree in the
target frame; the negative half of the polynomial is recovered solely from
the approved parity law.

This module is application independent: it imports no history matrix, Q
matrix, kernel request, or benchmark.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore
open JenningsHistory
open NativeQSPWitnessTwoFrameModel
open NativeQSPWitnessTransferModel
open NativeConcreteP18QSPWitness

noncomputable section

def approvedShapedWord
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (positiveDegree : 0 < input.degree) :
    ShapedQSPWordSynthesis040 (GeneralRealQSPPolynomial127.ofApproved input) :=
  Classical.choice (exists_shapedQSPWordSynthesis040
    (GeneralRealQSPPolynomial127.ofApproved input) positiveDegree)

def approvedAngles
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (positiveDegree : 0 < input.degree) : List ℝ :=
  let shaped := approvedShapedWord input positiveDegree
  compensatedFirstAngles042 shaped.angles (oddAngleSum037 shaped.angles)

theorem approvedAngles_ge_two
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (positiveDegree : 0 < input.degree) :
    2 ≤ (approvedAngles input positiveDegree).length := by
  unfold approvedAngles
  rw [compensatedFirstAngles042_length]
  exact (approvedShapedWord input positiveDegree).angles_ge_two

def approvedPhaseSchedule
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (positiveDegree : 0 < input.degree) :
    PhaseSchedule (approvedAngles input positiveDegree).length :=
  phaseScheduleOfAngles037 (approvedAngles input positiveDegree)
    (approvedAngles_ge_two input positiveDegree)

def approvedPhysicalWord
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (positiveDegree : 0 < input.degree) :
    List FixedPointRoleAwarePhaseStep :=
  alternatingFixedWord037 (liftFirstAngles037
    (approvedAngles input positiveDegree))

theorem approvedPhaseSchedule_response_nonnegative
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (positiveDegree : 0 < input.degree)
    (x : ℝ) (nonnegative : 0 ≤ x) (atMostOne : x ≤ 1) :
    (scheduleResponse (approvedPhaseSchedule input positiveDegree) x).re =
      input.singularValueResponse x := by
  have h := compensatedScheduleResponse_nonneg042
    (GeneralRealQSPPolynomial127.ofApproved input)
    (approvedShapedWord input positiveDegree) x nonnegative atMostOne
  have hreal := congrArg Complex.re h
  have hread := completionStandardState033_real_readout
    (GeneralRealQSPPolynomial127.ofApproved input) x
  have hP :
      (completionPair024 (GeneralRealQSPPolynomial127.ofApproved input)).P =
        input.polynomial := rfl
  rw [hread, hP] at hreal
  simpa [approvedPhaseSchedule, approvedAngles,
    VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial.singularValueResponse]
    using hreal

theorem approvedPhysicalWord_response_nonnegative
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (positiveDegree : 0 < input.degree)
    (x : ℝ) (nonnegative : 0 ≤ x) (atMostOne : x ≤ 1) :
    ((fixedPointSourceOrderTransferMatrix (1 - x ^ 2)
        (approvedPhysicalWord input positiveDegree)).mulVec sourceBasis 0).re =
      input.singularValueResponse x := by
  have h := approvedPhaseSchedule_response_nonnegative input positiveDegree x
    nonnegative atMostOne
  unfold approvedPhaseSchedule at h
  unfold scheduleResponse at h
  rw [phaseWord_schedule_matrix_eq_alternating037 nonnegative atMostOne
    (approvedAngles input positiveDegree)
    (approvedAngles_ge_two input positiveDegree)] at h
  exact h

/-- The parity-generic physical word as an independent two-projector phase
plan.  No project circuit occurs in this value. -/
def approvedPhysicalPlan
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (positiveDegree : 0 < input.degree) : TwoProjectorQSPPhasePlan where
  steps := approvedPhysicalWord input positiveDegree
  globalPhase := 1
  globalPhase_unitNormSq := by norm_num

theorem approvedPhysicalPlan_certificate
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (positiveDegree : 0 < input.degree) :
    TwoProjectorQSPRealizationCertificate
      (nativeQSPTarget024 (GeneralRealQSPPolynomial127.ofApproved input))
      (approvedPhysicalPlan input positiveDegree) := by
  constructor
  · intro successProbability promised
    let x := Real.sqrt (1 - successProbability)
    have hs0 : 0 ≤ successProbability := promised.1
    have hs1 : successProbability ≤ 1 := promised.2
    have harg : 0 ≤ 1 - successProbability := by linarith
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have hx1 : x ≤ 1 := by
      have hsq : x ^ 2 = 1 - successProbability := Real.sq_sqrt harg
      nlinarith [sq_nonneg x]
    have hprob : 1 - x ^ 2 = successProbability := by
      rw [Real.sq_sqrt harg]
      ring
    have hsource : fixedPointSourceAmplitude successProbability = x := by
      unfold fixedPointSourceAmplitude
      rw [max_eq_right harg]
    have hresponse := approvedPhysicalWord_response_nonnegative
      input positiveDegree x hx0 hx1
    rw [hprob] at hresponse
    simpa [approvedPhysicalPlan,
      TwoProjectorQSPPhasePlan.realizedScalarResponse,
      TwoProjectorQSPPhasePlan.complexFailureAmplitude,
      fixedPointRealizedComplexFailureAmplitude, fixedPointEvaluatedState,
      fixedPointSourceBasisState, fixedPointSourceIndex,
      JenningsHistory.sourceBasis, phaseCorrectedRealFailureAmplitude,
      nativeQSPTarget024, GeneralRealQSPPolynomial127.ofApproved,
      VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial.singularValueResponse,
      hsource, x] using hresponse
  · exact nativeQSPTarget024_parityLaw _

end

end SpectralSamplingProof.Analytic
