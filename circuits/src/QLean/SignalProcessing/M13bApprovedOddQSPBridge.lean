import QLean.SignalProcessing.QSPExistenceApprovedOddSchedule
import QLean.SignalProcessing.QSPDefaultPhaseProvider
import QLean.SignalProcessing.M13bSpecification
import QLean.SignalProcessing.M13bChebyshevCoordinateBridge

/-!
Bridge from the application-independent, physically alternating odd-degree
QSP word to the independent two-dimensional response contract used by the
primitive QSVT correspondence theorem.  The QSVT variable is the target
amplitude `sigma`; the polynomial variable is the complementary source
amplitude `sqrt (1 - sigma²)`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

namespace M13bApprovedOddQSPBridge

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic
open NativeQSPWitnessTwoFrameModel
open NativeQSPWitnessTransferModel
open M13bGramFullCompressedAction
open M13bSpecification
open NativeFixedPointPrimitive
open NativeSignalQSVTFunctionalBridge
open M13bPrimitiveCandidate

noncomputable section

private theorem sourceOrder_eq_abstract
    (probability : ℝ) (steps : List FixedPointRoleAwarePhaseStep) :
    fixedPointSourceOrderTransferMatrix probability steps =
      abstractTransferWord probability steps := by
  let matrixOf := fixedPointRoleAwareStepTransferMatrix probability
  have aux : ∀ (word : List FixedPointRoleAwarePhaseStep)
      (acc : FixedPointTransferMatrix),
      word.foldl (fun current step => matrixOf step * current) acc =
        operatorSequence (word.map matrixOf) * acc := by
    intro word
    induction word with
    | nil =>
        intro acc
        simp [operatorSequence]
    | cons step rest ih =>
        intro acc
        simp only [List.foldl_cons, List.map_cons, operatorSequence]
        rw [ih]
        simp only [mul_assoc]
  unfold fixedPointSourceOrderTransferMatrix abstractTransferWord
  simpa [matrixOf] using aux steps 1

private theorem sourceBasis_readout
    (matrix : FixedPointTransferMatrix) :
    matrix.mulVec JenningsHistory.sourceBasis 0 = matrix 0 0 := by
  simp [JenningsHistory.sourceBasis, Matrix.mulVec, dotProduct]

def approvedOddKernelRequest
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial) :
    VerifiedMath.Quantum.QSP.Request where
  target := fun sigma =>
    input.hermitianizedResponse (Real.sqrt (1 - sigma ^ 2))
  error := 0
  error_nonneg := le_refl 0

theorem approvedOddWord_satisfies
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1) :
    VerifiedMath.Quantum.QSP.Satisfies
      (approvedOddKernelRequest input)
      ((approvedOddPhysicalWord input oddDegree).map toPureQSPStep119) := by
  constructor
  · exact frameWord_to_pureQSP119
      (approvedOddPhysicalWord_frame input oddDegree)
  · intro sigma sigma_nonneg sigma_le_one
    let x := Real.sqrt (1 - sigma ^ 2)
    have hnonneg : 0 ≤ 1 - sigma ^ 2 := by nlinarith
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have hx1 : x ≤ 1 := by
      have hsq : x ^ 2 = 1 - sigma ^ 2 := Real.sq_sqrt hnonneg
      nlinarith [sq_nonneg sigma]
    have hprob : 1 - x ^ 2 = sigma ^ 2 := by
      rw [Real.sq_sqrt hnonneg]
      ring
    have hresponse := approvedOddPhysicalWord_hermitianizedResponse
      input oddDegree x hx0 hx1
    rw [hprob] at hresponse
    have hmatrix :
        fixedPointSourceOrderTransferMatrix (sigma ^ 2)
            (approvedOddPhysicalWord input oddDegree) =
          VerifiedMath.Quantum.QSP.wordTransfer (sigma ^ 2)
            ((approvedOddPhysicalWord input oddDegree).map toPureQSPStep119) := by
      rw [sourceOrder_eq_abstract, abstractTransferWord_eq_pureQSP119]
    rw [hmatrix, sourceBasis_readout] at hresponse
    simp [VerifiedMath.Quantum.QSP.hermitianResponse,
      approvedOddKernelRequest, x, hresponse]

theorem approvedOddWord_exact_response
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1)
    (sigma : ℝ) (nonnegative : 0 ≤ sigma) (atMostOne : sigma ≤ 1) :
    VerifiedMath.Quantum.QSP.hermitianResponse
        ((approvedOddPhysicalWord input oddDegree).map toPureQSPStep119) sigma =
      input.hermitianizedResponse (Real.sqrt (1 - sigma ^ 2)) := by
  have h := (approvedOddWord_satisfies input oddDegree).2 sigma
    nonnegative atMostOne
  change |VerifiedMath.Quantum.QSP.hermitianResponse
      ((approvedOddPhysicalWord input oddDegree).map toPureQSPStep119) sigma -
      input.hermitianizedResponse (Real.sqrt (1 - sigma ^ 2))| ≤ 0 at h
  rcases abs_le.mp h with ⟨lower, upper⟩
  linarith

/-- The theoretical provider selects real phases; a numerical provider may
instead supply a finite closed angle program.  Both use the same compiler. -/
noncomputable def approvedOddProgram
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1) : List PhaseProgramStep :=
  (approvedOddPhysicalWord input oddDegree).map PhaseProgramStep.ofReal

/-- The only application-specific premise here is an independent polynomial
approximation to the requested kernel response.  There is no premise about
the circuit's correctness or equality to a selected implementation. -/
theorem approvedOddProgram_meets
    (request : KernelSynthesisRequest119)
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial)
    (oddDegree : input.degree % 2 = 1)
    (polynomialError : ℝ) (polynomialError_pos : 0 < polynomialError)
    (polynomialError_lt_two : polynomialError < 2)
    (responseError : ℝ) (responseError_nonneg : 0 ≤ responseError)
    (budget : polynomialError + responseError ≤ request.epsilon)
    (approximation : ∀ sigma : ℝ, 0 ≤ sigma → sigma ≤ 1 →
      |input.hermitianizedResponse (Real.sqrt (1 - sigma ^ 2)) -
        continuousKernelResponse119 request.input polynomialError
          polynomialError_pos polynomialError_lt_two sigma| ≤ responseError) :
    PhaseProgramMeets119 request (approvedOddProgram input oddDegree) := by
  constructor
  · exact PhaseProgram.ofReal_isSymbolFree _
  constructor
  · simpa [approvedOddProgram, List.map_map, Function.comp_def] using
      approvedOddPhysicalWord_frame input oddDegree
  refine ⟨polynomialError, polynomialError_pos, polynomialError_lt_two,
    responseError, responseError_nonneg, budget, ?_⟩
  have hs : VerifiedMath.Quantum.QSP.Satisfies
      (kernelQSPResponseRequest119 request.input polynomialError
        polynomialError_pos polynomialError_lt_two responseError responseError_nonneg)
      ((approvedOddPhysicalWord input oddDegree).map toPureQSPStep119) := by
    constructor
    · exact (approvedOddWord_satisfies input oddDegree).1
    · intro sigma sigma_nonneg sigma_le_one
      rw [approvedOddWord_exact_response input oddDegree sigma
        sigma_nonneg sigma_le_one]
      exact approximation sigma sigma_nonneg sigma_le_one
  simpa [approvedOddProgram, List.map_map, Function.comp_def] using hs

/-- The kernel's Chebyshev polynomial is ordinary approved QSP data:
degree, parity, and boundedness are inherited from its scalar construction,
not from a preselected circuit or a phase-witness assumption. -/
def approvedChebyshevPolynomial
    (target : PhaseScheduleProofs.ChebyshevTarget125) :
    VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial where
  polynomial := (chebyshevGeneralInput041 target).polynomial
  degree := (chebyshevGeneralInput041 target).degree
  degree_bound := (chebyshevGeneralInput041 target).degree_bound
  parity_law := (chebyshevGeneralInput041 target).parity_law
  bounded_on_unitInterval :=
    (chebyshevGeneralInput041 target).bounded_on_unitInterval

theorem approvedChebyshevPolynomial_odd
    (target : PhaseScheduleProofs.ChebyshevTarget125) :
    (approvedChebyshevPolynomial target).degree % 2 = 1 :=
  target.L_odd

def approvedKernelPolynomial (request : KernelSynthesisRequest119) :
    VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial :=
  approvedChebyshevPolynomial
    (KernelQSPGeneralQSPIntegration.kernelChebyshevTargetQSP126
      (kernelQSPParameters119 request.input request.epsilon
        request.epsilon_pos request.epsilon_lt_two))

theorem approvedKernelPolynomial_odd (request : KernelSynthesisRequest119) :
    (approvedKernelPolynomial request).degree % 2 = 1 :=
  approvedChebyshevPolynomial_odd _

theorem approvedKernelPolynomial_exact_response
    (request : KernelSynthesisRequest119)
    (sigma : ℝ) (sigma_nonneg : 0 ≤ sigma) (sigma_le_one : sigma ≤ 1) :
    (approvedKernelPolynomial request).hermitianizedResponse
        (Real.sqrt (1 - sigma ^ 2)) =
      continuousKernelResponse119 request.input request.epsilon
        request.epsilon_pos request.epsilon_lt_two sigma := by
  let params := kernelQSPParameters119 request.input request.epsilon
    request.epsilon_pos request.epsilon_lt_two
  let x := Real.sqrt (1 - sigma ^ 2)
  have hnonneg : 0 ≤ 1 - sigma ^ 2 := by nlinarith
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hcompletion : x ^ 2 + sigma ^ 2 = 1 := by
    rw [Real.sq_sqrt hnonneg]
    ring
  have hcheb := M13bChebyshevCoordinateBridge.kernelQSP_chebyshev_response_at_complementary_amplitude
    params x sigma hx0 hcompletion
  have hpoly :
      (approvedKernelPolynomial request).singularValueResponse x =
        PhaseScheduleProofs.chebyshevResponse125
          (KernelQSPGeneralQSPIntegration.kernelChebyshevTargetQSP126 params) x := by
    exact chebyshevPolynomial041_eval _ x
  unfold VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial.hermitianizedResponse
  rw [hpoly, hcheb]
  rfl

noncomputable def approvedKernelProgram (request : KernelSynthesisRequest119) :
    List PhaseProgramStep :=
  approvedOddProgram (approvedKernelPolynomial request)
    (approvedKernelPolynomial_odd request)

theorem approvedKernelProgram_eq_odd (request : KernelSynthesisRequest119) :
    approvedKernelProgram request =
      approvedOddProgram (approvedKernelPolynomial request)
        (approvedKernelPolynomial_odd request) := by
  unfold approvedKernelProgram approvedOddProgram
  rfl

theorem approvedKernelProgram_meets (request : KernelSynthesisRequest119) :
    PhaseProgramMeets119 request (approvedKernelProgram request) := by
  have happrox : ∀ sigma : ℝ, 0 ≤ sigma → sigma ≤ 1 →
      |(approvedKernelPolynomial request).hermitianizedResponse
          (Real.sqrt (1 - sigma ^ 2)) -
        continuousKernelResponse119 request.input request.epsilon
          request.epsilon_pos request.epsilon_lt_two sigma| ≤ 0 := by
    intro sigma sigma_nonneg sigma_le_one
    rw [approvedKernelPolynomial_exact_response request sigma
      sigma_nonneg sigma_le_one]
    simp
  simpa [approvedKernelProgram_eq_odd request] using
    (approvedOddProgram_meets request (approvedKernelPolynomial request)
      (approvedKernelPolynomial_odd request) request.epsilon
      request.epsilon_pos request.epsilon_lt_two 0 (le_refl 0)
      (by simp) happrox)

end

end M13bApprovedOddQSPBridge
