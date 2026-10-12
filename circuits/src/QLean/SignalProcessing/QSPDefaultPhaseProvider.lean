import QLean.SignalProcessing.QSPExistenceApprovedOddSchedule
import VerifiedMath.Quantum.QSPFiniteRequest

/-!
# Application-independent default QSP phase provider

This is the public synthesis boundary for a real polynomial on `[-1,1]`.
The caller supplies only degree, parity, and interval-boundedness data.  The
provider is selected from the general QSP existence theorem and mentions no
Q matrix, history system, kernel reflection, benchmark, or Q-Lean checkpoint.

The physical circuit reads a nonnegative singular value `x ∈ [0,1]`; the
negative half of the user polynomial is fixed by its approved even/odd law.
The separate physical alternating-word compiler is provided by
`QSPExistenceApprovedSchedule`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace VerifiedMath.Quantum.QSP

open SpectralSamplingProof.Analytic

/-- Human-approved QSP synthesis data.  `AdmissibleRealPolynomial` itself is
the request: it does not contain phases or a circuit-correctness premise. -/
abbrev SynthesisRequest := AdmissibleRealPolynomial

/-- The independent two-projector phase plan selected by the QSP theorem. -/
abbrev PhaseSequence := TwoProjectorQSPPhasePlan

/-- Forget the legacy role and direction names without changing the word. -/
def roleStepToGeneric : FixedPointRoleAwarePhaseStep → Step ℝ
  | .signal .forward => .signal .forward
  | .signal .adjoint => .signal .adjoint
  | .projectorPhase .source angle => .projectorPhase .source angle
  | .projectorPhase .target angle => .projectorPhase .target angle

def roleWordToGeneric (plan : PhaseSequence) : Word ℝ :=
  plan.steps.map roleStepToGeneric

/-- Realization uses the independently certified real phase plan. The
provider's public value is only the generic angle word, not a PJ circuit. -/
def Realizes (request : SynthesisRequest) (phases : Word ℝ) : Prop :=
  ∃ plan : PhaseSequence,
    TwoProjectorQSPRealizationCertificate
      (nativeQSPTarget024 (GeneralRealQSPPolynomial127.ofApproved request))
      plan ∧ phases = roleWordToGeneric plan

/-- The proof-only selection uses the framed physical schedule for positive
degree. The constant case retains the general existence construction. -/
noncomputable def selectedPhasePlan (request : SynthesisRequest) :
    PhaseSequence :=
  if positive : 0 < request.degree then
    approvedPhysicalPlan request positive
  else
    canonicalPlan035 (GeneralRealQSPPolynomial127.ofApproved request)

theorem selectedPhasePlan_certificate (request : SynthesisRequest) :
    TwoProjectorQSPRealizationCertificate
      (nativeQSPTarget024 (GeneralRealQSPPolynomial127.ofApproved request))
      (selectedPhasePlan request) := by
  by_cases positive : 0 < request.degree
  · simpa [selectedPhasePlan, positive] using
      approvedPhysicalPlan_certificate request positive
  · simpa [selectedPhasePlan, positive] using
      canonicalCertificate035 (GeneralRealQSPPolynomial127.ofApproved request)

theorem selectedPhasePlan_realizes (request : SynthesisRequest) :
    Realizes request (roleWordToGeneric (selectedPhasePlan request)) :=
  ⟨selectedPhasePlan request, selectedPhasePlan_certificate request, rfl⟩

theorem exists_selected_phases (request : SynthesisRequest) :
    ∃ phases : Word ℝ,
      phases = roleWordToGeneric (selectedPhasePlan request) ∧
        Realizes request phases := by
  exact ⟨roleWordToGeneric (selectedPhasePlan request), rfl,
    selectedPhasePlan_realizes request⟩

/-- Noncomputable only because the mathematical existence theorem chooses a
phase sequence.  Numerical callers instead pass a finite closed phase word to
the same circuit builders. -/
noncomputable def defaultPhaseProvider {Request : Type}
    [PolynomialInterpretation Request] : RequestPhaseProvider Request ℝ :=
  fun request => Classical.choose
    (exists_selected_phases (PolynomialInterpretation.approved request))

theorem defaultPhaseProvider_finite_eq (request : FinitePolynomialRequest) :
    defaultPhaseProvider request = defaultPhaseProvider request.approved := rfl

theorem defaultPhaseProvider_selected (request : SynthesisRequest) :
    defaultPhaseProvider request =
      roleWordToGeneric (selectedPhasePlan request) :=
  (Classical.choose_spec (exists_selected_phases request)).1

theorem defaultPhaseProvider_odd_steps (request : SynthesisRequest)
    (oddDegree : request.degree % 2 = 1) :
    defaultPhaseProvider request =
      (approvedOddPhysicalWord request oddDegree).map roleStepToGeneric := by
  have positive : 0 < request.degree := by omega
  rw [defaultPhaseProvider_selected]
  simp only [roleWordToGeneric, selectedPhasePlan, dif_pos positive,
    approvedPhysicalPlan]
  exact congrArg (List.map roleStepToGeneric)
    (approvedOddPhysicalWord_eq_general request oddDegree).symm

end VerifiedMath.Quantum.QSP
