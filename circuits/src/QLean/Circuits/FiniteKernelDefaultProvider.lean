import QLean.Circuits.FiniteKernelCircuit
import QLean.Circuits.FiniteScientificSpectralBound
import QLean.Circuits.CP03ProgramConversion
import QLean.SignalProcessing.JenningsM13AnalyticBounds
import QLean.History.JenningsExecutableHistoryDomain

/-!
Interpretation of a finite request belongs to the existence-based provider,
not to the circuit constructor. The general polynomial QSP provider is
unchanged. A finite external provider does not depend on this module.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.FiniteKernelCircuit

open VerifiedCircuitCore
open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open QLean.Circuits.CheckpointCircuits

noncomputable section

/-- Derive the analytic data from the finite science source. Nonzero initial
data is a scientific domain condition, not a circuit-correctness premise. -/
@[implicit_reducible] def Input.executableInput (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) : ExecutableInput :=
  let source := input.source.layoutSource
  let domain := executableHistoryDomain119 source
  let witness := Classical.choose (Function.ne_iff.mp nonzero)
  let witness_nonzero := Classical.choose_spec (Function.ne_iff.mp nonzero)
  let oldAssumptions := JenningsM13AnalyticBounds.executableM13Assumptions119_of_initialNonzero
    source domain input.fits witness witness_nonzero
  let assumptions : ExecutableM13Assumptions119 source :=
    { oldAssumptions with
      kappaH := FiniteKernelPolynomial.inverseBound source.historyParameters.taylorOrder
        source.historyParameters.clockEnd source.historyParameters.binaryLabels
      kappaH_pos := by
        exact_mod_cast FiniteKernelPolynomial.inverseBound_pos
          source.historyParameters.taylorOrder source.historyParameters.clockEnd
          source.historyParameters.binaryLabels
      historyInverseNorm_le_kappaH :=
        FiniteScientificSpectralBound.inverse_norm_le_finite source domain input.fits }
  { source := source
    domain := domain
    fits := input.fits
    assumptions := assumptions
    circuitSource :=
      { targetQubits := (ExecutableRaw119 source).history.qubits + 3
        layout := ExecutableHistoryCore.branchControlLayout119
          (ExecutableRaw119 source).history.qubits } }

def Input.synthesisRequest (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    M13bSpecification.KernelSynthesisRequest119 :=
  { input := input.executableInput nonzero
    epsilon := input.epsilon
    epsilon_pos := by exact_mod_cast input.epsilon_pos
    epsilon_lt_two := by exact_mod_cast input.epsilon_lt_two }

theorem Input.plannedDegree_eq (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    input.polynomialRequest.degree = KernelQSP.L_KRGeneral126
      (M13bPrimitiveCandidate.kernelQSPParameters119 (input.executableInput nonzero)
        input.epsilon (by exact_mod_cast input.epsilon_pos)
        (by exact_mod_cast input.epsilon_lt_two)) := by
  let bound := FiniteKernelPolynomial.inverseBound input.source.historyParameters.taylorOrder
    input.source.historyParameters.clockEnd input.source.historyParameters.binaryLabels
  have bound_pos : 0 < bound := FiniteKernelPolynomial.inverseBound_pos _ _ _
  have bound_real : (bound : ℝ) ≠ 0 := by exact_mod_cast bound_pos.ne'
  have eps_real : (input.epsilon : ℝ) ≠ 0 := by exact_mod_cast input.epsilon_pos.ne'
  change KernelQSP.leastOddAtLeast126 (FiniteKernelPolynomial.queryLowerBound
    input.source.historyParameters.taylorOrder input.source.historyParameters.clockEnd
    input.source.historyParameters.binaryLabels input.epsilon) =
    KernelQSP.leastOddAtLeast126 (Nat.find (exists_nat_gt
      (1 / ((bound : ℝ)⁻¹ * ((input.epsilon : ℝ) / 2)))))
  congr 1
  have value : (1 / ((bound : ℝ)⁻¹ * ((input.epsilon : ℝ) / 2))) =
      (((bound : ℚ) * 2 / input.epsilon : ℚ) : ℝ) := by
    push_cast
    field_simp
  simp_rw [value]
  rw [FiniteKernelPolynomial.firstNatAbove_rat _
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num)) input.epsilon_pos.le)]
  rfl

theorem Input.polynomialRequest_approved (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    input.polynomialRequest.approved =
      M13bApprovedOddQSPBridge.approvedKernelPolynomial (input.synthesisRequest nonzero) := by
  rw [Input.polynomialRequest, FiniteKernelPolynomial.request_approved]
  have extTarget : ∀ (left right : PhaseScheduleProofs.ChebyshevTarget125),
      left.delta = right.delta → left.L = right.L → left = right := by
    intro left right delta degree
    cases left
    cases right
    cases delta
    cases degree
    rfl
  unfold M13bApprovedOddQSPBridge.approvedKernelPolynomial
  congr 1
  exact extTarget _ _ rfl (Input.plannedDegree_eq input nonzero)

theorem defaultPhaseProvider_eq (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    VerifiedMath.Quantum.QSP.defaultPhaseProvider input.polynomialRequest =
      VerifiedMath.Quantum.QSP.defaultPhaseProvider
        (M13bApprovedOddQSPBridge.approvedKernelPolynomial
          (input.synthesisRequest nonzero)) := by
  rw [VerifiedMath.Quantum.QSP.defaultPhaseProvider_finite_eq,
    Input.polynomialRequest_approved input nonzero]

/-- This is the phase contract supplied internally by the existence theorem.
It is not an assertion about an external numerical provider. The primitive
builder's correspondence is a separate, subsequent theorem. -/
theorem defaultPhaseProvider_meets (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    M13bSpecification.PhaseProgramMeets119 (input.synthesisRequest nonzero)
      (cp03ProgramWord (VerifiedMath.Quantum.QSP.defaultPhaseProvider input.polynomialRequest)) := by
  rw [defaultPhaseProvider_eq input nonzero]
  change M13bSpecification.PhaseProgramMeets119 (input.synthesisRequest nonzero)
    (cp03ProgramFromProvider (input.synthesisRequest nonzero)
      VerifiedMath.Quantum.QSP.defaultPhaseProvider)
  rw [cp03ProgramFromProvider_default_eq]
  exact M13bApprovedOddQSPBridge.approvedKernelProgram_meets _

end
end QLean.Circuits.FiniteKernelCircuit
