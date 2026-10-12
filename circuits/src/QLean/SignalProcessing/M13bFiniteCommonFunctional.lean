import QLean.SignalProcessing.M13bFiniteCommonCompression
import QLean.SignalProcessing.M13bSpecification

/-! Complete real-logical functional calculus of the common outer circuit.
The zero eigenvalue is handled by the degenerate strict pair, and eigenvalue
one by norm saturation.  No legacy circuit equation is used below. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace M13bFiniteCommonFunctional

open VerifiedCircuitCore NativeConcreteP18QSPWitness NativeSignalQSVTActual
open M13bPrimitiveCandidate M13bGramBasisStrictPair M13bGramBoundaryWitness
open M13bGramFullCompressedAction M13bFiniteCommonCompression M13bFiniteCommonBoundary
open M13bFiniteOuterIntertwining M13bSpecification NativeSignalQSVTFunctionalBridge
open NativeQSPWitnessTwoFrameModel NativeQSPWitnessTransferModel SpectralSamplingProof.Analytic

noncomputable section

theorem commonProgram_gram_basis
    (input : ExecutableInput119)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation input.source input.domain input.fits input.assumptions] (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (wellFormed : FrameWord .source
      (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))) .target)
    (j : executableSignalCleanIndex119 input.source) :
    (commonLogicalBlock input.source input.domain input.fits input.assumptions program).mulVec
      (realColumn119 ((DalzellDilation.gramBasis130
        (executableGramOperator119 input.source input.assumptions) j).ofLp)) =
    ((wordResponseFilter119
      (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0)))
      (Real.sqrt (DalzellDilation.gramEigenvalue130
        (executableGramOperator119 input.source input.assumptions) j)) : ℝ) : ℂ) •
      realColumn119 ((DalzellDilation.gramBasis130
        (executableGramOperator119 input.source input.assumptions) j).ofLp) := by
  obtain strict | endpoint := commonGram_strict_or_endpoint input.source input.assumptions j
  · let pair := executableGramStrictPair119 input.source input.assumptions j strict
    have action := commonStrict_compressed_action input.source input.domain input.fits input.assumptions
      pair program wellFormed
    by_cases zero : DalzellDilation.gramEigenvalue130
        (executableGramOperator119 input.source input.assumptions) j = 0
    · convert action using 1 <;>
        norm_num [wordResponseFilter119, programTransfer, pair, executableGramStrictPair119,
          executableGramZeroStrictPair119, zero]
    · simpa [wordResponseFilter119, programTransfer, pair, executableGramStrictPair119,
        executableGramPositiveStrictPair119, zero] using action
  · have action := commonBoundary_compressed_action input.source input.domain input.fits input.assumptions
      j endpoint program wellFormed
    simpa [wordResponseFilter119, programTransfer, endpoint, boundaryGramVector119] using action

/-- All real logical vectors are covered, not only a nonzero spectral
subspace or selected benchmark states. -/
theorem commonProgram_real_functional_intertwines
    (input : ExecutableInput119)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation input.source input.domain input.fits input.assumptions] (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (wellFormed : FrameWord .source
      (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))) .target)
    (v : EuclideanSpace ℝ (executableSignalCleanIndex119 input.source)) :
    (commonLogicalBlock input.source input.domain input.fits input.assumptions program).mulVec
      (complexifyVector v) =
    complexifyVector (DalzellDilation.gramFilterAction130
      (executableGramOperator119 input.source input.assumptions)
      (wordResponseFilter119
        (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0)))) v) :=
  real_functional_intertwines_of_basis input _ _ (commonProgram_gram_basis input program wellFormed) v

private theorem complexify_sub {ι : Type*} (v w : EuclideanSpace ℝ ι) :
    complexifyVector (v - w) = complexifyVector v - complexifyVector w := by
  ext i
  simp [complexifyVector, VerifiedMath.Complexification.euclideanVector]

private theorem stateL2Norm_complexify {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    stateL2Norm (complexifyVector v) = ‖v‖ := by
  simp [stateL2Norm, complexifyVector, VerifiedMath.Complexification.euclideanVector,
    EuclideanSpace.norm_eq, Complex.normSq_ofReal, pow_two]

theorem commonProgram_state_error_of_response
    (input : ExecutableInput119)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation input.source input.domain input.fits input.assumptions]
    (epsilon : ℝ) (epsilon_pos : 0 < epsilon) (epsilon_lt_two : epsilon < 2)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (wellFormed : FrameWord .source
      (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))) .target)
    (phaseError : ℝ) (phaseError_nonneg : 0 ≤ phaseError)
    (responseBound : ∀ j : executableSignalCleanIndex119 input.source,
      |wordResponseFilter119
          (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0)))
          (Real.sqrt (DalzellDilation.gramEigenvalue130
            (executableGramOperator119 input.source input.assumptions) j)) -
        idealKernelFilter119 input epsilon epsilon_pos epsilon_lt_two
          (Real.sqrt (DalzellDilation.gramEigenvalue130
            (executableGramOperator119 input.source input.assumptions) j))| ≤ phaseError)
    (v : EuclideanSpace ℝ (executableSignalCleanIndex119 input.source)) :
    stateL2Norm
      ((commonLogicalBlock input.source input.domain input.fits input.assumptions program).mulVec
        (complexifyVector v) - complexifyVector
          (WithLp.toLp 2 ((GramOperator.idealKernelReflection
            (certifiedInput119 input).base.system (certifiedInput119 input).base.alpha
            (certifiedInput119 input).base.nu (certifiedInput119 input).base.hdet).mulVec v.ofLp))) ≤
      (phaseError + epsilon) * ‖v‖ := by
  let G := executableGramOperator119 input.source input.assumptions
  let steps := program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))
  let filteredWord := DalzellDilation.gramFilterAction130 G (wordResponseFilter119 steps) v
  let filteredIdeal := DalzellDilation.gramFilterAction130 G
    (idealKernelFilter119 input epsilon epsilon_pos epsilon_lt_two) v
  let ideal := WithLp.toLp 2 ((GramOperator.idealKernelReflection
    (certifiedInput119 input).base.system (certifiedInput119 input).base.alpha
    (certifiedInput119 input).base.nu (certifiedInput119 input).base.hdet).mulVec v.ofLp)
  rw [commonProgram_real_functional_intertwines input program wellFormed,
    ← complexify_sub, stateL2Norm_complexify]
  have phaseBound : ‖filteredWord - filteredIdeal‖ ≤ phaseError * ‖v‖ :=
    DalzellDilation.gram_filter_difference_bound130 G (wordResponseFilter119 steps)
      (idealKernelFilter119 input epsilon epsilon_pos epsilon_lt_two)
      phaseError phaseError_nonneg responseBound v
  have idealBound : ‖filteredIdeal - ideal‖ ≤ epsilon * ‖v‖ :=
    idealKernelFilter119_error_bound input epsilon epsilon_pos epsilon_lt_two v
  calc
    ‖filteredWord - ideal‖ = ‖(filteredWord - filteredIdeal) + (filteredIdeal - ideal)‖ := by
      congr 1
      abel
    _ ≤ ‖filteredWord - filteredIdeal‖ + ‖filteredIdeal - ideal‖ := norm_add_le _ _
    _ ≤ phaseError * ‖v‖ + epsilon * ‖v‖ := add_le_add phaseBound idealBound
    _ = (phaseError + epsilon) * ‖v‖ := by ring

/-- Theory-side response evidence is applied to the actual common compiler.
The public default provider supplies this evidence; numerical generation has
no new certification requirement. -/
theorem commonProgram_real_logical_operator_approx
    (request : KernelSynthesisRequest119)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation request.input.source request.input.domain request.input.fits request.input.assumptions]
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (meets : PhaseProgramMeets119 request program) :
    RealLogicalL2OperatorApprox119
      (fun v => (commonLogicalBlock request.input.source request.input.domain request.input.fits
        request.input.assumptions program).mulVec (complexifyVector v))
      (fun v => complexifyVector (WithLp.toLp 2
        ((GramOperator.idealKernelReflection
          (certifiedInput119 request.input).base.system (certifiedInput119 request.input).base.alpha
          (certifiedInput119 request.input).base.nu (certifiedInput119 request.input).base.hdet).mulVec v.ofLp)))
      request.epsilon := by
  obtain ⟨_closed, frame, polynomialError, polynomialError_pos, polynomialError_lt_two,
    responseError, responseError_nonneg, budget, satisfies⟩ := meets
  intro v
  have action := commonProgram_state_error_of_response request.input polynomialError
    polynomialError_pos polynomialError_lt_two program frame responseError responseError_nonneg
    (fun j => by
      have upper := executable_gram_basis_sqrt_le_one119 request.input.source request.input.assumptions j
      have bound := satisfies.2 _ (Real.sqrt_nonneg _) upper
      simpa only [kernelQSPResponseRequest119, VerifiedMath.Quantum.QSP.Satisfies,
        ← wordResponseFilter_eq_pureQSP119, continuousKernelResponse_eq_ideal_on_gram_basis119]
        using bound) v
  exact action.trans (mul_le_mul_of_nonneg_right (by simpa [add_comm] using budget) (norm_nonneg _))

end
end M13bFiniteCommonFunctional
