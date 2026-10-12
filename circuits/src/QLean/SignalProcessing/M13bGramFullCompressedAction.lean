import QLean.SignalProcessing.M13bGramBoundaryTransferUnitary
import QLean.SignalProcessing.M13bHermitianOuterScalar
import QLean.SignalProcessing.M13bConjugateControlledCompute
import QLean.SignalProcessing.M13bControlXStateSemantics
import QLean.SignalProcessing.M13bHadamardTrueStateSemantics
import QLean.SignalProcessing.M13bTwoFrameHermitianDilation
import QLean.SignalProcessing.M13bHermitianSuccessReflection
import QLean.SignalProcessing.M13bQSVTLogicalEmbedding
import QLean.SignalProcessing.M13bPrimitiveCandidate
import QLean.SignalProcessing.M13bUnitaritySemanticVerification
import QLean.SignalProcessing.M13bGramBoundaryWitness
import QLean.SignalProcessing.NativeSignalQSVTFunctionalBridge
import QLean.SignalProcessing.M13bChebyshevCoordinateBridge
import VerifiedMath.Quantum.QSP

set_option autoImplicit false

namespace M13bGramFullCompressedAction

open scoped BigOperators

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness
open SpectralSamplingProof.Analytic
open NativeQSPWitnessTransferModel
open NativeQSPWitnessTwoFrameModel
open M13bGramBasisStrictPair

open M13bGramBoundaryWitness

open M13bPrimitiveCandidate

noncomputable section

/-- Erase only the application-specific names, retaining direction, role,
angle and the source-order convention of the independent two-dimensional
word. -/
def toPureQSPStep119 : FixedPointRoleAwarePhaseStep → VerifiedMath.Quantum.QSP.Step ℝ
  | .signal .forward => .signal .forward
  | .signal .adjoint => .signal .adjoint
  | .projectorPhase .source angle => .projectorPhase .source angle
  | .projectorPhase .target angle => .projectorPhase .target angle

def toPureQSPFrame119 : ActiveFrame → VerifiedMath.Quantum.QSP.Frame
  | .source => .source
  | .target => .target

theorem frameAfter_eq_pureQSP119
    (frame : ActiveFrame) (step : FixedPointRoleAwarePhaseStep) :
    VerifiedMath.Quantum.QSP.frameAfter (toPureQSPFrame119 frame)
        (toPureQSPStep119 step) =
      Option.map toPureQSPFrame119 (frameAfter frame step) := by
  cases frame <;> cases step with
  | signal direction => cases direction <;> rfl
  | projectorPhase role angle => cases role <;> rfl

theorem frameWord_to_pureQSP119
    {first last : ActiveFrame} {steps : List FixedPointRoleAwarePhaseStep}
    (valid : FrameWord first steps last) :
    VerifiedMath.Quantum.QSP.ValidWord
      (toPureQSPFrame119 first) (steps.map toPureQSPStep119)
      (toPureQSPFrame119 last) := by
  induction valid with
  | nil frame => exact .nil _
  | @cons current next final step rest transition remaining inductionHypothesis =>
      apply VerifiedMath.Quantum.QSP.ValidWord.cons
      · rw [frameAfter_eq_pureQSP119]
        simpa using congrArg (Option.map toPureQSPFrame119) transition
      · exact inductionHypothesis

theorem stepTransfer_eq_pureQSP119
    (probability : ℝ) (step : FixedPointRoleAwarePhaseStep) :
    fixedPointRoleAwareStepTransferMatrix probability step =
      VerifiedMath.Quantum.QSP.stepTransfer probability (toPureQSPStep119 step) := by
  cases step with
  | signal direction =>
      cases direction <;> ext row column <;>
        fin_cases row <;> fin_cases column <;> rfl
  | projectorPhase role angle => cases role <;> rfl

theorem abstractTransferWord_eq_pureQSP119
    (probability : ℝ) (steps : List FixedPointRoleAwarePhaseStep) :
    abstractTransferWord probability steps =
      VerifiedMath.Quantum.QSP.wordTransfer probability (steps.map toPureQSPStep119) := by
  induction steps with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      simp only [abstractTransferWord, List.map_cons,
        VerifiedCircuitCore.operatorSequence, VerifiedMath.Quantum.QSP.wordTransfer]
      rw [← show abstractTransferWord probability rest =
        VerifiedCircuitCore.operatorSequence
          (rest.map (fixedPointRoleAwareStepTransferMatrix probability)) from rfl]
      rw [inductionHypothesis, stepTransfer_eq_pureQSP119]

theorem executable_gram_basis_sqrt_ge_input_gap
    (input : ExecutableInput119)
    (j : executableSignalCleanIndex119 input.source)
    (hj : DalzellDilation.gramEigenvalue130
      (executableGramOperator119 input.source input.assumptions) j ≠ 0) :
    DalzellDilation.deltaKR130 (certifiedInput119 input) ≤
      Real.sqrt (DalzellDilation.gramEigenvalue130
        (executableGramOperator119 input.source input.assumptions) j) := by
  apply DalzellDilation.gram_basis_sqrt_ge_delta130 _ j
    (DalzellDilation.deltaKR130 (certifiedInput119 input))
  · intro w hw
    apply DalzellDilation.rightSingularLowerGap130 (certifiedInput119 input) w
    simpa [DalzellDilation.KernelOrthogonal130, DalzellDilation.kernelOrthogonalFn130,
      executableGramOperator119, certifiedInput119,
      ExecutableHistoryExecutableP18.executableP18Input119,
      ExecutableHistoryExecutableP18.executableM13Base119, dotProduct, mul_comm] using hw
  · exact hj

/-- The real Hermitianized scalar of an arbitrary phase word.  This is
computed from the two-dimensional word transfer, not from the circuit or the
independent kernel-reflection target. -/
def wordResponseFilter119 (steps : List FixedPointRoleAwarePhaseStep)
    (sigma : ℝ) : ℝ :=
  2 * ((abstractTransferWord (sigma ^ 2) steps)
    fixedPointSourceIndex fixedPointSourceIndex).re ^ 2 - 1

/-- A continuous, circuit-independent Chebyshev response.  The scientific
reflection filter agrees with it on the actual zero-or-gap Gram spectrum;
the latter is deliberately clipped away from that spectrum. -/
def continuousKernelResponse119
    (input : ExecutableInput119) (epsilon : ℝ)
    (epsilon_pos : 0 < epsilon) (epsilon_lt_two : epsilon < 2)
    (sigma : ℝ) : ℝ :=
  2 * (fixedPointChebyshevFailureResponse
    (KernelQSP.fixedPointParametersGeneral126
      (kernelQSPParameters119 input epsilon epsilon_pos epsilon_lt_two))
    (sigma ^ 2)) ^ 2 - 1

theorem continuousKernelResponse_eq_ideal_on_gram_basis119
    (input : ExecutableInput119) (epsilon : ℝ)
    (epsilon_pos : 0 < epsilon) (epsilon_lt_two : epsilon < 2)
    (j : executableSignalCleanIndex119 input.source) :
    continuousKernelResponse119 input epsilon epsilon_pos epsilon_lt_two
      (Real.sqrt (DalzellDilation.gramEigenvalue130
        (executableGramOperator119 input.source input.assumptions) j)) =
    idealKernelFilter119 input epsilon epsilon_pos epsilon_lt_two
      (Real.sqrt (DalzellDilation.gramEigenvalue130
        (executableGramOperator119 input.source input.assumptions) j)) := by
  let params := kernelQSPParameters119 input epsilon epsilon_pos epsilon_lt_two
  let ev := DalzellDilation.gramEigenvalue130
    (executableGramOperator119 input.source input.assumptions) j
  let sigma := Real.sqrt ev
  by_cases hzero : ev = 0
  · have hsigma : sigma = 0 := by simp [sigma, hzero]
    change continuousKernelResponse119 input epsilon epsilon_pos epsilon_lt_two sigma =
      idealKernelFilter119 input epsilon epsilon_pos epsilon_lt_two sigma
    rw [hsigma]
    simp [continuousKernelResponse119, idealKernelFilter119,
      M13bHermitianReflectionScalar.rhoFromInput,
      M13bHermitianReflectionScalar.rho,
      kernelQSPParameters119, DalzellDilation.fixedPointFailureResponse_zero130]
    norm_num
  · have hgap : params.gap ≤ sigma := by
      exact executable_gram_basis_sqrt_ge_input_gap input j hzero
    have htransition :
        (KernelQSP.fixedPointParametersGeneral126 params).transitionWidth ≤
          sigma ^ 2 := by
      have hsigma_nonneg : 0 ≤ sigma := Real.sqrt_nonneg _
      exact le_trans (M13bHermitianOuterScalar.transitionWidth_le_sq_gap119 params)
        ((sq_le_sq₀ (le_of_lt params.gap_pos) hsigma_nonneg).2 hgap)
    have hsigma_pos : 0 < sigma := lt_of_lt_of_le params.gap_pos hgap
    change continuousKernelResponse119 input epsilon epsilon_pos epsilon_lt_two sigma =
      idealKernelFilter119 input epsilon epsilon_pos epsilon_lt_two sigma
    change 2 * (fixedPointChebyshevFailureResponse
      (KernelQSP.fixedPointParametersGeneral126 params) (sigma ^ 2)) ^ 2 - 1 =
      (if sigma = 0 then 1 else
        2 * (fixedPointChebyshevFailureResponse
          (KernelQSP.fixedPointParametersGeneral126 params)
          (max (KernelQSP.fixedPointParametersGeneral126 params).transitionWidth
            (sigma ^ 2))) ^ 2 - 1)
    rw [if_neg (ne_of_gt hsigma_pos), max_eq_right htransition]

theorem wordResponseFilter_eq_pureQSP119
    (steps : List FixedPointRoleAwarePhaseStep) (sigma : ℝ) :
    wordResponseFilter119 steps sigma =
      VerifiedMath.Quantum.QSP.hermitianResponse (steps.map toPureQSPStep119) sigma := by
  simp [wordResponseFilter119, VerifiedMath.Quantum.QSP.hermitianResponse,
    abstractTransferWord_eq_pureQSP119, fixedPointSourceIndex]

private theorem complexify_sum_gram_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (a : ι → ℝ) :
    NativeSignalQSVTFunctionalBridge.complexifyVector
      (∑ j, a j • DalzellDilation.gramBasis130 G j) =
      ∑ j, (a j : ℂ) • realColumn119 ((DalzellDilation.gramBasis130 G j).ofLp) := by
  ext i
  simp [NativeSignalQSVTFunctionalBridge.complexifyVector,
    VerifiedMath.Complexification.euclideanVector, realColumn119]

private theorem complexify_gram_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (j : ι) :
    NativeSignalQSVTFunctionalBridge.complexifyVector (DalzellDilation.gramBasis130 G j) =
      realColumn119 ((DalzellDilation.gramBasis130 G j).ofLp) := rfl

private theorem complexify_real_smul
    {ι : Type*} (a : ℝ) (v : EuclideanSpace ℝ ι) :
    NativeSignalQSVTFunctionalBridge.complexifyVector (a • v) =
      (a : ℂ) • NativeSignalQSVTFunctionalBridge.complexifyVector v := by
  ext i
  simp [NativeSignalQSVTFunctionalBridge.complexifyVector,
    VerifiedMath.Complexification.euclideanVector]

private theorem real_mul_smul_eq_complex_smul_smul
    {ι : Type*} (a b : ℝ) (w : ι → ℂ) :
    (a * b) • w = (a : ℂ) • (b : ℂ) • w := by
  ext i
  simp only [Pi.smul_apply]
  change (((a * b : ℝ) : ℂ) * w i) = (a : ℂ) * ((b : ℂ) * w i)
  rw [Complex.ofReal_mul, mul_assoc]

/-- The physical compressed primitive reflection agrees with the Gram
functional calculus on every real logical vector.  The proof extends the
sealed strict/boundary basis theorem through the complete Gram basis. -/
theorem real_functional_intertwines_of_basis
    (input : ExecutableInput119)
    (physical : Matrix (executableSignalCleanIndex119 input.source)
      (executableSignalCleanIndex119 input.source) ℂ)
    (f : ℝ → ℝ)
    (hbasis : ∀ j : executableSignalCleanIndex119 input.source,
      physical.mulVec
        (realColumn119 ((DalzellDilation.gramBasis130
          (executableGramOperator119 input.source input.assumptions) j).ofLp)) =
      ((f (Real.sqrt (DalzellDilation.gramEigenvalue130
        (executableGramOperator119 input.source input.assumptions) j)) : ℝ) : ℂ) •
        realColumn119 ((DalzellDilation.gramBasis130
          (executableGramOperator119 input.source input.assumptions) j).ofLp))
    (v : EuclideanSpace ℝ (executableSignalCleanIndex119 input.source)) :
    let G := executableGramOperator119 input.source input.assumptions
    physical.mulVec (NativeSignalQSVTFunctionalBridge.complexifyVector v) =
      NativeSignalQSVTFunctionalBridge.complexifyVector
        (DalzellDilation.gramFilterAction130 G f v) := by
  dsimp
  let G := executableGramOperator119 input.source input.assumptions
  let b := DalzellDilation.gramBasis130 G
  have hv : v = ∑ j, (b.repr v) j • b j := by
    symm
    exact b.sum_repr v
  have hbasis' (j : executableSignalCleanIndex119 input.source) :
      physical.mulVec (realColumn119 ((b j).ofLp)) =
      ((f (Real.sqrt (DalzellDilation.gramEigenvalue130 G j)) : ℝ) : ℂ) •
        realColumn119 ((b j).ofLp) := by
    simpa [G, b] using hbasis j
  dsimp [b] at hv
  dsimp [b] at hbasis'
  calc
    physical.mulVec (NativeSignalQSVTFunctionalBridge.complexifyVector v) =
        physical.mulVec (NativeSignalQSVTFunctionalBridge.complexifyVector
          (∑ j, ((DalzellDilation.gramBasis130 G).repr v) j •
            DalzellDilation.gramBasis130 G j)) := by
      conv_lhs => rw [hv]
    _ = physical.mulVec (∑ j,
          (((DalzellDilation.gramBasis130 G).repr v) j : ℂ) •
            realColumn119 ((DalzellDilation.gramBasis130 G j).ofLp)) := by
      rw [complexify_sum_gram_basis G]
    _ = ∑ j, physical.mulVec
          ((((DalzellDilation.gramBasis130 G).repr v) j : ℂ) •
            realColumn119 ((DalzellDilation.gramBasis130 G j).ofLp)) := by
      rw [Matrix.mulVec_sum]
    _ = ∑ j, (((DalzellDilation.gramBasis130 G).repr v) j : ℂ) •
          physical.mulVec (realColumn119 ((DalzellDilation.gramBasis130 G j).ofLp)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mulVec_smul]
    _ = ∑ j, (((DalzellDilation.gramBasis130 G).repr v) j : ℂ) •
          ((f (Real.sqrt (DalzellDilation.gramEigenvalue130 G j)) : ℝ) : ℂ) •
            realColumn119 ((DalzellDilation.gramBasis130 G j).ofLp) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hbasis']
      change (((DalzellDilation.gramBasis130 G).repr v) j : ℂ) •
          ((f (Real.sqrt (DalzellDilation.gramEigenvalue130 G j)) : ℝ) : ℂ) •
            realColumn119 ((DalzellDilation.gramBasis130 G j).ofLp) =
        (((DalzellDilation.gramBasis130 G).repr v) j : ℂ) •
          ((f (Real.sqrt (DalzellDilation.gramEigenvalue130 G j)) : ℝ) : ℂ) •
            realColumn119 ((DalzellDilation.gramBasis130 G j).ofLp)
      rfl
    _ = ∑ j, NativeSignalQSVTFunctionalBridge.complexifyVector
          ((((DalzellDilation.gramBasis130 G).repr v) j •
            f (Real.sqrt (DalzellDilation.gramEigenvalue130 G j))) •
            DalzellDilation.gramBasis130 G j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [complexify_real_smul, complexify_gram_basis G j]
      exact (real_mul_smul_eq_complex_smul_smul
        (((DalzellDilation.gramBasis130 G).repr v) j)
        (f (Real.sqrt (DalzellDilation.gramEigenvalue130 G j)))
        (realColumn119 ((DalzellDilation.gramBasis130 G j).ofLp))).symm
    _ = NativeSignalQSVTFunctionalBridge.complexifyVector
          (∑ j, (((DalzellDilation.gramBasis130 G).repr v) j •
            f (Real.sqrt (DalzellDilation.gramEigenvalue130 G j))) •
            DalzellDilation.gramBasis130 G j) := by
      calc
        ∑ j, NativeSignalQSVTFunctionalBridge.complexifyVector
            ((((DalzellDilation.gramBasis130 G).repr v) j •
              f (Real.sqrt (DalzellDilation.gramEigenvalue130 G j))) •
              DalzellDilation.gramBasis130 G j) =
            ∑ j, ((((DalzellDilation.gramBasis130 G).repr v) j •
              f (Real.sqrt (DalzellDilation.gramEigenvalue130 G j)) : ℝ) : ℂ) •
              realColumn119 ((DalzellDilation.gramBasis130 G j).ofLp) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [complexify_real_smul, complexify_gram_basis]
        _ = NativeSignalQSVTFunctionalBridge.complexifyVector
            (∑ j, (((DalzellDilation.gramBasis130 G).repr v) j •
              f (Real.sqrt (DalzellDilation.gramEigenvalue130 G j))) •
              DalzellDilation.gramBasis130 G j) := by
          symm
          apply complexify_sum_gram_basis G
    _ = NativeSignalQSVTFunctionalBridge.complexifyVector
          (DalzellDilation.gramFilterAction130 G
            f v) := by
      rw [← DalzellDilation.gramFilterLinear_apply130]
      congr 1
      conv_rhs => rw [hv]
      rw [map_sum]
      simp_rw [map_smul]
      apply Finset.sum_congr rfl
      intro j _
      rw [DalzellDilation.gramFilterLinear_apply130,
        DalzellDilation.gramFilterAction_basis130]
      simp [smul_smul]

end

end M13bGramFullCompressedAction
