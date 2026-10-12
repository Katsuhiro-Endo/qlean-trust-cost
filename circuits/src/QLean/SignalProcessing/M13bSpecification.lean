import QLean.SignalProcessing.M13bGramFullCompressedAction
import QLean.SignalProcessing.M13bConjugateControlledCompute
import QLean.SignalProcessing.M13bControlXStateSemantics
import QLean.SignalProcessing.M13bHadamardTrueStateSemantics
import QLean.SignalProcessing.M13bHermitianSuccessReflection
import QLean.SignalProcessing.M13bQSVTLogicalEmbedding

/-!
# Public M13b specification

The phase word is retained as a proof-carrying object.  The approximation
contract is deliberately over the real logical subspace: the compressed
primitive has complex codomain, while the certified ideal filter is stated on
real Gram vectors.  Thus a complex-full-space operator norm is not claimed.
-/

open scoped BigOperators
open VerifiedCircuitCore
open SpectralSamplingProof.Analytic
open NativeConcreteP18QSPWitness
open NativeSignalQSVTFunctionalBridge
open NativeQSPWitnessTwoFrameModel
open NativeQSPWitnessTransferModel
open M13bGramBasisStrictPair
open M13bGramFullCompressedAction
open M13bPrimitiveCandidate
open NativeFixedPointPrimitive

namespace M13bSpecification

noncomputable section

/-- The real-logical-subspace operator-norm contract.  This is the typed
replacement for an unproved complex-full-space norm claim. -/
def RealLogicalL2OperatorApprox119
    {ι : Type*} [Fintype ι]
    (actual target : EuclideanSpace ℝ ι → State ι) (epsilon : ℝ) : Prop :=
  ∀ v, stateL2Norm (actual v - target v) ≤ epsilon * ‖v‖

/-- An arbitrary well-framed phase word is certified by its independently
evaluated two-dimensional response on the relevant Gram spectrum.  In
particular, this contract does not identify the word with the built-in
Chebyshev schedule or with a chosen implementation value. -/
def kernelQSPResponseRequest119
    (input : ExecutableInput119) (epsilon : ℝ)
    (epsilon_pos : 0 < epsilon) (epsilon_lt_two : epsilon < 2)
    (phaseError : ℝ) (phaseError_nonneg : 0 ≤ phaseError) :
    VerifiedMath.Quantum.QSP.Request where
  target := continuousKernelResponse119 input epsilon epsilon_pos epsilon_lt_two
  error := phaseError
  error_nonneg := phaseError_nonneg

/-- The circuit-facing request retains the scientific input and error budget;
it does not contain the desired phase word or a circuit-correctness premise. -/
structure KernelSynthesisRequest119 where
  input : ExecutableInput119
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_two : epsilon < 2

def PhaseProgramMeets119 (request : KernelSynthesisRequest119)
    (program : List PhaseProgramStep) : Prop :=
  PhaseProgram.IsSymbolFree program ∧
    FrameWord .source
      (program.map (PhaseProgramStep.eval (fun _ => 0))) .target ∧
    ∃ polynomialError : ℝ,
      ∃ polynomialError_pos : 0 < polynomialError,
      ∃ polynomialError_lt_two : polynomialError < 2,
      ∃ responseError : ℝ,
      ∃ responseError_nonneg : 0 ≤ responseError,
        polynomialError + responseError ≤ request.epsilon ∧
          VerifiedMath.Quantum.QSP.Satisfies
            (kernelQSPResponseRequest119 request.input polynomialError
              polynomialError_pos polynomialError_lt_two responseError
              responseError_nonneg)
            ((program.map (PhaseProgramStep.eval (fun _ => 0))).map toPureQSPStep119)

end

end M13bSpecification
