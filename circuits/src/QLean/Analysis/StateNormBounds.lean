import QLean.SignalProcessing.M13cSpecification
import QLean.SignalProcessing.M13bQSVTLogicalEmbedding
import QLean.Circuits.Foundation.ClassicalArithmeticCorrectnessAnalytic
import Mathlib
import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.History.Jennings.PureSpec
import QLean.SignalProcessing.PhaseScheduleProofsPhaseWordContract
import QLean.SignalProcessing.PhaseScheduleProofsChebyshevContract
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.PhaseShiftMacros
import QLean.History.HistoryEmbeddingNorm
import QLean.History.Jennings.ProofEstablishedBridge
import QLean.Circuits.Foundation.FinitePhaseTransformAnalytic
import QLean.Circuits.Foundation.CircuitListLemmas
import QLean.Circuits.Foundation.Foundations
import QLean.Circuits.Foundation.QubitBasisEncoding
import QLean.Circuits.Foundation.QuantumFourierAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic
import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.WireEmbeddingAnalytic
import QLean.Circuits.Foundation.ReversibleLogicCleanAnalytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkMultiControlledXCorrectnessAnalytic
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2
import QLean.Circuits.Foundation.QuantumFourier
import QLean.Circuits.Foundation.OperatorL2Error
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import QLean.Circuits.Foundation.Metrics
import QLean.Circuits.Foundation.ReversibleLogic
import QLean.Circuits.Foundation.WireEmbedding
import QLean.Circuits.Foundation.WireEmbeddingL2Analytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkClean
import QLean.Circuits.Foundation.ControlledConstantAdderAnalytic
import VerifiedMath.FiniteDistribution
import VerifiedMath.FiniteComplex

/-! Norm bounds for isometric and contractive operators. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2400000

namespace ScientificErrorBudgetSpecification

open Matrix
open VerifiedCircuitCore
open SpectralSamplingProof.Analytic
open M13bPrimitiveCandidate

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- A rectangular basis embedding is L2-contractive.  This is derived from
its isometry equation, rather than supplied as an extra hypothesis at each
scientific endpoint. -/
theorem stateL2Norm_mulVec_le_of_isometry
    {inputBasis outputBasis : Type*}
    [Fintype inputBasis] [Fintype outputBasis]
    [DecidableEq inputBasis] [DecidableEq outputBasis]
    [Nonempty inputBasis]
    (embedding : Matrix outputBasis inputBasis ℂ)
    (isometry : Matrix.conjTranspose embedding * embedding = 1)
    (state : State inputBasis) :
    stateL2Norm (embedding.mulVec state) ≤ stateL2Norm state := by
  have normSquare : ‖embedding‖ * ‖embedding‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, isometry]
    simp
  have normLe : ‖embedding‖ ≤ 1 := by
    nlinarith [norm_nonneg embedding]
  have actionBound := embedding.l2_opNorm_mulVec (toEuclideanState state)
  rw [stateL2Norm_eq_euclideanNorm, stateL2Norm_eq_euclideanNorm]
  change ‖(EuclideanSpace.equiv outputBasis ℂ).symm
      (embedding.mulVec (toEuclideanState state).ofLp)‖ ≤ _
  have scaled := mul_le_mul_of_nonneg_right normLe
    (norm_nonneg (toEuclideanState state))
  exact actionBound.trans (by simpa using scaled)

theorem stateL2Norm_mulVec_le_of_opNorm_le
    {inputBasis outputBasis : Type*}
    [Fintype inputBasis] [Fintype outputBasis]
    [DecidableEq inputBasis] [DecidableEq outputBasis]
    (operator : Matrix outputBasis inputBasis ℂ)
    (normLe : ‖operator‖ ≤ 1) (state : State inputBasis) :
    stateL2Norm (operator.mulVec state) ≤ stateL2Norm state := by
  have actionBound := operator.l2_opNorm_mulVec (toEuclideanState state)
  rw [stateL2Norm_eq_euclideanNorm, stateL2Norm_eq_euclideanNorm]
  change ‖(EuclideanSpace.equiv outputBasis ℂ).symm
      (operator.mulVec (toEuclideanState state).ofLp)‖ ≤ _
  have scaled := mul_le_mul_of_nonneg_right normLe
    (norm_nonneg (toEuclideanState state))
  exact actionBound.trans (by simpa using scaled)

/-- A finite rectangular isometry preserves L2 norm exactly. -/
theorem stateL2Norm_mulVec_eq_of_isometry
    {inputBasis outputBasis : Type*}
    [Fintype inputBasis] [Fintype outputBasis]
    [DecidableEq inputBasis] [DecidableEq outputBasis]
    [Nonempty inputBasis]
    (embedding : Matrix outputBasis inputBasis ℂ)
    (isometry : Matrix.conjTranspose embedding * embedding = 1)
    (state : State inputBasis) :
    stateL2Norm (embedding.mulVec state) = stateL2Norm state := by
  apply le_antisymm
  · exact stateL2Norm_mulVec_le_of_isometry embedding isometry state
  · have normSquare : ‖embedding‖ * ‖embedding‖ = 1 := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self, isometry]
      simp
    have normLe : ‖embedding‖ ≤ 1 := by
      nlinarith [norm_nonneg embedding]
    have adjointNormLe : ‖Matrix.conjTranspose embedding‖ ≤ 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact normLe
    calc
      stateL2Norm state = stateL2Norm
          ((Matrix.conjTranspose embedding * embedding).mulVec state) := by
        rw [isometry, Matrix.one_mulVec]
      _ = stateL2Norm
          ((Matrix.conjTranspose embedding).mulVec (embedding.mulVec state)) := by
        rw [Matrix.mulVec_mulVec]
      _ ≤ stateL2Norm (embedding.mulVec state) :=
        stateL2Norm_mulVec_le_of_opNorm_le
          (Matrix.conjTranspose embedding) adjointNormLe _

end

end ScientificErrorBudgetSpecification
