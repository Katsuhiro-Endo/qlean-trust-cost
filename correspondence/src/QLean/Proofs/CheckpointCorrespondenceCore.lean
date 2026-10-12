import QLean.Correspondence.CheckpointReadout
import VerifiedMath.Basis
import VerifiedMath.FiniteComplex
import VerifiedMath.FiniteDistribution
import QLean.MathematicalSpecifications.PublicCheckpointData
import VerifiedMath.OperatorRelations
import QLean.Circuits.CheckpointCircuits
import QLean.Correspondence.BenchmarkHistoryCorrespondence
import QLean.Correspondence.KernelReflectionTransport
import QLean.SignalProcessing.M13bSpecification
import QLean.Correspondence.RepresentationTransport
import QLean.MathematicalSpecifications.CoalescingWalkModel
import Mathlib.Tactic
import QLean.Generator.Analysis.QGenerator
import QLean.SignalProcessing.M13bPrimitiveCandidate
import QLean.SignalProcessing.JenningsM13AnalyticBounds
import QLean.History.JenningsExecutableHistoryDomain
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
import QLean.Analysis.StateNormBounds
import QLean.SignalProcessing.NativeSingularPairTwoFrame
import QLean.Generator.Implementation.QDecoderCorrectness
import QLean.MathematicalSpecifications.KernelReflection
import QLean.MathematicalSpecifications.HistoryLinearSystem

/-! Internal bindings and representation-transport lemmas used by the public
CP01–CP04 correspondence theorems. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option warningAsError true

namespace QLean.Proofs.CheckpointCorrespondence.Internal

open Matrix
open scoped Matrix.Norms.L2Operator
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open NativeSingularPairTwoFrame
open SpectralSamplingProof.Analytic
open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open NativeConcreteP18QSPWitness

open ScientificExtractionPhysicalSpecification

open QLean.MathematicalSpecifications
open QLean.MathematicalSpecifications.PublicCheckpoints
open QLean.Circuits.CheckpointCircuits
open QLean.Correspondence.CheckpointReadout
open QLean.Correspondence.BenchmarkHistoryCorrespondence

open QLean.Correspondence.RepresentationTransport

noncomputable section

def squareBasisBinding {logical physical : Type*}
    [Fintype logical] [Fintype physical] [DecidableEq physical]
    (embedding : logical ↪ physical) : VerifiedMath.BlockReadout.SquareBinding logical physical where
  inputEmbedding := embedding
  outputEmbedding := embedding

theorem squareBlock_squareBasisBinding_apply
    {logical physical : Type*}
    [Fintype logical] [Fintype physical]
    [DecidableEq logical] [DecidableEq physical]
    (embedding : logical ↪ physical)
    (operator : Matrix physical physical ℂ)
    (output input : logical) :
    squareBlock (squareBasisBinding embedding) operator output input =
      operator (embedding output) (embedding input) := by
  rfl

theorem squareBlock_squareBasisBinding
    {logical physical : Type*}
    [Fintype logical] [Fintype physical]
    [DecidableEq logical] [DecidableEq physical]
    (embedding : logical ↪ physical)
    (operator : Matrix physical physical ℂ) :
    squareBlock (squareBasisBinding embedding) operator =
      fun output input => operator (embedding output) (embedding input) := by
  funext output input
  exact squareBlock_squareBasisBinding_apply embedding operator output input

theorem squareBlock_transEmbedding
    {source target physical : Type*}
    [Fintype source] [Fintype target] [Fintype physical]
    [DecidableEq source] [DecidableEq target] [DecidableEq physical]
    (equivalence : source ≃ target) (embedding : target ↪ physical)
    (operator : Matrix physical physical ℂ) :
    squareBlock
        (squareBasisBinding (equivalence.toEmbedding.trans embedding)) operator =
      Matrix.reindexAlgEquiv ℂ ℂ equivalence.symm
        (cleanBlock operator (basisKetEmbeddingMatrix embedding)) := by
  ext output input
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  change operator (embedding (equivalence output))
      (embedding (equivalence input)) =
    cleanBlock operator (basisKetEmbeddingMatrix embedding)
      (equivalence output) (equivalence input)
  exact (cleanBlock_basisKetEmbeddingMatrix_apply operator embedding
    (equivalence output) (equivalence input)).symm

theorem stateNorm_comp_equiv
    {source target : Type*} [Fintype source] [Fintype target]
    (equivalence : source ≃ target) (state : target → ℂ) :
    stateNorm (state ∘ equivalence) = stateNorm state := by
  simp only [stateNorm, VerifiedMath.FiniteComplex.norm,
    VerifiedMath.FiniteComplex.mass, Function.comp_apply]
  apply congrArg Real.sqrt
  exact equivalence.sum_comp (fun index => Complex.normSq (state index))

/-- The two separately owned layers use extensionally identical real-to-complex
coordinate casts.  State this once over an abstract basis so concrete
checkpoint proofs never unfold a large benchmark index merely to compare the
two names. -/
theorem cp03_native_to_public_complexify
    {basis : Type*} [Fintype basis]
    (implementation : Matrix basis basis ℂ)
    (target : EuclideanSpace ℝ basis → EuclideanSpace ℝ basis)
    (tolerance : ℝ)
    (contract : VerifiedMath.OperatorRelations.RealLogicalActionApprox
      NativeSignalQSVTFunctionalBridge.complexifyVector implementation target
      tolerance) :
    VerifiedMath.OperatorRelations.RealLogicalActionApprox complexifyVector implementation target tolerance := by
  exact contract

theorem reindex_mulVec_apply
    {source target scalar : Type*} [Fintype source] [Fintype target]
    [DecidableEq source] [DecidableEq target] [CommSemiring scalar]
    (equivalence : source ≃ target)
    (matrix : Matrix source source scalar) (vector : source → scalar)
    (index : source) :
    (Matrix.reindex equivalence equivalence matrix).mulVec
        (fun targetIndex => vector (equivalence.symm targetIndex))
        (equivalence index) =
      matrix.mulVec vector index := by
  rw [Matrix.reindex_apply]
  unfold Matrix.mulVec dotProduct
  rw [← equivalence.sum_comp]
  simp

/-- The target-index form of `reindex_mulVec_apply`.  Keeping this conversion
abstract prevents concrete benchmark equivalences from being unfolded during
definitional equality checking. -/
theorem reindex_mulVec_apply_target
    {source target scalar : Type*} [Fintype source] [Fintype target]
    [DecidableEq source] [DecidableEq target] [CommSemiring scalar]
    (equivalence : source ≃ target)
    (matrix : Matrix target target scalar) (vector : target → scalar)
    (index : source) :
    (Matrix.reindex equivalence.symm equivalence.symm matrix).mulVec
        (fun sourceIndex => vector (equivalence sourceIndex)) index =
      matrix.mulVec vector (equivalence index) := by
  have pointwise := reindex_mulVec_apply equivalence.symm matrix vector
    (equivalence index)
  simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using pointwise

/-- Casting a real matrix-vector product to complex coordinates commutes with
simultaneous reindexing. -/
theorem complexifyMatrix_mulVec_reindex
    {source target : Type*} [Fintype source] [Fintype target]
    [DecidableEq source] [DecidableEq target]
    (equivalence : source ≃ target)
    (matrix : Matrix source source ℝ) (vector : source → ℝ)
    (index : source) :
    (complexifyMatrix matrix).mulVec (complexifyState vector) index =
      NativeSignalQSVTFunctionalBridge.complexifyVector
        (WithLp.toLp 2
          ((Matrix.reindexAlgEquiv ℝ ℝ equivalence matrix).mulVec
            (fun targetIndex => vector (equivalence.symm targetIndex))))
        (equivalence index) := by
  rw [Matrix.coe_reindexAlgEquiv]
  change (∑ coordinate, (matrix index coordinate : ℂ) *
      (vector coordinate : ℂ)) =
    (((Matrix.reindex equivalence equivalence matrix).mulVec
      (fun targetIndex => vector (equivalence.symm targetIndex))
      (equivalence index) : ℝ) : ℂ)
  rw [reindex_mulVec_apply equivalence matrix vector index]
  simp only [Matrix.mulVec, dotProduct]
  push_cast
  rfl

def l2Reindex {source target : Type*} [Fintype source] [Fintype target]
    (equivalence : source ≃ target) :
    EuclideanSpace ℝ source ≃ₗᵢ[ℝ] EuclideanSpace ℝ target :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ equivalence

theorem realLogicalApprox_of_reindex
    {source target : Type*} [Fintype source] [Fintype target]
    [DecidableEq source] [DecidableEq target]
    (equivalence : source ≃ target)
    (actual : Matrix target target ℂ) (ideal : Matrix source source ℝ)
    (tolerance : ℝ)
    (contract : VerifiedMath.OperatorRelations.RealLogicalActionApprox complexifyVector actual
      (fun state => WithLp.toLp 2
        ((Matrix.reindexAlgEquiv ℝ ℝ equivalence ideal).mulVec state.ofLp))
      tolerance) :
    VerifiedMath.OperatorRelations.RealLogicalActionApprox complexifyVector
      (Matrix.reindexAlgEquiv ℂ ℂ equivalence.symm actual)
      (fun state => WithLp.toLp 2 (ideal.mulVec state.ofLp)) tolerance := by
  intro state
  let transported : EuclideanSpace ℝ target :=
    WithLp.toLp 2 (fun index => state.ofLp (equivalence.symm index))
  have bound := contract transported
  have transportedNorm : ‖transported‖ = ‖state‖ := by
    change ‖(l2Reindex equivalence) state‖ = ‖state‖
    exact (l2Reindex equivalence).norm_map state
  have actualPoint (index : source) :
      (Matrix.reindexAlgEquiv ℂ ℂ equivalence.symm actual).mulVec
          (complexifyVector state) index =
        actual.mulVec (complexifyVector transported) (equivalence index) := by
    rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
    unfold Matrix.mulVec dotProduct
    rw [← equivalence.sum_comp]
    simp [transported, complexifyVector,
      VerifiedMath.Complexification.euclideanVector]
  have idealPoint (index : source) :
      complexifyVector (WithLp.toLp 2 (ideal.mulVec state.ofLp)) index =
        complexifyVector
          (WithLp.toLp 2
            ((Matrix.reindexAlgEquiv ℝ ℝ equivalence ideal).mulVec
              transported.ofLp)) (equivalence index) := by
    change ((ideal.mulVec state.ofLp index : ℝ) : ℂ) = _
    rw [Matrix.coe_reindexAlgEquiv]
    simpa [transported, complexifyVector,
      VerifiedMath.Complexification.euclideanVector] using congrArg
      (fun value : ℝ => (value : ℂ))
      (reindex_mulVec_apply equivalence ideal state.ofLp index).symm
  have difference :
      (fun index =>
        (Matrix.reindexAlgEquiv ℂ ℂ equivalence.symm actual).mulVec
            (complexifyVector state) index -
          complexifyVector (WithLp.toLp 2 (ideal.mulVec state.ofLp)) index) =
        (fun index => actual.mulVec (complexifyVector transported) index -
          complexifyVector
            (WithLp.toLp 2
              ((Matrix.reindexAlgEquiv ℝ ℝ equivalence ideal).mulVec
                transported.ofLp)) index) ∘ equivalence := by
    funext index
    rw [actualPoint, idealPoint]
    rfl
  change stateNorm (fun index =>
    (Matrix.reindexAlgEquiv ℂ ℂ equivalence.symm actual).mulVec
        (complexifyVector state) index -
      complexifyVector (WithLp.toLp 2 (ideal.mulVec state.ofLp)) index) ≤
    tolerance * ‖state‖
  rw [difference, stateNorm_comp_equiv]
  rw [transportedNorm] at bound
  exact bound

/-- Combined abstract transport when the upstream circuit layer uses its own
name for the coordinatewise real-to-complex cast. -/
theorem realLogicalApprox_of_reindex_native
    {source target : Type*} [Fintype source] [Fintype target]
    [DecidableEq source] [DecidableEq target]
    (equivalence : source ≃ target)
    (actual : Matrix target target ℂ) (ideal : Matrix source source ℝ)
    (tolerance : ℝ)
    (contract : VerifiedMath.OperatorRelations.RealLogicalActionApprox
      NativeSignalQSVTFunctionalBridge.complexifyVector actual
      (fun state => WithLp.toLp 2
        ((Matrix.reindexAlgEquiv ℝ ℝ equivalence ideal).mulVec state.ofLp))
      tolerance) :
    VerifiedMath.OperatorRelations.RealLogicalActionApprox complexifyVector
      (Matrix.reindexAlgEquiv ℂ ℂ equivalence.symm actual)
      (fun state => WithLp.toLp 2 (ideal.mulVec state.ofLp)) tolerance := by
  apply realLogicalApprox_of_reindex equivalence actual ideal tolerance
  exact cp03_native_to_public_complexify actual _ tolerance contract

end

end QLean.Proofs.CheckpointCorrespondence.Internal
