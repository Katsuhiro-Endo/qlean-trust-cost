import QLean.Correspondence.GeneralCheckpointData
import QLean.Proofs.CheckpointCorrespondenceCore
import VerifiedMath.Basis
import VerifiedMath.FiniteComplex
import VerifiedMath.FiniteDistribution
import QLean.MathematicalSpecifications.PublicCheckpointData
import VerifiedMath.OperatorRelations
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
import QLean.Correspondence.RepresentationTransport
import QLean.Generator.Implementation.QDecoderCorrectness
import QLean.MathematicalSpecifications.TargetReuseProofs
import QLean.SignalProcessing.M13bFiniteCommonFunctional
import QLean.SignalProcessing.M13bFiniteOuterCompiler
import QLean.SignalProcessing.M13bConjugateControlledCompute
import QLean.SignalProcessing.M13bControlXStateSemantics
import QLean.SignalProcessing.M13bHadamardTrueStateSemantics
import QLean.SignalProcessing.M13bHermitianSuccessReflection

/-! Parameter-general checkpoint correspondence.

The mathematical targets and circuit inputs are constructed from the same
freely varying executable source. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option warningAsError true

namespace QLean.Proofs.GeneralCheckpointCorrespondence

open Matrix VerifiedCircuitCore
open ProbabilityGeneratorQProof
open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open QLean.MathematicalSpecifications
open QLean.MathematicalSpecifications.PublicCheckpoints
open QLean.MathematicalSpecifications.Targets
open QLean.Circuits.CheckpointCircuits
open QLean.Correspondence.CheckpointReadout
open QLean.Correspondence.GeneralCheckpointData
open NativeConcreteP18QSPWitness
open NativeSingularPairTwoFrame
open SpectralSamplingProof.Analytic
open QLean.Proofs.CheckpointCorrespondence.Internal

noncomputable section

/-- Put an independent history coordinate into the actual data, clock and
order registers.  Selector, signal and work wires remain zero. -/
def historyPhysicalBasis (input : M13bPrimitiveCandidate.ExecutableInput119)
    (index : HistoryMatrixIndex (historyMatrixParameters input.source)) :
    QubitBasis (ExecutableRaw119 input.source).history.qubits :=
  ExecutableHistoryHistoryEmbedding.executableHistoryBasis119
    input.source input.domain input.fits
    { clock := index.clock
      state :=
        { label := index.order
          configuration := configurationEquiv input.source index.state } }

/-- The former internal index conversion, retained only to prove that the
direct register placement above has exactly the established semantics. -/
private def historyPhysicalEmbeddingLegacy
    (input : M13bPrimitiveCandidate.ExecutableInput119) :
    HistoryMatrixIndex (historyMatrixParameters input.source) ↪
      QubitBasis (ExecutableRaw119 input.source).history.qubits :=
  (historyIndexEquiv input.source).toEmbedding.trans
    ((ExecutableHistoryReferenceM10Bridge.indexEquiv
      input.source.historyParameters).symm.toEmbedding.trans
        (ExecutableHistoryHistoryEmbedding.executableHistoryEmbedding119
          input.source input.domain input.fits))

theorem historyPhysicalBasis_eq_legacy
    (input : M13bPrimitiveCandidate.ExecutableInput119)
    (index : HistoryMatrixIndex (historyMatrixParameters input.source)) :
    historyPhysicalBasis input index = historyPhysicalEmbeddingLegacy input index := by
  let bridge := ExecutableHistoryReferenceM10Bridge.indexEquiv
    (Configuration := QConfiguration input.source.qParameters)
    input.source.historyParameters
  have hbridge :
      bridge
        { clock := index.clock
          state :=
            { label := index.order
              configuration := configurationEquiv input.source index.state } } =
        historyIndexEquiv input.source index := by
    cases index
    rfl
  have hindex :
      { clock := index.clock
        state :=
          { label := index.order
            configuration := configurationEquiv input.source index.state } } =
        bridge.symm (historyIndexEquiv input.source index) := by
    apply bridge.injective
    simpa only [Equiv.apply_symm_apply] using hbridge
  change ExecutableHistoryHistoryEmbedding.executableHistoryBasis119
      input.source input.domain input.fits
      { clock := index.clock
        state :=
          { label := index.order
            configuration := configurationEquiv input.source index.state } } =
    ExecutableHistoryHistoryEmbedding.executableHistoryBasis119
      input.source input.domain input.fits
      (bridge.symm (historyIndexEquiv input.source index))
  exact congrArg
    (ExecutableHistoryHistoryEmbedding.executableHistoryBasis119
      input.source input.domain input.fits) hindex

/-- The binding is just the direct logical-history-to-physical-bit placement. -/
def historyPhysicalEmbedding (input : M13bPrimitiveCandidate.ExecutableInput119) :
    HistoryMatrixIndex (historyMatrixParameters input.source) ↪
      QubitBasis (ExecutableRaw119 input.source).history.qubits where
  toFun := historyPhysicalBasis input
  inj' := by
    intro left right equal
    apply (historyPhysicalEmbeddingLegacy input).injective
    calc
      historyPhysicalEmbeddingLegacy input left = historyPhysicalBasis input left :=
        (historyPhysicalBasis_eq_legacy input left).symm
      _ = historyPhysicalBasis input right := equal
      _ = historyPhysicalEmbeddingLegacy input right :=
        historyPhysicalBasis_eq_legacy input right

def historyBinding (input : M13bPrimitiveCandidate.ExecutableInput119) :
    VerifiedMath.BlockReadout.SquareBinding (HistoryMatrixIndex (historyMatrixParameters input.source))
      (QubitBasis (ExecutableRaw119 input.source).history.qubits) :=
  QLean.Proofs.CheckpointCorrespondence.Internal.squareBasisBinding
    (historyPhysicalEmbedding input)

theorem executable_historyOperator_eq_independent
    (source : AlignedCommonSource119) :
    JenningsHistory.historyMatrix (executableSystem119 source) =
      Matrix.reindexAlgEquiv ℝ ℝ (historyIndexEquiv source)
        (HistoryLinearSystem.operator
          (historyEquationData source).toMatrixData) := by
  rw [executableSystem_eq_independent_reindex]
  change JenningsHistory.historyMatrix
      (QLean.Correspondence.HistoryLinearSystemTransport.toCircuitData
        (stateEquiv source)
        (historyEquationData source)) =
    Matrix.reindexAlgEquiv ℝ ℝ
      (QLean.Correspondence.HistoryLinearSystemTransport.indexEquiv
        (stateEquiv source))
      (HistoryLinearSystem.operator (historyEquationData source).toMatrixData)
  exact QLean.Correspondence.KernelReflectionTransport.historyOperator_eq_reindex
    (stateEquiv source) (historyEquationData source)

/-- CP02, parameter-general: the actual primitive history circuit is the
independent Jennings matrix divided by the normalization emitted from the
same source. -/
theorem historyCircuit_correct
    (input : M13bPrimitiveCandidate.ExecutableInput119) :
    historyBlock (historyBinding input)
        (Circuit.denote
          (primitiveGateOperatorWithSymbols ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
          (historyCircuit input)) =
      ((executableAlpha119 input.source : ℂ)⁻¹) •
        historyMatrix (historyMatrixParameters input.source)
          (historyMatrixConditions input.source) := by
  rw [historyCircuit, Circuit.denote_withSymbols_specializeSymbols]
  funext output inputIndex
  rw [historyBlock, historyBinding,
    QLean.Proofs.CheckpointCorrespondence.Internal.squareBlock_squareBasisBinding]
  change Circuit.denote
      (primitiveGateOperatorWithSymbols ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
      (buildHistoryCircuit input)
      (historyPhysicalBasis input output)
      (historyPhysicalBasis input inputIndex) = _
  rw [historyPhysicalBasis_eq_legacy, historyPhysicalBasis_eq_legacy]
  change Circuit.denote
      (primitiveGateOperatorWithSymbols ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
      (buildHistoryCircuit input)
      (ExecutableHistoryHistoryEmbedding.executableHistoryBasis119
        input.source input.domain input.fits
        ((ExecutableHistoryReferenceM10Bridge.indexEquiv
          input.source.historyParameters).symm
            (historyIndexEquiv input.source output)))
      (ExecutableHistoryHistoryEmbedding.executableHistoryBasis119
        input.source input.domain input.fits
        ((ExecutableHistoryReferenceM10Bridge.indexEquiv
          input.source.historyParameters).symm
            (historyIndexEquiv input.source inputIndex))) = _
  unfold buildHistoryCircuit cp02HistoryCircuit
  rw [ExecutableHistoryExecutableHistory.correctedP05Component119_entry_eq_scaledHistory]
  simp only [Equiv.apply_symm_apply]
  unfold JenningsHistory.scaledHistory
  change
    ((JenningsHistory.historyMatrix (executableSystem119 input.source)
      (historyIndexEquiv input.source output)
      (historyIndexEquiv input.source inputIndex) /
        executableAlpha119 input.source : ℝ) : ℂ) = _
  rw [executable_historyOperator_eq_independent]
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  simp [historyMatrix_eq_operator,
    VerifiedMath.Complexification.matrix, div_eq_mul_inv,
    mul_comm]
  left
  rfl

/-! ## CP03: parameter-general kernel reflection -/

/-- Independent scalar-extended coordinates occupy the signal source basis;
the image-phase workspace is zero, and the outer success control is false.
This is the logical basis placement read by the public CP03 theorem. -/
def qsvtPhysicalEmbedding (input : M13bPrimitiveCandidate.ExecutableInput119) :
    KernelExtendedIndex
        (kernelReflectionParameters input.source input.assumptions) ↪
      QubitBasis (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource + 3) :=
  let signal :=
    (extendedIndexEquiv input.source input.assumptions).toEmbedding.trans
      (NativeSignalQSVTActual.executableSignalSourceEmbedding119
        input.source input.domain input.fits
        input.assumptions input.circuitSource)
  let imageWorkspace := fixedOutsideBasisEmbedding
    (VerifiedCircuitCore.NativeEmbeddingImagePhase.standardImagePhasePlacement
      (NativeSignalQSVTActual.ExecutableSignalP18Qubits119
        input.source input.domain input.fits
        input.assumptions input.circuitSource)) (fun _ => false)
  let successControl := fixedOutsideBasisEmbedding
    (M13bExternallyControlledCompute.m13bExternalControlLayout
      (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource)).placement
    (M13bExternallyControlledCompute.m13bControlOutside
      (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource) false)
  signal.trans (imageWorkspace.trans successControl)

theorem qsvtPhysicalEmbedding_eq_legacy
    (input : M13bPrimitiveCandidate.ExecutableInput119) :
    qsvtPhysicalEmbedding input =
      (extendedIndexEquiv input.source input.assumptions).toEmbedding.trans
        (M13bQSVTLogicalEmbedding.qsvtLogicalBasisEmbedding119
          input.domain input.fits input.circuitSource) := by
  ext index wire
  rfl

def qsvtBinding (input : M13bPrimitiveCandidate.ExecutableInput119) :
    VerifiedMath.BlockReadout.SquareBinding
      (KernelExtendedIndex
        (kernelReflectionParameters input.source input.assumptions))
      (QubitBasis (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource + 3)) :=
  squareBasisBinding (qsvtPhysicalEmbedding input)

theorem qsvtBlock_eq_reindex
    (input : M13bPrimitiveCandidate.ExecutableInput119)
    (operator : Matrix
      (QubitBasis (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource + 3))
      (QubitBasis (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource + 3)) ℂ) :
    qsvtBlock (qsvtBinding input) operator =
      Matrix.reindexAlgEquiv ℂ ℂ
        (extendedIndexEquiv input.source input.assumptions).symm
        (cleanBlock operator
          (M13bQSVTLogicalEmbedding.qsvtLogicalEmbedding119
            input.domain input.fits input.circuitSource)) := by
  simpa [qsvtBlock, qsvtBinding, squareBasisBinding,
    qsvtPhysicalEmbedding_eq_legacy,
    M13bQSVTLogicalEmbedding.qsvtLogicalEmbedding119, NativeSingularPairTwoFrame.basisKetEmbeddingMatrix] using
      (squareBlock_transEmbedding
        (extendedIndexEquiv input.source input.assumptions)
        (M13bQSVTLogicalEmbedding.qsvtLogicalBasisEmbedding119
          input.domain input.fits input.circuitSource) operator)

/-- The executable certified reflection and the independent reflection are
the same matrix after the explicit coordinate equivalence. -/
theorem certifiedIdealReflection_eq_independent_reindex
    (input : M13bPrimitiveCandidate.ExecutableInput119) :
    GramOperator.idealKernelReflection
        (M13bPrimitiveCandidate.certifiedInput119 input).base.system
        (M13bPrimitiveCandidate.certifiedInput119 input).base.alpha
        (M13bPrimitiveCandidate.certifiedInput119 input).base.nu
        (M13bPrimitiveCandidate.certifiedInput119 input).base.hdet =
      Matrix.reindexAlgEquiv ℝ ℝ
        (extendedIndexEquiv input.source input.assumptions)
        (kernelReflectionMatrix
          (kernelReflectionParameters input.source input.assumptions)
          (kernelReflectionConditions input.source input.assumptions)) := by
  change GramOperator.idealKernelReflection
      (executableSystem119 input.source)
      (executableAlpha119 input.source) input.assumptions.nu
      input.assumptions.hdet = _
  exact executableIdealReflection_eq_independent_reindex
    input.source input.assumptions

/-! ## CP04: successful history state -/

/-- Minimal public readout of the history branch of a supplied physical
operator.  It contains no benchmark data. -/
def successfulHistoryReadout
    (input : M13bPrimitiveCandidate.ExecutableInput119)
    (operator : Matrix
      (QubitBasis (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource + 3))
      (QubitBasis (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource + 3)) ℂ) :
    KernelExtendedIndex
      (kernelReflectionParameters input.source input.assumptions) → ℂ :=
  (kernelHistoryProjector
      (kernelReflectionParameters input.source input.assumptions)).mulVec
    ((VerifiedMath.BlockReadout.squareBlock (qsvtBinding input) operator).mulVec
      (kernelExtensionState
        (kernelReflectionParameters input.source input.assumptions)))

theorem kernelExtensionState_transport_real
    (input : M13bPrimitiveCandidate.ExecutableInput119)
    (index : KernelExtendedIndex
      (kernelReflectionParameters input.source input.assumptions)) :
    kernelExtensionStateReal
        (kernelReflectionParameters input.source input.assumptions) index =
      (TypedNegativeCases.actualBasis
        (d := ExecutableD119 input.source)
        (c := ExecutableC119 input.source)
        (R := ExecutableLabels119 input.source))
        (extendedIndexEquiv input.source input.assumptions index) := by
  cases index <;> rfl

theorem kernelExtensionState_transport
    (input : M13bPrimitiveCandidate.ExecutableInput119)
    (index : KernelExtendedIndex
      (kernelReflectionParameters input.source input.assumptions)) :
    kernelExtensionState
        (kernelReflectionParameters input.source input.assumptions) index =
      NativeSignalQSVTFunctionalBridge.complexifyVector
        (TypedNegativeCases.actualBasis
          (d := ExecutableD119 input.source)
          (c := ExecutableC119 input.source)
          (R := ExecutableLabels119 input.source))
        (extendedIndexEquiv input.source input.assumptions index) := by
  rw [kernelExtensionState_eq_real]
  exact congrArg (fun value : ℝ => (value : ℂ))
    (kernelExtensionState_transport_real input index)

theorem kernelHistoryProjector_transport
    (input : M13bPrimitiveCandidate.ExecutableInput119)
    (state : executableSignalCleanIndex119 input.source → ℂ)
    (index : KernelExtendedIndex
      (kernelReflectionParameters input.source input.assumptions)) :
    (kernelHistoryProjector
      (kernelReflectionParameters input.source input.assumptions)).mulVec
        (fun publicIndex => state
          (extendedIndexEquiv input.source input.assumptions publicIndex)) index =
      M13cSpecification.complexHistoryProjector119 state
        (extendedIndexEquiv input.source input.assumptions index) := by
  classical
  cases index with
  | inl history =>
      have mapped :
          extendedIndexEquiv input.source input.assumptions (Sum.inl history) =
            Sum.inl
              (QLean.Correspondence.HistoryLinearSystemTransport.indexEquiv
                (stateEquiv input.source) history) := rfl
      simp [kernelHistoryProjector, Matrix.mulVec, dotProduct,
        M13cSpecification.complexHistoryProjector119, mapped]
      rfl
  | inr extension =>
      have mapped :
          extendedIndexEquiv input.source input.assumptions (Sum.inr extension) =
            Sum.inr extension := rfl
      simp [kernelHistoryProjector, Matrix.mulVec, dotProduct,
        M13cSpecification.complexHistoryProjector119, mapped]

theorem qsvtState_reindex
    (input : M13bPrimitiveCandidate.ExecutableInput119)
    (operator : Matrix
      (QubitBasis (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource + 3))
      (QubitBasis (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource + 3)) ℂ) :
    (qsvtBlock (qsvtBinding input) operator).mulVec
        (kernelExtensionState
          (kernelReflectionParameters input.source input.assumptions)) =
      fun index =>
        (cleanBlock operator
          (M13bQSVTLogicalEmbedding.qsvtLogicalEmbedding119
            input.domain input.fits input.circuitSource)).mulVec
          (NativeSignalQSVTFunctionalBridge.complexifyVector
            (TypedNegativeCases.actualBasis
              (d := ExecutableD119 input.source)
              (c := ExecutableC119 input.source)
              (R := ExecutableLabels119 input.source)))
          (extendedIndexEquiv input.source input.assumptions index) := by
  rw [qsvtBlock_eq_reindex]
  have inputEq :
      kernelExtensionState
          (kernelReflectionParameters input.source input.assumptions) =
        fun publicIndex =>
          NativeSignalQSVTFunctionalBridge.complexifyVector
            (TypedNegativeCases.actualBasis
              (d := ExecutableD119 input.source)
              (c := ExecutableC119 input.source)
              (R := ExecutableLabels119 input.source))
            (extendedIndexEquiv input.source input.assumptions publicIndex) := by
    funext publicIndex
    exact kernelExtensionState_transport input publicIndex
  rw [inputEq]
  funext index
  exact reindex_mulVec_apply_target
    (extendedIndexEquiv input.source input.assumptions)
    (cleanBlock operator
      (M13bQSVTLogicalEmbedding.qsvtLogicalEmbedding119
        input.domain input.fits input.circuitSource))
    (NativeSignalQSVTFunctionalBridge.complexifyVector
      (TypedNegativeCases.actualBasis
        (d := ExecutableD119 input.source)
        (c := ExecutableC119 input.source)
        (R := ExecutableLabels119 input.source))) index

theorem successfulHistoryReadout_reindex
    (input : M13bPrimitiveCandidate.ExecutableInput119)
    (operator : Matrix
      (QubitBasis (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource + 3))
      (QubitBasis (widenedP18Qubits119 input.source input.domain input.fits
        input.assumptions input.circuitSource + 3)) ℂ) :
    successfulHistoryReadout input operator =
      fun index => M13cSpecification.complexHistoryProjector119
        ((cleanBlock operator
          (M13bQSVTLogicalEmbedding.qsvtLogicalEmbedding119
            input.domain input.fits input.circuitSource)).mulVec
          (NativeSignalQSVTFunctionalBridge.complexifyVector
            (TypedNegativeCases.actualBasis
              (d := ExecutableD119 input.source)
              (c := ExecutableC119 input.source)
              (R := ExecutableLabels119 input.source))))
        (extendedIndexEquiv input.source input.assumptions index) := by
  unfold successfulHistoryReadout
  change (kernelHistoryProjector
      (kernelReflectionParameters input.source input.assumptions)).mulVec
    ((qsvtBlock (qsvtBinding input) operator).mulVec
      (kernelExtensionState
        (kernelReflectionParameters input.source input.assumptions))) = _
  rw [qsvtState_reindex]
  funext index
  exact kernelHistoryProjector_transport input _ index

theorem executableIdealHistoryProjection_eq_target
    (input : M13bPrimitiveCandidate.ExecutableInput119) :
    M13cSpecification.complexHistoryProjector119
      (NativeSignalQSVTFunctionalBridge.complexifyVector
        (WithLp.toLp 2
          ((GramOperator.idealKernelReflection
            (M13bPrimitiveCandidate.certifiedInput119 input).base.system
            (M13bPrimitiveCandidate.certifiedInput119 input).base.alpha
            (M13bPrimitiveCandidate.certifiedInput119 input).base.nu
            (M13bPrimitiveCandidate.certifiedInput119 input).base.hdet).mulVec
              (TypedNegativeCases.actualBasis
                (d := ExecutableD119 input.source)
                (c := ExecutableC119 input.source)
                (R := ExecutableLabels119 input.source)).ofLp))) =
      M13cSpecification.idealHistoryTarget119 input := by
  let A := (M13bPrimitiveCandidate.certifiedInput119 input).base
  have h := ConcreteHistoryInput.m13ConcreteIdealHistoryTarget_eq_actual
    A.system A.alpha A.nu A.x A.hwell A.hdet A.hraw A.hrhs A.hα A.hν A.hb
  rw [M13cSpecification.complexHistoryProjector119_complexify]
  simpa [A, M13cSpecification.idealHistoryTarget119,
    TypedNegativeCases.actualTarget, TypedNegativeCases.actualBasis,
    ConcreteHistoryInput.m13IdealReflectionEMap,
    ConcreteHistoryInput.matrixEMap, ConcreteHistoryInput.m13ExtensionBasisE,
    ConcreteHistoryInput.extToE, ConcreteHistoryInput.toE] using
      congrArg NativeSignalQSVTFunctionalBridge.complexifyVector h

theorem independentSuccessfulHistory_eq_reindex
    (input : M13bPrimitiveCandidate.ExecutableInput119) :
    successfulHistoryState
        (kernelReflectionParameters input.source input.assumptions)
        (kernelReflectionConditions input.source input.assumptions) =
      fun index => M13cSpecification.idealHistoryTarget119 input
        (extendedIndexEquiv input.source input.assumptions index) := by
  let parameters := kernelReflectionParameters input.source input.assumptions
  let conditions := kernelReflectionConditions input.source input.assumptions
  let equivalence := extendedIndexEquiv input.source input.assumptions
  let matrix := kernelReflectionMatrix parameters conditions
  have vectorEq :
      (fun internalIndex =>
        kernelExtensionStateReal parameters (equivalence.symm internalIndex)) =
        (TypedNegativeCases.actualBasis
          (d := ExecutableD119 input.source)
          (c := ExecutableC119 input.source)
          (R := ExecutableLabels119 input.source)).ofLp := by
    funext internalIndex
    simpa [parameters, equivalence] using
      kernelExtensionState_transport_real input (equivalence.symm internalIndex)
  have stateEq :
      (complexifyMatrix matrix).mulVec (kernelExtensionState parameters) =
        fun index => NativeSignalQSVTFunctionalBridge.complexifyVector
          (WithLp.toLp 2
            ((Matrix.reindexAlgEquiv ℝ ℝ equivalence matrix).mulVec
              (TypedNegativeCases.actualBasis
                (d := ExecutableD119 input.source)
                (c := ExecutableC119 input.source)
                (R := ExecutableLabels119 input.source)).ofLp))
          (equivalence index) := by
    rw [kernelExtensionState_eq_real]
    change (complexifyMatrix matrix).mulVec
        (complexifyState (kernelExtensionStateReal parameters)) = _
    funext index
    have transported := complexifyMatrix_mulVec_reindex equivalence matrix
      (kernelExtensionStateReal parameters) index
    rw [vectorEq] at transported
    exact transported
  change (kernelHistoryProjector parameters).mulVec
      ((complexifyMatrix matrix).mulVec (kernelExtensionState parameters)) = _
  rw [stateEq]
  funext index
  rw [kernelHistoryProjector_transport input]
  rw [← certifiedIdealReflection_eq_independent_reindex input]
  exact congrFun (executableIdealHistoryProjection_eq_target input)
    (extendedIndexEquiv input.source input.assumptions index)



end

end QLean.Proofs.GeneralCheckpointCorrespondence
