import QLean.Circuits.FiniteRationalConfigurationPreparation
import QLean.History.Implementation.HistoryPipelineFiniteScientificH3
import QLean.History.Implementation.HistoryPipelineFiniteCorrectedP05
import QLean.History.Implementation.HistoryPipelineSumComposition
import QLean.History.FiniteScientificHistoryPlan
import QLean.History.ExtendedHistoryEnumeration
import QLean.SignalProcessing.M13bFiniteOuterCompiler
import QLean.SignalProcessing.RootExactBasisPhase
import QLean.Circuits.QSPProgramSyntax
import QLean.Circuits.Foundation.OrderedImagePhase

/-!
# Finite scientific source for numerical circuit construction

The numerical emitter reads the integer history shape and rational initial
amplitudes.  Its internal adapter supplies an inert real error field solely
because the existing layout type carries analytic data; the emitted history
word does not read that field.  This adapter is not a scientific target and
does not confer the theory-path correspondence theorem on numerical output.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.FiniteScientificCircuitSource

open ProbabilityGeneratorQProof
open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open ExecutableHistoryFiniteScientificH3
open ExecutableHistoryCore

open ExecutableHistoryImplementationRole
open ExecutableHistoryHistoryEmbedding
open ScientificExtractionPhysicalSpecification
open SpectralSamplingProof.Analytic
open VerifiedCircuitCore
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open QLean.Circuits.FiniteRationalConfigurationPreparation

structure FiniteScientificSource where
  qParameters : QParameters
  historyParameters : HistoryBlockEncoding.HistorySpec.Parameters
  historyWellFormed : HistoryBlockEncoding.HistorySpec.WellFormed historyParameters
  initial : SparseInitial qParameters
  historyBlocks : Nat
  historyBlocksPositive : 0 < historyBlocks
  binaryLabelsExact :
    historyParameters.binaryLabels =
      historyIdleBlockSize historyParameters.taylorOrder
  clockEndExact :
    historyParameters.clockEnd =
      historyParameters.physicalClocks + historyBlocks
  stepPositive : 0 < historyParameters.stepSize
  scaledStepSmall :
    (3 * (qParameters.K : ℝ)) * (historyParameters.stepSize : ℝ) ≤ 1

/-- Inert analytic fields are erased by the finite history emitter.  They
must not be interpreted as an accuracy certificate or a numerical output
guarantee. -/
def FiniteScientificSource.layoutSource
    (input : FiniteScientificSource) : AlignedCommonSource119 :=
  { qParameters := input.qParameters
    historyParameters := input.historyParameters
    historyWellFormed := input.historyWellFormed
    initial := input.initial.amplitude
    historyBlocks := input.historyBlocks
    historyBlocksPositive := input.historyBlocksPositive
    binaryLabelsExact := input.binaryLabelsExact
    clockEndExact := input.clockEndExact
    stepPositive := input.stepPositive
    scaledStepSmall := input.scaledStepSmall
    targetStateError := 1
    targetStateErrorPositive := by norm_num
    independentParameterLayout := () }

/-- Present a proof-side scientific source in the same finite input type
used by numerical generation.  Enumeration is confined to this theoretical
adapter; a numerical caller supplies its sparse list directly. -/
noncomputable def FiniteScientificSource.ofAlignedCommonSource
    (source : AlignedCommonSource119) : FiniteScientificSource :=
  { qParameters := source.qParameters
    historyParameters := source.historyParameters
    historyWellFormed := source.historyWellFormed
    initial := SparseInitial.ofAmplitude source.initial
    historyBlocks := source.historyBlocks
    historyBlocksPositive := source.historyBlocksPositive
    binaryLabelsExact := source.binaryLabelsExact
    clockEndExact := source.clockEndExact
    stepPositive := source.stepPositive
    scaledStepSmall := source.scaledStepSmall }

def FiniteScientificSource.historyQubits
    (input : FiniteScientificSource) : Nat :=
  finiteScientificHistoryQubits119 input.layoutSource

def FiniteScientificSource.historyCircuit
    (input : FiniteScientificSource) :
    VerifiedCircuitCore.Circuit (PrimitiveGate input.historyQubits) :=
  finiteScientificCorrectedP05Circuit119 input.layoutSource

def FiniteScientificSource.branchQubits
    (input : FiniteScientificSource) : Nat :=
  input.historyQubits + 3

def FiniteScientificSource.preparationQubits
    (input : FiniteScientificSource) : Nat :=
  ExecutableHistoryCore.prepWidth023 input.branchQubits

def FiniteScientificSource.branchLayout
    (input : FiniteScientificSource) :
    ControlLayout input.historyQubits input.branchQubits :=
  ExecutableHistoryCore.branchControlLayout119 input.historyQubits

def FiniteScientificSource.historyControlLayout
    (input : FiniteScientificSource) :
    ControlLayout input.historyQubits input.preparationQubits :=
  let branch := input.branchLayout
  let embed := ExecutableHistoryCore.dataPlacement023 input.branchQubits
  { placement := branch.placement.trans embed
    control := embed branch.control
    work := fun slot => embed (branch.work slot)
    control_ne_placed := by
      intro wire equal
      exact branch.control_ne_placed wire (embed.injective equal)
    work_injective := by
      intro left right equal
      exact branch.work_injective (embed.injective equal)
    work_ne_control := by
      intro slot equal
      exact branch.work_ne_control slot (embed.injective equal)
    work_ne_placed := by
      intro slot wire equal
      exact branch.work_ne_placed slot wire (embed.injective equal) }

private theorem FiniteScientificSource.systemWidth_le_historyQubits
    (input : FiniteScientificSource) :
    input.qParameters.systemWidth ≤ input.historyQubits := by
  dsimp [FiniteScientificSource.historyQubits,
    finiteScientificHistoryQubits119,
    FiniteScientificSource.layoutSource]
  omega

def FiniteScientificSource.rhsPlacement
    (input : FiniteScientificSource) :
    PreparationPlacement input.qParameters input.preparationQubits where
  data := fun bit =>
    input.historyControlLayout.placement
      (finiteScientificHistoryDataWire119 input.layoutSource bit)
  /- `dataPlacement023` interleaves each logical data wire with two clean
  work wires. An offset from `branchQubits` can overlap those data wires;
  the first free wire of each triple is used instead. -/
  scratch := (List.finRange input.qParameters.systemWidth).map fun bit =>
    ⟨3 * bit.val + 1, by
      rw [FiniteScientificSource.preparationQubits,
        ExecutableHistoryCore.prepWidth023_eq_data_plus_work]
      dsimp [ExecutableHistoryCore.prepWorkCount023]
      have bound := bit.isLt
      have hsys := input.systemWidth_le_historyQubits
      dsimp [FiniteScientificSource.branchQubits] at *
      omega⟩
  phase := ⟨3 * input.qParameters.systemWidth + 1, by
    rw [FiniteScientificSource.preparationQubits,
      ExecutableHistoryCore.prepWidth023_eq_data_plus_work]
    dsimp [ExecutableHistoryCore.prepWorkCount023]
    have hsys := input.systemWidth_le_historyQubits
    dsimp [FiniteScientificSource.branchQubits] at *
    omega⟩

def FiniteScientificSource.rhsPreparation
    (input : FiniteScientificSource) :
    NormalizedCircuit input.preparationQubits :=
  input.initial.bPlusPreparation input.rhsPlacement
    input.historyControlLayout.control

/-- The public scientific construction takes ν = 1.  Its controlled
extension rotation is therefore zero; no independent numerical scale is
accepted here that would change the signal circuit apart from QSP phases. -/
def FiniteScientificSource.nuAngle
    (_input : FiniteScientificSource) : VerifiedCircuitCore.AngleExpr :=
  rationalAngle 0

/-- Compile the H-nu branch on its native register, then place it in the
preparation workspace. This is also the physical assembly used by the
independent P18 proof. The finite RHS preparer is unchanged. -/
def FiniteScientificSource.branchHistory
    (input : FiniteScientificSource) : NormalizedCircuit input.historyQubits :=
  { circuit := input.historyCircuit
    normalized := by intro gate _; cases gate <;> trivial }

def FiniteScientificSource.hnuBranchWithAngle
    (input : FiniteScientificSource) (angle : VerifiedCircuitCore.AngleExpr) :
    NormalizedCircuit input.branchQubits :=
  { circuit := VerifiedCircuitCore.Circuit.sequence [
      (controlCircuit input.branchLayout input.branchHistory).circuit,
      VerifiedCircuitCore.Circuit.boolMultiControlledRy
        [(input.branchLayout.control, false)] [input.branchLayout.work 0]
        (input.branchLayout.work 1) angle]
    normalized := by intro gate _; cases gate <;> trivial }

def FiniteScientificSource.alignedHnuWithAngle
    (input : FiniteScientificSource) (angle : VerifiedCircuitCore.AngleExpr) :
    NormalizedCircuit input.preparationQubits :=
  NormalizedCircuit.mapWires (dataPlacement023 input.branchQubits)
    (input.hnuBranchWithAngle angle)

def FiniteScientificSource.p18CircuitWithAngle
    (input : FiniteScientificSource) (angle : VerifiedCircuitCore.AngleExpr) :
    VerifiedCircuitCore.Circuit (PrimitiveGate
      (ExecutableHistoryQbPlusCleanBlock.blockQubits119
        input.preparationQubits)) :=
  VerifiedCircuitCore.Circuit.sequence [
    (NormalizedCircuit.mapWires
      (ExecutableHistoryQbPlusCleanBlock.dataPlacement119 input.preparationQubits)
      (input.alignedHnuWithAngle angle)).circuit,
    ExecutableHistoryQbPlusCleanBlock.qBPlusBlockCircuit119 input.rhsPreparation]

/-- The complete image-phase work register is a second P18 block and one
clean flag, matching the physical width used by the theoretical projector.
-/
def FiniteScientificSource.p18Qubits
    (input : FiniteScientificSource) : Nat :=
  ExecutableHistoryQbPlusCleanBlock.blockQubits119 input.preparationQubits

def FiniteScientificSource.phaseQubits
    (input : FiniteScientificSource) : Nat :=
  input.p18Qubits + (input.p18Qubits + 1)

def FiniteScientificSource.phasePlacement
    (input : FiniteScientificSource) :
    Fin input.p18Qubits ↪ Fin input.phaseQubits :=
  VerifiedCircuitCore.NativeEmbeddingImagePhase.standardImagePhasePlacement
    input.p18Qubits

def FiniteScientificSource.phaseScratch
    (input : FiniteScientificSource) : List (Fin input.phaseQubits) :=
  VerifiedCircuitCore.NativeEmbeddingImagePhase.standardImagePhaseScratches
    input.p18Qubits

def FiniteScientificSource.phaseFlag
    (input : FiniteScientificSource) : Fin input.phaseQubits :=
  VerifiedCircuitCore.NativeEmbeddingImagePhase.standardImagePhaseFlag
    input.p18Qubits

def FiniteScientificSource.sourceBasis
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (index : GramOperator.ExtendedIndex
      (Fintype.card (QConfiguration input.qParameters))
      input.historyParameters.clockEnd
      input.historyParameters.binaryLabels) :
    QubitBasis input.p18Qubits :=
  let historyPlan := finiteScientificHistorySourcePlan119 input.layoutSource
    fits input.branchLayout
  let branch := finiteExtendedIndexBasisOfPlan119 historyPlan index
  let aligned := finiteFixedOutsideBasisEmbedding
    (dataPlacement023 input.branchQubits) (fun _ => false) branch
  NativeSignalQSVTActual.finiteSignalBasis119 input.preparationQubits 0 aligned

/-- A deterministic enumeration of the logical image. The valid history
layout is injective, so no duplicate removal or classical enumeration is
needed. Completeness is proved at the correspondence boundary. -/
def FiniteScientificSource.imagePhaseProgram
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource) :
    List (List (Fin input.phaseQubits × Bool)) :=
  let indices := ScientificExtractionPhysicalSpecification.finiteExtendedHistoryRows119
    (Fintype.card (QConfiguration input.qParameters))
    input.historyParameters.clockEnd
    input.historyParameters.binaryLabels
  VerifiedCircuitCore.OrderedImagePhase.program indices (input.sourceBasis fits)

def FiniteScientificSource.imagePhaseCircuit
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (angle : VerifiedCircuitCore.AngleExpr) :
    VerifiedCircuitCore.Circuit (PrimitiveGate input.phaseQubits) :=
  VerifiedCircuitCore.NativeExactBasisPhase.booleanProgramPhaseCircuitExpr
    (input.imagePhaseProgram fits) input.phaseScratch input.phaseFlag angle

/-- The finite generator's selected image is independent of its enumeration
order. Completeness is intrinsic; a caller supplies only the logical
relabeling used at a proof boundary. -/
theorem FiniteScientificSource.imagePhaseCircuit_apply_clean_state
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    {target : Type*} [Fintype target] [DecidableEq target]
    (rename : GramOperator.ExtendedIndex
      (Fintype.card (QConfiguration input.qParameters))
      input.historyParameters.clockEnd input.historyParameters.binaryLabels ≃ target)
    (embedding : target ↪ QubitBasis input.p18Qubits)
    (same : ∀ row, input.sourceBasis fits row = embedding (rename row))
    (angle : VerifiedCircuitCore.AngleExpr)
    (state : VerifiedCircuitCore.State (QubitBasis input.p18Qubits)) :
    VerifiedCircuitCore.applyOperator
      (VerifiedCircuitCore.Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (input.imagePhaseCircuit fits angle))
      (fixedOutsideStateEmbedding (NativeEmbeddingImagePhase.standardImagePhasePlacement
        input.p18Qubits) (fun _ => false) state) =
    fixedOutsideStateEmbedding (NativeEmbeddingImagePhase.standardImagePhasePlacement
      input.p18Qubits) (fun _ => false)
      (VerifiedCircuitCore.applyOperator (NativeEmbeddingImagePhase.sourceImagePhaseOperator
        embedding angle.uniformValue) state) := by
  dsimp only [FiniteScientificSource.phaseQubits]
  have circuit_eq : input.imagePhaseCircuit fits angle =
      OrderedImagePhase.circuit
        (ScientificExtractionPhysicalSpecification.finiteExtendedHistoryRows119
          (Fintype.card (QConfiguration input.qParameters))
          input.historyParameters.clockEnd input.historyParameters.binaryLabels)
        (input.sourceBasis fits) angle := rfl
  rw [circuit_eq]
  have action := OrderedImagePhase.apply_clean_state_of_reindex (n := input.p18Qubits)
    (ScientificExtractionPhysicalSpecification.finiteExtendedHistoryRows119 _ _ _)
    (ScientificExtractionPhysicalSpecification.finiteExtendedHistoryRows119_nodup _ _ _)
    (ScientificExtractionPhysicalSpecification.finiteExtendedHistoryRows119_complete _ _ _)
    (input.sourceBasis fits) rename embedding same angle (fun _ => 0) state
  exact action

def FiniteScientificSource.liftedP18CircuitWithAngle
    (input : FiniteScientificSource) (angle : VerifiedCircuitCore.AngleExpr) :
    VerifiedCircuitCore.Circuit (PrimitiveGate input.phaseQubits) :=
  (input.p18CircuitWithAngle angle).mapGates (PrimitiveGate.mapWires input.phasePlacement)

def externalControlLayout (qubits : Nat) :
    ExternallyControlledCircuitLayout qubits (qubits + 3) :=
  M13bExternallyControlledCompute.m13bExternalControlLayout qubits

def FiniteScientificSource.outerPlanWithAngle
    (input : FiniteScientificSource)
    (angle : VerifiedCircuitCore.AngleExpr)
    (fits : HistoryIndexFitsLayout119 input.layoutSource) :
    M13bFiniteOuterCompiler.Plan input.phaseQubits where
  signalCircuit := input.liftedP18CircuitWithAngle angle
  sourcePhase := input.imagePhaseCircuit fits
  targetPhase := input.imagePhaseCircuit fits
  layout := externalControlLayout input.phaseQubits

def FiniteScientificSource.outerPlan
    (input : FiniteScientificSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource) :
    M13bFiniteOuterCompiler.Plan input.phaseQubits :=
  input.outerPlanWithAngle input.nuAngle fits

end QLean.Circuits.FiniteScientificCircuitSource
