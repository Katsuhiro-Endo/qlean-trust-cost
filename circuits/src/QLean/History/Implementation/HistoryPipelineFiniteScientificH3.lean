import QLean.History.Implementation.HistoryPipelineFiniteScientificLayout
import QLean.History.Implementation.HistoryPipelineFiniteCorrectedP05Plan

set_option autoImplicit false
set_option warningAsError true

/-!
Finite repaired-H3 evidence and corrected history assembly. The constructors
below only inspect integer wire positions and finite angle expressions.
They do not evaluate proof-side raw history data or choose QSP phases.
-/

namespace ExecutableHistoryFiniteScientificH3

open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open ExecutableHistoryFiniteScientificLayout
open ExecutableHistoryFiniteScientificAngles
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open VerifiedCircuitCore

private theorem finiteUniformWorkNeActive119
    (source : AlignedCommonSource119) (index : Fin 2) :
    (historyUniformControlWork (finiteScientificHistoryLayout119 source)).wire
      index ≠ historyActiveWire (finiteScientificHistoryLayout119 source) := by
  let layout := finiteScientificHistoryLayout119 source
  intro equality
  dsimp [historyUniformControlWork, historyActiveWire,
    historyWorkspaceSlice] at equality
  have values := congrArg Fin.val (layout.workspace.injective equality)
  simp only [Nat.zero_add] at values
  omega

theorem finiteH3UniformEvidence119 (source : AlignedCommonSource119) :
    HistoryOrderUniformExternalControlEvidence
      (finiteScientificHistoryLayout119 source) := by
  let layout := finiteScientificHistoryLayout119 source
  exact {
    active_ne_order := by
      intro index
      exact finiteWorkspaceNeOrder119 source _
        (historyActiveWire_mem_workspace layout) index
    work₀_ne_active := finiteUniformWorkNeActive119 source 0
    work₁_ne_active := finiteUniformWorkNeActive119 source 1
    work₀_ne_order := by
      intro index
      exact finiteWorkspaceNeOrder119 source _
        (historyUniformControlWork_wire_mem_workspace layout 0) index
    work₁_ne_order := by
      intro index
      exact finiteWorkspaceNeOrder119 source _
        (historyUniformControlWork_wire_mem_workspace layout 1) index }

private theorem finiteBranchNeClockCarry119 (source : AlignedCommonSource119) :
    historyBranchWire (finiteScientificHistoryLayout119 source) ≠
      historyClockIncrementCarry (finiteScientificHistoryLayout119 source) := by
  let layout := finiteScientificHistoryLayout119 source
  intro equality
  change layout.workspace.wire _ = layout.workspace.wire _ at equality
  have values := congrArg Fin.val (layout.workspace.injective equality)
  change historySharedPoolWidth (finiteCircuitShapeParameters119 source)
      source.qParameters.generatorWorkWidth + 2 =
    5 + 2 * historyClockWidth
        (finiteCircuitShapeParameters119 source).timeSteps
        (finiteCircuitShapeParameters119 source).taylorOrder
        (finiteCircuitShapeParameters119 source).idlingSteps +
      historyEqualityWorkWidth (finiteCircuitShapeParameters119 source) at values
  have hStructural := Nat.le_max_right source.qParameters.generatorWorkWidth
    (historyStructuralPoolWidth (finiteCircuitShapeParameters119 source))
  unfold historySharedPoolWidth historyStructuralPoolWidth at values hStructural
  omega

private theorem finiteCarryNeMasked119 (source : AlignedCommonSource119)
    (index : Fin (historyClockTailWidth
      (finiteCircuitShapeParameters119 source) + 1)) :
    historyClockIncrementCarry (finiteScientificHistoryLayout119 source) ≠
      (historyClockMaskedConstantRegister
        (finiteScientificHistoryLayout119 source)).wire index := by
  let layout := finiteScientificHistoryLayout119 source
  intro equality
  change layout.workspace.wire _ = layout.workspace.wire _ at equality
  have values := congrArg Fin.val (layout.workspace.injective equality)
  change 5 + 2 * historyClockWidth
        (finiteCircuitShapeParameters119 source).timeSteps
        (finiteCircuitShapeParameters119 source).taylorOrder
        (finiteCircuitShapeParameters119 source).idlingSteps +
      historyEqualityWorkWidth (finiteCircuitShapeParameters119 source) =
    5 + 2 * historyClockWidth
        (finiteCircuitShapeParameters119 source).timeSteps
        (finiteCircuitShapeParameters119 source).taylorOrder
        (finiteCircuitShapeParameters119 source).idlingSteps +
      historyEqualityWorkWidth (finiteCircuitShapeParameters119 source) +
      historyMaximumLabelWidth (finiteCircuitShapeParameters119 source) +
      index.val at values
  have hClock : 0 < historyClockWidth
      (finiteCircuitShapeParameters119 source).timeSteps
      (finiteCircuitShapeParameters119 source).taylorOrder
      (finiteCircuitShapeParameters119 source).idlingSteps := by
    unfold historyClockWidth
    omega
  have hMax := Nat.le_max_left
    (historyClockWidth
      (finiteCircuitShapeParameters119 source).timeSteps
      (finiteCircuitShapeParameters119 source).taylorOrder
      (finiteCircuitShapeParameters119 source).idlingSteps)
    (historyOrderWidth (finiteCircuitShapeParameters119 source).taylorOrder)
  unfold historyMaximumLabelWidth at values
  omega

private theorem finiteWorkspaceNeClock119 (source : AlignedCommonSource119)
    (wire : Fin (finiteScientificHistoryQubits119 source))
    (wireMem : wire ∈ historyRegisterWires
      (finiteScientificHistoryLayout119 source).workspace)
    (index : Fin (historyClockWidth
      (finiteCircuitShapeParameters119 source).timeSteps
      (finiteCircuitShapeParameters119 source).taylorOrder
      (finiteCircuitShapeParameters119 source).idlingSteps)) :
    wire ≠ (finiteScientificHistoryLayout119 source).clock.wire index := by
  let layout := finiteScientificHistoryLayout119 source
  simp only [historyRegisterWires, List.mem_ofFn] at wireMem
  rcases wireMem with ⟨workspaceIndex, rfl⟩
  exact (layout.clock_wire_ne_workspace_wire index workspaceIndex).symm

private theorem finiteClockAccumulatorEq119 (source : AlignedCommonSource119)
    (index : Fin (historyClockTailWidth
      (finiteCircuitShapeParameters119 source) + 1)) :
    (historyClockAccumulatorRegister
      (finiteScientificHistoryLayout119 source)).wire index =
      (finiteScientificHistoryLayout119 source).clock.wire
        ⟨index.val, by
          rw [← historyClockTailWidth_succ
            (finiteCircuitShapeParameters119 source)]
          exact index.isLt⟩ := by
  unfold historyClockAccumulatorRegister
  rfl

private theorem finiteBranchNeMasked119 (source : AlignedCommonSource119)
    (index : Fin (historyClockTailWidth
      (finiteCircuitShapeParameters119 source) + 1)) :
    historyBranchWire (finiteScientificHistoryLayout119 source) ≠
      (historyClockMaskedConstantRegister
        (finiteScientificHistoryLayout119 source)).wire index := by
  let layout := finiteScientificHistoryLayout119 source
  intro equality
  change layout.workspace.wire _ = layout.workspace.wire _ at equality
  have values := congrArg Fin.val (layout.workspace.injective equality)
  have hStructural := Nat.le_max_right source.qParameters.generatorWorkWidth
    (historyStructuralPoolWidth (finiteCircuitShapeParameters119 source))
  have hMax := Nat.le_max_left
    (historyClockWidth
      (finiteCircuitShapeParameters119 source).timeSteps
      (finiteCircuitShapeParameters119 source).taylorOrder
      (finiteCircuitShapeParameters119 source).idlingSteps)
    (historyOrderWidth (finiteCircuitShapeParameters119 source).taylorOrder)
  have hIndex : index.val < historyClockWidth
      (finiteCircuitShapeParameters119 source).timeSteps
      (finiteCircuitShapeParameters119 source).taylorOrder
      (finiteCircuitShapeParameters119 source).idlingSteps := by
    have hTail := historyClockTailWidth_succ
      (finiteCircuitShapeParameters119 source)
    omega
  change historySharedPoolWidth (finiteCircuitShapeParameters119 source)
      source.qParameters.generatorWorkWidth + 2 =
    5 + 2 * historyClockWidth
        (finiteCircuitShapeParameters119 source).timeSteps
        (finiteCircuitShapeParameters119 source).taylorOrder
        (finiteCircuitShapeParameters119 source).idlingSteps +
      historyEqualityWorkWidth (finiteCircuitShapeParameters119 source) +
      historyMaximumLabelWidth (finiteCircuitShapeParameters119 source) +
      index.val at values
  unfold historySharedPoolWidth historyStructuralPoolWidth
    historyMaximumLabelWidth at values hStructural
  omega

theorem finiteH3ClockIncrementEvidence119
    (source : AlignedCommonSource119) :
    HistoryControlledClockIncrementEvidence
      (finiteScientificHistoryLayout119 source) := by
  let layout := finiteScientificHistoryLayout119 source
  exact {
    masked_clock_disjoint := by
      intro left right
      have member := historyClockMaskedConstantRegister_wire_mem_workspace
        layout left
      rw [finiteClockAccumulatorEq119 source right]
      exact finiteWorkspaceNeClock119 source _ member _
    carry_ne_masked := by
      intro index
      exact finiteCarryNeMasked119 source index
    carry_ne_clock := by
      intro index
      rw [finiteClockAccumulatorEq119 source index]
      exact finiteWorkspaceNeClock119 source _
        (historyClockIncrementCarry_mem_workspace layout) _
    branch_ne_masked := by
      intro index
      exact finiteBranchNeMasked119 source index
    branch_ne_clock := by
      intro index
      rw [finiteClockAccumulatorEq119 source index]
      exact finiteWorkspaceNeClock119 source _
        (historyBranchWire_mem_workspace layout) _
    branch_ne_carry := finiteBranchNeClockCarry119 source }

/-- All H3 source-order proof fields are recovered from the same finite
history layout. The two recorded angles are syntactically fixed values. -/
def finiteH3SourceOrderEvidence119 (source : AlignedCommonSource119) :
    HistoryClockConcreteSourceOrderEvidence
      (finiteScientificHistoryLayout119 source) where
  uniformExternalControl := finiteH3UniformEvidence119 source
  idleTransform := finiteH3IdleTransformEvidence119 source
  coefficientControl_ne_signal :=
    (finiteHistoryTaylorL2Evidence119 source).active_ne_coefficientSignal
  projectorControl := finiteH3ProjectorEvidence119 source
  controlledIncrement := finiteH3ClockIncrementEvidence119 source
  idleCoefficientAngle := idleCoefficient
  coefficientAngle := correctedCoefficient source 0

/-- The complete repaired-H3 word is emitted from finite scientific layout,
comparison and angle data, with no proof-side raw evaluation. -/
def finiteScientificRepairedH3Circuit119 (source : AlignedCommonSource119) :
    Circuit (PrimitiveGate (finiteScientificHistoryQubits119 source)) :=
  finiteRepairedH3Circuit119 (finiteScientificHistoryLayout119 source)
    (finiteH3SourceOrderEvidence119 source)
    (finiteClockTimeComparison119 source)
    (finiteClockIdleEndComparison119 source)
    source.historyParameters.physicalClocks
    (historyIdleClockEnd source.historyParameters.physicalClocks
      source.historyParameters.taylorOrder
      (finiteScientificHistoryIdleSteps119 source))
    source.historyParameters.binaryLabels
    (repairedIdle source) idleCoefficient

/-- The finite P15 and H3 words share one layout and one typed corrected-P05
plan. Proof fields are erased before primitive gates are emitted. -/
def finiteScientificCorrectedP05Plan119 (source : AlignedCommonSource119) :
    ExecutableHistoryFiniteCorrectedP05.Plan
      (finiteScientificHistoryQubits119 source)
      source.qParameters.generatorDataWidth
      source.qParameters.generatorSignalWidth
      source.qParameters.generatorWorkWidth
      source.qParameters
      (finiteCircuitShapeParameters119 source) :=
  let layout := finiteScientificHistoryLayout119 source
  { layout := layout
    selector := historySelectorPreparationParametersAtLayout layout
      (correctedSelectorHigh source) correctedSelectorLow correctedSelectorLow
    p15Evidence := finiteHistoryTaylorL2Evidence119 source
    p15Control := finiteHistoryQ10ControlEvidence119 source
    coefficientAngles := fun index => correctedCoefficient source index.val
    idleCoefficientAngle := idleCoefficient
    clockEvidence := finiteH3SourceOrderEvidence119 source
    timeComparison := finiteClockTimeComparison119 source
    idleEndComparison := finiteClockIdleEndComparison119 source
    physicalClocks := source.historyParameters.physicalClocks
    idleClockEnd := historyIdleClockEnd
      source.historyParameters.physicalClocks
      source.historyParameters.taylorOrder
      (finiteScientificHistoryIdleSteps119 source)
    binaryLabels := source.historyParameters.binaryLabels
    repairedIdleAngle := repairedIdle source
    repairedCoefficientAngle := idleCoefficient }

def finiteScientificCorrectedP05Circuit119 (source : AlignedCommonSource119) :
    Circuit (PrimitiveGate (finiteScientificHistoryQubits119 source)) :=
  (finiteScientificCorrectedP05Plan119 source).compile

theorem finiteScientificCorrectedP05Circuit119_eq_parts
    (source : AlignedCommonSource119) :
    finiteScientificCorrectedP05Circuit119 source =
      finiteCorrectedP05Circuit119
        (finiteScientificCorrectedP05Plan119 source).selector
        (finiteScientificTaylorCircuit119 source)
        (finiteScientificRepairedH3Circuit119 source) := by
  rfl

end ExecutableHistoryFiniteScientificH3
