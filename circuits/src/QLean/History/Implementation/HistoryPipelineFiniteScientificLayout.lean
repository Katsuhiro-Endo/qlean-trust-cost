import QLean.History.Implementation.HistoryPipelineFiniteScientificWirePlan
import QLean.History.Implementation.HistoryPipelineFiniteP15
import QLean.History.Implementation.HistoryPipelineFiniteScientificAngles

set_option autoImplicit false
set_option warningAsError true

/-!
A computable, fully typed history layout on the finite scientific width.

`HistoryBlockParameters` combines integer layout indices with analytic fields.
The finite emitter reads only the integer indices from this private shape
adapter. Its neutral analytic values are not the scientific target and must
not be used to claim a circuit/target correspondence. That correspondence
requires a separate equality theorem against the certified scientific plan.
-/

namespace ExecutableHistoryFiniteScientificLayout

open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open SpectralSamplingProof.Analytic
open VerifiedCircuitCore
open HistoryPipelineReferenceAdmissibility041
open SpectralSamplingProof.Components

/-- Layout indices for the finite emitter. Analytic entries are inert here;
the mathematical parameters remain those of the independent specification. -/
def finiteCircuitShapeParameters119 (source : AlignedCommonSource119) :
    HistoryBlockParameters where
  timeSteps := source.historyParameters.physicalClocks
  taylorOrder := source.historyParameters.taylorOrder
  idlingSteps := finiteScientificHistoryIdleSteps119 source
  historyBlocks := source.historyBlocks
  timeStepsPositive := source.historyWellFormed.1
  taylorOrderPositive := source.historyWellFormed.2.1
  idlingFitsBinaryBlocks := by
    have hBlock : 0 < historyIdleBlockSize source.historyParameters.taylorOrder := by
      unfold historyIdleBlockSize
      positivity
    have hProd : 0 < source.historyBlocks *
        historyIdleBlockSize source.historyParameters.taylorOrder :=
      Nat.mul_pos source.historyBlocksPositive hBlock
    change (source.historyBlocks *
      historyIdleBlockSize source.historyParameters.taylorOrder - 1 + 1) %
        historyIdleBlockSize source.historyParameters.taylorOrder = 0
    have hEq : source.historyBlocks *
        historyIdleBlockSize source.historyParameters.taylorOrder - 1 + 1 =
      source.historyBlocks *
        historyIdleBlockSize source.historyParameters.taylorOrder := by omega
    rw [hEq]
    simp
  duration := 0
  targetStateError := 1
  stepSize := 1
  omegaH := 0
  historyBlockScale := 0
  gTaylor := 0
  targetStateErrorPositive := by norm_num
  stepSizePositive := by norm_num
  omegaHNonnegative := by norm_num
  selectorPreparationAngles := fun _ => .rational 0 1 (by decide)
  coefficientAngles := fun _ => .rational 0 1 (by decide)
  idleCoefficientAngle := .rational 0 1 (by decide)

def finiteSelectorRegister119 (source : AlignedCommonSource119) :
    Register (finiteScientificHistoryQubits119 source) 2 where
  wire := finiteScientificHistorySelectorWire119 source
  injective := finiteScientificHistorySelectorWire119_injective source

def finiteGeneratorSignalRegister119 (source : AlignedCommonSource119) :
    Register (finiteScientificHistoryQubits119 source)
      source.qParameters.generatorSignalWidth where
  wire := finiteScientificHistoryGeneratorSignalWire119 source
  injective := finiteScientificHistoryGeneratorSignalWire119_injective source

def finiteWorkspaceRegister119 (source : AlignedCommonSource119) :
    Register (finiteScientificHistoryQubits119 source)
      (finiteScientificHistoryWorkspaceWidth119 source) where
  wire := finiteScientificHistoryWorkspaceWire119 source
  injective := finiteScientificHistoryWorkspaceWire119_injective source

def finiteWireList119 (source : AlignedCommonSource119) :
    List (Fin (finiteScientificHistoryQubits119 source)) :=
  historyRegisterWires (finiteSelectorRegister119 source) ++
  historyRegisterWires (finiteScientificHistoryDataRegister119 source) ++
  historyRegisterWires (finiteScientificHistoryClockRegister119 source) ++
  historyRegisterWires (finiteScientificHistoryOrderRegister119 source) ++
  historyRegisterWires (finiteGeneratorSignalRegister119 source) ++
  List.ofFn (finiteScientificHistoryDistinguishedSignalWire119 source) ++
  historyRegisterWires (finiteWorkspaceRegister119 source)

private noncomputable def referenceWireValues119
    (source : AlignedCommonSource119) : List Nat :=
  let data := referenceData119 source
  (List.ofFn (selectorWire041 data)).map Fin.val ++
  (List.ofFn (dataWire041 data)).map Fin.val ++
  (List.ofFn (clockWire041 data)).map Fin.val ++
  (List.ofFn (orderWire041 data)).map Fin.val ++
  (List.ofFn (generatorSignalWire041 data)).map Fin.val ++
  (List.ofFn (signalWire041 data)).map Fin.val ++
  (List.ofFn (workspaceWire041 data)).map Fin.val

private theorem finiteWireList119_values_eq
    (source : AlignedCommonSource119) :
    (finiteWireList119 source).map Fin.val =
      referenceWireValues119 source := by
  simp only [finiteWireList119, referenceWireValues119,
    historyRegisterWires, List.map_append, List.map_ofFn]
  simp [Function.comp_def, finiteSelectorRegister119,
    finiteGeneratorSignalRegister119, finiteWorkspaceRegister119,
    finiteScientificHistoryDataRegister119,
    finiteScientificHistoryClockRegister119,
    finiteScientificHistoryOrderRegister119,
    finiteScientificHistorySelectorWire119,
    finiteScientificHistoryDataWire119,
    finiteScientificHistoryClockWire119,
    finiteScientificHistoryOrderWire119,
    finiteScientificHistoryGeneratorSignalWire119,
    finiteScientificHistoryDistinguishedSignalWire119,
    finiteScientificHistoryWorkspaceWire119,
    selectorWire041, dataWire041, clockWire041, orderWire041,
    generatorSignalWire041, signalWire041, workspaceWire041,
    finiteScientificHistoryDataBase119,
    finiteScientificHistorySignalBase119,
    finiteScientificHistoryStructuralPool119,
    finiteScientificHistoryClockWidth119,
    finiteScientificHistoryOrderWidth119,
    finiteScientificHistoryWorkspaceWidth119,
    finiteScientificHistoryIdleSteps119,
    semanticBase041, workspaceBase041, structuralPool041,
    workspaceWidth041, rawIdlingSteps041, rawHistoryBlocks041,
    generatorParameters041, referenceData119, referenceData041Base,
    HistoryPipelineReferenceRawValueConstructor.rawTimeSteps036,
    HistoryPipelineReferenceRawValueConstructor.rawTaylorOrder036,
    HistoryPipelineReferenceRawValueConstructor.rawOrderWidth036]

/-- The finite coordinates are pairwise distinct for arbitrary valid input.
The proof transports the established raw-wire fact by exact integer values;
the finite layout does not evaluate the raw model. -/
theorem finiteWireList119_nodup (source : AlignedCommonSource119) :
    (finiteWireList119 source).Nodup := by
  apply List.Nodup.of_map Fin.val
  rw [finiteWireList119_values_eq]
  simpa only [referenceWireValues119, List.map_append] using
    (history041_allWiresNodup (referenceData119 source)).map
      (fun (left right : Fin (qubits041 (referenceData119 source)))
        equal => Fin.ext equal)

/-- An ordinary `def` whose return-type indices depend only on finite
scientific integer data, not on `ExecutableRaw119`. -/
def finiteScientificHistoryLayout119 (source : AlignedCommonSource119) :
    HistoryBlockLayout
      (finiteScientificHistoryQubits119 source)
      source.qParameters.generatorDataWidth
      source.qParameters.generatorSignalWidth
      (historyClockWorkspaceWidth (finiteCircuitShapeParameters119 source)
        source.qParameters.generatorWorkWidth)
      (finiteCircuitShapeParameters119 source) where
  selector := finiteSelectorRegister119 source
  data := finiteScientificHistoryDataRegister119 source
  clock := finiteScientificHistoryClockRegister119 source
  order := finiteScientificHistoryOrderRegister119 source
  generatorSignal := finiteGeneratorSignalRegister119 source
  coefficientSignal := finiteScientificHistoryDistinguishedSignalWire119 source 0
  orderBoundarySignal := finiteScientificHistoryDistinguishedSignalWire119 source 1
  projectorSignal := finiteScientificHistoryDistinguishedSignalWire119 source 2
  clockBoundarySignal := finiteScientificHistoryDistinguishedSignalWire119 source 3
  workspace := finiteWorkspaceRegister119 source
  allWiresNodup := by
    change (finiteWireList119 source).Nodup
    exact finiteWireList119_nodup source

/-- The finite source-order placement of the Q child inside the history
carrier. No proof-side `ExecutableRaw119` appears in the list or its type. -/
def finiteHistoryQ10PlacedWires119 (source : AlignedCommonSource119) :
    List (Fin (finiteScientificHistoryQubits119 source)) :=
  let layout := finiteScientificHistoryLayout119 source
  historyRegisterWires layout.generatorSignal ++
  historyRegisterWires (historyGeneratorWorkRegister layout) ++
  historyRegisterWires layout.data

theorem finiteHistoryQ10PlacedWires119_length
    (source : AlignedCommonSource119) :
    (finiteHistoryQ10PlacedWires119 source).length =
      source.qParameters.ancillaWidth + source.qParameters.systemWidth := by
  simpa only [finiteHistoryQ10PlacedWires119, historyRegisterWires,
    List.length_append, List.length_ofFn, Nat.add_assoc] using
    (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
      source.qParameters).sourceWidth_eq.symm

theorem finiteHistoryQ10PlacedWires119_nodup
    (source : AlignedCommonSource119) :
    (finiteHistoryQ10PlacedWires119 source).Nodup := by
  let layout := finiteScientificHistoryLayout119 source
  let placement := historyP15Q10PlacementEvidence_ofFrozenLayout
    (layout := layout)
    (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
      source.qParameters)
  change (historyRegisterWires layout.generatorSignal ++
    historyRegisterWires (historyGeneratorWorkRegister layout) ++
    historyRegisterWires layout.data).Nodup
  rw [← historyP15Q10Placement_sourceOrder
    (layout := layout)
    (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
      source.qParameters)]
  exact List.nodup_ofFn.mpr placement.embedding.placement.injective

/-- A computable typed embedding for the controlled Q child. Its proofs are
erased; the actual placement is `List.get` on the finite source-order list. -/
def finiteHistoryQ10Embedding119 (source : AlignedCommonSource119) :
    Fin (source.qParameters.ancillaWidth + source.qParameters.systemWidth) ↪
      Fin (finiteScientificHistoryQubits119 source) :=
  wireEmbeddingOfNodupList (finiteHistoryQ10PlacedWires119 source)
    (finiteHistoryQ10PlacedWires119_length source)
    (finiteHistoryQ10PlacedWires119_nodup source)

/-- The newly computable placement is literally the placement used by the
certified layout construction; proof terms do not change the wire values. -/
theorem finiteHistoryQ10Embedding119_eq_certified
    (source : AlignedCommonSource119) :
    finiteHistoryQ10Embedding119 source =
      (historyP15Q10PlacementEvidence_ofFrozenLayout
        (layout := finiteScientificHistoryLayout119 source)
        (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
          source.qParameters)).embedding.placement := by
  rfl

/-- Executable placement evidence for the controlled Q child. The finite
embedding is built from the source-order list, while the old certificate is
used only inside an erased separation proof. -/
def finiteHistoryQ10PlacementEvidence119 (source : AlignedCommonSource119) :
    HistoryTaylorQ10PlacementEvidence
      (qubits := finiteScientificHistoryQubits119 source)
      (generatorSignalWidth := source.qParameters.generatorSignalWidth)
      (generatorWorkWidth := source.qParameters.generatorWorkWidth)
      (dataWidth := source.qParameters.generatorDataWidth)
      source.qParameters := by
  let layout := finiteScientificHistoryLayout119 source
  refine {
    widths := ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
      source.qParameters
    signal := layout.generatorSignal
    generatorWork := historyGeneratorWorkRegister layout
    data := layout.data
    activeWire := historyActiveWire layout
    compilerWork := historyControlledWork layout
    embedding := { placement := finiteHistoryQ10Embedding119 source }
    placement_sourceOrder := ?_
    control_ne_placed := ?_ }
  · change List.ofFn (finiteHistoryQ10Embedding119 source) =
      finiteHistoryQ10PlacedWires119 source
    exact wireEmbeddingOfNodupList_ofFn
      (finiteHistoryQ10PlacedWires119 source)
      (finiteHistoryQ10PlacedWires119_length source)
      (finiteHistoryQ10PlacedWires119_nodup source)
  · intro index
    let old := historyP15Q10PlacementEvidence_ofFrozenLayout
      (layout := layout)
      (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
        source.qParameters)
    change historyActiveWire layout ≠
      (finiteHistoryQ10Embedding119 source) index
    rw [finiteHistoryQ10Embedding119_eq_certified source]
    exact old.control_ne_placed index

/-- The complete control-work record is finite data with erased separation
proofs. In particular, its external placement is not obtained by executing
the noncomputable certified constructor. -/
def finiteHistoryQ10ControlEvidence119 (source : AlignedCommonSource119) :
    HistoryTaylorQ10ControlEvidence
      (qubits := finiteScientificHistoryQubits119 source)
      (generatorSignalWidth := source.qParameters.generatorSignalWidth)
      (generatorWorkWidth := source.qParameters.generatorWorkWidth)
      (dataWidth := source.qParameters.generatorDataWidth)
      source.qParameters := by
  let layout := finiteScientificHistoryLayout119 source
  refine {
    placement := finiteHistoryQ10PlacementEvidence119 source
    cleanWorkValid := {
      work₀ := (historyControlledWork layout).wire 0
      work₁ := (historyControlledWork layout).wire 1
      controlWork_eq := ?_
      work₀_ne_control := ?_
      work₁_ne_control := ?_
      work₀_ne_work₁ := ?_
      work₀_ne_placed := ?_
      work₁_ne_placed := ?_ }}
  · rfl
  · let old := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout)
      (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
        source.qParameters)
    change (historyControlledWork layout).wire 0 ≠ historyActiveWire layout
    exact old.cleanWorkValid.work₀_ne_control
  · let old := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout)
      (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
        source.qParameters)
    change (historyControlledWork layout).wire 1 ≠ historyActiveWire layout
    exact old.cleanWorkValid.work₁_ne_control
  · intro equal
    have indices := (historyControlledWork layout).injective equal
    exact Fin.zero_ne_one indices
  · intro index
    let old := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout)
      (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
        source.qParameters)
    change (historyControlledWork layout).wire 0 ≠
      (finiteHistoryQ10Embedding119 source) index
    rw [finiteHistoryQ10Embedding119_eq_certified source]
    exact old.cleanWorkValid.work₀_ne_placed index
  · intro index
    let old := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout)
      (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
        source.qParameters)
    change (historyControlledWork layout).wire 1 ≠
      (finiteHistoryQ10Embedding119 source) index
    rw [finiteHistoryQ10Embedding119_eq_certified source]
    exact old.cleanWorkValid.work₁_ne_placed index

/-- The central controlled-generator word can now be emitted directly from
the finite scientific placement without evaluating the proof-side raw type. -/
def finiteScientificControlledGenerator119 (source : AlignedCommonSource119) :
    VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate
        (finiteScientificHistoryQubits119 source)) :=
  finiteHistoryTaylorControlledGenerator119 source.qParameters
    (finiteHistoryQ10ControlEvidence119 source)

/-- The time-bound comparator's purely logical layout certificate is derived
from finite wire arithmetic. No proof-side raw record is evaluated. -/
theorem finiteClockTimeLessThanEvidence119 (source : AlignedCommonSource119) :
    HistoryTaylorLessThanEvidence
      (finiteScientificHistoryLayout119 source).clock
      (historyBoundRegister (finiteScientificHistoryLayout119 source))
      (historyBorrowRegister (finiteScientificHistoryLayout119 source))
      (historyLessThanTimeWire (finiteScientificHistoryLayout119 source)) := by
  let layout := finiteScientificHistoryLayout119 source
  refine {
    widthPositive := ?_
    lhsRhsDifferent := ?_
    lhsBorrowDifferent := ?_
    rhsBorrowDifferent := ?_
    targetLhsDifferent := ?_
    targetRhsDifferent := ?_
    targetBorrowDifferent := ?_ }
  · unfold historyClockWidth
    omega
  · intro left right
    have member := historyBoundRegister_wire_mem_workspace layout right
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨workspaceIndex, equality⟩
    change layout.clock.wire left ≠ (historyBoundRegister layout).wire right
    rw [← equality]
    exact layout.clock_wire_ne_workspace_wire left workspaceIndex
  · intro left right
    have member := historyBorrowRegister_wire_mem_workspace layout right
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨workspaceIndex, equality⟩
    change layout.clock.wire left ≠ (historyBorrowRegister layout).wire right
    rw [← equality]
    exact layout.clock_wire_ne_workspace_wire left workspaceIndex
  · intro left right equal
    change layout.workspace.wire ⟨5 + left.val, by
      unfold historyClockWorkspaceWidth historySharedPoolWidth
      unfold historyStructuralPoolWidth
      omega⟩ =
      layout.workspace.wire ⟨5 + (historyClockWidth
        (finiteCircuitShapeParameters119 source).timeSteps
        (finiteCircuitShapeParameters119 source).taylorOrder
        (finiteCircuitShapeParameters119 source).idlingSteps) + right.val, by
          unfold historyClockWorkspaceWidth historySharedPoolWidth
          unfold historyStructuralPoolWidth
          omega⟩ at equal
    have values := congrArg Fin.val (layout.workspace.injective equal)
    simp only at values
    omega
  · intro index
    have member := historyLessThanTimeWire_mem_workspace layout
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨workspaceIndex, equality⟩
    change historyLessThanTimeWire layout ≠ layout.clock.wire index
    rw [← equality]
    exact (layout.clock_wire_ne_workspace_wire index workspaceIndex).symm
  · intro index equal
    change layout.workspace.wire
        ⟨historySharedPoolWidth (finiteCircuitShapeParameters119 source)
            source.qParameters.generatorWorkWidth + 3, by
          unfold historyClockWorkspaceWidth
          omega⟩ =
      layout.workspace.wire ⟨5 + index.val, by
        unfold historyClockWorkspaceWidth historySharedPoolWidth
        unfold historyStructuralPoolWidth
        omega⟩ at equal
    have values := congrArg Fin.val (layout.workspace.injective equal)
    change historySharedPoolWidth (finiteCircuitShapeParameters119 source)
      source.qParameters.generatorWorkWidth + 3 = 5 + index.val at values
    unfold historySharedPoolWidth historyStructuralPoolWidth at values
    have hStructural := Nat.le_max_right source.qParameters.generatorWorkWidth
      (historyStructuralPoolWidth (finiteCircuitShapeParameters119 source))
    unfold historyStructuralPoolWidth at hStructural
    omega
  · intro index equal
    change layout.workspace.wire
        ⟨historySharedPoolWidth (finiteCircuitShapeParameters119 source)
            source.qParameters.generatorWorkWidth + 3, by
          unfold historyClockWorkspaceWidth
          omega⟩ =
      layout.workspace.wire ⟨5 + historyClockWidth
          (finiteCircuitShapeParameters119 source).timeSteps
          (finiteCircuitShapeParameters119 source).taylorOrder
          (finiteCircuitShapeParameters119 source).idlingSteps + index.val, by
        unfold historyClockWorkspaceWidth historySharedPoolWidth
        unfold historyStructuralPoolWidth
        omega⟩ at equal
    have values := congrArg Fin.val (layout.workspace.injective equal)
    change historySharedPoolWidth (finiteCircuitShapeParameters119 source)
      source.qParameters.generatorWorkWidth + 3 = 5 +
        historyClockWidth
          (finiteCircuitShapeParameters119 source).timeSteps
          (finiteCircuitShapeParameters119 source).taylorOrder
          (finiteCircuitShapeParameters119 source).idlingSteps + index.val at values
    unfold historySharedPoolWidth historyStructuralPoolWidth at values
    have hStructural := Nat.le_max_right source.qParameters.generatorWorkWidth
      (historyStructuralPoolWidth (finiteCircuitShapeParameters119 source))
    unfold historyStructuralPoolWidth at hStructural
    omega

/-- The second P15 clock comparator shares the same finite operand registers;
only its output wire is the next reserved workspace bit. -/
theorem finiteClockIdleEndLessThanEvidence119 (source : AlignedCommonSource119) :
    HistoryTaylorLessThanEvidence
      (finiteScientificHistoryLayout119 source).clock
      (historyBoundRegister (finiteScientificHistoryLayout119 source))
      (historyBorrowRegister (finiteScientificHistoryLayout119 source))
      (historyLessThanIdleEndWire (finiteScientificHistoryLayout119 source)) := by
  let layout := finiteScientificHistoryLayout119 source
  let timeEvidence := finiteClockTimeLessThanEvidence119 source
  refine {
    widthPositive := timeEvidence.widthPositive
    lhsRhsDifferent := timeEvidence.lhsRhsDifferent
    lhsBorrowDifferent := timeEvidence.lhsBorrowDifferent
    rhsBorrowDifferent := timeEvidence.rhsBorrowDifferent
    targetLhsDifferent := ?_
    targetRhsDifferent := ?_
    targetBorrowDifferent := ?_ }
  · intro index
    have member := historyLessThanIdleEndWire_mem_workspace layout
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨workspaceIndex, equality⟩
    change historyLessThanIdleEndWire layout ≠ layout.clock.wire index
    rw [← equality]
    exact (layout.clock_wire_ne_workspace_wire index workspaceIndex).symm
  · intro index equal
    change layout.workspace.wire
        ⟨historySharedPoolWidth (finiteCircuitShapeParameters119 source)
            source.qParameters.generatorWorkWidth + 4, by
          unfold historyClockWorkspaceWidth
          omega⟩ =
      layout.workspace.wire ⟨5 + index.val, by
        unfold historyClockWorkspaceWidth historySharedPoolWidth
        unfold historyStructuralPoolWidth
        omega⟩ at equal
    have values := congrArg Fin.val (layout.workspace.injective equal)
    change historySharedPoolWidth (finiteCircuitShapeParameters119 source)
      source.qParameters.generatorWorkWidth + 4 = 5 + index.val at values
    unfold historySharedPoolWidth historyStructuralPoolWidth at values
    have hStructural := Nat.le_max_right source.qParameters.generatorWorkWidth
      (historyStructuralPoolWidth (finiteCircuitShapeParameters119 source))
    unfold historyStructuralPoolWidth at hStructural
    omega
  · intro index equal
    change layout.workspace.wire
        ⟨historySharedPoolWidth (finiteCircuitShapeParameters119 source)
            source.qParameters.generatorWorkWidth + 4, by
          unfold historyClockWorkspaceWidth
          omega⟩ =
      layout.workspace.wire ⟨5 + historyClockWidth
          (finiteCircuitShapeParameters119 source).timeSteps
          (finiteCircuitShapeParameters119 source).taylorOrder
          (finiteCircuitShapeParameters119 source).idlingSteps + index.val, by
        unfold historyClockWorkspaceWidth historySharedPoolWidth
        unfold historyStructuralPoolWidth
        omega⟩ at equal
    have values := congrArg Fin.val (layout.workspace.injective equal)
    change historySharedPoolWidth (finiteCircuitShapeParameters119 source)
      source.qParameters.generatorWorkWidth + 4 = 5 +
        historyClockWidth
          (finiteCircuitShapeParameters119 source).timeSteps
          (finiteCircuitShapeParameters119 source).taylorOrder
          (finiteCircuitShapeParameters119 source).idlingSteps + index.val at values
    unfold historySharedPoolWidth historyStructuralPoolWidth at values
    have hStructural := Nat.le_max_right source.qParameters.generatorWorkWidth
      (historyStructuralPoolWidth (finiteCircuitShapeParameters119 source))
    unfold historyStructuralPoolWidth at hStructural
    omega

/-- Both clock predicates are executable comparison layouts. All disjointness
proofs are erased; the operand and target wires are finite source functions. -/
def finiteClockTimeComparison119 (source : AlignedCommonSource119) :
    UnsignedLessThanXorSpec
      (finiteScientificHistoryQubits119 source)
      (historyClockWidth
        (finiteCircuitShapeParameters119 source).timeSteps
        (finiteCircuitShapeParameters119 source).taylorOrder
        (finiteCircuitShapeParameters119 source).idlingSteps) :=
  (finiteClockTimeLessThanEvidence119 source).toSpec

def finiteClockIdleEndComparison119 (source : AlignedCommonSource119) :
    UnsignedLessThanXorSpec
      (finiteScientificHistoryQubits119 source)
      (historyClockWidth
        (finiteCircuitShapeParameters119 source).timeSteps
        (finiteCircuitShapeParameters119 source).taylorOrder
        (finiteCircuitShapeParameters119 source).idlingSteps) :=
  (finiteClockIdleEndLessThanEvidence119 source).toSpec

/-- The four pre-generator P15 calls, including both comparison words, are
emitted from finite scientific coordinates and integer bounds alone. -/
def finiteScientificTaylorBefore119 (source : AlignedCommonSource119) :
    List (VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate
        (finiteScientificHistoryQubits119 source))) :=
  let layout := finiteScientificHistoryLayout119 source
  [finiteMinimumWorkEquality119 (historyRegisterWires layout.selector) [] 1
      (historyBranchWire layout),
    finiteLessThanConstantCircuit119 (finiteClockTimeComparison119 source)
      source.historyParameters.physicalClocks,
    finiteLessThanConstantCircuit119 (finiteClockIdleEndComparison119 source)
      (historyIdleClockEnd source.historyParameters.physicalClocks
        source.historyParameters.taylorOrder
        (finiteScientificHistoryIdleSteps119 source)),
    finiteMinimumWorkConjunction119
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyActiveWire layout)]

/-- The generic P15 source-order proof supplies only erased inequalities;
the order, mask and output wires remain the finite layout projections. -/
theorem finiteDegreeOrderLessThanEvidence119
    (source : AlignedCommonSource119) :
    HistoryTaylorLessThanEvidence
      (finiteScientificHistoryLayout119 source).order
      (historyOrderBoundRegister (finiteScientificHistoryLayout119 source))
      (historyOrderMaskedConstantRegister
        (finiteScientificHistoryLayout119 source))
      (historyEqualityFlag (finiteScientificHistoryLayout119 source)) := by
  let layout := finiteScientificHistoryLayout119 source
  let spec := providerIntegration_orderBoundaryLessThanSpec layout
  exact {
    widthPositive := spec.widthPositive
    lhsRhsDifferent := spec.lhsRhsDifferent
    lhsBorrowDifferent := spec.lhsBorrowDifferent
    rhsBorrowDifferent := spec.rhsBorrowDifferent
    targetLhsDifferent := spec.targetLhsDifferent
    targetRhsDifferent := spec.targetRhsDifferent
    targetBorrowDifferent := spec.targetBorrowDifferent }

theorem finiteDegreeIncrementEvidence119
    (source : AlignedCommonSource119) :
    HistoryTaylorDegreeIncrementEvidence
      (finiteScientificHistoryLayout119 source) := by
  let layout := finiteScientificHistoryLayout119 source
  let spec := providerIntegration_degreeIncrementSpec layout
  exact {
    addend_accumulator_disjoint := spec.addend_accumulator_disjoint
    carry_ne_addend := spec.carry_ne_addend
    carry_ne_accumulator := spec.carry_ne_accumulator
    control_ne_addend := spec.control_ne_addend
    control_ne_accumulator := spec.control_ne_accumulator
    control_ne_carry := spec.control_ne_carry }

/-- The four live P15 control wires occupy distinct finite workspace slots. -/
private def finiteLiveRoleWire119 (source : AlignedCommonSource119) :
    Fin 4 → Fin (finiteScientificHistoryQubits119 source) := fun index =>
  let layout := finiteScientificHistoryLayout119 source
  layout.workspace.wire ⟨historySharedPoolWidth
      (finiteCircuitShapeParameters119 source)
      source.qParameters.generatorWorkWidth + 2 + index.val, by
    unfold historyClockWorkspaceWidth
    omega⟩

private theorem finiteLiveRoleWire119_injective (source : AlignedCommonSource119) :
    Function.Injective (finiteLiveRoleWire119 source) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val
    ((finiteScientificHistoryLayout119 source).workspace.injective equal)
  dsimp [finiteLiveRoleWire119] at values
  omega

private theorem finiteWorkspaceNeReserved119
    (source : AlignedCommonSource119)
    (wire : Fin (finiteScientificHistoryQubits119 source))
    (wireMem : wire ∈ historyRegisterWires
      (finiteScientificHistoryLayout119 source).workspace)
    (signal : Fin (finiteScientificHistoryQubits119 source))
    (signalMem : signal ∈
      [(finiteScientificHistoryLayout119 source).coefficientSignal,
        (finiteScientificHistoryLayout119 source).orderBoundarySignal]) :
    wire ≠ signal := by
  let layout := finiteScientificHistoryLayout119 source
  simp only [historyRegisterWires, List.mem_ofFn] at wireMem
  rcases wireMem with ⟨workspaceIndex, rfl⟩
  exact (layout.postGeneratorSignal_separated signal signalMem).2.2
    workspaceIndex

/-- Full P15 L2 evidence from finite layout and rational scientific angles.
Its proof fields erase; the two angle fields remain computable data. -/
def finiteHistoryTaylorL2Evidence119 (source : AlignedCommonSource119) :
    HistoryTaylorL2Evidence
      (finiteScientificHistoryLayout119 source) := by
  let layout := finiteScientificHistoryLayout119 source
  refine {
    clockTimeLessThan := finiteClockTimeLessThanEvidence119 source
    clockIdleEndLessThan := finiteClockIdleEndLessThanEvidence119 source
    degreeOrderLessThan := finiteDegreeOrderLessThanEvidence119 source
    degreeIncrement := finiteDegreeIncrementEvidence119 source
    branch_ne_ltIdleEnd := ?_
    branch_ne_coefficientSignal := ?_
    ltIdleEnd_ne_coefficientSignal := ?_
    active_ne_equality := ?_
    active_ne_orderBoundary := ?_
    equality_ne_orderBoundary := ?_
    ltIdleEnd_ne_idle := ?_
    ltTime_ne_idle := ?_
    active_ne_coefficientSignal := ?_
    coefficientControl_ne_coefficientSignal := ?_
    coefficientAngles := fun index =>
      ExecutableHistoryFiniteScientificAngles.correctedCoefficient source index.val
    idleCoefficientAngle :=
      ExecutableHistoryFiniteScientificAngles.idleCoefficient }
  · change finiteLiveRoleWire119 source 0 ≠ finiteLiveRoleWire119 source 2
    intro equality
    have := finiteLiveRoleWire119_injective source equality
    exact (by decide : (0 : Fin 4) ≠ 2) this
  · exact finiteWorkspaceNeReserved119 source _
      (historyBranchWire_mem_workspace layout) _ (by simp)
  · exact finiteWorkspaceNeReserved119 source _
      (historyLessThanIdleEndWire_mem_workspace layout) _ (by simp)
  · intro equality
    change layout.workspace.wire _ = layout.workspace.wire _ at equality
    have values := congrArg Fin.val (layout.workspace.injective equality)
    dsimp [historyActiveWire, historyEqualityFlag,
      historyWorkspaceSlice] at values
    omega
  · exact finiteWorkspaceNeReserved119 source _
      (historyActiveWire_mem_workspace layout) _ (by simp)
  · have member : historyEqualityFlag layout ∈
        historyRegisterWires layout.workspace := by
      unfold historyEqualityFlag
      apply historyWorkspaceSlice_wire_mem
    exact finiteWorkspaceNeReserved119 source _ member _ (by simp)

  · intro equality
    change layout.workspace.wire _ = layout.workspace.wire _ at equality
    have values := congrArg Fin.val (layout.workspace.injective equality)
    dsimp [historyLessThanIdleEndWire, historyIdleFlag,
      historyWorkspaceSlice] at values
    have hStructural := Nat.le_max_right source.qParameters.generatorWorkWidth
      (historyStructuralPoolWidth (finiteCircuitShapeParameters119 source))
    unfold historySharedPoolWidth historyStructuralPoolWidth at values
    unfold historyStructuralPoolWidth at hStructural
    omega
  · intro equality
    change layout.workspace.wire _ = layout.workspace.wire _ at equality
    have values := congrArg Fin.val (layout.workspace.injective equality)
    dsimp [historyLessThanTimeWire, historyIdleFlag,
      historyWorkspaceSlice] at values
    have hStructural := Nat.le_max_right source.qParameters.generatorWorkWidth
      (historyStructuralPoolWidth (finiteCircuitShapeParameters119 source))
    unfold historySharedPoolWidth historyStructuralPoolWidth at values
    unfold historyStructuralPoolWidth at hStructural
    omega
  · exact finiteWorkspaceNeReserved119 source _
      (historyActiveWire_mem_workspace layout) _ (by simp)
  · have member : historyCoefficientControl layout ∈
        historyRegisterWires layout.workspace := by
      unfold historyCoefficientControl
      apply historyWorkspaceSlice_wire_mem
    exact finiteWorkspaceNeReserved119 source _ member _ (by simp)

/-- The suffix of the P15 history word, including degree updates and
scientific coefficient rotations, is emitted without a proof-side `choose`. -/
def finiteScientificTaylorAfter119 (source : AlignedCommonSource119) :
    List (VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate
        (finiteScientificHistoryQubits119 source))) :=
  finiteHistoryTaylorAfter119 (finiteScientificHistoryLayout119 source)
    (finiteHistoryTaylorL2Evidence119 source)
    (fun index =>
      ExecutableHistoryFiniteScientificAngles.correctedCoefficient
        source index.val)
    ExecutableHistoryFiniteScientificAngles.idleCoefficient

/-- Complete finite P15 primitive word, assembled from the same proof-erased
layout and angle values used by the earlier certified prefix. -/
def finiteScientificTaylorCircuit119 (source : AlignedCommonSource119) :
    VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate
        (finiteScientificHistoryQubits119 source)) :=
  VerifiedCircuitCore.Circuit.sequence
    (finiteScientificTaylorBefore119 source ++
      [finiteScientificControlledGenerator119 source] ++
      finiteScientificTaylorAfter119 source)

/-- Every reserved H3 signal is outside the finite workspace. -/
private theorem finiteWorkspaceNeAnyReserved119
    (source : AlignedCommonSource119)
    (wire : Fin (finiteScientificHistoryQubits119 source))
    (wireMem : wire ∈ historyRegisterWires
      (finiteScientificHistoryLayout119 source).workspace)
    (signal : Fin (finiteScientificHistoryQubits119 source))
    (signalMem : signal ∈
      [(finiteScientificHistoryLayout119 source).coefficientSignal,
        (finiteScientificHistoryLayout119 source).orderBoundarySignal,
        (finiteScientificHistoryLayout119 source).projectorSignal,
        (finiteScientificHistoryLayout119 source).clockBoundarySignal]) :
    wire ≠ signal := by
  let layout := finiteScientificHistoryLayout119 source
  have split := List.nodup_append.mp layout.allWiresNodup
  have signalMem' : signal ∈
      [layout.coefficientSignal, layout.orderBoundarySignal,
        layout.projectorSignal, layout.clockBoundarySignal] := by
    simpa only [layout] using signalMem
  have prefixMem : signal ∈
      historyRegisterWires layout.selector ++
      historyRegisterWires layout.data ++
      historyRegisterWires layout.clock ++
      historyRegisterWires layout.order ++
      historyRegisterWires layout.generatorSignal ++
      [layout.coefficientSignal, layout.orderBoundarySignal,
        layout.projectorSignal, layout.clockBoundarySignal] := by
    simp only [List.mem_append]
    exact Or.inr signalMem'
  exact (split.2.2 _ prefixMem _ wireMem).symm

theorem finiteWorkspaceNeOrder119
    (source : AlignedCommonSource119)
    (wire : Fin (finiteScientificHistoryQubits119 source))
    (wireMem : wire ∈ historyRegisterWires
      (finiteScientificHistoryLayout119 source).workspace)
    (index : Fin (historyOrderWidth source.historyParameters.taylorOrder)) :
    wire ≠ (finiteScientificHistoryLayout119 source).order.wire index := by
  let layout := finiteScientificHistoryLayout119 source
  simp only [historyRegisterWires, List.mem_ofFn] at wireMem
  rcases wireMem with ⟨workspaceIndex, rfl⟩
  exact (layout.orderWire_separated index).2.2.2 workspaceIndex |>.symm

/-- H3 projector controls need no extra caller-provided wire assumptions. -/
theorem finiteH3ProjectorEvidence119 (source : AlignedCommonSource119) :
    HistoryProjectorControlEvidence
      (finiteScientificHistoryLayout119 source) := by
  let layout := finiteScientificHistoryLayout119 source
  exact {
    branch_ne_projector := finiteWorkspaceNeAnyReserved119 source _
      (historyBranchWire_mem_workspace layout) _ (by simp)
    coefficientControl_ne_projector := finiteWorkspaceNeAnyReserved119 source _
      (by unfold historyCoefficientControl; apply historyWorkspaceSlice_wire_mem)
      _ (by simp) }

/-- H3 idle transform disjointness follows from the finite P15 layout. -/
theorem finiteH3IdleTransformEvidence119 (source : AlignedCommonSource119) :
    HistoryIdleTransformEvidence
      (finiteScientificHistoryLayout119 source) := by
  let layout := finiteScientificHistoryLayout119 source
  exact {
    idleEnd_ne_idle :=
      (finiteHistoryTaylorL2Evidence119 source).ltIdleEnd_ne_idle
    time_ne_idle := (finiteHistoryTaylorL2Evidence119 source).ltTime_ne_idle
    active_ne_order := by
      intro target targetMem
      simp only [historyRegisterWires, List.mem_ofFn] at targetMem
      rcases targetMem with ⟨index, rfl⟩
      exact finiteWorkspaceNeOrder119 source _
        (historyActiveWire_mem_workspace layout) index
    active_ne_coefficient :=
      (finiteHistoryTaylorL2Evidence119 source).active_ne_coefficientSignal }

end ExecutableHistoryFiniteScientificLayout
