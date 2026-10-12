import QLean.History.Implementation.HistoryPipelineH3ActiveProduct
import QLean.History.Implementation.HistoryPipelineH2OrderTransport
import QLean.History.Implementation.HistoryPipelineH2TerminalEntry

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput
open HistoryPipelineReferenceRawValueConstructor
open HistoryPipelineReferenceRawValueConstructorV3
open HistoryPipelineReferenceAdmissibility041

noncomputable section

def h3OrderZeroIndex119
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source) : OldHistoryIndex119 source where
  clock := index.clock
  state := {
    label := ⟨0, source.historyWellFormed.binaryLabels_pos⟩
    configuration := index.state.configuration }

@[simp] theorem h3OrderZeroIndex119_clock
    (source : AlignedCommonSource119) (index : OldHistoryIndex119 source) :
    (h3OrderZeroIndex119 source index).clock = index.clock := rfl

@[simp] theorem h3OrderZeroIndex119_label
    (source : AlignedCommonSource119) (index : OldHistoryIndex119 source) :
    (h3OrderZeroIndex119 source index).state.label.val = 0 := rfl

@[simp] theorem h3OrderZeroIndex119_configuration
    (source : AlignedCommonSource119) (index : OldHistoryIndex119 source) :
    (h3OrderZeroIndex119 source index).state.configuration =
      index.state.configuration := rfl

theorem executableHistoryBasis119_orderZero_outside_order
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (outside : ∀ orderIndex,
      (ExecutableLayout119 source domain).order.wire orderIndex ≠ wire) :
    executableHistoryBasis119 source domain fits
        (h3OrderZeroIndex119 source index) wire =
      executableHistoryBasis119 source domain fits index wire := by
  have clockBitsEqual :
      clockBits119 source fits (h3OrderZeroIndex119 source index) =
        clockBits119 source fits index := by
    funext bit
    rfl
  unfold executableHistoryBasis119
  rw [clockBitsEqual]
  simp [h3OrderZeroIndex119, writeRegisterBits, outside]

theorem correctedBranchHistoryBasis119_orderZero_outside_order
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (outside : ∀ orderIndex,
      (ExecutableLayout119 source domain).order.wire orderIndex ≠ wire) :
    correctedBranchHistoryBasis119 source domain fits branch
        (h3OrderZeroIndex119 source index) wire =
      correctedBranchHistoryBasis119 source domain fits branch index wire := by
  by_cases selectorMember : wire ∈
      historyRegisterWires (ExecutableLayout119 source domain).selector
  · simp only [historyRegisterWires, List.mem_ofFn] at selectorMember
    rcases selectorMember with ⟨selectorIndex, rfl⟩
    have left := congrFun
      (correctedBranchHistoryBasis119_restrict_selector source domain fits branch
        (h3OrderZeroIndex119 source index)) selectorIndex
    have right := congrFun
      (correctedBranchHistoryBasis119_restrict_selector source domain fits branch
        index) selectorIndex
    exact left.trans right.symm
  · rw [correctedBranchHistoryBasis119_apply_of_not_selector,
      correctedBranchHistoryBasis119_apply_of_not_selector]
    · exact executableHistoryBasis119_orderZero_outside_order
        source domain fits index wire outside
    · exact selectorMember
    · exact selectorMember

theorem writeRegisterValue_correctedBranchHistoryBasis119_orderZero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    writeRegisterValue (ExecutableLayout119 source domain).order 0
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      correctedBranchHistoryBasis119 source domain fits branch
        (h3OrderZeroIndex119 source index) := by
  funext wire
  by_cases inside : ∃ orderIndex,
      (ExecutableLayout119 source domain).order.wire orderIndex = wire
  · rcases inside with ⟨orderIndex, rfl⟩
    rw [writeRegisterValue_apply_wire]
    have readZero := congrFun
      (correctedBranchHistoryBasis119_read_order source domain fits branch
        (h3OrderZeroIndex119 source index)) orderIndex
    change Nat.testBit 0 orderIndex.val =
      (ExecutableLayout119 source domain).order.read
        (correctedBranchHistoryBasis119 source domain fits branch
          (h3OrderZeroIndex119 source index)) orderIndex
    rw [readZero]
    rfl
  · rw [writeRegisterValue_apply_outside]
    · exact (correctedBranchHistoryBasis119_orderZero_outside_order
        source domain fits branch index wire
        (fun orderIndex equal => inside ⟨orderIndex, equal⟩)).symm
    · intro orderIndex equal
      exact inside ⟨orderIndex, equal⟩

theorem h3AfterSelector119_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    h3AfterSelector119 layout (writeRegisterValue layout.order value input) =
      writeRegisterValue layout.order value (h3AfterSelector119 layout input) := by
  unfold h3AfterSelector119
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [littleEndianRegisterEqualsNat_write_order119]
  exact (writeRegisterValue_xorWire_commute119 layout.order
    (historyBranchWire layout) (by
      intro orderIndex
      have member := historyBranchWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      intro equal
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm))
    value _ input).symm

theorem h3AfterIdleEnd119_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    h3AfterIdleEnd119 layout (writeRegisterValue layout.order value input) =
      writeRegisterValue layout.order value (h3AfterIdleEnd119 layout input) := by
  unfold h3AfterIdleEnd119 h3AfterTime119
  rw [h3AfterSelector119_write_order119,
    historyTaylorTimeComparisonBasisAction_write_order119,
    historyTaylorIdleEndComparisonBasisAction_write_order119]

theorem historyTaylorActiveConjunctionBasisAction_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    historyTaylorActiveConjunctionBasisAction layout
        (writeRegisterValue layout.order value input) =
      writeRegisterValue layout.order value
        (historyTaylorActiveConjunctionBasisAction layout input) := by
  have branchStable : writeRegisterValue layout.order value input
      (historyBranchWire layout) = input (historyBranchWire layout) :=
    writeRegisterValue_apply_outside layout.order value input _ (by
      intro orderIndex equal
      have member := historyBranchWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm))
  have timeStable : writeRegisterValue layout.order value input
      (historyLessThanTimeWire layout) = input (historyLessThanTimeWire layout) :=
    writeRegisterValue_apply_outside layout.order value input _ (by
      intro orderIndex equal
      have member := historyLessThanTimeWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm))
  unfold historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
    ClassicalReversibleStage.allWiresTrue
    ClassicalReversibleStage.readWires
  simp only [List.map, List.all, id_eq, Bool.and_true]
  rw [branchStable, timeStable]
  exact (writeRegisterValue_xorWire_commute119 layout.order
    (historyActiveWire layout) (by
      intro orderIndex
      have member := historyActiveWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      intro equal
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm)) value _ input).symm

theorem h3BeforeUniform119_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    h3BeforeUniform119 layout (writeRegisterValue layout.order value input) =
      writeRegisterValue layout.order value (h3BeforeUniform119 layout input) := by
  unfold h3BeforeUniform119
  rw [h3AfterIdleEnd119_write_order119,
    historyTaylorActiveConjunctionBasisAction_write_order119]

theorem h3ZeroOrder119_before_eq_orderZeroIndex
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    h3ZeroOrder119 layout (h3BeforeUniform119 layout logical) =
      h3BeforeUniform119 layout
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          (h3OrderZeroIndex119 source index)) := by
  dsimp only
  unfold h3ZeroOrder119
  rw [← h3BeforeUniform119_write_order119]
  rw [writeRegisterValue_correctedBranchHistoryBasis119_orderZero]

theorem executableHistoryBasis119_clockNext_outside_clock
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (outside : ∀ clockIndex,
      (ExecutableLayout119 source domain).clock.wire clockIndex ≠ wire) :
    executableHistoryBasis119 source domain fits
        (h3ActiveOutputIndex119 source index clockNext) wire =
      executableHistoryBasis119 source domain fits
        (h3OrderZeroIndex119 source index) wire := by
  have orderBitsEqual :
      orderBits119 source fits
          (h3ActiveOutputIndex119 source index clockNext) =
        orderBits119 source fits (h3OrderZeroIndex119 source index) := by
    funext bit
    rfl
  unfold executableHistoryBasis119
  rw [orderBitsEqual]
  simp [h3ActiveOutputIndex119, h3OrderZeroIndex119,
    writeRegisterBits, outside]

private def h3SelectorTailWires119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    List (Fin qubits) :=
  historyRegisterWires layout.data ++ historyRegisterWires layout.clock ++
    historyRegisterWires layout.order ++ historyRegisterWires layout.generatorSignal ++
    [layout.coefficientSignal, layout.orderBoundarySignal,
      layout.projectorSignal, layout.clockBoundarySignal] ++
    historyRegisterWires layout.workspace

private theorem h3SelectorWire_ne_clock119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (selectorIndex : Fin 2)
    (clockIndex : Fin (historyClockWidth parameters.timeSteps
      parameters.taylorOrder parameters.idlingSteps)) :
    layout.selector.wire selectorIndex ≠ layout.clock.wire clockIndex := by
  have normalized :
      (historyRegisterWires layout.selector ++
        h3SelectorTailWires119 layout).Nodup := by
    simpa [h3SelectorTailWires119, List.append_assoc] using
      layout.allWiresNodup
  have split := List.nodup_append.mp normalized
  exact split.2.2 _ (List.mem_ofFn.mpr ⟨selectorIndex, rfl⟩) _ (by
    simp [h3SelectorTailWires119, historyRegisterWires])

theorem correctedBranchHistoryBasis119_clockNext_outside_clock
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (outside : ∀ clockIndex,
      (ExecutableLayout119 source domain).clock.wire clockIndex ≠ wire) :
    correctedBranchHistoryBasis119 source domain fits branch
        (h3ActiveOutputIndex119 source index clockNext) wire =
      correctedBranchHistoryBasis119 source domain fits branch
        (h3OrderZeroIndex119 source index) wire := by
  by_cases selectorMember : wire ∈
      historyRegisterWires (ExecutableLayout119 source domain).selector
  · simp only [historyRegisterWires, List.mem_ofFn] at selectorMember
    rcases selectorMember with ⟨selectorIndex, rfl⟩
    have left := congrFun
      (correctedBranchHistoryBasis119_restrict_selector source domain fits branch
        (h3ActiveOutputIndex119 source index clockNext)) selectorIndex
    have right := congrFun
      (correctedBranchHistoryBasis119_restrict_selector source domain fits branch
        (h3OrderZeroIndex119 source index)) selectorIndex
    exact left.trans right.symm
  · rw [correctedBranchHistoryBasis119_apply_of_not_selector,
      correctedBranchHistoryBasis119_apply_of_not_selector]
    · exact executableHistoryBasis119_clockNext_outside_clock
        source domain fits index clockNext wire outside
    · exact selectorMember
    · exact selectorMember

theorem writeRegisterValue_correctedBranchHistoryBasis119_clockNext
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    writeRegisterValue (ExecutableLayout119 source domain).clock
        (index.clock.val + 1)
        (correctedBranchHistoryBasis119 source domain fits branch
          (h3OrderZeroIndex119 source index)) =
      correctedBranchHistoryBasis119 source domain fits branch
        (h3ActiveOutputIndex119 source index clockNext) := by
  funext wire
  by_cases inside : ∃ clockIndex,
      (ExecutableLayout119 source domain).clock.wire clockIndex = wire
  · rcases inside with ⟨clockIndex, rfl⟩
    rw [writeRegisterValue_apply_wire]
    have readNext := congrFun
      (correctedBranchHistoryBasis119_read_clock source domain fits branch
        (h3ActiveOutputIndex119 source index clockNext)) clockIndex
    change Nat.testBit (index.clock.val + 1) clockIndex.val =
      (ExecutableLayout119 source domain).clock.read
        (correctedBranchHistoryBasis119 source domain fits branch
          (h3ActiveOutputIndex119 source index clockNext)) clockIndex
    rw [readNext]
    rfl
  · rw [writeRegisterValue_apply_outside]
    · exact (correctedBranchHistoryBasis119_clockNext_outside_clock
        source domain fits branch index clockNext wire
        (fun clockIndex equal => inside ⟨clockIndex, equal⟩)).symm
    · intro clockIndex equal
      exact inside ⟨clockIndex, equal⟩

theorem h3AfterSelector119_write_clock119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    h3AfterSelector119 layout (writeRegisterValue layout.clock value input) =
      writeRegisterValue layout.clock value (h3AfterSelector119 layout input) := by
  unfold h3AfterSelector119
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  have selectorStable :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 2
          (writeRegisterValue layout.clock value input) =
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 2 input := by
    apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
    intro wire member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨selectorIndex, rfl⟩
    exact writeRegisterValue_apply_outside layout.clock value input _ (by
      intro clockIndex equal
      exact h3SelectorWire_ne_clock119 layout selectorIndex clockIndex equal.symm)
  rw [selectorStable]
  exact (writeRegisterValue_xorWire_commute119 layout.clock
    (historyBranchWire layout) (by
      intro clockIndex
      have member := historyBranchWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      intro equal
      exact layout.clock_wire_ne_workspace_wire clockIndex workspaceIndex
        (equal.trans member.symm))
    value _ input).symm

theorem h3AfterSelector119_clock_read
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    layout.clock.read (h3AfterSelector119 layout input) =
      layout.clock.read input := by
  funext clockIndex
  unfold h3AfterSelector119
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  change xorWire (historyBranchWire layout)
      (ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 2 input) input
      (layout.clock.wire clockIndex) = input (layout.clock.wire clockIndex)
  rw [xorWire_apply_other]
  intro equal
  have member := historyBranchWire_mem_workspace layout
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
  exact layout.clock_wire_ne_workspace_wire clockIndex workspaceIndex
    (equal.trans member.symm)

theorem h3AfterSelector119_order_read
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    layout.order.read (h3AfterSelector119 layout input) =
      layout.order.read input := by
  funext orderIndex
  unfold h3AfterSelector119
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  change xorWire (historyBranchWire layout)
      (ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 2 input) input
      (layout.order.wire orderIndex) = input (layout.order.wire orderIndex)
  rw [xorWire_apply_other]
  intro equal
  have member := historyBranchWire_mem_workspace layout
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
  exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
    (equal.trans member.symm)

theorem h3AfterSelector119_involutive
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    h3AfterSelector119 layout (h3AfterSelector119 layout input) = input := by
  have selectorStable :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 2
          (h3AfterSelector119 layout input) =
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 2 input := by
    apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
    intro wire member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨selectorIndex, rfl⟩
    unfold h3AfterSelector119
      ClassicalReversibleStage.equalityToConstantDirectBasisAction
    rw [xorWire_apply_other]
    intro equal
    have branchMember := historyBranchWire_mem_workspace layout
    rcases List.mem_ofFn.mp branchMember with ⟨workspaceIndex, branchEq⟩
    exact layout.selector_wire_ne_workspace_wire selectorIndex workspaceIndex
      (equal.trans branchEq.symm)
  unfold h3AfterSelector119 at selectorStable
  unfold ClassicalReversibleStage.equalityToConstantDirectBasisAction at selectorStable
  unfold h3AfterSelector119
  unfold ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [selectorStable]
  funext wire
  simp [xorWire]

theorem h3ActiveTailBasisAction119_expected_eq_logical
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let expected := h3ZeroOrder119 layout
      (h3BeforeUniform119 layout logical)
    h3ActiveTailBasisAction119 source domain expected =
      correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
        (h3ActiveOutputIndex119 source index clockNext) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let zeroIndex := h3OrderZeroIndex119 source index
  let zeroLogical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 zeroIndex
  let output := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 (h3ActiveOutputIndex119 source index clockNext)
  let expected := h3ZeroOrder119 layout
    (h3BeforeUniform119 layout
      (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119 index))
  have expectedEq : expected = h3BeforeUniform119 layout zeroLogical := by
    exact h3ZeroOrder119_before_eq_orderZeroIndex source domain fits index
  have activeStep : historyTaylorActiveConjunctionBasisAction layout expected =
      h3AfterIdleEnd119 layout zeroLogical := by
    rw [expectedEq]
    unfold h3BeforeUniform119
    exact historyTaylorActiveConjunctionBasisAction_involutive119 layout
      (h3AfterIdleEnd119 layout zeroLogical)
  have idleRestore : historyTaylorIdleEndComparisonBasisAction layout
      (historyTaylorActiveConjunctionBasisAction layout expected) =
        h3AfterTime119 layout zeroLogical := by
    rw [activeStep]
    unfold h3AfterIdleEnd119
    exact historyTaylorIdleEndComparisonBasisAction_involutive119 layout
      (h3AfterTime119 layout zeroLogical)
  have timeRestore : historyTaylorTimeComparisonBasisAction layout
      (historyTaylorIdleEndComparisonBasisAction layout
        (historyTaylorActiveConjunctionBasisAction layout expected)) =
          h3AfterSelector119 layout zeroLogical := by
    rw [idleRestore]
    unfold h3AfterTime119
    exact historyTaylorTimeComparisonBasisAction_involutive119 layout
      (h3AfterSelector119 layout zeroLogical)
  let afterSelector := h3AfterSelector119 layout zeroLogical
  have branchTrue : afterSelector (historyBranchWire layout) = true := by
    exact h3AfterSelector119_selected_branch_true source domain fits zeroIndex
  have orderZero : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order) 0 afterSelector = true := by
    calc
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 afterSelector =
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 zeroLogical := by
            apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
            intro wire member
            simp only [historyRegisterWires, List.mem_ofFn] at member
            rcases member with ⟨orderIndex, rfl⟩
            exact congrFun (h3AfterSelector119_order_read layout zeroLogical)
              orderIndex
      _ = true := by
        exact correctedBranchHistoryBasis119_order_equals source domain fits
          h3SelectedBranch119 zeroIndex 0 (by
            have positive : 0 < 2 ^ historyOrderWidth
                source.historyParameters.taylorOrder :=
              lt_of_lt_of_le source.historyWellFormed.binaryLabels_pos
                fits.label_fits
            have taylorOrderEq :
                (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
                  (ExecutableAdmissible119 source domain).analytic).taylorOrder =
                  source.historyParameters.taylorOrder := by rfl
            have orderWidthEq :
                (historyRegisterWires layout.order).length =
                  historyOrderWidth source.historyParameters.taylorOrder := by
              simp [historyRegisterWires, layout, taylorOrderEq]
            rw [orderWidthEq]
            exact positive)
  have projectorStep : h3I06BasisAction layout afterSelector = afterSelector := by
    funext wire
    simp [h3I06BasisAction, h3I06ProjectorPredicate, branchTrue, orderZero,
      xorWire]
  let clockSpec := historyControlledClockIncrementSpec layout
    (ExecutableClockEvidence119 source domain).controlledIncrement
  have clockControl : afterSelector clockSpec.control = true := by
    exact branchTrue
  have clockValue : registerValue clockSpec.accumulator afterSelector =
      index.clock.val := by
    change registerValue layout.clock afterSelector = index.clock.val
    unfold registerValue
    rw [h3AfterSelector119_clock_read]
    rw [correctedBranchHistoryBasis119_read_clock]
    dsimp [zeroLogical, zeroIndex, h3OrderZeroIndex119, clockBits119]
    exact qubitBasisLittleEndianIndex_basis _
  have tailWidthEq :
      historyClockTailWidth
          (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic) + 1 =
        historyClockWidth source.historyParameters.physicalClocks
          source.historyParameters.taylorOrder
          (source.historyBlocks *
            historyIdleBlockSize source.historyParameters.taylorOrder - 1) := by
    have blockWidthEq :
        historyClockWidth
            (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
              (ExecutableAdmissible119 source domain).analytic).timeSteps
            (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
              (ExecutableAdmissible119 source domain).analytic).taylorOrder
            (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
              (ExecutableAdmissible119 source domain).analytic).idlingSteps =
          historyClockWidth source.historyParameters.physicalClocks
            source.historyParameters.taylorOrder
            (source.historyBlocks *
              historyIdleBlockSize source.historyParameters.taylorOrder - 1) := by
      change historyClockWidth
          (rawTimeSteps036 (referenceData041Base (referenceData119 source)))
          (rawTaylorOrder036 (referenceData041Base (referenceData119 source)))
          (rawIdlingSteps041 (referenceData119 source)) = _
      exact executable_historyClockWidth_eq119 source
    unfold historyClockTailWidth
    rw [blockWidthEq]
    have widthPositive : 0 < historyClockWidth
        source.historyParameters.physicalClocks
        source.historyParameters.taylorOrder
        (source.historyBlocks *
          historyIdleBlockSize source.historyParameters.taylorOrder - 1) := by
      unfold historyClockWidth
      positivity
    omega
  have clockFits : index.clock.val + 1 <
      2 ^ (historyClockTailWidth
        (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
          (ExecutableAdmissible119 source domain).analytic) + 1) := by
    rw [tailWidthEq]
    exact lt_trans clockNext fits.clock_fits
  have clockStep : controlledAddConstantMod2PowBasisAction clockSpec
      afterSelector = writeRegisterValue layout.clock (index.clock.val + 1)
        afterSelector := by
    unfold controlledAddConstantMod2PowBasisAction
    rw [if_pos clockControl, clockValue]
    change writeRegisterValue layout.clock
      ((index.clock.val + 1) %
        2 ^ (historyClockTailWidth
          (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic) + 1))
      afterSelector = _
    rw [Nat.mod_eq_of_lt clockFits]
  have clockToOutput : writeRegisterValue layout.clock
      (index.clock.val + 1) afterSelector = h3AfterSelector119 layout output := by
    unfold afterSelector output
    rw [← h3AfterSelector119_write_clock119]
    rw [writeRegisterValue_correctedBranchHistoryBasis119_clockNext]
  unfold h3ActiveTailBasisAction119
  change h3AfterSelector119 layout
    (controlledAddConstantMod2PowBasisAction clockSpec
      (h3I06BasisAction layout
        (historyTaylorTimeComparisonBasisAction layout
          (historyTaylorIdleEndComparisonBasisAction layout
            (historyTaylorActiveConjunctionBasisAction layout expected))))) = output
  rw [timeRestore, projectorStep, clockStep,
    clockToOutput]
  exact h3AfterSelector119_involutive layout output

end
end ExecutableHistoryExecutableHistory
