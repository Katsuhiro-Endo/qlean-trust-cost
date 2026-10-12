import QLean.History.Implementation.HistoryPipelineH3BranchIdentity
import QLean.History.Implementation.HistoryPipelineH2PostFacts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

def h3SelectedBranch119 : Fin 4 := ⟨2, by decide⟩

private theorem false_bne119 (value : Bool) :
    (false != value) = value := by
  cases value <;> rfl

theorem h3AfterSelector119_selected_branch_true
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    h3AfterSelector119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h3SelectedBranch119 index)
        (historyBranchWire (ExecutableLayout119 source domain)) = true := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 index
  have branchZero := historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
    layout input auxiliary _ (historyBranchWire_mem_workspace layout)
  unfold h3AfterSelector119
  rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target]
  change (input (historyBranchWire layout) !=
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 2 input) = true
  rw [branchZero]
  have selected := correctedBranchHistoryBasis119_selector_two
    source domain fits h3SelectedBranch119 index
  rw [selected]
  decide

theorem h3AfterIdleEnd119_selected_branch_true
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    h3AfterIdleEnd119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h3SelectedBranch119 index)
        (historyBranchWire (ExecutableLayout119 source domain)) = true := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  unfold h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
  rw [xorWire_apply_other _ _
    (historyBranchWire_ne_lessThanIdleEndWire layout)]
  unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
  rw [xorWire_apply_other _ _
    (historyBranchWire_ne_lessThanTimeWire layout)]
  exact h3AfterSelector119_selected_branch_true source domain fits index

private theorem h3AfterSelector119_clock_read_stable
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    layout.clock.read (h3AfterSelector119 layout input) =
      layout.clock.read input := by
  unfold h3AfterSelector119
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  exact layout.clock_read_xorWire_workspace
    (historyBranchWire layout) (historyBranchWire_mem_workspace layout) _ _

theorem h3AfterIdleEnd119_time_flag_value
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    h3AfterIdleEnd119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h3SelectedBranch119 index)
        (historyLessThanTimeWire (ExecutableLayout119 source domain)) =
      decide (index.clock.val < source.historyParameters.physicalClocks) := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 index
  have timeZero : h3AfterSelector119 layout input
      (historyLessThanTimeWire layout) = false := by
    unfold h3AfterSelector119
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
    · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
        layout input auxiliary _ (historyLessThanTimeWire_mem_workspace layout)
    · exact (historyBranchWire_ne_lessThanTimeWire layout).symm
  unfold h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
  rw [xorWire_apply_other _ _
    (historyLessThanTimeWire_ne_lessThanIdleEndWire layout)]
  unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
  simp only [layout, xorWire, Function.update_self]
  rw [timeZero]
  rw [false_bne119]
  unfold historyTaylorClockLessThanTimeValue
  rw [h3AfterSelector119_clock_read_stable]
  exact correctedBranchHistoryBasis119_clockLessThanTime
    source domain fits h3SelectedBranch119 index

theorem h3AfterIdleEnd119_idle_end_flag_value
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    h3AfterIdleEnd119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h3SelectedBranch119 index)
        (historyLessThanIdleEndWire (ExecutableLayout119 source domain)) =
      decide (index.clock.val < source.historyParameters.clockEnd) := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 index
  have idleZero : h3AfterTime119 layout input
      (historyLessThanIdleEndWire layout) = false := by
    unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
    rw [xorWire_apply_other _ _
      (historyLessThanTimeWire_ne_lessThanIdleEndWire layout).symm]
    unfold h3AfterSelector119
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
    · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
        layout input auxiliary _
        (historyLessThanIdleEndWire_mem_workspace layout)
    · exact (historyBranchWire_ne_lessThanIdleEndWire layout).symm
  have clockStable : layout.clock.read (h3AfterTime119 layout input) =
      layout.clock.read input := by
    unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
    rw [layout.clock_read_xorWire_workspace
      (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_mem_workspace layout)]
    exact h3AfterSelector119_clock_read_stable layout input
  unfold h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
  simp only [xorWire, Function.update_self]
  rw [idleZero]
  rw [false_bne119]
  unfold historyTaylorClockLessThanIdleEndValue
  rw [clockStable]
  exact correctedBranchHistoryBasis119_clockLessThanIdleEnd
    source domain fits h3SelectedBranch119 index

theorem h3BeforeUniform119_active_selected_value
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    h3BeforeUniform119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h3SelectedBranch119 index)
        (historyActiveWire (ExecutableLayout119 source domain)) =
      decide (index.clock.val < source.historyParameters.physicalClocks) := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 index
  have activeZero := h3AfterIdleEnd119_active_zero layout input auxiliary
  unfold h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
  simp only [xorWire, Function.update_self]
  unfold ClassicalReversibleStage.allWiresTrue
    ClassicalReversibleStage.readWires
  rw [activeZero]
  rw [false_bne119]
  simp only [List.map, List.all, id_eq, Bool.and_true]
  rw [h3AfterIdleEnd119_selected_branch_true source domain fits index,
    h3AfterIdleEnd119_time_flag_value source domain fits index]
  cases decide (index.clock.val < source.historyParameters.physicalClocks) <;>
    rfl

private theorem h3_uniform_work_ne_active119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin 2) :
    (historyUniformControlWork layout).wire index ≠
      historyActiveWire layout := by
  have notLive : (historyUniformControlWork layout).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
    simpa [historyUniformControlWork] using
      historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
        layout 0 (by
          unfold historyClockWorkspaceWidth
          omega) (by
          unfold historySharedPoolWidth historyStructuralPoolWidth
          omega) index
  intro equal
  apply notLive
  simp [historyTaylorBeforeGeneratorLiveWires, equal]

private theorem h3AfterIdleEnd119_uniform_work_zero_live119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input)
    (index : Fin 2) :
    h3AfterIdleEnd119 layout input
        ((historyUniformControlWork layout).wire index) = false := by
  have notLive : (historyUniformControlWork layout).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
    simpa [historyUniformControlWork] using
      historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
        layout 0 (by
          unfold historyClockWorkspaceWidth
          omega) (by
          unfold historySharedPoolWidth historyStructuralPoolWidth
          omega) index
  unfold h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
  rw [xorWire_apply_other]
  · unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
    rw [xorWire_apply_other]
    · unfold h3AfterSelector119
      rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
      · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
          layout input auxiliary _
          (historyUniformControlWork_wire_mem_workspace layout index)
      · intro equal
        apply notLive
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
    · intro equal
      apply notLive
      simp [historyTaylorBeforeGeneratorLiveWires, equal]
  · intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]

theorem h3BeforeUniform119_uniform_work_clean
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    externallyControlledCleanWorkPredicate
      (historyOrderUniformExternalControlCleanWorkValid
        (ExecutableLayout119 source domain)
        (ExecutableClockEvidence119 source domain).uniformExternalControl)
      (h3BeforeUniform119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h3SelectedBranch119 index)) := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 index
  change h3BeforeUniform119 layout input
        ((historyUniformControlWork layout).wire 0) = false ∧
    h3BeforeUniform119 layout input
        ((historyUniformControlWork layout).wire 1) = false
  constructor <;> unfold h3BeforeUniform119
  · unfold historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other]
    · exact h3AfterIdleEnd119_uniform_work_zero_live119
        layout input auxiliary 0
    · exact h3_uniform_work_ne_active119 layout 0
  · unfold historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other]
    · exact h3AfterIdleEnd119_uniform_work_zero_live119
        layout input auxiliary 1
    · exact h3_uniform_work_ne_active119 layout 1

theorem h3AfterIdleEnd119_read_order
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    layout.order.read (h3AfterIdleEnd119 layout input) =
      layout.order.read input := by
  funext orderIndex
  have branchMember := historyBranchWire_mem_workspace layout
  rcases List.mem_ofFn.mp branchMember with ⟨branchIndex, branchEq⟩
  have timeMember := historyLessThanTimeWire_mem_workspace layout
  rcases List.mem_ofFn.mp timeMember with ⟨timeIndex, timeEq⟩
  have idleMember := historyLessThanIdleEndWire_mem_workspace layout
  rcases List.mem_ofFn.mp idleMember with ⟨idleIndex, idleEq⟩
  have branchNe : layout.order.wire orderIndex ≠ historyBranchWire layout := by
    intro equal
    exact (layout.orderWire_separated orderIndex).2.2.2 branchIndex
      (equal.trans branchEq.symm)
  have timeNe : layout.order.wire orderIndex ≠
      historyLessThanTimeWire layout := by
    intro equal
    exact (layout.orderWire_separated orderIndex).2.2.2 timeIndex
      (equal.trans timeEq.symm)
  have idleNe : layout.order.wire orderIndex ≠
      historyLessThanIdleEndWire layout := by
    intro equal
    exact (layout.orderWire_separated orderIndex).2.2.2 idleIndex
      (equal.trans idleEq.symm)
  change h3AfterIdleEnd119 layout input (layout.order.wire orderIndex) =
    input (layout.order.wire orderIndex)
  unfold h3AfterIdleEnd119 h3AfterTime119 h3AfterSelector119
    historyTaylorIdleEndComparisonBasisAction
    historyTaylorTimeComparisonBasisAction
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [xorWire_apply_other _ _ idleNe,
    xorWire_apply_other _ _ timeNe,
    xorWire_apply_other _ _ branchNe]

theorem h3BeforeUniform119_read_order
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    layout.order.read (h3BeforeUniform119 layout input) =
      layout.order.read input := by
  funext orderIndex
  have activeMember := historyActiveWire_mem_workspace layout
  rcases List.mem_ofFn.mp activeMember with ⟨activeIndex, activeEq⟩
  have orderNe : layout.order.wire orderIndex ≠ historyActiveWire layout := by
    intro equal
    exact (layout.orderWire_separated orderIndex).2.2.2 activeIndex
      (equal.trans activeEq.symm)
  unfold h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
  change xorWire (historyActiveWire layout) _
      (h3AfterIdleEnd119 layout input) (layout.order.wire orderIndex) = _
  rw [xorWire_apply_other _ _ orderNe]
  exact congrFun (h3AfterIdleEnd119_read_order layout input) orderIndex

end
end ExecutableHistoryExecutableHistory
