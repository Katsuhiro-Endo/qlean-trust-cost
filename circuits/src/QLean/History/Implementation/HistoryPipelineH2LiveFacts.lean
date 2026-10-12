import QLean.History.Implementation.HistoryPipelineH2SelectedQEntry

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
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

private theorem h2BeforeQ119_selector_value_stable
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 1 (h2BeforeQ119 layout input) =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 1 input := by
  unfold h2BeforeQ119 historyTaylorActiveConjunctionBasisAction
    h2AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
    h2AfterTime119 historyTaylorTimeComparisonBasisAction
    h2AfterSelector119 historyTaylorSelectorEqualityBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [layout.selectorEqualsNat_xorWire_workspace
    (historyActiveWire layout) (historyActiveWire_mem_workspace layout)]
  rw [layout.selectorEqualsNat_xorWire_workspace
    (historyLessThanIdleEndWire layout)
    (historyLessThanIdleEndWire_mem_workspace layout)]
  rw [layout.selectorEqualsNat_xorWire_workspace
    (historyLessThanTimeWire layout)
    (historyLessThanTimeWire_mem_workspace layout)]
  rw [layout.selectorEqualsNat_xorWire_workspace
    (historyBranchWire layout) (historyBranchWire_mem_workspace layout)]

private theorem h2BeforeQ119_clock_read_stable
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    layout.clock.read (h2BeforeQ119 layout input) = layout.clock.read input := by
  unfold h2BeforeQ119 historyTaylorActiveConjunctionBasisAction
    h2AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
    h2AfterTime119 historyTaylorTimeComparisonBasisAction
    h2AfterSelector119 historyTaylorSelectorEqualityBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [layout.clock_read_xorWire_workspace
    (historyActiveWire layout) (historyActiveWire_mem_workspace layout)]
  rw [layout.clock_read_xorWire_workspace
    (historyLessThanIdleEndWire layout)
    (historyLessThanIdleEndWire_mem_workspace layout)]
  rw [layout.clock_read_xorWire_workspace
    (historyLessThanTimeWire layout)
    (historyLessThanTimeWire_mem_workspace layout)]
  rw [layout.clock_read_xorWire_workspace
    (historyBranchWire layout) (historyBranchWire_mem_workspace layout)]

theorem h2BeforeQ119_branch_flag_value
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    h2BeforeQ119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index)
        (historyBranchWire (ExecutableLayout119 source domain)) =
      decide (branch.val = 1) := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits branch index
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input :=
    correctedBranchHistoryBasis119_p15_auxiliary source domain fits branch index
  have afterSelector :=
    historyTaylorSelectorEqualityBasisAction_maps_phase layout input auxiliary
  have afterTime := historyTaylorTimeComparisonBasisAction_maps_phase
    layout (h2AfterSelector119 layout input) afterSelector
  have afterIdle := historyTaylorIdleEndComparisonBasisAction_maps_phase
    layout (h2AfterTime119 layout input) afterTime
  have before := historyTaylorActiveConjunctionBasisAction_maps_phase
    layout (h2AfterIdleEnd119 layout input) afterIdle
  have selectorStable :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 1
          (historyTaylorActiveConjunctionBasisAction layout
            (h2AfterIdleEnd119 layout input)) =
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 1 input := by
    simpa only [h2BeforeQ119] using
      h2BeforeQ119_selector_value_stable layout input
  change h2BeforeQ119 layout input (historyBranchWire layout) = _
  unfold h2BeforeQ119
  rw [before.1, selectorStable]
  exact correctedBranchHistoryBasis119_selector_one source domain fits branch index

theorem h2BeforeQ119_time_flag_value
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    h2BeforeQ119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index)
        (historyLessThanTimeWire (ExecutableLayout119 source domain)) =
      decide (index.clock.val < source.historyParameters.physicalClocks) := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits branch index
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input :=
    correctedBranchHistoryBasis119_p15_auxiliary source domain fits branch index
  have afterSelector :=
    historyTaylorSelectorEqualityBasisAction_maps_phase layout input auxiliary
  have afterTime := historyTaylorTimeComparisonBasisAction_maps_phase
    layout (h2AfterSelector119 layout input) afterSelector
  have afterIdle := historyTaylorIdleEndComparisonBasisAction_maps_phase
    layout (h2AfterTime119 layout input) afterTime
  have before := historyTaylorActiveConjunctionBasisAction_maps_phase
    layout (h2AfterIdleEnd119 layout input) afterIdle
  have clockStable :
      layout.clock.read
          (historyTaylorActiveConjunctionBasisAction layout
            (h2AfterIdleEnd119 layout input)) = layout.clock.read input := by
    simpa only [h2BeforeQ119] using
      h2BeforeQ119_clock_read_stable layout input
  change h2BeforeQ119 layout input (historyLessThanTimeWire layout) = _
  unfold h2BeforeQ119
  rw [before.2.1]
  unfold historyTaylorClockLessThanTimeValue
  rw [clockStable]
  exact correctedBranchHistoryBasis119_clockLessThanTime
    source domain fits branch index

theorem h2BeforeQ119_idle_flag_value
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    h2BeforeQ119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index)
        (historyLessThanIdleEndWire (ExecutableLayout119 source domain)) =
      historyTaylorClockLessThanIdleEndValue
        (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index) := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits branch index
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input :=
    correctedBranchHistoryBasis119_p15_auxiliary source domain fits branch index
  have afterSelector :=
    historyTaylorSelectorEqualityBasisAction_maps_phase layout input auxiliary
  have afterTime := historyTaylorTimeComparisonBasisAction_maps_phase
    layout (h2AfterSelector119 layout input) afterSelector
  have afterIdle := historyTaylorIdleEndComparisonBasisAction_maps_phase
    layout (h2AfterTime119 layout input) afterTime
  have before := historyTaylorActiveConjunctionBasisAction_maps_phase
    layout (h2AfterIdleEnd119 layout input) afterIdle
  have clockStable :
      layout.clock.read
          (historyTaylorActiveConjunctionBasisAction layout
            (h2AfterIdleEnd119 layout input)) = layout.clock.read input := by
    simpa only [h2BeforeQ119] using
      h2BeforeQ119_clock_read_stable layout input
  change h2BeforeQ119 layout input (historyLessThanIdleEndWire layout) =
    historyTaylorClockLessThanIdleEndValue layout input
  unfold h2BeforeQ119
  rw [before.2.2.1]
  unfold historyTaylorClockLessThanIdleEndValue
  rw [clockStable]

end
end ExecutableHistoryExecutableHistory
