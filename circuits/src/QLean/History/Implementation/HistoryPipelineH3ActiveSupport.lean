import QLean.History.Implementation.HistoryPipelineH3ActiveTail
import QLean.History.Implementation.HistoryPipelineH2ActivePostAction

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
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

noncomputable section

theorem h3BeforeUniform119_workspace_of_not_live
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
    h3BeforeUniform119 layout input wire = input wire := by
  have neBranch : wire ≠ historyBranchWire layout := by
    intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  have neTime : wire ≠ historyLessThanTimeWire layout := by
    intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  have neIdleEnd : wire ≠ historyLessThanIdleEndWire layout := by
    intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  have neActive : wire ≠ historyActiveWire layout := by
    intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  unfold h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
  rw [xorWire_apply_other _ _ neActive]
  unfold h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
  rw [xorWire_apply_other _ _ neIdleEnd]
  unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
  rw [xorWire_apply_other _ _ neTime]
  unfold h3AfterSelector119
  exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
    _ _ _ _ neBranch input

theorem h3OutsideEqual_workspace119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout)
    (output input : QubitBasis qubits)
    (outsideEqual :
      restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout evidence).placement output =
        restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout evidence).placement input)
    (workspaceIndex : Fin (historyClockWorkspaceWidth parameters
      generatorWorkWidth)) :
    output (layout.workspace.wire workspaceIndex) =
      input (layout.workspace.wire workspaceIndex) := by
  let controlled := historyOrderUniformExternalControlLayout layout evidence
  let outside : OutsideWire controlled.placement :=
    ⟨layout.workspace.wire workspaceIndex, by
      intro orderIndex
      change layout.order.wire orderIndex ≠ layout.workspace.wire workspaceIndex
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex⟩
  have atOutside := congrFun outsideEqual outside
  change output outside.val = input outside.val at atOutside
  simpa [outside] using atOutside

theorem h3OutsideEqual_coefficient119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout)
    (output input : QubitBasis qubits)
    (outsideEqual :
      restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout evidence).placement output =
        restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout evidence).placement input) :
    output layout.coefficientSignal = input layout.coefficientSignal := by
  let controlled := historyOrderUniformExternalControlLayout layout evidence
  let outside : OutsideWire controlled.placement :=
    ⟨layout.coefficientSignal, by
      intro orderIndex
      change layout.order.wire orderIndex ≠ layout.coefficientSignal
      exact (layout.orderWire_separated orderIndex).2.2.1
        layout.coefficientSignal (by simp)⟩
  have atOutside := congrFun outsideEqual outside
  change output outside.val = input outside.val at atOutside
  simpa [outside] using atOutside

theorem h3OutsideEqual_workspace_member119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout)
    (output input : QubitBasis qubits)
    (outsideEqual :
      restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout evidence).placement output =
        restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout evidence).placement input)
    (wire : Fin qubits) (member : wire ∈ historyRegisterWires layout.workspace) :
    output wire = input wire := by
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨workspaceIndex, rfl⟩
  exact h3OutsideEqual_workspace119 layout evidence output input outsideEqual
    workspaceIndex

theorem h3WorkspaceWire_ne_projector119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyClockWorkspaceWidth parameters generatorWorkWidth)) :
    layout.workspace.wire index ≠ layout.projectorSignal := by
  have split := List.nodup_append.mp layout.allWiresNodup
  have projectorInPrefix : layout.projectorSignal ∈
      historyRegisterWires layout.selector ++
        historyRegisterWires layout.data ++ historyRegisterWires layout.clock ++
        historyRegisterWires layout.order ++
        historyRegisterWires layout.generatorSignal ++
        [layout.coefficientSignal, layout.orderBoundarySignal,
          layout.projectorSignal, layout.clockBoundarySignal] := by
    simp
  have workspaceMember : layout.workspace.wire index ∈
      historyRegisterWires layout.workspace := List.mem_ofFn.mpr ⟨index, rfl⟩
  exact (split.2.2 _ projectorInPrefix _ workspaceMember).symm

private theorem h3IdleFlag_not_live119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ∉ historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyIdleFlag
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  have sharedAtLeast : 5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
    calc
      5 ≤ historyStructuralPoolWidth parameters := by
        unfold historyStructuralPoolWidth
        omega
      _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
        Nat.le_max_right _ _
  omega

theorem h3EqualityFlag_not_live119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyEqualityFlag layout ∉ historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyEqualityFlag
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  have sharedAtLeast : 5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
    calc
      5 ≤ historyStructuralPoolWidth parameters := by
        unfold historyStructuralPoolWidth
        omega
      _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
        Nat.le_max_right _ _
  omega

theorem h3CoefficientControl_not_live119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyCoefficientControl
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  have sharedAtLeast : 5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
    calc
      5 ≤ historyStructuralPoolWidth parameters := by
        unfold historyStructuralPoolWidth
        omega
      _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
        Nat.le_max_right _ _
  omega

theorem h3EqualityWork_not_live119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyEqualityWorkWidth parameters)) :
    (historyEqualityWork layout).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyEqualityWork
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  have structuralFits := Nat.le_max_right generatorWorkWidth
    (historyStructuralPoolWidth parameters)
  unfold historySharedPoolWidth
  unfold historyStructuralPoolWidth at structuralFits ⊢
  omega

theorem h3ClockMasked_not_live119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyClockTailWidth parameters + 1)) :
    (historyClockMaskedConstantRegister layout).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyClockMaskedConstantRegister
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  rw [historyClockTailWidth_succ]
  have structuralFits := Nat.le_max_right generatorWorkWidth
    (historyStructuralPoolWidth parameters)
  unfold historySharedPoolWidth
  unfold historyStructuralPoolWidth at structuralFits ⊢
  unfold historyMaximumLabelWidth
  omega

theorem h3ClockCarry_not_live119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyClockIncrementCarry layout ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyClockIncrementCarry
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  calc
    5 + 2 * historyClockWidth parameters.timeSteps parameters.taylorOrder
          parameters.idlingSteps + historyEqualityWorkWidth parameters + 1 ≤
        historyStructuralPoolWidth parameters := by
      unfold historyStructuralPoolWidth historyMaximumLabelWidth
        historyClockWidth historyOrderWidth
      omega
    _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
      Nat.le_max_right _ _

theorem h3BeforeUniform119_active_clean_values
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    before (historyBranchWire layout) = true ∧
      before (historyLessThanTimeWire layout) = true ∧
      before (historyLessThanIdleEndWire layout) = true ∧
      before (historyIdleFlag layout) = false ∧
      before (historyActiveWire layout) = true ∧
      before layout.coefficientSignal = false := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout logical :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 index
  have branch : before (historyBranchWire layout) = true := by
    unfold before h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _ (historyBranchWire_ne_activeWire layout)]
    exact h3AfterIdleEnd119_selected_branch_true source domain fits index
  have time : before (historyLessThanTimeWire layout) = true := by
    unfold before h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _
      (historyLessThanTimeWire_ne_activeWire layout)]
    simpa [clockActive] using
      h3AfterIdleEnd119_time_flag_value source domain fits index
  have idleEnd : before (historyLessThanIdleEndWire layout) = true := by
    unfold before h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _
      (historyLessThanIdleEndWire_ne_activeWire layout)]
    have inside : index.clock.val < source.historyParameters.clockEnd :=
      lt_trans clockActive source.historyWellFormed.2.2.2.2
    simpa [inside] using
      h3AfterIdleEnd119_idle_end_flag_value source domain fits index
  have idle : before (historyIdleFlag layout) = false := by
    calc
      before (historyIdleFlag layout) = logical (historyIdleFlag layout) := by
        unfold before
        exact h3BeforeUniform119_workspace_of_not_live layout logical
          (historyIdleFlag layout) (h3IdleFlag_not_live119 layout)
      _ = false := historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
        layout logical auxiliary _ (by
          unfold historyIdleFlag
          apply historyWorkspaceSlice_wire_mem)
  have active : before (historyActiveWire layout) = true := by
    simpa [before, logical, layout, clockActive] using
      h3BeforeUniform119_active_selected_value source domain fits index
  have coefficient : before layout.coefficientSignal = false := by
    have separated := layout.postGeneratorSignal_separated
      layout.coefficientSignal (by simp)
    have activeNe : historyActiveWire layout ≠ layout.coefficientSignal := by
      unfold historyActiveWire
      exact separated.2.2 _
    have idleEndNe : historyLessThanIdleEndWire layout ≠
        layout.coefficientSignal := by
      unfold historyLessThanIdleEndWire
      exact separated.2.2 _
    have timeNe : historyLessThanTimeWire layout ≠
        layout.coefficientSignal := by
      unfold historyLessThanTimeWire
      exact separated.2.2 _
    have branchNe : historyBranchWire layout ≠ layout.coefficientSignal := by
      unfold historyBranchWire
      exact separated.2.2 _
    unfold before h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
      h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
      h3AfterTime119 historyTaylorTimeComparisonBasisAction
      h3AfterSelector119
    rw [xorWire_apply_other _ _ activeNe.symm,
      xorWire_apply_other _ _ idleEndNe.symm,
      xorWire_apply_other _ _ timeNe.symm,
      ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
    · exact correctedBranchHistoryBasis119_coefficientSignal_false119
        source domain fits h3SelectedBranch119 index
    · exact branchNe.symm
  exact ⟨branch, time, idleEnd, idle, active, coefficient⟩

theorem h3UniformMiddle119_active_clean_values
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (middle : QubitBasis (ExecutableRaw119 source).history.qubits)
    (outsideEqual :
      let layout := ExecutableLayout119 source domain
      let before := h3BeforeUniform119 layout
        (correctedBranchHistoryBasis119 source domain fits
          h3SelectedBranch119 index)
      restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout
            (ExecutableClockEvidence119 source domain).uniformExternalControl
          ).placement middle =
        restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout
            (ExecutableClockEvidence119 source domain).uniformExternalControl
          ).placement before) :
    let layout := ExecutableLayout119 source domain
    middle (historyBranchWire layout) = true ∧
      middle (historyLessThanTimeWire layout) = true ∧
      middle (historyLessThanIdleEndWire layout) = true ∧
      middle (historyIdleFlag layout) = false ∧
      middle (historyActiveWire layout) = true ∧
      middle layout.coefficientSignal = false := by
  dsimp only at outsideEqual ⊢
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).uniformExternalControl
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  have beforeValues := h3BeforeUniform119_active_clean_values
    source domain fits index clockActive
  have workspaceValue (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace) :
      middle wire = before wire :=
    h3OutsideEqual_workspace_member119 layout evidence middle before
      outsideEqual wire member
  have coefficientValue : middle layout.coefficientSignal =
      before layout.coefficientSignal :=
    h3OutsideEqual_coefficient119 layout evidence middle before outsideEqual
  exact ⟨
    (workspaceValue _ (historyBranchWire_mem_workspace layout)).trans
      beforeValues.1,
    (workspaceValue _ (historyLessThanTimeWire_mem_workspace layout)).trans
      beforeValues.2.1,
    (workspaceValue _ (historyLessThanIdleEndWire_mem_workspace layout)).trans
      beforeValues.2.2.1,
    (workspaceValue _ (by
      unfold historyIdleFlag
      apply historyWorkspaceSlice_wire_mem)).trans beforeValues.2.2.2.1,
    (workspaceValue _ (historyActiveWire_mem_workspace layout)).trans
      beforeValues.2.2.2.2.1,
    coefficientValue.trans beforeValues.2.2.2.2.2⟩

end
end ExecutableHistoryExecutableHistory
