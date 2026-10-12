import QLean.History.Implementation.HistoryPipelineH3IdleTerminal

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
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

private theorem h3IdleGeneral_idle_ne_branch119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ≠ historyBranchWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast : 5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
    calc
      5 ≤ historyStructuralPoolWidth parameters := by
        unfold historyStructuralPoolWidth
        omega
      _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
        Nat.le_max_right _ _
  omega

private theorem h3IdleGeneral_idle_ne_active119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ≠ historyActiveWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast : 5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
    calc
      5 ≤ historyStructuralPoolWidth parameters := by
        unfold historyStructuralPoolWidth
        omega
      _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
        Nat.le_max_right _ _
  omega

/-- On an idle logical input the repaired idle transform restores every
workspace wire.  Its only clean-branch data mutation is in the order register. -/
theorem h3IdleTransformCleanAction119_workspace
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (member : wire ∈ historyRegisterWires
      (ExecutableLayout119 source domain).workspace) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    h3IdleTransformCleanAction119 layout
        source.historyParameters.binaryLabels before wire = before wire := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  let afterEnd := xorWire (historyIdleFlag layout)
    (before (historyLessThanIdleEndWire layout)) before
  let afterTime := xorWire (historyIdleFlag layout)
    (afterEnd (historyLessThanTimeWire layout)) afterEnd
  let afterConjunction :=
    ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) afterTime
  let afterOrder := h3CnotTargetsBasisAction119
    (repairedH3IdleOrderTargets119 layout
      source.historyParameters.binaryLabels)
    (historyActiveWire layout) afterConjunction
  let afterRestoreConjunction :=
    ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) afterOrder
  let afterTimeRestore := xorWire (historyIdleFlag layout)
    (afterRestoreConjunction (historyLessThanTimeWire layout))
    afterRestoreConjunction
  have values := h3BeforeUniform119_idle_clean_values
    source domain fits index clockIdle
  have beforeBranch : before (historyBranchWire layout) = true := values.1
  have beforeTime : before (historyLessThanTimeWire layout) = false := values.2.1
  have beforeIdleEnd : before (historyLessThanIdleEndWire layout) = true :=
    values.2.2.1
  have beforeIdle : before (historyIdleFlag layout) = false := values.2.2.2.1
  have beforeActive : before (historyActiveWire layout) = false :=
    values.2.2.2.2.1
  have afterEndTime : afterEnd (historyLessThanTimeWire layout) = false := by
    unfold afterEnd
    rw [xorWire_apply_other]
    · exact beforeTime
    · exact (ExecutableClockEvidence119 source domain).idleTransform.time_ne_idle
  have afterTimeEq : afterTime = afterEnd := by
    unfold afterTime
    rw [afterEndTime]
    funext outputWire
    simp [xorWire]
  have afterTimeBranch : afterTime (historyBranchWire layout) = true := by
    rw [afterTimeEq]
    unfold afterEnd
    rw [xorWire_apply_other]
    · exact beforeBranch
    · exact (h3IdleGeneral_idle_ne_branch119 layout).symm
  have afterTimeIdle : afterTime (historyIdleFlag layout) = true := by
    rw [afterTimeEq]
    simp [afterEnd, xorWire, beforeIdleEnd, beforeIdle]
  have afterTimeActive : afterTime (historyActiveWire layout) = false := by
    rw [afterTimeEq]
    unfold afterEnd
    rw [xorWire_apply_other]
    · exact beforeActive
    · exact (h3IdleGeneral_idle_ne_active119 layout).symm
  have afterConjunctionActive :
      afterConjunction (historyActiveWire layout) = true := by
    simp [afterConjunction,
      ClassicalReversibleStage.conjunctionDirectBasisAction,
      ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires, xorWire, afterTimeBranch,
      afterTimeIdle, afterTimeActive]
  have orderOnWorkspace
      (workspaceWire : Fin (ExecutableRaw119 source).history.qubits)
      (workspaceMember : workspaceWire ∈ historyRegisterWires layout.workspace) :
      afterOrder workspaceWire = afterConjunction workspaceWire := by
    unfold afterOrder
    rw [h3CnotTargetsBasisAction119_apply_outside]
    intro target targetMember
    have orderMember := repairedH3IdleOrderTargets119_mem_order
      layout source.historyParameters.binaryLabels target targetMember
    simp only [historyRegisterWires, List.mem_ofFn] at orderMember workspaceMember
    rcases orderMember with ⟨orderIndex, rfl⟩
    rcases workspaceMember with ⟨workspaceIndex, rfl⟩
    exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
  have restoreOnWorkspace
      (workspaceWire : Fin (ExecutableRaw119 source).history.qubits)
      (workspaceMember : workspaceWire ∈ historyRegisterWires layout.workspace) :
      afterRestoreConjunction workspaceWire = afterTime workspaceWire := by
    have activeMember := historyActiveWire_mem_workspace layout
    have branchMember := historyBranchWire_mem_workspace layout
    have idleMember : historyIdleFlag layout ∈
        historyRegisterWires layout.workspace := by
      unfold historyIdleFlag
      apply historyWorkspaceSlice_wire_mem
    have afterConjunctionBranch :
        afterConjunction (historyBranchWire layout) = true := by
      unfold afterConjunction
      rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other]
      · exact afterTimeBranch
      · exact historyBranchWire_ne_activeWire layout
    have afterConjunctionIdle :
        afterConjunction (historyIdleFlag layout) = true := by
      unfold afterConjunction
      rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other]
      · exact afterTimeIdle
      · exact h3IdleGeneral_idle_ne_active119 layout
    have afterOrderBranch : afterOrder (historyBranchWire layout) = true := by
      rw [orderOnWorkspace (historyBranchWire layout) branchMember]
      exact afterConjunctionBranch
    have afterOrderIdle : afterOrder (historyIdleFlag layout) = true := by
      rw [orderOnWorkspace (historyIdleFlag layout) idleMember]
      exact afterConjunctionIdle
    have afterOrderActive : afterOrder (historyActiveWire layout) = true := by
      rw [orderOnWorkspace (historyActiveWire layout) activeMember]
      exact afterConjunctionActive
    unfold afterRestoreConjunction
    by_cases isActive : workspaceWire = historyActiveWire layout
    · subst workspaceWire
      simp [ClassicalReversibleStage.conjunctionDirectBasisAction,
        ClassicalReversibleStage.allWiresTrue,
        ClassicalReversibleStage.readWires, xorWire, afterOrderBranch,
        afterOrderIdle, afterOrderActive, afterTimeActive]
    · rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other]
      · rw [orderOnWorkspace workspaceWire workspaceMember]
        unfold afterConjunction
        rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other]
        exact isActive
      · exact isActive
  have restoreTimeFalse :
      afterRestoreConjunction (historyLessThanTimeWire layout) = false := by
    rw [restoreOnWorkspace _ (historyLessThanTimeWire_mem_workspace layout)]
    rw [afterTimeEq]
    exact afterEndTime
  have afterTimeRestoreEq : afterTimeRestore = afterRestoreConjunction := by
    unfold afterTimeRestore
    rw [restoreTimeFalse]
    funext outputWire
    simp [xorWire]
  have restoredIdleEnd : afterTimeRestore
      (historyLessThanIdleEndWire layout) = true := by
    rw [afterTimeRestoreEq,
      restoreOnWorkspace _ (historyLessThanIdleEndWire_mem_workspace layout),
      afterTimeEq]
    unfold afterEnd
    rw [xorWire_apply_other]
    · exact beforeIdleEnd
    · exact (ExecutableClockEvidence119 source domain).idleTransform.idleEnd_ne_idle
  unfold h3IdleTransformCleanAction119
  change xorWire (historyIdleFlag layout)
      (afterTimeRestore (historyLessThanIdleEndWire layout))
      afterTimeRestore wire = before wire
  rw [restoredIdleEnd]
  calc
    xorWire (historyIdleFlag layout) true afterTimeRestore wire =
        xorWire (historyIdleFlag layout) true afterRestoreConjunction wire := by
          rw [afterTimeRestoreEq]
    _ = xorWire (historyIdleFlag layout) true afterTime wire := by
          have idleMember : historyIdleFlag layout ∈
              historyRegisterWires layout.workspace := by
            unfold historyIdleFlag
            apply historyWorkspaceSlice_wire_mem
          by_cases equal : wire = historyIdleFlag layout
          · subst wire
            simp [xorWire,
              restoreOnWorkspace (historyIdleFlag layout) idleMember]
          · simpa [xorWire, equal] using restoreOnWorkspace wire member
    _ = xorWire (historyIdleFlag layout) true afterEnd wire := by
          rw [afterTimeEq]
    _ = before wire := by
      unfold afterEnd
      rw [beforeIdleEnd]
      simp [xorWire]

/-- The inactive suffix is exact on any order/coefficient variant of the
logical zero-order state, provided all workspace wires are unchanged. -/
theorem h3IdlePostTransformOperator119_apply_basisKet_workspace_variant
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (inputWorkspace : ∀ wire,
      wire ∈ historyRegisterWires (ExecutableLayout119 source domain).workspace →
      input wire =
        h3ZeroOrder119 (ExecutableLayout119 source domain)
          (h3BeforeUniform119 (ExecutableLayout119 source domain)
            (correctedBranchHistoryBasis119 source domain fits
              h3SelectedBranch119 index)) wire) :
    VerifiedCircuitCore.applyOperator
        (h3IdlePostTransformOperator119 source domain)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet
        (h3ActiveTailBasisAction119 source domain input) := by
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  let zeroIndex := h3OrderZeroIndex119 source index
  let zeroLogical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 zeroIndex
  let expected := h3ZeroOrder119 layout
    (h3BeforeUniform119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h3SelectedBranch119 index))
  let afterActive := historyTaylorActiveConjunctionBasisAction layout input
  let afterIdle := historyTaylorIdleEndComparisonBasisAction layout afterActive
  let afterTime := historyTaylorTimeComparisonBasisAction layout afterIdle
  let afterProjector := h3I06BasisAction layout afterTime
  have expectedEq : expected = h3BeforeUniform119 layout zeroLogical :=
    h3ZeroOrder119_before_eq_orderZeroIndex source domain fits index
  have clockIdleZero : ¬ zeroIndex.clock.val <
      source.historyParameters.physicalClocks := by
    simpa [zeroIndex] using clockIdle
  have values := h3BeforeUniform119_idle_clean_values
    source domain fits zeroIndex clockIdleZero
  have workspaceEq
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace) :
      input wire = expected wire := by
    exact inputWorkspace wire member
  have branchTrue : input (historyBranchWire layout) = true := by
    rw [workspaceEq _ (historyBranchWire_mem_workspace layout), expectedEq]
    exact values.1
  have timeFalse : input (historyLessThanTimeWire layout) = false := by
    rw [workspaceEq _ (historyLessThanTimeWire_mem_workspace layout), expectedEq]
    exact values.2.1
  have activeFalse : input (historyActiveWire layout) = false := by
    rw [workspaceEq _ (historyActiveWire_mem_workspace layout), expectedEq]
    exact values.2.2.2.2.1
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout zeroLogical :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 zeroIndex
  have zeroOfNotLive
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace)
      (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
      input wire = false := by
    rw [workspaceEq wire member, expectedEq]
    calc
      h3BeforeUniform119 layout zeroLogical wire = zeroLogical wire :=
        h3BeforeUniform119_workspace_of_not_live layout zeroLogical wire notLive
      _ = false := historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
        layout zeroLogical auxiliary wire member
  have afterActiveZero
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
      afterActive wire = input wire := by
    unfold afterActive historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other]
    intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  have restoredZero
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace)
      (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
      afterTime wire = false := by
    calc
      afterTime wire = input wire :=
        h3ActiveRestoredComparisons119_apply_other layout input wire notLive
      _ = false := zeroOfNotLive wire member notLive
  have idleComparisonClean :
      (∀ i, afterActive ((historyBorrowRegister layout).wire i) = false) ∧
        ∀ i, afterActive ((historyBoundRegister layout).wire i) = false := by
    constructor
    · intro i
      rw [afterActiveZero _
        (historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires layout i)]
      exact zeroOfNotLive _ (historyBorrowRegister_wire_mem_workspace layout i)
        (historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires layout i)
    · intro i
      rw [afterActiveZero _
        (historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires layout i)]
      exact zeroOfNotLive _ (historyBoundRegister_wire_mem_workspace layout i)
        (historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires layout i)
  have timeComparisonClean :
      (∀ i, afterIdle ((historyBorrowRegister layout).wire i) = false) ∧
        ∀ i, afterIdle ((historyBoundRegister layout).wire i) = false := by
    constructor
    · intro i
      unfold afterIdle historyTaylorIdleEndComparisonBasisAction
      rw [xorWire_apply_other]
      · exact idleComparisonClean.1 i
      · intro equal
        apply historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires layout i
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
    · intro i
      unfold afterIdle historyTaylorIdleEndComparisonBasisAction
      rw [xorWire_apply_other]
      · exact idleComparisonClean.2 i
      · intro equal
        apply historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires layout i
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
  have projectorWorkClean :
      ClassicalReversibleStage.minimumWorkCleanPredicate
          (historyRegisterWires (historyEqualityWork layout)) afterTime ∧
        h3I06CleanInputPredicate layout afterTime := by
    constructor
    · intro wire member
      simp only [historyRegisterWires, List.mem_ofFn] at member
      rcases member with ⟨i, rfl⟩
      exact restoredZero _ (by
          unfold historyEqualityWork
          apply historyWorkspaceSlice_wire_mem)
        (h3EqualityWork_not_live119 layout i)
    · change afterTime (historyEqualityFlag layout) = false ∧
        afterTime (historyCoefficientControl layout) = false
      constructor
      · exact restoredZero _ (by
          unfold historyEqualityFlag
          apply historyWorkspaceSlice_wire_mem)
          (h3EqualityFlag_not_live119 layout)
      · exact restoredZero _ (by
          unfold historyCoefficientControl
          apply historyWorkspaceSlice_wire_mem)
          (h3CoefficientControl_not_live119 layout)
  have clockWorkClean : controlledAddConstantMod2PowCleanPredicate
      (historyControlledClockIncrementSpec layout clock.controlledIncrement)
      afterProjector := by
    change (∀ i, afterProjector
        ((historyClockMaskedConstantRegister layout).wire i) = false) ∧
      afterProjector (historyClockIncrementCarry layout) = false
    constructor
    · intro i
      unfold afterProjector h3I06BasisAction
      rw [xorWire_apply_other]
      · exact restoredZero _
          (historyClockMaskedConstantRegister_wire_mem_workspace layout i)
          (h3ClockMasked_not_live119 layout i)
      · unfold historyClockMaskedConstantRegister
        exact h3WorkspaceWire_ne_projector119 layout _
    · unfold afterProjector h3I06BasisAction
      rw [xorWire_apply_other]
      · exact restoredZero _ (historyClockIncrementCarry_mem_workspace layout)
          (h3ClockCarry_not_live119 layout)
      · unfold historyClockIncrementCarry
        exact h3WorkspaceWire_ne_projector119 layout _
  exact h3IdlePostTransformOperator119_apply_basisKet source domain input
    branchTrue timeFalse activeFalse idleComparisonClean timeComparisonClean
    projectorWorkClean clockWorkClean

end
end ExecutableHistoryExecutableHistory
