import QLean.History.Implementation.HistoryPipelineH3IdleTransform

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

private theorem h3IdleFlag_not_live_idle119
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

private theorem h3IdleFlag_ne_branch_idle119
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

private theorem h3IdleFlag_ne_active_idle119
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

theorem h3IdleConjunctionBasisAction_involutive119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyIdleFlag layout]
        (historyActiveWire layout)
        (ClassicalReversibleStage.conjunctionDirectBasisAction
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) input) = input := by
  funext wire
  simp [ClassicalReversibleStage.conjunctionDirectBasisAction,
    ClassicalReversibleStage.allWiresTrue,
    ClassicalReversibleStage.readWires, xorWire,
    historyBranchWire_ne_activeWire layout,
    h3IdleFlag_ne_active_idle119 layout]

theorem h3IdleConjunctionBasisAction_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyIdleFlag layout]
        (historyActiveWire layout)
        (writeRegisterValue layout.order value input) =
      writeRegisterValue layout.order value
        (ClassicalReversibleStage.conjunctionDirectBasisAction
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) input) := by
  have branchStable : writeRegisterValue layout.order value input
      (historyBranchWire layout) = input (historyBranchWire layout) :=
    writeRegisterValue_apply_outside layout.order value input _ (by
      intro orderIndex equal
      rcases List.mem_ofFn.mp (historyBranchWire_mem_workspace layout) with
        ⟨workspaceIndex, member⟩
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm))
  have idleStable : writeRegisterValue layout.order value input
      (historyIdleFlag layout) = input (historyIdleFlag layout) :=
    writeRegisterValue_apply_outside layout.order value input _ (by
      intro orderIndex equal
      unfold historyIdleFlag at equal
      exact (layout.orderWire_separated orderIndex).2.2.2 _ equal)
  unfold ClassicalReversibleStage.conjunctionDirectBasisAction
    ClassicalReversibleStage.allWiresTrue
    ClassicalReversibleStage.readWires
  simp only [List.map, List.all, id_eq, Bool.and_true]
  rw [branchStable, idleStable]
  exact (writeRegisterValue_xorWire_commute119 layout.order
    (historyActiveWire layout) (by
      intro orderIndex
      rcases List.mem_ofFn.mp (historyActiveWire_mem_workspace layout) with
        ⟨workspaceIndex, member⟩
      intro equal
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm)) value _ input).symm

theorem h3IdleConjunctionBasisAction_replace_coefficient119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Bool) (input : QubitBasis qubits) :
    ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyIdleFlag layout]
        (historyActiveWire layout)
        (replaceQubitWire input layout.coefficientSignal value) =
      replaceQubitWire
        (ClassicalReversibleStage.conjunctionDirectBasisAction
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) input)
        layout.coefficientSignal value := by
  have separated := layout.postGeneratorSignal_separated
    layout.coefficientSignal (by simp)
  have branchNe : historyBranchWire layout ≠ layout.coefficientSignal := by
    rcases List.mem_ofFn.mp (historyBranchWire_mem_workspace layout) with
      ⟨workspaceIndex, member⟩
    exact member.symm ▸ separated.2.2 workspaceIndex
  have idleNe : historyIdleFlag layout ≠ layout.coefficientSignal := by
    unfold historyIdleFlag
    exact separated.2.2 _
  have activeNe : historyActiveWire layout ≠ layout.coefficientSignal := by
    unfold historyActiveWire
    exact separated.2.2 _
  unfold ClassicalReversibleStage.conjunctionDirectBasisAction
    ClassicalReversibleStage.allWiresTrue
    ClassicalReversibleStage.readWires
  simp only [List.map, List.all, id_eq, Bool.and_true]
  rw [replaceQubitWire_outside input layout.coefficientSignal
      (historyBranchWire layout) value branchNe,
    replaceQubitWire_outside input layout.coefficientSignal
      (historyIdleFlag layout) value idleNe]
  exact (replaceQubitWire_xorWire_commute119
    (historyActiveWire layout) layout.coefficientSignal activeNe _ value input).symm

theorem h3IdleTransformDirtyAction119_eq_replace_clean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (binaryLabels : Nat) (input : QubitBasis qubits) :
    h3IdleTransformDirtyAction119 layout binaryLabels input =
      replaceQubitWire
        (h3IdleTransformCleanAction119 layout binaryLabels input)
        layout.coefficientSignal true := by
  have separated := layout.postGeneratorSignal_separated
    layout.coefficientSignal (by simp)
  have timeNe : historyLessThanTimeWire layout ≠
      layout.coefficientSignal := by
    unfold historyLessThanTimeWire
    exact separated.2.2 _
  have idleEndNe : historyLessThanIdleEndWire layout ≠
      layout.coefficientSignal := by
    unfold historyLessThanIdleEndWire
    exact separated.2.2 _
  simp only [h3IdleTransformDirtyAction119, h3IdleTransformCleanAction119]
  rw [h3IdleConjunctionBasisAction_replace_coefficient119]
  rw [replaceQubitWire_outside _ _ (historyLessThanTimeWire layout) _ timeNe]
  rw [← replaceQubitWire_xorWire_commute119
    (historyIdleFlag layout) layout.coefficientSignal (by
      unfold historyIdleFlag
      exact separated.2.2 _) ]
  rw [replaceQubitWire_outside _ _ (historyLessThanIdleEndWire layout) _ idleEndNe]
  rw [← replaceQubitWire_xorWire_commute119
    (historyIdleFlag layout) layout.coefficientSignal (by
      unfold historyIdleFlag
      exact separated.2.2 _) ]

theorem h3BeforeUniform119_idle_clean_values
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    before (historyBranchWire layout) = true ∧
      before (historyLessThanTimeWire layout) = false ∧
      before (historyLessThanIdleEndWire layout) = true ∧
      before (historyIdleFlag layout) = false ∧
      before (historyActiveWire layout) = false ∧
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
  have time : before (historyLessThanTimeWire layout) = false := by
    unfold before h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _
      (historyLessThanTimeWire_ne_activeWire layout)]
    simpa [clockIdle] using
      h3AfterIdleEnd119_time_flag_value source domain fits index
  have idleEnd : before (historyLessThanIdleEndWire layout) = true := by
    unfold before h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _
      (historyLessThanIdleEndWire_ne_activeWire layout)]
    have inside : index.clock.val < source.historyParameters.clockEnd :=
      index.clock.isLt
    simpa [inside] using
      h3AfterIdleEnd119_idle_end_flag_value source domain fits index
  have idle : before (historyIdleFlag layout) = false := by
    calc
      before (historyIdleFlag layout) = logical (historyIdleFlag layout) := by
        unfold before
        exact h3BeforeUniform119_workspace_of_not_live layout logical
          (historyIdleFlag layout) (h3IdleFlag_not_live_idle119 layout)
      _ = false := historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
        layout logical auxiliary _ (by
          unfold historyIdleFlag
          apply historyWorkspaceSlice_wire_mem)
  have active : before (historyActiveWire layout) = false := by
    simpa [before, logical, layout, clockIdle] using
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

theorem h3UniformInverse119_apply_basisKet_idle
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let before := h3BeforeUniform119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h3SelectedBranch119 index)
    applyOperator
        (historyOrderUniformPreparationInverseExactComponent layout
          (ExecutableClockEvidence119 source domain).uniformExternalControl).target
        (basisKet before) = basisKet before := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).uniformExternalControl
  let blockParameters := HistoryRawSchema.parameters203
    (ExecutableRaw119 source).history
    (ExecutableAdmissible119 source domain).analytic
  let parameters := historyOrderUniformPreparationParameters blockParameters
  let controlled := historyOrderUniformExternalControlLayout layout evidence
  let before := h3BeforeUniform119 layout
    (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119 index)
  have clean : externallyControlledCleanWorkPredicate
      (historyOrderUniformExternalControlCleanWorkValid layout evidence) before :=
    h3BeforeUniform119_uniform_work_clean source domain fits index
  have controlFalse : before controlled.control = false := by
    change before (historyActiveWire layout) = false
    exact (h3BeforeUniform119_idle_clean_values
      source domain fits index clockIdle).2.2.2.2.1
  funext output
  have semanticEntry :
      ExternallyControlledPrimitivePlan.strictPlanOperator (fun _ => 0)
          controlled (shuklaVedulaWidthOnlyUniformInversePlan parameters)
          output before =
        externallyControlledWireLiftOperator controlled
          (star (shuklaVedulaWidthOnlyUniformStrictOperator (fun _ => 0)
            parameters)) output before :=
    uniformInverseStrict_clean_entry119 parameters controlled
      (historyOrderUniformExternalControlCleanWorkValid layout evidence)
      output before clean
  rw [applyOperator_basisKet,
    historyOrderUniformPreparationInverseExactComponent_target]
  change ExternallyControlledPrimitivePlan.strictPlanOperator (fun _ => 0)
      controlled (shuklaVedulaWidthOnlyUniformInversePlan parameters)
      output before = basisKet before output
  rw [semanticEntry]
  unfold externallyControlledWireLiftOperator
  rw [if_neg (by simp [controlFalse])]
  simp [basisKet]

theorem h3IdleTransformCleanAction119_eq_zero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (finalLabel : index.state.label.val + 1 =
      source.historyParameters.binaryLabels) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    h3IdleTransformCleanAction119 layout
        source.historyParameters.binaryLabels before =
      h3ZeroOrder119 layout before := by
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
    funext wire
    simp [xorWire]
  have afterEndBranch : afterEnd (historyBranchWire layout) = true := by
    unfold afterEnd
    rw [xorWire_apply_other]
    · exact beforeBranch
    · exact (h3IdleFlag_ne_branch_idle119 layout).symm
  have afterEndIdle : afterEnd (historyIdleFlag layout) = true := by
    simp [afterEnd, xorWire, beforeIdleEnd, beforeIdle]
  have afterEndActive : afterEnd (historyActiveWire layout) = false := by
    unfold afterEnd
    rw [xorWire_apply_other _ _ (h3IdleFlag_ne_active_idle119 layout).symm]
    exact beforeActive
  have afterConjunctionActive :
      afterConjunction (historyActiveWire layout) = true := by
    unfold afterConjunction
    rw [afterTimeEq]
    simp [ClassicalReversibleStage.conjunctionDirectBasisAction,
      ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires, xorWire, afterEndBranch,
      afterEndIdle, afterEndActive]
  have labelEq : index.state.label.val =
      source.historyParameters.binaryLabels - 1 := by
    have positive := source.historyWellFormed.binaryLabels_pos
    omega
  have afterConjunctionOrder (orderIndex : Fin
      (historyOrderWidth source.historyParameters.taylorOrder)) :
      afterConjunction (layout.order.wire orderIndex) =
        (source.historyParameters.binaryLabels - 1).testBit orderIndex.val := by
    have orderNeActive : layout.order.wire orderIndex ≠
        historyActiveWire layout := by
      rcases List.mem_ofFn.mp (historyActiveWire_mem_workspace layout) with
        ⟨workspaceIndex, member⟩
      intro equal
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm)
    have orderNeIdle : layout.order.wire orderIndex ≠
        historyIdleFlag layout := by
      unfold historyIdleFlag
      exact (layout.orderWire_separated orderIndex).2.2.2 _
    calc
      afterConjunction (layout.order.wire orderIndex) =
          afterTime (layout.order.wire orderIndex) := by
        unfold afterConjunction
        rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other]
        exact orderNeActive
      _ = afterEnd (layout.order.wire orderIndex) := by rw [afterTimeEq]
      _ = before (layout.order.wire orderIndex) := by
        unfold afterEnd
        rw [xorWire_apply_other _ _ orderNeIdle]
      _ = (layout.order.read before) orderIndex := rfl
      _ = (layout.order.read logical) orderIndex := by
        rw [h3BeforeUniform119_read_order]
      _ = (orderBits119 source fits index) orderIndex := by
        rw [correctedBranchHistoryBasis119_read_order]
      _ = index.state.label.val.testBit orderIndex.val := rfl
      _ = (source.historyParameters.binaryLabels - 1).testBit orderIndex.val := by
        rw [labelEq]
  have afterOrderEq : afterOrder =
      writeRegisterValue layout.order 0 afterConjunction := by
    exact h3CnotTargetsBasisAction119_repaired_final_eq_zero
      layout (ExecutableClockEvidence119 source domain).idleTransform
      source.historyParameters.binaryLabels afterConjunction
      afterConjunctionActive afterConjunctionOrder
  have afterRestoreEq : afterRestoreConjunction =
      writeRegisterValue layout.order 0 afterTime := by
    unfold afterRestoreConjunction
    rw [afterOrderEq, h3IdleConjunctionBasisAction_write_order119]
    rw [h3IdleConjunctionBasisAction_involutive119]
  have afterRestoreTime :
      afterRestoreConjunction (historyLessThanTimeWire layout) = false := by
    rw [afterRestoreEq]
    rw [writeRegisterValue_apply_outside]
    · rw [afterTimeEq]
      exact afterEndTime
    · intro orderIndex equal
      rcases List.mem_ofFn.mp (historyLessThanTimeWire_mem_workspace layout) with
        ⟨workspaceIndex, member⟩
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm)
  have afterTimeRestoreEq : afterTimeRestore = afterRestoreConjunction := by
    unfold afterTimeRestore
    rw [afterRestoreTime]
    funext wire
    simp [xorWire]
  unfold h3IdleTransformCleanAction119 h3ZeroOrder119
  change xorWire (historyIdleFlag layout)
      (afterTimeRestore (historyLessThanIdleEndWire layout))
      afterTimeRestore = writeRegisterValue layout.order 0 before
  rw [afterTimeRestoreEq, afterRestoreEq]
  have restoredIdleEnd :
      writeRegisterValue layout.order 0 afterTime
          (historyLessThanIdleEndWire layout) = true := by
    rw [writeRegisterValue_apply_outside]
    · rw [afterTimeEq]
      unfold afterEnd
      rw [xorWire_apply_other]
      · exact beforeIdleEnd
      · intro equal
        exact (ExecutableClockEvidence119 source domain).idleTransform.idleEnd_ne_idle
          equal
    · intro orderIndex equal
      rcases List.mem_ofFn.mp
        (historyLessThanIdleEndWire_mem_workspace layout) with
        ⟨workspaceIndex, member⟩
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm)
  rw [restoredIdleEnd]
  rw [← writeRegisterValue_xorWire_commute119 layout.order
    (historyIdleFlag layout) (by
      intro orderIndex
      unfold historyIdleFlag
      exact (layout.orderWire_separated orderIndex).2.2.2 _) 0 true afterTime]
  congr 1
  rw [afterTimeEq]
  unfold afterEnd
  rw [beforeIdleEnd]
  funext wire
  simp [xorWire]

end
end ExecutableHistoryExecutableHistory
