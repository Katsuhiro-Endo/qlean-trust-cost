import QLean.History.Implementation.HistoryPipelineH3IdleGeneralColumn

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
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

/-- The clean idle transform XORs the logical label with the repaired
constant `binaryLabels - 1` in the physical order register. -/
theorem h3IdleTransformCleanAction119_read_order_xor
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    layout.order.read
        (h3IdleTransformCleanAction119 layout
          source.historyParameters.binaryLabels before) =
      fun orderIndex =>
        (index.state.label.val ^^^
          (source.historyParameters.binaryLabels - 1)).testBit orderIndex.val := by
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
    · intro equal
      change layout.workspace.wire _ = layout.workspace.wire _ at equal
      have indexEqual := layout.workspace.injective equal
      have valuesEqual := congrArg Fin.val indexEqual
      dsimp at valuesEqual
      have sharedAtLeast : 5 ≤ historySharedPoolWidth
          (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic)
          (ExecutableRaw119 source).history.generatorWorkWidth := by
        calc
          5 ≤ historyStructuralPoolWidth
              (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
                (ExecutableAdmissible119 source domain).analytic) := by
            unfold historyStructuralPoolWidth
            omega
          _ ≤ historySharedPoolWidth _ _ := Nat.le_max_right _ _
      omega
  have afterEndIdle : afterEnd (historyIdleFlag layout) = true := by
    simp [afterEnd, xorWire, beforeIdleEnd, beforeIdle]
  have afterEndActive : afterEnd (historyActiveWire layout) = false := by
    unfold afterEnd
    rw [xorWire_apply_other]
    · exact beforeActive
    · intro equal
      change layout.workspace.wire _ = layout.workspace.wire _ at equal
      have indexEqual := layout.workspace.injective equal
      have valuesEqual := congrArg Fin.val indexEqual
      dsimp at valuesEqual
      have sharedAtLeast : 5 ≤ historySharedPoolWidth
          (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic)
          (ExecutableRaw119 source).history.generatorWorkWidth := by
        calc
          5 ≤ historyStructuralPoolWidth
              (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
                (ExecutableAdmissible119 source domain).analytic) := by
            unfold historyStructuralPoolWidth
            omega
          _ ≤ historySharedPoolWidth _ _ := Nat.le_max_right _ _
      omega
  have afterConjunctionActive :
      afterConjunction (historyActiveWire layout) = true := by
    simp [afterConjunction,
      ClassicalReversibleStage.conjunctionDirectBasisAction,
      ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires, xorWire, afterTimeEq, afterEndBranch,
      afterEndIdle, afterEndActive]
  funext orderIndex
  have orderNeIdle : layout.order.wire orderIndex ≠ historyIdleFlag layout := by
    unfold historyIdleFlag
    exact (layout.orderWire_separated orderIndex).2.2.2 _
  have orderNeActive : layout.order.wire orderIndex ≠
      historyActiveWire layout := by
    unfold historyActiveWire
    exact (layout.orderWire_separated orderIndex).2.2.2 _
  have afterConjunctionOrder :
      afterConjunction (layout.order.wire orderIndex) =
        index.state.label.val.testBit orderIndex.val := by
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
  have afterOrderBit : afterOrder (layout.order.wire orderIndex) =
      (index.state.label.val ^^^
        (source.historyParameters.binaryLabels - 1)).testBit orderIndex.val := by
    unfold afterOrder
    rw [h3CnotTargetsBasisAction119_apply_of_control_true]
    · simp only [repairedH3IdleOrderTargets119_order_mem_iff]
      rw [afterConjunctionOrder, Nat.testBit_xor]
      cases index.state.label.val.testBit orderIndex.val <;>
        cases (source.historyParameters.binaryLabels - 1).testBit orderIndex.val <;>
        rfl
    · exact repairedH3IdleOrderTargets119_nodup layout
        source.historyParameters.binaryLabels
    · intro target member
      exact (ExecutableClockEvidence119 source domain).idleTransform.active_ne_order
        target (repairedH3IdleOrderTargets119_mem_order layout
          source.historyParameters.binaryLabels target member)
    · exact afterConjunctionActive
  unfold h3IdleTransformCleanAction119
  change xorWire (historyIdleFlag layout)
      (afterTimeRestore (historyLessThanIdleEndWire layout))
      afterTimeRestore (layout.order.wire orderIndex) = _
  rw [xorWire_apply_other _ _ orderNeIdle]
  unfold afterTimeRestore
  rw [xorWire_apply_other _ _ orderNeIdle]
  unfold afterRestoreConjunction
  rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other]
  exact afterOrderBit
  exact orderNeActive

end
end ExecutableHistoryExecutableHistory
