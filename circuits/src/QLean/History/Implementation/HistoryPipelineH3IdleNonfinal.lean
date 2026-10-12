import QLean.History.Implementation.HistoryPipelineH3IdleOrderXor

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
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

private theorem h3ClockWire_ne_projector119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (clockIndex : Fin (historyClockWidth parameters.timeSteps
      parameters.taylorOrder parameters.idlingSteps)) :
    layout.clock.wire clockIndex ≠ layout.projectorSignal := by
  let selectorWires := historyRegisterWires layout.selector
  let dataWires := historyRegisterWires layout.data
  let clockWires := historyRegisterWires layout.clock
  let orderWires := historyRegisterWires layout.order
  let generatorWires := historyRegisterWires layout.generatorSignal
  let reservedWires := [layout.coefficientSignal, layout.orderBoundarySignal,
    layout.projectorSignal, layout.clockBoundarySignal]
  let workspaceWires := historyRegisterWires layout.workspace
  have normalized :
      (selectorWires ++ (dataWires ++ (clockWires ++ (orderWires ++
        (generatorWires ++ (reservedWires ++ workspaceWires)))))).Nodup := by
    simpa [selectorWires, dataWires, clockWires, orderWires, generatorWires,
      reservedWires, workspaceWires, List.append_assoc] using layout.allWiresNodup
  have selectorSplit := List.nodup_append.mp normalized
  have dataSplit := List.nodup_append.mp selectorSplit.2.1
  have clockSplit := List.nodup_append.mp dataSplit.2.1
  exact clockSplit.2.2 _ (List.mem_ofFn.mpr ⟨clockIndex, rfl⟩) _
    (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (by simp [reservedWires]))))

private theorem h3BranchWire_ne_projector119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyBranchWire layout ≠ layout.projectorSignal := by
  rcases List.mem_ofFn.mp (historyBranchWire_mem_workspace layout) with
    ⟨workspaceIndex, equal⟩
  rw [← equal]
  exact h3WorkspaceWire_ne_projector119 layout workspaceIndex

private theorem h3OrderWire_ne_projector119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire index ≠ layout.projectorSignal := by
  let selectorWires := historyRegisterWires layout.selector
  let dataWires := historyRegisterWires layout.data
  let clockWires := historyRegisterWires layout.clock
  let orderWires := historyRegisterWires layout.order
  let generatorWires := historyRegisterWires layout.generatorSignal
  let reservedWires := [layout.coefficientSignal, layout.orderBoundarySignal,
    layout.projectorSignal, layout.clockBoundarySignal]
  let workspaceWires := historyRegisterWires layout.workspace
  have normalized :
      (selectorWires ++ (dataWires ++ (clockWires ++ (orderWires ++
        (generatorWires ++ (reservedWires ++ workspaceWires)))))).Nodup := by
    simpa [selectorWires, dataWires, clockWires, orderWires, generatorWires,
      reservedWires, workspaceWires, List.append_assoc] using layout.allWiresNodup
  have selectorSplit := List.nodup_append.mp normalized
  have dataSplit := List.nodup_append.mp selectorSplit.2.1
  have clockSplit := List.nodup_append.mp dataSplit.2.1
  have orderSplit := List.nodup_append.mp clockSplit.2.1
  exact orderSplit.2.2 _ (List.mem_ofFn.mpr ⟨index, rfl⟩) _
    (List.mem_append_right _
      (List.mem_append_left _ (by simp [reservedWires])))

/-- The corrected logical branch embedding has a clean projector signal. -/
theorem correctedBranchHistoryBasis119_projectorSignal_false119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    correctedBranchHistoryBasis119 source domain fits branch index
        (ExecutableLayout119 source domain).projectorSignal = false := by
  let layout := ExecutableLayout119 source domain
  rw [correctedBranchHistoryBasis119_apply_of_not_selector]
  · apply executableHistoryBasis119_apply_of_tail_mem source domain fits index
    change (ExecutableLayout119 source domain).projectorSignal ∈
      historyRegisterWires
          (ExecutableLayout119 source domain).generatorSignal ++
        [(ExecutableLayout119 source domain).coefficientSignal,
          (ExecutableLayout119 source domain).orderBoundarySignal,
          (ExecutableLayout119 source domain).projectorSignal,
          (ExecutableLayout119 source domain).clockBoundarySignal] ++
        historyRegisterWires
          (ExecutableLayout119 source domain).workspace
    have reservedMember :
        (ExecutableLayout119 source domain).projectorSignal ∈
          [(ExecutableLayout119 source domain).coefficientSignal,
            (ExecutableLayout119 source domain).orderBoundarySignal,
            (ExecutableLayout119 source domain).projectorSignal,
            (ExecutableLayout119 source domain).clockBoundarySignal] :=
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)
    exact List.mem_append_left _
      (List.mem_append_right _ reservedMember)
  · intro selectorMember
    simp only [historyRegisterWires, List.mem_ofFn] at selectorMember
    rcases selectorMember with ⟨selectorIndex, equal⟩
    let selectorWires := historyRegisterWires layout.selector
    let dataWires := historyRegisterWires layout.data
    let clockWires := historyRegisterWires layout.clock
    let orderWires := historyRegisterWires layout.order
    let generatorWires := historyRegisterWires layout.generatorSignal
    let reservedWires := [layout.coefficientSignal, layout.orderBoundarySignal,
      layout.projectorSignal, layout.clockBoundarySignal]
    let workspaceWires := historyRegisterWires layout.workspace
    have normalized :
        (selectorWires ++ (dataWires ++ (clockWires ++ (orderWires ++
          (generatorWires ++ (reservedWires ++ workspaceWires)))))).Nodup := by
      simpa [layout, selectorWires, dataWires, clockWires, orderWires,
        generatorWires, reservedWires, workspaceWires, List.append_assoc] using
        layout.allWiresNodup
    have split := List.nodup_append.mp normalized
    apply split.2.2 (layout.selector.wire selectorIndex)
      (List.mem_ofFn.mpr ⟨selectorIndex, rfl⟩) layout.projectorSignal
    · exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_left _ (by simp [reservedWires])))))
    · exact equal

/-- The clean idle transform does not touch the projector signal. -/
theorem h3IdleTransformCleanAction119_projectorSignal
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (_clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    h3IdleTransformCleanAction119 layout
        source.historyParameters.binaryLabels before layout.projectorSignal = false := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  have branchNe := h3BranchWire_ne_projector119 layout
  have activeNe : historyActiveWire layout ≠ layout.projectorSignal := by
    unfold historyActiveWire
    exact h3WorkspaceWire_ne_projector119 layout _
  have idleNe : historyIdleFlag layout ≠ layout.projectorSignal := by
    unfold historyIdleFlag
    exact h3WorkspaceWire_ne_projector119 layout _
  have timeNe : historyLessThanTimeWire layout ≠ layout.projectorSignal := by
    unfold historyLessThanTimeWire
    exact h3WorkspaceWire_ne_projector119 layout _
  have idleEndNe : historyLessThanIdleEndWire layout ≠
      layout.projectorSignal := by
    unfold historyLessThanIdleEndWire
    exact h3WorkspaceWire_ne_projector119 layout _
  have beforeProjector : before layout.projectorSignal = false := by
    unfold before h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
      h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
      h3AfterTime119 historyTaylorTimeComparisonBasisAction
      h3AfterSelector119
      ClassicalReversibleStage.equalityToConstantDirectBasisAction
    rw [xorWire_apply_other _ _ activeNe.symm,
      xorWire_apply_other _ _ idleEndNe.symm,
      xorWire_apply_other _ _ timeNe.symm,
      xorWire_apply_other _ _ branchNe.symm]
    exact correctedBranchHistoryBasis119_projectorSignal_false119
      source domain fits h3SelectedBranch119 index
  change h3IdleTransformCleanAction119 layout
    source.historyParameters.binaryLabels before layout.projectorSignal = false
  unfold h3IdleTransformCleanAction119
  rw [xorWire_apply_other _ _ idleNe.symm,
    xorWire_apply_other _ _ idleNe.symm]
  rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other]
  · rw [h3CnotTargetsBasisAction119_apply_outside]
    · rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other]
      · rw [xorWire_apply_other _ _ idleNe.symm,
          xorWire_apply_other _ _ idleNe.symm]
        exact beforeProjector
      · exact activeNe.symm
    · intro target member
      have orderMember := repairedH3IdleOrderTargets119_mem_order
        layout source.historyParameters.binaryLabels target member
      simp only [historyRegisterWires, List.mem_ofFn] at orderMember
      rcases orderMember with ⟨orderIndex, rfl⟩
      exact h3OrderWire_ne_projector119 layout orderIndex
  · exact activeNe.symm

/-- Closed formula for the projector signal of the classical H3 suffix. -/
theorem h3ActiveTailBasisAction119_projectorSignal
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits) :
    let layout := ExecutableLayout119 source domain
    h3ActiveTailBasisAction119 source domain input layout.projectorSignal =
      (input layout.projectorSignal !=
        (input (historyBranchWire layout) &&
          !ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order) 0 input)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  let afterActive := historyTaylorActiveConjunctionBasisAction layout input
  let afterIdle := historyTaylorIdleEndComparisonBasisAction layout afterActive
  let afterTime := historyTaylorTimeComparisonBasisAction layout afterIdle
  let afterProjector := h3I06BasisAction layout afterTime
  have branchNeActive := historyBranchWire_ne_activeWire layout
  have branchNeIdle := historyBranchWire_ne_lessThanIdleEndWire layout
  have branchNeTime := historyBranchWire_ne_lessThanTimeWire layout
  have afterTimeBranch : afterTime (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    unfold afterTime historyTaylorTimeComparisonBasisAction
      afterIdle historyTaylorIdleEndComparisonBasisAction
      afterActive historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _ branchNeTime,
      xorWire_apply_other _ _ branchNeIdle,
      xorWire_apply_other _ _ branchNeActive]
  have afterTimeOrder :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 afterTime =
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 input := by
    apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
    intro wire member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨orderIndex, rfl⟩
    have orderNeActive : layout.order.wire orderIndex ≠
        historyActiveWire layout := by
      unfold historyActiveWire
      exact (layout.orderWire_separated orderIndex).2.2.2 _
    have orderNeIdle : layout.order.wire orderIndex ≠
        historyLessThanIdleEndWire layout := by
      unfold historyLessThanIdleEndWire
      exact (layout.orderWire_separated orderIndex).2.2.2 _
    have orderNeTime : layout.order.wire orderIndex ≠
        historyLessThanTimeWire layout := by
      unfold historyLessThanTimeWire
      exact (layout.orderWire_separated orderIndex).2.2.2 _
    unfold afterTime historyTaylorTimeComparisonBasisAction
      afterIdle historyTaylorIdleEndComparisonBasisAction
      afterActive historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _ orderNeTime,
      xorWire_apply_other _ _ orderNeIdle,
      xorWire_apply_other _ _ orderNeActive]
  have projectorNeActive : historyActiveWire layout ≠ layout.projectorSignal := by
    unfold historyActiveWire
    exact h3WorkspaceWire_ne_projector119 layout _
  have projectorNeIdle : historyLessThanIdleEndWire layout ≠
      layout.projectorSignal := by
    unfold historyLessThanIdleEndWire
    exact h3WorkspaceWire_ne_projector119 layout _
  have projectorNeTime : historyLessThanTimeWire layout ≠
      layout.projectorSignal := by
    unfold historyLessThanTimeWire
    exact h3WorkspaceWire_ne_projector119 layout _
  have afterTimeProjector : afterTime layout.projectorSignal =
      input layout.projectorSignal := by
    unfold afterTime historyTaylorTimeComparisonBasisAction
      afterIdle historyTaylorIdleEndComparisonBasisAction
      afterActive historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _ projectorNeTime.symm,
      xorWire_apply_other _ _ projectorNeIdle.symm,
      xorWire_apply_other _ _ projectorNeActive.symm]
  have afterProjectorValue : afterProjector layout.projectorSignal =
      (input layout.projectorSignal !=
        (input (historyBranchWire layout) &&
          !ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order) 0 input)) := by
    unfold afterProjector h3I06BasisAction h3I06ProjectorPredicate
    simp [xorWire, afterTimeBranch, afterTimeOrder, afterTimeProjector]
  have afterClockValue : controlledAddConstantMod2PowBasisAction
      (historyControlledClockIncrementSpec layout clock.controlledIncrement)
      afterProjector layout.projectorSignal = afterProjector layout.projectorSignal := by
    apply controlledAddConstantMod2PowBasisAction_apply_outside
    intro clockIndex equal
    exact h3ClockWire_ne_projector119 layout clockIndex equal.symm
  change xorWire (historyBranchWire layout)
      (ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 2
        (controlledAddConstantMod2PowBasisAction
          (historyControlledClockIncrementSpec layout clock.controlledIncrement)
          afterProjector))
      (controlledAddConstantMod2PowBasisAction
        (historyControlledClockIncrementSpec layout clock.controlledIncrement)
        afterProjector) layout.projectorSignal = _
  rw [xorWire_apply_other _ _ (h3BranchWire_ne_projector119 layout).symm]
  rw [afterClockValue, afterProjectorValue]

/-- A non-final idle label produces a nonzero physical order word, hence H3
raises the projector signal and has no clean logical output. -/
theorem repairedH3RecordedTarget119_idle_nonfinal_all_rows
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (nonFinal : ¬ inputIndex.state.label.val + 1 =
      source.historyParameters.binaryLabels) :
    repairedH3RecordedTarget119 source domain
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          outputIndex)
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          inputIndex) =
      (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
          outputIndex inputIndex : Real) : Complex)) := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 inputIndex
  let row := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 outputIndex
  let before := h3BeforeUniform119 layout input
  let clean := h3IdleTransformCleanAction119 layout
    source.historyParameters.binaryLabels before
  let cleanOutput := h3ActiveTailBasisAction119 source domain clean
  let xorValue := inputIndex.state.label.val ^^^
    (source.historyParameters.binaryLabels - 1)
  have labelNe : inputIndex.state.label.val ≠
      source.historyParameters.binaryLabels - 1 := by
    intro equal
    have positive := source.historyWellFormed.binaryLabels_pos
    omega
  have xorNonzero : xorValue ≠ 0 := by
    intro equal
    exact labelNe (Nat.xor_eq_zero_iff.mp equal)
  have labelFits : inputIndex.state.label.val <
      2 ^ historyOrderWidth source.historyParameters.taylorOrder :=
    lt_of_lt_of_le inputIndex.state.label.isLt fits.label_fits
  have maskFits : source.historyParameters.binaryLabels - 1 <
      2 ^ historyOrderWidth source.historyParameters.taylorOrder := by
    have positive := source.historyWellFormed.binaryLabels_pos
    exact lt_of_lt_of_le (Nat.sub_lt (by omega) (by omega)) fits.label_fits
  have xorFits : xorValue <
      2 ^ historyOrderWidth source.historyParameters.taylorOrder :=
    Nat.xor_lt_two_pow labelFits maskFits
  have orderRead := h3IdleTransformCleanAction119_read_order_xor
    source domain fits inputIndex clockIdle
  have orderPredicateFalse :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) 0 clean = false := by
    have predicateCongr :
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order) 0 clean =
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order) 0
            (writeRegisterValue layout.order xorValue before) := by
      apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
      intro wire member
      simp only [historyRegisterWires, List.mem_ofFn] at member
      rcases member with ⟨orderIndex, rfl⟩
      have bitEq := congrFun orderRead orderIndex
      change clean (layout.order.wire orderIndex) = _ at bitEq
      rw [bitEq, writeRegisterValue_apply_wire]
    rw [predicateCongr]
    rw [ClassicalReversibleStage.littleEndianRegisterEqualsNat_eq_decide
      (historyRegisterWires layout.order) 0
      (writeRegisterValue layout.order xorValue before) (by positivity)]
    have listValue :
        ClassicalReversibleStage.littleEndianListNat
            (ClassicalReversibleStage.readWires
              (historyRegisterWires layout.order)
              (writeRegisterValue layout.order xorValue before)) = xorValue := by
      simp only [ClassicalReversibleStage.readWires, historyRegisterWires,
        List.map_ofFn]
      change ClassicalReversibleStage.littleEndianListNat
          (List.ofFn (layout.order.read
            (writeRegisterValue layout.order xorValue before))) = xorValue
      rw [littleEndianListNat_ofFn119]
      exact registerValue_writeRegisterValue_of_lt119 layout.order
        xorValue before xorFits
    rw [listValue]
    simp [xorNonzero]
  have cleanProjector : clean layout.projectorSignal = false := by
    exact h3IdleTransformCleanAction119_projectorSignal
      source domain fits inputIndex clockIdle
  have cleanBranch : clean (historyBranchWire layout) = true := by
    have branchMember := historyBranchWire_mem_workspace layout
    have preserved := h3IdleTransformCleanAction119_workspace
      source domain fits inputIndex clockIdle _ branchMember
    change clean (historyBranchWire layout) =
      before (historyBranchWire layout) at preserved
    rw [preserved]
    exact (h3BeforeUniform119_idle_clean_values
      source domain fits inputIndex clockIdle).1
  have cleanOutputProjector : cleanOutput layout.projectorSignal = true := by
    have formula := h3ActiveTailBasisAction119_projectorSignal
      source domain clean
    change cleanOutput layout.projectorSignal = _ at formula
    rw [formula, cleanProjector, cleanBranch, orderPredicateFalse]
    decide
  have rowProjector : row layout.projectorSignal = false :=
    correctedBranchHistoryBasis119_projectorSignal_false119
      source domain fits h3SelectedBranch119 outputIndex
  have rowNe : row ≠ cleanOutput := by
    intro equal
    have atProjector := congrFun equal layout.projectorSignal
    rw [rowProjector, cleanOutputProjector] at atProjector
    contradiction
  rw [repairedH3RecordedTarget119_idle_general_clean_logical_entry
    source domain fits inputIndex outputIndex clockIdle]
  rw [if_neg rowNe]
  have correctedZero :
      (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
          outputIndex inputIndex : Real) : Complex)) = 0 := by
    change ((((Real.sqrt
        (source.historyParameters.taylorOrder + 1))⁻¹ *
        ((HistoryBlockEncoding.HistorySpec.L2 source.historyParameters
          outputIndex inputIndex : Rat) : Real) : Real) : Complex)) = 0
    unfold HistoryBlockEncoding.HistorySpec.L2
    by_cases clockEq : outputIndex.clock.val = inputIndex.clock.val + 1
    · rw [if_pos clockEq, if_neg clockIdle]
      unfold HistoryBlockEncoding.HistorySpec.fBin
      rw [if_neg]
      · norm_num
      · intro condition
        exact nonFinal condition.2.1
    · rw [if_neg clockEq]
      norm_num
  rw [correctedZero]

end
end ExecutableHistoryExecutableHistory
