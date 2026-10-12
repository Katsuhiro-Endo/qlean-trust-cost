import QLean.History.Implementation.HistoryPipelineH2OrderTransport

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

theorem h2AfterIdleEnd119_read_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    layout.order.read (h2AfterIdleEnd119 layout input) =
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
  change h2AfterIdleEnd119 layout input (layout.order.wire orderIndex) =
    input (layout.order.wire orderIndex)
  unfold h2AfterIdleEnd119 h2AfterTime119 h2AfterSelector119
    historyTaylorIdleEndComparisonBasisAction
    historyTaylorTimeComparisonBasisAction
    historyTaylorSelectorEqualityBasisAction
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [xorWire_apply_other _ _ idleNe,
    xorWire_apply_other _ _ timeNe,
    xorWire_apply_other _ _ branchNe]

theorem h2AfterIdleEnd119_coefficientSignal119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    h2AfterIdleEnd119 layout input layout.coefficientSignal =
      input layout.coefficientSignal := by
  have separated := layout.postGeneratorSignal_separated
    layout.coefficientSignal (by simp)
  have branchNe : layout.coefficientSignal ≠ historyBranchWire layout := by
    have member := historyBranchWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
    intro equal
    exact separated.2.2 workspaceIndex (member.trans equal.symm)
  have timeNe : layout.coefficientSignal ≠ historyLessThanTimeWire layout := by
    have member := historyLessThanTimeWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
    intro equal
    exact separated.2.2 workspaceIndex (member.trans equal.symm)
  have idleNe : layout.coefficientSignal ≠ historyLessThanIdleEndWire layout := by
    have member := historyLessThanIdleEndWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
    intro equal
    exact separated.2.2 workspaceIndex (member.trans equal.symm)
  unfold h2AfterIdleEnd119 h2AfterTime119 h2AfterSelector119
    historyTaylorIdleEndComparisonBasisAction
    historyTaylorTimeComparisonBasisAction
    historyTaylorSelectorEqualityBasisAction
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [xorWire_apply_other _ _ idleNe,
    xorWire_apply_other _ _ timeNe,
    xorWire_apply_other _ _ branchNe]

theorem h2AfterIdleEnd119_postStable119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    historyTaylorPostGeneratorStablePredicate
        (ExecutableLayout119 source domain)
        (h2AfterIdleEnd119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits branch index)) := by
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
  refine ⟨afterIdle.1, afterIdle.2.1, afterIdle.2.2.1, ?_⟩
  intro workspaceIndex outside
  apply afterIdle.2.2.2 workspaceIndex
  intro member
  apply outside
  exact List.mem_append_left _ member

theorem historyTaylorOrderLessThanTaylorOrderValue_h2AfterIdleEnd119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (labelLt : index.state.label.val < source.historyParameters.taylorOrder) :
    historyTaylorOrderLessThanTaylorOrderValue
        (ExecutableLayout119 source domain)
        (h2AfterIdleEnd119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits branch index)) =
      true := by
  let width := historyOrderWidth source.historyParameters.taylorOrder
  have widthEq : width = Nat.log2 source.historyParameters.taylorOrder + 1 := by
    unfold width historyOrderWidth
    omega
  have orderBound : source.historyParameters.taylorOrder < 2 ^ width := by
    rw [widthEq]
    exact Nat.lt_log2_self
  let orderEncoded : QubitBasis width :=
    qubitBasisOfLittleEndianIndex
      ⟨source.historyParameters.taylorOrder, orderBound⟩
  have constantBits :
      (fun bit : Fin width =>
        source.historyParameters.taylorOrder.testBit bit.val) = orderEncoded := by
    funext bit
    rfl
  have orderEncodedValue :
      qubitBasisLittleEndianIndex width orderEncoded =
        source.historyParameters.taylorOrder := by
    dsimp only [orderEncoded]
    exact qubitBasisLittleEndianIndex_basis
      ⟨source.historyParameters.taylorOrder, orderBound⟩
  unfold historyTaylorOrderLessThanTaylorOrderValue
  rw [unsignedLessThanBits_eq_decide_lt]
  change decide
    (qubitBasisLittleEndianIndex width
        ((ExecutableLayout119 source domain).order.read
          (h2AfterIdleEnd119 (ExecutableLayout119 source domain)
            (correctedBranchHistoryBasis119 source domain fits branch index))) <
      qubitBasisLittleEndianIndex width
        (fun bit : Fin width =>
          source.historyParameters.taylorOrder.testBit bit.val)) = true
  rw [h2AfterIdleEnd119_read_order119,
    correctedBranchHistoryBasis119_read_order, constantBits]
  simp only [orderBits119, qubitBasisLittleEndianIndex_basis]
  rw [orderEncodedValue]
  simp [labelLt]

theorem registerValue_h2AfterIdleEnd_correctedBranch119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    registerValue (ExecutableLayout119 source domain).order
        (h2AfterIdleEnd119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits branch index)) =
      index.state.label.val := by
  unfold registerValue
  rw [h2AfterIdleEnd119_read_order119,
    correctedBranchHistoryBasis119_read_order]
  dsimp only [orderBits119]
  exact qubitBasisLittleEndianIndex_basis _

theorem correctedBranchHistoryBasis119_coefficientSignal_false119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    correctedBranchHistoryBasis119 source domain fits branch index
        (ExecutableLayout119 source domain).coefficientSignal = false := by
  have separated := (ExecutableLayout119 source domain).postGeneratorSignal_separated
    (ExecutableLayout119 source domain).coefficientSignal (by simp)
  rw [correctedBranchHistoryBasis119_apply_of_not_selector]
  · apply executableHistoryBasis119_apply_of_tail_mem
    change (ExecutableLayout119 source domain).coefficientSignal ∈
      historyRegisterWires (ExecutableLayout119 source domain).generatorSignal ++
        [(ExecutableLayout119 source domain).coefficientSignal,
          (ExecutableLayout119 source domain).orderBoundarySignal,
          (ExecutableLayout119 source domain).projectorSignal,
          (ExecutableLayout119 source domain).clockBoundarySignal] ++
        historyRegisterWires (ExecutableLayout119 source domain).workspace
    simp
  · intro member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨selectorIndex, equal⟩
    exact separated.1 selectorIndex equal

theorem applyOperator_h2PostOperator_active_taylor119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (labelTaylor : index.state.label.val < source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let logicalInput := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119
      (replaceConfiguration119 source index configuration)
    let logicalOutput := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119
      (raiseHistoryLabel119 source index configuration labelTaylor)
    VerifiedCircuitCore.applyOperator
        (h2PostOperator119 layout
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout logicalInput)) =
      ((Real.cos
          ((correctedTaylorCoefficientAngle119 source.toCommonSource119
            index.state.label.val).uniformValue / 2) : Real) : Complex) •
          VerifiedCircuitCore.basisKet logicalOutput +
        ((Real.sin
          ((correctedTaylorCoefficientAngle119 source.toCommonSource119
            index.state.label.val).uniformValue / 2) : Real) : Complex) •
          VerifiedCircuitCore.basisKet (replaceQubitWire logicalOutput
            layout.coefficientSignal true) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let oldIndex := replaceConfiguration119 source index configuration
  let newIndex := raiseHistoryLabel119 source index configuration labelTaylor
  let logicalInput := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 oldIndex
  let logicalOutput := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 newIndex
  let stable := h2AfterIdleEnd119 layout logicalInput
  let incremented := h2AfterIdleEnd119 layout logicalOutput
  have taylorOrderEq :
      (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic).taylorOrder =
        source.historyParameters.taylorOrder := by
    rfl
  let selected : Fin
      (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic).taylorOrder :=
    ⟨index.state.label.val, by rw [taylorOrderEq]; exact labelTaylor⟩
  have branchStable : stable (historyBranchWire layout) = true := by
    exact h2AfterIdleEnd119_branch_flag_selected source domain fits oldIndex
  have timeFlagStable : stable (historyLessThanTimeWire layout) = true := by
    exact h2AfterIdleEnd119_time_flag_active source domain fits oldIndex
      (by simpa [oldIndex] using clockActive)
  have idleFlagStable : stable (historyLessThanIdleEndWire layout) = true := by
    exact h2AfterIdleEnd119_idle_flag_active source domain fits oldIndex
      (by simpa [oldIndex] using clockActive)
  have stablePredicate : historyTaylorPostGeneratorStablePredicate layout stable :=
    h2AfterIdleEnd119_postStable119 source domain fits h2SelectedBranch119 oldIndex
  have clockTrue : historyTaylorClockLessThanTimeValue layout stable = true := by
    rw [← stablePredicate.2.1]
    exact timeFlagStable
  have idleClockTrue :
      historyTaylorClockLessThanIdleEndValue layout stable = true := by
    rw [← stablePredicate.2.2.1]
    exact idleFlagStable
  have orderLess : historyTaylorOrderLessThanTaylorOrderValue layout stable =
      true := by
    exact historyTaylorOrderLessThanTaylorOrderValue_h2AfterIdleEnd119
      source domain fits h2SelectedBranch119 oldIndex
      (by simpa [oldIndex] using labelTaylor)
  have activeStep :
      historyTaylorActiveConjunctionBasisAction layout
          (h2BeforeQ119 layout logicalInput) = stable := by
    exact historyTaylorActiveConjunctionBasisAction_involutive119 layout stable
  have invalidStep :
      historyTaylorInvalidClockBasisAction layout stable = stable := by
    exact historyTaylorInvalidClockBasisAction_selected_active119
      source domain fits oldIndex (by simpa [oldIndex] using clockActive)
  have orderBoundaryStep :
      historyTaylorOrderBoundaryBasisAction layout stable = stable := by
    unfold historyTaylorOrderBoundaryBasisAction
      historyTaylorOrderBoundaryCondition
    rw [branchStable, clockTrue, orderLess]
    simp [xorWire]
  have idleIntervalFalse :
      historyTaylorIdleIntervalCondition layout stable = false := by
    unfold historyTaylorIdleIntervalCondition
    rw [idleClockTrue, clockTrue]
    rfl
  have idleBoundaryStep :
      historyTaylorIdleBoundaryBasisAction layout stable = stable := by
    unfold historyTaylorIdleBoundaryBasisAction
      historyTaylorIdleBoundaryCondition
    rw [branchStable, idleIntervalFalse]
    simp [xorWire]
  have selectedBound :=
    historyTaylorCoefficientIndex_succ_lt_orderPow119
      (parameters := HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic) selected
  have registerValueStable : registerValue layout.order stable =
      selected.val := by
    exact registerValue_h2AfterIdleEnd_correctedBranch119
      source domain fits h2SelectedBranch119 oldIndex
  have degreeCondition :
      historyTaylorDegreeIncrementCondition layout stable = true := by
    simp [historyTaylorDegreeIncrementCondition, branchStable, idleClockTrue]
  have degreeStep :
      historyTaylorDegreeIncrementBasisAction layout stable = incremented := by
    unfold historyTaylorDegreeIncrementBasisAction
      predicateControlledAddMod2PowBasisAction
    rw [if_pos degreeCondition, registerValueStable,
      Nat.mod_eq_of_lt selectedBound]
    exact (h2AfterIdleEnd119_raiseHistoryLabel119 source domain fits
      h2SelectedBranch119 index configuration labelTaylor).symm
  have incrementedPredicate :
      historyTaylorPostGeneratorStablePredicate layout incremented :=
    h2AfterIdleEnd119_postStable119 source domain fits h2SelectedBranch119 newIndex
  have branchIncremented : incremented (historyBranchWire layout) = true := by
    exact h2AfterIdleEnd119_branch_flag_selected source domain fits newIndex
  have timeFlagIncremented :
      incremented (historyLessThanTimeWire layout) = true := by
    exact h2AfterIdleEnd119_time_flag_active source domain fits newIndex
      (by simpa [newIndex] using clockActive)
  have loopClockTrue :
      historyTaylorClockLessThanTimeValue layout incremented = true := by
    rw [← incrementedPredicate.2.1]
    exact timeFlagIncremented
  have loopOrderSelected :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (selected.val + 1) incremented =
        true := by
    have sameOrder :
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order) (selected.val + 1) incremented =
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order) (selected.val + 1)
              logicalOutput := by
      apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
      intro wire member
      simp only [historyRegisterWires, List.mem_ofFn] at member
      rcases member with ⟨orderIndex, rfl⟩
      exact congrFun (h2AfterIdleEnd119_read_order119 layout logicalOutput)
        orderIndex
    rw [sameOrder,
      correctedBranchHistoryBasis119_order_equals source domain fits
        h2SelectedBranch119 newIndex (selected.val + 1) (by
          simpa [historyRegisterWires, layout] using selectedBound)]
    simp [newIndex, selected]
  have loopSignalFalse : incremented layout.coefficientSignal = false := by
    calc
      incremented layout.coefficientSignal =
          logicalOutput layout.coefficientSignal := by
        exact h2AfterIdleEnd119_coefficientSignal119 layout logicalOutput
      _ = false := correctedBranchHistoryBasis119_coefficientSignal_false119
        source domain fits h2SelectedBranch119 newIndex
  have idleCoefficientFalse :
      (incremented (historyBranchWire layout) &&
        historyTaylorIdleIntervalCondition layout incremented) = false := by
    have idleFlagIncremented :
        incremented (historyLessThanIdleEndWire layout) = true := by
      exact h2AfterIdleEnd119_idle_flag_active source domain fits newIndex
        (by simpa [newIndex] using clockActive)
    have idleClockIncremented :
        historyTaylorClockLessThanIdleEndValue layout incremented = true := by
      rw [← incrementedPredicate.2.2.1]
      exact idleFlagIncremented
    unfold historyTaylorIdleIntervalCondition
    rw [idleClockIncremented, loopClockTrue]
    simp
  have idleCoefficientDirtyFalse :
      ((replaceQubitWire incremented layout.coefficientSignal true)
          (historyBranchWire layout) &&
        historyTaylorIdleIntervalCondition layout
          (replaceQubitWire incremented layout.coefficientSignal true)) = false := by
    have separated := layout.postGeneratorSignal_separated
      layout.coefficientSignal (by simp)
    have branchNe : historyBranchWire layout ≠ layout.coefficientSignal := by
      have member := historyBranchWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      exact member.symm ▸ separated.2.2 workspaceIndex
    rw [replaceQubitWire_outside incremented layout.coefficientSignal
      (historyBranchWire layout) true branchNe]
    unfold historyTaylorIdleIntervalCondition
    rw [historyTaylorClockLessThanIdleEndValue_replace_coefficient119,
      historyTaylorClockLessThanTimeValue_replace_coefficient119]
    exact idleCoefficientFalse
  have restoreClean :
      VerifiedCircuitCore.applyOperator
          (operatorSequence
            [historyTaylorIdleEndComparisonOperator layout,
             historyTaylorTimeComparisonOperator layout,
             historyTaylorSelectorEqualityOperator layout])
          (VerifiedCircuitCore.basisKet incremented) =
        VerifiedCircuitCore.basisKet logicalOutput := by
    exact h2RestoreEntryFlags_apply_basisKet119 layout logicalOutput
  have restoreDirty :
      VerifiedCircuitCore.applyOperator
          (operatorSequence
            [historyTaylorIdleEndComparisonOperator layout,
             historyTaylorTimeComparisonOperator layout,
             historyTaylorSelectorEqualityOperator layout])
          (VerifiedCircuitCore.basisKet
            (replaceQubitWire incremented layout.coefficientSignal true)) =
        VerifiedCircuitCore.basisKet
          (replaceQubitWire logicalOutput layout.coefficientSignal true) := by
    rw [← h2AfterIdleEnd119_replace_coefficient119]
    exact h2RestoreEntryFlags_apply_basisKet119 layout
      (replaceQubitWire logicalOutput layout.coefficientSignal true)
  exact applyOperator_h2PostOperator_of_stage_actions119
    layout
    (fun coefficientIndex => correctedTaylorCoefficientAngle119
      source.toCommonSource119 coefficientIndex.val)
    compiledIdleCoefficientAngle119 selected
    (h2BeforeQ119 layout logicalInput) stable incremented logicalOutput
    activeStep invalidStep orderBoundaryStep idleBoundaryStep degreeStep
    branchIncremented loopClockTrue loopOrderSelected loopSignalFalse
    idleCoefficientFalse idleCoefficientDirtyFalse restoreClean restoreDirty

end
end ExecutableHistoryExecutableHistory
