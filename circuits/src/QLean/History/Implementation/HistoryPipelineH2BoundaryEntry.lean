import QLean.History.Implementation.HistoryPipelineH2IdleFullRange

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
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

/-- Wires which may be written strictly after the two H2 boundary tests. -/
def h2AfterBoundarySupport119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Finset (Fin qubits) :=
  Finset.univ.image layout.order.wire ∪
    {layout.coefficientSignal, historyActiveWire layout,
      historyLessThanIdleEndWire layout, historyLessThanTimeWire layout,
      historyBranchWire layout}

/-- Suffix of H2 beginning immediately after the idle-boundary test. -/
def h2AfterBoundaryOperator119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr) :
    VerifiedCircuitCore.Operator (QubitBasis qubits) :=
  operatorSequence
    [historyTaylorDegreeIncrementOperator layout,
     historyTaylorCoefficientLoopOperator layout angles,
     historyTaylorIdleCoefficientOperator layout idleAngle,
     operatorSequence
       [historyTaylorIdleEndComparisonOperator layout,
        historyTaylorTimeComparisonOperator layout,
        historyTaylorSelectorEqualityOperator layout]]

theorem h2AfterBoundaryOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr) :
    OperatorPreservesOutside (h2AfterBoundarySupport119 layout)
      (h2AfterBoundaryOperator119 layout angles idleAngle) := by
  unfold h2AfterBoundaryOperator119
  apply OperatorPreservesOutside.operatorSequence_of_forall
  intro operator member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact (historyTaylorDegreeIncrementOperator_local119 layout).mono (by
      intro wire wireMember
      exact Finset.mem_union_left _ wireMember)
  · exact (historyTaylorCoefficientLoopOperator_local119 layout angles).mono (by
      intro wire wireMember
      simp only [Finset.mem_singleton] at wireMember
      subst wire
      simp [h2AfterBoundarySupport119])
  · exact (historyTaylorIdleCoefficientOperator_local119 layout idleAngle).mono (by
      intro wire wireMember
      simp only [Finset.mem_singleton] at wireMember
      subst wire
      simp [h2AfterBoundarySupport119])
  · apply OperatorPreservesOutside.operatorSequence_of_forall
    intro restore restoreMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at restoreMember
    rcases restoreMember with rfl | rfl | rfl
    · exact (historyTaylorIdleEndComparisonOperator_local119 layout).mono (by
        intro wire wireMember
        simp only [Finset.mem_singleton] at wireMember
        subst wire
        simp [h2AfterBoundarySupport119])
    · exact (historyTaylorTimeComparisonOperator_local119 layout).mono (by
        intro wire wireMember
        simp only [Finset.mem_singleton] at wireMember
        subst wire
        simp [h2AfterBoundarySupport119])
    · exact (historyTaylorSelectorEqualityOperator_local119 layout).mono (by
        intro wire wireMember
        simp only [Finset.mem_singleton] at wireMember
        subst wire
        simp [h2AfterBoundarySupport119])

/-- Algebraic cut of the H2 word immediately after both deterministic
boundary tests.  Keeping this independent of the executable-history data makes
the later boundary proofs small enough for deterministic kernel checking. -/
theorem applyOperator_h2PostOperator_to_afterBoundary119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr)
    (before stable dirty : QubitBasis qubits)
    (activeStep :
      historyTaylorActiveConjunctionBasisAction layout before = stable)
    (invalidStep :
      historyTaylorInvalidClockBasisAction layout stable = stable)
    (orderBoundaryStep :
      historyTaylorOrderBoundaryBasisAction layout stable = dirty)
    (idleBoundaryStep :
      historyTaylorIdleBoundaryBasisAction layout dirty = dirty) :
    VerifiedCircuitCore.applyOperator
        (h2PostOperator119 layout angles idleAngle)
        (VerifiedCircuitCore.basisKet before) =
      VerifiedCircuitCore.applyOperator
        (h2AfterBoundaryOperator119 layout angles idleAngle)
        (VerifiedCircuitCore.basisKet dirty) := by
  unfold h2PostOperator119 h2AfterBoundaryOperator119
  simp only [operatorSequence, applyOperator_mul, Matrix.one_mul]
  rw [historyTaylorActiveConjunctionOperator,
    applyOperator_deterministicOperator_basisKet, activeStep]
  rw [historyTaylorInvalidClockOperator,
    applyOperator_deterministicOperator_basisKet, invalidStep]
  rw [historyTaylorOrderBoundaryOperator,
    applyOperator_deterministicOperator_basisKet, orderBoundaryStep]
  rw [historyTaylorIdleBoundaryOperator,
    applyOperator_deterministicOperator_basisKet, idleBoundaryStep]

theorem coefficientSignal_ne_orderBoundarySignal119
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters) :
    layout.coefficientSignal ≠ layout.orderBoundarySignal := by
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
      reservedWires, workspaceWires, List.append_assoc] using
      layout.allWiresNodup
  have selectorSplit := List.nodup_append.mp normalized
  have dataSplit := List.nodup_append.mp selectorSplit.2.1
  have clockSplit := List.nodup_append.mp dataSplit.2.1
  have orderSplit := List.nodup_append.mp clockSplit.2.1
  have generatorSplit := List.nodup_append.mp orderSplit.2.1
  have reservedSplit := List.nodup_append.mp generatorSplit.2.1
  have reservedFacts := reservedSplit.1
  simp [reservedWires] at reservedFacts
  exact reservedFacts.1.1

theorem orderBoundarySignal_not_mem_h2AfterBoundarySupport119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    layout.orderBoundarySignal ∉ h2AfterBoundarySupport119 layout := by
  simp only [h2AfterBoundarySupport119, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, (coefficientSignal_ne_orderBoundarySignal119 layout).symm, ?_, ?_, ?_, ?_⟩
  · rintro ⟨orderIndex, _, equal⟩
    exact (layout.orderWire_separated orderIndex).2.2.1 _ (by simp) equal
  · rcases List.mem_ofFn.mp (historyActiveWire_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    intro boundaryEqual
    exact (layout.postGeneratorSignal_separated layout.orderBoundarySignal
      (by simp)).2.2 workspaceIndex (equal.trans boundaryEqual.symm)
  · rcases List.mem_ofFn.mp (historyLessThanIdleEndWire_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    intro boundaryEqual
    exact (layout.postGeneratorSignal_separated layout.orderBoundarySignal
      (by simp)).2.2 workspaceIndex (equal.trans boundaryEqual.symm)
  · rcases List.mem_ofFn.mp (historyLessThanTimeWire_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    intro boundaryEqual
    exact (layout.postGeneratorSignal_separated layout.orderBoundarySignal
      (by simp)).2.2 workspaceIndex (equal.trans boundaryEqual.symm)
  · rcases List.mem_ofFn.mp (historyBranchWire_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    intro boundaryEqual
    exact (layout.postGeneratorSignal_separated layout.orderBoundarySignal
      (by simp)).2.2 workspaceIndex (equal.trans boundaryEqual.symm)

theorem historyTaylorOrderLessThanTaylorOrderValue_h2AfterIdleEnd_decide119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    historyTaylorOrderLessThanTaylorOrderValue
        (ExecutableLayout119 source domain)
        (h2AfterIdleEnd119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits branch index)) =
      decide (index.state.label.val < source.historyParameters.taylorOrder) := by
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
          source.historyParameters.taylorOrder.testBit bit.val)) =
    decide (index.state.label.val < source.historyParameters.taylorOrder)
  rw [h2AfterIdleEnd119_read_order119,
    correctedBranchHistoryBasis119_read_order, constantBits]
  simp only [orderBits119, qubitBasisLittleEndianIndex_basis]
  rw [orderEncodedValue]

theorem correctedBranchHistoryBasis119_orderBoundarySignal_false119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    correctedBranchHistoryBasis119 source domain fits branch index
        (ExecutableLayout119 source domain).orderBoundarySignal = false := by
  have separated := (ExecutableLayout119 source domain).postGeneratorSignal_separated
    (ExecutableLayout119 source domain).orderBoundarySignal (by simp)
  rw [correctedBranchHistoryBasis119_apply_of_not_selector]
  · apply executableHistoryBasis119_apply_of_tail_mem
    change (ExecutableLayout119 source domain).orderBoundarySignal ∈
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

theorem h2AfterIdleEnd119_orderBoundarySignal119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    h2AfterIdleEnd119 layout input layout.orderBoundarySignal =
      input layout.orderBoundarySignal := by
  have separated := layout.postGeneratorSignal_separated
    layout.orderBoundarySignal (by simp)
  have branchNe : layout.orderBoundarySignal ≠ historyBranchWire layout := by
    have member := historyBranchWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
    intro equal
    exact separated.2.2 workspaceIndex (member.trans equal.symm)
  have timeNe : layout.orderBoundarySignal ≠
      historyLessThanTimeWire layout := by
    have member := historyLessThanTimeWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
    intro equal
    exact separated.2.2 workspaceIndex (member.trans equal.symm)
  have idleNe : layout.orderBoundarySignal ≠
      historyLessThanIdleEndWire layout := by
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

/-- A suffix which cannot write the boundary signal has zero matrix entries
from a boundary-dirty input to a boundary-clean row. -/
theorem h2AfterBoundaryOperator_entry_zero_of_boundary119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr)
    (row input : QubitBasis qubits)
    (rowClean : row layout.orderBoundarySignal = false)
    (inputDirty : input layout.orderBoundarySignal = true) :
    h2AfterBoundaryOperator119 layout angles idleAngle row input = 0 := by
  by_contra nonzero
  have sameBoundary := h2AfterBoundaryOperator_local119 layout angles idleAngle
    row input nonzero layout.orderBoundarySignal
    (orderBoundarySignal_not_mem_h2AfterBoundarySupport119 layout)
  rw [rowClean, inputDirty] at sameBoundary
  contradiction

/-- Active boundary columns reach the post-boundary suffix with the typed
boundary signal set. -/
theorem applyOperator_h2PostOperator_active_boundary119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (labelBoundary : ¬ inputIndex.state.label.val <
      source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let angles : Fin
        (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
          (ExecutableAdmissible119 source domain).analytic).taylorOrder →
          VerifiedCircuitCore.AngleExpr :=
      fun coefficientIndex => correctedTaylorCoefficientAngle119
        source.toCommonSource119 coefficientIndex.val
    let logicalInput := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex
    let before := h2BeforeQ119 layout logicalInput
    let stable := h2AfterIdleEnd119 layout logicalInput
    let dirty := historyTaylorOrderBoundaryBasisAction layout stable
    VerifiedCircuitCore.applyOperator
        (h2PostOperator119 layout angles compiledIdleCoefficientAngle119)
        (VerifiedCircuitCore.basisKet before) =
      VerifiedCircuitCore.applyOperator
        (h2AfterBoundaryOperator119 layout angles compiledIdleCoefficientAngle119)
        (VerifiedCircuitCore.basisKet dirty) ∧
      dirty layout.orderBoundarySignal = true := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let angles : Fin
      (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic).taylorOrder →
        VerifiedCircuitCore.AngleExpr :=
    fun coefficientIndex => correctedTaylorCoefficientAngle119
      source.toCommonSource119 coefficientIndex.val
  let logicalInput := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 inputIndex
  let before := h2BeforeQ119 layout logicalInput
  let stable := h2AfterIdleEnd119 layout logicalInput
  let dirty := historyTaylorOrderBoundaryBasisAction layout stable
  have stablePredicate : historyTaylorPostGeneratorStablePredicate layout stable :=
    h2AfterIdleEnd119_postStable119 source domain fits h2SelectedBranch119
      inputIndex
  have branchStable : stable (historyBranchWire layout) = true :=
    h2AfterIdleEnd119_branch_flag_selected source domain fits inputIndex
  have timeFlagStable : stable (historyLessThanTimeWire layout) = true :=
    h2AfterIdleEnd119_time_flag_active source domain fits inputIndex clockActive
  have idleFlagStable : stable (historyLessThanIdleEndWire layout) = true :=
    h2AfterIdleEnd119_idle_flag_active source domain fits inputIndex clockActive
  have clockTrue : historyTaylorClockLessThanTimeValue layout stable = true := by
    rw [← stablePredicate.2.1]
    exact timeFlagStable
  have orderFalse :
      historyTaylorOrderLessThanTaylorOrderValue layout stable = false := by
    rw [historyTaylorOrderLessThanTaylorOrderValue_h2AfterIdleEnd_decide119
      source domain fits h2SelectedBranch119 inputIndex]
    simp [labelBoundary]
  have activeStep :
      historyTaylorActiveConjunctionBasisAction layout before = stable :=
    historyTaylorActiveConjunctionBasisAction_involutive119 layout stable
  have invalidStep :
      historyTaylorInvalidClockBasisAction layout stable = stable :=
    historyTaylorInvalidClockBasisAction_selected_active119 source domain fits
      inputIndex clockActive
  have orderCondition : historyTaylorOrderBoundaryCondition layout stable = true := by
    unfold historyTaylorOrderBoundaryCondition
    rw [branchStable, clockTrue, orderFalse]
    rfl
  have dirtyBoundaryTrue : dirty layout.orderBoundarySignal = true := by
    have stableBoundaryFalse : stable layout.orderBoundarySignal = false := by
      calc
        stable layout.orderBoundarySignal =
            logicalInput layout.orderBoundarySignal :=
          h2AfterIdleEnd119_orderBoundarySignal119 layout logicalInput
        _ = false := correctedBranchHistoryBasis119_orderBoundarySignal_false119
          source domain fits h2SelectedBranch119 inputIndex
    dsimp only [dirty]
    unfold historyTaylorOrderBoundaryBasisAction
    rw [orderCondition]
    simp [xorWire, stableBoundaryFalse]
  have dirtyPredicate : historyTaylorPostGeneratorStablePredicate layout dirty :=
    historyTaylorOrderBoundaryBasisAction_maps_stable layout stable stablePredicate
  have boundaryOutside := orderBoundarySignal_not_mem_h2AfterBoundarySupport119
    layout
  have boundaryNeBranch : layout.orderBoundarySignal ≠ historyBranchWire layout := by
    intro equal
    apply boundaryOutside
    rw [equal]
    simp [h2AfterBoundarySupport119]
  have boundaryNeTime : layout.orderBoundarySignal ≠
      historyLessThanTimeWire layout := by
    intro equal
    apply boundaryOutside
    rw [equal]
    simp [h2AfterBoundarySupport119]
  have boundaryNeIdle : layout.orderBoundarySignal ≠
      historyLessThanIdleEndWire layout := by
    intro equal
    apply boundaryOutside
    rw [equal]
    simp [h2AfterBoundarySupport119]
  have dirtyBranch : dirty (historyBranchWire layout) = true := by
    dsimp only [dirty]
    unfold historyTaylorOrderBoundaryBasisAction
    rw [xorWire_apply_other _ _ boundaryNeBranch.symm]
    exact branchStable
  have dirtyTime : dirty (historyLessThanTimeWire layout) = true := by
    dsimp only [dirty]
    unfold historyTaylorOrderBoundaryBasisAction
    rw [xorWire_apply_other _ _ boundaryNeTime.symm]
    exact timeFlagStable
  have dirtyIdle : dirty (historyLessThanIdleEndWire layout) = true := by
    dsimp only [dirty]
    unfold historyTaylorOrderBoundaryBasisAction
    rw [xorWire_apply_other _ _ boundaryNeIdle.symm]
    exact idleFlagStable
  have dirtyClockTrue :
      historyTaylorClockLessThanTimeValue layout dirty = true := by
    rw [← dirtyPredicate.2.1]
    exact dirtyTime
  have dirtyIdleClockTrue :
      historyTaylorClockLessThanIdleEndValue layout dirty = true := by
    rw [← dirtyPredicate.2.2.1]
    exact dirtyIdle
  have dirtyIdleIntervalFalse :
      historyTaylorIdleIntervalCondition layout dirty = false := by
    unfold historyTaylorIdleIntervalCondition
    rw [dirtyIdleClockTrue, dirtyClockTrue]
    rfl
  have idleBoundaryStep :
      historyTaylorIdleBoundaryBasisAction layout dirty = dirty := by
    unfold historyTaylorIdleBoundaryBasisAction historyTaylorIdleBoundaryCondition
    rw [dirtyBranch, dirtyIdleIntervalFalse]
    simp [xorWire]
  constructor
  · exact applyOperator_h2PostOperator_to_afterBoundary119 layout angles
      compiledIdleCoefficientAngle119 before stable dirty activeStep invalidStep
      rfl idleBoundaryStep
  · exact dirtyBoundaryTrue

/-- On an active clock at or above the Taylor boundary, the actual post-Q10
word has no clean logical output entry. -/
theorem h2PostOperator_active_boundary_logical_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (labelBoundary : ¬ inputIndex.state.label.val <
      source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let before := h2BeforeQ119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h2SelectedBranch119 inputIndex)
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    h2PostOperator119 layout
        (fun coefficientIndex => correctedTaylorCoefficientAngle119
          source.toCommonSource119 coefficientIndex.val)
        compiledIdleCoefficientAngle119 row before = 0 := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let angles : Fin
      (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic).taylorOrder →
        VerifiedCircuitCore.AngleExpr :=
    fun coefficientIndex => correctedTaylorCoefficientAngle119
      source.toCommonSource119 coefficientIndex.val
  let logicalInput := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 inputIndex
  let before := h2BeforeQ119 layout logicalInput
  let stable := h2AfterIdleEnd119 layout logicalInput
  let dirty := historyTaylorOrderBoundaryBasisAction layout stable
  let row := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 outputIndex
  have action := applyOperator_h2PostOperator_active_boundary119 source domain fits
    inputIndex clockActive labelBoundary
  have entryEq := congrFun action.1 row
  simp only [VerifiedCircuitCore.applyOperator_basisKet] at entryEq
  rw [entryEq]
  exact h2AfterBoundaryOperator_entry_zero_of_boundary119 layout angles
    compiledIdleCoefficientAngle119 row dirty
    (correctedBranchHistoryBasis119_orderBoundarySignal_false119 source domain fits
      h2SelectedBranch119 outputIndex) action.2

end
end ExecutableHistoryExecutableHistory
