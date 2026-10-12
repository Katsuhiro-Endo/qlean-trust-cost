import QLean.History.Implementation.HistoryPipelineH2BoundaryEntry

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
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

/-- Wires written strictly after the H2 degree increment. -/
def h2AfterDegreeSupport119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Finset (Fin qubits) :=
  {layout.coefficientSignal, historyActiveWire layout,
    historyLessThanIdleEndWire layout, historyLessThanTimeWire layout,
    historyBranchWire layout}

/-- H2 suffix beginning immediately after the degree increment. -/
def h2AfterDegreeOperator119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr) :
    VerifiedCircuitCore.Operator (QubitBasis qubits) :=
  operatorSequence
    [historyTaylorCoefficientLoopOperator layout angles,
     historyTaylorIdleCoefficientOperator layout idleAngle,
     operatorSequence
       [historyTaylorIdleEndComparisonOperator layout,
        historyTaylorTimeComparisonOperator layout,
        historyTaylorSelectorEqualityOperator layout]]

theorem h2AfterDegreeOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr) :
    OperatorPreservesOutside (h2AfterDegreeSupport119 layout)
      (h2AfterDegreeOperator119 layout angles idleAngle) := by
  unfold h2AfterDegreeOperator119
  apply OperatorPreservesOutside.operatorSequence_of_forall
  intro operator member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (historyTaylorCoefficientLoopOperator_local119 layout angles).mono (by
      intro wire wireMember
      simp only [Finset.mem_singleton] at wireMember
      subst wire
      simp [h2AfterDegreeSupport119])
  · exact (historyTaylorIdleCoefficientOperator_local119 layout idleAngle).mono (by
      intro wire wireMember
      simp only [Finset.mem_singleton] at wireMember
      subst wire
      simp [h2AfterDegreeSupport119])
  · apply OperatorPreservesOutside.operatorSequence_of_forall
    intro restore restoreMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at restoreMember
    rcases restoreMember with rfl | rfl | rfl
    · exact (historyTaylorIdleEndComparisonOperator_local119 layout).mono (by
        intro wire wireMember
        simp only [Finset.mem_singleton] at wireMember
        subst wire
        simp [h2AfterDegreeSupport119])
    · exact (historyTaylorTimeComparisonOperator_local119 layout).mono (by
        intro wire wireMember
        simp only [Finset.mem_singleton] at wireMember
        subst wire
        simp [h2AfterDegreeSupport119])
    · exact (historyTaylorSelectorEqualityOperator_local119 layout).mono (by
        intro wire wireMember
        simp only [Finset.mem_singleton] at wireMember
        subst wire
        simp [h2AfterDegreeSupport119])

theorem orderWire_not_mem_h2AfterDegreeSupport119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (orderIndex : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire orderIndex ∉ h2AfterDegreeSupport119 layout := by
  simp only [h2AfterDegreeSupport119, Finset.mem_insert,
    Finset.mem_singleton, not_or]
  refine ⟨(layout.orderWire_separated orderIndex).2.2.1
      layout.coefficientSignal (by simp), ?_, ?_, ?_, ?_⟩
  · rcases List.mem_ofFn.mp (historyActiveWire_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    intro orderEqual
    exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
      (orderEqual.trans equal.symm)
  · rcases List.mem_ofFn.mp (historyLessThanIdleEndWire_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    intro orderEqual
    exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
      (orderEqual.trans equal.symm)
  · rcases List.mem_ofFn.mp (historyLessThanTimeWire_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    intro orderEqual
    exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
      (orderEqual.trans equal.symm)
  · rcases List.mem_ofFn.mp (historyBranchWire_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    intro orderEqual
    exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
      (orderEqual.trans equal.symm)

theorem h2AfterDegreeOperator_entry_zero_of_registerValue_ne119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr)
    (row input : QubitBasis qubits)
    (valuesNe : registerValue layout.order row ≠
      registerValue layout.order input) :
    h2AfterDegreeOperator119 layout angles idleAngle row input = 0 := by
  by_contra nonzero
  have locality := h2AfterDegreeOperator_local119 layout angles idleAngle
  have readEq : layout.order.read row = layout.order.read input := by
    funext orderIndex
    exact locality row input nonzero (layout.order.wire orderIndex)
      (orderWire_not_mem_h2AfterDegreeSupport119 layout orderIndex)
  apply valuesNe
  unfold registerValue
  rw [readEq]

theorem h2AfterDegreeOperator_entry_zero_of_boundary119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr)
    (row input : QubitBasis qubits)
    (rowClean : row layout.orderBoundarySignal = false)
    (inputDirty : input layout.orderBoundarySignal = true) :
    h2AfterDegreeOperator119 layout angles idleAngle row input = 0 := by
  by_contra nonzero
  have outside : layout.orderBoundarySignal ∉
      h2AfterDegreeSupport119 layout := by
    intro member
    apply orderBoundarySignal_not_mem_h2AfterBoundarySupport119 layout
    simp only [h2AfterDegreeSupport119, Finset.mem_insert,
      Finset.mem_singleton] at member
    rcases member with equal | equal | equal | equal | equal <;>
      simp [h2AfterBoundarySupport119, equal]
  have sameBoundary := h2AfterDegreeOperator_local119 layout angles idleAngle
    row input nonzero layout.orderBoundarySignal outside
  rw [rowClean, inputDirty] at sameBoundary
  contradiction

/-- Algebraic cut of H2 immediately after its degree increment. -/
theorem applyOperator_h2PostOperator_to_afterDegree119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr)
    (before stable afterOrder afterBoundary advanced : QubitBasis qubits)
    (activeStep :
      historyTaylorActiveConjunctionBasisAction layout before = stable)
    (invalidStep :
      historyTaylorInvalidClockBasisAction layout stable = stable)
    (orderStep :
      historyTaylorOrderBoundaryBasisAction layout stable = afterOrder)
    (idleStep :
      historyTaylorIdleBoundaryBasisAction layout afterOrder = afterBoundary)
    (degreeStep :
      historyTaylorDegreeIncrementBasisAction layout afterBoundary = advanced) :
    VerifiedCircuitCore.applyOperator
        (h2PostOperator119 layout angles idleAngle)
        (VerifiedCircuitCore.basisKet before) =
      VerifiedCircuitCore.applyOperator
        (h2AfterDegreeOperator119 layout angles idleAngle)
        (VerifiedCircuitCore.basisKet advanced) := by
  unfold h2PostOperator119 h2AfterDegreeOperator119
  simp only [operatorSequence, applyOperator_mul, Matrix.one_mul]
  rw [historyTaylorActiveConjunctionOperator,
    applyOperator_deterministicOperator_basisKet, activeStep]
  rw [historyTaylorInvalidClockOperator,
    applyOperator_deterministicOperator_basisKet, invalidStep]
  rw [historyTaylorOrderBoundaryOperator,
    applyOperator_deterministicOperator_basisKet, orderStep]
  rw [historyTaylorIdleBoundaryOperator,
    applyOperator_deterministicOperator_basisKet, idleStep]
  have degreeStep' :
      predicateControlledAddMod2PowBasisAction
          (historyTaylorDegreeIncrementCondition layout) layout.order 1
          afterBoundary = advanced := by
    simpa [historyTaylorDegreeIncrementBasisAction] using degreeStep
  rw [historyTaylorDegreeIncrementOperator,
    predicateControlledAddMod2PowOperator,
    applyOperator_deterministicOperator_basisKet, degreeStep']

theorem registerValue_correctedBranchHistoryBasis119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    registerValue (ExecutableLayout119 source domain).order
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      index.state.label.val := by
  unfold registerValue
  rw [correctedBranchHistoryBasis119_read_order]
  dsimp only [orderBits119]
  exact qubitBasisLittleEndianIndex_basis _

theorem registerValue_writeRegisterValue_of_lt119
    {qubits width : Nat}
    (register : Register qubits width)
    (value : Nat)
    (input : QubitBasis qubits)
    (valueFits : value < 2 ^ width) :
    registerValue register (writeRegisterValue register value input) = value := by
  let encoded : QubitBasis width :=
    qubitBasisOfLittleEndianIndex ⟨value, valueFits⟩
  have readEq : register.read (writeRegisterValue register value input) = encoded := by
    funext index
    change writeRegisterValue register value input (register.wire index) =
      encoded index
    rw [writeRegisterValue_apply_wire]
    rfl
  unfold registerValue
  rw [readEq]
  dsimp only [encoded]
  exact qubitBasisLittleEndianIndex_basis _

/-- Every idle logical column reaches the suffix after degree increment at the
deterministically computed basis. -/
theorem applyOperator_h2PostOperator_idle_to_afterDegree119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks) :
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
    let afterBoundary := historyTaylorIdleBoundaryBasisAction layout stable
    let advanced := historyTaylorDegreeIncrementBasisAction layout afterBoundary
    VerifiedCircuitCore.applyOperator
        (h2PostOperator119 layout angles compiledIdleCoefficientAngle119)
        (VerifiedCircuitCore.basisKet before) =
      VerifiedCircuitCore.applyOperator
        (h2AfterDegreeOperator119 layout angles compiledIdleCoefficientAngle119)
        (VerifiedCircuitCore.basisKet advanced) := by
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
  let afterBoundary := historyTaylorIdleBoundaryBasisAction layout stable
  let advanced := historyTaylorDegreeIncrementBasisAction layout afterBoundary
  have stablePredicate : historyTaylorPostGeneratorStablePredicate layout stable :=
    h2AfterIdleEnd119_postStable119 source domain fits h2SelectedBranch119
      inputIndex
  have branchStable : stable (historyBranchWire layout) = true :=
    h2AfterIdleEnd119_branch_flag_selected source domain fits inputIndex
  have timeFlagStable : stable (historyLessThanTimeWire layout) = false :=
    h2AfterIdleEnd119_time_flag_idle119 source domain fits inputIndex clockIdle
  have idleFlagStable : stable (historyLessThanIdleEndWire layout) = true :=
    h2AfterIdleEnd119_idle_flag_logical119 source domain fits inputIndex
  have clockFalse : historyTaylorClockLessThanTimeValue layout stable = false := by
    rw [← stablePredicate.2.1]
    exact timeFlagStable
  have activeStep :
      historyTaylorActiveConjunctionBasisAction layout before = stable :=
    historyTaylorActiveConjunctionBasisAction_involutive119 layout stable
  have invalidStep :
      historyTaylorInvalidClockBasisAction layout stable = stable := by
    unfold historyTaylorInvalidClockBasisAction historyTaylorInvalidClockCondition
    rw [branchStable, idleFlagStable]
    simp [xorWire]
  have orderStep :
      historyTaylorOrderBoundaryBasisAction layout stable = stable := by
    unfold historyTaylorOrderBoundaryBasisAction historyTaylorOrderBoundaryCondition
    rw [branchStable, clockFalse]
    simp [xorWire]
  exact applyOperator_h2PostOperator_to_afterDegree119 layout angles
    compiledIdleCoefficientAngle119 before stable stable afterBoundary advanced
    activeStep invalidStep orderStep rfl rfl

/-- The last logical idle label has no clean logical output: either the
physical order register is exactly full and raises the boundary signal, or the
zero-padded physical register advances outside the logical label range. -/
theorem h2PostOperator_idle_terminal_logical_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (terminal : ¬ inputIndex.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
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
  let afterBoundary := historyTaylorIdleBoundaryBasisAction layout stable
  let advanced := historyTaylorDegreeIncrementBasisAction layout afterBoundary
  let row := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 outputIndex
  let capacity := historyIdleBlockSize source.historyParameters.taylorOrder
  have taylorOrderEq :
      (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic).taylorOrder =
        source.historyParameters.taylorOrder := by
    rfl
  have orderWidthEq :
      (historyRegisterWires layout.order).length =
        historyOrderWidth source.historyParameters.taylorOrder := by
    simp [historyRegisterWires, layout, taylorOrderEq]
  have terminalEq : inputIndex.state.label.val + 1 =
      source.historyParameters.binaryLabels := by
    have labelLt := inputIndex.state.label.isLt
    omega
  have labelsLeCapacity : source.historyParameters.binaryLabels ≤ capacity := by
    simpa [capacity, historyIdleBlockSize] using fits.label_fits
  have action := applyOperator_h2PostOperator_idle_to_afterDegree119
    source domain fits inputIndex clockIdle
  have entryEq := congrFun action row
  simp only [VerifiedCircuitCore.applyOperator_basisKet] at entryEq
  rw [entryEq]
  have rowBoundaryFalse : row layout.orderBoundarySignal = false :=
    correctedBranchHistoryBasis119_orderBoundarySignal_false119 source domain fits
      h2SelectedBranch119 outputIndex
  have stablePredicate : historyTaylorPostGeneratorStablePredicate layout stable :=
    h2AfterIdleEnd119_postStable119 source domain fits h2SelectedBranch119
      inputIndex
  have branchStable : stable (historyBranchWire layout) = true :=
    h2AfterIdleEnd119_branch_flag_selected source domain fits inputIndex
  have timeFlagStable : stable (historyLessThanTimeWire layout) = false :=
    h2AfterIdleEnd119_time_flag_idle119 source domain fits inputIndex clockIdle
  have idleFlagStable : stable (historyLessThanIdleEndWire layout) = true :=
    h2AfterIdleEnd119_idle_flag_logical119 source domain fits inputIndex
  have clockFalse : historyTaylorClockLessThanTimeValue layout stable = false := by
    rw [← stablePredicate.2.1]
    exact timeFlagStable
  have idleClockTrue :
      historyTaylorClockLessThanIdleEndValue layout stable = true := by
    rw [← stablePredicate.2.2.1]
    exact idleFlagStable
  have idleIntervalTrue :
      historyTaylorIdleIntervalCondition layout stable = true := by
    unfold historyTaylorIdleIntervalCondition
    rw [idleClockTrue, clockFalse]
    rfl
  have registerValueStable : registerValue layout.order stable =
      inputIndex.state.label.val :=
    registerValue_h2AfterIdleEnd_correctedBranch119 source domain fits
      h2SelectedBranch119 inputIndex
  rcases lt_or_eq_of_le labelsLeCapacity with labelsLt | labelsEq
  · have boundaryNe : inputIndex.state.label.val ≠ capacity - 1 := by
      omega
    have boundaryFits : capacity - 1 <
        2 ^ (historyRegisterWires layout.order).length := by
      rw [orderWidthEq]
      simp [capacity, historyIdleBlockSize]
    have boundaryFalse :
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order) (capacity - 1) stable = false := by
      have sameOrder :
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
              (historyRegisterWires layout.order) (capacity - 1) stable =
            ClassicalReversibleStage.littleEndianRegisterEqualsNat
              (historyRegisterWires layout.order) (capacity - 1) logicalInput := by
        apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
        intro wire member
        simp only [historyRegisterWires, List.mem_ofFn] at member
        rcases member with ⟨orderIndex, rfl⟩
        exact congrFun (h2AfterIdleEnd119_read_order119 layout logicalInput)
          orderIndex
      rw [sameOrder,
        correctedBranchHistoryBasis119_order_equals source domain fits
          h2SelectedBranch119 inputIndex (capacity - 1) boundaryFits]
      simp [boundaryNe]
    have idleStep : afterBoundary = stable := by
      have boundaryFalse' :
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
              (historyRegisterWires layout.order)
              (historyIdleBlockSize
                (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
                  (ExecutableAdmissible119 source domain).analytic).taylorOrder - 1)
              stable = false := by
        simpa only [taylorOrderEq] using boundaryFalse
      dsimp only [afterBoundary]
      unfold historyTaylorIdleBoundaryBasisAction historyTaylorIdleBoundaryCondition
      rw [branchStable, idleIntervalTrue, boundaryFalse']
      simp [xorWire]
    have nextBound : source.historyParameters.binaryLabels <
        2 ^ historyOrderWidth source.historyParameters.taylorOrder := by
      simpa [capacity, historyIdleBlockSize] using labelsLt
    have degreeCondition :
        historyTaylorDegreeIncrementCondition layout stable = true := by
      simp [historyTaylorDegreeIncrementCondition, branchStable, idleClockTrue]
    have nextBoundLayout : source.historyParameters.binaryLabels <
        2 ^ historyOrderWidth
          (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic).taylorOrder := by
      simpa only [taylorOrderEq] using nextBound
    have inputNextBoundLayout : inputIndex.state.label.val + 1 <
        2 ^ historyOrderWidth
          (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic).taylorOrder := by
      rw [terminalEq]
      exact nextBoundLayout
    have degreeStep : advanced =
        writeRegisterValue layout.order source.historyParameters.binaryLabels
          stable := by
      dsimp only [advanced]
      rw [idleStep]
      unfold historyTaylorDegreeIncrementBasisAction
        predicateControlledAddMod2PowBasisAction
      rw [if_pos degreeCondition, registerValueStable,
        Nat.mod_eq_of_lt inputNextBoundLayout, terminalEq]
    have advancedValue : registerValue layout.order advanced =
        source.historyParameters.binaryLabels := by
      rw [degreeStep]
      exact registerValue_writeRegisterValue_of_lt119 layout.order
        source.historyParameters.binaryLabels stable nextBoundLayout
    have rowValue : registerValue layout.order row = outputIndex.state.label.val :=
      registerValue_correctedBranchHistoryBasis119 source domain fits
        h2SelectedBranch119 outputIndex
    apply h2AfterDegreeOperator_entry_zero_of_registerValue_ne119 layout angles
      compiledIdleCoefficientAngle119 row advanced
    rw [rowValue, advancedValue]
    exact ne_of_lt outputIndex.state.label.isLt
  · have labelBoundary : inputIndex.state.label.val = capacity - 1 := by
      omega
    have boundaryFits : capacity - 1 <
        2 ^ (historyRegisterWires layout.order).length := by
      rw [orderWidthEq]
      simp [capacity, historyIdleBlockSize]
    have boundaryTrue :
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order) (capacity - 1) stable = true := by
      have sameOrder :
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
              (historyRegisterWires layout.order) (capacity - 1) stable =
            ClassicalReversibleStage.littleEndianRegisterEqualsNat
              (historyRegisterWires layout.order) (capacity - 1) logicalInput := by
        apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
        intro wire member
        simp only [historyRegisterWires, List.mem_ofFn] at member
        rcases member with ⟨orderIndex, rfl⟩
        exact congrFun (h2AfterIdleEnd119_read_order119 layout logicalInput)
          orderIndex
      rw [sameOrder,
        correctedBranchHistoryBasis119_order_equals source domain fits
          h2SelectedBranch119 inputIndex (capacity - 1) boundaryFits]
      simp [labelBoundary]
    have idleCondition : historyTaylorIdleBoundaryCondition layout stable = true := by
      have boundaryTrue' :
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
              (historyRegisterWires layout.order)
              (historyIdleBlockSize
                (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
                  (ExecutableAdmissible119 source domain).analytic).taylorOrder - 1)
              stable = true := by
        simpa only [taylorOrderEq] using boundaryTrue
      unfold historyTaylorIdleBoundaryCondition
      rw [branchStable, idleIntervalTrue, boundaryTrue']
      rfl
    have stableBoundaryFalse : stable layout.orderBoundarySignal = false := by
      calc
        stable layout.orderBoundarySignal =
            logicalInput layout.orderBoundarySignal :=
          h2AfterIdleEnd119_orderBoundarySignal119 layout logicalInput
        _ = false := correctedBranchHistoryBasis119_orderBoundarySignal_false119
          source domain fits h2SelectedBranch119 inputIndex
    have afterBoundaryTrue : afterBoundary layout.orderBoundarySignal = true := by
      dsimp only [afterBoundary]
      unfold historyTaylorIdleBoundaryBasisAction
      rw [idleCondition]
      simp [xorWire, stableBoundaryFalse]
    have advancedBoundaryTrue : advanced layout.orderBoundarySignal = true := by
      calc
        advanced layout.orderBoundarySignal =
            afterBoundary layout.orderBoundarySignal := by
          dsimp only [advanced]
          unfold historyTaylorDegreeIncrementBasisAction
          apply predicateControlledAddMod2PowBasisAction_apply_outside
          intro orderIndex equal
          exact (layout.orderWire_separated orderIndex).2.2.1
            layout.orderBoundarySignal (by simp) equal.symm
        _ = true := afterBoundaryTrue
    exact h2AfterDegreeOperator_entry_zero_of_boundary119 layout angles
      compiledIdleCoefficientAngle119 row advanced rowBoundaryFalse
      advancedBoundaryTrue

end
end ExecutableHistoryExecutableHistory
