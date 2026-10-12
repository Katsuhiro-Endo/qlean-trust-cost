import QLean.History.Implementation.HistoryPipelineH3IdleNonterminal
import QLean.History.Implementation.HistoryPipelineH2TerminalEntry

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
open HistoryPipelineReferenceRawValueConstructor
open HistoryPipelineReferenceRawValueConstructorV3
open HistoryPipelineReferenceAdmissibility041

noncomputable section

/-- The clean branch of an idle H3 column always advances the physical clock
by one, including the terminal step that leaves the logical clock carrier. -/
theorem h3ActiveTailBasisAction119_expected_clock
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let expected := h3ZeroOrder119 layout
      (h3BeforeUniform119 layout logical)
    registerValue layout.clock
        (h3ActiveTailBasisAction119 source domain expected) =
      index.clock.val + 1 := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let zeroIndex := h3OrderZeroIndex119 source index
  let zeroLogical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 zeroIndex
  let expected := h3ZeroOrder119 layout
    (h3BeforeUniform119 layout
      (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119 index))
  have expectedEq : expected = h3BeforeUniform119 layout zeroLogical := by
    exact h3ZeroOrder119_before_eq_orderZeroIndex source domain fits index
  have activeStep : historyTaylorActiveConjunctionBasisAction layout expected =
      h3AfterIdleEnd119 layout zeroLogical := by
    rw [expectedEq]
    unfold h3BeforeUniform119
    exact historyTaylorActiveConjunctionBasisAction_involutive119 layout
      (h3AfterIdleEnd119 layout zeroLogical)
  have idleRestore : historyTaylorIdleEndComparisonBasisAction layout
      (historyTaylorActiveConjunctionBasisAction layout expected) =
        h3AfterTime119 layout zeroLogical := by
    rw [activeStep]
    unfold h3AfterIdleEnd119
    exact historyTaylorIdleEndComparisonBasisAction_involutive119 layout
      (h3AfterTime119 layout zeroLogical)
  have timeRestore : historyTaylorTimeComparisonBasisAction layout
      (historyTaylorIdleEndComparisonBasisAction layout
        (historyTaylorActiveConjunctionBasisAction layout expected)) =
          h3AfterSelector119 layout zeroLogical := by
    rw [idleRestore]
    unfold h3AfterTime119
    exact historyTaylorTimeComparisonBasisAction_involutive119 layout
      (h3AfterSelector119 layout zeroLogical)
  let afterSelector := h3AfterSelector119 layout zeroLogical
  have branchTrue : afterSelector (historyBranchWire layout) = true := by
    exact h3AfterSelector119_selected_branch_true source domain fits zeroIndex
  have orderZero : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order) 0 afterSelector = true := by
    calc
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 afterSelector =
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 zeroLogical := by
            apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
            intro wire member
            simp only [historyRegisterWires, List.mem_ofFn] at member
            rcases member with ⟨orderIndex, rfl⟩
            exact congrFun (h3AfterSelector119_order_read layout zeroLogical)
              orderIndex
      _ = true := by
        exact correctedBranchHistoryBasis119_order_equals source domain fits
          h3SelectedBranch119 zeroIndex 0 (by
            have positive : 0 < 2 ^ historyOrderWidth
                source.historyParameters.taylorOrder :=
              lt_of_lt_of_le source.historyWellFormed.binaryLabels_pos
                fits.label_fits
            have taylorOrderEq :
                (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
                  (ExecutableAdmissible119 source domain).analytic).taylorOrder =
                  source.historyParameters.taylorOrder := by rfl
            have orderWidthEq :
                (historyRegisterWires layout.order).length =
                  historyOrderWidth source.historyParameters.taylorOrder := by
              simp [historyRegisterWires, layout, taylorOrderEq]
            rw [orderWidthEq]
            exact positive)
  have projectorStep : h3I06BasisAction layout afterSelector = afterSelector := by
    funext wire
    simp [h3I06BasisAction, h3I06ProjectorPredicate, branchTrue, orderZero,
      xorWire]
  let clockSpec := historyControlledClockIncrementSpec layout
    (ExecutableClockEvidence119 source domain).controlledIncrement
  have clockControl : afterSelector clockSpec.control = true := by
    exact branchTrue
  have clockValue : registerValue clockSpec.accumulator afterSelector =
      index.clock.val := by
    change registerValue layout.clock afterSelector = index.clock.val
    unfold registerValue
    rw [h3AfterSelector119_clock_read]
    rw [correctedBranchHistoryBasis119_read_clock]
    dsimp [zeroLogical, zeroIndex, h3OrderZeroIndex119, clockBits119]
    exact qubitBasisLittleEndianIndex_basis _
  have tailWidthEq :
      historyClockTailWidth
          (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic) + 1 =
        historyClockWidth source.historyParameters.physicalClocks
          source.historyParameters.taylorOrder
          (source.historyBlocks *
            historyIdleBlockSize source.historyParameters.taylorOrder - 1) := by
    have blockWidthEq :
        historyClockWidth
            (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
              (ExecutableAdmissible119 source domain).analytic).timeSteps
            (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
              (ExecutableAdmissible119 source domain).analytic).taylorOrder
            (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
              (ExecutableAdmissible119 source domain).analytic).idlingSteps =
          historyClockWidth source.historyParameters.physicalClocks
            source.historyParameters.taylorOrder
            (source.historyBlocks *
              historyIdleBlockSize source.historyParameters.taylorOrder - 1) := by
      change historyClockWidth
          (rawTimeSteps036 (referenceData041Base (referenceData119 source)))
          (rawTaylorOrder036 (referenceData041Base (referenceData119 source)))
          (rawIdlingSteps041 (referenceData119 source)) = _
      exact executable_historyClockWidth_eq119 source
    unfold historyClockTailWidth
    rw [blockWidthEq]
    have widthPositive : 0 < historyClockWidth
        source.historyParameters.physicalClocks
        source.historyParameters.taylorOrder
        (source.historyBlocks *
          historyIdleBlockSize source.historyParameters.taylorOrder - 1) := by
      unfold historyClockWidth
      positivity
    omega
  have clockFits : index.clock.val + 1 <
      2 ^ (historyClockTailWidth
        (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
          (ExecutableAdmissible119 source domain).analytic) + 1) := by
    rw [tailWidthEq]
    exact lt_of_le_of_lt (Nat.succ_le_iff.mpr index.clock.isLt) fits.clock_fits
  have clockStep : controlledAddConstantMod2PowBasisAction clockSpec
      afterSelector = writeRegisterValue layout.clock (index.clock.val + 1)
        afterSelector := by
    unfold controlledAddConstantMod2PowBasisAction
    rw [if_pos clockControl, clockValue]
    change writeRegisterValue layout.clock
      ((index.clock.val + 1) %
        2 ^ (historyClockTailWidth
          (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic) + 1))
      afterSelector = _
    rw [Nat.mod_eq_of_lt clockFits]
  have actionEq : h3ActiveTailBasisAction119 source domain expected =
      h3AfterSelector119 layout
        (writeRegisterValue layout.clock (index.clock.val + 1) afterSelector) := by
    unfold h3ActiveTailBasisAction119
    change h3AfterSelector119 layout
      (controlledAddConstantMod2PowBasisAction clockSpec
        (h3I06BasisAction layout
          (historyTaylorTimeComparisonBasisAction layout
            (historyTaylorIdleEndComparisonBasisAction layout
              (historyTaylorActiveConjunctionBasisAction layout expected))))) = _
    rw [timeRestore, projectorStep, clockStep]
  rw [actionEq]
  unfold registerValue
  rw [h3AfterSelector119_clock_read]
  exact registerValue_writeRegisterValue_of_lt119 layout.clock
    (index.clock.val + 1) afterSelector clockFits

/-- At the terminal logical clock there is no clean logical H3 output.  Both
the recorded circuit and the corrected `L2` target therefore have zero entry. -/
theorem repairedH3RecordedTarget119_idle_final_terminal_all_rows
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (finalLabel : inputIndex.state.label.val + 1 =
      source.historyParameters.binaryLabels)
    (terminal : ¬ inputIndex.clock.val + 1 <
      source.historyParameters.clockEnd) :
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
  let clean := h3ZeroOrder119 layout (h3BeforeUniform119 layout input)
  let cleanOutput := h3ActiveTailBasisAction119 source domain clean
  have terminalEq : inputIndex.clock.val + 1 =
      source.historyParameters.clockEnd := by
    have inputLt := inputIndex.clock.isLt
    omega
  have rowClock : registerValue layout.clock row = outputIndex.clock.val := by
    unfold registerValue
    rw [correctedBranchHistoryBasis119_read_clock]
    dsimp [row, clockBits119]
    exact qubitBasisLittleEndianIndex_basis _
  have cleanClock : registerValue layout.clock cleanOutput =
      inputIndex.clock.val + 1 :=
    h3ActiveTailBasisAction119_expected_clock source domain fits inputIndex
  have rowNe : row ≠ cleanOutput := by
    intro equal
    have valueEq := congrArg (registerValue layout.clock) equal
    rw [rowClock, cleanClock, terminalEq] at valueEq
    exact (ne_of_lt outputIndex.clock.isLt) valueEq
  rw [repairedH3RecordedTarget119_idle_final_clean_logical_entry
    source domain fits inputIndex outputIndex clockIdle finalLabel]
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
    have clockNe : outputIndex.clock.val ≠ inputIndex.clock.val + 1 := by
      rw [terminalEq]
      exact ne_of_lt outputIndex.clock.isLt
    rw [if_neg clockNe]
    norm_num
  rw [correctedZero]

end
end ExecutableHistoryExecutableHistory
