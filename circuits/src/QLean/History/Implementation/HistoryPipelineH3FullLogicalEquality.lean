import QLean.History.Implementation.HistoryPipelineH3ActiveAllRows

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
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

/-- The repaired physical active-clock H3 column agrees with corrected L2 on
every clean logical output row, including every off-support zero entry. -/
theorem repairedH3RecordedTarget119_active_all_rows
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (clockNext : inputIndex.clock.val + 1 <
      source.historyParameters.clockEnd) :
    repairedH3RecordedTarget119 source domain
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          outputIndex)
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          inputIndex) =
      (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
          outputIndex inputIndex : Real) : Complex)) := by
  let expectedIndex := h3ActiveOutputIndex119 source inputIndex clockNext
  by_cases indexEq : outputIndex = expectedIndex
  · subst outputIndex
    exact repairedH3RecordedTarget119_active_expected_eq_correctedBranch119
      source domain fits inputIndex clockActive clockNext
  · rw [repairedH3RecordedTarget119_active_all_rows_physical
      source domain fits inputIndex outputIndex clockActive clockNext]
    rw [if_neg indexEq]
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
      · rw [if_pos clockEq, if_pos clockActive]
        unfold HistoryBlockEncoding.HistorySpec.fSigma
        by_cases stateEq : outputIndex.state.label.val = 0 ∧
            inputIndex.state.label.val ≤
              source.historyParameters.taylorOrder ∧
            outputIndex.state.configuration =
              inputIndex.state.configuration
        · exfalso
          apply indexEq
          apply oldHistoryIndex_ext119
          · apply Fin.ext
            simpa [expectedIndex, h3ActiveOutputIndex119] using clockEq
          · apply labelState_ext119
            · apply Fin.ext
              simpa [expectedIndex, h3ActiveOutputIndex119] using stateEq.1
            · simpa [expectedIndex, h3ActiveOutputIndex119] using stateEq.2.2
        · rw [if_neg stateEq]
          norm_num
      · rw [if_neg clockEq]
        norm_num
    exact correctedZero.symm

/-- Complete repaired H3 logical block equality.  This is exhaustive over
active clocks, final-idle nonterminal/terminal clocks, and non-final idle
labels; no caller-supplied target or support premise remains. -/
theorem repairedH3RecordedTarget119_all_logical_entries
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source) :
    repairedH3RecordedTarget119 source domain
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          outputIndex)
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          inputIndex) =
      (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
          outputIndex inputIndex : Real) : Complex)) := by
  by_cases clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks
  · have clockNext : inputIndex.clock.val + 1 <
        source.historyParameters.clockEnd := by
      have physicalLtClockEnd := source.historyWellFormed.2.2.2.2
      omega
    exact repairedH3RecordedTarget119_active_all_rows
      source domain fits inputIndex outputIndex clockActive clockNext
  · by_cases finalLabel : inputIndex.state.label.val + 1 =
        source.historyParameters.binaryLabels
    · by_cases clockNext : inputIndex.clock.val + 1 <
          source.historyParameters.clockEnd
      · exact repairedH3RecordedTarget119_idle_final_nonterminal_all_rows
          source domain fits inputIndex outputIndex clockActive finalLabel
            clockNext
      · exact repairedH3RecordedTarget119_idle_final_terminal_all_rows
          source domain fits inputIndex outputIndex clockActive finalLabel
            clockNext
    · exact repairedH3RecordedTarget119_idle_nonfinal_all_rows
        source domain fits inputIndex outputIndex clockActive finalLabel

end
end ExecutableHistoryExecutableHistory
