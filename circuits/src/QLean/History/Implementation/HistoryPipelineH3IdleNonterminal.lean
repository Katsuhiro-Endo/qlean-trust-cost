import QLean.History.Implementation.HistoryPipelineH3IdleColumn

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

/-- Every clean logical row of a nonterminal final-idle H3 column equals the
corresponding normalized `L2` entry, including all off-support zero rows. -/
theorem repairedH3RecordedTarget119_idle_final_nonterminal_all_rows
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (finalLabel : inputIndex.state.label.val + 1 =
      source.historyParameters.binaryLabels)
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
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 inputIndex
  let row := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 outputIndex
  let clean := h3ZeroOrder119 layout (h3BeforeUniform119 layout input)
  let cleanOutput := h3ActiveTailBasisAction119 source domain clean
  let expectedIndex := h3ActiveOutputIndex119 source inputIndex clockNext
  have cleanOutputEq : cleanOutput =
      correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
        expectedIndex :=
    h3ActiveTailBasisAction119_expected_eq_logical
      source domain fits inputIndex clockNext
  by_cases indexEq : outputIndex = expectedIndex
  · subst outputIndex
    exact repairedH3RecordedTarget119_idle_final_expected_eq_correctedBranch119
      source domain fits inputIndex clockIdle finalLabel clockNext
  · have rowNe : row ≠ cleanOutput := by
      intro equal
      apply indexEq
      apply correctedBranchHistoryBasis119_injective_index
        source domain fits h3SelectedBranch119
      exact equal.trans cleanOutputEq
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
      by_cases clockEq : outputIndex.clock.val = inputIndex.clock.val + 1
      · rw [if_pos clockEq, if_neg clockIdle]
        unfold HistoryBlockEncoding.HistorySpec.fBin
        by_cases stateEq : outputIndex.state.label.val = 0 ∧
            inputIndex.state.label.val + 1 =
              source.historyParameters.binaryLabels ∧
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
    rw [correctedZero]

end
end ExecutableHistoryExecutableHistory
