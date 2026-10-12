import QLean.History.Implementation.HistoryPipelineH3IdleProduct

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
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

theorem repairedH3RecordedTarget119_active_logical_entry
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    repairedH3RecordedTarget119 source domain
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          (h3ActiveOutputIndex119 source index clockNext))
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          index) =
      if index.state.label.val ≤ source.historyParameters.taylorOrder then
        -(((1 / Real.sqrt
          (source.historyParameters.taylorOrder + 1) : Real) : Complex))
      else 0 := by
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let expected := h3ZeroOrder119 layout
    (h3BeforeUniform119 layout logical)
  have rowEq := h3ActiveTailBasisAction119_expected_eq_logical
    source domain fits index clockNext
  rw [← rowEq]
  exact repairedH3RecordedTarget119_active_physical_entry
    source domain fits index clockActive

theorem repairedH3RecordedTarget119_idle_final_logical_entry
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (finalLabel : index.state.label.val + 1 =
      source.historyParameters.binaryLabels)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    repairedH3RecordedTarget119 source domain
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          (h3ActiveOutputIndex119 source index clockNext))
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          index) =
      -(((1 / Real.sqrt
        (source.historyParameters.taylorOrder + 1) : Real) : Complex)) := by
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let expected := h3ZeroOrder119 layout
    (h3BeforeUniform119 layout logical)
  have rowEq := h3ActiveTailBasisAction119_expected_eq_logical
    source domain fits index clockNext
  rw [← rowEq]
  exact repairedH3RecordedTarget119_idle_final_physical_entry
    source domain fits index clockIdle finalLabel

theorem correctedBranchOperator119_h3_active_output
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    (((correctedBranchOperator119 source.historyParameters
        (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
        (h3ActiveOutputIndex119 source index clockNext) index : Real) :
      Complex)) =
      if index.state.label.val ≤ source.historyParameters.taylorOrder then
        -(((1 / Real.sqrt
          (source.historyParameters.taylorOrder + 1) : Real) : Complex))
      else 0 := by
  change ((((Real.sqrt
      (source.historyParameters.taylorOrder + 1))⁻¹ *
      ((HistoryBlockEncoding.HistorySpec.L2 source.historyParameters
        (h3ActiveOutputIndex119 source index clockNext) index : Rat) : Real) :
      Real) : Complex)) = _
  simp [HistoryBlockEncoding.HistorySpec.L2, HistoryBlockEncoding.HistorySpec.fSigma,
    h3ActiveOutputIndex119, clockActive]
  split <;> simp_all

theorem correctedBranchOperator119_h3_idle_final_output
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (finalLabel : index.state.label.val + 1 =
      source.historyParameters.binaryLabels)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    (((correctedBranchOperator119 source.historyParameters
        (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
        (h3ActiveOutputIndex119 source index clockNext) index : Real) :
      Complex)) =
      -(((1 / Real.sqrt
        (source.historyParameters.taylorOrder + 1) : Real) : Complex)) := by
  change ((((Real.sqrt
      (source.historyParameters.taylorOrder + 1))⁻¹ *
      ((HistoryBlockEncoding.HistorySpec.L2 source.historyParameters
        (h3ActiveOutputIndex119 source index clockNext) index : Rat) : Real) :
      Real) : Complex)) = _
  simp [HistoryBlockEncoding.HistorySpec.L2, HistoryBlockEncoding.HistorySpec.fBin,
    h3ActiveOutputIndex119, clockIdle, finalLabel, one_div]

theorem repairedH3RecordedTarget119_active_expected_eq_correctedBranch119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    repairedH3RecordedTarget119 source domain
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          (h3ActiveOutputIndex119 source index clockNext))
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          index) =
      (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
          (h3ActiveOutputIndex119 source index clockNext) index : Real) :
        Complex)) := by
  rw [repairedH3RecordedTarget119_active_logical_entry
    source domain fits index clockActive clockNext]
  rw [correctedBranchOperator119_h3_active_output
    source index clockActive clockNext]

theorem repairedH3RecordedTarget119_idle_final_expected_eq_correctedBranch119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (finalLabel : index.state.label.val + 1 =
      source.historyParameters.binaryLabels)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    repairedH3RecordedTarget119 source domain
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          (h3ActiveOutputIndex119 source index clockNext))
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          index) =
      (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
          (h3ActiveOutputIndex119 source index clockNext) index : Real) :
        Complex)) := by
  rw [repairedH3RecordedTarget119_idle_final_logical_entry
    source domain fits index clockIdle finalLabel clockNext]
  rw [correctedBranchOperator119_h3_idle_final_output
    source index clockIdle finalLabel clockNext]

end
end ExecutableHistoryExecutableHistory
