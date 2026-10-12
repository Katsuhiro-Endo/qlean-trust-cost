import QLean.History.Implementation.HistoryPipelineParameterAlignmentSemanticVerification
import QLean.History.Implementation.HistoryPipelineCorrectedLCU

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
open HistoryPipelineReferenceRawValueConstructor
open HistoryPipelineReferenceRawValueConstructorV3
open HistoryPipelineReferenceAdmissibility041

noncomputable section

theorem correctedBranchHistoryBasis119_clockLessThanIdleEnd
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    historyTaylorClockLessThanIdleEndValue
        (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      decide (index.clock.val < source.historyParameters.clockEnd) := by
  let width := historyClockWidth source.historyParameters.physicalClocks
    source.historyParameters.taylorOrder
    (source.historyBlocks *
      historyIdleBlockSize source.historyParameters.taylorOrder - 1)
  have constantBits :
      (fun bit : Fin width =>
        source.historyParameters.clockEnd.testBit bit.val) =
      qubitBasisOfLittleEndianIndex
        (⟨source.historyParameters.clockEnd,
          fits.clock_fits⟩ : Fin (2 ^ width)) := by
    funext bit
    rfl
  unfold historyTaylorClockLessThanIdleEndValue
  rw [unsignedLessThanBits_eq_decide_lt]
  change decide
    (qubitBasisLittleEndianIndex
        (historyClockWidth
          (rawTimeSteps036 (referenceData041Base (referenceData119 source)))
          (rawTaylorOrder036 (referenceData041Base (referenceData119 source)))
          (rawIdlingSteps041 (referenceData119 source)))
        ((ExecutableLayout119 source domain).clock.read
          (correctedBranchHistoryBasis119 source domain fits branch index)) <
      qubitBasisLittleEndianIndex
        (historyClockWidth
          (rawTimeSteps036 (referenceData041Base (referenceData119 source)))
          (rawTaylorOrder036 (referenceData041Base (referenceData119 source)))
          (rawIdlingSteps041 (referenceData119 source)))
        (fun bit =>
          (historyIdleClockEnd
            (rawTimeSteps036 (referenceData041Base (referenceData119 source)))
            (rawTaylorOrder036 (referenceData041Base (referenceData119 source)))
            (rawIdlingSteps041 (referenceData119 source))).testBit bit.val)) = _
  simp only [rawTimeSteps036, rawTaylorOrder036, rawIdlingSteps041,
    rawHistoryBlocks041, referenceData041Base, referenceData119]
  simp only [executable_historyIdleClockEnd_expanded_eq119]
  rw [correctedBranchHistoryBasis119_read_clock, constantBits]
  simp only [clockBits119, qubitBasisLittleEndianIndex_basis]

theorem h2BeforeQ119_idle_flag_value_numeric
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    h2BeforeQ119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index)
        (historyLessThanIdleEndWire (ExecutableLayout119 source domain)) =
      decide (index.clock.val < source.historyParameters.clockEnd) := by
  rw [h2BeforeQ119_idle_flag_value]
  exact correctedBranchHistoryBasis119_clockLessThanIdleEnd
    source domain fits branch index

theorem h2AfterIdleEnd119_branch_flag_selected
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    h2AfterIdleEnd119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h2SelectedBranch119 index)
        (historyBranchWire (ExecutableLayout119 source domain)) = true := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 index
  change h2AfterIdleEnd119 layout input (historyBranchWire layout) = true
  have value := h2BeforeQ119_branch_flag_value
    source domain fits h2SelectedBranch119 index
  change h2BeforeQ119 layout input (historyBranchWire layout) = _ at value
  unfold h2BeforeQ119 historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction at value
  rw [xorWire_apply_other (historyActiveWire layout)
    (historyBranchWire layout) (historyBranchWire_ne_activeWire layout)] at value
  simpa [h2SelectedBranch119] using value

theorem h2AfterIdleEnd119_time_flag_active
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks) :
    h2AfterIdleEnd119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h2SelectedBranch119 index)
        (historyLessThanTimeWire (ExecutableLayout119 source domain)) = true := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 index
  change h2AfterIdleEnd119 layout input
    (historyLessThanTimeWire layout) = true
  have value := h2BeforeQ119_time_flag_value
    source domain fits h2SelectedBranch119 index
  change h2BeforeQ119 layout input (historyLessThanTimeWire layout) = _ at value
  unfold h2BeforeQ119 historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction at value
  rw [xorWire_apply_other (historyActiveWire layout)
    (historyLessThanTimeWire layout)
    (historyLessThanTimeWire_ne_activeWire layout)] at value
  simpa [clockActive] using value

theorem h2AfterIdleEnd119_idle_flag_active
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks) :
    h2AfterIdleEnd119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h2SelectedBranch119 index)
        (historyLessThanIdleEndWire (ExecutableLayout119 source domain)) = true := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 index
  change h2AfterIdleEnd119 layout input
    (historyLessThanIdleEndWire layout) = true
  have value := h2BeforeQ119_idle_flag_value_numeric
    source domain fits h2SelectedBranch119 index
  change h2BeforeQ119 layout input (historyLessThanIdleEndWire layout) = _ at value
  unfold h2BeforeQ119 historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction at value
  rw [xorWire_apply_other (historyActiveWire layout)
    (historyLessThanIdleEndWire layout)
    (historyLessThanIdleEndWire_ne_activeWire layout)] at value
  have clockBeforeEnd : index.clock.val < source.historyParameters.clockEnd :=
    lt_trans clockActive source.historyWellFormed.2.2.2.2
  simpa [clockBeforeEnd] using value

theorem historyTaylorInvalidClockBasisAction_selected_active119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 index
    historyTaylorInvalidClockBasisAction layout
        (h2AfterIdleEnd119 layout input) =
      h2AfterIdleEnd119 layout input := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 index
  have branchValue := h2AfterIdleEnd119_branch_flag_selected
    source domain fits index
  have idleValue := h2AfterIdleEnd119_idle_flag_active
    source domain fits index clockActive
  unfold historyTaylorInvalidClockBasisAction
    historyTaylorInvalidClockCondition
  rw [branchValue, idleValue]
  simp [xorWire]

end
end ExecutableHistoryExecutableHistory
