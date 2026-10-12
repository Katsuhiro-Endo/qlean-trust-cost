import QLean.History.Implementation.HistoryPipelineH2ConfigurationTransport

set_option autoImplicit false

namespace ExecutableHistoryExecutableHistory

open SpectralSamplingProof.Analytic
open ExecutableHistoryHistoryEmbedding
open HistoryPipelineReferenceRawCompiler
open HistoryPipelineReferenceRawValueConstructor
open HistoryPipelineReferenceRawValueConstructorV3
open HistoryPipelineReferenceAdmissibility041

theorem executable_historyIdleClockEnd_eq119
    (source : AlignedCommonSource119) :
    historyIdleClockEnd
        (rawTimeSteps036 (referenceData041Base (referenceData119 source)))
        (rawTaylorOrder036 (referenceData041Base (referenceData119 source)))
        (rawIdlingSteps041 (referenceData119 source)) =
      source.historyParameters.clockEnd := by
  rw [source.clockEndExact]
  unfold historyIdleClockEnd historyIdleClockBlocks
  simp only [rawTimeSteps036, rawTaylorOrder036, rawIdlingSteps041,
    rawHistoryBlocks041, referenceData041Base, referenceData119]
  let blockSize := historyIdleBlockSize source.historyParameters.taylorOrder
  have blockSizePositive : 0 < blockSize := by
    unfold blockSize historyIdleBlockSize historyOrderWidth
    positivity
  have productPositive : 0 < source.historyBlocks * blockSize :=
    Nat.mul_pos source.historyBlocksPositive blockSizePositive
  have productPred : source.historyBlocks * blockSize - 1 + 1 =
      source.historyBlocks * blockSize := Nat.sub_add_cancel (by omega)
  change source.historyParameters.physicalClocks +
      (source.historyBlocks * blockSize - 1 + 1) / blockSize =
    source.historyParameters.physicalClocks + source.historyBlocks
  rw [productPred]
  simp [blockSizePositive]

theorem executable_historyClockWidth_eq119
    (source : AlignedCommonSource119) :
    historyClockWidth
        (rawTimeSteps036 (referenceData041Base (referenceData119 source)))
        (rawTaylorOrder036 (referenceData041Base (referenceData119 source)))
        (rawIdlingSteps041 (referenceData119 source)) =
      historyClockWidth source.historyParameters.physicalClocks
        source.historyParameters.taylorOrder
        (source.historyBlocks *
          historyIdleBlockSize source.historyParameters.taylorOrder - 1) := by
  simp only [rawTimeSteps036, rawTaylorOrder036, rawIdlingSteps041,
    rawHistoryBlocks041, referenceData041Base, referenceData119]

theorem executable_historyIdleClockEnd_expanded_eq119
    (source : AlignedCommonSource119) :
    historyIdleClockEnd source.historyParameters.physicalClocks
        source.historyParameters.taylorOrder
        (source.historyBlocks *
          historyIdleBlockSize source.historyParameters.taylorOrder - 1) =
      source.historyParameters.clockEnd := by
  simpa only [rawTimeSteps036, rawTaylorOrder036, rawIdlingSteps041,
    rawHistoryBlocks041, referenceData041Base, referenceData119] using
    executable_historyIdleClockEnd_eq119 source

end ExecutableHistoryExecutableHistory
