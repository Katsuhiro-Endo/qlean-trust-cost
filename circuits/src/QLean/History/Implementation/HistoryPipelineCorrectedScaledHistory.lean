import QLean.History.Implementation.HistoryPipelineCorrectedLCU
import QLean.History.Implementation.HistoryPipelineReferenceM10Bridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix

noncomputable section

theorem corrected_scaledHistory_entry_eq_normalizedTarget119
    {Configuration : Type*} [Fintype Configuration]
    [DecidableEq Configuration]
    (p : HistoryBlockEncoding.HistorySpec.Parameters)
    (modelQ : Matrix Configuration Configuration ℚ)
    (initial : Configuration → ℚ)
    (wf : HistoryBlockEncoding.HistorySpec.WellFormed p)
    (row col : HistoryBlockEncoding.HistorySpec.Index Configuration p) :
    JenningsHistory.scaledHistory
        (ExecutableHistoryReferenceM10Bridge.translatedSystem p modelQ initial wf)
        (correctedAlpha119 p.taylorOrder)
        (ExecutableHistoryReferenceM10Bridge.indexEquiv p row)
        (ExecutableHistoryReferenceM10Bridge.indexEquiv p col) =
      correctedNormalizedHistoryTarget119 p modelQ row col := by
  change
    JenningsHistory.historyMatrix
          (ExecutableHistoryReferenceM10Bridge.translatedSystem p modelQ initial wf)
          (ExecutableHistoryReferenceM10Bridge.indexEquiv p row)
          (ExecutableHistoryReferenceM10Bridge.indexEquiv p col) /
        correctedAlpha119 p.taylorOrder =
      (correctedAlpha119 p.taylorOrder)⁻¹ *
        correctedCastMatrix119
          (HistoryBlockEncoding.HistorySpec.H_hist p modelQ) row col
  rw [ExecutableHistoryReferenceM10Bridge.history_matrix_entry_eq_cast_h_hist
    p modelQ initial wf row col]
  simp [HistoryBlockEncoding.Checkpoint2.RealHistory.castMatrix,
    correctedCastMatrix119, div_eq_mul_inv, mul_comm]

end

end ExecutableHistoryExecutableHistory
