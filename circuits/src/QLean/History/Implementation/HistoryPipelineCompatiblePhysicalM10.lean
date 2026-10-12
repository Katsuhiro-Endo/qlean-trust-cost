import QLean.History.Implementation.HistoryPipelineHistoryExtendedBlocks
import QLean.History.Foundation.HistorySpec
import QLean.History.Foundation.HistoryLCU

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace HistoryPipelineCompatiblePhysicalM10

open Matrix
open HistoryBlockEncoding

noncomputable section

open VerifiedCircuitCore

/-!  The declarations below are the compatible physical layer.  They are
    intentionally structural: no old `Checkpoint2` import is needed and no
    desired history operator is stored as a circuit/certificate field. -/

/-!  Current HistoryAssembly/P05 data remains available as a separate, typed
    executable boundary.  These aliases expose its actual source order and
    denotation without identifying it with the old HistoryBlockEncoding history matrix. -/

end
end HistoryPipelineCompatiblePhysicalM10
