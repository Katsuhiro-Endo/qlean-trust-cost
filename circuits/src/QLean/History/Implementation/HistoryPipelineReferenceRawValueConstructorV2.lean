import QLean.History.Implementation.HistoryPipelineReferenceRawValueConstructor

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace HistoryPipelineReferenceRawValueConstructorV2

open Matrix
open HistoryBlockEncoding
open VerifiedCircuitCore
open HistoryPipelineReferenceRawCompiler
open HistoryPipelineReferenceRawSemanticCompiler
open HistoryPipelineReferenceEntryDecoder
open HistoryPipelineReferenceRawValueConstructor

noncomputable section

/-!
  DevelopmentStage038 is a value-only repair of the generator fragment.  The history
  value is deliberately reused from DevelopmentStage036.  The P17/P44 raw schema has a
  stricter contract than the old value constructor: its control-work list is
  the empty list, and its register widths are the widths of one positive
  `QParameters` record.  We therefore make that register choice explicit and
  keep all model/initial/angle data on the already certified decoder path.
-/

abbrev ReferenceData038 {Configuration : Type*} [Fintype Configuration] :=
  ReferenceData036 (Configuration := Configuration)

end

end HistoryPipelineReferenceRawValueConstructorV2
