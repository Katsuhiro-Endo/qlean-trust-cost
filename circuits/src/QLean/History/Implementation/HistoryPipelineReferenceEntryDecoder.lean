import QLean.History.Implementation.HistoryPipelineReferenceRawSemanticCompiler
import QLean.History.Implementation.HistoryPipelineCompatiblePhysicalM10

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace HistoryPipelineReferenceEntryDecoder

open Matrix
open HistoryBlockEncoding
open VerifiedCircuitCore
open HistoryPipelineReferenceRawCompiler
open HistoryPipelineReferenceRawSemanticCompiler
open HistoryPipelineCompatiblePhysicalM10

noncomputable section

/-!
  DevelopmentStage035 constructive first layer.

  A raw P15 packet contains executable angle syntax, while the reference
  entry is a rational value.  The following encoder stores one reference
  entry in the actual `AngleExpr` grammar and the decoder is the current
  rotation evaluator used by the compatible P15 layer.  This is deliberately
  an entry-level component: it does not pretend to be the full raw packet or
  an admissibility proof.
-/

def encodedEntryAngle035 (value : ℚ) : AngleExpr :=
  .mul (.const 2)
    (.acos (.sqrt (.const (((value : ℝ) + 1) / 2))))

/-! The exact angle/provider fragment has the same types as the corresponding
    raw packet fields.  It is constructed from one reference row/column and
    never stores a desired equality as a field. -/

/-! The only admissibility needed by this first entry layer is the actual
    interval bound for the encoded scalar.  It is kept separate from the
    much stronger full HistoryP15P16Admissible203 record. -/

/-! Fully applied d=2 positives and semantic negatives. -/

end

end HistoryPipelineReferenceEntryDecoder
