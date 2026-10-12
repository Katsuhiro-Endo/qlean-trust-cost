import QLean.Generator.Analysis.QGenerator
import QLean.History.Foundation.ModelQ

open Matrix

namespace HistoryBlockEncoding
namespace QModel

open ProbabilityGeneratorQProof
open ProbabilityGeneratorQProof.QParameters

noncomputable section

/-- Concrete model matrix indexed only by legal configurations. -/
def configurationQMatrix {p : QParameters} :
    Matrix (QConfiguration p) (QConfiguration p) ℚ :=
  fun output input => configurationProbabilityGenerator output input

@[simp] theorem configurationQMatrix_apply
    {p : QParameters} (output input : QConfiguration p) :
    configurationQMatrix output input =
      configurationProbabilityGenerator output input := rfl

/-- Pure delimiter encoding of the model matrix into the register basis. -/
def encodedQMatrix {p : QParameters} :
    Matrix (RegisterBasis p.systemWidth) (RegisterBasis p.systemWidth) ℚ :=
  ModelQ.encodedMatrix decodeDelimiter (configurationQMatrix (p := p))

@[simp] theorem encodedQMatrix_encoding
    {p : QParameters} (output input : QConfiguration p) :
    encodedQMatrix (delimiterEncoding output) (delimiterEncoding input) =
      configurationQMatrix output input := by
  exact ModelQ.encodedMatrix_encode
    { encode := delimiterEncoding
      decode := decodeDelimiter
      decode_encode := decodeDelimiter_encoding }
    (configurationQMatrix (p := p)) output input

/-- The canonical complex-valued embedding is the scalar extension of the pure embedding. -/
theorem canonicalEmbeddedQ_eq_cast
    {p : QParameters} (output input : RegisterBasis p.systemWidth) :
    embeddedProbabilityGenerator p output input =
      (encodedQMatrix output input : ℂ) := by
  classical
  unfold ProbabilityGeneratorQProof.embeddedProbabilityGenerator
    encodedQMatrix ModelQ.encodedMatrix configurationQMatrix
  cases hOutput : decodeDelimiter output <;>
    cases hInput : decodeDelimiter input <;>
    simp [hOutput, hInput]

end

end QModel
end HistoryBlockEncoding
