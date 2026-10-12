import QLean.Generator.Implementation.ProbabilityGeneratorFullOperatorCorrectness
import QLean.History.Foundation.QModel

open Matrix

namespace HistoryBlockEncoding
namespace M09Bridge

open ProbabilityGeneratorQProof
open ProbabilityGeneratorQProof.QParameters
open HistoryBlockEncoding.QModel

noncomputable section

/-- The nine-stage analytic operator is recorded full-space implementation semantics. -/
def recordedFullSpaceQ (p : QParameters) :=
  ProbabilityGeneratorFullAnalyticOperator p

/-- The configuration-to-register bridge is entrywise on legal encodings. -/
theorem encodedQMatrix_entry
    {p : QParameters} (output input : QConfiguration p) :
    encodedQMatrix (delimiterEncoding output) (delimiterEncoding input) =
      configurationQMatrix output input :=
  encodedQMatrix_encoding output input

/-- The full-space canonical embedding is exactly the scalar extension of the pure encoding. -/
def encodedQComplexMatrix (p : QParameters) :
    Matrix (RegisterBasis p.systemWidth) (RegisterBasis p.systemWidth) ℂ :=
  fun output input => (encodedQMatrix output input : ℂ)

theorem canonicalEmbeddedQ_eq_encodedQComplexMatrix (p : QParameters) :
    embeddedProbabilityGenerator p = encodedQComplexMatrix p := by
  ext output input
  exact canonicalEmbeddedQ_eq_cast output input

/-- The success block uses the independently defined encoded model matrix. -/
theorem recordedFullSpaceQ_success_block (p : QParameters) :
    IsApproxQubitBlockEncoding
      (allZeroAncilla p.ancillaWidth)
      (recordedFullSpaceQ p)
      (encodedQComplexMatrix p)
      (3 * p.K)
      0 := by
  rw [← canonicalEmbeddedQ_eq_encodedQComplexMatrix]
  exact ProbabilityGeneratorFullAnalyticOperator_blockEncoding_correct p

end

end M09Bridge
end HistoryBlockEncoding
