import QLean.History.Integration.HistoryAdmissibilityActualAdapter
import QLean.History.HistoryAnalyticParameters194

set_option autoImplicit false
set_option maxRecDepth 100000

namespace HistoryAdmissibility

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ProbabilityGeneratorQProof
open HistoryAnalyticParameterExistence194

noncomputable section

abbrev RawInput196 := HistoryAdmissibilityActualAdapter.RawInput196
abbrev CorrectedAdmissible196 (input : RawInput196) :=
  HistoryAdmissibilityActualAdapter.CorrectedAdmissible196 input

end

end HistoryAdmissibility
