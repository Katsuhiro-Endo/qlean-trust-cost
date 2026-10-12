import QLean.History.Implementation.HistoryPipelineP05SandwichReduction

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

noncomputable section

theorem repairedP05H1ForwardTarget119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    h1SelectorRecordedOperator
        (historyH4CorrectedConcreteSelectorSpecification
          (ExecutableLayout119 source domain)
          (correctedSelectorHighAngleExpr119 source)
          correctedSelectorLowAngleExpr119
          correctedSelectorLowAngleExpr119) =
      historySelectorPreparationOperator internalZeroSymbolEnvironment
        (correctedSelectorParameters119 source domain) := by
  rfl

end

end ExecutableHistoryExecutableHistory
