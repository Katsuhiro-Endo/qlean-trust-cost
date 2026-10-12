import QLean.History.Implementation.HistoryPipelineExecutableCorrectedInput
import QLean.History.Implementation.HistoryPipelineHistoryExtendedBlocks
import QLean.History.Integration.HistoryAssemblyP15P44Adapter
import QLean.Spectral.Circuits.HistoryH4CorrectedClean

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

abbrev ExecutableRaw119 (source : AlignedCommonSource119) :=
  executableRawInput119 source

abbrev ExecutableAdmissible119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  executableCorrectedAdmissible119 source domain

abbrev ExecutableLayout119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  ScientificWidthGenericContract.correctedLayout259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)

abbrev ExecutableClockEvidence119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  HistoryAssemblyComponentIntegration.p16ConcreteEvidence145
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)

end
end ExecutableHistoryExecutableHistory
