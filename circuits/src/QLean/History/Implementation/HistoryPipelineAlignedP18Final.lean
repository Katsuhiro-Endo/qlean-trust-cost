import QLean.History.Implementation.HistoryPipelineP18Final
import QLean.History.Implementation.HistoryPipelineAlignedPhysicalP18Block

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option warningAsError true

namespace ExecutableHistoryExecutableAlignedP18

open Matrix
open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryCore
open ExecutableHistoryImplementationRole
open ExecutableHistoryAlignedPhysicalP18
open ExecutableHistoryAlignedPhysicalP18Block
open ExecutableHistoryExecutableP18
open ExecutableHistoryExecutableHistory
open ExecutableHistoryHistoryEmbedding

noncomputable section

abbrev ExecutableAlignedP18Qubits119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119
      source domain fits assumptions) : Nat :=
  AlignedTotalQubits119
    (executableInternalHHistory119 source domain fits assumptions circuitSource)

def executableAlignedP18Circuit119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119
      source domain fits assumptions) :
    Circuit (PrimitiveGate
      (ExecutableAlignedP18Qubits119 source domain fits assumptions
        circuitSource)) :=
  alignedP18Circuit119
    (executableInternalHHistory119 source domain fits assumptions circuitSource)

end

end ExecutableHistoryExecutableAlignedP18
