import QLean.SignalProcessing.NativeSignalQSVTGeneric
import QLean.History.Implementation.HistoryPipelineAlignedP18Final

set_option autoImplicit false

namespace NativeSignalQSVTActual

open JenningsHistory
open VerifiedCircuitCore
open ExecutableHistoryQbPlusCleanBlock
open NativeSignalQSVTGeneric

noncomputable def dataEmbedding {dataQubits : Nat} {index : Type*}
    (embedding : index ↪ QubitBasis dataQubits) :
    (Fin 2 × index) ↪ QubitBasis (blockQubits119 dataQubits) where
  toFun := fun pair => NativeSignalPhase.embedding dataQubits (pair.1, embedding pair.2)
  inj' := by
    intro left right h
    have hpair := (NativeSignalPhase.embedding dataQubits).injective h
    have hbit := congrArg Prod.fst hpair
    have hdata := congrArg Prod.snd hpair
    exact Prod.ext hbit (embedding.injective hdata)

noncomputable def executableAlignedP18Program
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) :
    Program (ExecutableHistoryAlignedPhysicalP18.AlignedDataQubits119
      (ExecutableHistoryExecutableP18.executableInternalHHistory119 source domain fits
        assumptions circuitSource)) where
  signalCircuit := ExecutableHistoryExecutableAlignedP18.executableAlignedP18Circuit119
    source domain fits assumptions circuitSource

noncomputable def executableSignalEmbedding
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) :=
  dataEmbedding (ExecutableHistoryAlignedPhysicalP18.alignedDataEmbedding119
    (ExecutableHistoryExecutableP18.executableInternalHHistory119 source domain fits
      assumptions circuitSource))

end NativeSignalQSVTActual
