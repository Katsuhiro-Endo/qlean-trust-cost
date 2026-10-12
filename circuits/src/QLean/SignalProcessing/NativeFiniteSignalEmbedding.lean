import QLean.History.Implementation.HistoryPipelineFiniteAlignedEmbedding
import QLean.SignalProcessing.NativeSignalQSVTActual

/-! Finite physical signal-frame basis, equal to the established image. -/

set_option autoImplicit false
set_option warningAsError true

namespace NativeSignalQSVTActual

open VerifiedCircuitCore
open ExecutableHistoryQbPlusCleanBlock
open ExecutableHistoryAlignedPhysicalP18

def finiteSignalBasis119 (n : Nat) (signalBit : Fin 2)
    (data : QubitBasis n) : QubitBasis (blockQubits119 n) :=
  fun wire =>
    if wire = signalWire119 n then signalBit = 1
    else finiteBlockBasis119 data wire

theorem finiteSignalBasis119_eq (n : Nat) (signalBit : Fin 2)
    (data : QubitBasis n) :
    finiteSignalBasis119 n signalBit data =
      NativeSignalPhase.basis n signalBit data := by
  funext wire
  by_cases signal : wire = signalWire119 n
  · simp [finiteSignalBasis119, NativeSignalPhase.basis, signal]
  · simp [finiteSignalBasis119, NativeSignalPhase.basis,
      finiteBlockBasis119_eq, signal]

end NativeSignalQSVTActual
