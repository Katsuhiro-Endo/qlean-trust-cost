import QLean.SignalProcessing.NativeSignalPhase

set_option autoImplicit false

namespace NativeSignalQSVTGeneric

open JenningsHistory
open VerifiedCircuitCore
open ExecutableHistoryQbPlusCleanBlock

structure Program (dataQubits : Nat) where
  signalCircuit : Circuit (PrimitiveGate (blockQubits119 dataQubits))

end NativeSignalQSVTGeneric
