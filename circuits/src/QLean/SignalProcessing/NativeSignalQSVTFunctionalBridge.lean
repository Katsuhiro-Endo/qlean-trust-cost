import QLean.SignalProcessing.NativeSignalQSVTActual
import QLean.SignalProcessing.KernelQSPGeneralQSPIntegration
import QLean.SignalProcessing.KernelReflectionRightSVTSpectralTransfer
import VerifiedMath.Complexification

set_option autoImplicit false

namespace NativeSignalQSVTFunctionalBridge

open JenningsHistory
open VerifiedCircuitCore
open NativeSignalQSVTGeneric
open NativeSignalQSVTActual

/-- Embeds a real Euclidean vector into the complex coordinate space selected
by a clean compression. -/
def complexifyVector {index : Type*}
    (vector : EuclideanSpace ℝ index) : index → ℂ :=
  VerifiedMath.Complexification.euclideanVector vector

end NativeSignalQSVTFunctionalBridge
