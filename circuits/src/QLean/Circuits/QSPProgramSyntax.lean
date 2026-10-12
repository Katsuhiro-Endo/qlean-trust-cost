import QLean.Circuits.Foundation.QSPAngles
import QLean.Circuits.NativeFixedPointPrimitive
import VerifiedMath.Quantum.QSP

/-! Pure QSP-word conversion, independent of checkpoint builders.  Both
the finite emitter and theoretical assembly use these exact constructors. -/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.CheckpointCircuits

def cp03ProgramStep {AngleType : Type} [VerifiedCircuitCore.QSPCircuitAngle AngleType] :
    VerifiedMath.Quantum.QSP.Step AngleType →
      NativeFixedPointPrimitive.PhaseProgramStep
  | .signal .forward => .signal .forward
  | .signal .adjoint => .signal .adjoint
  | .projectorPhase .source angle =>
      .projectorPhase .source (VerifiedCircuitCore.QSPCircuitAngle.toCircuitAngle angle)
  | .projectorPhase .target angle =>
      .projectorPhase .target (VerifiedCircuitCore.QSPCircuitAngle.toCircuitAngle angle)

def cp03ProgramWord {AngleType : Type} [VerifiedCircuitCore.QSPCircuitAngle AngleType]
    (word : VerifiedMath.Quantum.QSP.Word AngleType) :
    List NativeFixedPointPrimitive.PhaseProgramStep :=
  word.map cp03ProgramStep

end QLean.Circuits.CheckpointCircuits
