import QLean.SignalProcessing.M13bConjugatePhaseWord
import QLean.SignalProcessing.M13bExternallyControlledCompute

/-! A computable finite-data construction of the complete primitive kernel
reflection.  It consumes a signal circuit, phase-image builders, an external
control layout and one finite phase program.  No real-angle evaluation or
operator target is an input. -/

set_option autoImplicit false
set_option warningAsError true

namespace M13bFiniteOuterCompiler

open VerifiedCircuitCore

structure Plan (sourceQubits : Nat) where
  signalCircuit : Circuit (PrimitiveGate sourceQubits)
  sourcePhase : AngleExpr → Circuit (PrimitiveGate sourceQubits)
  targetPhase : AngleExpr → Circuit (PrimitiveGate sourceQubits)
  layout : ExternallyControlledCircuitLayout sourceQubits (sourceQubits + 3)

def Plan.step {n : Nat} (plan : Plan n) :
    NativeFixedPointPrimitive.PhaseProgramStep →
      Circuit (PrimitiveGate n)
  | .signal .forward => plan.signalCircuit
  | .signal .adjoint => plan.signalCircuit.reverse PrimitiveGate.inverse
  | .projectorPhase .source angle => plan.sourcePhase angle
  | .projectorPhase .target angle => plan.targetPhase angle

def Plan.word {n : Nat} (plan : Plan n)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep) :
    Circuit (PrimitiveGate n) :=
  Circuit.sequence (program.map plan.step)

/-- The existing leaf-wise verified external-control decoder is also the
finite-data construction path.  Every constructor of `PrimitiveGate` is
supported, so the proof is only a type check and cannot choose a circuit. -/
def Plan.controlled {n : Nat} (plan : Plan n)
    (circuit : Circuit (PrimitiveGate n)) :
    Circuit (PrimitiveGate (n + 3)) :=
  let supported : ∀ gate, gate ∈ circuit.flatten →
      IsExternallyControllablePrimitive gate := by
    intro gate _
    cases gate <;> trivial
  Circuit.sequence ((decodeSupportedPrimitiveCircuit circuit supported).map
    fun leaf => leaf.compile plan.layout)

def Plan.hermitianCompute {n : Nat} (plan : Plan n)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep) :
    Circuit (PrimitiveGate (n + 3)) :=
  let h : Circuit (PrimitiveGate (n + 3)) := .gate (.h plan.layout.control)
  let x : Circuit (PrimitiveGate (n + 3)) := .gate (.x plan.layout.control)
  Circuit.sequence [h,
    Circuit.sequence [x, plan.controlled (plan.word program), x,
      plan.controlled (plan.word
        (M13bConjugatePhaseWord.conjugatePhaseProgram119 program))], h]

def Plan.successReflection {n : Nat} (plan : Plan n)
    (reflectionAngle : AngleExpr) :
    Circuit (PrimitiveGate (n + 3)) :=
  let x : Circuit (PrimitiveGate (n + 3)) := .gate (.x plan.layout.control)
  Circuit.sequence [
    Circuit.sequence [x,
      plan.controlled (plan.word [.projectorPhase .target reflectionAngle]), x],
    .gate (.phaseShift reflectionAngle plan.layout.control)]

def outerFromComputeAndReflection {n : Nat}
    (compute reflection : Circuit (PrimitiveGate n)) :
    Circuit (PrimitiveGate n) :=
  Circuit.sequence [compute, reflection, compute.reverse PrimitiveGate.inverse]

/-- Executable CP03 assembly: Hermitianization, external control, success
reflection and outer uncomputation are all generated from the finite plan. -/
def Plan.compile {n : Nat} (plan : Plan n)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (reflectionAngle : AngleExpr) :
    Circuit (PrimitiveGate (n + 3)) :=
  outerFromComputeAndReflection (plan.hermitianCompute program)
    (plan.successReflection reflectionAngle)

end M13bFiniteOuterCompiler
