import QLean.SignalProcessing.M13bFiniteOuterCompiler
import QLean.Circuits.Foundation.CircuitListLemmas

/-! Exact pre-optimization resource accounting for the shared outer compiler.
Angles never select a gate count. The external-control expansion is counted
from its actual primitive compiler, not from an asymptotic upper bound. -/

set_option autoImplicit false
set_option warningAsError true

namespace M13bFiniteOuterCompiler

open VerifiedCircuitCore NativeFixedPointPrimitive

def leafCost {n m : Nat} (layout : ExternallyControlledCircuitLayout n m)
    (gate : PrimitiveGate n) : Nat :=
  (compileExternallyControlledPrimitive layout gate).gateCount

def controlCost {n m : Nat} (layout : ExternallyControlledCircuitLayout n m)
    (circuit : Circuit (PrimitiveGate n)) : Nat :=
  (circuit.flatten.map (leafCost layout)).sum

@[simp] theorem leafCost_inverse {n m : Nat}
    (layout : ExternallyControlledCircuitLayout n m) (gate : PrimitiveGate n) :
    leafCost layout gate.inverse = leafCost layout gate := by
  cases gate <;> rfl

@[simp] theorem leafCost_phase {n m : Nat}
    (layout : ExternallyControlledCircuitLayout n m) (angle : AngleExpr) (wire : Fin n) :
    leafCost layout (.phaseShift angle wire) = 5 := rfl

@[simp] theorem controlCost_gate {n m : Nat}
    (layout : ExternallyControlledCircuitLayout n m) (gate : PrimitiveGate n) :
    controlCost layout (.gate gate) = leafCost layout gate := by
  simp [controlCost, Circuit.flatten]

@[simp] theorem controlCost_seq {n m : Nat}
    (layout : ExternallyControlledCircuitLayout n m)
    (left right : Circuit (PrimitiveGate n)) :
    controlCost layout (.seq left right) = controlCost layout left + controlCost layout right := by
  simp [controlCost, Circuit.flatten]

@[simp] theorem controlCost_reverse {n m : Nat}
    (layout : ExternallyControlledCircuitLayout n m) (circuit : Circuit (PrimitiveGate n)) :
    controlCost layout (circuit.reverse PrimitiveGate.inverse) = controlCost layout circuit := by
  simp [controlCost, Circuit.flatten_reverse, List.map_map, Function.comp_def]

theorem controlled_gateCount {n : Nat} (plan : Plan n)
    (circuit : Circuit (PrimitiveGate n)) :
    (plan.controlled circuit).gateCount = controlCost plan.layout circuit := by
  unfold Plan.controlled Circuit.gateCount
  rw [flatten_sequence_decodeSupportedPrimitiveCircuit_compile,
    flatten_compileExternallyControlledCircuit]
  simp only [controlCost]
  induction circuit.flatten with
  | nil => rfl
  | cons gate rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih]
      rfl

def programCost (signal phase : Nat) : List PhaseProgramStep → Nat
  | [] => 0
  | .signal _ :: rest => signal + programCost signal phase rest
  | .projectorPhase _ _ :: rest => phase + programCost signal phase rest

theorem programCost_conjugate (signal phase : Nat) (program : List PhaseProgramStep) :
    programCost signal phase (M13bConjugatePhaseWord.conjugatePhaseProgram119 program) =
      programCost signal phase program := by
  induction program with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [M13bConjugatePhaseWord.conjugatePhaseProgram119,
        M13bConjugatePhaseWord.conjugatePhaseProgramStep119, programCost] at ih ⊢ <;> exact ih

theorem word_controlCost {n : Nat} (plan : Plan n) (phase : Nat)
    (sourceCost : ∀ angle, controlCost plan.layout (plan.sourcePhase angle) = phase)
    (targetCost : ∀ angle, controlCost plan.layout (plan.targetPhase angle) = phase)
    (program : List PhaseProgramStep) :
    controlCost plan.layout (plan.word program) =
      programCost (controlCost plan.layout plan.signalCircuit) phase program := by
  induction program with
  | nil => rfl
  | cons step rest ih =>
      change controlCost plan.layout (.seq (plan.step step) (plan.word rest)) = _
      rw [controlCost_seq, ih]
      cases step with
      | signal direction => cases direction <;> simp [Plan.step, programCost]
      | projectorPhase role angle => cases role <;> simp [Plan.step, programCost, sourceCost, targetCost]

theorem compile_gateCount {n : Nat} (plan : Plan n) (phase : Nat)
    (sourceCost : ∀ angle, controlCost plan.layout (plan.sourcePhase angle) = phase)
    (targetCost : ∀ angle, controlCost plan.layout (plan.targetPhase angle) = phase)
    (program : List PhaseProgramStep) (reflectionAngle : AngleExpr) :
    (plan.compile program reflectionAngle).gateCount =
      11 + 4 * programCost (controlCost plan.layout plan.signalCircuit) phase program + phase := by
  have wordCount := fun word => (controlled_gateCount plan (plan.word word)).trans
    (word_controlCost plan phase sourceCost targetCost word)
  simp only [Plan.compile, outerFromComputeAndReflection, Circuit.gateCount_sequence,
    Circuit.gateCount_reverse, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [Plan.hermitianCompute, Plan.successReflection, Circuit.gateCount_sequence,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wordCount,
    programCost_conjugate, programCost]
  change _ = _
  simp only [Circuit.gateCount, Circuit.flatten, List.length_singleton]
  omega

end M13bFiniteOuterCompiler
