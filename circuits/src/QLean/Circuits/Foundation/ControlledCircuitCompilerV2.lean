import QLean.Circuits.Foundation.ClassicalMinimumWorkClean
import QLean.Circuits.Foundation.ControlledHadamard

/-!
# Normalized externally-controlled circuit compiler (v2)

This is a parallel replacement for the P44 lowering boundary.  It deliberately
does not import or alter `ControlledCircuitCompiler`: the two implementations
can be checked independently during the approved migration.

The target gate language is syntactically closed to the six normalized
constructors `X`, `H`, `Ry`, `PhaseShift`, `CNOT`, and `Toffoli`.  The two
compiler work wires are explicit data of `ControlLayout`; no caller supplies
an existential work-register witness.
-/

namespace VerifiedCircuitCore

noncomputable section

namespace ControlledCircuitCompilerV2

/-- Placement and explicit clean-work resources for one external control.

The `work` bundle has exactly two wires because the shared positive
multi-controlled-X decomposition used by the Toffoli branch requires two
clean work bits for its three controls. -/
structure ControlLayout (sourceQubits targetQubits : Nat) where
  placement : Fin sourceQubits ↪ Fin targetQubits
  control : Fin targetQubits
  work : Fin 2 → Fin targetQubits
  control_ne_placed : ∀ source, control ≠ placement source
  work_injective : Function.Injective work
  work_ne_control : ∀ slot, work slot ≠ control
  work_ne_placed : ∀ slot source, work slot ≠ placement source

namespace ControlLayout

/-- The work bundle in the source order expected by the shared Boolean
compiler. -/
def workList {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) : List (Fin targetQubits) :=
  [layout.work 0, layout.work 1]

/-- Basis states on which the explicit compiler work bundle is clean. -/
def workIsClean {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (basis : QubitBasis targetQubits) : Prop :=
  ∀ slot, basis (layout.work slot) = false

@[simp] theorem workList_length {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) :
    layout.workList.length = 2 := by
  rfl

theorem work_ne_each_other {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) :
    layout.work 0 ≠ layout.work 1 := by
  intro equal
  have slots : (0 : Fin 2) = 1 := layout.work_injective equal
  norm_num at slots

theorem workList_nodup {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) : layout.workList.Nodup := by
  simp [workList, work_ne_each_other]

/-- The three logical controls, the explicit two-wire work bundle, and the
logical target of the controlled-Toffoli lowering are pairwise distinct. -/
theorem toffoliLayout_nodup {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (firstControl secondControl target : Fin sourceQubits)
    (controlsDifferent : firstControl ≠ secondControl)
    (firstDifferent : firstControl ≠ target)
    (secondDifferent : secondControl ≠ target) :
    ([layout.control, layout.placement firstControl,
      layout.placement secondControl] ++ layout.workList ++
        [layout.placement target]).Nodup := by
  have placedControlsDifferent :
      layout.placement firstControl ≠ layout.placement secondControl := by
    intro equal
    exact controlsDifferent (layout.placement.injective equal)
  have placedFirstDifferent :
      layout.placement firstControl ≠ layout.placement target := by
    intro equal
    exact firstDifferent (layout.placement.injective equal)
  have placedSecondDifferent :
      layout.placement secondControl ≠ layout.placement target := by
    intro equal
    exact secondDifferent (layout.placement.injective equal)
  have controlDifferentWork (slot : Fin 2) : layout.control ≠ layout.work slot :=
    (layout.work_ne_control slot).symm
  have placedDifferentWork (slot : Fin 2) (source : Fin sourceQubits) :
      layout.placement source ≠ layout.work slot :=
    (layout.work_ne_placed slot source).symm
  have firstWorkDifferentTarget : layout.work 0 ≠ layout.placement target :=
    layout.work_ne_placed 0 target
  have secondWorkDifferentTarget : layout.work 1 ≠ layout.placement target :=
    layout.work_ne_placed 1 target
  simp [workList, layout.control_ne_placed, controlDifferentWork,
    placedDifferentWork, firstWorkDifferentTarget, secondWorkDifferentTarget,
    work_ne_each_other, placedControlsDifferent,
    placedFirstDifferent, placedSecondDifferent]

end ControlLayout

/-- The executable source language accepted by the normalized v2 compiler is
already closed to the six normalized constructors.  This predicate is kept
explicit at the boundary so the output contract remains machine-auditable. -/
def IsNormalizedPrimitive {qubits : Nat} : PrimitiveGate qubits → Prop :=
  fun gate => match gate with
    | .x _ | .h _ | .ry _ _ | .phaseShift _ _ | .cnot _ _ _ |
        .toffoli _ _ _ _ _ _ => True

/-- A source circuit carries no hidden admission evidence: this is the public
flattened-leaf predicate used by clients to certify a complete source AST. -/
def IsNormalizedCircuit {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits)) : Prop :=
  ∀ gate, gate ∈ circuit.flatten → IsNormalizedPrimitive gate

/-- A single source leaf admitted by the v2 lowering boundary.  Keeping the
membership proof in the input type makes it impossible to silently route a
legacy `PrimitiveGate` through a total fallback branch. -/
abbrev NormalizedPrimitiveGate (qubits : Nat) :=
  { gate : PrimitiveGate qubits // IsNormalizedPrimitive gate }

namespace NormalizedPrimitiveGate

def x {qubits : Nat} (target : Fin qubits) : NormalizedPrimitiveGate qubits :=
  ⟨.x target, by simp [IsNormalizedPrimitive]⟩

def h {qubits : Nat} (target : Fin qubits) : NormalizedPrimitiveGate qubits :=
  ⟨.h target, by simp [IsNormalizedPrimitive]⟩

def ry {qubits : Nat} (angle : AngleExpr) (target : Fin qubits) :
    NormalizedPrimitiveGate qubits :=
  ⟨.ry angle target, by simp [IsNormalizedPrimitive]⟩

def phaseShift {qubits : Nat} (angle : AngleExpr) (target : Fin qubits) :
    NormalizedPrimitiveGate qubits :=
  ⟨.phaseShift angle target, by simp [IsNormalizedPrimitive]⟩

def cnot {qubits : Nat} (source target : Fin qubits)
    (different : source ≠ target) : NormalizedPrimitiveGate qubits :=
  ⟨.cnot source target different, by simp [IsNormalizedPrimitive]⟩

def toffoli {qubits : Nat}
    (firstControl secondControl target : Fin qubits)
    (controlsDifferent : firstControl ≠ secondControl)
    (firstDifferent : firstControl ≠ target)
    (secondDifferent : secondControl ≠ target) :
    NormalizedPrimitiveGate qubits :=
  ⟨.toffoli firstControl secondControl target controlsDifferent firstDifferent
    secondDifferent, by simp [IsNormalizedPrimitive]⟩

end NormalizedPrimitiveGate

theorem normalizedPrimitive_inverse {qubits : Nat}
    (gate : PrimitiveGate qubits)
    (normalized : IsNormalizedPrimitive gate) :
    IsNormalizedPrimitive gate.inverse := by
  cases gate <;>
    simp [IsNormalizedPrimitive, PrimitiveGate.inverse] at normalized ⊢

theorem normalizedPrimitive_mapWires
    {sourceQubits targetQubits : Nat}
    (embedding : Fin sourceQubits ↪ Fin targetQubits)
    (gate : PrimitiveGate sourceQubits)
    (normalized : IsNormalizedPrimitive gate) :
    IsNormalizedPrimitive (gate.mapWires embedding) := by
  cases gate <;>
    simp [IsNormalizedPrimitive, PrimitiveGate.mapWires] at normalized ⊢

namespace NormalizedPrimitiveGate

def inverse {qubits : Nat} (source : NormalizedPrimitiveGate qubits) :
    NormalizedPrimitiveGate qubits :=
  ⟨source.1.inverse, normalizedPrimitive_inverse source.1 source.2⟩

def mapWires {sourceQubits targetQubits : Nat}
    (embedding : Fin sourceQubits ↪ Fin targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    NormalizedPrimitiveGate targetQubits :=
  ⟨source.1.mapWires embedding,
    normalizedPrimitive_mapWires embedding source.1 source.2⟩

end NormalizedPrimitiveGate

theorem normalizedCircuit_seq {qubits : Nat}
    (first second : Circuit (PrimitiveGate qubits))
    (firstNormalized : IsNormalizedCircuit first)
    (secondNormalized : IsNormalizedCircuit second) :
    IsNormalizedCircuit (.seq first second) := by
  intro gate member
  rcases List.mem_append.mp (by simpa [Circuit.flatten] using member) with
    firstMember | secondMember
  · exact firstNormalized gate firstMember
  · exact secondNormalized gate secondMember

theorem normalizedCircuit_repeat {qubits : Nat}
    (count : Nat) (body : Circuit (PrimitiveGate qubits))
    (normalized : IsNormalizedCircuit body) :
    IsNormalizedCircuit (.repeat count body) := by
  intro gate member
  rw [Circuit.flatten] at member
  rcases List.mem_flatten.mp member with ⟨stream, streamMember, gateMember⟩
  have stream_eq : stream = body.flatten := (List.mem_replicate.mp streamMember).2
  subst stream
  exact normalized gate gateMember

theorem normalizedCircuit_mapWires
    {sourceQubits targetQubits : Nat}
    (embedding : Fin sourceQubits ↪ Fin targetQubits)
    (circuit : Circuit (PrimitiveGate sourceQubits))
    (normalized : IsNormalizedCircuit circuit) :
    IsNormalizedCircuit (circuit.mapGates (PrimitiveGate.mapWires embedding)) := by
  intro gate member
  rw [Circuit.flatten_mapGates] at member
  rcases List.mem_map.mp member with ⟨sourceGate, sourceMember, rfl⟩
  exact normalizedPrimitive_mapWires embedding sourceGate
    (normalized sourceGate sourceMember)

theorem normalizedCircuit_reverse {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits))
    (normalized : IsNormalizedCircuit circuit) :
    IsNormalizedCircuit (circuit.reverse PrimitiveGate.inverse) := by
  induction circuit with
  | identity =>
      intro gate member
      simp [Circuit.reverse, Circuit.flatten] at member
  | gate value =>
      intro gate member
      have sourceNormalized : IsNormalizedPrimitive value :=
        normalized value (by simp [Circuit.flatten])
      simp [Circuit.reverse, Circuit.flatten] at member
      subst gate
      exact normalizedPrimitive_inverse value sourceNormalized
  | seq first second firstInduction secondInduction =>
      have firstNormalized : IsNormalizedCircuit first := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      have secondNormalized : IsNormalizedCircuit second := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      exact normalizedCircuit_seq _ _
        (secondInduction secondNormalized) (firstInduction firstNormalized)
  | «repeat» count body inductionHypothesis =>
      cases count with
      | zero =>
          intro gate member
          simp [Circuit.reverse, Circuit.flatten] at member
      | succ count =>
          have bodyNormalized : IsNormalizedCircuit body := by
            intro gate member
            exact normalized gate (by
              simp [Circuit.flatten, List.replicate_succ, member])
          exact normalizedCircuit_repeat (Nat.succ count) _
            (inductionHypothesis bodyNormalized)

/-- A complete source AST admitted by the v2 boundary.  The certificate is
flattened-leaf based, so it is stable under all public AST constructors below. -/
structure NormalizedCircuit (qubits : Nat) where
  circuit : Circuit (PrimitiveGate qubits)
  normalized : IsNormalizedCircuit circuit

/-- Forgetting only the certificate is permitted for semantic consumers; no
coercion in the other direction exists, so raw syntax cannot enter the v2
compiler without the checked `?` adapters. -/
instance normalizedCircuitCoe {qubits : Nat} :
    Coe (NormalizedCircuit qubits) (Circuit (PrimitiveGate qubits)) where
  coe source := source.circuit

namespace NormalizedCircuit

def identity (qubits : Nat) : NormalizedCircuit qubits :=
  ⟨.identity, by
    intro gate member
    simp [Circuit.flatten] at member⟩

def gate {qubits : Nat} (source : NormalizedPrimitiveGate qubits) :
    NormalizedCircuit qubits :=
  ⟨.gate source.1, by
    intro gate member
    simp [Circuit.flatten] at member
    subst gate
    exact source.2⟩

def seq {qubits : Nat} (first second : NormalizedCircuit qubits) :
    NormalizedCircuit qubits :=
  ⟨.seq first.circuit second.circuit,
    normalizedCircuit_seq first.circuit second.circuit first.normalized
      second.normalized⟩

def «repeat» {qubits : Nat} (count : Nat) (body : NormalizedCircuit qubits) :
    NormalizedCircuit qubits :=
  ⟨.repeat count body.circuit,
    normalizedCircuit_repeat count body.circuit body.normalized⟩

def mapWires {sourceQubits targetQubits : Nat}
    (embedding : Fin sourceQubits ↪ Fin targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    NormalizedCircuit targetQubits :=
  ⟨source.circuit.mapGates (PrimitiveGate.mapWires embedding),
    normalizedCircuit_mapWires embedding source.circuit source.normalized⟩

def inverse {qubits : Nat} (source : NormalizedCircuit qubits) :
    NormalizedCircuit qubits :=
  ⟨source.circuit.reverse PrimitiveGate.inverse,
    normalizedCircuit_reverse source.circuit source.normalized⟩

end NormalizedCircuit

/-!
The following pass is intentionally a typed normalization recheck, rather than
a second semantic compiler.  Its input already carries the six-constructor
certificate, so reapplying the pass cannot rewrite the certified AST or invent
an identity fallback.
-/

def NormalizedCircuit.normalize {qubits : Nat}
    (source : NormalizedCircuit qubits) : NormalizedCircuit qubits :=
  ⟨source.circuit, source.normalized⟩

@[simp] theorem NormalizedCircuit.normalize_circuit {qubits : Nat}
    (source : NormalizedCircuit qubits) :
    (NormalizedCircuit.normalize source).circuit = source.circuit := rfl

@[simp] theorem NormalizedCircuit.normalize_idempotent {qubits : Nat}
    (source : NormalizedCircuit qubits) :
    (NormalizedCircuit.normalize (NormalizedCircuit.normalize source)).circuit =
      source.circuit := rfl

/-- Half of a symbolic phase angle, represented without evaluating its
symbol environment. -/
def phaseShiftHalfAngle (angle : AngleExpr) : AngleExpr :=
  .div angle (.rational 2 1 (by decide))

@[simp] theorem phaseShiftHalfAngle_eval
    (symbolValue : String → ℝ) (angle : AngleExpr) :
    (phaseShiftHalfAngle angle).eval symbolValue = angle.eval symbolValue / 2 := by
  simp [phaseShiftHalfAngle, AngleExpr.eval]

/-- Exact five-gate positive-control decomposition for a phase shift.
The list is in execution order. -/
def controlledPhaseShiftFiveGateCircuit {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (angle : AngleExpr) (target : Fin sourceQubits) :
    Circuit (PrimitiveGate targetQubits) :=
  Circuit.fromList [
    .phaseShift (phaseShiftHalfAngle angle) layout.control,
    .phaseShift (phaseShiftHalfAngle angle) (layout.placement target),
    .cnot layout.control (layout.placement target)
      (layout.control_ne_placed target),
    .phaseShift (.neg (phaseShiftHalfAngle angle)) (layout.placement target),
    .cnot layout.control (layout.placement target)
      (layout.control_ne_placed target)]

/-- The independent semantic target of one controlled phase-shift leaf. -/
def controlledPhaseShiftTarget {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (angle : AngleExpr) (target : Fin sourceQubits) :
    Operator (QubitBasis targetQubits) :=
  analyticControlledPhaseOperator layout.control (layout.placement target)
    (layout.control_ne_placed target) (angle.eval symbolValue)

/-- The proof-carrying core has exactly six productive branches.  Legacy
constructors are eliminated from their `IsNormalizedPrimitive` contradiction;
there is deliberately no identity fallback. -/
private def controlPrimitiveCore {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : PrimitiveGate sourceQubits)
    (normalized : IsNormalizedPrimitive source) :
    Circuit (PrimitiveGate targetQubits) := by
  cases source with
  | x target =>
      exact .gate (.cnot layout.control (layout.placement target)
        (layout.control_ne_placed target))
  | h target =>
      exact controlledHadamardSpecialAngleCircuit {
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }
  | ry angle target =>
      exact Circuit.controlledRyMacroExpansion layout.control (layout.placement target)
        (layout.control_ne_placed target) angle
  | phaseShift angle target =>
      exact controlledPhaseShiftFiveGateCircuit layout angle target
  | cnot sourceControl target different =>
      exact .gate (.toffoli layout.control (layout.placement sourceControl)
        (layout.placement target)
        (layout.control_ne_placed sourceControl)
        (layout.control_ne_placed target)
        (fun equal => different (layout.placement.injective equal)))
  | toffoli firstControl secondControl target _ _ _ =>
      exact (ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement firstControl,
          layout.placement secondControl]
        layout.workList (layout.placement target)).compile
/-- Declaration-order prelude for the typed public boundary.  Like the main
core below, all legacy branches are contradictions, never fallbacks. -/
private def controlPrimitiveTargetPrelude {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : PrimitiveGate sourceQubits)
    (normalized : IsNormalizedPrimitive source) :
    Operator (QubitBasis targetQubits) := by
  cases source with
  | x target =>
      exact reversibleAnalyticCnotOperator layout.control (layout.placement target)
  | h target =>
      exact controlledHadamardSpecialAngleOperator {
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }
  | ry angle target =>
      exact embedControlledSingleQubitOperator layout.control (layout.placement target)
        (layout.control_ne_placed target) (localRy (angle.eval symbolValue))
  | phaseShift angle target =>
      exact controlledPhaseShiftTarget symbolValue layout angle target
  | cnot sourceControl target _ =>
      exact analyticToffoliOperator layout.control (layout.placement sourceControl)
        (layout.placement target)
  | toffoli firstControl secondControl target _ _ _ =>
      exact (ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement firstControl,
          layout.placement secondControl]
        layout.workList (layout.placement target)).analyticOperator
private theorem controlPrimitiveCore_output_normalizedPrelude
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : PrimitiveGate sourceQubits)
    (normalized : IsNormalizedPrimitive source) :
    ∀ gate ∈ (controlPrimitiveCore layout source normalized).flatten,
      IsNormalizedPrimitive gate := by
  cases source with
  | x _ => simp [controlPrimitiveCore, IsNormalizedPrimitive, Circuit.flatten]
  | h _ =>
      simp [controlPrimitiveCore, IsNormalizedPrimitive,
        controlledHadamardSpecialAngleCircuit,
        controlledRyZSevenGateCircuit,
        controlledHadamardSevenGateCircuit]
  | ry _ _ =>
      simp [controlPrimitiveCore, IsNormalizedPrimitive,
        Circuit.controlledRyMacroExpansion]
  | phaseShift _ _ =>
      simp [controlPrimitiveCore, IsNormalizedPrimitive,
        controlledPhaseShiftFiveGateCircuit]
  | cnot _ _ _ => simp [controlPrimitiveCore, IsNormalizedPrimitive, Circuit.flatten]
  | toffoli firstControl secondControl target _ _ _ =>
      let stage := ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement firstControl,
          layout.placement secondControl]
        layout.workList (layout.placement target)
      change ∀ gate ∈ stage.compile.flatten, IsNormalizedPrimitive gate
      rw [ClassicalReversibleStage.compile, Circuit.flatten_mapGates]
      intro gate member
      rcases List.mem_map.mp member with ⟨instruction, _, rfl⟩
      cases instruction <;>
        simp [ClassicalReversibleInstruction.toPrimitiveGate,
          IsNormalizedPrimitive]
private def controlCircuitCorePrelude {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) :
    (circuit : Circuit (PrimitiveGate sourceQubits)) →
      IsNormalizedCircuit circuit → Circuit (PrimitiveGate targetQubits)
  | .identity, _ => .identity
  | .gate source, normalized =>
      controlPrimitiveCore layout source
        (normalized source (by simp [Circuit.flatten]))
  | .seq first second, normalized =>
      .seq
        (controlCircuitCorePrelude layout first (by
          intro gate member
          exact normalized gate (by simp [Circuit.flatten, member])))
        (controlCircuitCorePrelude layout second (by
          intro gate member
          exact normalized gate (by simp [Circuit.flatten, member])))
  | .repeat 0 _, _ => .identity
  | .repeat (Nat.succ count) body, normalized =>
      .repeat (Nat.succ count)
        (controlCircuitCorePrelude layout body (by
          intro gate member
          exact normalized gate (by
            simp [Circuit.flatten, List.replicate_succ, member])))

private theorem controlCircuitCore_output_normalizedPrelude
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (circuit : Circuit (PrimitiveGate sourceQubits))
    (normalized : IsNormalizedCircuit circuit) :
    IsNormalizedCircuit (controlCircuitCorePrelude layout circuit normalized) := by
  induction circuit with
  | identity =>
      intro gate member
      have impossible : False := by
        simp [controlCircuitCorePrelude, Circuit.flatten] at member
      exact impossible.elim
  | gate source =>
      change ∀ gate ∈
        (controlPrimitiveCore layout source
          (normalized source (by simp [Circuit.flatten]))).flatten,
        IsNormalizedPrimitive gate
      exact controlPrimitiveCore_output_normalizedPrelude layout source
        (normalized source (by simp [Circuit.flatten]))
  | seq first second firstInduction secondInduction =>
      have firstNormalized : IsNormalizedCircuit first := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      have secondNormalized : IsNormalizedCircuit second := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      simpa [controlCircuitCorePrelude] using
        normalizedCircuit_seq _ _ (firstInduction firstNormalized)
          (secondInduction secondNormalized)
  | «repeat» count body inductionHypothesis =>
      cases count with
      | zero =>
          intro gate member
          have impossible : False := by
            simp [controlCircuitCorePrelude, Circuit.flatten] at member
          exact impossible.elim
      | succ count =>
          have bodyNormalized : IsNormalizedCircuit body := by
            intro gate member
            exact normalized gate (by
              simp [Circuit.flatten, List.replicate_succ, member])
          simpa [controlCircuitCorePrelude] using
            normalizedCircuit_repeat (Nat.succ count) _
              (inductionHypothesis bodyNormalized)

/-- The semantic target is defined on the same normalized source domain as
the public primitive compiler; legacy gates have no target interpretation in
v2. -/
def controlPrimitiveTarget {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    Operator (QubitBasis targetQubits) :=
  controlPrimitiveTargetPrelude symbolValue layout source.1 source.2

/-- Every public primitive output carries its exact six-family normalized
syntax certificate. -/
theorem controlPrimitive_output_normalized
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    IsNormalizedCircuit
      (controlPrimitiveCore layout source.1 source.2) :=
  controlPrimitiveCore_output_normalizedPrelude layout source.1 source.2

/-- The theorem-grade primitive v2 lowering boundary.  The output is again a
`NormalizedCircuit`, so it can be externally controlled a second time without
re-entering a raw-gate adapter. -/
def controlPrimitive {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    NormalizedCircuit targetQubits :=
  ⟨controlPrimitiveCore layout source.1 source.2,
    controlPrimitive_output_normalized layout source⟩

/-- The theorem-grade circuit v2 lowering boundary.  It accepts and returns
certified normalized syntax. -/
def controlCircuit {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    NormalizedCircuit targetQubits :=
  ⟨controlCircuitCorePrelude layout source.circuit source.normalized,
    controlCircuitCore_output_normalizedPrelude layout source.circuit source.normalized⟩

/-- The full public compiler returns only certified six-family normalized
syntax. -/
theorem controlCircuit_output_normalized
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    IsNormalizedCircuit (controlCircuit layout source).circuit :=
  (controlCircuit layout source).normalized

/-- Repeated evaluation of the typed primitive compiler is deterministic for
the same layout and certified source. -/
theorem controlPrimitive_deterministic
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    (controlPrimitive layout source).circuit =
      (controlPrimitive layout source).circuit := rfl

/-- Repeated evaluation of the typed circuit compiler is deterministic for the
same layout and certified source AST. -/
theorem controlCircuit_deterministic
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    (controlCircuit layout source).circuit =
      (controlCircuit layout source).circuit := rfl

/-- The typed normalization recheck leaves a compiler output structurally
unchanged after one or more applications. -/
theorem controlPrimitive_normalization_stable
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    (NormalizedCircuit.normalize (NormalizedCircuit.normalize
      (controlPrimitive layout source))).circuit =
        (controlPrimitive layout source).circuit := rfl

/-- Migration adapter for a raw primitive.  Legacy primitive constructors
produce `none`, never an identity lowerer. -/
noncomputable def controlPrimitive? {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : PrimitiveGate sourceQubits) :
    Option (NormalizedCircuit targetQubits) := by
  classical
  by_cases normalized : IsNormalizedPrimitive source
  · exact some (controlPrimitive layout ⟨source, normalized⟩)
  · exact none

theorem controlPrimitiveOption_none_of_not_normalized
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : PrimitiveGate sourceQubits)
    (notNormalized : ¬ IsNormalizedPrimitive source) :
    controlPrimitive? layout source = none := by
  simp [controlPrimitive?, notNormalized]

/-- Migration adapter for a raw circuit.  A raw AST is accepted only after a
complete flattened-leaf certificate has been constructed. -/
noncomputable def controlCircuit? {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : Circuit (PrimitiveGate sourceQubits)) :
    Option (NormalizedCircuit targetQubits) := by
  classical
  by_cases normalized : IsNormalizedCircuit source
  · exact some (controlCircuit layout ⟨source, normalized⟩)
  · exact none

theorem controlCircuitOption_none_of_not_normalized
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : Circuit (PrimitiveGate sourceQubits))
    (notNormalized : ¬ IsNormalizedCircuit source) :
    controlCircuit? layout source = none := by
  simp [controlCircuit?, notNormalized]

@[simp] theorem controlCircuit_identity {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) :
    (controlCircuit layout (NormalizedCircuit.identity sourceQubits)).circuit =
      .identity := rfl

@[simp] theorem controlCircuit_gate {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    (controlCircuit layout (NormalizedCircuit.gate source)).circuit =
      (controlPrimitive layout source).circuit := rfl

@[simp] theorem controlCircuit_seq {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (first second : NormalizedCircuit sourceQubits) :
    (controlCircuit layout (NormalizedCircuit.seq first second)).circuit =
      .seq (controlCircuit layout first).circuit
        (controlCircuit layout second).circuit := rfl

@[simp] theorem controlCircuit_repeat_zero {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (body : NormalizedCircuit sourceQubits) :
    (controlCircuit layout (NormalizedCircuit.«repeat» 0 body)).circuit =
      .identity := rfl

@[simp] theorem controlCircuit_repeat_succ {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (count : Nat) (body : NormalizedCircuit sourceQubits) :
    (controlCircuit layout (NormalizedCircuit.«repeat» (Nat.succ count) body)).circuit =
      .repeat (Nat.succ count) (controlCircuit layout body).circuit := rfl

/-- A public type-level re-control witness. -/
def controlCircuitRecontrol
    {sourceQubits middleQubits targetQubits : Nat}
    (firstLayout : ControlLayout sourceQubits middleQubits)
    (secondLayout : ControlLayout middleQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    NormalizedCircuit targetQubits :=
  controlCircuit secondLayout (controlCircuit firstLayout source)

/-- Reversing a typed v2 output remains typed normalized syntax. -/
def controlCircuitOutputInverse {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    NormalizedCircuit targetQubits :=
  NormalizedCircuit.inverse (controlCircuit layout source)

theorem controlCircuit_reverse_output_normalized
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    IsNormalizedCircuit (controlCircuitOutputInverse layout source).circuit :=
  (controlCircuitOutputInverse layout source).normalized

/-- The primitive-level inverse semantics gives the exact adjoint of any typed
v2 output circuit, including the clean-work Toffoli stage. -/
theorem controlCircuit_reverse_denote
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuitOutputInverse layout source).circuit =
      star (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuit layout source).circuit) :=
  primitiveCircuit_denote_reverse symbolValue (controlCircuit layout source).circuit

/-- Structural core for a certified source circuit.  Its zero-repeat branch
does not inspect an unreachable body, while every executed leaf is passed to
the proof-carrying primitive boundary. -/
private def controlCircuitCore {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) :
    (circuit : Circuit (PrimitiveGate sourceQubits)) →
      IsNormalizedCircuit circuit → Circuit (PrimitiveGate targetQubits)
  | .identity, _ => .identity
  | .gate source, normalized =>
      controlPrimitiveCore layout source
        (normalized source (by simp [Circuit.flatten]))
  | .seq first second, normalized =>
      .seq
        (controlCircuitCore layout first (by
          intro gate member
          exact normalized gate (by simp [Circuit.flatten, member])))
        (controlCircuitCore layout second (by
          intro gate member
          exact normalized gate (by simp [Circuit.flatten, member])))
  | .repeat 0 _, _ => .identity
  | .repeat (Nat.succ count) body, normalized =>
      .repeat (Nat.succ count)
        (controlCircuitCore layout body (by
          intro gate member
          exact normalized gate (by
            simp [Circuit.flatten, List.replicate_succ, member])))

/-- Every output leaf of the shared reversible-stage compiler is normalized. -/
theorem reversibleInstruction_normalized {qubits : Nat}
    (instruction : ClassicalReversibleInstruction qubits) :
    IsNormalizedPrimitive instruction.toPrimitiveGate := by
  cases instruction <;>
    simp [ClassicalReversibleInstruction.toPrimitiveGate, IsNormalizedPrimitive]

theorem reversibleStage_compile_normalized {qubits : Nat}
    (stage : ClassicalReversibleStage qubits) :
    ∀ gate ∈ stage.compile.flatten, IsNormalizedPrimitive gate := by
  rw [ClassicalReversibleStage.compile, Circuit.flatten_mapGates]
  intro gate member
  rcases List.mem_map.mp member with ⟨instruction, _, rfl⟩
  exact reversibleInstruction_normalized instruction

/-- All output leaves of the proof-carrying primitive core are in the six-form
normalized language, including the clean-work Toffoli lowering. -/
theorem controlPrimitiveCore_output_normalized
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : PrimitiveGate sourceQubits)
    (normalized : IsNormalizedPrimitive source) :
    ∀ gate ∈ (controlPrimitiveCore layout source normalized).flatten,
      IsNormalizedPrimitive gate := by
  cases source with
  | x _ =>
      simp [controlPrimitiveCore, IsNormalizedPrimitive, Circuit.flatten]
  | h _ =>
      simp [controlPrimitiveCore, IsNormalizedPrimitive,
        controlledHadamardSpecialAngleCircuit,
        controlledRyZSevenGateCircuit,
        controlledHadamardSevenGateCircuit]
  | ry _ _ =>
      simp [controlPrimitiveCore, IsNormalizedPrimitive,
        Circuit.controlledRyMacroExpansion]
  | phaseShift _ _ =>
      simp [controlPrimitiveCore, IsNormalizedPrimitive,
        controlledPhaseShiftFiveGateCircuit]
  | cnot _ _ _ =>
      simp [controlPrimitiveCore, IsNormalizedPrimitive, Circuit.flatten]
  | toffoli firstControl secondControl target controlsDifferent firstDifferent
      secondDifferent =>
      change ∀ gate ∈
        ((ClassicalReversibleStage.positiveMultiControlledX
          [layout.control, layout.placement firstControl,
            layout.placement secondControl]
          layout.workList (layout.placement target)).compile).flatten,
        IsNormalizedPrimitive gate
      exact reversibleStage_compile_normalized _
/-- Full-dirty target for one proof-carrying lowered primitive.  The Toffoli
branch names the shared clean-work stage itself; it has no legacy identity
semantic branch. -/
private def controlPrimitiveTargetCore {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : PrimitiveGate sourceQubits)
    (normalized : IsNormalizedPrimitive source) :
    Operator (QubitBasis targetQubits) := by
  cases source with
  | x target =>
      exact reversibleAnalyticCnotOperator layout.control (layout.placement target)
  | h target =>
      exact controlledHadamardSpecialAngleOperator {
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }
  | ry angle target =>
      exact embedControlledSingleQubitOperator layout.control (layout.placement target)
        (layout.control_ne_placed target) (localRy (angle.eval symbolValue))
  | phaseShift angle target =>
      exact controlledPhaseShiftTarget symbolValue layout angle target
  | cnot sourceControl target _ =>
      exact analyticToffoliOperator layout.control (layout.placement sourceControl)
        (layout.placement target)
  | toffoli firstControl secondControl target _ _ _ =>
      exact (ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement firstControl,
          layout.placement secondControl]
        layout.workList (layout.placement target)).analyticOperator
/-- Common output contract for the explicit work bundle.  A nonzero output
amplitude may not alter either work wire when the input bundle is clean.  For
the five work-free rules the clean premise is unused; for Toffoli it is
discharged by the shared clean-work stage theorem. -/
def OperatorPreservesCleanWork {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (operator : Operator (QubitBasis targetQubits)) : Prop :=
  ∀ output input, operator output input ≠ 0 → layout.workIsClean input →
    ∀ slot, output (layout.work slot) = input (layout.work slot)

/-- A usual support-locality theorem entails the common clean-work contract
whenever the declared work bundle lies outside that support. -/
theorem operatorPreservesCleanWork_of_preservesOutside
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    {support : Finset (Fin targetQubits)}
    {operator : Operator (QubitBasis targetQubits)}
    (locality : OperatorPreservesOutside support operator)
    (workOutside : ∀ slot, layout.work slot ∉ support) :
    OperatorPreservesCleanWork layout operator := by
  intro output input nonzero _ slot
  exact locality output input nonzero (layout.work slot) (workOutside slot)

theorem ControlLayout.work_not_mem_placed
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : Fin sourceQubits) (slot : Fin 2) :
    layout.work slot ∉ ({layout.placement source} : Finset (Fin targetQubits)) := by
  intro member
  have equal : layout.work slot = layout.placement source := by
    simpa using member
  exact layout.work_ne_placed slot source equal

theorem ControlLayout.work_not_mem_controlPlaced
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (source : Fin sourceQubits) (slot : Fin 2) :
    layout.work slot ∉ ({layout.control, layout.placement source} :
      Finset (Fin targetQubits)) := by
  intro member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with equal | equal
  · exact layout.work_ne_control slot equal
  · exact layout.work_ne_placed slot source equal

namespace OperatorPreservesCleanWork

theorem one {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) :
    OperatorPreservesCleanWork layout (1 : Operator (QubitBasis targetQubits)) := by
  apply operatorPreservesCleanWork_of_preservesOutside layout
  · exact OperatorPreservesOutside.one ∅
  · intro slot
    simp

/-- The clean-work contract is closed under execution-order operator
composition.  The first contract makes every nonzero intermediate amplitude
clean, which is exactly the premise needed for the second contract. -/
theorem mul {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    {first second : Operator (QubitBasis targetQubits)}
    (firstPreserves : OperatorPreservesCleanWork layout first)
    (secondPreserves : OperatorPreservesCleanWork layout second) :
    OperatorPreservesCleanWork layout (second * first) := by
  intro output input productNonzero inputClean slot
  by_contra changed
  have everyTermZero : ∀ intermediate : QubitBasis targetQubits,
      second output intermediate * first intermediate input = 0 := by
    intro intermediate
    by_cases firstZero : first intermediate input = 0
    · simp [firstZero]
    · by_cases secondZero : second output intermediate = 0
      · simp [secondZero]
      · have intermediateClean : layout.workIsClean intermediate := by
          intro intermediateSlot
          rw [firstPreserves intermediate input firstZero inputClean intermediateSlot]
          exact inputClean intermediateSlot
        have outputIntermediate :=
          secondPreserves output intermediate secondZero intermediateClean slot
        have intermediateInput :=
          firstPreserves intermediate input firstZero inputClean slot
        exact False.elim (changed (outputIntermediate.trans intermediateInput))
  apply productNonzero
  change (∑ intermediate, second output intermediate * first intermediate input) = 0
  simp [everyTermZero]

theorem pow {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    {operator : Operator (QubitBasis targetQubits)}
    (preserves : OperatorPreservesCleanWork layout operator) :
    ∀ count : Nat, OperatorPreservesCleanWork layout (operator ^ count)
  | 0 => by simpa using one layout
  | Nat.succ count => by
      simpa [pow_succ] using mul layout preserves (pow layout preserves count)

end OperatorPreservesCleanWork

theorem controlPrimitive_x_correct {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (target : Fin sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlPrimitive layout (.x target)) =
      controlPrimitiveTarget symbolValue layout (.x target) := by
  rfl

theorem controlPrimitive_x_target_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (target : Fin sourceQubits) :
    OperatorPreservesCleanWork layout
      (controlPrimitiveTarget symbolValue layout (.x target)) := by
  unfold controlPrimitiveTarget controlPrimitiveTargetPrelude
    reversibleAnalyticCnotOperator
  apply operatorPreservesCleanWork_of_preservesOutside layout
  · exact OperatorPreservesOutside.deterministicXorWire
      (layout.placement target) (fun input => input layout.control)
  · exact layout.work_not_mem_placed target

theorem controlPrimitive_h_correct {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (target : Fin sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlPrimitive layout (.h target)) =
      controlPrimitiveTarget symbolValue layout (.h target) := by
  exact (controlledHadamardSpecialAngleExactOperatorComponent symbolValue {
    control := layout.control
    target := layout.placement target
    different := layout.control_ne_placed target }).correct

theorem controlPrimitive_h_target_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (target : Fin sourceQubits) :
    OperatorPreservesCleanWork layout
      (controlPrimitiveTarget symbolValue layout (.h target)) := by
  unfold controlPrimitiveTarget controlPrimitiveTargetPrelude
    controlledHadamardSpecialAngleOperator
  unfold embedControlledSingleQubitOperator
  apply operatorPreservesCleanWork_of_preservesOutside layout
  · exact OperatorPreservesOutside.embedTwoQubitOperator layout.control
      (layout.placement target) (layout.control_ne_placed target) _
  · exact layout.work_not_mem_controlPlaced target

theorem controlPrimitive_ry_correct {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (angle : AngleExpr) (target : Fin sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlPrimitive layout (.ry angle target)) =
      controlPrimitiveTarget symbolValue layout (.ry angle target) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (Circuit.controlledRyMacroExpansion layout.control (layout.placement target)
        (layout.control_ne_placed target) angle) =
    embedControlledSingleQubitOperator layout.control (layout.placement target)
      (layout.control_ne_placed target) (localRy (angle.eval symbolValue))
  simp only [Circuit.controlledRyMacroExpansion, Circuit.fromList, Circuit.denote,
    primitiveGateOperatorWithSymbols, Circuit.halfAngle, AngleExpr.eval, Matrix.one_mul]
  rw [show deterministicOperator
      (fun input => xorWire (layout.placement target) (input layout.control) input) =
        analyticCnotOperator layout.control (layout.placement target) by rfl]
  rw [analyticCnotOperator_eq_embedTwo_localCnot
    layout.control (layout.placement target) (layout.control_ne_placed target)]
  rw [← embedTwoQubitOperator_localOnTarget layout.control (layout.placement target)
      (layout.control_ne_placed target),
    ← embedTwoQubitOperator_localOnTarget layout.control (layout.placement target)
      (layout.control_ne_placed target)]
  rw [← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul,
    ← embedTwoQubitOperator_mul]
  unfold embedControlledSingleQubitOperator
  apply congrArg (embedTwoQubitOperator layout.control (layout.placement target)
    (layout.control_ne_placed target))
  convert local_controlledRy_decomposition (angle.eval symbolValue) using 1
  norm_num
  ring_nf

theorem controlPrimitive_ry_target_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (angle : AngleExpr) (target : Fin sourceQubits) :
    OperatorPreservesCleanWork layout
      (controlPrimitiveTarget symbolValue layout (.ry angle target)) := by
  unfold controlPrimitiveTarget controlPrimitiveTargetPrelude
    embedControlledSingleQubitOperator
  apply operatorPreservesCleanWork_of_preservesOutside layout
  · exact OperatorPreservesOutside.embedTwoQubitOperator layout.control
      (layout.placement target) (layout.control_ne_placed target) _
  · exact layout.work_not_mem_controlPlaced target

/-- Local exact decomposition for the phase-shift convention
`diag(1, exp(i * angle))`. -/
theorem local_controlledPhaseShift_decomposition (angle : ℝ) :
    localCnotOperator * localOnTarget (localPhaseShift (-(angle / 2))) *
        localCnotOperator * localOnTarget (localPhaseShift (angle / 2)) *
        localOnControl (localPhaseShift (angle / 2)) =
      localControlledPhaseOperator angle := by
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases outputTarget <;>
    cases inputControl <;> cases inputTarget <;>
    simp [localCnotOperator, localOnTarget, localOnControl,
      localPhaseShift, localPhase, localControlledPhaseOperator,
      Matrix.mul_apply, Matrix.kronecker, Fintype.sum_prod_type]
  all_goals
    rw [← Complex.exp_add]
    ring_nf <;> exact Complex.exp_zero

theorem controlPrimitive_phaseShift_correct {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (angle : AngleExpr) (target : Fin sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlPrimitive layout (.phaseShift angle target)) =
      controlPrimitiveTarget symbolValue layout (.phaseShift angle target) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (controlledPhaseShiftFiveGateCircuit layout angle target) =
    controlledPhaseShiftTarget symbolValue layout angle target
  simp only [controlledPhaseShiftFiveGateCircuit, Circuit.fromList, Circuit.denote,
    primitiveGateOperatorWithSymbols, AngleExpr.eval_neg, phaseShiftHalfAngle_eval,
    Matrix.one_mul]
  rw [show deterministicOperator
      (fun input => xorWire (layout.placement target) (input layout.control) input) =
        analyticCnotOperator layout.control (layout.placement target) by rfl]
  rw [analyticCnotOperator_eq_embedTwo_localCnot
    layout.control (layout.placement target) (layout.control_ne_placed target)]
  rw [← embedTwoQubitOperator_localOnTarget layout.control (layout.placement target)
      (layout.control_ne_placed target),
    ← embedTwoQubitOperator_localOnTarget layout.control (layout.placement target)
      (layout.control_ne_placed target),
    ← embedTwoQubitOperator_localOnControl layout.control (layout.placement target)
      (layout.control_ne_placed target)]
  rw [← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul,
    ← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul]
  unfold controlledPhaseShiftTarget analyticControlledPhaseOperator
  rw [local_controlledPhaseShift_decomposition]

theorem controlPrimitive_phaseShift_target_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (angle : AngleExpr) (target : Fin sourceQubits) :
    OperatorPreservesCleanWork layout
      (controlPrimitiveTarget symbolValue layout (.phaseShift angle target)) := by
  unfold controlPrimitiveTarget controlPrimitiveTargetPrelude
    controlledPhaseShiftTarget analyticControlledPhaseOperator
  apply operatorPreservesCleanWork_of_preservesOutside layout
  · exact OperatorPreservesOutside.embedTwoQubitOperator layout.control
      (layout.placement target) (layout.control_ne_placed target) _
  · exact layout.work_not_mem_controlPlaced target

theorem controlPrimitive_cnot_correct {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (sourceControl target : Fin sourceQubits)
    (different : sourceControl ≠ target) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlPrimitive layout (.cnot sourceControl target different)) =
      controlPrimitiveTarget symbolValue layout (.cnot sourceControl target different) := by
  rfl

theorem controlPrimitive_cnot_target_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (sourceControl target : Fin sourceQubits)
    (different : sourceControl ≠ target) :
    OperatorPreservesCleanWork layout
      (controlPrimitiveTarget symbolValue layout (.cnot sourceControl target different)) := by
  unfold controlPrimitiveTarget controlPrimitiveTargetPrelude analyticToffoliOperator
  apply operatorPreservesCleanWork_of_preservesOutside layout
  · exact OperatorPreservesOutside.deterministicXorWire
      (layout.placement target) (fun input =>
        input layout.control && input (layout.placement sourceControl))
  · exact layout.work_not_mem_placed target

/-- The intended basis action of the externally controlled Toffoli leaf. -/
def controlledToffoliBasisAction {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (firstControl secondControl target : Fin sourceQubits)
    (input : QubitBasis targetQubits) : QubitBasis targetQubits :=
  xorWire (layout.placement target)
    (input layout.control && (input (layout.placement firstControl) &&
      input (layout.placement secondControl))) input

/-- The shared two-work-wire stage has the intended controlled-Toffoli action
when the caller's explicit work bundle is clean. -/
theorem controlPrimitive_toffoli_reference_apply_of_cleanWork
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (firstControl secondControl target : Fin sourceQubits)
    (controlsDifferent : firstControl ≠ secondControl)
    (firstDifferent : firstControl ≠ target)
    (secondDifferent : secondControl ≠ target)
    (input : QubitBasis targetQubits)
    (cleanWork : layout.workIsClean input) :
    (ClassicalReversibleStage.positiveMultiControlledX
      [layout.control, layout.placement firstControl,
        layout.placement secondControl]
      layout.workList (layout.placement target)).reference input =
      controlledToffoliBasisAction layout firstControl secondControl target input := by
  have enoughScratch :
      [layout.control, layout.placement firstControl,
        layout.placement secondControl].length ≤ layout.workList.length + 1 := by
    simp [ControlLayout.workList]
  have layoutNodup :
      ([layout.control, layout.placement firstControl,
        layout.placement secondControl] ++ layout.workList ++
        [layout.placement target]).Nodup :=
    ControlLayout.toffoliLayout_nodup layout firstControl secondControl target
      controlsDifferent firstDifferent secondDifferent
  have scratchZero : ∀ wire ∈ layout.workList, input wire = false := by
    intro wire member
    simp [ControlLayout.workList] at member
    rcases member with rfl | rfl
    · exact cleanWork 0
    · exact cleanWork 1
  simpa [controlledToffoliBasisAction,
    ClassicalReversibleStage.allWiresTrue, ClassicalReversibleStage.readWires] using
    ClassicalReversibleStage.positiveMultiControlledX_reference_apply_of_cleanWork
      [layout.control, layout.placement firstControl,
        layout.placement secondControl]
      layout.workList (layout.placement target) input enoughScratch layoutNodup scratchZero

/-- The final clean-work Toffoli action restores each explicit work wire. -/
theorem controlPrimitive_toffoli_reference_preserves_work_of_cleanWork
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (firstControl secondControl target : Fin sourceQubits)
    (controlsDifferent : firstControl ≠ secondControl)
    (firstDifferent : firstControl ≠ target)
    (secondDifferent : secondControl ≠ target)
    (input : QubitBasis targetQubits)
    (cleanWork : layout.workIsClean input) (slot : Fin 2) :
    (ClassicalReversibleStage.positiveMultiControlledX
      [layout.control, layout.placement firstControl,
        layout.placement secondControl]
      layout.workList (layout.placement target)).reference input (layout.work slot) =
      input (layout.work slot) := by
  rw [controlPrimitive_toffoli_reference_apply_of_cleanWork layout
    firstControl secondControl target controlsDifferent firstDifferent secondDifferent
    input cleanWork]
  unfold controlledToffoliBasisAction
  exact xorWire_apply_other (layout.placement target) (layout.work slot)
    (layout.work_ne_placed slot target) _ input

/-- The explicit three-control work-stage is self-inverse at the independent
classical permutation level.  Its AST reverse only reassociates sequencing,
so we state the semantic equality rather than a false syntactic equality. -/
theorem positiveMultiControlledX_three_reference_selfInverse
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (firstControl secondControl target : Fin sourceQubits) :
    (ClassicalReversibleStage.positiveMultiControlledX
      [layout.control, layout.placement firstControl,
        layout.placement secondControl]
      layout.workList (layout.placement target)).reference =
      (ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement firstControl,
          layout.placement secondControl]
        layout.workList (layout.placement target)).reference.symm := by
  have controlFirst : layout.control ≠ layout.placement firstControl :=
    layout.control_ne_placed firstControl
  have controlWork : layout.control ≠ layout.work 0 :=
    (layout.work_ne_control 0).symm
  have firstWork : layout.placement firstControl ≠ layout.work 0 :=
    (layout.work_ne_placed 0 firstControl).symm
  have workSecond : layout.work 0 ≠ layout.placement secondControl :=
    layout.work_ne_placed 0 secondControl
  have workDifferent : layout.work 0 ≠ layout.work 1 :=
    ControlLayout.work_ne_each_other layout
  have secondWork : layout.placement secondControl ≠ layout.work 1 :=
    (layout.work_ne_placed 1 secondControl).symm
  have workTarget : layout.work 1 ≠ layout.placement target :=
    layout.work_ne_placed 1 target
  rw [← ClassicalReversibleStage.reverse_reference]
  simp [ClassicalReversibleStage.positiveMultiControlledX,
    ClassicalReversibleStage.andChainUse, ClassicalReversibleStage.safeXorDoublyControlled,
    ClassicalReversibleStage.safeXorControlled, ClassicalReversibleStage.reverse,
    ClassicalReversibleStage.reference, ControlLayout.workList, controlFirst,
    controlWork, firstWork, workSecond, workDifferent, secondWork, workTarget,
    mul_assoc]

theorem positiveMultiControlledX_three_analytic_selfAdjoint
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (firstControl secondControl target : Fin sourceQubits) :
    let stage := ClassicalReversibleStage.positiveMultiControlledX
      [layout.control, layout.placement firstControl,
        layout.placement secondControl]
      layout.workList (layout.placement target)
    stage.analyticOperator = star stage.analyticOperator := by
  dsimp
  let stage := ClassicalReversibleStage.positiveMultiControlledX
    [layout.control, layout.placement firstControl,
      layout.placement secondControl]
    layout.workList (layout.placement target)
  have referenceSelfInverse : stage.reference = stage.reference.symm := by
    simpa [stage] using
      positiveMultiControlledX_three_reference_selfInverse layout
        firstControl secondControl target
  have referenceInvolutive : Function.Involutive stage.reference := by
    intro input
    have inner : stage.reference input = stage.reference.symm input :=
      congrArg (fun permutation : Equiv.Perm (QubitBasis targetQubits) =>
        permutation input) referenceSelfInverse
    calc
      stage.reference (stage.reference input) =
          stage.reference (stage.reference.symm input) := by rw [inner]
      _ = input := stage.reference.apply_symm_apply input
  rw [ClassicalReversibleStage.analyticOperator_eq_deterministicReference]
  exact (star_deterministicOperator_of_involutive stage.reference
    referenceInvolutive).symm

theorem star_localControlledPhaseOperator (angle : ℝ) :
    star (localControlledPhaseOperator angle) =
      localControlledPhaseOperator (-angle) := by
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases outputTarget <;>
    cases inputControl <;> cases inputTarget <;>
    simp [localControlledPhaseOperator]
  change star (Complex.exp (Complex.I * (angle : ℂ))) =
    Complex.exp (-(Complex.I * (angle : ℂ)))
  rw [star_complexExp_imaginary]
  congr 1
  simp only [Complex.ofReal_neg, mul_neg]

/-- The raw proof-carrying target core is inverse-correct without projecting a
public subtype record.  Keeping this proof at the six-branch core avoids a
large proof-projection definitional equality at the public boundary. -/
private theorem controlPrimitiveTargetPrelude_inverse
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : PrimitiveGate sourceQubits)
    (normalized : IsNormalizedPrimitive source) :
    controlPrimitiveTargetPrelude symbolValue layout source.inverse
        (normalizedPrimitive_inverse source normalized) =
      star (controlPrimitiveTargetPrelude symbolValue layout source normalized) := by
  cases source with
  | x target =>
      change reversibleAnalyticCnotOperator layout.control (layout.placement target) =
        star (reversibleAnalyticCnotOperator layout.control (layout.placement target))
      unfold reversibleAnalyticCnotOperator
      change deterministicOperator (cnotBasisAction layout.control
        (layout.placement target)) =
        star (deterministicOperator (cnotBasisAction layout.control
          (layout.placement target)))
      exact (star_cnotOperator layout.control (layout.placement target)
        (layout.control_ne_placed target)).symm
  | h target =>
      simp only [PrimitiveGate.inverse]
      unfold controlPrimitiveTargetPrelude controlledHadamardSpecialAngleOperator
      rw [star_embedControlledSingleQubitOperator]
      simp [star_localH]
  | ry angle target =>
      simp only [PrimitiveGate.inverse]
      unfold controlPrimitiveTargetPrelude
      simp only [AngleExpr.eval_neg]
      rw [star_embedControlledSingleQubitOperator]
      simp [star_localRy]
  | phaseShift angle target =>
      simp only [PrimitiveGate.inverse]
      unfold controlPrimitiveTargetPrelude controlledPhaseShiftTarget
        analyticControlledPhaseOperator
      simp only [AngleExpr.eval_neg]
      rw [star_embedTwoQubitOperator, star_localControlledPhaseOperator]
  | cnot sourceControl target different =>
      have placedDifferent : layout.placement sourceControl ≠ layout.placement target := by
        intro equal
        exact different (layout.placement.injective equal)
      simp only [PrimitiveGate.inverse]
      unfold controlPrimitiveTargetPrelude analyticToffoliOperator
      change deterministicOperator (toffoliBasisAction layout.control
        (layout.placement sourceControl) (layout.placement target)) =
        star (deterministicOperator (toffoliBasisAction layout.control
          (layout.placement sourceControl) (layout.placement target)))
      exact (star_toffoliOperator layout.control (layout.placement sourceControl)
        (layout.placement target) (layout.control_ne_placed target)
        placedDifferent).symm
  | toffoli firstControl secondControl target _ _ _ =>
      simp only [PrimitiveGate.inverse]
      exact positiveMultiControlledX_three_analytic_selfAdjoint layout
        firstControl secondControl target
/-- The independent target of a normalized leaf compiled from the source
inverse is the exact adjoint target. -/
theorem controlPrimitiveTarget_inverse
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    controlPrimitiveTarget symbolValue layout
        (NormalizedPrimitiveGate.inverse source) =
      star (controlPrimitiveTarget symbolValue layout source) := by
  change controlPrimitiveTargetPrelude symbolValue layout source.1.inverse
      (normalizedPrimitive_inverse source.1 source.2) =
    star (controlPrimitiveTargetPrelude symbolValue layout source.1 source.2)
  exact controlPrimitiveTargetPrelude_inverse symbolValue layout source.1 source.2

theorem controlPrimitive_toffoli_target_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (firstControl secondControl target : Fin sourceQubits)
    (controlsDifferent : firstControl ≠ secondControl)
    (firstDifferent : firstControl ≠ target)
    (secondDifferent : secondControl ≠ target) :
    OperatorPreservesCleanWork layout
      (controlPrimitiveTarget symbolValue layout
        (.toffoli firstControl secondControl target controlsDifferent
          firstDifferent secondDifferent)) := by
  let stage := ClassicalReversibleStage.positiveMultiControlledX
    [layout.control, layout.placement firstControl,
      layout.placement secondControl]
    layout.workList (layout.placement target)
  change OperatorPreservesCleanWork layout stage.analyticOperator
  intro output input nonzero cleanWork slot
  rw [ClassicalReversibleStage.analyticOperator_eq_deterministicReference] at nonzero
  rw [deterministicOperator_apply] at nonzero
  by_cases outputEqual : output = stage.reference input
  · subst output
    simpa [stage] using
      controlPrimitive_toffoli_reference_preserves_work_of_cleanWork layout
        firstControl secondControl target controlsDifferent firstDifferent
        secondDifferent input cleanWork slot
  · simp [outputEqual] at nonzero

/-- The common target-side work contract for every normalized source leaf. -/
theorem controlPrimitiveTarget_normalized_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    OperatorPreservesCleanWork layout
      (controlPrimitiveTarget symbolValue layout source) := by
  rcases source with ⟨source, normalized⟩
  cases source with
  | x target =>
      exact controlPrimitive_x_target_preserves_clean_work symbolValue layout target
  | h target =>
      exact controlPrimitive_h_target_preserves_clean_work symbolValue layout target
  | ry angle target =>
      exact controlPrimitive_ry_target_preserves_clean_work symbolValue layout angle target
  | phaseShift angle target =>
      exact controlPrimitive_phaseShift_target_preserves_clean_work
        symbolValue layout angle target
  | cnot sourceControl target different =>
      exact controlPrimitive_cnot_target_preserves_clean_work
        symbolValue layout sourceControl target different
  | toffoli firstControl secondControl target controlsDifferent firstDifferent
      secondDifferent =>
      exact controlPrimitive_toffoli_target_preserves_clean_work
        symbolValue layout firstControl secondControl target controlsDifferent
        firstDifferent secondDifferent
/-- All normalized leaf lowerings implement their target operator. -/
theorem controlPrimitive_normalized_correct
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlPrimitive layout source) =
      controlPrimitiveTarget symbolValue layout source := by
  rcases source with ⟨source, normalized⟩
  cases source with
  | x target => exact controlPrimitive_x_correct symbolValue layout target
  | h target => exact controlPrimitive_h_correct symbolValue layout target
  | ry angle target =>
      exact controlPrimitive_ry_correct symbolValue layout angle target
  | phaseShift angle target =>
      exact controlPrimitive_phaseShift_correct symbolValue layout angle target
  | cnot sourceControl target different =>
      exact controlPrimitive_cnot_correct symbolValue layout sourceControl target different
  | toffoli firstControl secondControl target controlsDifferent firstDifferent
      secondDifferent =>
      let stage := ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement firstControl,
          layout.placement secondControl]
        layout.workList (layout.placement target)
      change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) stage.compile =
        stage.analyticOperator
      rw [← ClassicalReversibleStage.primitiveExactOperatorComponent_circuit
        symbolValue stage]
      rw [(stage.primitiveExactOperatorComponent symbolValue).correct]
      exact ClassicalReversibleStage.primitiveExactOperatorComponent_target
        symbolValue stage
/-- Every emitted normalized leaf preserves the explicit clean-work bundle.
This is the compiler's common output contract, stated for the actual lowered
circuit rather than only its independently named target. -/
theorem controlPrimitive_normalized_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    OperatorPreservesCleanWork layout
      (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlPrimitive layout source)) := by
  rw [controlPrimitive_normalized_correct symbolValue layout source]
  exact controlPrimitiveTarget_normalized_preserves_clean_work
    symbolValue layout source

/-- The leaf contract composes through the complete source AST.  Thus a
normalized `controlCircuit` keeps the caller-supplied work bundle clean at
every nonzero output amplitude, across sequencing and repetition. -/
theorem controlCircuit_normalized_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    OperatorPreservesCleanWork layout
      (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuit layout source)) := by
  rcases source with ⟨circuit, normalized⟩
  induction circuit with
  | identity =>
      simpa [controlCircuit, controlCircuitCorePrelude, Circuit.denote] using
        OperatorPreservesCleanWork.one layout
  | gate gate =>
      change OperatorPreservesCleanWork layout
        (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (controlPrimitive layout ⟨gate,
            normalized gate (by simp [Circuit.flatten])⟩))
      exact controlPrimitive_normalized_preserves_clean_work symbolValue layout
        ⟨gate, normalized gate (by simp [Circuit.flatten])⟩
  | seq first second firstInduction secondInduction =>
      have firstNormalized : IsNormalizedCircuit first := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      have secondNormalized : IsNormalizedCircuit second := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      change OperatorPreservesCleanWork layout
        (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (.seq (controlCircuitCorePrelude layout first firstNormalized)
            (controlCircuitCorePrelude layout second secondNormalized)))
      rw [Circuit.denote_seq]
      exact OperatorPreservesCleanWork.mul layout
        (firstInduction firstNormalized) (secondInduction secondNormalized)
  | «repeat» count body inductionHypothesis =>
      cases count with
      | zero =>
          simpa [controlCircuit, controlCircuitCorePrelude, Circuit.denote] using
            OperatorPreservesCleanWork.one layout
      | succ count =>
          have bodyNormalized : IsNormalizedCircuit body := by
            intro gate member
            exact normalized gate (by
              simp [Circuit.flatten, List.replicate_succ, member])
          change OperatorPreservesCleanWork layout
            (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
              (.repeat (Nat.succ count)
                (controlCircuitCorePrelude layout body bodyNormalized)))
          rw [Circuit.denote_repeat]
          exact OperatorPreservesCleanWork.pow layout
            (inductionHypothesis bodyNormalized) (Nat.succ count)

/-- Leaf semantics at the proof-carrying raw core, kept separate from the
public subtype wrapper to avoid proof-projection reduction in AST induction. -/
private theorem controlPrimitiveCore_correct
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : PrimitiveGate sourceQubits)
    (normalized : IsNormalizedPrimitive source) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlPrimitiveCore layout source normalized) =
      controlPrimitiveTargetPrelude symbolValue layout source normalized := by
  cases source with
  | x _ => rfl
  | h target =>
      exact (controlledHadamardSpecialAngleExactOperatorComponent symbolValue {
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }).correct
  | ry angle target =>
      change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (Circuit.controlledRyMacroExpansion layout.control (layout.placement target)
            (layout.control_ne_placed target) angle) =
        embedControlledSingleQubitOperator layout.control (layout.placement target)
          (layout.control_ne_placed target) (localRy (angle.eval symbolValue))
      simp only [Circuit.controlledRyMacroExpansion, Circuit.fromList, Circuit.denote,
        primitiveGateOperatorWithSymbols, Circuit.halfAngle, AngleExpr.eval, Matrix.one_mul]
      rw [show deterministicOperator
          (fun input => xorWire (layout.placement target) (input layout.control) input) =
            analyticCnotOperator layout.control (layout.placement target) by rfl]
      rw [analyticCnotOperator_eq_embedTwo_localCnot
        layout.control (layout.placement target) (layout.control_ne_placed target)]
      rw [← embedTwoQubitOperator_localOnTarget layout.control (layout.placement target)
          (layout.control_ne_placed target),
        ← embedTwoQubitOperator_localOnTarget layout.control (layout.placement target)
          (layout.control_ne_placed target)]
      rw [← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul,
        ← embedTwoQubitOperator_mul]
      unfold embedControlledSingleQubitOperator
      apply congrArg (embedTwoQubitOperator layout.control (layout.placement target)
        (layout.control_ne_placed target))
      convert local_controlledRy_decomposition (angle.eval symbolValue) using 1
      norm_num
      ring_nf
  | phaseShift angle target =>
      change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (controlledPhaseShiftFiveGateCircuit layout angle target) =
        controlledPhaseShiftTarget symbolValue layout angle target
      simp only [controlledPhaseShiftFiveGateCircuit, Circuit.fromList, Circuit.denote,
        primitiveGateOperatorWithSymbols, AngleExpr.eval_neg, phaseShiftHalfAngle_eval,
        Matrix.one_mul]
      rw [show deterministicOperator
          (fun input => xorWire (layout.placement target) (input layout.control) input) =
            analyticCnotOperator layout.control (layout.placement target) by rfl]
      rw [analyticCnotOperator_eq_embedTwo_localCnot
        layout.control (layout.placement target) (layout.control_ne_placed target)]
      rw [← embedTwoQubitOperator_localOnTarget layout.control (layout.placement target)
          (layout.control_ne_placed target),
        ← embedTwoQubitOperator_localOnTarget layout.control (layout.placement target)
          (layout.control_ne_placed target),
        ← embedTwoQubitOperator_localOnControl layout.control (layout.placement target)
          (layout.control_ne_placed target)]
      rw [← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul,
        ← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul]
      unfold controlledPhaseShiftTarget analyticControlledPhaseOperator
      rw [local_controlledPhaseShift_decomposition]
  | cnot _ _ _ => rfl
  | toffoli firstControl secondControl target _ _ _ =>
      let stage := ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement firstControl,
          layout.placement secondControl]
        layout.workList (layout.placement target)
      change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) stage.compile =
        stage.analyticOperator
      rw [← ClassicalReversibleStage.primitiveExactOperatorComponent_circuit
        symbolValue stage]
      rw [(stage.primitiveExactOperatorComponent symbolValue).correct]
      exact ClassicalReversibleStage.primitiveExactOperatorComponent_target
        symbolValue stage
/-- Repackage a certified raw AST as a circuit whose leaf type itself is the
normalized subtype.  The zero-repeat case discards its semantically
unreachable body, so no legacy leaf can be recovered from it. -/
private def normalizedCircuitTypedCore {qubits : Nat} :
    (circuit : Circuit (PrimitiveGate qubits)) →
      IsNormalizedCircuit circuit → Circuit (NormalizedPrimitiveGate qubits)
  | .identity, _ => .identity
  | .gate gate, normalized =>
      .gate ⟨gate, normalized gate (by simp [Circuit.flatten])⟩
  | .seq first second, normalized =>
      .seq
        (normalizedCircuitTypedCore first (by
          intro gate member
          exact normalized gate (by simp [Circuit.flatten, member])))
        (normalizedCircuitTypedCore second (by
          intro gate member
          exact normalized gate (by simp [Circuit.flatten, member])))
  | .repeat 0 _, _ => .identity
  | .repeat (Nat.succ count) body, normalized =>
      .repeat (Nat.succ count)
        (normalizedCircuitTypedCore body (by
          intro gate member
          exact normalized gate (by
            simp [Circuit.flatten, List.replicate_succ, member])))

/-- Exact semantics of the structural compiler against the typed normalized
source language. -/
private theorem controlCircuitCore_correct
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (circuit : Circuit (PrimitiveGate sourceQubits))
    (normalized : IsNormalizedCircuit circuit) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuitCorePrelude layout circuit normalized) =
      Circuit.denote (controlPrimitiveTarget symbolValue layout)
        (normalizedCircuitTypedCore circuit normalized) := by
  induction circuit with
  | identity =>
      simp [controlCircuitCorePrelude, normalizedCircuitTypedCore, Circuit.denote]
  | gate gate =>
      change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (controlPrimitiveCore layout gate
            (normalized gate (by simp [Circuit.flatten]))) =
        controlPrimitiveTargetPrelude symbolValue layout gate
          (normalized gate (by simp [Circuit.flatten]))
      exact controlPrimitiveCore_correct symbolValue layout gate
        (normalized gate (by simp [Circuit.flatten]))
  | seq first second firstInduction secondInduction =>
      have firstNormalized : IsNormalizedCircuit first := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      have secondNormalized : IsNormalizedCircuit second := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (.seq (controlCircuitCorePrelude layout first firstNormalized)
            (controlCircuitCorePrelude layout second secondNormalized)) =
        Circuit.denote (controlPrimitiveTarget symbolValue layout)
          (.seq (normalizedCircuitTypedCore first firstNormalized)
            (normalizedCircuitTypedCore second secondNormalized))
      rw [Circuit.denote_seq, Circuit.denote_seq]
      rw [firstInduction firstNormalized, secondInduction secondNormalized]
  | «repeat» count body inductionHypothesis =>
      cases count with
      | zero =>
          simp [controlCircuitCorePrelude, normalizedCircuitTypedCore,
            Circuit.denote]
      | succ count =>
          have bodyNormalized : IsNormalizedCircuit body := by
            intro gate member
            exact normalized gate (by
              simp [Circuit.flatten, List.replicate_succ, member])
          change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
              (.repeat (Nat.succ count)
                (controlCircuitCorePrelude layout body bodyNormalized)) =
            Circuit.denote (controlPrimitiveTarget symbolValue layout)
              (.repeat (Nat.succ count)
                (normalizedCircuitTypedCore body bodyNormalized))
          rw [Circuit.denote_repeat, Circuit.denote_repeat]
          rw [inductionHypothesis bodyNormalized]

/-- The typed source representation commutes with source-level inversion. -/
private theorem normalizedCircuitTypedCore_reverse
    {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits))
    (normalized : IsNormalizedCircuit circuit) :
    normalizedCircuitTypedCore (circuit.reverse PrimitiveGate.inverse)
        (normalizedCircuit_reverse circuit normalized) =
      (normalizedCircuitTypedCore circuit normalized).reverse
        NormalizedPrimitiveGate.inverse := by
  induction circuit with
  | identity => rfl
  | gate gate => rfl
  | seq first second firstInduction secondInduction =>
      have firstNormalized : IsNormalizedCircuit first := by
        intro value member
        exact normalized value (by simp [Circuit.flatten, member])
      have secondNormalized : IsNormalizedCircuit second := by
        intro value member
        exact normalized value (by simp [Circuit.flatten, member])
      simp [Circuit.reverse, normalizedCircuitTypedCore,
        firstInduction firstNormalized, secondInduction secondNormalized]
  | «repeat» count body inductionHypothesis =>
      cases count with
      | zero => rfl
      | succ count =>
          have bodyNormalized : IsNormalizedCircuit body := by
            intro value member
            exact normalized value (by
              simp [Circuit.flatten, List.replicate_succ, member])
          simp [Circuit.reverse, normalizedCircuitTypedCore,
            inductionHypothesis bodyNormalized]

/-- Whole-AST compiler correctness on certified normalized syntax. -/
theorem controlCircuit_normalized_correct
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuit layout source).circuit =
      Circuit.denote (controlPrimitiveTarget symbolValue layout)
        (normalizedCircuitTypedCore source.circuit source.normalized) :=
  controlCircuitCore_correct symbolValue layout source.circuit source.normalized

/-- Compiling the source-level inverse has exactly the adjoint operator of the
compiled source.  This is an operator theorem, not a syntactic circuit claim. -/
theorem controlCircuit_normalized_inverse_denote
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuit layout (NormalizedCircuit.inverse source)).circuit =
      star (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuit layout source).circuit) := by
  calc
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuit layout (NormalizedCircuit.inverse source)).circuit =
      Circuit.denote (controlPrimitiveTarget symbolValue layout)
        (normalizedCircuitTypedCore
          (source.circuit.reverse PrimitiveGate.inverse)
          (normalizedCircuit_reverse source.circuit source.normalized)) :=
      controlCircuitCore_correct symbolValue layout
        (source.circuit.reverse PrimitiveGate.inverse)
        (normalizedCircuit_reverse source.circuit source.normalized)
    _ = Circuit.denote (controlPrimitiveTarget symbolValue layout)
        ((normalizedCircuitTypedCore source.circuit source.normalized).reverse
          NormalizedPrimitiveGate.inverse) := by
      rw [normalizedCircuitTypedCore_reverse source.circuit source.normalized]
    _ = star (Circuit.denote (controlPrimitiveTarget symbolValue layout)
        (normalizedCircuitTypedCore source.circuit source.normalized)) :=
      Circuit.denote_reverse NormalizedPrimitiveGate.inverse
        (controlPrimitiveTarget symbolValue layout)
        (controlPrimitiveTarget_inverse symbolValue layout)
        (normalizedCircuitTypedCore source.circuit source.normalized)
    _ = star (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuit layout source).circuit) := by
      rw [← controlCircuit_normalized_correct symbolValue layout source]

/-- The complete clean-work contract is closed under source-level inversion. -/
theorem controlCircuit_inverse_normalized_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    OperatorPreservesCleanWork layout
      (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuit layout (NormalizedCircuit.inverse source)).circuit) :=
  controlCircuit_normalized_preserves_clean_work symbolValue layout
    (NormalizedCircuit.inverse source)

/-- Transport the inverse compiled-output contract through the exact adjoint
operator equality above. -/
theorem controlCircuit_adjoint_preserves_clean_work
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits) :
    OperatorPreservesCleanWork layout
      (star (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuit layout source).circuit)) := by
  rw [← controlCircuit_normalized_inverse_denote symbolValue layout source]
  exact controlCircuit_inverse_normalized_preserves_clean_work
    symbolValue layout source

/-- The Toffoli lowering is a shared reversible stage with exactly the two
explicit work wires in `ControlLayout`; no existence witness is accepted by
this API. -/
theorem controlPrimitive_toffoli_dirty_correct
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (firstControl secondControl target : Fin sourceQubits)
    (controlsDifferent : firstControl ≠ secondControl)
    (firstDifferent : firstControl ≠ target)
    (secondDifferent : secondControl ≠ target) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlPrimitive layout
          (.toffoli firstControl secondControl target controlsDifferent
            firstDifferent secondDifferent)) =
      controlPrimitiveTarget symbolValue layout
        (.toffoli firstControl secondControl target controlsDifferent
          firstDifferent secondDifferent) := by
  let stage := ClassicalReversibleStage.positiveMultiControlledX
    [layout.control, layout.placement firstControl,
      layout.placement secondControl]
    layout.workList (layout.placement target)
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) stage.compile =
    stage.analyticOperator
  rw [← ClassicalReversibleStage.primitiveExactOperatorComponent_circuit
    symbolValue stage]
  rw [(stage.primitiveExactOperatorComponent symbolValue).correct]
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_target
    symbolValue stage

end ControlledCircuitCompilerV2

end

end VerifiedCircuitCore
