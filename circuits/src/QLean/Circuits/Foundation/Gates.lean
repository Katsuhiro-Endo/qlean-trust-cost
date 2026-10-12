import QLean.Circuits.Foundation.Circuit
import QLean.Circuits.Foundation.PrimitiveOperatorSemantics

/-!
# 型安全な正規化基本ゲート構文と解析作用素への解釈

The executable primitive language has exactly six constructors.  Named
rotations and phase conventions are lowered by their typed macro modules.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- The six normalized primitive gate forms. -/
inductive PrimitiveGate (qubits : Nat) where
  | x (target : Fin qubits)
  | h (target : Fin qubits)
  | ry (angle : AngleExpr) (target : Fin qubits)
  | phaseShift (angle : AngleExpr) (target : Fin qubits)
  | cnot (control target : Fin qubits) (different : control ≠ target)
  | toffoli (control₀ control₁ target : Fin qubits)
      (controlsDifferent : control₀ ≠ control₁)
      (firstDifferent : control₀ ≠ target)
      (secondDifferent : control₁ ≠ target)

/-- Internal interpretation used by generic tooling that deliberately accepts
an external symbol environment.  Public Q-Lean circuits use the environment-
free `primitiveGateOperator` below. -/
def primitiveGateOperatorWithSymbols {qubits : Nat} (symbolValue : String → ℝ) :
    PrimitiveGate qubits → Operator (QubitBasis qubits)
  | .x target => embedSingleQubitOperator target localX
  | .h target => embedSingleQubitOperator target localH
  | .ry angle target => embedSingleQubitOperator target (localRy (angle.eval symbolValue))
  | .phaseShift angle target =>
      embedSingleQubitOperator target (localPhaseShift (angle.eval symbolValue))
  | .cnot control target _ =>
      deterministicOperator fun input => xorWire target (input control) input
  | .toffoli control₀ control₁ target _ _ _ =>
      deterministicOperator fun input =>
        xorWire target (input control₀ && input control₁) input

/-- Canonical public interpretation of normalized primitive gates.  It has no
evaluation-environment argument.  The public-circuit theorems prove that every
generated leaf is symbol-free, so this internal zero choice agrees with every
environment (see `Circuit.denote_primitiveGateOperatorWithSymbols_eq`). -/
noncomputable def primitiveGateOperator {qubits : Nat} :
    PrimitiveGate qubits → Operator (QubitBasis qubits) :=
  primitiveGateOperatorWithSymbols (fun _ => 0)

/-- Replace any remaining external symbol reference by its value in a chosen
environment.  The result is a verified real constant, not a numerical
approximation. -/
def AngleExpr.specializeSymbols (symbolValue : String → ℝ)
    (expression : AngleExpr) : AngleExpr :=
  .const (expression.eval symbolValue)

/-- Resolve only external symbols.  Closed rational, decimal, π, and
composite angle syntax is left intact, so finite numerical programs keep
their exact gate-level representation. -/
def AngleExpr.closeSymbolsPreserving (symbolValue : String → ℝ) :
    AngleExpr → AngleExpr
  | .const value => .const value
  | .rational numerator denominator positive =>
      .rational numerator denominator positive
  | .decimal mantissa scale => .decimal mantissa scale
  | .symbol name => .const (symbolValue name)
  | .pi => .pi
  | .add left right =>
      .add (left.closeSymbolsPreserving symbolValue)
        (right.closeSymbolsPreserving symbolValue)
  | .mul left right =>
      .mul (left.closeSymbolsPreserving symbolValue)
        (right.closeSymbolsPreserving symbolValue)
  | .div left right =>
      .div (left.closeSymbolsPreserving symbolValue)
        (right.closeSymbolsPreserving symbolValue)
  | .neg value => .neg (value.closeSymbolsPreserving symbolValue)
  | .sqrt value => .sqrt (value.closeSymbolsPreserving symbolValue)
  | .acos value => .acos (value.closeSymbolsPreserving symbolValue)

theorem AngleExpr.closeSymbolsPreserving_isSymbolFree
    (symbolValue : String → ℝ) (expression : AngleExpr) :
    (expression.closeSymbolsPreserving symbolValue).IsSymbolFree := by
  induction expression with
  | const | rational | decimal | symbol | pi => trivial
  | add left right ihLeft ihRight | mul left right ihLeft ihRight
  | div left right ihLeft ihRight => exact ⟨ihLeft, ihRight⟩
  | neg value ih | sqrt value ih | acos value ih => exact ih

theorem AngleExpr.closeSymbolsPreserving_eval
    (symbolValue : String → ℝ) (expression : AngleExpr) :
    (expression.closeSymbolsPreserving symbolValue).eval (fun _ => 0) =
      expression.eval symbolValue := by
  induction expression with
  | const | rational | decimal | symbol | pi => rfl
  | add left right ihLeft ihRight | mul left right ihLeft ihRight
  | div left right ihLeft ihRight => simp [AngleExpr.closeSymbolsPreserving,
      AngleExpr.eval, ihLeft, ihRight]
  | neg value ih | sqrt value ih | acos value ih =>
      simp [AngleExpr.closeSymbolsPreserving, AngleExpr.eval, ih]

theorem AngleExpr.closeSymbolsPreserving_eq_self_of_isSymbolFree
    (symbolValue : String → ℝ) (expression : AngleExpr)
    (closed : expression.IsSymbolFree) :
    expression.closeSymbolsPreserving symbolValue = expression := by
  induction expression with
  | const | rational | decimal | pi => rfl
  | symbol name => simp [AngleExpr.IsSymbolFree] at closed
  | add left right ihLeft ihRight | mul left right ihLeft ihRight
  | div left right ihLeft ihRight =>
      simp only [AngleExpr.IsSymbolFree] at closed
      simp [AngleExpr.closeSymbolsPreserving, ihLeft closed.1,
        ihRight closed.2]
  | neg value ih | sqrt value ih | acos value ih =>
      simpa [AngleExpr.closeSymbolsPreserving] using ih closed

/-- Gatewise syntax-preserving closing transformation. -/
def PrimitiveGate.closeSymbolsPreserving {qubits : Nat}
    (symbolValue : String → ℝ) : PrimitiveGate qubits → PrimitiveGate qubits
  | .x target => .x target
  | .h target => .h target
  | .ry angle target => .ry (angle.closeSymbolsPreserving symbolValue) target
  | .phaseShift angle target =>
      .phaseShift (angle.closeSymbolsPreserving symbolValue) target
  | .cnot control target different => .cnot control target different
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      .toffoli control₀ control₁ target controlsDifferent firstDifferent
        secondDifferent

def Circuit.closeSymbolsPreserving {qubits : Nat} (symbolValue : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits)) :
    Circuit (PrimitiveGate qubits) :=
  circuit.mapGates (PrimitiveGate.closeSymbolsPreserving symbolValue)

/-- Close the angle payload of a primitive gate while preserving its wires. -/
def PrimitiveGate.specializeSymbols {qubits : Nat}
    (symbolValue : String → ℝ) : PrimitiveGate qubits → PrimitiveGate qubits
  | .x target => .x target
  | .h target => .h target
  | .ry angle target => .ry (angle.specializeSymbols symbolValue) target
  | .phaseShift angle target =>
      .phaseShift (angle.specializeSymbols symbolValue) target
  | .cnot control target different => .cnot control target different
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      .toffoli control₀ control₁ target controlsDifferent firstDifferent
        secondDifferent

/-- Close every primitive leaf of a circuit in one typed lowering pass. -/
def Circuit.specializeSymbols {qubits : Nat} (symbolValue : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits)) :
    Circuit (PrimitiveGate qubits) :=
  circuit.mapGates (PrimitiveGate.specializeSymbols symbolValue)

/-- A normalized primitive gate contains no externally supplied angle symbol. -/
def PrimitiveGate.IsSymbolFree {qubits : Nat} : PrimitiveGate qubits → Prop
  | .ry angle _ | .phaseShift angle _ => angle.IsSymbolFree
  | _ => True

/-- Every primitive leaf of a circuit is independent of external symbols. -/
def Circuit.IsSymbolFree {qubits : Nat} :
    Circuit (PrimitiveGate qubits) → Prop
  | .identity => True
  | .gate value => PrimitiveGate.IsSymbolFree value
  | .seq first second => first.IsSymbolFree ∧ second.IsSymbolFree
  | .repeat _ body => body.IsSymbolFree

/-- Specializing an angle removes every external symbol. -/
theorem AngleExpr.specializeSymbols_isSymbolFree
    (symbolValue : String → ℝ) (expression : AngleExpr) :
    (expression.specializeSymbols symbolValue).IsSymbolFree := by
  trivial

/-- Every specialized primitive gate is symbol-free. -/
theorem PrimitiveGate.specializeSymbols_isSymbolFree {qubits : Nat}
    (symbolValue : String → ℝ) (gate : PrimitiveGate qubits) :
    PrimitiveGate.IsSymbolFree (gate.specializeSymbols symbolValue) := by
  cases gate <;> trivial

/-- Every circuit produced by the closing pass is symbol-free. -/
theorem Circuit.specializeSymbols_isSymbolFree {qubits : Nat}
    (symbolValue : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits)) :
    Circuit.IsSymbolFree (circuit.specializeSymbols symbolValue) := by
  unfold Circuit.specializeSymbols
  induction circuit with
  | identity =>
      change True
      trivial
  | gate value =>
      change PrimitiveGate.IsSymbolFree
        (value.specializeSymbols symbolValue)
      exact PrimitiveGate.specializeSymbols_isSymbolFree symbolValue value
  | seq first second firstInduction secondInduction =>
      exact ⟨firstInduction, secondInduction⟩
  | «repeat» _ body inductionHypothesis => exact inductionHypothesis

/-- Mapping a circuit to symbol-free primitive leaves produces a symbol-free
circuit.  This covers wire maps and controlled lowering, which are expressed
through `Circuit.mapGates`. -/
theorem Circuit.isSymbolFree_mapGates
    {Gate : Type*} {qubits : Nat}
    (mapGate : Gate → PrimitiveGate qubits)
    (mapGateSymbolFree : ∀ gate, PrimitiveGate.IsSymbolFree (mapGate gate)) :
    ∀ circuit : Circuit Gate,
      Circuit.IsSymbolFree (circuit.mapGates mapGate) := by
  intro circuit
  induction circuit with
  | identity =>
      change True
      trivial
  | gate value =>
      change PrimitiveGate.IsSymbolFree (mapGate value)
      exact mapGateSymbolFree value
  | seq first second firstInduction secondInduction =>
      change Circuit.IsSymbolFree (first.mapGates mapGate) ∧
        Circuit.IsSymbolFree (second.mapGates mapGate)
      exact ⟨firstInduction, secondInduction⟩
  | «repeat» _ body inductionHypothesis =>
      change Circuit.IsSymbolFree (body.mapGates mapGate)
      exact inductionHypothesis

/-- Resolving only external symbols makes every gate and circuit closed. -/
theorem PrimitiveGate.closeSymbolsPreserving_isSymbolFree {qubits : Nat}
    (symbolValue : String → ℝ) (gate : PrimitiveGate qubits) :
    PrimitiveGate.IsSymbolFree (gate.closeSymbolsPreserving symbolValue) := by
  cases gate <;> simp [PrimitiveGate.closeSymbolsPreserving,
    PrimitiveGate.IsSymbolFree,
    AngleExpr.closeSymbolsPreserving_isSymbolFree]

theorem Circuit.closeSymbolsPreserving_isSymbolFree {qubits : Nat}
    (symbolValue : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits)) :
    Circuit.IsSymbolFree (circuit.closeSymbolsPreserving symbolValue) := by
  exact Circuit.isSymbolFree_mapGates
    (PrimitiveGate.closeSymbolsPreserving symbolValue)
    (PrimitiveGate.closeSymbolsPreserving_isSymbolFree symbolValue) circuit

/-- Compiling each source leaf to a symbol-free primitive circuit preserves
symbol-freedom. -/
theorem Circuit.isSymbolFree_compileGates
    {Gate : Type*} {qubits : Nat}
    (compileGate : Gate → Circuit (PrimitiveGate qubits))
    (compileGateSymbolFree : ∀ gate,
      Circuit.IsSymbolFree (compileGate gate)) :
    ∀ circuit : Circuit Gate,
      Circuit.IsSymbolFree (circuit.compileGates compileGate) := by
  intro circuit
  induction circuit with
  | identity =>
      change True
      trivial
  | gate value =>
      change Circuit.IsSymbolFree (compileGate value)
      exact compileGateSymbolFree value
  | seq first second firstInduction secondInduction =>
      change Circuit.IsSymbolFree (first.compileGates compileGate) ∧
        Circuit.IsSymbolFree (second.compileGates compileGate)
      exact ⟨firstInduction, secondInduction⟩
  | «repeat» _ body inductionHypothesis =>
      change Circuit.IsSymbolFree (body.compileGates compileGate)
      exact inductionHypothesis

/-- Sequencing a list of symbol-free circuits is symbol-free. -/
theorem Circuit.isSymbolFree_sequence {qubits : Nat}
    (circuits : List (Circuit (PrimitiveGate qubits)))
    (allSymbolFree : ∀ circuit ∈ circuits,
      Circuit.IsSymbolFree circuit) :
    Circuit.IsSymbolFree (Circuit.sequence circuits) := by
  induction circuits with
  | nil =>
      change True
      trivial
  | cons first rest inductionHypothesis =>
      change Circuit.IsSymbolFree first ∧
        Circuit.IsSymbolFree (Circuit.sequence rest)
      exact ⟨allSymbolFree first (by simp),
        inductionHypothesis (fun circuit member =>
          allSymbolFree circuit (by simp [member]))⟩

/-- Forming a circuit from a list of symbol-free gates is symbol-free. -/
theorem Circuit.isSymbolFree_fromList {qubits : Nat}
    (gates : List (PrimitiveGate qubits))
    (allSymbolFree : ∀ gate ∈ gates,
      PrimitiveGate.IsSymbolFree gate) :
    Circuit.IsSymbolFree (Circuit.fromList gates) := by
  induction gates with
  | nil =>
      change True
      trivial
  | cons first rest inductionHypothesis =>
      change PrimitiveGate.IsSymbolFree first ∧
        Circuit.IsSymbolFree (Circuit.fromList rest)
      exact ⟨allSymbolFree first (by simp),
        inductionHypothesis (fun gate member =>
          allSymbolFree gate (by simp [member]))⟩

/-- Every leaf appearing in the flattened gate stream of a symbol-free
circuit is symbol-free. -/
theorem Circuit.flatten_gate_isSymbolFree {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits))
    (symbolFree : Circuit.IsSymbolFree circuit) :
    ∀ gate ∈ circuit.flatten, PrimitiveGate.IsSymbolFree gate := by
  induction circuit with
  | identity => simp [Circuit.flatten]
  | gate value =>
      intro gate member
      change PrimitiveGate.IsSymbolFree value at symbolFree
      rcases List.mem_singleton.mp member with rfl
      exact symbolFree
  | seq first second firstInduction secondInduction =>
      intro gate member
      simp only [Circuit.flatten, List.mem_append] at member
      rcases member with member | member
      · exact firstInduction symbolFree.1 gate member
      · exact secondInduction symbolFree.2 gate member
  | «repeat» count body inductionHypothesis =>
      intro gate member
      simp only [Circuit.flatten, List.mem_flatten] at member
      rcases member with ⟨stream, streamMember, gateMember⟩
      have streamEq : stream = body.flatten := by
        exact (List.mem_replicate.mp streamMember).2
      subst stream
      exact inductionHypothesis symbolFree gate gateMember

/-- A flattened prefix reconstructed as a circuit remains symbol-free. -/
theorem Circuit.isSymbolFree_fromList_take_flatten {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits))
    (symbolFree : Circuit.IsSymbolFree circuit) (count : Nat) :
    Circuit.IsSymbolFree (Circuit.fromList (circuit.flatten.take count)) := by
  apply Circuit.isSymbolFree_fromList
  intro gate member
  exact Circuit.flatten_gate_isSymbolFree circuit symbolFree gate
    (List.mem_of_mem_take member)

/-- A flattened suffix reconstructed as a circuit remains symbol-free. -/
theorem Circuit.isSymbolFree_fromList_drop_flatten {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits))
    (symbolFree : Circuit.IsSymbolFree circuit) (count : Nat) :
    Circuit.IsSymbolFree (Circuit.fromList (circuit.flatten.drop count)) := by
  apply Circuit.isSymbolFree_fromList
  intro gate member
  exact Circuit.flatten_gate_isSymbolFree circuit symbolFree gate
    (List.mem_of_mem_drop member)

/-- A symbol-free primitive has the same analytic action in every external
environment. -/
theorem PrimitiveGate.operatorWithSymbols_eq_of_isSymbolFree
    {qubits : Nat} (gate : PrimitiveGate qubits)
    (symbolFree : PrimitiveGate.IsSymbolFree gate)
    (first second : String → ℝ) :
    primitiveGateOperatorWithSymbols first gate =
      primitiveGateOperatorWithSymbols second gate := by
  cases gate <;>
    simp_all only [PrimitiveGate.IsSymbolFree, primitiveGateOperatorWithSymbols]
  all_goals rw [AngleExpr.eval_eq_of_isSymbolFree _ symbolFree first second]

/-- Closing a primitive gate in `symbolValue` preserves exactly its analytic
action under that environment. -/
theorem PrimitiveGate.operator_specializeSymbols
    {qubits : Nat} (symbolValue : String → ℝ)
    (gate : PrimitiveGate qubits) :
    primitiveGateOperator (gate.specializeSymbols symbolValue) =
      primitiveGateOperatorWithSymbols symbolValue gate := by
  cases gate <;> rfl

/-- Closing every leaf preserves exactly the circuit denotation selected by
the supplied environment. -/
theorem Circuit.denote_specializeSymbols
    {qubits : Nat} (symbolValue : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits)) :
    Circuit.denote primitiveGateOperator
        (circuit.specializeSymbols symbolValue) =
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) circuit := by
  rw [Circuit.specializeSymbols, Circuit.denote_mapGates]
  apply Circuit.denote_congr
  exact PrimitiveGate.operator_specializeSymbols symbolValue

theorem PrimitiveGate.operator_closeSymbolsPreserving
    {qubits : Nat} (symbolValue : String → ℝ)
    (gate : PrimitiveGate qubits) :
    primitiveGateOperator (gate.closeSymbolsPreserving symbolValue) =
      primitiveGateOperatorWithSymbols symbolValue gate := by
  cases gate <;>
    simp only [PrimitiveGate.closeSymbolsPreserving,
      primitiveGateOperator, primitiveGateOperatorWithSymbols,
      AngleExpr.closeSymbolsPreserving_eval]

theorem Circuit.denote_closeSymbolsPreserving
    {qubits : Nat} (symbolValue : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits)) :
    Circuit.denote primitiveGateOperator
        (circuit.closeSymbolsPreserving symbolValue) =
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) circuit := by
  rw [Circuit.closeSymbolsPreserving, Circuit.denote_mapGates]
  apply Circuit.denote_congr
  exact PrimitiveGate.operator_closeSymbolsPreserving symbolValue

/-- A symbol-free circuit has the same denotation in every external
environment. -/
theorem Circuit.denote_primitiveGateOperatorWithSymbols_eq
    {qubits : Nat} (circuit : Circuit (PrimitiveGate qubits))
    (symbolFree : Circuit.IsSymbolFree circuit)
    (first second : String → ℝ) :
    Circuit.denote (primitiveGateOperatorWithSymbols first) circuit =
      Circuit.denote (primitiveGateOperatorWithSymbols second) circuit := by
  induction circuit with
  | identity => rfl
  | gate gate =>
      change PrimitiveGate.IsSymbolFree gate at symbolFree
      exact gate.operatorWithSymbols_eq_of_isSymbolFree symbolFree first second
  | seq left right leftInduction rightInduction =>
      exact congrArg₂ (fun x y => x * y)
        (rightInduction symbolFree.2) (leftInduction symbolFree.1)
  | «repeat» count body inductionHypothesis =>
      exact congrArg (fun operator => operator ^ count)
        (inductionHypothesis symbolFree)

/-- On a symbol-free circuit the public environment-free interpretation equals
the legacy environment-parameterized interpretation for every environment. -/
theorem Circuit.denote_primitiveGateOperator_eq_withSymbols
    {qubits : Nat} (circuit : Circuit (PrimitiveGate qubits))
    (symbolFree : Circuit.IsSymbolFree circuit)
    (symbolValue : String → ℝ) :
    Circuit.denote primitiveGateOperator circuit =
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) circuit := by
  exact Circuit.denote_primitiveGateOperatorWithSymbols_eq circuit symbolFree
    (fun _ => 0) symbolValue

/-- Evaluating a closed circuit in any environment gives exactly the action
selected when its symbols were specialized.  This is the compatibility bridge
used by the legacy environment-parameterized implementation proofs. -/
theorem Circuit.denote_withSymbols_specializeSymbols
    {qubits : Nat} (selectedEnvironment actualEnvironment : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits)) :
    Circuit.denote (primitiveGateOperatorWithSymbols actualEnvironment)
        (circuit.specializeSymbols selectedEnvironment) =
      Circuit.denote (primitiveGateOperatorWithSymbols selectedEnvironment)
        circuit := by
  calc
    Circuit.denote (primitiveGateOperatorWithSymbols actualEnvironment)
        (circuit.specializeSymbols selectedEnvironment) =
        Circuit.denote primitiveGateOperator
          (circuit.specializeSymbols selectedEnvironment) :=
      (Circuit.denote_primitiveGateOperator_eq_withSymbols _
        (Circuit.specializeSymbols_isSymbolFree selectedEnvironment circuit)
        actualEnvironment).symm
    _ = Circuit.denote
          (primitiveGateOperatorWithSymbols selectedEnvironment) circuit :=
      Circuit.denote_specializeSymbols selectedEnvironment circuit

theorem Circuit.denote_withSymbols_closeSymbolsPreserving
    {qubits : Nat} (selectedEnvironment actualEnvironment : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits)) :
    Circuit.denote (primitiveGateOperatorWithSymbols actualEnvironment)
        (circuit.closeSymbolsPreserving selectedEnvironment) =
      Circuit.denote (primitiveGateOperatorWithSymbols selectedEnvironment)
        circuit := by
  calc
    Circuit.denote (primitiveGateOperatorWithSymbols actualEnvironment)
        (circuit.closeSymbolsPreserving selectedEnvironment) =
        Circuit.denote primitiveGateOperator
          (circuit.closeSymbolsPreserving selectedEnvironment) :=
      (Circuit.denote_primitiveGateOperator_eq_withSymbols _
        (Circuit.closeSymbolsPreserving_isSymbolFree selectedEnvironment circuit)
        actualEnvironment).symm
    _ = Circuit.denote
          (primitiveGateOperatorWithSymbols selectedEnvironment) circuit :=
      Circuit.denote_closeSymbolsPreserving selectedEnvironment circuit

/-- Syntactic inverse of a normalized primitive. -/
def PrimitiveGate.inverse {qubits : Nat} : PrimitiveGate qubits → PrimitiveGate qubits
  | .x target => .x target
  | .h target => .h target
  | .ry angle target => .ry (.neg angle) target
  | .phaseShift angle target => .phaseShift (.neg angle) target
  | .cnot control target different => .cnot control target different
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent secondDifferent =>
      .toffoli control₀ control₁ target controlsDifferent firstDifferent secondDifferent

/-- Injectively map a normalized primitive to a wider register. -/
def PrimitiveGate.mapWires {sourceQubits targetQubits : Nat}
    (embedding : Fin sourceQubits ↪ Fin targetQubits) :
    PrimitiveGate sourceQubits → PrimitiveGate targetQubits
  | .x target => .x (embedding target)
  | .h target => .h (embedding target)
  | .ry angle target => .ry angle (embedding target)
  | .phaseShift angle target => .phaseShift angle (embedding target)
  | .cnot control target different =>
      .cnot (embedding control) (embedding target)
        (fun equal => different (embedding.injective equal))
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent secondDifferent =>
      .toffoli (embedding control₀) (embedding control₁) (embedding target)
        (fun equal => controlsDifferent (embedding.injective equal))
        (fun equal => firstDifferent (embedding.injective equal))
        (fun equal => secondDifferent (embedding.injective equal))

/-- Symbol-freedom is preserved by primitive inversion. -/
theorem PrimitiveGate.inverse_isSymbolFree {qubits : Nat}
    (gate : PrimitiveGate qubits)
    (symbolFree : PrimitiveGate.IsSymbolFree gate) :
    PrimitiveGate.IsSymbolFree gate.inverse := by
  cases gate <;> simp_all [PrimitiveGate.inverse, PrimitiveGate.IsSymbolFree,
    AngleExpr.IsSymbolFree]

/-- Symbol-freedom is preserved by injective wire remapping. -/
theorem PrimitiveGate.mapWires_isSymbolFree {sourceQubits targetQubits : Nat}
    (embedding : Fin sourceQubits ↪ Fin targetQubits)
    (gate : PrimitiveGate sourceQubits)
    (symbolFree : PrimitiveGate.IsSymbolFree gate) :
    PrimitiveGate.IsSymbolFree (gate.mapWires embedding) := by
  cases gate <;> simp_all [PrimitiveGate.mapWires, PrimitiveGate.IsSymbolFree]

/-- Reversing a symbol-free primitive circuit remains symbol-free. -/
theorem Circuit.isSymbolFree_reverse {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits))
    (symbolFree : Circuit.IsSymbolFree circuit) :
    Circuit.IsSymbolFree (circuit.reverse PrimitiveGate.inverse) := by
  induction circuit with
  | identity => trivial
  | gate gate =>
      change PrimitiveGate.IsSymbolFree gate at symbolFree
      exact gate.inverse_isSymbolFree symbolFree
  | seq first second firstInduction secondInduction =>
      exact ⟨secondInduction symbolFree.2, firstInduction symbolFree.1⟩
  | «repeat» _ body inductionHypothesis => exact inductionHypothesis symbolFree

/-- Every constructor of `PrimitiveGate` is normalized by construction. -/
def IsNormalizedPrimitive {qubits : Nat} : PrimitiveGate qubits → Prop
  | .x _ | .h _ | .ry _ _ | .phaseShift _ _ | .cnot _ _ _ |
      .toffoli _ _ _ _ _ _ => True

end

end VerifiedCircuitCore
