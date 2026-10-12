import QLean.Circuits.Foundation.ControlledCircuitCompilerV2

/-! Control compilation respects a source's flattened gate sequence. This
allows finite history syntax to use an existing history proof without asking
for equality of two state-preparation unitaries. -/

set_option autoImplicit false
set_option warningAsError true

namespace VerifiedCircuitCore.ControlledCircuitCompilerV2

@[simp] theorem normalizedCircuit_source_cast_circuit {n m : Nat}
    (width : n = m) (source : NormalizedCircuit n) :
    (Eq.mp (congrArg NormalizedCircuit width) source).circuit =
      width ▸ source.circuit := by cases width; rfl

@[simp] theorem controlLayout_source_cast_control {n m target : Nat}
    (width : n = m) (layout : ControlLayout n target) :
    (Eq.mp (congrArg (fun k => ControlLayout k target) width) layout).control =
      layout.control := by cases width; rfl

@[simp] theorem controlLayout_source_cast_work {n m target : Nat}
    (width : n = m) (layout : ControlLayout n target) (slot : Fin 2) :
    (Eq.mp (congrArg (fun k => ControlLayout k target) width) layout).work slot =
      layout.work slot := by cases width; rfl

theorem controlCircuit_source_cast {n m target : Nat} (width : n = m)
    (layout : ControlLayout n target) (source : NormalizedCircuit n) :
    (controlCircuit
      (Eq.mp (congrArg (fun k => ControlLayout k target) width) layout)
      (Eq.mp (congrArg NormalizedCircuit width) source)).circuit =
      (controlCircuit layout source).circuit := by
  cases width
  rfl

def totalControlLeaf {n m : Nat} (layout : ControlLayout n m)
    (gate : PrimitiveGate n) : Circuit (PrimitiveGate m) :=
  (controlPrimitive layout ⟨gate, by cases gate <;> trivial⟩).circuit

theorem controlCircuit_flatten_eq_compileGates {n m : Nat}
    (layout : ControlLayout n m) (circuit : Circuit (PrimitiveGate n))
    (normalized : IsNormalizedCircuit circuit) :
    (controlCircuit layout ⟨circuit, normalized⟩).circuit.flatten =
      (circuit.compileGates (totalControlLeaf layout)).flatten := by
  induction circuit with
  | identity => rfl
  | gate gate => rfl
  | seq first second firstIH secondIH =>
      have nf : IsNormalizedCircuit first := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      have ns : IsNormalizedCircuit second := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      change (controlCircuit layout ⟨first, nf⟩).circuit.flatten ++
          (controlCircuit layout ⟨second, ns⟩).circuit.flatten = _
      rw [firstIH nf, secondIH ns]
      rfl
  | «repeat» count body ih =>
      cases count with
      | zero => rfl
      | succ count =>
          have nb : IsNormalizedCircuit body := by
            intro gate member
            exact normalized gate (by
              simp [Circuit.flatten, List.replicate_succ, member])
          change (List.replicate (count + 1)
              (controlCircuit layout ⟨body, nb⟩).circuit.flatten).flatten = _
          rw [ih nb]
          rfl

theorem controlCircuit_flatten_congr {n m : Nat}
    (layout : ControlLayout n m) (left right : NormalizedCircuit n)
    (same : left.circuit.flatten = right.circuit.flatten) :
    (controlCircuit layout left).circuit.flatten =
      (controlCircuit layout right).circuit.flatten := by
  rw [controlCircuit_flatten_eq_compileGates,
    controlCircuit_flatten_eq_compileGates,
    Circuit.flatten_compileGates, Circuit.flatten_compileGates, same]

theorem controlCircuit_denote_congr {n m : Nat}
    (layout : ControlLayout n m) (left right : NormalizedCircuit n)
    (same : left.circuit.flatten = right.circuit.flatten)
    (operator : PrimitiveGate m → Operator (QubitBasis m)) :
    Circuit.denote operator (controlCircuit layout left).circuit =
      Circuit.denote operator (controlCircuit layout right).circuit :=
  Circuit.denote_eq_of_flatten operator _ _
    (controlCircuit_flatten_congr layout left right same)

end VerifiedCircuitCore.ControlledCircuitCompilerV2
