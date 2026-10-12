import QLean.History.Implementation.HistoryPipelineControlledRotationAction

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore

noncomputable section

/-- A source-order operator word fixes a state when every member fixes it. -/
theorem applyOperator_operatorSequence_of_each_fixes119
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operators : List (Operator basis)) (state : State basis)
    (fixes : ∀ operator, operator ∈ operators →
      applyOperator operator state = state) :
    applyOperator (operatorSequence operators) state = state := by
  induction operators with
  | nil =>
      change applyOperator (1 : Operator basis) state = state
      funext output
      simp only [applyOperator, Matrix.mulVec, dotProduct, Matrix.one_apply]
      simp
  | cons first rest inductionHypothesis =>
      simp only [operatorSequence, applyOperator_mul]
      rw [fixes first (by simp)]
      apply inductionHypothesis
      intro operator member
      exact fixes operator (by simp [member])

/-- In a finite source-order word of one-qubit rotations with a common target,
if exactly one index is enabled and every predicate ignores that target wire,
the whole word has exactly the selected `Ry` action on a zero target. -/
theorem applyOperator_single_selected_controlledRy_loop119
    {qubits n : Nat}
    (predicate : Fin n → QubitBasis qubits → Bool)
    (target : Fin qubits)
    (angles : Fin n → Real)
    (selected : Fin n)
    (input : QubitBasis qubits)
    (targetFalse : input target = false)
    (selectedTrue : predicate selected input = true)
    (otherFalse : ∀ index, index ≠ selected →
      predicate index input = false)
    (predicateReplace : ∀ index value,
      predicate index (replaceQubitWire input target value) =
        predicate index input) :
    applyOperator
        (operatorSequence ((List.finRange n).map (fun index =>
          predicateControlledSingleQubitOperator (predicate index) target
            (localRy (angles index)))))
        (basisKet input) =
      ((Real.cos (angles selected / 2) : Real) : Complex) • basisKet input +
        ((Real.sin (angles selected / 2) : Real) : Complex) •
          basisKet (replaceQubitWire input target true) := by
  obtain ⟨before, after, split, selectedNotBefore⟩ :=
    List.eq_append_cons_of_mem (List.mem_finRange selected)
  have allNodup : (List.finRange n).Nodup := List.nodup_finRange n
  rw [split] at allNodup
  have selectedNotAfter : selected ∉ after :=
    (List.nodup_cons.mp (List.nodup_append.mp allNodup).2.1).1
  let iteration : Fin n → Operator (QubitBasis qubits) := fun index =>
    predicateControlledSingleQubitOperator (predicate index) target
      (localRy (angles index))
  let selectedState : State (QubitBasis qubits) :=
    ((Real.cos (angles selected / 2) : Real) : Complex) • basisKet input +
      ((Real.sin (angles selected / 2) : Real) : Complex) •
        basisKet (replaceQubitWire input target true)
  have beforeFixes :
      applyOperator (operatorSequence (before.map iteration))
          (basisKet input) = basisKet input := by
    apply applyOperator_operatorSequence_of_each_fixes119
    intro operator member
    rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
    apply applyOperator_predicateControlledSingleQubitOperator_basisKet_column_false119
    apply otherFalse index
    intro equal
    exact selectedNotBefore (equal ▸ indexMember)
  have selectedAction :
      applyOperator (iteration selected) (basisKet input) = selectedState := by
    dsimp only [iteration, selectedState]
    exact applyOperator_predicateControlledRy_basisKet_of_true_false119
      (predicate selected) target (angles selected) input selectedTrue targetFalse
  have afterFixes :
      applyOperator (operatorSequence (after.map iteration)) selectedState =
        selectedState := by
    apply applyOperator_operatorSequence_of_each_fixes119
    intro operator member
    rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
    have indexNe : index ≠ selected := by
      intro equal
      exact selectedNotAfter (equal ▸ indexMember)
    have falseInput : predicate index input = false := otherFalse index indexNe
    have falseFlipped :
        predicate index (replaceQubitWire input target true) = false := by
      rw [predicateReplace index true, falseInput]
    dsimp only [selectedState]
    rw [applyOperator_add, applyOperator_smul, applyOperator_smul]
    rw [applyOperator_predicateControlledSingleQubitOperator_basisKet_column_false119
      (predicate index) target (localRy (angles index)) input falseInput]
    rw [applyOperator_predicateControlledSingleQubitOperator_basisKet_column_false119
      (predicate index) target (localRy (angles index))
      (replaceQubitWire input target true) falseFlipped]
  change applyOperator
      (operatorSequence ((List.finRange n).map iteration)) (basisKet input) =
    selectedState
  rw [split, List.map_append, List.map_cons,
    operatorSequence_append, applyOperator_mul, beforeFixes]
  simp only [operatorSequence, applyOperator_mul]
  rw [selectedAction, afterFixes]

end
end ExecutableHistoryExecutableHistory
