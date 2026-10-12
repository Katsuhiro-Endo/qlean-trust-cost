import QLean.SignalProcessing.NativeConcreteP18QSPWitness

/-! A computable image-phase builder with an explicit finite enumeration.
The list is execution data; completeness and injectivity occur only in the
proofs. No choice of a `Finset.toList` occurs in the circuit constructor. -/

set_option autoImplicit false
set_option warningAsError true

namespace VerifiedCircuitCore.OrderedImagePhase

open NativeEmbeddingImagePhase NativeExactBasisPhase ClassicalReversibleStage
open NativeConcreteP18QSPWitness

def program {index : Type*} {n : Nat}
    (rows : List index) (basis : index → QubitBasis n) :
    List (List (Fin (n + (n + 1)) × Bool)) :=
  rows.map fun row => placedPatternControls (standardImagePhasePlacement n) (basis row)

def circuit {index : Type*} {n : Nat}
    (rows : List index) (basis : index → QubitBasis n) (angle : AngleExpr) :
    Circuit (PrimitiveGate (n + (n + 1))) :=
  booleanProgramPhaseCircuitExpr (program rows basis)
    (standardImagePhaseScratches n) (standardImagePhaseFlag n) angle

theorem parity {index : Type*} [Fintype index] [DecidableEq index] {n : Nat}
    (rows : List index) (nodup : rows.Nodup) (complete : ∀ row, row ∈ rows)
    (embedding : index ↪ QubitBasis n) (input : QubitBasis (n + (n + 1))) :
    boolControlProgramParity (program rows embedding) input =
      decide (∃ row, restrictToPlacedWires (standardImagePhasePlacement n) input =
        embedding row) := by
  classical
  rw [boolControlProgramParity_eq_boolListParity]
  have values : (program rows embedding).map
      (fun controls => ClassicalReversibleStage.boolControlsSatisfied controls input) =
      rows.map (fun row => decide
        (restrictToPlacedWires (standardImagePhasePlacement n) input = embedding row)) := by
    simp only [program, List.map_map]
    apply List.map_congr_left
    intro row _
    exact boolControlsSatisfied_placedPatternControls _ _ _
  rw [values, boolListParity_decide_image embedding rows nodup]
  simp only [complete, true_and]

theorem enoughScratch {index : Type*} {n : Nat}
    (rows : List index) (basis : index → QubitBasis n)
    {controls : List (Fin (n + (n + 1)) × Bool)}
    (member : controls ∈ program rows basis) :
    controls.length ≤ (standardImagePhaseScratches n).length + 1 := by
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
  simp [placedPatternControls, standardImagePhaseScratches_length]

theorem layoutNodup {index : Type*} {n : Nat}
    (rows : List index) (basis : index → QubitBasis n)
    {controls : List (Fin (n + (n + 1)) × Bool)}
    (member : controls ∈ program rows basis) :
    (controls.map Prod.fst ++ standardImagePhaseScratches n ++
      [standardImagePhaseFlag n]).Nodup := by
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
  exact placedPatternControls_layout_nodup
    (standardImagePhasePlacement n) (basis row)
    (standardImagePhaseScratches n) (standardImagePhaseScratches_nodup n)
    (standardImagePhaseScratches_outside n) (standardImagePhaseFlag n)
    (standardImagePhaseFlag_outside_scratches n) (standardImagePhaseFlag_outside n)

theorem apply_clean_basis {index : Type*} [Fintype index] [DecidableEq index] {n : Nat}
    (rows : List index) (nodup : rows.Nodup) (complete : ∀ row, row ∈ rows)
    (embedding : index ↪ QubitBasis n) (angle : AngleExpr)
    (symbolValue : String → ℝ) (input : QubitBasis n) :
    applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (circuit rows embedding angle))
      (basisKet (fixedOutsideBasisEmbedding (standardImagePhasePlacement n)
        (fun _ => false) input)) =
    applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (standardEmbeddingImagePhaseCircuit embedding (angle.eval symbolValue)))
      (basisKet (fixedOutsideBasisEmbedding (standardImagePhasePlacement n)
        (fun _ => false) input)) := by
  classical
  rw [standardEmbeddingImagePhaseCircuit_apply_clean_basisKet_of_input]
  unfold circuit
  rw [booleanProgramPhaseCircuitExpr_denote]
  rw [booleanProgramPhaseCircuit_apply_basisKet symbolValue
    (program rows embedding) (standardImagePhaseScratches n) (standardImagePhaseFlag n)
    (angle.eval symbolValue)
    (fixedOutsideBasisEmbedding (standardImagePhasePlacement n) (fun _ => false) input)
    (fun _ member => enoughScratch rows embedding member)
    (fun _ member => layoutNodup rows embedding member)
    (standardImagePhaseFlag_outside_scratches n)
    (fun wire member => fixedOutsideBasisEmbedding_zero_apply_outside
      (standardImagePhasePlacement n) input wire
      (fun source => standardImagePhaseScratches_outside n wire member source))
    (fixedOutsideBasisEmbedding_zero_apply_outside
      (standardImagePhasePlacement n) input (standardImagePhaseFlag n)
      (standardImagePhaseFlag_outside n))]
  rw [parity rows nodup complete embedding]
  simp [fixedOutsideBasisEmbedding]

theorem apply_clean_state {index : Type*} [Fintype index] [DecidableEq index] {n : Nat}
    (rows : List index) (nodup : rows.Nodup) (complete : ∀ row, row ∈ rows)
    (embedding : index ↪ QubitBasis n) (angle : AngleExpr)
    (symbolValue : String → ℝ) (state : State (QubitBasis n)) :
    applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (circuit rows embedding angle))
      (fixedOutsideStateEmbedding (standardImagePhasePlacement n) (fun _ => false) state) =
    applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (standardEmbeddingImagePhaseCircuit embedding (angle.eval symbolValue)))
      (fixedOutsideStateEmbedding (standardImagePhasePlacement n) (fun _ => false) state) := by
  classical
  rw [state_eq_sum_smul_basisKet119 state, fixedOutsideStateEmbedding_finset_sum119,
    applyOperator_finset_sum119, applyOperator_finset_sum119]
  apply Finset.sum_congr rfl
  intro input _
  rw [fixedOutsideStateEmbedding_smul119, applyOperator_smul, applyOperator_smul]
  rw [fixedOutsideStateEmbedding_basisKet]
  rw [apply_clean_basis rows nodup complete embedding angle symbolValue input]

/-- Relabeling a complete logical enumeration changes no selected image.
The physical clean-state statement avoids assuming equality on dirty work
registers, which neither construction needs. -/
theorem apply_clean_state_reindex
    {index target : Type*} [Fintype index] [DecidableEq index]
    [Fintype target] [DecidableEq target] {n : Nat}
    (rows : List index) (nodup : rows.Nodup) (complete : ∀ row, row ∈ rows)
    (rename : index ≃ target) (embedding : target ↪ QubitBasis n)
    (angle : AngleExpr) (symbolValue : String → ℝ) (state : State (QubitBasis n)) :
    applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (circuit rows (fun row => embedding (rename row)) angle))
      (fixedOutsideStateEmbedding (standardImagePhasePlacement n) (fun _ => false) state) =
    fixedOutsideStateEmbedding (standardImagePhasePlacement n) (fun _ => false)
      (applyOperator (sourceImagePhaseOperator embedding (angle.eval symbolValue)) state) := by
  classical
  let combined := rename.toEmbedding.trans embedding
  have action := apply_clean_state rows nodup complete combined angle symbolValue state
  rw [standardEmbeddingImagePhaseCircuit_apply_clean_fixedOutsideState] at action
  have sameImage : sourceImagePhaseOperator combined (angle.eval symbolValue) =
      sourceImagePhaseOperator embedding (angle.eval symbolValue) := by
    ext output input
    have same : (∃ row, input = combined row) ↔ ∃ row, input = embedding row := by
      constructor
      · rintro ⟨row, equal⟩
        exact ⟨rename row, equal⟩
      · rintro ⟨row, equal⟩
        refine ⟨rename.symm row, ?_⟩
        simpa [combined] using equal
    simp only [sourceImagePhaseOperator, same]
  rw [sameImage] at action
  exact action

section

local instance (priority := 2000) canonicalFinFintype (n : Nat) : Fintype (Fin n) :=
  Fin.fintype n

theorem apply_clean_state_of_reindex
    {index target : Type*} [Fintype index] [DecidableEq index]
    [Fintype target] [DecidableEq target] {n : Nat}
    (rows : List index) (nodup : rows.Nodup) (complete : ∀ row, row ∈ rows)
    (basis : index → QubitBasis n) (rename : index ≃ target)
    (embedding : target ↪ QubitBasis n)
    (same : ∀ row, basis row = embedding (rename row))
    (angle : AngleExpr) (symbolValue : String → ℝ) (state : State (QubitBasis n)) :
    applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (circuit rows basis angle))
      (fixedOutsideStateEmbedding (standardImagePhasePlacement n) (fun _ => false) state) =
    fixedOutsideStateEmbedding (standardImagePhasePlacement n) (fun _ => false)
      (applyOperator (sourceImagePhaseOperator embedding (angle.eval symbolValue)) state) := by
  rw [funext same]
  exact apply_clean_state_reindex rows nodup complete rename embedding angle symbolValue state

end

end VerifiedCircuitCore.OrderedImagePhase
