import QLean.SignalProcessing.RootExactBasisPhase
import QLean.Circuits.Foundation.WireEmbeddingAnalytic
import QLean.SignalProcessing.NativeSignalQSVTActual
import QLean.SignalProcessing.KernelQSPGeneralQSPIntegration

/-!
# Exact phase on the image of a finite computational-basis embedding

The construction enumerates the finite logical image, computes membership
with reversible Boolean controls, applies an arbitrary exact real phase, and
uncomputes every ancilla.  Its theorem is stated on the fixed external block
used by a widened physical circuit.
-/

namespace VerifiedCircuitCore

noncomputable section

namespace NativeEmbeddingImagePhase

open ClassicalReversibleStage
open NativeExactBasisPhase

/-- Full source-register pattern, placed injectively in a wider register. -/
def placedPatternControls {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (pattern : QubitBasis sourceQubits) :
    List (Fin targetQubits × Bool) :=
  List.ofFn fun wire => (placement wire, pattern wire)

/-- A placed complete pattern tests exactly the restricted source basis. -/
theorem boolControlsSatisfied_placedPatternControls
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (pattern : QubitBasis sourceQubits)
    (input : QubitBasis targetQubits) :
    ClassicalReversibleStage.boolControlsSatisfied
        (placedPatternControls placement pattern) input =
      decide (restrictToPlacedWires placement input = pattern) := by
  classical
  unfold ClassicalReversibleStage.boolControlsSatisfied
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro allMatch
    funext wire
    have member :
        (placement wire, pattern wire) ∈ placedPatternControls placement pattern := by
      exact List.mem_ofFn.mpr ⟨wire, rfl⟩
    have matchAt := (List.all_eq_true.mp allMatch) _ member
    exact of_decide_eq_true matchAt
  · intro equal
    rw [List.all_eq_true]
    intro entry member
    rcases List.mem_ofFn.mp member with ⟨wire, rfl⟩
    exact decide_eq_true (congrFun equal wire)

/-- Parity of equality tests along a duplicate-free injective list is exactly
existence of a matching image point. -/
theorem boolListParity_decide_image
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (embedding : β ↪ γ) (indices : List β) (indicesNodup : indices.Nodup)
    (value : γ) :
    boolListParity (indices.map fun index => decide (value = embedding index)) =
      decide (∃ index ∈ indices, value = embedding index) := by
  induction indices with
  | nil => simp [boolListParity]
  | cons head tail inductionHypothesis =>
      have headOutside : head ∉ tail := (List.nodup_cons.mp indicesNodup).1
      have tailNodup : tail.Nodup := (List.nodup_cons.mp indicesNodup).2
      simp only [List.map_cons, boolListParity]
      rw [inductionHypothesis tailNodup]
      by_cases headEqual : value = embedding head
      · have noTail : ¬ ∃ index ∈ tail, value = embedding index := by
          rintro ⟨index, member, indexEqual⟩
          have equalIndex : head = index :=
            embedding.injective (headEqual.symm.trans indexEqual)
          subst index
          exact headOutside member
        simpa [headEqual, noTail] using headOutside
      · simp [headEqual]

/-- Source-order Boolean program enumerating every logical basis image. -/
def embeddingImageProgram {β : Type*} [Fintype β] [DecidableEq β]
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (embedding : β ↪ QubitBasis sourceQubits) :
    List (List (Fin targetQubits × Bool)) :=
  Finset.univ.toList.map fun index =>
    placedPatternControls placement (embedding index)

/-- The reversible program parity is precisely membership in the finite
logical image after restricting to the placed source wires. -/
theorem embeddingImageProgram_parity
    {β : Type*} [Fintype β] [DecidableEq β]
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (embedding : β ↪ QubitBasis sourceQubits)
    (input : QubitBasis targetQubits) :
    boolControlProgramParity (embeddingImageProgram placement embedding) input =
      decide (∃ index : β,
        restrictToPlacedWires placement input = embedding index) := by
  classical
  rw [boolControlProgramParity_eq_boolListParity]
  let indices : List β := Finset.univ.toList
  have rowValues :
      (embeddingImageProgram placement embedding).map
          (fun controls =>
            ClassicalReversibleStage.boolControlsSatisfied controls input) =
        indices.map (fun index =>
          decide (restrictToPlacedWires placement input = embedding index)) := by
    unfold embeddingImageProgram indices
    simp only [List.map_map]
    apply List.map_congr_left
    intro index member
    exact boolControlsSatisfied_placedPatternControls placement
      (embedding index) input
  rw [rowValues]
  rw [boolListParity_decide_image embedding indices Finset.univ.nodup_toList
    (restrictToPlacedWires placement input)]
  simp [indices]

/-- Exact primitive phase circuit for the image of a finite logical basis
embedding, in a widened register. -/
def embeddingImagePhaseCircuit
    {β : Type*} [Fintype β] [DecidableEq β]
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (embedding : β ↪ QubitBasis sourceQubits)
    (scratches : List (Fin targetQubits)) (flag : Fin targetQubits)
    (angle : ℝ) : Circuit (PrimitiveGate targetQubits) :=
  booleanProgramPhaseCircuit (embeddingImageProgram placement embedding)
    scratches flag angle

/-- On the clean added-ancilla block, the circuit applies `exp(i*angle)`
exactly to source computational basis strings in the range of `embedding`,
and restores every added ancilla. -/
theorem embeddingImagePhaseCircuit_apply_basisKet
    {β : Type*} [Fintype β] [DecidableEq β]
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (embedding : β ↪ QubitBasis sourceQubits)
    (scratches : List (Fin targetQubits)) (flag : Fin targetQubits)
    (angle : ℝ) (input : QubitBasis targetQubits)
    (enoughScratch : ∀ controls ∈ embeddingImageProgram placement embedding,
      controls.length ≤ scratches.length + 1)
    (layoutNodup : ∀ controls ∈ embeddingImageProgram placement embedding,
      (controls.map Prod.fst ++ scratches ++ [flag]).Nodup)
    (flagOutsideScratch : flag ∉ scratches)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (flagZero : input flag = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (embeddingImagePhaseCircuit placement embedding scratches flag angle))
        (basisKet input) =
      (if ∃ index : β,
          restrictToPlacedWires placement input = embedding index then
        Complex.exp (Complex.I * (angle : ℂ)) else 1) • basisKet input := by
  rw [embeddingImagePhaseCircuit]
  rw [booleanProgramPhaseCircuit_apply_basisKet symbolValue
    (embeddingImageProgram placement embedding) scratches flag angle input
    enoughScratch layoutNodup flagOutsideScratch scratchZero flagZero]
  rw [embeddingImageProgram_parity placement embedding input]
  by_cases member : ∃ index : β,
      restrictToPlacedWires placement input = embedding index <;> simp [member]

/-- Independent ideal operator: an exact phase on the span of the listed
computational basis image and identity on every other source basis state. -/
def sourceImagePhaseOperator
    {β : Type*} [Fintype β] [DecidableEq β]
    {sourceQubits : Nat}
    (embedding : β ↪ QubitBasis sourceQubits) (angle : ℝ) :
    Operator (QubitBasis sourceQubits) :=
  fun output input =>
    if output = input then
      if ∃ index : β, input = embedding index then
        Complex.exp (Complex.I * (angle : ℂ))
      else 1
    else 0

/-- The standard outside-zero basis embedding has zero on every wire outside
the placed source register. -/
theorem fixedOutsideBasisEmbedding_zero_apply_outside
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (input : QubitBasis sourceQubits) (wire : Fin targetQubits)
    (outside : ∀ source, placement source ≠ wire) :
    fixedOutsideBasisEmbedding placement (fun _ => false) input wire = false := by
  simp [fixedOutsideBasisEmbedding, mergePlacedAndOutsideBasis, outside]

end NativeEmbeddingImagePhase

end

end VerifiedCircuitCore
