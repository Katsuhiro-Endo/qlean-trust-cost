import QLean.SignalProcessing.RootPlacedEmbeddingImagePhase

/-!
# A concrete clean layout for finite-image projector phases

The original register occupies the first `n` wires.  A second block of `n`
clean wires supplies reversible work, and the final clean wire is the phase
flag.  This removes the remaining caller-supplied layout existence premise
from the exact image-phase construction.
-/

namespace VerifiedCircuitCore

noncomputable section

namespace NativeEmbeddingImagePhase

/-- First-block placement into `n + (n + 1)` wires. -/
def standardImagePhasePlacement (n : Nat) : Fin n ↪ Fin (n + (n + 1)) where
  toFun := Fin.castAdd (n + 1)
  inj' := by
    intro left right equal
    exact Fin.castAdd_injective n (n + 1) equal

/-- The `n` reversible work wires in the second block. -/
def standardImagePhaseScratchWire (n : Nat) (wire : Fin n) :
    Fin (n + (n + 1)) :=
  Fin.natAdd n (Fin.castSucc wire)

def standardImagePhaseScratches (n : Nat) :
    List (Fin (n + (n + 1))) :=
  List.ofFn (standardImagePhaseScratchWire n)

/-- The final wire is a clean phase flag. -/
def standardImagePhaseFlag (n : Nat) : Fin (n + (n + 1)) :=
  Fin.natAdd n (Fin.last n)

theorem standardImagePhaseScratches_length (n : Nat) :
    (standardImagePhaseScratches n).length = n := by
  simp [standardImagePhaseScratches]

theorem standardImagePhaseScratches_nodup (n : Nat) :
    (standardImagePhaseScratches n).Nodup := by
  rw [standardImagePhaseScratches]
  apply List.nodup_ofFn.mpr
  intro left right equal
  have values := congrArg Fin.val equal
  simp [standardImagePhaseScratchWire] at values
  exact Fin.ext values

theorem standardImagePhaseFlag_outside_scratches (n : Nat) :
    standardImagePhaseFlag n ∉ standardImagePhaseScratches n := by
  intro member
  rw [standardImagePhaseScratches] at member
  rcases List.mem_ofFn.mp member with ⟨index, equal⟩
  have values := congrArg Fin.val equal
  simp [standardImagePhaseFlag, standardImagePhaseScratchWire] at values
  omega

theorem standardImagePhaseScratches_outside (n : Nat)
    (wire : Fin (n + (n + 1))) (member : wire ∈ standardImagePhaseScratches n)
    (source : Fin n) : standardImagePhasePlacement n source ≠ wire := by
  rw [standardImagePhaseScratches] at member
  rcases List.mem_ofFn.mp member with ⟨index, rfl⟩
  intro equal
  have values := congrArg Fin.val equal
  simp [standardImagePhasePlacement, standardImagePhaseScratchWire] at values
  omega

theorem standardImagePhaseFlag_outside (n : Nat) (source : Fin n) :
    standardImagePhasePlacement n source ≠ standardImagePhaseFlag n := by
  intro equal
  have values := congrArg Fin.val equal
  simp [standardImagePhasePlacement, standardImagePhaseFlag] at values
  omega

theorem placedPatternControls_wires_nodup
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (pattern : QubitBasis sourceQubits) :
    ((placedPatternControls placement pattern).map Prod.fst).Nodup := by
  rw [placedPatternControls, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right equal
  exact placement.injective equal

theorem placedPatternControls_layout_nodup
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (pattern : QubitBasis sourceQubits)
    (scratches : List (Fin targetQubits))
    (scratchesNodup : scratches.Nodup)
    (scratchesOutside : ∀ wire ∈ scratches, ∀ source, placement source ≠ wire)
    (flag : Fin targetQubits)
    (flagOutsideScratch : flag ∉ scratches)
    (flagOutside : ∀ source, placement source ≠ flag) :
    ((placedPatternControls placement pattern).map Prod.fst ++
      scratches ++ [flag]).Nodup := by
  rw [List.append_assoc]
  apply List.nodup_append.mpr
  refine ⟨placedPatternControls_wires_nodup placement pattern, ?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨scratchesNodup, by simp, ?_⟩
    intro scratch scratchMember flagWire flagMember
    simp only [List.mem_singleton] at flagMember
    subst flagWire
    exact Ne.symm (by
      intro equal
      exact flagOutsideScratch (equal ▸ scratchMember))
  · intro control controlMember outside outsideMember equal
    rcases List.mem_map.mp controlMember with ⟨entry, entryMember, rfl⟩
    rcases List.mem_ofFn.mp entryMember with ⟨source, rfl⟩
    rcases List.mem_append.mp outsideMember with outsideMember | flagMember
    · exact scratchesOutside outside outsideMember source equal
    · simp only [List.mem_singleton] at flagMember
      exact flagOutside source (equal.trans flagMember)

theorem standardImagePhase_enoughScratch
    {β : Type*} [Fintype β] [DecidableEq β]
    {n : Nat} (embedding : β ↪ QubitBasis n)
    {controls : List (Fin (n + (n + 1)) × Bool)}
    (member : controls ∈
      embeddingImageProgram (standardImagePhasePlacement n) embedding) :
    controls.length ≤
      (standardImagePhaseScratches n).length + 1 := by
  rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
  simp [placedPatternControls, standardImagePhaseScratches_length]

theorem standardImagePhase_layoutNodup
    {β : Type*} [Fintype β] [DecidableEq β]
    {n : Nat} (embedding : β ↪ QubitBasis n)
    {controls : List (Fin (n + (n + 1)) × Bool)}
    (member : controls ∈
      embeddingImageProgram (standardImagePhasePlacement n) embedding) :
    (controls.map Prod.fst ++
      standardImagePhaseScratches n ++
      [standardImagePhaseFlag n]).Nodup := by
  rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
  exact placedPatternControls_layout_nodup
    (standardImagePhasePlacement n) (embedding index)
    (standardImagePhaseScratches n) (standardImagePhaseScratches_nodup n)
    (standardImagePhaseScratches_outside n) (standardImagePhaseFlag n)
    (standardImagePhaseFlag_outside_scratches n)
    (standardImagePhaseFlag_outside n)

/-- Fully instantiated exact image phase with no layout premises. -/
def standardEmbeddingImagePhaseCircuit
    {β : Type*} [Fintype β] [DecidableEq β] {n : Nat}
    (embedding : β ↪ QubitBasis n) (angle : ℝ) :
    Circuit (PrimitiveGate (n + (n + 1))) :=
  embeddingImagePhaseCircuit (standardImagePhasePlacement n) embedding
    (standardImagePhaseScratches n)
    (standardImagePhaseFlag n) angle

end NativeEmbeddingImagePhase

end

end VerifiedCircuitCore
