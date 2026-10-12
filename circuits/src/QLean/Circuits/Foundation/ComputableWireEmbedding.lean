import QLean.Circuits.Foundation.ComputableRegisterWrite
import QLean.Circuits.Foundation.WireEmbeddingAnalytic

/-!
Executable wire embedding by finite inverse lookup.  The analytic embedding
used `Classical.choose` to invert an injective placement at each target wire.
The finite version searches the typed source wires and is pointwise equal to
that established semantics.  No circuit-correctness premise is introduced.
-/

set_option autoImplicit false
set_option warningAsError true

namespace VerifiedCircuitCore

private def placementRegister {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits) :
    Register targetQubits sourceQubits where
  wire := placement
  injective := placement.injective

/-- Finite inverse lookup for a typed injective wire placement. -/
def finitePlacementLookup {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (wire : Fin targetQubits) : Option (Fin sourceQubits) :=
  registerWireLookup (placementRegister placement) wire

theorem finitePlacementLookup_some_correct {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (wire : Fin targetQubits) (source : Fin sourceQubits)
    (found : finitePlacementLookup placement wire = some source) :
    placement source = wire :=
  registerWireLookup_some_correct (placementRegister placement) wire source found

theorem finitePlacementLookup_none_iff {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (wire : Fin targetQubits) :
    finitePlacementLookup placement wire = none ↔
      ¬ ∃ source, placement source = wire :=
  registerWireLookup_none_iff (placementRegister placement) wire

/-- Executable merge with a total, finitely evaluable target-wire basis. -/
def finiteMergePlacedAndOutsideBasis {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (internal : QubitBasis sourceQubits)
    (outside : QubitBasis targetQubits) : QubitBasis targetQubits :=
  writeRegisterBitsFinite (placementRegister placement) internal outside

theorem finiteMergePlacedAndOutsideBasis_eq
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (internal : QubitBasis sourceQubits)
    (outside : QubitBasis targetQubits) :
    finiteMergePlacedAndOutsideBasis placement internal outside =
      mergePlacedAndOutsideBasis placement internal
        (fun wire => outside wire.1) := by
  rw [finiteMergePlacedAndOutsideBasis, writeRegisterBitsFinite_eq]
  funext wire
  by_cases existsSource : ∃ source, placement source = wire
  · simp only [writeRegisterBits, placementRegister,
      mergePlacedAndOutsideBasis, dif_pos existsSource]
  · simp only [writeRegisterBits, placementRegister,
      mergePlacedAndOutsideBasis, dif_neg existsSource]

/-- An executable embedding with exactly the analytic fixed-outside basis. -/
def finiteFixedOutsideBasisEmbedding {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : QubitBasis targetQubits) :
    QubitBasis sourceQubits ↪ QubitBasis targetQubits where
  toFun internal := finiteMergePlacedAndOutsideBasis placement internal outside
  inj' := by
    intro left right equal
    simp only [finiteMergePlacedAndOutsideBasis_eq] at equal
    apply (fixedOutsideBasisEmbedding placement
      (fun wire => outside wire.1)).injective
    exact equal

theorem finiteFixedOutsideBasisEmbedding_eq
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : QubitBasis targetQubits) :
    finiteFixedOutsideBasisEmbedding placement outside =
      fixedOutsideBasisEmbedding placement (fun wire => outside wire.1) := by
  apply Function.Embedding.ext
  intro internal
  exact finiteMergePlacedAndOutsideBasis_eq placement internal outside

end VerifiedCircuitCore
