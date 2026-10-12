import QLean.Circuits.Foundation.ControlledConstantAdderAnalytic

/-!
Computable register write.  The original analytic definition selected an
inverse wire with `Classical.choose`; the finite search below computes the
unique matching register index and is proved pointwise identical.  This is a
general circuit foundation, not a new scientific target or caller premise.
-/

set_option autoImplicit false
set_option warningAsError true

namespace VerifiedCircuitCore

def registerWireLookupList {qubits width : Nat}
    (register : Register qubits width) (wire : Fin qubits) :
    List (Fin width) → Option (Fin width)
  | [] => none
  | index :: rest =>
      if register.wire index = wire then some index
      else registerWireLookupList register wire rest

theorem registerWireLookupList_some_correct {qubits width : Nat}
    (register : Register qubits width) (wire : Fin qubits)
    (indices : List (Fin width)) (index : Fin width)
    (found : registerWireLookupList register wire indices = some index) :
    register.wire index = wire := by
  induction indices with
  | nil => simp [registerWireLookupList] at found
  | cons head rest inductionHypothesis =>
      by_cases headMatches : register.wire head = wire
      · have same : head = index := Option.some.inj (by
          simpa [registerWireLookupList, headMatches] using found)
        exact same ▸ headMatches
      · have tailFound :
            registerWireLookupList register wire rest = some index := by
          simpa [registerWireLookupList, headMatches] using found
        exact inductionHypothesis tailFound

theorem registerWireLookupList_none_excludes {qubits width : Nat}
    (register : Register qubits width) (wire : Fin qubits)
    (indices : List (Fin width))
    (missing : registerWireLookupList register wire indices = none) :
    ∀ index ∈ indices, register.wire index ≠ wire := by
  induction indices with
  | nil => simp
  | cons head rest inductionHypothesis =>
      have headMissing : register.wire head ≠ wire := by
        intro equal
        simp [registerWireLookupList, equal] at missing
      have tailMissing : registerWireLookupList register wire rest = none := by
        simpa [registerWireLookupList, headMissing] using missing
      intro index member
      rcases List.mem_cons.mp member with same | inRest
      · exact same ▸ headMissing
      · exact inductionHypothesis tailMissing index inRest

/-- Search all typed register positions for a physical wire. -/
def registerWireLookup {qubits width : Nat}
    (register : Register qubits width) (wire : Fin qubits) :
    Option (Fin width) :=
  registerWireLookupList register wire (List.finRange width)

theorem registerWireLookup_some_correct {qubits width : Nat}
    (register : Register qubits width) (wire : Fin qubits)
    (index : Fin width)
    (found : registerWireLookup register wire = some index) :
    register.wire index = wire :=
  registerWireLookupList_some_correct register wire _ index found

theorem registerWireLookup_none_iff {qubits width : Nat}
    (register : Register qubits width) (wire : Fin qubits) :
    registerWireLookup register wire = none ↔
      ¬ ∃ index, register.wire index = wire := by
  constructor
  · intro missing ⟨index, equal⟩
    have unequal := registerWireLookupList_none_excludes
      register wire (List.finRange width) missing index (by simp)
    exact unequal equal
  · intro noMatch
    cases found : registerWireLookup register wire with
    | none => rfl
    | some index =>
        exact False.elim (noMatch ⟨index,
          registerWireLookup_some_correct register wire index found⟩)

/-- Executable counterpart of `writeRegisterBits`. -/
def writeRegisterBitsFinite {qubits width : Nat}
    (register : Register qubits width) (bits : QubitBasis width)
    (input : QubitBasis qubits) : QubitBasis qubits := fun wire =>
  match registerWireLookup register wire with
  | some index => bits index
  | none => input wire

theorem writeRegisterBitsFinite_eq {qubits width : Nat}
    (register : Register qubits width) (bits : QubitBasis width)
    (input : QubitBasis qubits) :
    writeRegisterBitsFinite register bits input =
      writeRegisterBits register bits input := by
  funext wire
  by_cases existsIndex : ∃ index, register.wire index = wire
  · cases lookup : registerWireLookup register wire with
    | none =>
        exact False.elim ((registerWireLookup_none_iff register wire).mp
          lookup existsIndex)
    | some selected =>
        have selectedMatches := registerWireLookup_some_correct
          register wire selected lookup
        have sameIndex : selected = Classical.choose existsIndex :=
          register.injective
            (selectedMatches.trans (Classical.choose_spec existsIndex).symm)
        simp only [writeRegisterBitsFinite, lookup, writeRegisterBits,
          dif_pos existsIndex]
        rw [sameIndex]
  · have lookupNone := (registerWireLookup_none_iff register wire).mpr
      existsIndex
    simp [writeRegisterBitsFinite, lookupNone, writeRegisterBits, existsIndex]

/-- A finite register write is stable under a proved renumbering of the
ambient qubit width, provided every register wire and the prior basis agree. -/
theorem writeRegisterBitsFinite_transport
    {leftQubits rightQubits leftWidth rightWidth : Nat}
    (sameQubits : leftQubits = rightQubits)
    (sameWidth : leftWidth = rightWidth)
    (left : Register leftQubits leftWidth)
    (right : Register rightQubits rightWidth)
    (sameWires : ∀ index,
      Fin.cast sameQubits (left.wire index) =
        right.wire (Fin.cast sameWidth index))
    (leftBits : QubitBasis leftWidth)
    (rightBits : QubitBasis rightWidth)
    (sameBits : ∀ index,
      leftBits (Fin.cast sameWidth.symm index) = rightBits index)
    (leftInput : QubitBasis leftQubits)
    (rightInput : QubitBasis rightQubits)
    (sameInput : ∀ wire,
      leftInput (Fin.cast sameQubits.symm wire) = rightInput wire)
    (wire : Fin rightQubits) :
    writeRegisterBitsFinite left leftBits leftInput
        (Fin.cast sameQubits.symm wire) =
      writeRegisterBitsFinite right rightBits rightInput wire := by
  cases sameQubits
  cases sameWidth
  have registerEq : left = right := by
    cases left with
    | mk leftWire leftInjective =>
      cases right with
      | mk rightWire rightInjective =>
        have wireEq : leftWire = rightWire := by
          funext index
          exact sameWires index
        subst rightWire
        rfl
  have inputEq : leftInput = rightInput := by
    funext index
    exact sameInput index
  have bitsEq : leftBits = rightBits := by
    funext index
    exact sameBits index
  subst right
  subst rightInput
  subst rightBits
  rfl

end VerifiedCircuitCore
