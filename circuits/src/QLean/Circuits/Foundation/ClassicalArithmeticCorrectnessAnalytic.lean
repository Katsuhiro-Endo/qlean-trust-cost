import QLean.Circuits.Foundation.EqualityBranchLessThanAnalytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkMultiControlledXCorrectnessAnalytic

/-!
# Clean basis semantics for reversible little-endian arithmetic

This module isolates the width-generic mathematical facts used by the
building-block specifications.  It contains no gate-stream semantics.  The
recorded classical stages are related directly to independent basis actions.

The most important boundary is the controlled modular increment: on clean,
disjoint work it increments a little-endian word iff the external control is
true and restores every scratch wire.  No representative width is used.
-/

namespace VerifiedCircuitCore

namespace ClassicalReversibleStage

/-- Source-ordered X action on a list of distinct wires. -/
def flipListedWires {qubits : Nat} (wires : List (Fin qubits))
    (input : QubitBasis qubits) : QubitBasis qubits :=
  wires.foldl (fun state wire => xorWire wire true state) input

/-- A source-ordered list of X instructions realizes `flipListedWires`. -/
theorem sequenceXorOne_reference_apply {qubits : Nat}
    (wires : List (Fin qubits)) (input : QubitBasis qubits) :
    (sequence (wires.map fun wire => .instruction (.xorOne wire))).reference
        input = flipListedWires wires input := by
  rw [sequence_reference_apply]
  induction wires generalizing input with
  | nil => rfl
  | cons wire wires inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons]
      change (wires.map fun wire =>
          ClassicalReversibleStage.instruction
            (ClassicalReversibleInstruction.xorOne wire)).foldl
          (fun state (stage : ClassicalReversibleStage qubits) =>
            stage.reference state)
          (xorWire wire true input) = _
      rw [inductionHypothesis]
      rfl

/-- Independent basis action of a fixed-width constant mask. -/
def constantXorBasisAction {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  flipListedWires (constantXorWires register constant) input

/-- The source stage `xorConstant` realizes exactly the independent mask
action.  This theorem does not interpret the masked register as a natural
number; that requires a separate zero-input/range bridge. -/
theorem xorConstant_reference_apply {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat)
    (input : QubitBasis qubits) :
    (xorConstant register constant).reference input =
      constantXorBasisAction register constant input := by
  unfold xorConstant constantXorBasisAction
  exact sequenceXorOne_reference_apply
    (constantXorWires register constant) input

/-- On a duplicate-free list, a listed wire is complemented exactly once and
every outside wire is unchanged. -/
theorem flipListedWires_apply {qubits : Nat}
    (wires : List (Fin qubits)) (nodup : wires.Nodup)
    (input : QubitBasis qubits) (wire : Fin qubits) :
    flipListedWires wires input wire =
      if wire ∈ wires then !input wire else input wire := by
  induction wires generalizing input with
  | nil => simp [flipListedWires]
  | cons head tail inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rw [flipListedWires, List.foldl_cons]
      change flipListedWires tail (xorWire head true input) wire = _
      rw [inductionHypothesis tailNodup]
      by_cases equal : wire = head
      · subst wire
        simp [headFresh, xorWire]
      · simp [equal, xorWire]

theorem flipListedWires_commutes_xorWire {qubits : Nat}
    (wires : List (Fin qubits)) (wire : Fin qubits) (value : Bool)
    (input : QubitBasis qubits) (outside : wire ∉ wires) :
    flipListedWires wires (xorWire wire value input) =
      xorWire wire value (flipListedWires wires input) := by
  induction wires generalizing input with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have different : head ≠ wire := by
        intro equal
        apply outside
        simp [equal]
      have tailOutside : wire ∉ tail := by
        intro member
        apply outside
        simp [member]
      rw [flipListedWires, List.foldl_cons]
      change flipListedWires tail
          (xorWire head true (xorWire wire value input)) = _
      rw [xorWire_commute head wire different]
      exact inductionHypothesis (xorWire head true input) tailOutside

/-- A source-ordered X mask on distinct wires is self-inverse. -/
theorem flipListedWires_involutive {qubits : Nat}
    (wires : List (Fin qubits)) (nodup : wires.Nodup)
    (input : QubitBasis qubits) :
    flipListedWires wires (flipListedWires wires input) = input := by
  induction wires generalizing input with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rw [flipListedWires, List.foldl_cons]
      change flipListedWires tail
        (xorWire head true
          (flipListedWires tail (xorWire head true input))) = input
      rw [← flipListedWires_commutes_xorWire tail head true
        (xorWire head true input) headFresh]
      rw [inductionHypothesis tailNodup]
      exact xorWire_involutive head true input

/-- A fixed constant mask leaves every wire outside its declared register
unchanged.  This statement needs no duplicate-free premise. -/
theorem constantXorBasisAction_apply_outside {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : wire ∉ register) :
    constantXorBasisAction register constant input wire = input wire := by
  unfold constantXorBasisAction
  have selectedOutside : wire ∉ constantXorWires register constant := by
    intro member
    exact outside (constantXorWires_mem_register register constant wire member)
  have outsideLemma : ∀ selected : List (Fin qubits), wire ∉ selected →
      ∀ state : QubitBasis qubits,
        flipListedWires selected state wire = state wire := by
    intro selected
    induction selected with
    | nil => intro _ _; rfl
    | cons head tail inductionHypothesis =>
        intro selectedOutside state
        have headDifferent : head ≠ wire := by
          intro equal
          apply selectedOutside
          exact List.mem_cons.mpr (Or.inl equal.symm)
        have tailOutside : wire ∉ tail := by
          intro member
          exact selectedOutside (List.mem_cons_of_mem head member)
        rw [flipListedWires, List.foldl_cons]
        change flipListedWires tail (xorWire head true state) wire = state wire
        rw [inductionHypothesis tailOutside]
        exact xorWire_apply_other head wire headDifferent.symm true state
  exact outsideLemma (constantXorWires register constant) selectedOutside input

/-- Reading a register after masking it is exactly bitwise XOR with the
fixed-width little-endian bit list of the constant.  The register injection
prevents a selected wire from being toggled more than once. -/
theorem Register.read_constantXorBasisAction {qubits width : Nat}
    (register : Register qubits width) (constant : Nat)
    (input : QubitBasis qubits) :
    register.read
        (constantXorBasisAction (List.ofFn register.wire) constant input) =
      fun index => register.read input index != constant.testBit index.val := by
  funext index
  have selectedIff :
      register.wire index ∈
          constantXorWires (List.ofFn register.wire) constant ↔
        constant.testBit index.val = true := by
    constructor
    · intro member
      unfold constantXorWires at member
      rcases List.mem_filterMap.mp member with
        ⟨indexed, indexedMember, selected⟩
      by_cases bit : constant.testBit indexed.2
      · simp only [if_pos bit, Option.some.injEq] at selected
        have indexedFacts := List.mem_zipIdx' indexedMember
        have indexBound : indexed.2 < width := by
          simpa using indexedFacts.1
        have indexedWire :
            indexed.1 = register.wire ⟨indexed.2, indexBound⟩ := by
          simpa only [List.getElem_ofFn] using indexedFacts.2
        have sameWire :
            register.wire ⟨indexed.2, indexBound⟩ = register.wire index :=
          indexedWire.symm.trans selected
        have sameIndex : (⟨indexed.2, indexBound⟩ : Fin width) = index :=
          register.injective sameWire
        have sameNat : indexed.2 = index.val :=
          congrArg Fin.val sameIndex
        simpa [sameNat] using bit
      · simp only [if_neg bit] at selected
        contradiction
    · intro bit
      unfold constantXorWires
      apply List.mem_filterMap.mpr
      refine ⟨(register.wire index, index.val), ?_, ?_⟩
      · rw [List.mem_zipIdx_iff_getElem?]
        simp
      · simp [bit]
  unfold Register.read constantXorBasisAction
  rw [flipListedWires_apply]
  · rw [if_congr selectedIff rfl rfl]
    cases constant.testBit index.val <;>
      cases input (register.wire index) <;> rfl
  · exact constantXorWires_nodup (List.ofFn register.wire) constant
      (List.nodup_ofFn.mpr register.injective)

/-- On an all-zero register, the source-faithful constant mask prepares exactly
the fixed-width test-bit function of the natural number. -/
theorem Register.read_constantXorBasisAction_of_zero {qubits width : Nat}
    (register : Register qubits width) (constant : Nat)
    (input : QubitBasis qubits)
    (zero : ∀ index, register.read input index = false) :
    register.read
        (constantXorBasisAction (List.ofFn register.wire) constant input) =
      fun index => constant.testBit index.val := by
  rw [Register.read_constantXorBasisAction]
  funext index
  rw [zero index]
  cases constant.testBit index.val <;> rfl

/-- Independent carry-recursive action for a controlled little-endian
increment.  `lower` contains the already-inspected less-significant wires;
`higher` contains the targets still to be processed. -/
def controlledIncrementCarryReference {qubits : Nat}
    (control : Fin qubits) (lower : List (Fin qubits)) :
    List (Fin qubits) -> QubitBasis qubits -> QubitBasis qubits
  | [], input => input
  | target :: higher, input =>
      let higherState := controlledIncrementCarryReference control
        (lower ++ [target]) higher input
      xorWire target (allWiresTrue (control :: lower) higherState) higherState

/-- Independent full-word action of a controlled increment modulo the word
capacity. -/
def controlledIncrementWordReference {qubits : Nat}
    (control : Fin qubits) (word : List (Fin qubits))
    (input : QubitBasis qubits) : QubitBasis qubits :=
  controlledIncrementCarryReference control [] word input

/-- Carry-input Boolean increment in little-endian order. -/
def incrementBitsWithCarry : Bool -> List Bool -> List Bool
  | _, [] => []
  | carry, bit :: bits =>
      (if carry then !bit else bit) ::
        incrementBitsWithCarry (carry && bit) bits

/-- Ordinary fixed-width modular increment. -/
def incrementBits (bits : List Bool) : List Bool :=
  incrementBitsWithCarry true bits

@[simp] theorem incrementBitsWithCarry_false (bits : List Bool) :
    incrementBitsWithCarry false bits = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      simp [incrementBitsWithCarry, inductionHypothesis]

/-- The independent carry recursion changes no wire outside its target suffix. -/
theorem controlledIncrementCarryReference_outside {qubits : Nat}
    (control : Fin qubits) (lower higher : List (Fin qubits))
    (wire : Fin qubits) (input : QubitBasis qubits)
    (outside : wire ∉ higher) :
    controlledIncrementCarryReference control lower higher input wire =
      input wire := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      have wireDifferent : wire ≠ target := by
        intro equal
        apply outside
        simp [equal]
      have tailOutside : wire ∉ higher := by
        intro member
        apply outside
        simp [member]
      simp only [controlledIncrementCarryReference]
      let higherState := controlledIncrementCarryReference control
        (lower ++ [target]) higher input
      rw [xorWire_apply_other target wire wireDifferent]
      exact inductionHypothesis (lower ++ [target]) input tailOutside

/-- The independent carry action commutes with an XOR outside all of its read
and written wires. -/
theorem controlledIncrementCarryReference_commutes_xorWire {qubits : Nat}
    (control : Fin qubits) (lower higher : List (Fin qubits))
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (controlDifferent : wire ≠ control)
    (outsideLower : wire ∉ lower) (outsideHigher : wire ∉ higher) :
    controlledIncrementCarryReference control lower higher
        (xorWire wire value input) =
      xorWire wire value
        (controlledIncrementCarryReference control lower higher input) := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      have wireDifferentTarget : wire ≠ target := by
        intro equal
        apply outsideHigher
        simp [equal]
      have outsideTail : wire ∉ higher := by
        intro member
        apply outsideHigher
        simp [member]
      have outsideExtended : wire ∉ lower ++ [target] := by
        intro member
        rcases List.mem_append.mp member with lowerMember | targetMember
        · exact outsideLower lowerMember
        · have equal : wire = target := by simpa using targetMember
          exact wireDifferentTarget equal
      let leftHigher := controlledIncrementCarryReference control
        (lower ++ [target]) higher (xorWire wire value input)
      let rightHigher := controlledIncrementCarryReference control
        (lower ++ [target]) higher input
      have recursive : leftHigher = xorWire wire value rightHigher := by
        exact inductionHypothesis (lower ++ [target]) input outsideExtended
          outsideTail
      have controlsOutside : wire ∉ control :: lower := by
        simp [controlDifferent, outsideLower]
      have conditionEqual : allWiresTrue (control :: lower) leftHigher =
          allWiresTrue (control :: lower) rightHigher := by
        rw [recursive]
        unfold allWiresTrue
        rw [readWires_xorWire_of_not_mem _ _ _ _ controlsOutside]
      simp only [controlledIncrementCarryReference]
      change xorWire target (allWiresTrue (control :: lower) leftHigher)
          leftHigher = _
      rw [conditionEqual, recursive]
      exact xorWire_commute target wire (Ne.symm wireDifferentTarget)
        (allWiresTrue (control :: lower) rightHigher) value rightHigher

theorem controlledIncrementWordReference_commutes_xorWire {qubits : Nat}
    (control : Fin qubits) (word : List (Fin qubits))
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (controlDifferent : wire ≠ control) (outsideWord : wire ∉ word) :
    controlledIncrementWordReference control word (xorWire wire value input) =
      xorWire wire value (controlledIncrementWordReference control word input) := by
  exact controlledIncrementCarryReference_commutes_xorWire control [] word wire
    value input controlDifferent (by simp) outsideWord

/-- On a duplicate-free word, reading the independent controlled increment is
exactly the carry-input Boolean recurrence. -/
theorem readWires_controlledIncrementCarryReference {qubits : Nat}
    (control : Fin qubits) (lower higher : List (Fin qubits))
    (input : QubitBasis qubits)
    (layoutNodup : (control :: lower ++ higher).Nodup) :
    readWires higher
        (controlledIncrementCarryReference control lower higher input) =
      incrementBitsWithCarry
        (input control && allWiresTrue lower input)
        (readWires higher input) := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      have controlFresh := (List.nodup_cons.mp layoutNodup).1
      have lowerTargetTailNodup := (List.nodup_cons.mp layoutNodup).2
      have lowerNodup := (List.nodup_append.mp lowerTargetTailNodup).1
      have targetTailNodup := (List.nodup_append.mp lowerTargetTailNodup).2.1
      have lowerTailSeparated :=
        (List.nodup_append.mp lowerTargetTailNodup).2.2
      have targetFresh := (List.nodup_cons.mp targetTailNodup).1
      have recursiveLayout :
          (control :: (lower ++ [target]) ++ higher).Nodup := by
        have controlOutside : control ∉ (lower ++ [target]) ++ higher := by
          intro member
          apply controlFresh
          simpa [List.append_assoc] using member
        apply List.nodup_cons.mpr
        refine ⟨controlOutside, ?_⟩
        simpa [List.append_assoc] using lowerTargetTailNodup
      let higherState := controlledIncrementCarryReference control
        (lower ++ [target]) higher input
      have targetUnchanged : higherState target = input target := by
        exact controlledIncrementCarryReference_outside control
          (lower ++ [target]) higher target input targetFresh
      have controlUnchanged : higherState control = input control := by
        apply controlledIncrementCarryReference_outside control
          (lower ++ [target]) higher control input
        intro member
        apply controlFresh
        simp [member]
      have lowerUnchanged :
          readWires lower higherState = readWires lower input := by
        apply List.map_congr_left
        intro wire member
        apply controlledIncrementCarryReference_outside control
          (lower ++ [target]) higher wire input
        intro higherMember
        exact lowerTailSeparated wire member wire (by simp [higherMember]) rfl
      have conditionUnchanged :
          allWiresTrue (control :: lower) higherState =
            (input control && allWiresTrue lower input) := by
        unfold allWiresTrue readWires
        simp only [List.map_cons, List.all_cons, id_eq]
        rw [controlUnchanged]
        exact congrArg (fun value => input control && value)
          (by
            simpa [readWires] using congrArg (fun values => values.all id)
              lowerUnchanged)
      have tailResult : readWires higher higherState =
          incrementBitsWithCarry
            (input control && allWiresTrue (lower ++ [target]) input)
            (readWires higher input) := by
        exact inductionHypothesis (lower ++ [target]) input recursiveLayout
      have extendedCarry :
          allWiresTrue (lower ++ [target]) input =
            (allWiresTrue lower input && input target) := by
        simp [allWiresTrue, readWires, List.all_append]
      have targetUnchangedDirect :
          controlledIncrementCarryReference control (lower ++ [target])
              higher input target = input target := by
        exact targetUnchanged
      have tailResultDirect :
          readWires higher
              (controlledIncrementCarryReference control (lower ++ [target])
                higher input) =
            incrementBitsWithCarry
              (input control && allWiresTrue (lower ++ [target]) input)
              (readWires higher input) := by
        exact tailResult
      simp only [controlledIncrementCarryReference, readWires, List.map_cons]
      rw [conditionUnchanged]
      cases carryValue : input control && allWiresTrue lower input with
      | true =>
        simp only [if_true, incrementBitsWithCarry, Bool.true_and]
        congr 1
        · rw [xorWire_apply_same, targetUnchangedDirect]
          cases input target <;> rfl
        · change readWires higher
              (xorWire target true
                (controlledIncrementCarryReference control (lower ++ [target])
                  higher input)) = _
          rw [readWires_xorWire_of_not_mem higher target true
            (controlledIncrementCarryReference control (lower ++ [target])
              higher input) targetFresh]
          rw [tailResultDirect, extendedCarry]
          cases controlValue : input control <;>
            cases lowerValue : allWiresTrue lower input <;>
            simp [controlValue, lowerValue, readWires] at carryValue ⊢
      | false =>
        simp only [Bool.false_eq_true, if_false,
          incrementBitsWithCarry, Bool.false_and]
        congr 1
        · rw [xorWire_apply_same, targetUnchangedDirect]
          cases input target <;> rfl
        · change readWires higher
              (xorWire target false
                (controlledIncrementCarryReference control (lower ++ [target])
                  higher input)) = _
          rw [readWires_xorWire_of_not_mem higher target false
            (controlledIncrementCarryReference control (lower ++ [target])
              higher input) targetFresh]
          rw [tailResultDirect, extendedCarry]
          cases controlValue : input control <;>
            cases lowerValue : allWiresTrue lower input <;>
            simp [controlValue, lowerValue, readWires] at carryValue ⊢

/-- The recorded controlled-increment stage equals its independent basis
reference on clean, disjoint work. -/
theorem controlledIncrementCarrySequence_reference_apply_of_cleanWork
    {qubits : Nat}
    (control : Fin qubits) (lower higher scratches : List (Fin qubits))
    (input : QubitBasis qubits)
    (enoughScratch : (lower ++ higher).length ≤ scratches.length + 1)
    (layoutNodup : (control :: lower ++ higher ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (controlledIncrementCarrySequence control lower higher scratches).reference
        input =
      controlledIncrementCarryReference control lower higher input := by
  induction higher generalizing lower input with
  | nil => rfl
  | cons target higher inductionHypothesis =>
      have recursiveEnough :
          ((lower ++ [target]) ++ higher).length ≤ scratches.length + 1 := by
        simpa [List.length_append, Nat.add_assoc] using enoughScratch
      have recursiveLayout :
          (control :: (lower ++ [target]) ++ higher ++ scratches).Nodup := by
        simpa [List.append_assoc] using layoutNodup
      change (positiveMultiControlledX (control :: lower) scratches target).reference
        ((controlledIncrementCarrySequence control (lower ++ [target]) higher
          scratches).reference input) = _
      rw [inductionHypothesis (lower ++ [target]) input recursiveEnough
        recursiveLayout scratchZero]
      let higherState := controlledIncrementCarryReference control
        (lower ++ [target]) higher input
      have normalized :
          ((control :: lower ++ target :: higher) ++ scratches).Nodup := by
        simpa [List.append_assoc] using layoutNodup
      have targetScratchLayout :
          ((control :: lower) ++ scratches ++ [target]).Nodup := by
        have prefixNodup := (List.nodup_append.mp normalized).1
        have prefixScratchSeparated := (List.nodup_append.mp normalized).2.2
        have controlFresh := (List.nodup_cons.mp prefixNodup).1
        have restNodup := (List.nodup_cons.mp prefixNodup).2
        have lowerNodup := (List.nodup_append.mp restNodup).1
        have lowerSeparated := (List.nodup_append.mp restNodup).2.2
        have targetHigherNodup :=
          (List.nodup_append.mp restNodup).2.1
        have targetFresh :=
          (List.nodup_cons.mp targetHigherNodup).1
        have scratchesNodup := (List.nodup_append.mp normalized).2.1
        have controlsNodup : (control :: lower).Nodup := by
          apply List.nodup_cons.mpr
          refine ⟨?_, lowerNodup⟩
          intro member
          exact controlFresh (by simp [member])
        apply List.nodup_append.mpr
        refine ⟨?_, by simp, ?_⟩
        · apply List.nodup_append.mpr
          refine ⟨controlsNodup, scratchesNodup, ?_⟩
          intro controlWire controlMember scratchWire scratchMember
          rcases List.mem_cons.mp controlMember with rfl | lowerMember
          · exact prefixScratchSeparated controlWire (by simp)
              scratchWire scratchMember
          · exact prefixScratchSeparated controlWire
              (by simp [lowerMember]) scratchWire scratchMember
        · intro wire member finalTarget finalMember
          have finalTargetEq : finalTarget = target := by simpa using finalMember
          subst finalTarget
          rcases List.mem_append.mp member with controlMember | scratchMember
          · rcases List.mem_cons.mp controlMember with controlEq | lowerMember
            · intro wireEqTarget
              apply controlFresh
              rw [← controlEq, wireEqTarget]
              exact List.mem_append_right lower
                (List.mem_cons.mpr (Or.inl rfl))
            · exact lowerSeparated wire lowerMember target
                (List.mem_cons.mpr (Or.inl rfl))
          · exact (prefixScratchSeparated target
              (by
                exact List.mem_cons.mpr (Or.inr
                  (List.mem_append_right lower
                    (List.mem_cons.mpr (Or.inl rfl)))))
              wire scratchMember).symm
      have stageEnough : (control :: lower).length ≤ scratches.length + 1 := by
        simp only [List.length_cons, List.length_append] at enoughScratch ⊢
        omega
      have higherStateScratchZero : ∀ wire ∈ scratches,
          higherState wire = false := by
        intro wire scratchMember
        change controlledIncrementCarryReference control (lower ++ [target])
          higher input wire = false
        rw [controlledIncrementCarryReference_outside control
          (lower ++ [target]) higher wire input]
        · exact scratchZero wire scratchMember
        · intro higherMember
          have separated := (List.nodup_append.mp normalized).2.2
          exact separated wire
            (List.mem_append_right (control :: lower) (by simp [higherMember]))
            wire scratchMember rfl
      rw [positiveMultiControlledX_reference_apply_of_cleanWork
        (control :: lower) scratches target higherState stageEnough
        targetScratchLayout higherStateScratchZero]
      rfl

/-- The public full-word stage has the independent controlled increment action. -/
theorem controlledIncrementWordMod2PowInPlace_reference_apply_of_cleanWork
    {qubits : Nat}
    (control : Fin qubits) (word scratches : List (Fin qubits))
    (input : QubitBasis qubits)
    (enoughScratch : word.length ≤ scratches.length + 1)
    (layoutNodup : (control :: word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (controlledIncrementWordMod2PowInPlace control word scratches).reference
        input = controlledIncrementWordReference control word input := by
  apply controlledIncrementCarrySequence_reference_apply_of_cleanWork
  · simpa using enoughScratch
  · simpa using layoutNodup
  · exact scratchZero

/-- The controlled increment readout is the standard Boolean carry recurrence. -/
theorem readWires_controlledIncrementWordMod2PowInPlace_of_cleanWork
    {qubits : Nat}
    (control : Fin qubits) (word scratches : List (Fin qubits))
    (input : QubitBasis qubits)
    (enoughScratch : word.length ≤ scratches.length + 1)
    (layoutNodup : (control :: word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    readWires word
        ((controlledIncrementWordMod2PowInPlace control word scratches).reference
          input) =
      incrementBitsWithCarry (input control) (readWires word input) := by
  rw [controlledIncrementWordMod2PowInPlace_reference_apply_of_cleanWork
    control word scratches input enoughScratch layoutNodup scratchZero]
  simpa [controlledIncrementWordReference, allWiresTrue, readWires] using
    readWires_controlledIncrementCarryReference control [] word input
      (by
        have controlFresh := (List.nodup_cons.mp layoutNodup).1
        have wordNodup :=
          (List.nodup_append.mp (List.nodup_cons.mp layoutNodup).2).1
        apply List.nodup_cons.mpr
        refine ⟨?_, wordNodup⟩
        intro member
        exact controlFresh (List.mem_append_left scratches member))

/-- A clean controlled increment restores every scratch wire. -/
theorem controlledIncrementWordMod2PowInPlace_reference_scratch_zero
    {qubits : Nat}
    (control : Fin qubits) (word scratches : List (Fin qubits))
    (input : QubitBasis qubits)
    (enoughScratch : word.length ≤ scratches.length + 1)
    (layoutNodup : (control :: word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    ∀ wire ∈ scratches,
      (controlledIncrementWordMod2PowInPlace control word scratches).reference
          input wire = false := by
  intro wire member
  rw [controlledIncrementWordMod2PowInPlace_reference_apply_of_cleanWork
    control word scratches input enoughScratch layoutNodup scratchZero]
  unfold controlledIncrementWordReference
  rw [controlledIncrementCarryReference_outside control [] word wire input]
  · exact scratchZero wire member
  · intro wordMember
    have separated := (List.nodup_append.mp (List.nodup_cons.mp layoutNodup).2).2.2
    exact separated wire wordMember wire member rfl

/-- Apply a source-ordered list of control values to one modular counter. -/
def incrementBitsForControlValues : List Bool -> List Bool -> List Bool
  | [], bits => bits
  | control :: controls, bits =>
      incrementBitsForControlValues controls
        (incrementBitsWithCarry control bits)

/-- Number of true controls, defined independently of any register layout. -/
def boolTrueCount : List Bool -> Nat
  | [] => 0
  | value :: values => value.toNat + boolTrueCount values

theorem boolTrueCount_le_length (values : List Bool) :
    boolTrueCount values ≤ values.length := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      cases value <;> simp [boolTrueCount] <;> omega

theorem boolTrueCount_eq_length_iff_all_true (values : List Bool) :
    boolTrueCount values = values.length ↔ values.all id = true := by
  induction values with
  | nil => simp [boolTrueCount]
  | cons value values inductionHypothesis =>
      cases value with
      | false =>
          simp only [boolTrueCount, Bool.toNat_false, Nat.zero_add,
            List.length_cons, List.all_cons, id_eq, Bool.false_and,
            Bool.false_eq_true, iff_false]
          have bound := boolTrueCount_le_length values
          omega
      | true =>
          simp only [boolTrueCount, Bool.toNat_true, List.length_cons,
            List.all_cons, id_eq, Bool.true_and]
          constructor
          · intro equal
            apply inductionHypothesis.mp
            omega
          · intro allTrue
            have equal := inductionHypothesis.mpr allTrue
            omega

/-- Source-ordered controlled-increment program used by counter predicates. -/
def controlledIncrementProgram {qubits : Nat}
    (controls word scratches : List (Fin qubits)) :
    ClassicalReversibleStage qubits :=
  sequence <| controls.map fun control =>
    controlledIncrementWordMod2PowInPlace control word scratches

/-- Independent full-basis fold associated with a controlled-increment
program. -/
def controlledIncrementProgramReference {qubits : Nat}
    (controls word : List (Fin qubits)) (input : QubitBasis qubits) :
    QubitBasis qubits :=
  controls.foldl (fun state control =>
    controlledIncrementWordReference control word state) input

/-- A controlled increment changes no wire outside its counter word. -/
theorem controlledIncrementWordMod2PowInPlace_reference_apply_outside_word
    {qubits : Nat}
    (control : Fin qubits) (word scratches : List (Fin qubits))
    (input : QubitBasis qubits)
    (enoughScratch : word.length ≤ scratches.length + 1)
    (layoutNodup : (control :: word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (wire : Fin qubits) (outside : wire ∉ word) :
    (controlledIncrementWordMod2PowInPlace control word scratches).reference
        input wire = input wire := by
  rw [controlledIncrementWordMod2PowInPlace_reference_apply_of_cleanWork
    control word scratches input enoughScratch layoutNodup scratchZero]
  exact controlledIncrementCarryReference_outside control [] word wire input
    outside

/-- The recorded source-order program equals its independent fold on clean
work. -/
theorem controlledIncrementProgram_reference_apply_of_cleanWork {qubits : Nat}
    (controls word scratches : List (Fin qubits))
    (input : QubitBasis qubits)
    (enoughScratch : word.length ≤ scratches.length + 1)
    (layoutNodup : (controls ++ word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (controlledIncrementProgram controls word scratches).reference input =
      controlledIncrementProgramReference controls word input := by
  induction controls generalizing input with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp layoutNodup).1
      have tailLayout := (List.nodup_cons.mp layoutNodup).2
      have normalizedTail : (controls ++ (word ++ scratches)).Nodup := by
        simpa [List.append_assoc] using tailLayout
      have wordScratchNodup := (List.nodup_append.mp normalizedTail).2.1
      have headLayout : (control :: word ++ scratches).Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_, wordScratchNodup⟩
        intro member
        exact headFresh (by
          rcases List.mem_append.mp member with wordMember | scratchMember
          · simp [wordMember]
          · simp [scratchMember])
      let next := controlledIncrementWordReference control word input
      have stageResult :
          (controlledIncrementWordMod2PowInPlace control word scratches).reference
              input = next :=
        controlledIncrementWordMod2PowInPlace_reference_apply_of_cleanWork
          control word scratches input enoughScratch headLayout scratchZero
      have nextScratchZero : ∀ wire ∈ scratches, next wire = false := by
        intro wire member
        rw [← stageResult]
        exact controlledIncrementWordMod2PowInPlace_reference_scratch_zero
          control word scratches input enoughScratch headLayout scratchZero wire
          member
      change (controlledIncrementProgram controls word scratches).reference
          ((controlledIncrementWordMod2PowInPlace control word scratches).reference
            input) = _
      rw [stageResult]
      exact inductionHypothesis next tailLayout nextScratchZero

/-- On clean work, the whole counter program commutes with an XOR outside its
controls and counter word. -/
theorem controlledIncrementProgram_reference_commutes_xorWire_of_cleanWork
    {qubits : Nat}
    (controls word scratches : List (Fin qubits))
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (enoughScratch : word.length ≤ scratches.length + 1)
    (layoutNodup : (controls ++ word ++ scratches).Nodup)
    (scratchZero : ∀ scratch ∈ scratches, input scratch = false)
    (outsideControls : wire ∉ controls) (outsideWord : wire ∉ word)
    (outsideScratch : wire ∉ scratches) :
    (controlledIncrementProgram controls word scratches).reference
        (xorWire wire value input) =
      xorWire wire value
        ((controlledIncrementProgram controls word scratches).reference input) := by
  have scratchZeroAfterXor : ∀ scratch ∈ scratches,
      xorWire wire value input scratch = false := by
    intro scratch member
    rw [xorWire_apply_other wire scratch]
    · exact scratchZero scratch member
    · intro equal
      apply outsideScratch
      simpa [equal] using member
  rw [controlledIncrementProgram_reference_apply_of_cleanWork controls word
      scratches (xorWire wire value input) enoughScratch layoutNodup
      scratchZeroAfterXor,
    controlledIncrementProgram_reference_apply_of_cleanWork controls word
      scratches input enoughScratch layoutNodup scratchZero]
  unfold controlledIncrementProgramReference
  have foldCommutes : ∀ remaining : List (Fin qubits), wire ∉ remaining →
      ∀ state : QubitBasis qubits,
        remaining.foldl
            (fun current control =>
              controlledIncrementWordReference control word current)
            (xorWire wire value state) =
          xorWire wire value
            (remaining.foldl
              (fun current control =>
                controlledIncrementWordReference control word current)
              state) := by
    intro remaining outsideRemaining state
    induction remaining generalizing state with
    | nil => rfl
    | cons control remaining inductionHypothesis =>
        have wireDifferent : wire ≠ control := by
          intro equal
          exact outsideRemaining (List.mem_cons.mpr (Or.inl equal))
        have tailOutside : wire ∉ remaining := by
          intro member
          exact outsideRemaining (List.mem_cons_of_mem control member)
        simp only [List.foldl_cons]
        rw [controlledIncrementWordReference_commutes_xorWire control word wire
          value state wireDifferent outsideWord]
        exact inductionHypothesis tailOutside
          (controlledIncrementWordReference control word state)
  exact foldCommutes controls outsideControls input

/-- The source-ordered controlled-increment program reads as repeated Boolean
carry updates, and no hidden representative width is involved. -/
theorem readWires_controlledIncrementProgram_of_cleanWork {qubits : Nat}
    (controls word scratches : List (Fin qubits))
    (input : QubitBasis qubits)
    (enoughScratch : word.length ≤ scratches.length + 1)
    (layoutNodup : (controls ++ word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    readWires word
        ((controlledIncrementProgram controls word scratches).reference input) =
      incrementBitsForControlValues (readWires controls input)
        (readWires word input) := by
  induction controls generalizing input with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp layoutNodup).1
      have tailLayout := (List.nodup_cons.mp layoutNodup).2
      have normalizedTail : (controls ++ (word ++ scratches)).Nodup := by
        simpa [List.append_assoc] using tailLayout
      have wordScratchNodup := (List.nodup_append.mp normalizedTail).2.1
      have headLayout : (control :: word ++ scratches).Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_, wordScratchNodup⟩
        intro member
        exact headFresh (by
          rcases List.mem_append.mp member with wordMember | scratchMember
          · simp [wordMember]
          · simp [scratchMember])
      let next :=
        (controlledIncrementWordMod2PowInPlace control word scratches).reference
          input
      have nextScratchZero : ∀ wire ∈ scratches, next wire = false := by
        exact controlledIncrementWordMod2PowInPlace_reference_scratch_zero
          control word scratches input enoughScratch headLayout scratchZero
      have controlsUnchanged : readWires controls next = readWires controls input := by
        apply List.map_congr_left
        intro wire member
        apply controlledIncrementWordMod2PowInPlace_reference_apply_outside_word
          control word scratches input enoughScratch headLayout scratchZero
        intro wordMember
        have controlWordNodup := (List.nodup_append.mp tailLayout).1
        have separated := (List.nodup_append.mp controlWordNodup).2.2
        exact separated wire member wire wordMember rfl
      have wordUpdated : readWires word next =
          incrementBitsWithCarry (input control) (readWires word input) := by
        exact readWires_controlledIncrementWordMod2PowInPlace_of_cleanWork
          control word scratches input enoughScratch headLayout scratchZero
      change readWires word
          ((controlledIncrementProgram controls word scratches).reference next) = _
      rw [inductionHypothesis next tailLayout nextScratchZero]
      rw [controlsUnchanged, wordUpdated]
      rfl

/-- The whole counter program restores all arithmetic scratch. -/
theorem controlledIncrementProgram_reference_scratch_zero {qubits : Nat}
    (controls word scratches : List (Fin qubits))
    (input : QubitBasis qubits)
    (enoughScratch : word.length ≤ scratches.length + 1)
    (layoutNodup : (controls ++ word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    ∀ wire ∈ scratches,
      (controlledIncrementProgram controls word scratches).reference input wire =
        false := by
  induction controls generalizing input with
  | nil => exact scratchZero
  | cons control controls inductionHypothesis =>
      have headFresh := (List.nodup_cons.mp layoutNodup).1
      have tailLayout := (List.nodup_cons.mp layoutNodup).2
      have normalizedTail : (controls ++ (word ++ scratches)).Nodup := by
        simpa [List.append_assoc] using tailLayout
      have wordScratchNodup := (List.nodup_append.mp normalizedTail).2.1
      have headLayout : (control :: word ++ scratches).Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_, wordScratchNodup⟩
        intro member
        exact headFresh (by
          rcases List.mem_append.mp member with wordMember | scratchMember
          · simp [wordMember]
          · simp [scratchMember])
      let next :=
        (controlledIncrementWordMod2PowInPlace control word scratches).reference
          input
      have nextScratchZero : ∀ wire ∈ scratches, next wire = false :=
        controlledIncrementWordMod2PowInPlace_reference_scratch_zero
          control word scratches input enoughScratch headLayout scratchZero
      change ∀ wire ∈ scratches,
        (controlledIncrementProgram controls word scratches).reference next wire =
          false
      exact inductionHypothesis next tailLayout nextScratchZero

/-- Extensional little-endian register-equals-constant predicate.  It checks
exactly the in-width test bits of the natural number.  A separate range premise
is therefore required when this predicate is rewritten as equality of natural
numbers. -/
def littleEndianRegisterEqualsNat {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat)
    (input : QubitBasis qubits) : Bool :=
  register.zipIdx.all fun indexed =>
    decide (input indexed.1 = constant.testBit indexed.2)

/-- Register equality depends only on the values read from its declared
wires. -/
theorem littleEndianRegisterEqualsNat_congr {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat)
    (left right : QubitBasis qubits)
    (same : ∀ wire, wire ∈ register → left wire = right wire) :
    littleEndianRegisterEqualsNat register constant left =
      littleEndianRegisterEqualsNat register constant right := by
  unfold littleEndianRegisterEqualsNat
  have mapped :
      register.zipIdx.map
          (fun indexed => decide (left indexed.1 = constant.testBit indexed.2)) =
        register.zipIdx.map
          (fun indexed => decide (right indexed.1 = constant.testBit indexed.2)) := by
    apply List.map_congr_left
    intro indexed member
    rw [same indexed.1 (List.fst_mem_of_mem_zipIdx member)]
  simpa only [List.all_map, Function.comp_def, id_eq] using
    congrArg (fun values : List Bool => values.all id) mapped

/-- Width-truncated little-endian bit list of a natural number. -/
def littleEndianNatBits (width value : Nat) : List Bool :=
  (List.finRange width).map fun wire => value.testBit wire.val

@[simp] theorem littleEndianNatBits_length (width value : Nat) :
    (littleEndianNatBits width value).length = width := by
  simp [littleEndianNatBits]

/-- In-range naturals are recovered exactly from their fixed-width bit list. -/
theorem littleEndianListNat_littleEndianNatBits_of_lt
    (width value : Nat) (inside : value < 2 ^ width) :
    littleEndianListNat (littleEndianNatBits width value) = value := by
  let index : Fin (2 ^ width) := ⟨value, inside⟩
  have decoded := littleEndianListNat_finRange
    (qubitBasisOfLittleEndianIndex index)
  rw [qubitBasisLittleEndianIndex_basis] at decoded
  unfold littleEndianNatBits
  calc
    littleEndianListNat
        ((List.finRange width).map fun wire => value.testBit wire.val) =
      littleEndianListNat
        ((List.finRange width).map (qubitBasisOfLittleEndianIndex index)) := by
          rfl
    _ = value := decoded

/-- The explicit register predicate is equivalent to equality with the
fixed-width test-bit list. -/
theorem littleEndianRegisterEqualsNat_eq_true_iff {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat)
    (input : QubitBasis qubits) :
    littleEndianRegisterEqualsNat register constant input = true ↔
      readWires register input = littleEndianNatBits register.length constant := by
  unfold littleEndianRegisterEqualsNat
  constructor
  · intro allMatch
    apply List.ext_get
    · simp [readWires]
    · intro index leftBound rightBound
      have indexedBound : index < register.zipIdx.length := by
        simpa [readWires] using leftBound
      have indexedMember : register.zipIdx[index] ∈ register.zipIdx :=
        List.getElem_mem indexedBound
      have matchAt := (List.all_eq_true.mp allMatch)
        register.zipIdx[index] indexedMember
      simpa [readWires, littleEndianNatBits] using matchAt
  · intro listsEqual
    apply List.all_eq_true.mpr
    intro indexed member
    rcases List.mem_iff_getElem.mp member with
      ⟨index, indexBound, indexedAt⟩
    have registerBound : index < register.length := by
      simpa using indexBound
    have bitsAt := congrArg (fun bits : List Bool => bits[index]?) listsEqual
    subst indexed
    simpa [readWires, littleEndianNatBits, registerBound] using bitsAt

/-- Under the no-truncation range premise, the explicit Boolean predicate is
equivalent to equality of the decoded natural value. -/
theorem littleEndianRegisterEqualsNat_eq_decide {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat)
    (input : QubitBasis qubits) (inside : constant < 2 ^ register.length) :
    littleEndianRegisterEqualsNat register constant input =
      decide (littleEndianListNat (readWires register input) = constant) := by
  have sameLength : (readWires register input).length =
      (littleEndianNatBits register.length constant).length := by
    simp [readWires]
  have injective : ∀ left right : List Bool,
      left.length = right.length →
      littleEndianListNat left = littleEndianListNat right → left = right := by
    intro left
    induction left with
    | nil =>
        intro right lengthEqual valueEqual
        cases right <;> simp at lengthEqual ⊢
    | cons leftBit leftBits inductionHypothesis =>
        intro right lengthEqual valueEqual
        cases right with
        | nil => simp at lengthEqual
        | cons rightBit rightBits =>
            have tailLength : leftBits.length = rightBits.length := by
              simpa using Nat.succ.inj lengthEqual
            cases leftBit <;> cases rightBit <;>
              simp only [littleEndianListNat, Bool.toNat_false,
                Bool.toNat_true] at valueEqual ⊢
            · congr 1
              exact inductionHypothesis rightBits tailLength (by omega)
            · omega
            · omega
            · congr 1
              exact inductionHypothesis rightBits tailLength (by omega)
  by_cases valueEqual : littleEndianListNat (readWires register input) = constant
  · rw [decide_eq_true valueEqual]
    apply (littleEndianRegisterEqualsNat_eq_true_iff register constant input).2
    apply injective _ _ sameLength
    rw [valueEqual,
      littleEndianListNat_littleEndianNatBits_of_lt _ _ inside]
  · rw [decide_eq_false valueEqual]
    apply Bool.eq_false_of_not_eq_true
    intro predicateTrue
    apply valueEqual
    have bitsEqual :=
      (littleEndianRegisterEqualsNat_eq_true_iff register constant input).1
        predicateTrue
    rw [bitsEqual,
      littleEndianListNat_littleEndianNatBits_of_lt _ _ inside]

/-- Erasing the expected Boolean values from the constant-equality controls
recovers exactly the declared register wire list. -/
theorem equalityToConstantControls_map_fst {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat) :
    (equalityToConstantControls register constant).map Prod.fst = register := by
  apply List.ext_get
  · simp [equalityToConstantControls]
  · intro index leftBound rightBound
    simp [equalityToConstantControls]

/-- The recorded equality-to-constant stage has its direct clean XOR action
and restores all Boolean multi-control work. -/
theorem xorEqualityToConstantIntoTarget_reference_apply_of_cleanWork
    {qubits : Nat}
    (register scratches : List (Fin qubits)) (constant : Nat)
    (target : Fin qubits) (input : QubitBasis qubits)
    (enoughScratch : register.length ≤ scratches.length + 1)
    (layoutNodup : (register ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (xorEqualityToConstantIntoTarget register scratches constant target).reference
        input =
      xorWire target
        (littleEndianRegisterEqualsNat register constant input) input := by
  simpa [xorEqualityToConstantIntoTarget, equalityToConstantControls,
    littleEndianRegisterEqualsNat, boolControlsSatisfied, Function.comp_def]
    using boolMultiControlledX_reference_apply_of_cleanWork
      (equalityToConstantControls register constant) scratches target input
      (by simpa [equalityToConstantControls] using enoughScratch)
      (by
        rw [equalityToConstantControls_map_fst]
        exact layoutNodup)
      scratchZero

/-- The minimum-work equality-to-constant stage has the same clean extensional
action, now under the source-faithful `width ≤ scratch + 2` capacity bound. -/
theorem xorEqualityToConstantIntoTargetMinimumWork_reference_apply_of_cleanWork
    {qubits : Nat}
    (register scratches : List (Fin qubits)) (constant : Nat)
    (target : Fin qubits) (input : QubitBasis qubits)
    (enoughScratch : register.length ≤ scratches.length + 2)
    (layoutNodup : (register ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (xorEqualityToConstantIntoTargetMinimumWork
        register scratches constant target).reference input =
      xorWire target
        (littleEndianRegisterEqualsNat register constant input) input := by
  let controls := equalityToConstantControls register constant
  let controlWires := controls.map Prod.fst
  let invert := invertZeroControls controls
  let prepared := invert.reference input
  have controlsEnough : controlWires.length ≤ scratches.length + 2 := by
    simp [controlWires, controls, equalityToConstantControls]
    exact enoughScratch
  have controlsLayout : (controlWires ++ scratches ++ [target]).Nodup := by
    dsimp [controlWires, controls]
    rw [equalityToConstantControls_map_fst]
    exact layoutNodup
  have combinedNodup : (controlWires ++ scratches).Nodup :=
    (List.nodup_append.mp controlsLayout).1
  have controlNodup : controlWires.Nodup :=
    (List.nodup_append.mp combinedNodup).1
  have targetOutside : target ∉ controlWires := by
    intro member
    have separated := (List.nodup_append.mp controlsLayout).2.2
    exact separated target (List.mem_append_left scratches member)
      target (by simp) rfl
  have scratchesOutside : ∀ wire ∈ scratches, wire ∉ controlWires := by
    have separated := (List.nodup_append.mp combinedNodup).2.2
    intro wire scratchMember controlMember
    exact separated wire controlMember wire scratchMember rfl
  have preparedScratchZero : ∀ wire ∈ scratches, prepared wire = false := by
    intro wire member
    change (invertZeroControls controls).reference input wire = false
    rw [invertZeroControls_reference_apply_outside controls wire input
      (scratchesOutside wire member)]
    exact scratchZero wire member
  have preparedCondition :
      allWiresTrue controlWires prepared = boolControlsSatisfied controls input :=
    allWiresTrue_invertZeroControls_reference controls input controlNodup
  have cleanResult :
      (boolMultiControlledXMinimumWork controls scratches target).reference input =
        xorWire target (boolControlsSatisfied controls input) input := by
    change invert.reference
        ((minimumWorkPositiveMultiControlledX controlWires scratches target).reference
          prepared) = _
    rw [minimumWorkPositiveMultiControlledX_reference_apply_of_cleanWork
      controlWires scratches target prepared controlsEnough controlsLayout
      preparedScratchZero]
    rw [preparedCondition]
    rw [invertZeroControls_reference_commutes_xorWire controls target
      (boolControlsSatisfied controls input) prepared targetOutside]
    rw [invertZeroControls_reference_involutive controls input controlNodup]
  simpa [xorEqualityToConstantIntoTargetMinimumWork, controls,
    equalityToConstantControls, littleEndianRegisterEqualsNat,
    boolControlsSatisfied, Function.comp_def] using cleanResult

/-- Natural value represented by the carry recurrence.  The result is the
input value plus the carry, reduced modulo the fixed bit width. -/
theorem littleEndianListNat_lt_pow (bits : List Bool) :
    littleEndianListNat bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [littleEndianListNat]
  | cons bit bits inductionHypothesis =>
      cases bit <;> simp [littleEndianListNat, pow_succ] <;> omega

theorem littleEndianListNat_incrementBitsWithCarry
    (carry : Bool) (bits : List Bool) :
    littleEndianListNat (incrementBitsWithCarry carry bits) =
      (littleEndianListNat bits + carry.toNat) % (2 ^ bits.length) := by
  cases carry with
  | false =>
      rw [incrementBitsWithCarry_false]
      simp only [Bool.toNat_false, Nat.add_zero]
      rw [Nat.mod_eq_of_lt (littleEndianListNat_lt_pow bits)]
  | true =>
      induction bits with
      | nil => simp [incrementBitsWithCarry, littleEndianListNat]
      | cons bit bits inductionHypothesis =>
          cases bit with
          | false =>
              simp only [incrementBitsWithCarry, littleEndianListNat,
                Bool.toNat_false, Nat.add_zero, List.length_cons,
                Bool.true_and, if_true, Bool.not_false, Bool.toNat_true]
              rw [Nat.mod_eq_of_lt]
              · simp
              · have bound := littleEndianListNat_lt_pow bits
                rw [pow_succ]
                omega
          | true =>
              change 2 * littleEndianListNat (incrementBitsWithCarry true bits) =
                (2 * littleEndianListNat bits + 1 + 1) %
                  (2 ^ (bits.length + 1))
              rw [show 2 * littleEndianListNat bits + 1 + 1 =
                2 * (littleEndianListNat bits + 1) by omega]
              rw [pow_succ]
              rw [show 2 ^ bits.length * 2 = 2 * 2 ^ bits.length by omega]
              rw [Nat.mul_mod_mul_left]
              simpa using inductionHypothesis

/-- Repeated controlled increments add the number of true control values,
modulo the counter capacity. -/
theorem littleEndianListNat_incrementBitsForControlValues
    (controls bits : List Bool) :
    littleEndianListNat (incrementBitsForControlValues controls bits) =
      (littleEndianListNat bits + boolTrueCount controls) %
        (2 ^ bits.length) := by
  induction controls generalizing bits with
  | nil =>
      simp only [incrementBitsForControlValues, boolTrueCount, Nat.add_zero]
      rw [Nat.mod_eq_of_lt (littleEndianListNat_lt_pow bits)]
  | cons control controls inductionHypothesis =>
      have lengthPreserved :
          (incrementBitsWithCarry control bits).length = bits.length := by
        induction bits generalizing control with
        | nil => rfl
        | cons bit bits hypothesis =>
            simp [incrementBitsWithCarry, hypothesis]
      rw [incrementBitsForControlValues, inductionHypothesis,
        littleEndianListNat_incrementBitsWithCarry, lengthPreserved]
      cases control with
      | false =>
          simp only [Bool.toNat_false, Nat.add_zero, boolTrueCount, Nat.zero_add]
          rw [Nat.mod_add_mod]
      | true =>
          simp only [Bool.toNat_true, boolTrueCount]
          rw [Nat.mod_add_mod]
          congr 1
          omega

end ClassicalReversibleStage

end VerifiedCircuitCore
