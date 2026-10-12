import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic

/-!
# Clean semantics of positive multi-controlled XOR stages

The compute/use/uncompute chain is proved directly at the basis-action level.
No gate-stream semantics or matrix expansion is used.
-/

namespace VerifiedCircuitCore

namespace ClassicalReversibleStage

/-- Read a list of classical wires in source order. -/
def readWires {qubits : Nat} (wires : List (Fin qubits))
    (input : QubitBasis qubits) : List Bool :=
  wires.map input

/-- Test whether all listed wires are true. -/
def allWiresTrue {qubits : Nat} (wires : List (Fin qubits))
    (input : QubitBasis qubits) : Bool :=
  (readWires wires input).all id

/-- Moving one fresh wire across a list preserves list membership up to
permutation. -/
theorem perm_cons_append {α : Type*} (value : α)
    (middle suffix : List α) :
    (value :: middle ++ suffix).Perm (middle ++ value :: suffix) :=
  List.perm_middle.symm

/-- Reading wires not containing the XOR target is unchanged. -/
theorem readWires_xorWire_of_not_mem {qubits : Nat}
    (wires : List (Fin qubits)) (target : Fin qubits) (value : Bool)
    (input : QubitBasis qubits) (targetAbsent : target ∉ wires) :
    readWires wires (xorWire target value input) = readWires wires input := by
  apply List.map_congr_left
  intro wire member
  exact xorWire_apply_other target wire
    (fun equal => targetAbsent (equal ▸ member)) value input

/-- The internal AND chain uses a clean scratch suffix, toggles only the
final target by the conjunction, and restores every scratch wire. -/
theorem andChainUse_reference_apply_of_cleanWork
    {qubits : Nat} (previous : Fin qubits)
    (controls scratches : List (Fin qubits)) (target : Fin qubits)
    (input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length)
    (layoutNodup : (previous :: controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (andChainUse previous controls scratches target).reference input =
      xorWire target (allWiresTrue (previous :: controls) input) input := by
  induction controls generalizing previous scratches input with
  | nil =>
      have previousDifferentTarget : previous ≠ target := by
        intro equal
        apply (List.nodup_cons.mp layoutNodup).1
        simp [equal]
      simp [andChainUse, safeXorControlled, previousDifferentTarget,
        reference, ClassicalReversibleInstruction.reference,
        ClassicalReversibleInstruction.basisAction, allWiresTrue, readWires]
  | cons control controls inductionHypothesis =>
      cases scratches with
      | nil => simp at enoughScratch
      | cons scratch scratches =>
          have previousFresh := (List.nodup_cons.mp layoutNodup).1
          have tailNodup := (List.nodup_cons.mp layoutNodup).2
          have controlFresh := (List.nodup_cons.mp tailNodup).1
          have remainingNodup := (List.nodup_cons.mp tailNodup).2
          have previousDifferentControl : previous ≠ control := by
            intro equal
            apply previousFresh
            simp [equal]
          have previousDifferentScratch : previous ≠ scratch := by
            intro equal
            apply previousFresh
            simp [equal]
          have controlDifferentScratch : control ≠ scratch := by
            intro equal
            apply controlFresh
            simp [equal]
          have targetDifferentPrevious : target ≠ previous := by
            intro equal
            apply previousFresh
            simp [equal]
          have targetDifferentControl : target ≠ control := by
            intro equal
            apply controlFresh
            simp [equal]
          have recursiveLayout :
              (scratch :: controls ++ scratches ++ [target]).Nodup := by
            have permutation :=
              perm_cons_append scratch controls (scratches ++ [target])
            have reordered :
                (scratch :: controls ++ (scratches ++ [target])).Nodup := by
              apply permutation.symm.nodup
              simpa [List.append_assoc] using remainingNodup
            simpa [List.append_assoc] using reordered
          have scratchFresh := (List.nodup_cons.mp recursiveLayout).1
          have scratchZeroHead : input scratch = false :=
            scratchZero scratch (by simp)
          let instruction : ClassicalReversibleInstruction qubits :=
            .xorDoublyControlled previous control scratch
              previousDifferentControl previousDifferentScratch
              controlDifferentScratch
          let firstState := instruction.basisAction input
          have controlsUnchanged :
              readWires controls firstState = readWires controls input := by
            unfold firstState instruction
            apply readWires_xorWire_of_not_mem
            intro member
            exact scratchFresh (by simp [member])
          have scratchesStillZero :
              ∀ wire ∈ scratches, firstState wire = false := by
            intro wire member
            unfold firstState instruction
            change xorWire scratch (input previous && input control) input wire = false
            rw [xorWire_apply_other scratch wire]
            · exact scratchZero wire (by simp [member])
            · intro equal
              apply scratchFresh
              rw [← equal]
              simp [member]
          have allControlsUnchanged :
              (List.map firstState controls).all id =
                (List.map input controls).all id := by
            simpa [readWires] using
              congrArg (fun values => values.all id) controlsUnchanged
          have recursiveCondition :
              allWiresTrue (scratch :: controls) firstState =
                allWiresTrue (previous :: control :: controls) input := by
            unfold allWiresTrue readWires
            simp only [List.map_cons, List.all_cons, id_eq]
            rw [allControlsUnchanged]
            have scratchValue :
                firstState scratch = (input previous && input control) := by
              unfold firstState instruction
              simp [ClassicalReversibleInstruction.basisAction, xorWire,
                scratchZeroHead]
            rw [scratchValue]
            exact Bool.and_assoc _ _ _
          have targetDifferentScratch : target ≠ scratch := by
            intro equal
            apply scratchFresh
            simp [equal]
          have tailEnough : controls.length ≤ scratches.length := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using
              enoughScratch
          have recursive := inductionHypothesis scratch scratches firstState
            tailEnough recursiveLayout scratchesStillZero
          have targetOutsideInstruction :
              target ∉ instruction.supportWires := by
            simp [instruction, ClassicalReversibleInstruction.supportWires,
              targetDifferentPrevious, targetDifferentControl,
              targetDifferentScratch]
          have stepDefinition :
              safeXorDoublyControlled previous control scratch =
                .instruction instruction := by
            simp [safeXorDoublyControlled, instruction,
              previousDifferentControl, previousDifferentScratch,
              controlDifferentScratch]
          rw [andChainUse, stepDefinition]
          change instruction.basisAction
              ((andChainUse scratch controls scratches target).reference
                (instruction.basisAction input)) = _
          rw [recursive, recursiveCondition]
          rw [instruction.basisAction_commutes_xorWire_of_not_mem_support
            target _ firstState targetOutsideInstruction]
          exact congrArg (xorWire target
            (allWiresTrue (previous :: control :: controls) input))
            (instruction.basisAction_involutive input)

/-- A positive multi-controlled XOR has the direct conjunction action on
clean, disjoint scratch and restores the full input outside its target. -/
theorem positiveMultiControlledX_reference_apply_of_cleanWork
    {qubits : Nat} (controls scratches : List (Fin qubits))
    (target : Fin qubits) (input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (positiveMultiControlledX controls scratches target).reference input =
      xorWire target (allWiresTrue controls input) input := by
  cases controls with
  | nil =>
      simp [positiveMultiControlledX, reference,
        ClassicalReversibleInstruction.reference,
        ClassicalReversibleInstruction.basisAction, allWiresTrue, readWires]
  | cons control controls =>
      cases controls with
      | nil =>
          have controlDifferentTarget : control ≠ target := by
            intro equal
            apply (List.nodup_cons.mp layoutNodup).1
            simp [equal]
          simp [positiveMultiControlledX, safeXorControlled,
            controlDifferentTarget, reference,
            ClassicalReversibleInstruction.reference,
            ClassicalReversibleInstruction.basisAction, allWiresTrue,
            readWires]
      | cons control₂ controls =>
          cases scratches with
          | nil => simp at enoughScratch
          | cons scratch scratches =>
              have firstFresh := (List.nodup_cons.mp layoutNodup).1
              have afterFirstNodup := (List.nodup_cons.mp layoutNodup).2
              have secondFresh := (List.nodup_cons.mp afterFirstNodup).1
              have remainingNodup :=
                (List.nodup_cons.mp afterFirstNodup).2
              have controlsDifferent : control ≠ control₂ := by
                intro equal
                apply firstFresh
                simp [equal]
              have firstDifferentScratch : control ≠ scratch := by
                intro equal
                apply firstFresh
                simp [equal]
              have secondDifferentScratch : control₂ ≠ scratch := by
                intro equal
                apply secondFresh
                simp [equal]
              have targetDifferentFirst : target ≠ control := by
                intro equal
                apply firstFresh
                simp [equal]
              have targetDifferentSecond : target ≠ control₂ := by
                intro equal
                apply secondFresh
                simp [equal]
              have recursiveLayout :
                  (scratch :: controls ++ scratches ++ [target]).Nodup := by
                have permutation :=
                  perm_cons_append scratch controls (scratches ++ [target])
                have reordered :
                    (scratch :: controls ++ (scratches ++ [target])).Nodup := by
                  apply permutation.symm.nodup
                  simpa [List.append_assoc] using remainingNodup
                simpa [List.append_assoc] using reordered
              have scratchFresh := (List.nodup_cons.mp recursiveLayout).1
              have scratchZeroHead : input scratch = false :=
                scratchZero scratch (by simp)
              let instruction : ClassicalReversibleInstruction qubits :=
                .xorDoublyControlled control control₂ scratch
                  controlsDifferent firstDifferentScratch
                  secondDifferentScratch
              let firstState := instruction.basisAction input
              have controlsUnchanged :
                  readWires controls firstState = readWires controls input := by
                unfold firstState instruction
                apply readWires_xorWire_of_not_mem
                intro member
                exact scratchFresh (by simp [member])
              have allControlsUnchanged :
                  (List.map firstState controls).all id =
                    (List.map input controls).all id := by
                simpa [readWires] using
                  congrArg (fun values => values.all id) controlsUnchanged
              have recursiveCondition :
                  allWiresTrue (scratch :: controls) firstState =
                    allWiresTrue (control :: control₂ :: controls) input := by
                unfold allWiresTrue readWires
                simp only [List.map_cons, List.all_cons, id_eq]
                rw [allControlsUnchanged]
                have scratchValue :
                    firstState scratch = (input control && input control₂) := by
                  unfold firstState instruction
                  simp [ClassicalReversibleInstruction.basisAction, xorWire,
                    scratchZeroHead]
                rw [scratchValue]
                exact Bool.and_assoc _ _ _
              have scratchesStillZero :
                  ∀ wire ∈ scratches, firstState wire = false := by
                intro wire member
                unfold firstState instruction
                change xorWire scratch (input control && input control₂) input wire = false
                rw [xorWire_apply_other scratch wire]
                · exact scratchZero wire (by simp [member])
                · intro equal
                  apply scratchFresh
                  rw [← equal]
                  simp [member]
              have targetDifferentScratch : target ≠ scratch := by
                intro equal
                apply scratchFresh
                simp [equal]
              have tailEnough : controls.length ≤ scratches.length := by
                simp only [List.length_cons] at enoughScratch
                omega
              have recursive :=
                andChainUse_reference_apply_of_cleanWork scratch controls
                  scratches target firstState tailEnough recursiveLayout
                  scratchesStillZero
              have targetOutsideInstruction :
                  target ∉ instruction.supportWires := by
                simp [instruction,
                  ClassicalReversibleInstruction.supportWires,
                  targetDifferentFirst, targetDifferentSecond,
                  targetDifferentScratch]
              have stepDefinition :
                  safeXorDoublyControlled control control₂ scratch =
                    .instruction instruction := by
                simp [safeXorDoublyControlled, instruction,
                  controlsDifferent, firstDifferentScratch,
                  secondDifferentScratch]
              rw [positiveMultiControlledX, stepDefinition]
              change instruction.basisAction
                  ((andChainUse scratch controls scratches target).reference
                    (instruction.basisAction input)) = _
              rw [recursive, recursiveCondition]
              rw [instruction.basisAction_commutes_xorWire_of_not_mem_support
                target _ firstState targetOutsideInstruction]
              exact congrArg (xorWire target
                (allWiresTrue (control :: control₂ :: controls) input))
                (instruction.basisAction_involutive input)

/-- The public conjunction stage has the same direct clean-work action. -/
theorem xorConjunctionIntoTarget_reference_apply_of_cleanWork
    {qubits : Nat} (controls scratches : List (Fin qubits))
    (target : Fin qubits) (input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (xorConjunctionIntoTarget controls scratches target).reference input =
      xorWire target (allWiresTrue controls input) input := by
  simpa [xorConjunctionIntoTarget] using
    positiveMultiControlledX_reference_apply_of_cleanWork
      controls scratches target input enoughScratch layoutNodup scratchZero

end ClassicalReversibleStage

end VerifiedCircuitCore
