import QLean.Circuits.Foundation.ClassicalConstructionMultiControlledXCorrectnessAnalytic

/-!
# Clean semantics of the minimum-work positive multi-controlled XOR

The last control is used directly in the target Toffoli.  Thus `n` controls
need only `n - 2` clean scratch wires, while the older AND-chain family that
materializes the full conjunction remains a separate API.
-/

namespace VerifiedCircuitCore

namespace ClassicalReversibleStage

/-- The minimum-work tail reserves its final control for the target Toffoli,
uses a clean scratch prefix, and restores the full input outside the target. -/
theorem minimumWorkAndChainUse_reference_apply_of_cleanWork
    {qubits : Nat} (previous : Fin qubits)
    (controls scratches : List (Fin qubits)) (target : Fin qubits)
    (input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (previous :: controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (minimumWorkAndChainUse previous controls scratches target).reference input =
      xorWire target (allWiresTrue (previous :: controls) input) input := by
  induction controls generalizing previous scratches input with
  | nil =>
      have previousDifferentTarget : previous ≠ target := by
        intro equal
        apply (List.nodup_cons.mp layoutNodup).1
        simp [equal]
      simp [minimumWorkAndChainUse, safeXorControlled,
        previousDifferentTarget, reference,
        ClassicalReversibleInstruction.reference,
        ClassicalReversibleInstruction.basisAction, allWiresTrue, readWires]
  | cons control controls inductionHypothesis =>
      cases controls with
      | nil =>
          have previousFresh := (List.nodup_cons.mp layoutNodup).1
          have tailNodup := (List.nodup_cons.mp layoutNodup).2
          have controlFresh := (List.nodup_cons.mp tailNodup).1
          have previousDifferentControl : previous ≠ control := by
            intro equal
            apply previousFresh
            simp [equal]
          have previousDifferentTarget : previous ≠ target := by
            intro equal
            apply previousFresh
            simp [equal]
          have controlDifferentTarget : control ≠ target := by
            intro equal
            apply controlFresh
            simp [equal]
          simp [minimumWorkAndChainUse, safeXorDoublyControlled,
            previousDifferentControl, previousDifferentTarget,
            controlDifferentTarget, reference,
            ClassicalReversibleInstruction.reference,
            ClassicalReversibleInstruction.basisAction, allWiresTrue,
            readWires]
      | cons next controls =>
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
                  (scratch :: next :: controls ++ scratches ++ [target]).Nodup := by
                have permutation :=
                  perm_cons_append scratch (next :: controls)
                    (scratches ++ [target])
                have reordered :
                    (scratch :: (next :: controls) ++
                      (scratches ++ [target])).Nodup := by
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
                  readWires (next :: controls) firstState =
                    readWires (next :: controls) input := by
                unfold firstState instruction
                apply readWires_xorWire_of_not_mem
                intro member
                exact scratchFresh
                  (List.mem_append_left [target]
                    (List.mem_append_left scratches member))
              have scratchesStillZero :
                  ∀ wire ∈ scratches, firstState wire = false := by
                intro wire member
                unfold firstState instruction
                change xorWire scratch
                  (input previous && input control) input wire = false
                rw [xorWire_apply_other scratch wire]
                · exact scratchZero wire (by simp [member])
                · intro equal
                  apply scratchFresh
                  rw [← equal]
                  simp [member]
              have allControlsUnchanged :
                  (List.map firstState (next :: controls)).all id =
                    (List.map input (next :: controls)).all id := by
                simpa [readWires] using
                  congrArg (fun values => values.all id) controlsUnchanged
              have recursiveCondition :
                  allWiresTrue (scratch :: next :: controls) firstState =
                    allWiresTrue (previous :: control :: next :: controls)
                      input := by
                unfold allWiresTrue readWires
                change (firstState scratch &&
                    (List.map firstState (next :: controls)).all id) =
                  (input previous && (input control &&
                    (List.map input (next :: controls)).all id))
                have scratchValue :
                    firstState scratch =
                      (input previous && input control) := by
                  unfold firstState instruction
                  simp [ClassicalReversibleInstruction.basisAction, xorWire,
                    scratchZeroHead]
                rw [scratchValue, allControlsUnchanged]
                exact Bool.and_assoc _ _ _
              have targetDifferentScratch : target ≠ scratch := by
                intro equal
                apply scratchFresh
                simp [equal]
              have tailEnough :
                  (next :: controls).length ≤ scratches.length + 1 := by
                simpa only [List.length_cons, Nat.succ_le_succ_iff] using
                  enoughScratch
              have recursive :=
                inductionHypothesis scratch scratches firstState tailEnough
                  recursiveLayout scratchesStillZero
              have targetOutsideInstruction :
                  target ∉ instruction.supportWires := by
                simp [instruction,
                  ClassicalReversibleInstruction.supportWires,
                  targetDifferentPrevious, targetDifferentControl,
                  targetDifferentScratch]
              have stepDefinition :
                  safeXorDoublyControlled previous control scratch =
                    .instruction instruction := by
                simp [safeXorDoublyControlled, instruction,
                  previousDifferentControl, previousDifferentScratch,
                  controlDifferentScratch]
              have chainDefinition :
                  minimumWorkAndChainUse previous
                      (control :: next :: controls) (scratch :: scratches)
                      target =
                    .seq (.instruction instruction)
                      (.seq (minimumWorkAndChainUse scratch
                        (next :: controls) scratches target)
                        (.instruction instruction)) := by
                simp [minimumWorkAndChainUse, stepDefinition]
              rw [chainDefinition]
              change instruction.basisAction
                  ((minimumWorkAndChainUse scratch (next :: controls)
                    scratches target).reference
                    (instruction.basisAction input)) = _
              rw [recursive, recursiveCondition]
              rw [instruction.basisAction_commutes_xorWire_of_not_mem_support
                target _ firstState targetOutsideInstruction]
              exact congrArg (xorWire target
                (allWiresTrue
                  (previous :: control :: next :: controls) input))
                (instruction.basisAction_involutive input)

/-- A source-faithful minimum-work positive multi-controlled XOR has the
direct conjunction action on clean, disjoint scratch and restores every wire
outside its target. -/
theorem minimumWorkPositiveMultiControlledX_reference_apply_of_cleanWork
    {qubits : Nat} (controls scratches : List (Fin qubits))
    (target : Fin qubits) (input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length + 2)
    (layoutNodup : (controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (minimumWorkPositiveMultiControlledX controls scratches target).reference
        input = xorWire target (allWiresTrue controls input) input := by
  cases controls with
  | nil =>
      simp [minimumWorkPositiveMultiControlledX, reference,
        ClassicalReversibleInstruction.reference,
        ClassicalReversibleInstruction.basisAction, allWiresTrue, readWires]
  | cons first controls =>
      cases controls with
      | nil =>
          have firstDifferentTarget : first ≠ target := by
            intro equal
            apply (List.nodup_cons.mp layoutNodup).1
            simp [equal]
          simp [minimumWorkPositiveMultiControlledX, safeXorControlled,
            firstDifferentTarget, reference,
            ClassicalReversibleInstruction.reference,
            ClassicalReversibleInstruction.basisAction, allWiresTrue,
            readWires]
      | cons second controls =>
          cases controls with
          | nil =>
              have firstFresh := (List.nodup_cons.mp layoutNodup).1
              have secondNodup := (List.nodup_cons.mp layoutNodup).2
              have secondFresh := (List.nodup_cons.mp secondNodup).1
              have firstDifferentSecond : first ≠ second := by
                intro equal
                apply firstFresh
                simp [equal]
              have firstDifferentTarget : first ≠ target := by
                intro equal
                apply firstFresh
                simp [equal]
              have secondDifferentTarget : second ≠ target := by
                intro equal
                apply secondFresh
                simp [equal]
              simp [minimumWorkPositiveMultiControlledX,
                safeXorDoublyControlled, firstDifferentSecond,
                firstDifferentTarget, secondDifferentTarget, reference,
                ClassicalReversibleInstruction.reference,
                ClassicalReversibleInstruction.basisAction, allWiresTrue,
                readWires]
          | cons third controls =>
              cases scratches with
              | nil => simp at enoughScratch
              | cons scratch scratches =>
                  have firstFresh := (List.nodup_cons.mp layoutNodup).1
                  have afterFirstNodup :=
                    (List.nodup_cons.mp layoutNodup).2
                  have secondFresh :=
                    (List.nodup_cons.mp afterFirstNodup).1
                  have remainingNodup :=
                    (List.nodup_cons.mp afterFirstNodup).2
                  have firstDifferentSecond : first ≠ second := by
                    intro equal
                    apply firstFresh
                    simp [equal]
                  have firstDifferentScratch : first ≠ scratch := by
                    intro equal
                    apply firstFresh
                    simp [equal]
                  have secondDifferentScratch : second ≠ scratch := by
                    intro equal
                    apply secondFresh
                    simp [equal]
                  have targetDifferentFirst : target ≠ first := by
                    intro equal
                    apply firstFresh
                    simp [equal]
                  have targetDifferentSecond : target ≠ second := by
                    intro equal
                    apply secondFresh
                    simp [equal]
                  have recursiveLayout :
                      (scratch :: third :: controls ++ scratches ++
                        [target]).Nodup := by
                    have permutation :=
                      perm_cons_append scratch (third :: controls)
                        (scratches ++ [target])
                    have reordered :
                        (scratch :: (third :: controls) ++
                          (scratches ++ [target])).Nodup := by
                      apply permutation.symm.nodup
                      simpa [List.append_assoc] using remainingNodup
                    simpa [List.append_assoc] using reordered
                  have scratchFresh :=
                    (List.nodup_cons.mp recursiveLayout).1
                  have scratchZeroHead : input scratch = false :=
                    scratchZero scratch (by simp)
                  let instruction : ClassicalReversibleInstruction qubits :=
                    .xorDoublyControlled first second scratch
                      firstDifferentSecond firstDifferentScratch
                      secondDifferentScratch
                  let firstState := instruction.basisAction input
                  have controlsUnchanged :
                      readWires (third :: controls) firstState =
                        readWires (third :: controls) input := by
                    unfold firstState instruction
                    apply readWires_xorWire_of_not_mem
                    intro member
                    exact scratchFresh
                      (List.mem_append_left [target]
                        (List.mem_append_left scratches member))
                  have allControlsUnchanged :
                      (List.map firstState (third :: controls)).all id =
                        (List.map input (third :: controls)).all id := by
                    simpa [readWires] using
                      congrArg (fun values => values.all id)
                        controlsUnchanged
                  have recursiveCondition :
                      allWiresTrue (scratch :: third :: controls) firstState =
                        allWiresTrue
                          (first :: second :: third :: controls) input := by
                    unfold allWiresTrue readWires
                    change (firstState scratch &&
                        (List.map firstState (third :: controls)).all id) =
                      (input first && (input second &&
                        (List.map input (third :: controls)).all id))
                    have scratchValue :
                        firstState scratch =
                          (input first && input second) := by
                      unfold firstState instruction
                      simp [ClassicalReversibleInstruction.basisAction,
                        xorWire, scratchZeroHead]
                    rw [scratchValue, allControlsUnchanged]
                    exact Bool.and_assoc _ _ _
                  have scratchesStillZero :
                      ∀ wire ∈ scratches, firstState wire = false := by
                    intro wire member
                    unfold firstState instruction
                    change xorWire scratch
                      (input first && input second) input wire = false
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
                  have tailEnough :
                      (third :: controls).length ≤ scratches.length + 1 := by
                    simp only [List.length_cons] at enoughScratch ⊢
                    omega
                  have recursive :=
                    minimumWorkAndChainUse_reference_apply_of_cleanWork
                      scratch (third :: controls) scratches target firstState
                      tailEnough recursiveLayout scratchesStillZero
                  have targetOutsideInstruction :
                      target ∉ instruction.supportWires := by
                    simp [instruction,
                      ClassicalReversibleInstruction.supportWires,
                      targetDifferentFirst, targetDifferentSecond,
                      targetDifferentScratch]
                  have stepDefinition :
                      safeXorDoublyControlled first second scratch =
                        .instruction instruction := by
                    simp [safeXorDoublyControlled, instruction,
                      firstDifferentSecond, firstDifferentScratch,
                      secondDifferentScratch]
                  have cascadeDefinition :
                      minimumWorkPositiveMultiControlledX
                          (first :: second :: third :: controls)
                          (scratch :: scratches) target =
                        .seq (.instruction instruction)
                          (.seq (minimumWorkAndChainUse scratch
                            (third :: controls) scratches target)
                            (.instruction instruction)) := by
                    simp [minimumWorkPositiveMultiControlledX,
                      stepDefinition]
                  rw [cascadeDefinition]
                  change instruction.basisAction
                      ((minimumWorkAndChainUse scratch (third :: controls)
                        scratches target).reference
                        (instruction.basisAction input)) = _
                  rw [recursive, recursiveCondition]
                  rw [instruction.basisAction_commutes_xorWire_of_not_mem_support
                    target _ firstState targetOutsideInstruction]
                  exact congrArg (xorWire target
                    (allWiresTrue
                      (first :: second :: third :: controls) input))
                    (instruction.basisAction_involutive input)

end ClassicalReversibleStage

end VerifiedCircuitCore
