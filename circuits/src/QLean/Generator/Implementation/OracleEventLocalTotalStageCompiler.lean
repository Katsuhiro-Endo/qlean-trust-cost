import QLean.Generator.Analysis.OracleEventLocalTotalStage
import QLean.Generator.Implementation.BitonicTotalStageCompiler
import QLean.Generator.Implementation.OracleDiagonalTotalStageCompiler
import QLean.Generator.Implementation.OracleTotalProgramsCompiler

/-!
# event branch 局所全 dirty stage の compiler 一致
-/

namespace ProbabilityGeneratorQProof

namespace OracleEventTotalProgram

/-- pure slot 埋込みは既存正本と一致する。 -/
theorem slotToSortWord_eq (p : QParameters) (slot : Fin p.K) :
    slotToSortWord p slot = ProbabilityGeneratorQProof.slotToSortWord p slot := rfl

/-- pure register word 抽出は既存正本と一致する。 -/
theorem registerWordAt_eq (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) (slot : Fin p.K) :
    registerWordAt p register slot =
      ProbabilityGeneratorQProof.registerWordAt p register slot := rfl

/-- pure moved wire 列は既存正本と一致する。 -/
theorem movedWires_eq (p : QParameters) :
    movedWires p = ProbabilityGeneratorQProof.oracleMovedWires p := rfl

/-- pure membership equal wire 列は既存正本と一致する。 -/
theorem membershipEqualWires_eq (p : QParameters) :
    membershipEqualWires p = ProbabilityGeneratorQProof.membershipEqualWires p := rfl

/-- pure membership good wire 列は既存正本と一致する。 -/
theorem membershipGoodWires_eq (p : QParameters) :
    membershipGoodWires p = ProbabilityGeneratorQProof.membershipGoodWires p := rfl

/-- pure membership equal wire は既存正本と一致する。 -/
theorem membershipEqualWireAt_eq (p : QParameters) (slot : Fin p.K) :
    membershipEqualWireAt p slot =
      ProbabilityGeneratorQProof.membershipEqualWireAt p slot := rfl

/-- pure membership good wire は既存正本と一致する。 -/
theorem membershipGoodWireAt_eq (p : QParameters) (slot : Fin p.K) :
    membershipGoodWireAt p slot =
      ProbabilityGeneratorQProof.membershipGoodWireAt p slot := rfl

/-- pure absent wire は既存正本と一致する。 -/
theorem absentWire_eq (p : QParameters) :
    absentWire p = ProbabilityGeneratorQProof.oracleAbsentWire p := rfl

/-- pure present-other wire は既存正本と一致する。 -/
theorem presentOtherWire_eq (p : QParameters) :
    presentOtherWire p = ProbabilityGeneratorQProof.oraclePresentOtherWire p := rfl

/-- pure pair wire は既存正本と一致する。 -/
theorem pairWire_eq (p : QParameters) :
    pairWire p = ProbabilityGeneratorQProof.oraclePairWire p := rfl

/-- pure position wire は既存正本と一致する。 -/
theorem positionWire_eq (p : QParameters) :
    positionWire p = ProbabilityGeneratorQProof.oraclePositionWire p := rfl

/-- pure degree wire は既存正本と一致する。 -/
theorem degreeWireAt_eq (p : QParameters) (slot : Fin p.K) :
    degreeWireAt p slot = ProbabilityGeneratorQProof.oracleDegreeWireAt p slot := rfl

/-- pure candidate word は既存正本と一致する。 -/
theorem candidateWordAt_eq (p : QParameters) (word : Fin p.sortWordCount) :
    candidateWordAt p word = ProbabilityGeneratorQProof.candidateWordAt p word := rfl

/-- pure candidate marker は既存正本と一致する。 -/
theorem candidateMarkerWire_eq (p : QParameters) (word : Fin p.sortWordCount) :
    candidateMarkerWire p word =
      ProbabilityGeneratorQProof.candidateMarkerWire p word := rfl

/-- 一つの membership slot stage の compiler は既存正本と一致する。 -/
theorem compile_membershipSlot (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool) :
    (membershipSlot p register selectedSlot slot includePresentOther).compile =
      xorSiteSlotMatchAndGoodFlagAtIndexCircuit
        p register selectedSlot slot includePresentOther := by
  by_cases recordOther : includePresentOther && slot != selectedSlot
  · simp [membershipSlot, xorSiteSlotMatchAndGoodFlagAtIndexCircuit,
      membershipSlotCircuit, recordOther, registerWordAt_eq, movedWires_eq,
      membershipEqualWireAt_eq, membershipGoodWireAt_eq, presentOtherWire_eq,
      OracleDiagonalTotalProgram.presentWireAt_eq,
      DecoderTotalProgram.compareWorkWires_eq,
      DecoderTotalProgram.andScratchWires_eq,
      TotalReversibleStage.compile,
      TotalReversibleInstruction.toReversibleGate,
      TotalReversibleStage.compile_xorEqualityIntoTarget,
      TotalReversibleStage.compile_safeXorDoublyControlled]
  · simp [membershipSlot, xorSiteSlotMatchAndGoodFlagAtIndexCircuit,
      membershipSlotCircuit, recordOther, registerWordAt_eq, movedWires_eq,
      membershipEqualWireAt_eq, membershipGoodWireAt_eq,
      OracleDiagonalTotalProgram.presentWireAt_eq,
      DecoderTotalProgram.compareWorkWires_eq,
      DecoderTotalProgram.andScratchWires_eq,
      TotalReversibleStage.compile,
      TotalReversibleInstruction.toReversibleGate,
      TotalReversibleStage.compile_xorEqualityIntoTarget,
      TotalReversibleStage.compile_safeXorDoublyControlled]

/-- 全 slot membership stage の compiler は既存正本と一致する。 -/
theorem compile_membership (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    (membership p register selectedSlot includePresentOther).compile =
      xorMembershipMatchGoodAndAbsentFlagsCircuit
        p register selectedSlot includePresentOther := by
  rw [membership, TotalReversibleStage.compile]
  rw [xorMembershipMatchGoodAndAbsentFlagsCircuit,
    siteSlotMatchAndGoodFlagCircuits]
  congr 1
  · rw [TotalReversibleStage.compile_sequence]
    apply congrArg VerifiedCircuitCore.Circuit.sequence
    rw [List.map_map]
    apply List.map_congr_left
    intro slot _
    exact compile_membershipSlot p register selectedSlot slot includePresentOther
  · simpa [membershipGoodWires_eq, absentWire_eq,
      DecoderTotalProgram.andScratchWires_eq] using
        TotalReversibleStage.compile_positiveMultiControlledX
          (membershipGoodWires p) (DecoderTotalProgram.andScratchWires p)
          (absentWire p)

/-- candidate marker 初期化 stage の compiler は既存正本列と一致する。 -/
theorem compile_initializeCandidateMarkers (p : QParameters) :
    (initializeCandidateMarkers p).compile =
      Circuit.sequence (initializeCandidateMarkersTyped p) := by
  rw [initializeCandidateMarkers, TotalReversibleStage.compile_sequence]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  rw [initializeCandidateMarkersTyped, List.map_map]
  apply List.map_congr_left
  intro word _
  rfl

/-- 一つの candidate copy stage の compiler は既存正本と一致する。 -/
theorem compile_prepareCandidateSlot (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) (slot : Fin p.K) :
    (prepareCandidateSlot p register slot).compile =
      prepareCandidateSlotTyped p register slot := by
  simp [prepareCandidateSlot, prepareCandidateSlotTyped,
    candidateWordAt_eq, candidateMarkerWire_eq, slotToSortWord_eq,
    registerWordAt_eq, OracleDiagonalTotalProgram.presentWireAt_eq,
    TotalReversibleStage.compile, OracleTotalProgram.compile_controlledXorCopy,
    TotalReversibleStage.compile_safeXorControlled]

/-- candidate 準備 stage の compiler は既存正本と一致する。 -/
theorem compile_prepareCandidates (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    (prepareCandidates p register).compile =
      xorConfigurationIntoCandidateRegisterCircuit p register := by
  rw [prepareCandidates, xorConfigurationIntoCandidateRegisterCircuit,
    TotalReversibleStage.compile]
  congr 1
  · exact compile_initializeCandidateMarkers p
  · rw [TotalReversibleStage.compile_sequence, prepareCandidateSlotsTyped]
    apply congrArg VerifiedCircuitCore.Circuit.sequence
    rw [List.map_map]
    apply List.map_congr_left
    intro slot _
    exact compile_prepareCandidateSlot p register slot

/-- column candidate 更新 stage の compiler は既存正本更新と一致する。 -/
theorem compile_modifyColumnCandidate (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :
    (modifyColumnCandidate p register slot collision).compile =
      (let candidate := ProbabilityGeneratorQProof.candidateWordAt p
          (ProbabilityGeneratorQProof.slotToSortWord p slot)
       let removeSource := controlledXorCopy (oracleBranchWire p)
          (ProbabilityGeneratorQProof.registerWordAt p register slot)
          (candidate.take p.wordWidth)
       if collision then
         .seq removeSource <| ReversibleCircuit.safeCnot (oracleBranchWire p)
           (ProbabilityGeneratorQProof.candidateMarkerWire p
             (ProbabilityGeneratorQProof.slotToSortWord p slot))
       else
         .seq removeSource <| controlledXorCopy (oracleBranchWire p)
           (oracleMovedWires p) (candidate.take p.wordWidth)) := by
  cases collision <;>
    simp [modifyColumnCandidate, candidateWordAt_eq, slotToSortWord_eq,
      registerWordAt_eq, OracleDiagonalTotalProgram.branchWire_eq, movedWires_eq,
      candidateMarkerWire_eq, TotalReversibleStage.compile,
      OracleTotalProgram.compile_controlledXorCopy,
      TotalReversibleStage.compile_safeXorControlled]

/-- row collision の degree 一段 stage は既存正本命令と一致する。 -/
theorem compile_appendMovedCandidateAtDegree (p : QParameters)
    (degreeSlot : Fin (p.K - 1)) :
    (appendMovedCandidateAtDegree p degreeSlot).compile =
      (let degreeIndex : Fin p.K :=
          ⟨degreeSlot.val, lt_of_lt_of_le degreeSlot.isLt (Nat.sub_le _ _)⟩
       let candidateIndex : Fin p.sortWordCount :=
          ⟨degreeSlot.val + 1, by
            have : degreeSlot.val + 1 < p.K := by omega
            exact lt_of_lt_of_le this p.K_le_sortWordCount⟩
       let candidate := ProbabilityGeneratorQProof.candidateWordAt p candidateIndex
       let compute := ReversibleCircuit.positiveMultiControlledX
          [oracleBranchWire p, oracleDegreeWireAt p degreeIndex]
          (decoderAndScratchWires p) (oraclePairWire p)
       let use := .seq (controlledXorCopy (oraclePairWire p) (oracleMovedWires p)
          (candidate.take p.wordWidth))
          (ReversibleCircuit.safeCnot (oraclePairWire p)
            (ProbabilityGeneratorQProof.candidateMarkerWire p candidateIndex))
       Circuit.computeUseUncompute id compute use) := by
  simp [appendMovedCandidateAtDegree, candidateWordAt_eq, candidateMarkerWire_eq,
    degreeWireAt_eq, pairWire_eq, movedWires_eq,
    OracleDiagonalTotalProgram.branchWire_eq,
    DecoderTotalProgram.andScratchWires_eq,
    TotalReversibleStage.compile_computeUseUncompute,
    TotalReversibleStage.compile,
    TotalReversibleStage.compile_positiveMultiControlledX,
    OracleTotalProgram.compile_controlledXorCopy,
    TotalReversibleStage.compile_safeXorControlled]

/-- row candidate 更新 stage の compiler は既存正本更新と一致する。 -/
theorem compile_modifyRowCandidate (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :
    (modifyRowCandidate p register slot collision).compile =
      (if collision then
        Circuit.sequence <| (List.finRange (p.K - 1)).map fun degreeSlot =>
          let degreeIndex : Fin p.K :=
            ⟨degreeSlot.val, lt_of_lt_of_le degreeSlot.isLt (Nat.sub_le _ _)⟩
          let candidateIndex : Fin p.sortWordCount :=
            ⟨degreeSlot.val + 1, by
              have : degreeSlot.val + 1 < p.K := by omega
              exact lt_of_lt_of_le this p.K_le_sortWordCount⟩
          let candidate := ProbabilityGeneratorQProof.candidateWordAt p candidateIndex
          let compute := ReversibleCircuit.positiveMultiControlledX
            [oracleBranchWire p, oracleDegreeWireAt p degreeIndex]
            (decoderAndScratchWires p) (oraclePairWire p)
          let append := controlledXorCopy (oraclePairWire p) (oracleMovedWires p)
            (candidate.take p.wordWidth)
          let marker := ReversibleCircuit.safeCnot (oraclePairWire p)
            (ProbabilityGeneratorQProof.candidateMarkerWire p candidateIndex)
          Circuit.computeUseUncompute id compute <| .seq append marker
       else
        let candidate := ProbabilityGeneratorQProof.candidateWordAt p
          (ProbabilityGeneratorQProof.slotToSortWord p slot)
        .seq (controlledXorCopy (oracleBranchWire p)
          (ProbabilityGeneratorQProof.registerWordAt p register slot)
          (candidate.take p.wordWidth)) <|
        controlledXorCopy (oracleBranchWire p) (oracleMovedWires p)
          (candidate.take p.wordWidth)) := by
  cases collision with
  | false =>
      simp [modifyRowCandidate, candidateWordAt_eq, slotToSortWord_eq,
        registerWordAt_eq, movedWires_eq, OracleDiagonalTotalProgram.branchWire_eq,
        TotalReversibleStage.compile, OracleTotalProgram.compile_controlledXorCopy]
  | true =>
      rw [modifyRowCandidate, if_pos rfl, TotalReversibleStage.compile_sequence]
      apply congrArg VerifiedCircuitCore.Circuit.sequence
      rw [List.map_map]
      apply List.map_congr_left
      intro degreeSlot _
      exact compile_appendMovedCandidateAtDegree p degreeSlot

/-- sorted candidate の有効 prefix を出力へ写す stage は既存正本列と一致する。 -/
theorem compile_writeCandidatePrefix (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K) :
    (TotalReversibleStage.sequence <|
      (List.finRange outputDegree).map fun outputSlot =>
        let registerSlot : Fin p.K :=
          ⟨outputSlot.val, lt_of_lt_of_le outputSlot.isLt outputDegreeLe⟩
        let candidateSlot : Fin p.sortWordCount :=
          ⟨outputSlot.val,
            lt_of_lt_of_le registerSlot.isLt p.K_le_sortWordCount⟩
        OracleTotalProgram.controlledXorCopy (pairWire p)
          ((candidateWordAt p candidateSlot).take p.wordWidth)
          (registerWordAt p output registerSlot)).compile =
      Circuit.sequence ((List.finRange outputDegree).map fun outputSlot =>
        let registerSlot : Fin p.K :=
          ⟨outputSlot.val, lt_of_lt_of_le outputSlot.isLt outputDegreeLe⟩
        let candidateSlot : Fin p.sortWordCount :=
          ⟨outputSlot.val,
            lt_of_lt_of_le registerSlot.isLt p.K_le_sortWordCount⟩
        controlledXorCopy (oraclePairWire p)
          ((ProbabilityGeneratorQProof.candidateWordAt p candidateSlot).take p.wordWidth)
          (ProbabilityGeneratorQProof.registerWordAt p output registerSlot)) := by
  rw [TotalReversibleStage.compile_sequence]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  rw [List.map_map]
  apply List.map_congr_left
  intro outputSlot _
  simpa [pairWire_eq, candidateWordAt_eq, registerWordAt_eq] using
    OracleTotalProgram.compile_controlledXorCopy (pairWire p)
      ((candidateWordAt p
        ⟨outputSlot.val, lt_of_lt_of_le
          (lt_of_lt_of_le outputSlot.isLt outputDegreeLe) p.K_le_sortWordCount⟩).take
        p.wordWidth)
      (registerWordAt p output
        ⟨outputSlot.val, lt_of_lt_of_le outputSlot.isLt outputDegreeLe⟩)

/-- delimiter writer stage の compiler は既存正本 writer と一致する。 -/
theorem compile_writeSortedDelimiter (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth) (degreeChange : Int) :
    (writeSortedDelimiter p output outputLength outputActive degreeChange).compile =
      xorSortedCandidatesAsDelimiterIntoOutputCircuit
        p output outputLength outputActive degreeChange := by
  rw [writeSortedDelimiter, xorSortedCandidatesAsDelimiterIntoOutputCircuit,
    TotalReversibleStage.compile_sequence]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  rw [List.map_map]
  apply List.map_congr_left
  intro degreeSlot _
  simp only [Function.comp_apply]
  by_cases valid : (1 : Int) ≤
      Int.ofNat (degreeSlot.val + 1) + degreeChange ∧
      Int.ofNat (degreeSlot.val + 1) + degreeChange ≤ Int.ofNat p.K
  · simp only [dif_pos valid]
    have outputDegreeLe :
        (Int.ofNat (degreeSlot.val + 1) + degreeChange).toNat ≤ p.K :=
      Int.toNat_le.mpr valid.2
    rw [TotalReversibleStage.compile_computeUseUncompute]
    rw [TotalReversibleStage.compile_positiveMultiControlledX]
    rw [TotalReversibleStage.compile]
    rw [compile_writeCandidatePrefix p output _ outputDegreeLe]
    simp [pairWire_eq, degreeWireAt_eq,
      OracleDiagonalTotalProgram.branchWire_eq,
      DecoderTotalProgram.andScratchWires_eq,
      TotalReversibleStage.compile,
      TotalReversibleStage.compile_safeXorControlled]
  · simp only [dif_neg valid]
    rfl

/-- selector writer stage の compiler は既存正本 writer と一致する。 -/
theorem compile_writeMovedPosition (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth)) :
    (writeMovedPosition p offset outputSelector).compile =
      xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector := by
  rw [writeMovedPosition, xorMovedMemberPositionIntoSelectorOutputCircuit,
    TotalReversibleStage.compile_sequence]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  rw [List.map_map]
  apply List.map_congr_left
  intro slot _
  simp [candidateWordAt_eq, candidateMarkerWire_eq, slotToSortWord_eq,
    movedWires_eq, positionWire_eq, pairWire_eq,
    OracleDiagonalTotalProgram.branchWire_eq,
    DecoderTotalProgram.compareWorkWires_eq,
    DecoderTotalProgram.andScratchWires_eq,
    TotalReversibleStage.compile_computeUseUncompute,
    TotalReversibleStage.compile,
    TotalReversibleInstruction.toReversibleGate,
    TotalReversibleStage.compile_xorEqualityIntoTarget,
    TotalReversibleStage.compile_positiveMultiControlledX,
    OracleTotalProgram.compile_controlledXorConstant]

/-- column event stage の compiler は既存正本 event と一致する。 -/
theorem compile_columnEvent (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    (columnEventWithSort p slot offset (BitonicTotalProgram.sort p)).compile =
      applyColumnEventReferenceAndRestoreWorkCircuit p slot offset := by
  simp [columnEventWithSort, applyColumnEventReferenceAndRestoreWorkCircuit,
    registerWordAt_eq, movedWires_eq, absentWire_eq, presentOtherWire_eq,
    OraclePersistentTotalProgram.columnKeyWires_eq,
    OraclePersistentTotalProgram.degreeConditionWire_eq,
    OracleDiagonalTotalProgram.columnSelectorWires_eq,
    OracleDiagonalTotalProgram.rowOutputWires_eq,
    OracleDiagonalTotalProgram.selectorOutputWires_eq,
    OracleDiagonalTotalProgram.selectedWire_eq,
    OracleDiagonalTotalProgram.presentWireAt_eq,
    OracleDiagonalTotalProgram.branchWire_eq,
    OracleDiagonalTotalProgram.activeWire_eq,
    DecoderTotalProgram.legalWire_eq,
    DecoderTotalProgram.andScratchWires_eq,
    TotalReversibleStage.compile_computeUseUncompute,
    TotalReversibleStage.compile,
    OracleTotalProgram.compile_xorSelectorEqualsConstant,
    TotalReversibleStage.compile_xorCopy,
    TotalReversibleStage.compile_incrementWordMod2PowInPlace,
    compile_membership, TotalReversibleStage.compile_positiveMultiControlledX,
    compile_prepareCandidates, compile_modifyColumnCandidate,
    BitonicTotalProgram.compile_sort,
    compile_writeSortedDelimiter, compile_writeMovedPosition]

/-- row event stage の compiler は既存正本 event と一致する。 -/
theorem compile_rowEvent (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    (rowEventWithSort p slot offset (BitonicTotalProgram.sort p)).compile =
      applyRowEventReferenceAndRestoreWorkCircuit p slot offset := by
  simp [rowEventWithSort, applyRowEventReferenceAndRestoreWorkCircuit,
    registerWordAt_eq, movedWires_eq, absentWire_eq,
    OraclePersistentTotalProgram.systemWires_eq,
    OraclePersistentTotalProgram.columnKeyWires_eq,
    OraclePersistentTotalProgram.degreeConditionWire_eq,
    OracleDiagonalTotalProgram.rowSelectorWires_eq,
    OracleDiagonalTotalProgram.columnSelectorWires_eq,
    OracleDiagonalTotalProgram.selectedWire_eq,
    OracleDiagonalTotalProgram.presentWireAt_eq,
    OracleDiagonalTotalProgram.branchWire_eq,
    OracleDiagonalTotalProgram.keySignalWire_eq,
    DecoderTotalProgram.legalWire_eq,
    DecoderTotalProgram.andScratchWires_eq,
    TotalReversibleStage.compile_computeUseUncompute,
    TotalReversibleStage.compile,
    OracleTotalProgram.compile_xorSelectorEqualsConstant,
    TotalReversibleStage.compile_xorCopy,
    TotalReversibleStage.compile_decrementWordMod2PowInPlace,
    compile_membership, TotalReversibleStage.compile_positiveMultiControlledX,
    compile_prepareCandidates, compile_modifyRowCandidate,
    BitonicTotalProgram.compile_sort,
    compile_writeSortedDelimiter, compile_writeMovedPosition]

/-- column event を全入力の基底置換へ結ぶ component。 -/
def columnEventPermutationComponent (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :=
  (columnEventWithSort p slot offset (BitonicTotalProgram.sort p)).permutationComponent

/-- row event を全入力の基底置換へ結ぶ component。 -/
def rowEventPermutationComponent (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :=
  (rowEventWithSort p slot offset (BitonicTotalProgram.sort p)).permutationComponent

end OracleEventTotalProgram

end ProbabilityGeneratorQProof
