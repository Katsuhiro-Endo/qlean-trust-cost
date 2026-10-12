import QLean.Generator.Analysis.OracleDiagonalTotalStage

/-!
# event branch の局所全 dirty stage

membership、candidate 準備・更新、出力 writer を回路構文木から独立に定義する。
bitonic sort 自体は別の純粋 stage として引数に受け、event 全体の直接子を明示する。
-/

namespace ProbabilityGeneratorQProof

namespace OracleEventTotalProgram

/-- `Fin K` の slot を padding 込み sort word 添字へ埋め込む。 -/
def slotToSortWord (p : QParameters) (slot : Fin p.K) : Fin p.sortWordCount :=
  ⟨slot.val, lt_of_lt_of_le slot.isLt p.K_le_sortWordCount⟩

/-- 固定幅 register から指定 slot の word を取り出す。 -/
def registerWordAt (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) (slot : Fin p.K) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (register.drop (slot.val * p.wordWidth)).take p.wordWidth

/-- moved word の wire 列。 -/
def movedWires (p : QParameters) : List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.movedWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved).ancillaWire index

/-- membership の word 等値 flag 列。 -/
def membershipEqualWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.membershipEqWidth).map fun index =>
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).membershipEqual).ancillaWire index

/-- membership の有効一致 flag 列。 -/
def membershipGoodWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.membershipGoodWidth).map fun index =>
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).membershipGood).ancillaWire index

/-- 指定 slot の membership 等値 flag。 -/
def membershipEqualWireAt (p : QParameters) (slot : Fin p.K) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipEqual).ancillaWire slot

/-- 指定 slot の membership good flag。 -/
def membershipGoodWireAt (p : QParameters) (slot : Fin p.K) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipGood).ancillaWire slot

/-- moved word が全 present word と異なることを示す flag。 -/
def absentWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  OraclePersistentTotalProgram.singletonWire p (OracleWorkLayout.canonical p).absent

/-- 選択 slot 以外で moved word が現れたことを示す flag。 -/
def presentOtherWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  OraclePersistentTotalProgram.singletonWire p
    (OracleWorkLayout.canonical p).presentOther

/-- branch と degree の組に対する一時 flag。 -/
def pairWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).pair).ancillaWire
    ⟨0, by simpa [QParameters.pairWidth] using p.K_pos⟩

/-- moved word の sorted 位置に対する一時 flag。 -/
def positionWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).positionMatch).ancillaWire
      ⟨0, by simpa [QParameters.positionMatchWidth] using p.K_pos⟩

/-- 指定 degree の one-hot wire。 -/
def degreeWireAt (p : QParameters) (slot : Fin p.K) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).degree).ancillaWire slot

/-- candidate word の一 bit。 -/
def candidateWordWire (p : QParameters)
    (word : Fin p.sortWordCount) (bit : Fin (p.wordWidth + 1)) :
    Wire p.ancillaWidth p.systemWidth :=
  let localIndex : Fin p.candidateWidth :=
    ⟨word.val * (p.wordWidth + 1) + bit.val, by
      simp only [QParameters.candidateWidth]
      nlinarith [word.isLt, bit.isLt]⟩
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate).ancillaWire localIndex

/-- 型安全な添字で指定した marker 付き candidate word。 -/
def candidateWordAt (p : QParameters) (word : Fin p.sortWordCount) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange (p.wordWidth + 1)).map fun bit => candidateWordWire p word bit

/-- candidate word 末尾の padding marker。 -/
def candidateMarkerWire (p : QParameters) (word : Fin p.sortWordCount) :
    Wire p.ancillaWidth p.systemWidth :=
  candidateWordWire p word ⟨p.wordWidth, by omega⟩

/-- 一つの slot について membership の等値・good・present-other を XOR 計算する。 -/
def membershipSlot (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let equal := TotalReversibleStage.xorEqualityIntoTarget (movedWires p)
    (registerWordAt p register slot) (DecoderTotalProgram.compareWorkWires p)
    (DecoderTotalProgram.andScratchWires p) (membershipEqualWireAt p slot)
  let initializeGood := .instruction (.xorOne (membershipGoodWireAt p slot))
  let removeMatch := TotalReversibleStage.safeXorDoublyControlled
    (OracleDiagonalTotalProgram.presentWireAt p slot)
    (membershipEqualWireAt p slot) (membershipGoodWireAt p slot)
  let recordOther := if includePresentOther && slot != selectedSlot then
    TotalReversibleStage.safeXorDoublyControlled
      (OracleDiagonalTotalProgram.presentWireAt p slot)
      (membershipEqualWireAt p slot) (presentOtherWire p)
  else .identity
  .seq equal <| .seq initializeGood <| .seq removeMatch recordOther

/-- 全 slot の membership と absent flag を順に計算する。 -/
def membership (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  .seq (TotalReversibleStage.sequence <| (List.finRange p.K).map fun slot =>
    membershipSlot p register selectedSlot slot includePresentOther) <|
    TotalReversibleStage.positiveMultiControlledX (membershipGoodWires p)
      (DecoderTotalProgram.andScratchWires p) (absentWire p)

/-- 全 candidate marker を 1 へ XOR 初期化する。 -/
def initializeCandidateMarkers (p : QParameters) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  TotalReversibleStage.sequence <| (List.finRange p.sortWordCount).map fun word =>
    .instruction (.xorOne (candidateMarkerWire p word))

/-- 一つの present word を対応 candidate へ条件付き XOR copy する。 -/
def prepareCandidateSlot (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) (slot : Fin p.K) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let target := candidateWordAt p (slotToSortWord p slot)
  let copy := OracleTotalProgram.controlledXorCopy
    (OracleDiagonalTotalProgram.presentWireAt p slot)
    (registerWordAt p register slot) (target.take p.wordWidth)
  let marker := TotalReversibleStage.safeXorControlled
    (OracleDiagonalTotalProgram.presentWireAt p slot)
    (candidateMarkerWire p (slotToSortWord p slot))
  .seq copy marker

/-- register の配置を padding marker 付き candidate register へ XOR する。 -/
def prepareCandidates (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  .seq (initializeCandidateMarkers p) <|
    TotalReversibleStage.sequence <| (List.finRange p.K).map fun slot =>
      prepareCandidateSlot p register slot

/-- column event の candidate 一点更新。 -/
def modifyColumnCandidate (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let candidate := candidateWordAt p (slotToSortWord p slot)
  let removeSource := OracleTotalProgram.controlledXorCopy
    (OracleDiagonalTotalProgram.branchWire p) (registerWordAt p register slot)
    (candidate.take p.wordWidth)
  if collision then
    .seq removeSource <| TotalReversibleStage.safeXorControlled
      (OracleDiagonalTotalProgram.branchWire p)
      (candidateMarkerWire p (slotToSortWord p slot))
  else
    .seq removeSource <| OracleTotalProgram.controlledXorCopy
      (OracleDiagonalTotalProgram.branchWire p) (movedWires p)
      (candidate.take p.wordWidth)

/-- row collision event の degree ごとの candidate 追加。 -/
def appendMovedCandidateAtDegree (p : QParameters) (degreeSlot : Fin (p.K - 1)) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let degreeIndex : Fin p.K :=
    ⟨degreeSlot.val, lt_of_lt_of_le degreeSlot.isLt (Nat.sub_le _ _)⟩
  let candidateIndex : Fin p.sortWordCount :=
    ⟨degreeSlot.val + 1, by
      have : degreeSlot.val + 1 < p.K := by omega
      exact lt_of_lt_of_le this p.K_le_sortWordCount⟩
  let compute := TotalReversibleStage.positiveMultiControlledX
    [OracleDiagonalTotalProgram.branchWire p,
      degreeWireAt p degreeIndex]
    (DecoderTotalProgram.andScratchWires p) (pairWire p)
  let use := .seq (OracleTotalProgram.controlledXorCopy (pairWire p) (movedWires p)
      ((candidateWordAt p candidateIndex).take p.wordWidth)) <|
    TotalReversibleStage.safeXorControlled (pairWire p)
      (candidateMarkerWire p candidateIndex)
  TotalReversibleStage.computeUseUncompute compute use

/-- row event の candidate 更新。 -/
def modifyRowCandidate (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  if collision then
    TotalReversibleStage.sequence <| (List.finRange (p.K - 1)).map fun degreeSlot =>
      appendMovedCandidateAtDegree p degreeSlot
  else
    let candidate := candidateWordAt p (slotToSortWord p slot)
    .seq (OracleTotalProgram.controlledXorCopy
      (OracleDiagonalTotalProgram.branchWire p) (registerWordAt p register slot)
      (candidate.take p.wordWidth)) <|
    OracleTotalProgram.controlledXorCopy
      (OracleDiagonalTotalProgram.branchWire p) (movedWires p)
      (candidate.take p.wordWidth)

/-- degree と branch の組に応じて sorted candidate を delimiter 出力へ XOR する。 -/
def writeSortedDelimiter (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth) (degreeChange : Int) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  TotalReversibleStage.sequence <| (List.finRange p.K).map fun degreeSlot =>
    let inputDegree := degreeSlot.val + 1
    let outputDegreeInt := Int.ofNat inputDegree + degreeChange
    if valid : (1 : Int) ≤ outputDegreeInt ∧ outputDegreeInt ≤ Int.ofNat p.K then
      let outputDegree := outputDegreeInt.toNat
      have outputDegreeLe : outputDegree ≤ p.K := by
        dsimp only [outputDegree]
        exact Int.toNat_le.mpr valid.2
      let compute := TotalReversibleStage.positiveMultiControlledX
        [OracleDiagonalTotalProgram.branchWire p,
          degreeWireAt p degreeSlot]
        (DecoderTotalProgram.andScratchWires p) (pairWire p)
      let dataUse := TotalReversibleStage.sequence <|
        (List.finRange outputDegree).map fun outputSlot =>
          let registerSlot : Fin p.K :=
            ⟨outputSlot.val, lt_of_lt_of_le outputSlot.isLt outputDegreeLe⟩
          let candidateSlot : Fin p.sortWordCount :=
            ⟨outputSlot.val, lt_of_lt_of_le registerSlot.isLt p.K_le_sortWordCount⟩
          OracleTotalProgram.controlledXorCopy (pairWire p)
            ((candidateWordAt p candidateSlot).take p.wordWidth)
            (registerWordAt p output registerSlot)
      have delimiterLt : p.wordWidth * outputDegree < output.length := by
        rw [outputLength]
        calc
          p.wordWidth * outputDegree ≤ p.wordWidth * p.K :=
            Nat.mul_le_mul_left p.wordWidth outputDegreeLe
          _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _
          _ = p.systemWidth := rfl
      let delimiter := output.get ⟨p.wordWidth * outputDegree, delimiterLt⟩
      let use := .seq dataUse <|
        .seq (TotalReversibleStage.safeXorControlled (pairWire p) delimiter) <|
          TotalReversibleStage.safeXorControlled (pairWire p) outputActive
      TotalReversibleStage.computeUseUncompute compute use
    else .identity

/-- moved word の sorted 位置から selector 定数を XOR 出力する。 -/
def writeMovedPosition (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth)) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  TotalReversibleStage.sequence <| (List.finRange p.K).map fun slot =>
    let word := candidateWordAt p (slotToSortWord p slot)
    let equal := TotalReversibleStage.xorEqualityIntoTarget (movedWires p)
      (word.take p.wordWidth) (DecoderTotalProgram.compareWorkWires p)
      (DecoderTotalProgram.andScratchWires p) (positionWire p)
    let marker := candidateMarkerWire p (slotToSortWord p slot)
    let invert := TotalReversibleStage.instruction (.xorOne marker)
    let markerUse := .seq invert <| .seq
      (TotalReversibleStage.positiveMultiControlledX
        [OracleDiagonalTotalProgram.branchWire p, positionWire p, marker]
        (DecoderTotalProgram.andScratchWires p) (pairWire p)) invert
    let compute := .seq equal markerUse
    let use := OracleTotalProgram.controlledXorConstant (pairWire p)
      outputSelector (6 * slot.val + offset)
    TotalReversibleStage.computeUseUncompute compute use

/-! ## Named pure boundaries for candidate construction and selector output -/

/-- Pure candidate initialization: padding markers followed by the controlled
copies of every present register word. -/
def candidatePreparationStage (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  prepareCandidates p register

/-- Pure column-candidate replacement/collision update. -/
def columnCandidateModificationStage (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  modifyColumnCandidate p register slot collision

/-- Pure row-candidate replacement/collision update. -/
def rowCandidateModificationStage (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  modifyRowCandidate p register slot collision

/-- Independent pure operator for candidate initialization. -/
noncomputable def candidatePreparationAnalyticOperator (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :=
  (candidatePreparationStage p register).analyticOperator

/-- Independent pure operator for a column candidate update. -/
noncomputable def columnCandidateModificationAnalyticOperator (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :=
  (columnCandidateModificationStage p register slot collision).analyticOperator

/-- Independent pure operator for a row candidate update. -/
noncomputable def rowCandidateModificationAnalyticOperator (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :=
  (rowCandidateModificationStage p register slot collision).analyticOperator

/-- Complete column candidate-word construction in execution order. -/
def columnCandidateWordsStage (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  .seq (candidatePreparationStage p register)
    (columnCandidateModificationStage p register slot collision)

/-- Complete row candidate-word construction in execution order. -/
def rowCandidateWordsStage (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  .seq (candidatePreparationStage p register)
    (rowCandidateModificationStage p register slot collision)

/-- Independent pure operator for complete column candidate construction. -/
noncomputable def columnCandidateWordsAnalyticOperator (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :=
  (columnCandidateWordsStage p register slot collision).analyticOperator

/-- Independent pure operator for complete row candidate construction. -/
noncomputable def rowCandidateWordsAnalyticOperator (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (collision : Bool) :=
  (rowCandidateWordsStage p register slot collision).analyticOperator

/-- Pure moved-position selector-output writer. -/
def movedSelectorOutputStage (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth)) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  writeMovedPosition p offset outputSelector

/-- Independent pure operator for the moved-position selector-output writer. -/
noncomputable def movedSelectorOutputAnalyticOperator (p : QParameters)
    (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth)) :=
  (movedSelectorOutputStage p offset outputSelector).analyticOperator

/-- column event を、独立な sort stage を直接子として合成する。 -/
def columnEventWithSort (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (sorting : TotalReversibleStage p.ancillaWidth p.systemWidth) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let collision := offset.val % 2 = 1
  let vertical := 4 ≤ offset.val
  let register := OraclePersistentTotalProgram.columnKeyWires p
  let selector := OracleTotalProgram.xorSelectorEqualsConstant
    (OracleDiagonalTotalProgram.columnSelectorWires p)
    (DecoderTotalProgram.andScratchWires p) (6 * slot.val + offset.val)
    (OracleDiagonalTotalProgram.selectedWire p)
  let movedCopy := TotalReversibleStage.xorCopy
    (registerWordAt p register slot) (movedWires p)
  let coordinate := if vertical then (movedWires p).drop p.q |>.take p.q
    else (movedWires p).take p.q
  let move := TotalReversibleStage.incrementWordMod2PowInPlace coordinate
    (DecoderTotalProgram.andScratchWires p)
  let membershipStage := membership p register slot true
  let condition := if collision then presentOtherWire p else absentWire p
  let controls := [DecoderTotalProgram.legalWire p,
    OracleDiagonalTotalProgram.selectedWire p,
    OracleDiagonalTotalProgram.presentWireAt p slot, condition] ++
      if collision then [OraclePersistentTotalProgram.degreeConditionWire p] else []
  let branch := TotalReversibleStage.positiveMultiControlledX controls
    (DecoderTotalProgram.andScratchWires p) (OracleDiagonalTotalProgram.branchWire p)
  let compute := .seq selector <| .seq movedCopy <| .seq move <|
    .seq membershipStage <| .seq branch <| .seq (prepareCandidates p register) <|
      .seq (modifyColumnCandidate p register slot collision) sorting
  let use := .seq (writeSortedDelimiter p (OracleDiagonalTotalProgram.rowOutputWires p)
      (by simp [OracleDiagonalTotalProgram.rowOutputWires])
      (OracleDiagonalTotalProgram.activeWire p) (if collision then -1 else 0)) <|
    writeMovedPosition p offset.val (OracleDiagonalTotalProgram.selectorOutputWires p)
  TotalReversibleStage.computeUseUncompute compute use

/-- row event を、独立な sort stage を直接子として合成する。 -/
def rowEventWithSort (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (sorting : TotalReversibleStage p.ancillaWidth p.systemWidth) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let collision := offset.val % 2 = 1
  let vertical := 4 ≤ offset.val
  let register := OraclePersistentTotalProgram.systemWires p
  let selector := OracleTotalProgram.xorSelectorEqualsConstant
    (OracleDiagonalTotalProgram.rowSelectorWires p)
    (DecoderTotalProgram.andScratchWires p) (6 * slot.val + offset.val)
    (OracleDiagonalTotalProgram.selectedWire p)
  let movedCopy := TotalReversibleStage.xorCopy
    (registerWordAt p register slot) (movedWires p)
  let coordinate := if vertical then (movedWires p).drop p.q |>.take p.q
    else (movedWires p).take p.q
  let move := TotalReversibleStage.decrementWordMod2PowInPlace coordinate
    (DecoderTotalProgram.andScratchWires p)
  let membershipStage := membership p register slot false
  let controls := [DecoderTotalProgram.legalWire p,
    OracleDiagonalTotalProgram.selectedWire p,
    OracleDiagonalTotalProgram.presentWireAt p slot, absentWire p] ++
      if collision then [OraclePersistentTotalProgram.degreeConditionWire p] else []
  let branch := TotalReversibleStage.positiveMultiControlledX controls
    (DecoderTotalProgram.andScratchWires p) (OracleDiagonalTotalProgram.branchWire p)
  let compute := .seq selector <| .seq movedCopy <| .seq move <|
    .seq membershipStage <| .seq branch <| .seq (prepareCandidates p register) <|
      .seq (modifyRowCandidate p register slot collision) sorting
  let use := .seq (writeSortedDelimiter p
      (OraclePersistentTotalProgram.columnKeyWires p)
      (by simp [OraclePersistentTotalProgram.columnKeyWires])
      (OracleDiagonalTotalProgram.keySignalWire p) (if collision then 1 else 0)) <|
    writeMovedPosition p offset.val (OracleDiagonalTotalProgram.columnSelectorWires p)
  TotalReversibleStage.computeUseUncompute compute use

end OracleEventTotalProgram

end ProbabilityGeneratorQProof
