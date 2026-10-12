import QLean.Generator.Implementation.QDecoderCircuit
import QLean.Generator.Analysis.QOracleReference

/-!
# column/row oracleの基本ゲート正本回路

compact decoder、membership、candidate生成、bitonic sort、出力再符号化を
branchごとのcompute--use--uncomputeとして合成する。高水準oracleを新しいゲートとして
追加せず、返り値はすべて`Circuit ReversibleGate`またはその`PrimitiveGate`翻訳である。
-/

namespace ProbabilityGeneratorQProof

/-- system register全体の型安全なwire列。 -/
def systemWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.systemWidth).map fun index => QLayout.systemWire p index

/-- column key register全体の型安全なwire列。 -/
def columnKeyWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.systemWidth).map fun index => columnKeyWire p index

/-- row output register全体の型安全なwire列。 -/
def rowOutputWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.systemWidth).map fun index => rowOutputWire p index

/-- row selector register全体の型安全なwire列。 -/
def rowSelectorWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.selectorWidth).map fun index => rowSelectorWire p index

/-- column selector register全体の型安全なwire列。 -/
def columnSelectorWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.selectorWidth).map fun index => columnSelectorWire p index

/-- oracle selector output register全体の型安全なwire列。 -/
def selectorOutputWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.selectorWidth).map fun index => selectorOutputWire p index

/-- `Fin K`のslotをpadding込みsort word添字へ型安全に埋め込む。 -/
def slotToSortWord (p : QParameters) (slot : Fin p.K) : Fin p.sortWordCount :=
  ⟨slot.val, lt_of_lt_of_le slot.isLt p.K_le_sortWordCount⟩

/-- 固定幅registerから指定slotの`2q` bit wordを型安全に切り出す。 -/
def registerWordAt (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) (slot : Fin p.K) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (register.drop (slot.val * p.wordWidth)).take p.wordWidth

/-- 指定slotのpresent flag wireを型安全に得る。 -/
def oraclePresentWireAt (p : QParameters) (slot : Fin p.K) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).present).ancillaWire slot

/-- 指定degree添字のone-hot wireを型安全に得る。 -/
def oracleDegreeWireAt (p : QParameters) (slot : Fin p.K) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).degree).ancillaWire slot

/-- 指定slotのmembership等値flag wireを型安全に得る。 -/
def membershipEqualWireAt (p : QParameters) (slot : Fin p.K) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipEqual).ancillaWire slot

/-- 指定slotのmembership good flag wireを型安全に得る。 -/
def membershipGoodWireAt (p : QParameters) (slot : Fin p.K) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipGood).ancillaWire slot

/-- oracle workのpresent flag wire列。 -/
def oraclePresentWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.presentWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).present).ancillaWire index

/-- oracle workのmoved site wire列。 -/
def oracleMovedWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.movedWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved).ancillaWire index

/-- membership用word等値flag wire列。 -/
def membershipEqualWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.membershipEqWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).membershipEqual).ancillaWire index

/-- membership用有効一致flag wire列。 -/
def membershipGoodWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.membershipGoodWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).membershipGood).ancillaWire index

/-- oracle work内の幅1 sliceからwireを取り出す補助。 -/
def oracleSingletonWire (p : QParameters)
    (slice : RegisterSlice p.oracleWorkWidth 1) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice slice).ancillaWire 0

/-- degree境界条件flag wire。 -/
def oracleDegreeConditionWire (p : QParameters) :
    Wire p.ancillaWidth p.systemWidth :=
  oracleSingletonWire p (OracleWorkLayout.canonical p).degreeCondition

/-- 定数1としてcompute scope内で使うwire。 -/
def oracleOneWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  oracleSingletonWire p (OracleWorkLayout.canonical p).constantOne

/-- selector等値比較結果wire。 -/
def oracleSelectedWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  oracleSingletonWire p (OracleWorkLayout.canonical p).selected

/-- moved siteが既存wordに含まれないことを表すwire。 -/
def oracleAbsentWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  oracleSingletonWire p (OracleWorkLayout.canonical p).absent

/-- selected slot以外でmoved siteが見つかったことを表すwire。 -/
def oraclePresentOtherWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  oracleSingletonWire p (OracleWorkLayout.canonical p).presentOther

/-- 現在branchの全条件AND wire。 -/
def oracleBranchWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  oracleSingletonWire p (OracleWorkLayout.canonical p).branch

/-- `K>0`から構成した、sorted位置一致sliceの型安全な先頭wire。 -/
def oraclePositionWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).positionMatch).ancillaWire
      ⟨0, by simpa [QParameters.positionMatchWidth] using p.K_pos⟩

/-- `K>0`から構成した、degree・position pair sliceの型安全な先頭wire。 -/
def oraclePairWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).pair).ancillaWire
    ⟨0, by simpa [QParameters.pairWidth] using p.K_pos⟩

/-- selector定数比較に渡すBool値付き制御wire列を、任意の開始bitから再帰生成する。 -/
def selectorConstantControlsAux
    {ancillaQubits systemQubits : Nat}
    (constant start : Nat) :
    List (Wire ancillaQubits systemQubits) →
      List (Wire ancillaQubits systemQubits × Bool)
  | [] => []
  | wire :: wires =>
      (wire, constant.testBit start) ::
        selectorConstantControlsAux constant (start + 1) wires

/-- selector定数比較に渡すlittle-endianのBool値付き制御wire列。 -/
def selectorConstantControls
    {ancillaQubits systemQubits : Nat}
    (selector : List (Wire ancillaQubits systemQubits)) (constant : Nat) :
    List (Wire ancillaQubits systemQubits × Bool) :=
  selectorConstantControlsAux constant 0 selector

/-- selector registerが指定Nat定数に等しいときtargetを反転する。 -/
def selectorEqualsConstant
    {ancillaQubits systemQubits : Nat}
    (selector scratch : List (Wire ancillaQubits systemQubits))
    (constant : Nat) (target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  ReversibleCircuit.boolMultiControlledX
    (selectorConstantControls selector constant)
    scratch target

/-- controlが1のときsource wordをtarget wordへXOR copyする。 -/
def controlledXorCopy
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  Circuit.sequence <| (source.zip target).map fun pair =>
    ReversibleCircuit.safeToffoli control pair.1 pair.2

/--
`start`番目から見たNat定数のbitが1であるtargetだけを、control付きで反転する再帰回路。
添字を明示した再帰形にすることで、任意幅について基底作用を帰納的に証明できる。
-/
def controlledXorConstantAux
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (constant start : Nat) :
    List (Wire ancillaQubits systemQubits) →
      Circuit (ReversibleGate ancillaQubits systemQubits)
  | [] => .identity
  | target :: targets =>
      .seq
        (if constant.testBit start then
          ReversibleCircuit.safeCnot control target
        else .identity)
        (controlledXorConstantAux control constant (start + 1) targets)

/-- controlが1のときNat定数をtarget registerへlittle-endian XORする。 -/
def controlledXorConstant
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (target : List (Wire ancillaQubits systemQubits)) (constant : Nat) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  controlledXorConstantAux control constant 0 target

/-- degree one-hotからslot存在flagとrow/column側のdegree条件を計算し、oneを1にする。 -/
def computeSharedDecoderPresenceParityAndOneFlagsCircuit (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) (rowMode : Bool) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let degreeFlags := oracleDegreeWires p
  let degreeConditionSources :=
    if rowMode then degreeFlags.take (p.K - 1) else degreeFlags.drop 1
  .seq (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p input) <|
  .seq (slotPresenceCircuit degreeFlags (oraclePresentWires p)) <|
  .seq (Circuit.sequence <| degreeConditionSources.map fun flag =>
    ReversibleCircuit.safeCnot flag (oracleDegreeConditionWire p)) <|
  .gate (.x (oracleOneWire p))

/-- membershipの1 slot分について、等値・非一致・他slot一致のflagを計算する。 -/
def membershipSlotCircuit
    {ancillaQubits systemQubits : Nat}
    (moved word equalWork andScratch :
      List (Wire ancillaQubits systemQubits))
    (presentFlag equalFlag goodFlag presentOtherFlag :
      Wire ancillaQubits systemQubits)
    (recordPresentOther : Bool) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  let equal := ReversibleCircuit.xorEqualityIntoTargetCircuit moved word equalWork andScratch equalFlag
  let initializeGood := (.gate (.x goodFlag) :
    Circuit (ReversibleGate ancillaQubits systemQubits))
  let removeMatch := ReversibleCircuit.safeToffoli presentFlag equalFlag goodFlag
  let presentOther := if recordPresentOther then
    ReversibleCircuit.safeToffoli presentFlag equalFlag presentOtherFlag
  else .identity
  .seq equal <| .seq initializeGood <| .seq removeMatch presentOther

/-- moved wordと各present wordのmembership・absence・present-otherを計算する。 -/
def membershipCompute (p : QParameters)
    (inputWords : List (List (Wire p.ancillaWidth p.systemWidth)))
    (selectedSlot : Nat) (includePresentOther : Bool) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let moved := oracleMovedWires p
  let present := oraclePresentWires p
  let equalFlags := membershipEqualWires p
  let goodFlags := membershipGoodWires p
  let perSlot := Circuit.sequence <| (List.range p.K).filterMap fun slot =>
    match inputWords[slot]?, present[slot]?, equalFlags[slot]?, goodFlags[slot]? with
    | some word, some presentFlag, some equalFlag, some goodFlag =>
        some <| membershipSlotCircuit moved word
          (oracleCompareWorkWires p) (decoderAndScratchWires p)
          presentFlag equalFlag goodFlag (oraclePresentOtherWire p)
          (includePresentOther && slot != selectedSlot)
    | _, _, _, _ => none
  .seq perSlot <|
    ReversibleCircuit.positiveMultiControlledX goodFlags
      (decoderAndScratchWires p) (oracleAbsentWire p)

/-- 1個の`Fin K` slotに対応する型安全なmembership局所回路。 -/
def xorSiteSlotMatchAndGoodFlagAtIndexCircuit (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  membershipSlotCircuit (oracleMovedWires p) (registerWordAt p register slot)
    (oracleCompareWorkWires p) (decoderAndScratchWires p)
    (oraclePresentWireAt p slot) (membershipEqualWireAt p slot)
    (membershipGoodWireAt p slot) (oraclePresentOtherWire p)
    (includePresentOther && slot != selectedSlot)

/-- `Fin K` slotごとの型安全なmembership局所回路列。 -/
def siteSlotMatchAndGoodFlagCircuits (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    List (Circuit (ReversibleGate p.ancillaWidth p.systemWidth)) :=
  (List.finRange p.K).map fun slot =>
    xorSiteSlotMatchAndGoodFlagAtIndexCircuit p register selectedSlot slot includePresentOther

/-- `Fin K` slotだけを走査する、型安全な正本membership回路。 -/
def xorMembershipMatchGoodAndAbsentFlagsCircuit (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .seq (Circuit.sequence <|
    siteSlotMatchAndGoodFlagCircuits p register selectedSlot includePresentOther) <|
    ReversibleCircuit.positiveMultiControlledX (membershipGoodWires p)
      (decoderAndScratchWires p) (oracleAbsentWire p)

/-- present wordをcandidateへ写し、padding markerを1にする。 -/
def prepareCandidates (p : QParameters)
    (inputWords : List (List (Wire p.ancillaWidth p.systemWidth))) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let words := candidateWords p
  let present := oraclePresentWires p
  let initializeMarkers := Circuit.sequence <| words.filterMap fun word =>
    word[p.wordWidth]?.map fun marker =>
      (.gate (.x marker) : Circuit (ReversibleGate p.ancillaWidth p.systemWidth))
  let copyWords := Circuit.sequence <| (List.range p.K).filterMap fun slot =>
    match inputWords[slot]?, words[slot]?, present[slot]? with
    | some source, some target, some presentFlag =>
        let dataCopy := controlledXorCopy presentFlag source (target.take p.wordWidth)
        let marker := target[p.wordWidth]?.map fun markerWire =>
          ReversibleCircuit.safeCnot presentFlag markerWire
        some <| .seq dataCopy (marker.getD .identity)
    | _, _, _ => none
  .seq initializeMarkers copyWords

/-- 1個のcandidate wordのpadding markerを初期化する基本X回路。 -/
def initializeCandidateMarkerTyped (p : QParameters)
    (word : Fin p.sortWordCount) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .gate (.x (candidateMarkerWire p word))

/-- 1個の`Fin K` slotを対応するcandidate wordへ条件付きコピーする回路。 -/
def prepareCandidateSlotTyped (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    Fin p.K → Circuit (ReversibleGate p.ancillaWidth p.systemWidth)
  | slot =>
      let target := candidateWordAt p (slotToSortWord p slot)
      let dataCopy := controlledXorCopy (oraclePresentWireAt p slot)
        (registerWordAt p register slot) (target.take p.wordWidth)
      let markerCopy := ReversibleCircuit.safeCnot (oraclePresentWireAt p slot)
        (candidateMarkerWire p (slotToSortWord p slot))
      .seq dataCopy markerCopy

/-- 全candidate markerの型安全な初期化回路列。 -/
def initializeCandidateMarkersTyped (p : QParameters) :
    List (Circuit (ReversibleGate p.ancillaWidth p.systemWidth)) :=
  (List.finRange p.sortWordCount).map fun word =>
    initializeCandidateMarkerTyped p word

/-- 全`Fin K` slotの型安全なcandidate copy回路列。 -/
def prepareCandidateSlotsTyped (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    List (Circuit (ReversibleGate p.ancillaWidth p.systemWidth)) :=
  (List.finRange p.K).map fun slot => prepareCandidateSlotTyped p register slot

/-- `Fin`添字だけでpadding marker初期化とactive word copyを行う正本候補生成回路。 -/
def xorConfigurationIntoCandidateRegisterCircuit (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .seq (Circuit.sequence <| initializeCandidateMarkersTyped p)
    (Circuit.sequence <| prepareCandidateSlotsTyped p register)

/-- branch・degree pairに応じてsorted candidateをdelimiter出力へXORする。 -/
def xorSortedCandidatesAsDelimiterIntoOutputCircuit (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (degreeChange : Int) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let pairFlag := oraclePairWire p
  Circuit.sequence <| (List.finRange p.K).map fun degreeSlot =>
    let inputDegree := degreeSlot.val + 1
    let outputDegreeInt := Int.ofNat inputDegree + degreeChange
    if _valid : (1 : Int) ≤ outputDegreeInt ∧
        outputDegreeInt ≤ Int.ofNat p.K then
      let outputDegree := outputDegreeInt.toNat
      have outputDegreeLe : outputDegree ≤ p.K := by
        dsimp only [outputDegree]
        exact Int.toNat_le.mpr _valid.2
      let compute := ReversibleCircuit.positiveMultiControlledX
        [oracleBranchWire p, oracleDegreeWireAt p degreeSlot]
        (decoderAndScratchWires p) pairFlag
      let dataUse := Circuit.sequence <|
        (List.finRange outputDegree).map fun outputSlot =>
          let registerSlot : Fin p.K :=
            ⟨outputSlot.val,
              lt_of_lt_of_le outputSlot.isLt outputDegreeLe⟩
          let candidateSlot : Fin p.sortWordCount :=
            ⟨outputSlot.val, lt_of_lt_of_le registerSlot.isLt
              p.K_le_sortWordCount⟩
          controlledXorCopy pairFlag
            ((candidateWordAt p candidateSlot).take p.wordWidth)
            (registerWordAt p output registerSlot)
      have delimiterLt : p.wordWidth * outputDegree < output.length := by
        rw [outputLength]
        calc
          p.wordWidth * outputDegree ≤ p.wordWidth * p.K :=
            Nat.mul_le_mul_left p.wordWidth outputDegreeLe
          _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _
          _ = p.systemWidth := rfl
      let delimiter := output.get
        ⟨p.wordWidth * outputDegree, delimiterLt⟩
      let delimiterUse := ReversibleCircuit.safeCnot pairFlag delimiter
      let activeUse := ReversibleCircuit.safeCnot pairFlag outputActive
      Circuit.computeUseUncompute id compute <|
        .seq dataUse <| .seq delimiterUse activeUse
    else .identity

/-- moved wordのsorted位置から相手側selector定数`6*slot+offset`をXOR出力する。 -/
def xorMovedMemberPositionIntoSelectorOutputCircuit (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth)) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let positionFlag := oraclePositionWire p
  let pairFlag := oraclePairWire p
  Circuit.sequence <| (List.finRange p.K).map fun slot =>
    let word := candidateWordAt p (slotToSortWord p slot)
    let equal := ReversibleCircuit.xorEqualityIntoTargetCircuit (oracleMovedWires p)
      (word.take p.wordWidth) (oracleCompareWorkWires p)
      (decoderAndScratchWires p) positionFlag
    let marker := candidateMarkerWire p (slotToSortWord p slot)
    let invert := (.gate (.x marker) :
      Circuit (ReversibleGate p.ancillaWidth p.systemWidth))
    let markerUse := .seq invert <| .seq
      (ReversibleCircuit.positiveMultiControlledX
        [oracleBranchWire p, positionFlag, marker]
        (decoderAndScratchWires p) pairFlag) invert
    let compute := .seq equal markerUse
    let use := controlledXorConstant pairFlag outputSelector
      (6 * slot.val + offset)
    Circuit.computeUseUncompute id compute use

/-- column oracleの一個の対角branch。 -/
def columnDiagonalBranch (p : QParameters) (slot copy : Nat) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let computeSelector := selectorEqualsConstant (columnSelectorWires p)
    (decoderAndScratchWires p) (6 * slot + copy) (oracleSelectedWire p)
  match (oraclePresentWires p)[slot]? with
  | none => .identity
  | some presentFlag =>
      let computeBranch := ReversibleCircuit.positiveMultiControlledX
        [oracleLegalWire p, oracleSelectedWire p, presentFlag]
        (decoderAndScratchWires p) (oracleBranchWire p)
      let compute := .seq computeSelector computeBranch
      let use := .seq (controlledXorCopy (oracleBranchWire p)
          (columnKeyWires p) (rowOutputWires p)) <|
        .seq (controlledXorConstant (oracleBranchWire p)
          (selectorOutputWires p) (6 * slot + copy)) <|
        .seq (ReversibleCircuit.safeCnot (oracleBranchWire p) (negativeWire p)) <|
        ReversibleCircuit.safeCnot (oracleBranchWire p) (activeWire p)
      Circuit.computeUseUncompute id compute use

/-- column oracleの一個の移動branch。 -/
def columnEventBranch (p : QParameters) (slot offset : Nat) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let collision := offset % 2 = 1
  let vertical := 4 ≤ offset
  let inputWords := splitSystemWords p.wordWidth p.K (columnKeyWires p)
  let selectorCompute := selectorEqualsConstant (columnSelectorWires p)
    (decoderAndScratchWires p) (6 * slot + offset) (oracleSelectedWire p)
  match inputWords[slot]?, (oraclePresentWires p)[slot]? with
  | some sourceWord, some presentFlag =>
      let movedCopy := ReversibleCircuit.xorCopy sourceWord (oracleMovedWires p)
      let coordinate := if vertical then
        (oracleMovedWires p).drop p.q |>.take p.q
      else (oracleMovedWires p).take p.q
      let move := ReversibleCircuit.incrementWordMod2PowInPlaceCircuit coordinate
        (decoderAndScratchWires p)
      let membership := membershipCompute p inputWords slot true
      let condition := if collision then oraclePresentOtherWire p else oracleAbsentWire p
      let controls := [oracleLegalWire p, oracleSelectedWire p, presentFlag, condition] ++
        if collision then [oracleDegreeConditionWire p] else []
      let branch := ReversibleCircuit.positiveMultiControlledX controls
        (decoderAndScratchWires p) (oracleBranchWire p)
      let candidates := prepareCandidates p inputWords
      let selectedCandidate := (candidateWords p)[slot]?
      let modify := match selectedCandidate with
        | none => .identity
        | some candidate =>
            let removeSource := controlledXorCopy (oracleBranchWire p) sourceWord
              (candidate.take p.wordWidth)
            if collision then
              let marker := candidate[p.wordWidth]?.map fun markerWire =>
                ReversibleCircuit.safeCnot (oracleBranchWire p) markerWire
              .seq removeSource (marker.getD .identity)
            else
              .seq removeSource <| controlledXorCopy (oracleBranchWire p)
                (oracleMovedWires p) (candidate.take p.wordWidth)
      let sorting := reversiblySortCandidateWordsAndRestoreHistoryCircuit p
      let compute := .seq selectorCompute <| .seq movedCopy <| .seq move <|
        .seq membership <| .seq branch <| .seq candidates <| .seq modify sorting
      let use := .seq (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (rowOutputWires p)
          (by simp [rowOutputWires]) (activeWire p)
          (if collision then -1 else 0)) <|
        xorMovedMemberPositionIntoSelectorOutputCircuit p offset (selectorOutputWires p)
      Circuit.computeUseUncompute id compute use
  | _, _ => .identity

/-- 型安全なslot/copy添字を受け取るcolumn対角branch。 -/
def columnDiagonalResultComputeUseUncomputeCircuit (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let selectorValue := 6 * slot.val + copy.val
  let computeSelector := selectorEqualsConstant (columnSelectorWires p)
    (decoderAndScratchWires p) selectorValue (oracleSelectedWire p)
  let computeBranch := ReversibleCircuit.positiveMultiControlledX
    [oracleLegalWire p, oracleSelectedWire p, oraclePresentWireAt p slot]
    (decoderAndScratchWires p) (oracleBranchWire p)
  let compute := .seq computeSelector computeBranch
  let use := .seq (controlledXorCopy (oracleBranchWire p)
      (columnKeyWires p) (rowOutputWires p)) <|
    .seq (controlledXorConstant (oracleBranchWire p)
      (selectorOutputWires p) selectorValue) <|
    .seq (ReversibleCircuit.safeCnot (oracleBranchWire p) (negativeWire p)) <|
    ReversibleCircuit.safeCnot (oracleBranchWire p) (activeWire p)
  Circuit.computeUseUncompute id compute use

/-- 型安全なslot/event offsetを受け取るcolumn event branch。 -/
def applyColumnEventReferenceAndRestoreWorkCircuit (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let collision := offset.val % 2 = 1
  let vertical := 4 ≤ offset.val
  let register := columnKeyWires p
  let sourceWord := registerWordAt p register slot
  let selectorCompute := selectorEqualsConstant (columnSelectorWires p)
    (decoderAndScratchWires p) (6 * slot.val + offset.val)
      (oracleSelectedWire p)
  let movedCopy := ReversibleCircuit.xorCopy sourceWord (oracleMovedWires p)
  let coordinate := if vertical then
    (oracleMovedWires p).drop p.q |>.take p.q
  else (oracleMovedWires p).take p.q
  let move := ReversibleCircuit.incrementWordMod2PowInPlaceCircuit coordinate
    (decoderAndScratchWires p)
  let membership := xorMembershipMatchGoodAndAbsentFlagsCircuit p register slot true
  let condition := if collision then oraclePresentOtherWire p else oracleAbsentWire p
  let controls := [oracleLegalWire p, oracleSelectedWire p,
    oraclePresentWireAt p slot, condition] ++
      if collision then [oracleDegreeConditionWire p] else []
  let branch := ReversibleCircuit.positiveMultiControlledX controls
    (decoderAndScratchWires p) (oracleBranchWire p)
  let candidates := xorConfigurationIntoCandidateRegisterCircuit p register
  let candidate := candidateWordAt p (slotToSortWord p slot)
  let removeSource := controlledXorCopy (oracleBranchWire p) sourceWord
    (candidate.take p.wordWidth)
  let modify := if collision then
    .seq removeSource <|
      ReversibleCircuit.safeCnot (oracleBranchWire p)
        (candidateMarkerWire p (slotToSortWord p slot))
  else
    .seq removeSource <| controlledXorCopy (oracleBranchWire p)
      (oracleMovedWires p) (candidate.take p.wordWidth)
  let sorting := reversiblySortCandidateWordsAndRestoreHistoryCircuit p
  let compute := .seq selectorCompute <| .seq movedCopy <| .seq move <|
    .seq membership <| .seq branch <| .seq candidates <| .seq modify sorting
  let use := .seq (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (rowOutputWires p)
      (by simp [rowOutputWires]) (activeWire p)
      (if collision then -1 else 0)) <|
    xorMovedMemberPositionIntoSelectorOutputCircuit p offset.val (selectorOutputWires p)
  Circuit.computeUseUncompute id compute use

/-- column event の compute--use--uncompute という実装構造を明示する回路名。 -/
def columnEventResultComputeUseUncomputeCircuit (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  applyColumnEventReferenceAndRestoreWorkCircuit p slot offset

/-- 全slot・全6 offsetを合成したcolumn oracle可逆回路。 -/
def applyColumnOracleReferenceAndRestoreWorkCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let persistent := computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false
  let branches := Circuit.sequence <| (List.finRange p.K).flatMap fun slot =>
    [columnDiagonalResultComputeUseUncomputeCircuit p slot 0, columnDiagonalResultComputeUseUncomputeCircuit p slot 1,
      applyColumnEventReferenceAndRestoreWorkCircuit p slot 2, applyColumnEventReferenceAndRestoreWorkCircuit p slot 3,
      applyColumnEventReferenceAndRestoreWorkCircuit p slot 4, applyColumnEventReferenceAndRestoreWorkCircuit p slot 5]
  .seq persistent <| .seq branches (persistent.reverse id)

/-- column oracle の persistent compute・全branch fold・uncompute 構造を明示する回路名。 -/
def columnOraclePersistentComputeBranchFoldUncomputeCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  applyColumnOracleReferenceAndRestoreWorkCircuit p

/-- column oracleを許可基本ゲートだけのLean正本回路へ翻訳する。 -/
def applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  ReversibleCircuit.toPrimitive (applyColumnOracleReferenceAndRestoreWorkCircuit p)

/-- row oracleの一個の対角branch。 -/
def rowDiagonalBranch (p : QParameters) (slot copy : Nat) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let computeSelector := selectorEqualsConstant (rowSelectorWires p)
    (decoderAndScratchWires p) (6 * slot + copy) (oracleSelectedWire p)
  match (oraclePresentWires p)[slot]? with
  | none => .identity
  | some presentFlag =>
      let computeBranch := ReversibleCircuit.positiveMultiControlledX
        [oracleLegalWire p, oracleSelectedWire p, presentFlag]
        (decoderAndScratchWires p) (oracleBranchWire p)
      let compute := .seq computeSelector computeBranch
      let use := .seq (controlledXorCopy (oracleBranchWire p)
          (systemWires p) (columnKeyWires p)) <|
        .seq (controlledXorConstant (oracleBranchWire p)
          (columnSelectorWires p) (6 * slot + copy)) <|
        ReversibleCircuit.safeCnot (oracleBranchWire p) (keySignalWire p)
      Circuit.computeUseUncompute id compute use

/-- row oracleの一個の移動branch。 -/
def rowEventBranch (p : QParameters) (slot offset : Nat) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let collision := offset % 2 = 1
  let vertical := 4 ≤ offset
  let inputWords := splitSystemWords p.wordWidth p.K (systemWires p)
  let selectorCompute := selectorEqualsConstant (rowSelectorWires p)
    (decoderAndScratchWires p) (6 * slot + offset) (oracleSelectedWire p)
  match inputWords[slot]?, (oraclePresentWires p)[slot]? with
  | some arrivalWord, some presentFlag =>
      let movedCopy := ReversibleCircuit.xorCopy arrivalWord (oracleMovedWires p)
      let coordinate := if vertical then
        (oracleMovedWires p).drop p.q |>.take p.q
      else (oracleMovedWires p).take p.q
      let moveBack := ReversibleCircuit.decrementWordMod2PowInPlaceCircuit coordinate
        (decoderAndScratchWires p)
      let membership := membershipCompute p inputWords slot false
      let controls := [oracleLegalWire p, oracleSelectedWire p, presentFlag,
        oracleAbsentWire p] ++ if collision then [oracleDegreeConditionWire p] else []
      let branch := ReversibleCircuit.positiveMultiControlledX controls
        (decoderAndScratchWires p) (oracleBranchWire p)
      let candidates := prepareCandidates p inputWords
      let modify := if collision then
        Circuit.sequence <| (oracleDegreeWires p).zipIdx.filterMap fun indexed =>
          match (candidateWords p)[indexed.2 + 1]? with
          | some candidate =>
              let pairCompute := ReversibleCircuit.positiveMultiControlledX
                [oracleBranchWire p, indexed.1] (decoderAndScratchWires p)
                (oraclePairWire p)
              let append := controlledXorCopy
                (oraclePairWire p)
                (oracleMovedWires p) (candidate.take p.wordWidth)
              let marker := candidate[p.wordWidth]?.map fun markerWire =>
                ReversibleCircuit.safeCnot
                  (oraclePairWire p) markerWire
              some <| Circuit.computeUseUncompute id pairCompute <|
                .seq append (marker.getD .identity)
          | none => none
      else
        match (candidateWords p)[slot]? with
        | some candidate =>
            .seq (controlledXorCopy (oracleBranchWire p) arrivalWord
              (candidate.take p.wordWidth)) <|
            controlledXorCopy (oracleBranchWire p) (oracleMovedWires p)
              (candidate.take p.wordWidth)
        | none => .identity
      let sorting := reversiblySortCandidateWordsAndRestoreHistoryCircuit p
      let compute := .seq selectorCompute <| .seq movedCopy <| .seq moveBack <|
        .seq membership <| .seq branch <| .seq candidates <| .seq modify sorting
      let use := .seq (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (columnKeyWires p)
          (by simp [columnKeyWires]) (keySignalWire p)
          (if collision then 1 else 0)) <|
        xorMovedMemberPositionIntoSelectorOutputCircuit p offset (columnSelectorWires p)
      Circuit.computeUseUncompute id compute use
  | _, _ => .identity

/-- 型安全なslot/copy添字を受け取るrow対角branch。 -/
def rowDiagonalResultComputeUseUncomputeCircuit (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let selectorValue := 6 * slot.val + copy.val
  let computeSelector := selectorEqualsConstant (rowSelectorWires p)
    (decoderAndScratchWires p) selectorValue (oracleSelectedWire p)
  let computeBranch := ReversibleCircuit.positiveMultiControlledX
    [oracleLegalWire p, oracleSelectedWire p, oraclePresentWireAt p slot]
    (decoderAndScratchWires p) (oracleBranchWire p)
  let compute := .seq computeSelector computeBranch
  let use := .seq (controlledXorCopy (oracleBranchWire p)
      (systemWires p) (columnKeyWires p)) <|
    .seq (controlledXorConstant (oracleBranchWire p)
      (columnSelectorWires p) selectorValue) <|
    ReversibleCircuit.safeCnot (oracleBranchWire p) (keySignalWire p)
  Circuit.computeUseUncompute id compute use

/-- 型安全なslot/event offsetを受け取るrow event branch。 -/
def applyRowEventReferenceAndRestoreWorkCircuit (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let collision := offset.val % 2 = 1
  let vertical := 4 ≤ offset.val
  let register := systemWires p
  let arrivalWord := registerWordAt p register slot
  let selectorCompute := selectorEqualsConstant (rowSelectorWires p)
    (decoderAndScratchWires p) (6 * slot.val + offset.val)
      (oracleSelectedWire p)
  let movedCopy := ReversibleCircuit.xorCopy arrivalWord (oracleMovedWires p)
  let coordinate := if vertical then
    (oracleMovedWires p).drop p.q |>.take p.q
  else (oracleMovedWires p).take p.q
  let moveBack := ReversibleCircuit.decrementWordMod2PowInPlaceCircuit coordinate
    (decoderAndScratchWires p)
  let membership := xorMembershipMatchGoodAndAbsentFlagsCircuit p register slot false
  let controls := [oracleLegalWire p, oracleSelectedWire p,
    oraclePresentWireAt p slot, oracleAbsentWire p] ++
      if collision then [oracleDegreeConditionWire p] else []
  let branch := ReversibleCircuit.positiveMultiControlledX controls
    (decoderAndScratchWires p) (oracleBranchWire p)
  let candidates := xorConfigurationIntoCandidateRegisterCircuit p register
  let modify := if collision then
    Circuit.sequence <| (List.finRange (p.K - 1)).map fun degreeSlot =>
      let degreeIndex : Fin p.K :=
        ⟨degreeSlot.val, lt_of_lt_of_le degreeSlot.isLt (Nat.sub_le _ _)⟩
      let candidateIndex : Fin p.sortWordCount :=
        ⟨degreeSlot.val + 1, by
          have : degreeSlot.val + 1 < p.K := by omega
          exact lt_of_lt_of_le this p.K_le_sortWordCount⟩
      let candidate := candidateWordAt p candidateIndex
      let pairFlag := oraclePairWire p
      let pairCompute := ReversibleCircuit.positiveMultiControlledX
        [oracleBranchWire p, oracleDegreeWireAt p degreeIndex]
        (decoderAndScratchWires p) pairFlag
      let append := controlledXorCopy pairFlag (oracleMovedWires p)
        (candidate.take p.wordWidth)
      let marker := ReversibleCircuit.safeCnot pairFlag
        (candidateMarkerWire p candidateIndex)
      Circuit.computeUseUncompute id pairCompute <| .seq append marker
  else
    let candidate := candidateWordAt p (slotToSortWord p slot)
    .seq (controlledXorCopy (oracleBranchWire p) arrivalWord
      (candidate.take p.wordWidth)) <|
    controlledXorCopy (oracleBranchWire p) (oracleMovedWires p)
      (candidate.take p.wordWidth)
  let sorting := reversiblySortCandidateWordsAndRestoreHistoryCircuit p
  let compute := .seq selectorCompute <| .seq movedCopy <| .seq moveBack <|
    .seq membership <| .seq branch <| .seq candidates <| .seq modify sorting
  let use := .seq (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (columnKeyWires p)
      (by simp [columnKeyWires]) (keySignalWire p)
      (if collision then 1 else 0)) <|
    xorMovedMemberPositionIntoSelectorOutputCircuit p offset.val (columnSelectorWires p)
  Circuit.computeUseUncompute id compute use

/-- row event の compute--use--uncompute という実装構造を明示する回路名。 -/
def rowEventResultComputeUseUncomputeCircuit (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  applyRowEventReferenceAndRestoreWorkCircuit p slot offset

/-- 全slot・全6 offsetを合成したrow oracle可逆回路。 -/
def applyRowOracleReferenceAndRestoreWorkCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let persistent := computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true
  let branches := Circuit.sequence <| (List.finRange p.K).flatMap fun slot =>
    [rowDiagonalResultComputeUseUncomputeCircuit p slot 0, rowDiagonalResultComputeUseUncomputeCircuit p slot 1,
      applyRowEventReferenceAndRestoreWorkCircuit p slot 2, applyRowEventReferenceAndRestoreWorkCircuit p slot 3,
      applyRowEventReferenceAndRestoreWorkCircuit p slot 4, applyRowEventReferenceAndRestoreWorkCircuit p slot 5]
  .seq persistent <| .seq branches (persistent.reverse id)

/-- row oracle の persistent compute・全branch fold・uncompute 構造を明示する回路名。 -/
def rowOraclePersistentComputeBranchFoldUncomputeCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  applyRowOracleReferenceAndRestoreWorkCircuit p

/-- row oracleを許可基本ゲートだけのLean正本回路へ翻訳する。 -/
def applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  ReversibleCircuit.toPrimitive (applyRowOracleReferenceAndRestoreWorkCircuit p)

/-- column oracle正本の全葉は許可した五種類の基本ゲートである。 -/
theorem applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit_leaves (p : QParameters) :
    ∀ gate ∈ (applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p).flatten, IsAllowedPrimitiveGate gate :=
  primitiveCircuit_allLeavesAllowed _

/-- row oracle正本の全葉は許可した五種類の基本ゲートである。 -/
theorem applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit_leaves (p : QParameters) :
    ∀ gate ∈ (applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit p).flatten, IsAllowedPrimitiveGate gate :=
  primitiveCircuit_allLeavesAllowed _

end ProbabilityGeneratorQProof
