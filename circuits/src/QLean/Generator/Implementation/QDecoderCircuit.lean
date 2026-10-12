import QLean.Generator.Implementation.BitonicSortLayout

/-!
# delimiter配置のcompact decoder回路

物理system bit列からdegree one-hotと合法性flagを計算する。suffix OR、境界delimiter、
隣接siteの厳密昇順比較を、可逆算術部品だけで構成し、内部scratchは逆計算で0へ戻す。
-/

namespace ProbabilityGeneratorQProof

/-- oracle work内のdegree one-hot wire列。 -/
def oracleDegreeWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.degreeWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).degree).ancillaWire index

/-- oracle work内のdelimiter合法性wire。 -/
def oracleLegalWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).legal).ancillaWire 0

/-- oracle work内の全AND scratch wire列。 -/
def oracleAndWorkWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.andWorkWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).ancillaWire index

/-- oracle work内の比較用wire列。 -/
def oracleCompareWorkWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.wordWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork).ancillaWire index

/-- decoderのsuffix ORにcandidate領域を一時利用するwire列。 -/
def decoderSuffixWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  ((List.finRange p.candidateWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate).ancillaWire index).take
      p.systemWidth

/-- decoderの隣接比較結果に割り当てる一時wire列。 -/
def decoderLessWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (oracleAndWorkWires p).take (p.K - 1)

/-- degreeに応じて隣接比較が必要かを表す一時wire列。 -/
def decoderNeedWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (oracleAndWorkWires p).drop (p.K - 1) |>.take (p.K - 1)

/-- 不要比較または厳密昇順を表す一時wire列。 -/
def decoderGoodWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (oracleAndWorkWires p).drop (2 * (p.K - 1)) |>.take (p.K - 1)

/-- 少なくとも一個のdegree flagが立ったことを保持する型安全な一時wire。 -/
def decoderDegreeValidWire (p : QParameters) :
    Wire p.ancillaWidth p.systemWidth :=
  (oracleAndWorkWires p).get ⟨3 * (p.K - 1), by
    simp [oracleAndWorkWires, QParameters.andWorkWidth]
    omega⟩

/-- 合法性ANDの型安全な一時出力wire。 -/
def decoderLegalTemporaryWire (p : QParameters) :
    Wire p.ancillaWidth p.systemWidth :=
  (oracleAndWorkWires p).get ⟨3 * (p.K - 1) + 1, by
    simp [oracleAndWorkWires, QParameters.andWorkWidth]
    omega⟩

/-- decoder多重ANDで使う残りのscratch wire列。 -/
def decoderAndScratchWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (oracleAndWorkWires p).drop (3 * (p.K - 1) + 2)

/-- `target ^= (left OR right)`をXOR・ANDの三基本ゲートへ分解する。 -/
def reversibleOrXor
    {ancillaQubits systemQubits : Nat}
    (left right target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  .seq (ReversibleCircuit.safeCnot left target) <|
  .seq (ReversibleCircuit.safeCnot right target) <|
  ReversibleCircuit.safeToffoli left right target

/-- 右端から全suffix ORを計算する可逆回路。 -/
def suffixOrCircuit
    {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Circuit (ReversibleGate ancillaQubits systemQubits)
  | [], _ => .identity
  | _, [] => .identity
  | [inputLast], [suffixLast] =>
      ReversibleCircuit.safeCnot inputLast suffixLast
  | inputHead :: inputNext :: inputTail,
      suffixHead :: suffixNext :: suffixTail =>
      .seq (suffixOrCircuit (inputNext :: inputTail) (suffixNext :: suffixTail))
        (reversibleOrXor inputHead suffixNext suffixHead)
  | _, _ => .identity

/-- degree番号`degree+1`のdelimiter境界flagをsuffix ORから計算する。 -/
def degreeBoundaryCircuit
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (input suffix : List (Wire ancillaQubits systemQubits))
    (degree : Nat) (flag : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  let boundary := wordWidth * (degree + 1)
  match input[boundary]? with
  | none => .identity
  | some delimiter =>
      match suffix[boundary + 1]? with
      | none => ReversibleCircuit.safeCnot delimiter flag
      | some laterNonzero =>
          let invert := (.gate (.x laterNonzero) :
            Circuit (ReversibleGate ancillaQubits systemQubits))
          .seq invert <| .seq
            (ReversibleCircuit.safeToffoli delimiter laterNonzero flag) invert

/-- 指定degree番号から各degree flagへ境界条件を順にXORする内部回路。 -/
def degreeBoundarySequence
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (input suffix : List (Wire ancillaQubits systemQubits)) :
    Nat → List (Wire ancillaQubits systemQubits) →
      Circuit (ReversibleGate ancillaQubits systemQubits)
  | _, [] => .identity
  | degree, flag :: flags =>
      .seq (degreeBoundaryCircuit wordWidth input suffix degree flag)
        (degreeBoundarySequence wordWidth input suffix (degree + 1) flags)

/-- suffix ORをcomputeし、degree境界flagへ使用してからsuffixだけをuncomputeする回路。 -/
def xorDelimiterDegreeOneHotIntoTargetsCircuit
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (input suffix flags : List (Wire ancillaQubits systemQubits)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  let suffixCompute := suffixOrCircuit input suffix
  let degreeUse := degreeBoundarySequence wordWidth input suffix 0 flags
  Circuit.computeUseUncompute id suffixCompute degreeUse

/-- system bit列をword幅ごとのlittle-endian wordリストへ切り分ける。 -/
def splitSystemWords
    {ancillaQubits systemQubits : Nat}
    (wordWidth wordCount : Nat)
    (input : List (Wire ancillaQubits systemQubits)) :
    List (List (Wire ancillaQubits systemQubits)) :=
  (List.range wordCount).map fun slot =>
    (input.drop (slot * wordWidth)).take wordWidth

/-- 指定slot番号から、degree flagのsuffix parityを各存在flagへXORする内部回路。 -/
def xorDegreeSuffixParityIntoSlotPresenceCircuit
    {ancillaQubits systemQubits : Nat}
    (degreeFlags : List (Wire ancillaQubits systemQubits)) :
    Nat → List (Wire ancillaQubits systemQubits) →
      Circuit (ReversibleGate ancillaQubits systemQubits)
  | _, [] => .identity
  | slot, presentFlag :: presentFlags =>
      .seq (Circuit.sequence <| (degreeFlags.drop slot).map fun degreeFlag =>
        ReversibleCircuit.safeCnot degreeFlag presentFlag)
        (xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags (slot + 1) presentFlags)

/-- degree flagから各slotの存在flagをXOR計算する。 -/
def slotPresenceCircuit
    {ancillaQubits systemQubits : Nat}
    (degreeFlags presentFlags : List (Wire ancillaQubits systemQubits)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags 0 presentFlags

/--
一個の隣接wordについてless・need・goodを計算する比較step。
`good = (left < right) OR NOT need`となるように可逆ゲートを並べる。
-/
def decoderComparisonStep
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (left right : List (Wire ancillaQubits systemQubits))
    (less need good : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  let lessCircuit :=
    ReversibleCircuit.xorLessThanIntoTargetCircuit left right compareWork andScratch less
  let needCircuit := Circuit.sequence <|
    (degreeFlags.drop (slot + 1)).map fun degreeFlag =>
      ReversibleCircuit.safeCnot degreeFlag need
  let invertGood := (.gate (.x good) :
    Circuit (ReversibleGate ancillaQubits systemQubits))
  let invertLess := (.gate (.x less) :
    Circuit (ReversibleGate ancillaQubits systemQubits))
  .seq lessCircuit <| .seq needCircuit <|
    .seq invertGood <| .seq invertLess <|
    .seq (ReversibleCircuit.safeToffoli need less good) invertLess

/--
隣接word比較をslot番号とともに再帰実行し、less・need・good flagへ結果を保持する。
リスト再帰形により任意`K`の作用を基底列挙なしで帰納証明できる。
-/
def decoderComparisonSequence
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits)) :
    Nat → List (List (Wire ancillaQubits systemQubits)) →
      List (Wire ancillaQubits systemQubits) →
      List (Wire ancillaQubits systemQubits) →
      List (Wire ancillaQubits systemQubits) →
      Circuit (ReversibleGate ancillaQubits systemQubits)
  | slot, left :: right :: words, less :: lessFlags,
      need :: needFlags, good :: goodFlags =>
      .seq (decoderComparisonStep degreeFlags compareWork andScratch slot
        left right less need good) <|
      decoderComparisonSequence degreeFlags compareWork andScratch (slot + 1)
        (right :: words) lessFlags needFlags goodFlags
  | _, _, _, _, _ => .identity

/-- degree one-hot列のparityをdegree-valid wireへXORする可逆回路。 -/
def decoderDegreeValidCircuit
    {ancillaQubits systemQubits : Nat}
    (degreeFlags : List (Wire ancillaQubits systemQubits))
    (degreeValid : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  Circuit.sequence <| degreeFlags.map fun flag =>
    ReversibleCircuit.safeCnot flag degreeValid

/-- degree・隣接比較から合法性を一時wireへ計算する内部回路。 -/
def decoderLegalityCompute
    {ancillaQubits systemQubits : Nat}
    (words : List (List (Wire ancillaQubits systemQubits)))
    (degreeFlags lessFlags needFlags goodFlags compareWork andScratch :
      List (Wire ancillaQubits systemQubits))
    (degreeValid legalTemporary : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  let degreeValidCircuit := decoderDegreeValidCircuit degreeFlags degreeValid
  let comparisons := decoderComparisonSequence degreeFlags compareWork andScratch 0
    words lessFlags needFlags goodFlags
  let allGood := ReversibleCircuit.positiveMultiControlledX
    (degreeValid :: goodFlags) andScratch legalTemporary
  .seq degreeValidCircuit <| .seq comparisons allGood

/--
compact decoder本体。degree one-hotとlegalだけを保持し、suffix・比較・AND scratchは
compute--use--uncomputeにより消去する。
-/
def xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let suffix := decoderSuffixWires p
  let degreeFlags := oracleDegreeWires p
  let degreeDecode := xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth input suffix degreeFlags
  let words := splitSystemWords p.wordWidth p.K input
  let legalityCompute := decoderLegalityCompute words degreeFlags
    (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p)
    (oracleCompareWorkWires p) (decoderAndScratchWires p)
    (decoderDegreeValidWire p) (decoderLegalTemporaryWire p)
  let legalityUse := ReversibleCircuit.safeCnot
    (decoderLegalTemporaryWire p) (oracleLegalWire p)
  .seq degreeDecode <|
    Circuit.computeUseUncompute id legalityCompute legalityUse

/-- compact decoderを許可基本ゲートだけのLean正本回路へ翻訳する。 -/
def compactDecoderCircuit (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  ReversibleCircuit.toPrimitive (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p input)

/-- compact decoder正本の全葉は許可した五種類の基本ゲートである。 -/
theorem compactDecoderCircuit_leaves (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) :
    ∀ gate ∈ (compactDecoderCircuit p input).flatten,
      IsAllowedPrimitiveGate gate :=
  primitiveCircuit_allLeavesAllowed _

end ProbabilityGeneratorQProof
