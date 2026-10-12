import QLean.Generator.Analysis.TotalReversiblePrograms
import QLean.Generator.Analysis.QParameters

/-!
# compact decoderの全dirty純粋stage

delimiter one-hot、隣接word比較、合法性flagを、実装から独立なstageとして構成する。
-/

namespace ProbabilityGeneratorQProof

namespace DecoderTotalProgram

/-- degree one-hot wire列。 -/
def degreeWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.degreeWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).degree).ancillaWire index

/-- delimiter合法性wire。 -/
def legalWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.oracleSlice (OracleWorkLayout.canonical p).legal).ancillaWire 0

/-- decoder全AND scratch列。 -/
def andWorkWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.andWorkWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).ancillaWire index

/-- word比較work列。 -/
def compareWorkWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.wordWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork).ancillaWire index

/-- suffix OR一時wire列。 -/
def suffixWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  ((List.finRange p.candidateWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate).ancillaWire index).take
      p.systemWidth

/-- 隣接比較result列。 -/
def lessWires (p : QParameters) : List (Wire p.ancillaWidth p.systemWidth) :=
  (andWorkWires p).take (p.K - 1)

/-- 隣接比較need列。 -/
def needWires (p : QParameters) : List (Wire p.ancillaWidth p.systemWidth) :=
  (andWorkWires p).drop (p.K - 1) |>.take (p.K - 1)

/-- 隣接比較good列。 -/
def goodWires (p : QParameters) : List (Wire p.ancillaWidth p.systemWidth) :=
  (andWorkWires p).drop (2 * (p.K - 1)) |>.take (p.K - 1)

/-- degree-valid一時wire。 -/
def degreeValidWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (andWorkWires p).get ⟨3 * (p.K - 1), by
    simp [andWorkWires, QParameters.andWorkWidth]
    omega⟩

/-- legal一時wire。 -/
def legalTemporaryWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (andWorkWires p).get ⟨3 * (p.K - 1) + 1, by
    simp [andWorkWires, QParameters.andWorkWidth]
    omega⟩

/-- decoder多重AND用の残りscratch。 -/
def andScratchWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (andWorkWires p).drop (3 * (p.K - 1) + 2)

/-- `target ^= left OR right`の全dirty stage。 -/
def reversibleOrXor {ancillaQubits systemQubits : Nat}
    (left right target : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  .seq (TotalReversibleStage.safeXorControlled left target) <|
    .seq (TotalReversibleStage.safeXorControlled right target) <|
      TotalReversibleStage.safeXorDoublyControlled left right target

/-- 右端から全suffix ORを計算する。 -/
def suffixOr
    {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    TotalReversibleStage ancillaQubits systemQubits
  | [], _ => .identity
  | _, [] => .identity
  | [inputLast], [suffixLast] =>
      TotalReversibleStage.safeXorControlled inputLast suffixLast
  | inputHead :: inputNext :: inputTail,
      suffixHead :: suffixNext :: suffixTail =>
      .seq (suffixOr (inputNext :: inputTail) (suffixNext :: suffixTail))
        (reversibleOrXor inputHead suffixNext suffixHead)
  | _, _ => .identity

/-- 一つのdelimiter境界flagをsuffix ORから計算する。 -/
def degreeBoundary {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (input suffix : List (Wire ancillaQubits systemQubits))
    (degree : Nat) (flag : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  let boundary := wordWidth * (degree + 1)
  match input[boundary]? with
  | none => .identity
  | some delimiter =>
      match suffix[boundary + 1]? with
      | none => TotalReversibleStage.safeXorControlled delimiter flag
      | some laterNonzero =>
          let invert := TotalReversibleStage.instruction
            (.xorOne laterNonzero)
          .seq invert <| .seq
            (TotalReversibleStage.safeXorDoublyControlled
              delimiter laterNonzero flag) invert

/-- 各degree境界flagを順に計算する。 -/
def degreeBoundarySequence {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (input suffix : List (Wire ancillaQubits systemQubits)) :
    Nat → List (Wire ancillaQubits systemQubits) →
      TotalReversibleStage ancillaQubits systemQubits
  | _, [] => .identity
  | degree, flag :: flags =>
      .seq (degreeBoundary wordWidth input suffix degree flag)
        (degreeBoundarySequence wordWidth input suffix (degree + 1) flags)

/-- suffixを計算し、degree one-hotへ使用してから逆計算する。 -/
def xorDelimiterDegreeOneHotIntoTargets
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (input suffix flags : List (Wire ancillaQubits systemQubits)) :
    TotalReversibleStage ancillaQubits systemQubits :=
  let compute := suffixOr input suffix
  let use := degreeBoundarySequence wordWidth input suffix 0 flags
  TotalReversibleStage.computeUseUncompute compute use

/-- bit列を固定幅word列へ切り分ける純粋補助。 -/
def splitWords {ancillaQubits systemQubits : Nat}
    (wordWidth wordCount : Nat)
    (input : List (Wire ancillaQubits systemQubits)) :
    List (List (Wire ancillaQubits systemQubits)) :=
  (List.range wordCount).map fun slot =>
    (input.drop (slot * wordWidth)).take wordWidth

/-- degree suffix parityを各present flagへXORする。 -/
def xorDegreeSuffixParityIntoSlotPresence
    {ancillaQubits systemQubits : Nat}
    (degreeFlags : List (Wire ancillaQubits systemQubits)) :
    Nat → List (Wire ancillaQubits systemQubits) →
      TotalReversibleStage ancillaQubits systemQubits
  | _, [] => .identity
  | slot, presentFlag :: presentFlags =>
      .seq (TotalReversibleStage.sequence <|
          (degreeFlags.drop slot).map fun degreeFlag =>
            TotalReversibleStage.safeXorControlled degreeFlag presentFlag)
        (xorDegreeSuffixParityIntoSlotPresence
          degreeFlags (slot + 1) presentFlags)

/-- degree one-hotから各slot存在flagを計算する。 -/
def slotPresence {ancillaQubits systemQubits : Nat}
    (degreeFlags presentFlags : List (Wire ancillaQubits systemQubits)) :
    TotalReversibleStage ancillaQubits systemQubits :=
  xorDegreeSuffixParityIntoSlotPresence degreeFlags 0 presentFlags

/-- 一つの隣接wordについてless・need・goodを計算する。 -/
def comparisonStep {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (left right : List (Wire ancillaQubits systemQubits))
    (less need good : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  let lessStage := TotalReversibleStage.xorLessThanIntoTarget
    left right compareWork andScratch less
  let needStage := TotalReversibleStage.sequence <|
    (degreeFlags.drop (slot + 1)).map fun degreeFlag =>
      TotalReversibleStage.safeXorControlled degreeFlag need
  let invertGood := TotalReversibleStage.instruction (.xorOne good)
  let invertLess := TotalReversibleStage.instruction (.xorOne less)
  .seq lessStage <| .seq needStage <|
    .seq invertGood <| .seq invertLess <|
      .seq (TotalReversibleStage.safeXorDoublyControlled need less good) invertLess

/-- 隣接word比較をslot順に再帰実行する。 -/
def comparisonSequence {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits)) :
    Nat → List (List (Wire ancillaQubits systemQubits)) →
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
      TotalReversibleStage ancillaQubits systemQubits
  | slot, left :: right :: words, less :: lessFlags,
      need :: needFlags, good :: goodFlags =>
      .seq (comparisonStep degreeFlags compareWork andScratch slot
        left right less need good) <|
        comparisonSequence degreeFlags compareWork andScratch (slot + 1)
          (right :: words) lessFlags needFlags goodFlags
  | _, _, _, _, _ => .identity

/-- degree one-hotのparityをdegree-validへXORする。 -/
def degreeValid {ancillaQubits systemQubits : Nat}
    (degreeFlags : List (Wire ancillaQubits systemQubits))
    (degreeValid : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  TotalReversibleStage.sequence <| degreeFlags.map fun flag =>
    TotalReversibleStage.safeXorControlled flag degreeValid

/-- degreeと隣接比較からlegal一時flagを計算する。 -/
def legalityCompute {ancillaQubits systemQubits : Nat}
    (words : List (List (Wire ancillaQubits systemQubits)))
    (degreeFlags lessFlags needFlags goodFlags compareWork andScratch :
      List (Wire ancillaQubits systemQubits))
    (degreeValidWire legalTemporary : Wire ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  .seq (degreeValid degreeFlags degreeValidWire) <|
    .seq (comparisonSequence degreeFlags compareWork andScratch 0
      words lessFlags needFlags goodFlags) <|
      TotalReversibleStage.positiveMultiControlledX
        (degreeValidWire :: goodFlags) andScratch legalTemporary

/-- degree one-hotとdelimiter legalityをtargetへXORするcompact decoder stage。 -/
def xorDelimiterLegalityAndDegreeOneHotIntoTargets (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let degreeDecode := xorDelimiterDegreeOneHotIntoTargets p.wordWidth input
    (suffixWires p) (degreeWires p)
  let words := splitWords p.wordWidth p.K input
  let legality := legalityCompute words (degreeWires p)
    (lessWires p) (needWires p) (goodWires p)
    (compareWorkWires p) (andScratchWires p)
    (degreeValidWire p) (legalTemporaryWire p)
  let use := TotalReversibleStage.safeXorControlled
    (legalTemporaryWire p) (legalWire p)
  .seq degreeDecode <| TotalReversibleStage.computeUseUncompute legality use

end DecoderTotalProgram

end ProbabilityGeneratorQProof
