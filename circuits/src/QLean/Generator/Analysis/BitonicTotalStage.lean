import QLean.Generator.Analysis.BitonicScheduleTypes
import QLean.Generator.Analysis.OracleEventLocalTotalStage

/-!
# bitonic sort の回路非依存な全 dirty stage
-/

namespace ProbabilityGeneratorQProof

namespace BitonicTotalProgram

/-- 半幅命令を倍幅 network の前半へ埋め込む。 -/
def liftLeft {wordCount : Nat} (instruction : BareBitonicCompareExchange wordCount) :
    BareBitonicCompareExchange (2 * wordCount) :=
  instruction.liftLeft

/-- 半幅命令を倍幅 network の後半へ埋め込む。 -/
def liftRight {wordCount : Nat} (instruction : BareBitonicCompareExchange wordCount) :
    BareBitonicCompareExchange (2 * wordCount) :=
  instruction.liftRight

/-- 再帰的 merge の最上位 half-cleaner。 -/
def halfCleaner (level : Nat) (ascending : Bool) :
    List (BareBitonicCompareExchange (2 * recursiveBitonicWidth level)) :=
  VerifiedCircuitCore.bitonicHalfCleaner level ascending

/-- 指定方向の再帰的 bitonic merge。 -/
def recursiveMerge :
    (level : Nat) → (ascending : Bool) →
      List (BareBitonicCompareExchange (recursiveBitonicWidth level))
  := VerifiedCircuitCore.bitonicMergeSchedule

/-- 左半分と右半分を逆向きに sort してから merge する Batcher schedule。 -/
def recursiveSort :
    (level : Nat) → (ascending : Bool) →
      List (BareBitonicCompareExchange (recursiveBitonicWidth level))
  := VerifiedCircuitCore.bitonicSortSchedule

/-- word 数の等式に沿って命令添字を cast する。 -/
def cast {sourceWidth targetWidth : Nat} (widthEquality : sourceWidth = targetWidth)
    (instruction : BareBitonicCompareExchange sourceWidth) :
    BareBitonicCompareExchange targetWidth :=
  VerifiedCircuitCore.BitonicCompareExchange.cast widthEquality instruction

/-- 実行順 index を履歴添字として付与する。 -/
def attachHistoryFrom {wordCount historyCount : Nat} (positiveHistory : 0 < historyCount) :
    Nat → List (BareBitonicCompareExchange wordCount) →
      List (TypedBitonicCompareExchange wordCount historyCount)
  := VerifiedCircuitCore.attachBitonicHistoryFrom positiveHistory

/-- 実行順 index を 0 から履歴添字として付与する。 -/
def attachHistory {wordCount historyCount : Nat} (positiveHistory : 0 < historyCount)
    (schedule : List (BareBitonicCompareExchange wordCount)) :
    List (TypedBitonicCompareExchange wordCount historyCount) :=
  VerifiedCircuitCore.attachBitonicHistory positiveHistory schedule

/-- Q の padding 込み幅へ cast した history なし schedule。 -/
def qBareSchedule (p : QParameters) :
    List (BareBitonicCompareExchange p.sortWordCount) :=
  (recursiveSort (Nat.clog 2 p.K) true).map <| cast
    (by simp [QParameters.sortWordCount, recursiveBitonicWidth_eq_pow])

/-- Q の candidate sort 用の型安全な純粋 schedule。 -/
def qSchedule (p : QParameters) :
    List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :=
  attachHistory (by simp [QParameters.sortFlagWidth, QParameters.sortWordCount])
    (qBareSchedule p)

/-- sort 比較の equality work wire 列。 -/
def compareWorkWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  let comparison := (List.finRange p.wordWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork).ancillaWire index
  let extra := (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).andWork).ancillaWire
      ⟨0, by simp [QParameters.andWorkWidth]⟩
  comparison ++ [extra]

/-- sort 比較の AND scratch wire 列。 -/
def andScratchWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange (p.andWorkWidth - 1)).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).ancillaWire
      ⟨index.val + 1, by
        simp [QParameters.andWorkWidth] at index ⊢
        omega⟩

/-- 一つの compare--exchange を全 dirty stage として実行する。 -/
def comparisonStage (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let left := OracleEventTotalProgram.candidateWordAt p instruction.left
  let right := OracleEventTotalProgram.candidateWordAt p instruction.right
  let history :=
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).sortFlags).ancillaWire
      instruction.history
  if instruction.ascending then
    TotalReversibleStage.xorLessThanIntoTarget right left (compareWorkWires p)
      (andScratchWires p) history
  else
    TotalReversibleStage.xorLessThanIntoTarget left right (compareWorkWires p)
      (andScratchWires p) history

/-- The independent controlled-swap child of one compare--exchange stage. -/
def controlledSwapStage (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  let left := OracleEventTotalProgram.candidateWordAt p instruction.left
  let right := OracleEventTotalProgram.candidateWordAt p instruction.right
  let history :=
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).sortFlags).ancillaWire
      instruction.history
  TotalReversibleStage.controlledSwapWord history left right

/-- One compare--exchange as a dirty total stage. -/
def compareExchange (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  .seq (comparisonStage p instruction) (controlledSwapStage p instruction)

/-- Q candidate register に対する全 compare--exchange の純粋 sort stage。 -/
def sort (p : QParameters) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  TotalReversibleStage.sequence <| (qSchedule p).map fun instruction =>
    compareExchange p instruction

/-- One compare--exchange stage as an implementation-independent Q operator. -/
def compareExchangeAnalyticOperator (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  (compareExchange p instruction).analyticOperator

/-- The complete bitonic stage as an implementation-independent Q operator. -/
def sortAnalyticOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  (sort p).analyticOperator

/-- The independent compare--exchange operator on canonical core basis. -/
def compareExchangeCanonicalCoreAnalyticOperator (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    VerifiedCircuitCore.Operator
      (VerifiedCircuitCore.QubitBasis (p.ancillaWidth + p.systemWidth)) :=
  Matrix.reindex (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)
    (compareExchangeAnalyticOperator p instruction)

/-- The independent complete-sort operator on canonical core basis. -/
def sortCanonicalCoreAnalyticOperator (p : QParameters) :
    VerifiedCircuitCore.Operator
      (VerifiedCircuitCore.QubitBasis (p.ancillaWidth + p.systemWidth)) :=
  Matrix.reindex (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)
    (sortAnalyticOperator p)

/-- The independent sort target is the execution-order product of its
independent compare--exchange targets. -/
theorem sortAnalyticOperator_eq_operatorSequence (p : QParameters) :
    sortAnalyticOperator p =
      VerifiedCircuitCore.operatorSequence
        ((qSchedule p).map (compareExchangeAnalyticOperator p)) := by
  unfold sortAnalyticOperator sort
  rw [TotalReversibleStage.analyticOperator_sequence, List.map_map]
  rfl

end BitonicTotalProgram

end ProbabilityGeneratorQProof
