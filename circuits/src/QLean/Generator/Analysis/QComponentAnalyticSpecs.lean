import QLean.Generator.Analysis.QOracleReference

/-!
# Q回路の公開部品が実装すべき純粋な解析仕様

このファイルは、基本ゲート列や物理wire配置を参照せず、column/row oracleが外部から
観測できるregister値に与える作用だけを定義する。回路実装側の正しさ定理は別moduleで
この解析関数へ接続する。
-/

namespace ProbabilityGeneratorQProof

/-- 有限register基底を添字順のBool列として読む、回路非依存の解析関数。 -/
def analyticRegisterBits {width : Nat} (basis : RegisterBasis width) : List Bool :=
  (List.finRange width).map basis

/-- source bit列をtarget bit列へXORする、回路非依存の解析関数。 -/
def analyticXorBits (source target : List Bool) : List Bool :=
  List.zipWith (fun sourceBit targetBit => sourceBit != targetBit) source target

/-- 自然数のlittle-endian bitを開始位置から指定幅だけ読む解析関数。 -/
def analyticConstantBitsAux (constant start : Nat) : Nat → List Bool
  | 0 => []
  | width + 1 =>
      constant.testBit start :: analyticConstantBitsAux constant (start + 1) width

/-- 自然数の下位`width` bitをlittle-endian順に並べる解析関数。 -/
def analyticConstantBits (constant width : Nat) : List Bool :=
  analyticConstantBitsAux constant 0 width

/-- 定数bit列を開始位置からtarget bit列へXORする、回路非依存の解析関数。 -/
def analyticXorConstantAux (constant start : Nat) : List Bool → List Bool
  | [] => []
  | bit :: bits =>
      (constant.testBit start != bit) ::
        analyticXorConstantAux constant (start + 1) bits

/-- 定数の下位bit列をtargetへlittle-endian順でXORする解析関数。 -/
def analyticXorConstant (constant : Nat) (bits : List Bool) : List Bool :=
  analyticXorConstantAux constant 0 bits

/-- column oracleの外部から観測可能な四つのaccumulator。 -/
@[ext] structure ColumnOracleObservation where
  /-- 出力configurationのdelimiter符号を受け取るregister。 -/
  rowOutput : List Bool
  /-- row selectorを受け取るregister。 -/
  selectorOutput : List Bool
  /-- 対角項の符号を受け取るbit。 -/
  negative : Bool
  /-- 受理の有無を受け取るbit。 -/
  active : Bool
deriving DecidableEq

/-- row oracleの外部から観測可能な三つのaccumulator。 -/
@[ext] structure RowOracleObservation where
  /-- predecessor configurationのdelimiter符号を受け取るregister。 -/
  columnKey : List Bool
  /-- predecessor側のcolumn selectorを受け取るregister。 -/
  columnSelector : List Bool
  /-- 受理の有無を受け取るbit。 -/
  keySignal : Bool
deriving DecidableEq

/-- column参照結果一個を外部accumulatorへXORする解析作用。 -/
def applyColumnReference {p : QParameters}
    (reference : ColumnReferenceResult p)
    (observation : ColumnOracleObservation) : ColumnOracleObservation :=
  { rowOutput := analyticXorBits
      (analyticRegisterBits (delimiterEncoding reference.output))
      observation.rowOutput
    selectorOutput := analyticXorConstant reference.rowSelector.val
      observation.selectorOutput
    negative := reference.negative != observation.negative
    active := !observation.active }

/-- `columnReference`の受理・不受理を含めたcolumn oracle全体の解析作用。 -/
def columnOracleAnalyticAction {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p)
    (observation : ColumnOracleObservation) : ColumnOracleObservation :=
  match columnReference configuration selector with
  | none => observation
  | some reference => applyColumnReference reference observation

/-- row参照結果一個を外部accumulatorへXORする解析作用。 -/
def applyRowReference {p : QParameters}
    (reference : RowReferenceResult p)
    (observation : RowOracleObservation) : RowOracleObservation :=
  { columnKey := analyticXorBits
      (analyticRegisterBits (delimiterEncoding reference.input))
      observation.columnKey
    columnSelector := analyticXorConstant reference.columnSelector.val
      observation.columnSelector
    keySignal := !observation.keySignal }

/-- `rowReference`の受理・不受理を含めたrow oracle全体の解析作用。 -/
def rowOracleAnalyticAction {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p)
    (observation : RowOracleObservation) : RowOracleObservation :=
  match rowReference configuration selector with
  | none => observation
  | some reference => applyRowReference reference observation

/--
event computeの八段階を、回路構文や基底回路実行関数を使わず解析関数の逐次適用だけで保持する。
-/
structure EventComputeAnalyticStates (basis : Type*) where
  /-- selector一致作用後の状態。 -/
  afterSelector : basis
  /-- source/arrival wordのmoved registerへの複写後。 -/
  afterMovedCopy : basis
  /-- 一歩の周期移動後。 -/
  afterMove : basis
  /-- membership解析作用後。 -/
  afterMembership : basis
  /-- branch条件をtargetへ書いた後。 -/
  afterBranch : basis
  /-- candidate列を準備した後。 -/
  afterCandidates : basis
  /-- candidate一点更新後。 -/
  afterModify : basis
  /-- bitonic sort解析作用後。 -/
  output : basis

/-- 八個の解析関数からevent computeのpure状態列を構成する。 -/
def buildEventComputeAnalyticStates {basis : Type*}
    (selector movedCopy move membership branch candidates modify sorting : basis → basis)
    (input : basis) : EventComputeAnalyticStates basis :=
  let afterSelector := selector input
  let afterMovedCopy := movedCopy afterSelector
  let afterMove := move afterMovedCopy
  let afterMembership := membership afterMove
  let afterBranch := branch afterMembership
  let afterCandidates := candidates afterBranch
  let afterModify := modify afterCandidates
  let output := sorting afterModify
  { afterSelector, afterMovedCopy, afterMove, afterMembership, afterBranch,
    afterCandidates, afterModify, output }

/-- event useの二writerを解析関数の逐次適用だけで保持する。 -/
structure EventUseAnalyticStates (basis : Type*) where
  /-- sorted delimiter writer後の状態。 -/
  afterSortedWriter : basis
  /-- moved selector writer後の最終use状態。 -/
  output : basis

/-- 二個のwriter解析関数からevent useのpure状態列を構成する。 -/
def buildEventUseAnalyticStates {basis : Type*}
    (sortedWriter selectorWriter : basis → basis) (input : basis) :
    EventUseAnalyticStates basis :=
  let afterSortedWriter := sortedWriter input
  let output := selectorWriter afterSortedWriter
  { afterSortedWriter, output }

end ProbabilityGeneratorQProof
