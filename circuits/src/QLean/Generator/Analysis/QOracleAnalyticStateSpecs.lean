import QLean.Generator.Analysis.QComponentAnalyticSpecs

/-!
# Q event oracle の抽象的な解析状態

このファイルは、event compute を八つの純粋関数の合成として記述する。
物理 wire 配置や基本回路の実装は参照せず、検証側が各子部品の独立な
解析参照関数をこの抽象仕様へ代入する。
-/

namespace ProbabilityGeneratorQProof

namespace OracleAnalytic

/-- event compute の八段階を与える、回路実装から独立した解析参照関数族。 -/
structure EventPrimitiveReferences (State : Type) where
  /-- selector が当該 branch と一致するかを計算する解析関数。 -/
  selector : State → State
  /-- 入力語を moved register へ複写する解析関数。 -/
  moved : State → State
  /-- 座標を一段移動する解析関数。 -/
  move : State → State
  /-- membership 条件を計算する解析関数。 -/
  membership : State → State
  /-- branch 受理条件を計算する解析関数。 -/
  branch : State → State
  /-- candidate 列を準備する解析関数。 -/
  candidates : State → State
  /-- candidate を event に応じて更新する解析関数。 -/
  modify : State → State
  /-- candidate 列を sort する解析関数。 -/
  sort : State → State

/-- 八つの子部品の解析参照関数を順に合成した、event compute の解析状態記録。 -/
def eventStates {State : Type} (references : EventPrimitiveReferences State)
    (input : State) : EventComputeAnalyticStates State :=
  buildEventComputeAnalyticStates references.selector references.moved
    references.move references.membership references.branch references.candidates
    references.modify references.sort input

end OracleAnalytic

end ProbabilityGeneratorQProof
