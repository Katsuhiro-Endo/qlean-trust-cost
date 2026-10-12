import QLean.Generator.Analysis.QComponentAnalyticSpecs
import QLean.Generator.Analysis.QOracleAnalyticStateSpecs

/-!
# Q oracle の実装非依存な具体仕様interface

oracle の外部観測条件と、観測外の状態を入力へ戻す条件を別々の純粋な関係として受け取り、
一つの解析契約へ束ねる。このmoduleは物理ゲート列やその実行意味論を参照しない。
-/

namespace ProbabilityGeneratorQProof

/-- 解析的な外部観測関係と、観測外状態の復元関係を束ねる純粋な契約。 -/
structure RestoredObservationSpec {basis : Type*}
    (observation restoration : basis → basis → Prop)
    (input output : basis) : Prop where
  /-- 出力の外部観測値が独立な解析関係を満たす。 -/
  observation_correct : observation input output
  /-- 観測に使わない状態が入力値へ復元される。 -/
  restoration_correct : restoration input output

/-- 一意な解析出力が存在するときだけその出力を選び、それ以外では入力を返す純粋な参照関数。 -/
noncomputable def uniqueAnalyticReference
    {basis : Type*} (specification : basis → basis → Prop)
    (input : basis) : basis := by
  classical
  by_cases uniqueOutput : ∃! output, specification input output
  · exact Classical.choose uniqueOutput.exists
  · exact input

/-- 一意な解析出力が存在すれば、純粋な参照関数自身もその解析契約を満たす。 -/
theorem uniqueAnalyticReference_spec
    {basis : Type*} {specification : basis → basis → Prop}
    {input : basis} (uniqueOutput : ∃! output, specification input output) :
    specification input (uniqueAnalyticReference specification input) := by
  classical
  unfold uniqueAnalyticReference
  split
  · exact Classical.choose_spec uniqueOutput.exists
  · contradiction

/-- 一意な解析出力は、同じ契約を満たす任意の候補と純粋な参照関数を一致させる。 -/
theorem uniqueAnalyticReference_eq
    {basis : Type*} {specification : basis → basis → Prop}
    {input output : basis} (uniqueOutput : ∃! result, specification input result)
    (outputSpec : specification input output) :
    uniqueAnalyticReference specification input = output := by
  exact uniqueOutput.unique (uniqueAnalyticReference_spec uniqueOutput) outputSpec

end ProbabilityGeneratorQProof
