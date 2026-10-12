import Mathlib

/-!
# 確率生成子の回路非依存な解析定義

物理eventの数え上げと確率生成子を、回路AST・意味論・実装moduleをimportせずに定義する。
-/

namespace ProbabilityGeneratorQProof.TechnicalReportQ

noncomputable section

/-- 入力配置から出力配置へ移るactiveな物理eventの個数。 -/
def transitionCount
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration)
    (output input : Configuration) : Nat :=
  ((events input).filter fun event => update input event = output).card

/-- 技術レポートの列規約で定義した確率生成子`Q`。 -/
def probabilityGenerator
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (particleCount : Configuration → Nat)
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration)
    (output input : Configuration) : ℚ :=
  if output = input then
    -(particleCount input : ℚ)
  else
    (transitionCount events update output input : ℚ) / 2

/-- 二つの負の対角copyと正の移動eventを合計した未正規化selector内積。 -/
def rawSelectorOverlap
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (particleCount : Configuration → Nat)
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration)
    (output input : Configuration) : ℚ :=
  -(2 * (particleCount input : ℚ)) * (if output = input then 1 else 0) +
    (transitionCount events update output input : ℚ)

/-- `6K`個のselectorを両側で一様準備した後の正規化selector内積。 -/
def normalizedSelectorOverlap
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (K : Nat)
    (particleCount : Configuration → Nat)
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration)
    (output input : Configuration) : ℚ :=
  rawSelectorOverlap particleCount events update output input / (6 * (K : ℚ))

/-- 自己ループeventがなければ、自己遷移を数えるfilterは空になる。 -/
theorem transitionCount_self_eq_zero
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration)
    (noSelfLoop : ∀ input event, event ∈ events input → update input event ≠ input)
    (input : Configuration) :
    transitionCount events update input input = 0 := by
  rw [transitionCount, Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro event eventMem
  exact noSelfLoop input event eventMem

/-- 未正規化selector内積は、確率生成子の各行列要素のちょうど2倍である。 -/
theorem rawSelectorOverlap_eq_two_mul_probabilityGenerator
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (particleCount : Configuration → Nat)
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration)
    (noSelfLoop : ∀ input event, event ∈ events input → update input event ≠ input)
    (output input : Configuration) :
    rawSelectorOverlap particleCount events update output input =
      2 * probabilityGenerator particleCount events update output input := by
  by_cases same : output = input
  · subst output
    simp [rawSelectorOverlap, probabilityGenerator,
      transitionCount_self_eq_zero events update noSelfLoop input]
  · simp [rawSelectorOverlap, probabilityGenerator, same]
    ring

/-- 正規化selector内積は、正規化係数`α_Q = 3K`で割った生成子要素に等しい。 -/
theorem normalizedSelectorOverlap_eq_probabilityGenerator_div
    {Configuration Event : Type*}
    [DecidableEq Configuration] [DecidableEq Event]
    (K : Nat)
    (positiveK : 0 < K)
    (particleCount : Configuration → Nat)
    (events : Configuration → Finset Event)
    (update : Configuration → Event → Configuration)
    (noSelfLoop : ∀ input event, event ∈ events input → update input event ≠ input)
    (output input : Configuration) :
    normalizedSelectorOverlap K particleCount events update output input =
      probabilityGenerator particleCount events update output input / (3 * (K : ℚ)) := by
  rw [normalizedSelectorOverlap,
    rawSelectorOverlap_eq_two_mul_probabilityGenerator particleCount events update noSelfLoop]
  have nonzeroK : (K : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positiveK)
  field_simp [nonzeroK]
  ring

end

end ProbabilityGeneratorQProof.TechnicalReportQ
