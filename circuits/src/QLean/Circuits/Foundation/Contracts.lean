import QLean.Circuits.Foundation.PermutationSemantics

/-!
# 回路と独立解析仕様を結ぶcomponent contract

厳密作用素、置換、clean変換、状態準備、block encodingに加え、部分空間作用と
抽象誤差modelに基づく近似作用素・近似状態準備を定義する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 回路の理想作用素が独立な解析作用素へ厳密一致する契約。 -/
structure ExactOperatorComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) where
  /-- 実装する回路構文木。 -/
  circuit : Circuit Gate
  /-- 回路意味論から独立に与える解析的目標作用素。 -/
  target : Operator basis
  /-- 回路意味論と目標作用素の全作用素等式。 -/
  correct : circuit.denote gateOperator = target

/--
回路の理想作用素が独立な解析作用素へ厳密一致し、その解析作用素がユニタリである契約。

ユニタリ性を回路構文木から毎回再導出せず公開 field として保持することで、逐次合成、
逆実行、反復、制御化などの親 component は子 component の公開契約だけを利用できる。
-/
structure UnitaryExactOperatorComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    extends ExactOperatorComponent gateOperator where
  /-- 回路非依存 target はユニタリである。 -/
  target_unitary : target ∈ Matrix.unitaryGroup basis ℂ

/-- 可逆回路の基底作用と全作用素を同じ解析置換へ結ぶ契約。 -/
structure PermutationComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (gatePermutation : Gate → Equiv.Perm basis) where
  /-- 実装する可逆回路構文木。 -/
  circuit : Circuit Gate
  /-- 回路から独立に与える解析的基底置換。 -/
  reference : Equiv.Perm basis
  /-- 基底実行が解析置換と一致する。 -/
  runBasis_correct : ∀ input,
    circuit.runBasis gatePermutation input = reference input
  /-- 置換行列規約を含む全作用素等式。 -/
  operator_correct : circuit.denote gateOperator = reference⁻¹.permMatrix ℂ

/-- clean入力上の基底変換、出力条件、work復元を束ねる契約。 -/
structure CleanComponent
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis) where
  /-- 実装する可逆回路構文木。 -/
  circuit : Circuit Gate
  /-- clean入力上で実装すべき解析関数。 -/
  reference : basis → basis
  /-- 契約を適用できる入力条件。 -/
  inputCondition : basis → Prop
  /-- 解析出力が満たす条件。 -/
  outputCondition : basis → Prop
  /-- 入出力間で保存・復元される情報。 -/
  restoration : basis → basis → Prop
  /-- clean入力上の基底作用一致。 -/
  runBasis_correct : ∀ input, inputCondition input →
    circuit.runBasis gatePermutation input = reference input
  /-- 解析出力が出力条件を満たす。 -/
  outputCondition_correct : ∀ input, inputCondition input →
    outputCondition (reference input)
  /-- 解析入出力が復元関係を満たす。 -/
  restoration_correct : ∀ input, inputCondition input →
    restoration input (reference input)

/-- 指定した状態部分空間上でのみ厳密作用素一致を要求する契約。 -/
structure SubspaceMapComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) where
  /-- 実装する回路構文木。 -/
  circuit : Circuit Gate
  /-- 回路から独立に与える解析的作用素。 -/
  target : Operator basis
  /-- 正しさを要求する coherent な入力部分空間。 -/
  inputSubspace : Submodule ℂ (State basis)
  /-- 解析作用後の状態が属する coherent な出力部分空間。 -/
  outputSubspace : Submodule ℂ (State basis)
  /-- 入力部分空間上で回路作用と解析作用が一致する。 -/
  correct : ∀ state, state ∈ inputSubspace →
    applyOperator (circuit.denote gateOperator) state =
      applyOperator target state
  /-- 解析作用は入力部分空間を出力部分空間へ写す。 -/
  target_maps : ∀ state, state ∈ inputSubspace →
    applyOperator target state ∈ outputSubspace

/-- 同一部分空間を保存する `SubspaceMapComponent` の特殊化。 -/
structure SubspaceOperatorComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) where
  /-- 実装する回路構文木。 -/
  circuit : Circuit Gate
  /-- 回路から独立に与える解析的目標作用素。 -/
  target : Operator basis
  /-- 正しさを要求する、線形結合で閉じた状態部分空間。 -/
  subspace : Submodule ℂ (State basis)
  /-- 指定部分空間内の全状態で作用が一致する。 -/
  correct : ∀ state, state ∈ subspace →
    applyOperator (circuit.denote gateOperator) state =
      applyOperator target state
  /-- 解析targetは次の部分空間componentへ渡せるよう部分空間を保存する。 -/
  target_preserves : ∀ state, state ∈ subspace →
    applyOperator target state ∈ subspace

/-- 特定の初期状態を独立な解析的目標状態へ厳密準備する契約。 -/
structure StatePreparationComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) where
  /-- 状態準備回路。 -/
  circuit : Circuit Gate
  /-- 回路から独立に与える初期状態。 -/
  initialState : State basis
  /-- 回路から独立に与える目標状態。 -/
  targetState : State basis
  /-- 回路作用後の状態が目標状態へ一致する。 -/
  correct : applyOperator (circuit.denote gateOperator) initialState = targetState

/-- 任意の対象型に対する非負誤差付き近似関係の一般interface。 -/
structure ErrorModel (object : Type*) where
  /-- `actual`が`target`を誤差`error`以内で近似するという関係。 -/
  approx : object → object → ℝ → Prop
  /-- 同じ対象同士の誤差は0。 -/
  refl : ∀ value, approx value value 0
  /-- 誤差上限を大きくしても近似関係は保たれる。 -/
  weaken : ∀ {actual target smaller larger},
    approx actual target smaller → smaller ≤ larger →
      approx actual target larger
  /-- 中間対象を介した誤差は加法合成できる。 -/
  triangle : ∀ {first second third firstError secondError},
    approx first second firstError →
      approx second third secondError →
      approx first third (firstError + secondError)

/-- contraction条件を明示して作用素積と共役転置の誤差を合成する作用素誤差model。 -/
structure OperatorErrorModel (basis : Type*) [Fintype basis] [DecidableEq basis]
    extends ErrorModel (Operator basis) where
  /-- 逐次誤差加算でnorm増幅を起こさない作用素という条件。 -/
  isContraction : Operator basis → Prop
  /-- 恒等作用素はcontractionである。 -/
  identity_contraction : isContraction 1
  /-- contraction同士の積もcontractionである。 -/
  multiplication_contraction : ∀ {second first},
    isContraction second → isContraction first →
      isContraction (second * first)
  /-- 右のactual firstと左のtarget secondがcontractionなら局所誤差を加算する。 -/
  multiplication : ∀ {actualFirst targetFirst actualSecond targetSecond
      firstError secondError},
    approx actualFirst targetFirst firstError →
      approx actualSecond targetSecond secondError →
      0 ≤ firstError →
      0 ≤ secondError →
      isContraction actualFirst →
      isContraction targetSecond →
      approx (actualSecond * actualFirst) (targetSecond * targetFirst)
        (firstError + secondError)

/-- 抽象作用素誤差modelに対する近似作用素component。 -/
structure ApproxOperatorComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (errorModel : OperatorErrorModel basis) where
  /-- 実装する回路構文木。 -/
  circuit : Circuit Gate
  /-- 回路から独立に与える解析的目標作用素。 -/
  target : Operator basis
  /-- 証明済み誤差上限。 -/
  error : ℝ
  /-- 誤差上限は非負。 -/
  error_nonnegative : 0 ≤ error
  /-- 実回路作用素は逐次誤差合成で増幅を起こさない。 -/
  actual_contraction : errorModel.isContraction (circuit.denote gateOperator)
  /-- 解析targetも逐次誤差合成で増幅を起こさない。 -/
  target_contraction : errorModel.isContraction target
  /-- 回路作用素が目標作用素を宣言誤差以内で近似する。 -/
  correct : errorModel.approx (circuit.denote gateOperator) target error

/-- 状態に対する抽象誤差model。 -/
abbrev StateErrorModel (basis : Type*) := ErrorModel (State basis)

/-- 抽象状態誤差modelに対する近似状態準備component。 -/
structure ApproxStatePreparationComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (errorModel : StateErrorModel basis) where
  /-- 状態準備回路。 -/
  circuit : Circuit Gate
  /-- 回路から独立な初期状態。 -/
  initialState : State basis
  /-- 回路から独立な目標状態。 -/
  targetState : State basis
  /-- 証明済み誤差上限。 -/
  error : ℝ
  /-- 誤差上限は非負。 -/
  error_nonnegative : 0 ≤ error
  /-- 準備後状態が目標状態を宣言誤差以内で近似する。 -/
  correct : errorModel.approx
    (applyOperator (circuit.denote gateOperator) initialState) targetState error

/-- success blockを解析targetへ結ぶ、誤差model非依存なblock encoding契約。 -/
structure BlockEncodingComponent
    {Gate fullBasis systemBasis : Type*}
    [Fintype fullBasis] [DecidableEq fullBasis]
    (gateOperator : Gate → Operator fullBasis)
    (errorModel : ErrorModel (Operator systemBasis)) where
  /-- block encoding回路。 -/
  circuit : Circuit Gate
  /-- system基底をsuccess部分空間へ埋め込む写像。 -/
  successEmbedding : systemBasis ↪ fullBasis
  /-- 回路から独立な解析的目標作用素。 -/
  target : Operator systemBasis
  /-- success blockへ掛ける正規化係数。 -/
  scale : ℝ
  /-- 証明済み誤差上限。 -/
  error : ℝ
  /-- 正規化係数は正。 -/
  scale_positive : 0 < scale
  /-- 誤差上限は非負。 -/
  error_nonnegative : 0 ≤ error
  /-- 正規化済みsuccess blockがtargetを宣言誤差以内で近似する。 -/
  correct : errorModel.approx
    ((scale : ℂ) • successBlock successEmbedding (circuit.denote gateOperator))
    target error

/-- Standard block encoding contract whose full implementation operator is unitary. -/
structure UnitaryBlockEncodingComponent
    {Gate fullBasis systemBasis : Type*}
    [Fintype fullBasis] [DecidableEq fullBasis]
    (gateOperator : Gate → Operator fullBasis)
    (errorModel : ErrorModel (Operator systemBasis)) extends
      BlockEncodingComponent gateOperator errorModel where
  /-- The complete circuit denotation, not only its success block, is unitary. -/
  actual_unitary : circuit.denote gateOperator ∈
    Matrix.unitaryGroup fullBasis ℂ

/-- Forget the full-space unitary certificate and retain the block contract. -/
def UnitaryBlockEncodingComponent.toBlockEncoding
    {Gate fullBasis systemBasis : Type*}
    [Fintype fullBasis] [DecidableEq fullBasis]
    {gateOperator : Gate → Operator fullBasis}
    {errorModel : ErrorModel (Operator systemBasis)}
    (component : UnitaryBlockEncodingComponent gateOperator errorModel) :
    BlockEncodingComponent gateOperator errorModel :=
  component.toBlockEncodingComponent

/-- 置換componentを解析置換行列targetを持つ厳密作用素componentとして読む。 -/
def PermutationComponent.toExactOperatorComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {gatePermutation : Gate → Equiv.Perm basis}
    (component : PermutationComponent gateOperator gatePermutation) :
    ExactOperatorComponent gateOperator where
  circuit := component.circuit
  target := component.reference⁻¹.permMatrix ℂ
  correct := component.operator_correct

/-- ユニタリ厳密componentを通常の厳密作用素componentとして忘却する公開境界。 -/
def UnitaryExactOperatorComponent.toExact
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : UnitaryExactOperatorComponent gateOperator) :
    ExactOperatorComponent gateOperator :=
  component.toExactOperatorComponent

/-- 厳密componentと独立targetのユニタリ性からユニタリ厳密componentを構成する。 -/
def ExactOperatorComponent.withUnitaryTarget
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ExactOperatorComponent gateOperator)
    (targetUnitary : component.target ∈ Matrix.unitaryGroup basis ℂ) :
    UnitaryExactOperatorComponent gateOperator where
  toExactOperatorComponent := component
  target_unitary := targetUnitary

/-- ユニタリ厳密componentの実回路作用素もユニタリである。 -/
theorem UnitaryExactOperatorComponent.actual_unitary
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : UnitaryExactOperatorComponent gateOperator) :
    component.circuit.denote gateOperator ∈ Matrix.unitaryGroup basis ℂ := by
  rw [component.correct]
  exact component.target_unitary

end

end VerifiedCircuitCore
