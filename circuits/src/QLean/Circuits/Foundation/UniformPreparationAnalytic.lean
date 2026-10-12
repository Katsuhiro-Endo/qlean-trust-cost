import QLean.Circuits.Foundation.PrimitiveOperatorSemantics
import QLean.Circuits.Foundation.QubitBasisEncoding

/-!
# 任意サイズ一様状態準備の回路非依存解析仕様

`0 < N ≤ 2^w`に対し、先頭`N`計算基底を一様化する二分木回転計画を
厳密な記号角度で定義する。このmoduleは回路ASTや回路意味論を参照しない。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 一様準備計画の閉じた角度式を評価する。計画は自由記号を含まないため、記号環境は零で固定する。 -/
def AngleExpr.uniformValue (angle : AngleExpr) : ℝ :=
  angle.eval (fun _ => 0)

/-- 任意サイズ一様準備の正値・容量条件付きパラメータ。 -/
structure UniformPreparationParameters where
  /-- selector register幅。 -/
  width : Nat
  /-- 一様化する有効基底数。 -/
  validCount : Nat
  /-- 有効基底数は正である。 -/
  validCountPositive : 0 < validCount
  /-- 有効基底数はregister容量以内である。 -/
  validCountLeCapacity : validCount ≤ 2 ^ width

/-- 一個の多重Bool制御回転を表すwire割当前の実行可能な命令。 -/
structure UniformRotationInstruction where
  /-- 回転するselector bit位置。 -/
  target : Nat
  /-- 既に確定した上位bit位置と要求Bool。 -/
  controls : List (Nat × Bool)
  /-- targetへ適用する厳密な記号`Ry`角。 -/
  angle : AngleExpr

/-- `left+right` leafを左右へ分けるための厳密な`Ry`角。 -/
def uniformSplitAngle (left right : Nat) : AngleExpr :=
  if positive : 0 < left + right then
    .mul (.rational 2 1 (by decide))
      (.acos (.sqrt (.rational (Int.ofNat left) (left + right) positive)))
  else .rational 0 1 (by decide)

/-- 正の総leaf数に対する分割角の実数意味論。 -/
theorem uniformSplitAngle_eval (symbolValue : String → ℝ)
    (left right : Nat) (positive : 0 < left + right) :
    (uniformSplitAngle left right).eval symbolValue =
      2 * Real.arccos (Real.sqrt ((left : ℝ) / (left + right : ℝ))) := by
  simp [uniformSplitAngle, positive, AngleExpr.eval]

/-- 分割回転の上側振幅は左部分木のleaf比の平方根になる。 -/
theorem cos_half_uniformSplitAngle (symbolValue : String → ℝ)
    (left right : Nat) (positive : 0 < left + right) :
    Real.cos ((uniformSplitAngle left right).eval symbolValue / 2) =
      Real.sqrt ((left : ℝ) / (left + right : ℝ)) := by
  rw [uniformSplitAngle_eval symbolValue left right positive]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  apply Real.cos_arccos
  · exact le_trans (by norm_num) (Real.sqrt_nonneg _)
  · rw [Real.sqrt_le_one]
    have denominatorPositive : (0 : ℝ) < left + right := by
      exact_mod_cast positive
    rw [div_le_one denominatorPositive]
    exact_mod_cast Nat.le_add_right left right

/-- 分割回転の下側振幅は右部分木のleaf比の平方根になる。 -/
theorem sin_half_uniformSplitAngle (symbolValue : String → ℝ)
    (left right : Nat) (positive : 0 < left + right) :
    Real.sin ((uniformSplitAngle left right).eval symbolValue / 2) =
      Real.sqrt ((right : ℝ) / (left + right : ℝ)) := by
  rw [uniformSplitAngle_eval symbolValue left right positive]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.sin_arccos]
  congr 1
  have denominatorPositive : (0 : ℝ) < left + right := by
    exact_mod_cast positive
  have ratioNonnegative : (0 : ℝ) ≤ left / (left + right) := by positivity
  rw [Real.sq_sqrt ratioNonnegative]
  field_simp
  ring

/-- 幅`width`の二分木で先頭`validCount` leafだけを一様化する回転計画。 -/
def uniformRotationPlan : (width validCount : Nat) →
    List UniformRotationInstruction
  | 0, _ => []
  | width + 1, validCount =>
      if zero : validCount = 0 then []
      else
        let halfCapacity := 2 ^ width
        let leftCount := min validCount halfCapacity
        let rightCount := validCount - leftCount
        let root : UniformRotationInstruction :=
          ⟨width, [], uniformSplitAngle leftCount rightCount⟩
        let leftPlan := (uniformRotationPlan width leftCount).map fun instruction =>
          { instruction with controls := (width, false) :: instruction.controls }
        let rightPlan := (uniformRotationPlan width rightCount).map fun instruction =>
          { instruction with controls := (width, true) :: instruction.controls }
        root :: (leftPlan ++ rightPlan)
termination_by width => width

/-- 回転命令の全wire番号が幅内にあり、targetがcontrolsに含まれないこと。 -/
def UniformRotationInstruction.WellFormed
    (width : Nat) (instruction : UniformRotationInstruction) : Prop :=
  instruction.target < width ∧
    (∀ control ∈ instruction.controls, control.1 < width) ∧
    instruction.target ∉ instruction.controls.map Prod.fst ∧
    (instruction.controls.map Prod.fst).Nodup

/-- controlを一個追加しても元命令が下位幅で正しければ全体幅で正しい。 -/
theorem UniformRotationInstruction.wellFormed_addControl
    {width : Nat} {instruction : UniformRotationInstruction}
    (wellFormed : instruction.WellFormed width) (value : Bool) :
    ({ instruction with controls := (width, value) :: instruction.controls } :
      UniformRotationInstruction).WellFormed (width + 1) := by
  rcases wellFormed with
    ⟨targetBound, controlBounds, targetFresh, controlsNodup⟩
  refine ⟨Nat.lt_succ_of_lt targetBound, ?_, ?_, ?_⟩
  · intro control member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp
    · exact lt_trans (controlBounds control member) (by omega)
  · simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨ne_of_lt targetBound, targetFresh⟩
  · simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro member
      rcases List.mem_map.mp member with ⟨control, controlMember, firstEqual⟩
      have bound := controlBounds control controlMember
      omega
    · exact controlsNodup

/-- `N ≤ 2^w`なら生成した全回転命令は幅`w`内で型安全である。 -/
theorem uniformRotationPlan_wellFormed
    (width validCount : Nat) (capacity : validCount ≤ 2 ^ width) :
    ∀ instruction ∈ uniformRotationPlan width validCount,
      instruction.WellFormed width := by
  induction width generalizing validCount with
  | zero => simp [uniformRotationPlan]
  | succ width inductionHypothesis =>
      intro instruction member
      by_cases zero : validCount = 0
      · simp [uniformRotationPlan, zero] at member
      · simp [uniformRotationPlan, zero] at member
        rcases member with rfl | leftMember | rightMember
        · simp [UniformRotationInstruction.WellFormed]
        · rcases leftMember with ⟨sourceInstruction, sourceMember, rfl⟩
          apply UniformRotationInstruction.wellFormed_addControl
          apply inductionHypothesis (min validCount (2 ^ width))
          · exact min_le_right _ _
          · exact sourceMember
        · rcases rightMember with ⟨sourceInstruction, sourceMember, rfl⟩
          apply UniformRotationInstruction.wellFormed_addControl
          apply inductionHypothesis (validCount - min validCount (2 ^ width))
          · rw [Nat.pow_succ] at capacity
            omega
          · exact sourceMember

/-- 正値・容量条件付きparameterから得る型安全な一様回転計画。 -/
def uniformPreparationRotationPlan (parameters : UniformPreparationParameters) :
    List UniformRotationInstruction :=
  uniformRotationPlan parameters.width parameters.validCount

/-- parameter化した一様回転計画の全命令は幅内でwell-formedである。 -/
theorem uniformPreparationRotationPlan_wellFormed
    (parameters : UniformPreparationParameters) :
    ∀ instruction ∈ uniformPreparationRotationPlan parameters,
      instruction.WellFormed parameters.width :=
  uniformRotationPlan_wellFormed parameters.width parameters.validCount
    parameters.validCountLeCapacity

/-- 先頭`N`計算基底へ振幅`1/√N`を与えpaddingを零にする独立target state。 -/
def uniformPreparationTargetState (parameters : UniformPreparationParameters) :
    State (QubitBasis parameters.width) :=
  fun basis =>
    if qubitBasisLittleEndianIndex parameters.width basis < parameters.validCount then
      (1 / Real.sqrt parameters.validCount : ℝ)
    else 0

/-- local compiler全幅`2w`の前半からselector基底を取り出す。 -/
def uniformPreparationSelectorBasis (width : Nat)
    (basis : QubitBasis (2 * width)) : QubitBasis width :=
  fun wire => basis ⟨wire.val, by omega⟩

/-- local compiler全幅`2w`の後半scratchが全零であること。 -/
def uniformPreparationScratchZero (width : Nat)
    (basis : QubitBasis (2 * width)) : Prop :=
  ∀ wire : Fin width, basis ⟨width + wire.val, by omega⟩ = false

/-- selector一様状態とclean scratch零状態を合わせたlocal compiler全幅target。 -/
def uniformPreparationFullTargetState
    (parameters : UniformPreparationParameters) :
    State (QubitBasis (2 * parameters.width)) := by
  classical
  exact fun basis =>
    if uniformPreparationScratchZero parameters.width basis then
      uniformPreparationTargetState parameters
        (uniformPreparationSelectorBasis parameters.width basis)
    else 0

end

end VerifiedCircuitCore
