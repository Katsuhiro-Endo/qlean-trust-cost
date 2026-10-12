import QLean.Generator.Analysis.AngleExpr
import QLean.Generator.Analysis.QParameters
import Mathlib.Tactic

/-!
# 非2冪一様準備の記号回転計画

`N ≤ 2^w`に対し、MSBから二分木をたどる制御`Ry`列を生成する。各nodeの角度は左右の
有効leaf数だけから作る記号式であり、padding leafの個数は0として扱う。
-/

namespace ProbabilityGeneratorQProof

/-- 一個の多重制御回転を表す、wire割当前の実行可能な命令。 -/
structure UniformRotationInstruction where
  /-- 回転するselector bit位置。 -/
  target : Nat
  /-- 既に確定した上位bit位置と要求Bool。 -/
  controls : List (Nat × Bool)
  /-- targetへ適用する記号`Ry`角。 -/
  angle : AngleExpr
deriving DecidableEq, Repr

/-- `left+right` leafを左右へ分けるための厳密な`Ry`角。 -/
def uniformSplitAngle (left right : Nat) : AngleExpr :=
  if _positive : 0 < left + right then
    .twice (.acos (.sqrt (.rational ((left : ℚ) / (left + right : ℚ)))))
  else
    .rational 0

/-- 正の総leaf数に対する分割角の実数意味論。 -/
theorem uniformSplitAngle_toReal
    (left right : Nat) (positive : 0 < left + right) :
    (uniformSplitAngle left right).toReal =
      2 * Real.arccos (Real.sqrt ((left : ℝ) / (left + right : ℝ))) := by
  simp [uniformSplitAngle, positive, AngleExpr.toReal, AngleExpr.twice]

/-- 分割回転の上側振幅は左部分木のleaf比の平方根になる。 -/
theorem cos_half_uniformSplitAngle
    (left right : Nat) (positive : 0 < left + right) :
    Real.cos ((uniformSplitAngle left right).toReal / 2) =
      Real.sqrt ((left : ℝ) / (left + right : ℝ)) := by
  rw [uniformSplitAngle_toReal left right positive]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  apply Real.cos_arccos
  · exact le_trans (by norm_num) (Real.sqrt_nonneg _)
  · rw [Real.sqrt_le_one]
    have denominatorPositive : (0 : ℝ) < left + right := by
      exact_mod_cast positive
    rw [div_le_one denominatorPositive]
    exact_mod_cast Nat.le_add_right left right

/-- 分割回転の下側振幅は右部分木のleaf比の平方根になる。 -/
theorem sin_half_uniformSplitAngle
    (left right : Nat) (positive : 0 < left + right) :
    Real.sin ((uniformSplitAngle left right).toReal / 2) =
      Real.sqrt ((right : ℝ) / (left + right : ℝ)) := by
  rw [uniformSplitAngle_toReal left right positive]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.sin_arccos]
  congr 1
  have denominatorPositive : (0 : ℝ) < left + right := by exact_mod_cast positive
  have ratioNonnegative : (0 : ℝ) ≤ left / (left + right) := by positivity
  rw [Real.sq_sqrt ratioNonnegative]
  field_simp
  ring

/-- 幅`w`の二分木で先頭`validCount` leafだけを一様化する回転計画。 -/
def uniformRotationPlan : (width validCount : Nat) → List UniformRotationInstruction
  | 0, _ => []
  | width + 1, validCount =>
      if zero : validCount = 0 then
        []
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

/-- controlを一個追加しても、元命令がその下位幅で正しければ全体幅で正しい。 -/
theorem UniformRotationInstruction.wellFormed_addControl
    {width : Nat} {instruction : UniformRotationInstruction}
    (wellFormed : instruction.WellFormed width) (value : Bool) :
    ({ instruction with controls := (width, value) :: instruction.controls } :
      UniformRotationInstruction).WellFormed (width + 1) := by
  rcases wellFormed with ⟨targetBound, controlBounds, targetFresh, controlsNodup⟩
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

/-- `N ≤ 2^w`なら生成した全回転命令は幅`w`内で型安全に割当て可能である。 -/
theorem uniformRotationPlan_wellFormed
    (width validCount : Nat) (capacity : validCount ≤ 2 ^ width) :
    ∀ instruction ∈ uniformRotationPlan width validCount,
      instruction.WellFormed width := by
  induction width generalizing validCount with
  | zero =>
      simp [uniformRotationPlan]
  | succ width inductionHypothesis =>
      intro instruction member
      by_cases zero : validCount = 0
      · simp [uniformRotationPlan, zero] at member
      · simp [uniformRotationPlan, zero] at member
        rcases member with rfl | leftMember | rightMember
        ·
          simp [UniformRotationInstruction.WellFormed]
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

/-- Q回路の`N=6K` selector用回転計画。 -/
def qUniformRotationPlan (p : QParameters) : List UniformRotationInstruction :=
  uniformRotationPlan p.selectorWidth p.selectorCount

/-- Q用一様準備計画の全命令はselector幅内でwell-formedである。 -/
theorem qUniformRotationPlan_wellFormed (p : QParameters) :
    ∀ instruction ∈ qUniformRotationPlan p,
      instruction.WellFormed p.selectorWidth :=
  uniformRotationPlan_wellFormed p.selectorWidth p.selectorCount
    p.selectorCount_le_capacity

/-- 一様準備計画は`N=0`なら回転を一個も生成しない。 -/
@[simp] theorem uniformRotationPlan_zero (width : Nat) :
    uniformRotationPlan width 0 = [] := by
  cases width <;> simp [uniformRotationPlan]

end ProbabilityGeneratorQProof
