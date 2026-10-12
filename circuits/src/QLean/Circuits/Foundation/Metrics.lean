import QLean.Circuits.Foundation.Contracts
import VerifiedMath.FiniteDistribution

/-!
# L2状態誤差と全変動距離

有限基底上で直接計算できる二種類の誤差尺度を定義し、それぞれの状態準備契約を与える。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 二状態のL2距離。 -/
def l2Distance {basis : Type*} [Fintype basis]
    (left right : State basis) : ℝ :=
  Real.sqrt (∑ index, Complex.normSq (left index - right index))

/-- L2距離は非負である。 -/
theorem l2Distance_nonnegative
    {basis : Type*} [Fintype basis] (left right : State basis) :
    0 ≤ l2Distance left right :=
  Real.sqrt_nonneg _

/-- 同じ状態同士のL2距離は0である。 -/
@[simp] theorem l2Distance_self
    {basis : Type*} [Fintype basis] (state : State basis) :
    l2Distance state state = 0 := by
  simp [l2Distance]

/-- 計算基底測定で状態が与える確率。 -/
def basisProbability {basis : Type*} (state : State basis) (index : basis) : ℝ :=
  Complex.normSq (state index)

/-- 状態の計算基底確率の総和が1であるという正規化条件。 -/
def IsNormalizedState {basis : Type*} [Fintype basis]
    (state : State basis) : Prop :=
  ∑ index, basisProbability state index = 1

/-- 正規化状態の各計算基底振幅のnormは1以下である。 -/
theorem norm_le_one_of_normalized
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {state : State basis} (normalized : IsNormalizedState state) (index : basis) :
    ‖state index‖ ≤ 1 := by
  have singleTerm :
      Complex.normSq (state index) ≤ ∑ current, Complex.normSq (state current) := by
    exact Finset.single_le_sum
      (fun current _ => Complex.normSq_nonneg (state current))
      (Finset.mem_univ index)
  have squareBound : ‖state index‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    rw [Complex.sq_norm]
    simpa [IsNormalizedState, basisProbability] using
      singleTerm.trans_eq normalized
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp squareBound

/-- 正規化二状態について、一基底点の確率差を振幅差で上から抑える。 -/
theorem basisProbability_sub_le_two_mul_norm
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {left right : State basis}
    (leftNormalized : IsNormalizedState left)
    (rightNormalized : IsNormalizedState right) (index : basis) :
    |basisProbability left index - basisProbability right index| ≤
      2 * ‖left index - right index‖ := by
  have leftBound := norm_le_one_of_normalized leftNormalized index
  have rightBound := norm_le_one_of_normalized rightNormalized index
  have sumBound : |‖left index‖ + ‖right index‖| ≤ (2 : ℝ) := by
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    linarith
  calc
    |basisProbability left index - basisProbability right index| =
        |‖left index‖ ^ 2 - ‖right index‖ ^ 2| := by
          rw [basisProbability, basisProbability, Complex.sq_norm, Complex.sq_norm]
    _ = |(‖left index‖ - ‖right index‖) *
        (‖left index‖ + ‖right index‖)| := by
          congr 1
          ring
    _ = |‖left index‖ - ‖right index‖| *
        |‖left index‖ + ‖right index‖| := abs_mul _ _
    _ ≤ ‖left index - right index‖ *
        |‖left index‖ + ‖right index‖| := by
          exact mul_le_mul_of_nonneg_right
            (abs_norm_sub_norm_le (left index) (right index)) (abs_nonneg _)
    _ ≤ ‖left index - right index‖ * 2 := by
          exact mul_le_mul_of_nonneg_left sumBound (norm_nonneg _)
    _ = 2 * ‖left index - right index‖ := by ring

/-- 二状態の計算基底測定分布間の全変動距離。 -/
def totalVariationDistance {basis : Type*} [Fintype basis]
    (left right : State basis) : ℝ :=
  VerifiedMath.FiniteDistribution.totalVariation
    (basisProbability left) (basisProbability right)

theorem totalVariationDistance_eq_common {basis : Type*} [Fintype basis]
    (left right : State basis) :
    totalVariationDistance left right =
      VerifiedMath.FiniteDistribution.totalVariation
        (basisProbability left) (basisProbability right) := rfl

/-- 既知global phaseを目標へ整列した後のL2誤差上限。 -/
def PhaseAlignedL2Approx {basis : Type*} [Fintype basis]
    (actual target : State basis) (error : ℝ) : Prop :=
  ∃ angle : ℝ,
    l2Distance actual ((Complex.exp (Complex.I * angle)) • target) ≤ error

/-- 単位複素global phaseは各計算基底測定確率を変えない。 -/
@[simp] theorem basisProbability_globalPhase
    {basis : Type*} (angle : ℝ) (state : State basis) (index : basis) :
    basisProbability ((Complex.exp (Complex.I * angle)) • state) index =
      basisProbability state index := by
  simp only [basisProbability, Pi.smul_apply, smul_eq_mul,
    Complex.normSq_eq_norm_sq]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

/-- global phase整列は計算基底測定TV距離を変えない。 -/
theorem totalVariationDistance_globalPhase_right
    {basis : Type*} [Fintype basis]
    (angle : ℝ) (left right : State basis) :
    totalVariationDistance left ((Complex.exp (Complex.I * angle)) • right) =
      totalVariationDistance left right := by
  simp [totalVariationDistance]

/-- 全変動距離は非負である。 -/
theorem totalVariationDistance_nonnegative
    {basis : Type*} [Fintype basis] (left right : State basis) :
    0 ≤ totalVariationDistance left right := by
  apply mul_nonneg
  · norm_num
  · exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- 同じ状態同士の全変動距離は0である。 -/
@[simp] theorem totalVariationDistance_self
    {basis : Type*} [Fintype basis] (state : State basis) :
    totalVariationDistance state state = 0 := by
  simp [totalVariationDistance]

/-- 正規化状態の計算基底測定TV距離を、次元定数付きL2距離で抑える安全な境界。 -/
theorem totalVariationDistance_le_sqrt_card_mul_l2Distance
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {left right : State basis}
    (leftNormalized : IsNormalizedState left)
    (rightNormalized : IsNormalizedState right) :
    totalVariationDistance left right ≤
      Real.sqrt (Fintype.card basis) * l2Distance left right := by
  let difference : basis → ℝ := fun index => ‖left index - right index‖
  have probabilitySum :
      (∑ index, |basisProbability left index - basisProbability right index|) ≤
        2 * ∑ index, difference index := by
    calc
      (∑ index, |basisProbability left index - basisProbability right index|) ≤
          ∑ index, 2 * difference index := by
            exact Finset.sum_le_sum fun index _ =>
              basisProbability_sub_le_two_mul_norm
                leftNormalized rightNormalized index
      _ = 2 * ∑ index, difference index := by rw [Finset.mul_sum]
  have cauchy := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    difference (fun _ : basis => (1 : ℝ))
  have l1Bound :
      (∑ index, difference index) ≤
        Real.sqrt (Fintype.card basis) * l2Distance left right := by
    have rewritten :
        (∑ index, difference index) ≤
          l2Distance left right * Real.sqrt (Fintype.card basis) := by
      simpa [difference, l2Distance, ← Complex.sq_norm] using cauchy
    simpa [mul_comm] using rewritten
  calc
    totalVariationDistance left right =
        (1 / 2 : ℝ) *
          ∑ index, |basisProbability left index - basisProbability right index| := rfl
    _ ≤ (1 / 2 : ℝ) * (2 * ∑ index, difference index) := by
      exact mul_le_mul_of_nonneg_left probabilitySum (by norm_num)
    _ = ∑ index, difference index := by ring
    _ ≤ Real.sqrt (Fintype.card basis) * l2Distance left right := l1Bound

/-- 正規化純粋状態では、計算基底測定TV距離は次元に依存せずL2距離以下である。 -/
theorem totalVariationDistance_le_l2Distance
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {left right : State basis}
    (leftNormalized : IsNormalizedState left)
    (rightNormalized : IsNormalizedState right) :
    totalVariationDistance left right ≤ l2Distance left right := by
  let amplitudeDifference : basis → ℝ :=
    fun index => |‖left index‖ - ‖right index‖|
  let amplitudeSum : basis → ℝ :=
    fun index => ‖left index‖ + ‖right index‖
  have leftSquares : (∑ index, ‖left index‖ ^ 2) = 1 := by
    simpa [IsNormalizedState, basisProbability, Complex.sq_norm] using leftNormalized
  have rightSquares : (∑ index, ‖right index‖ ^ 2) = 1 := by
    simpa [IsNormalizedState, basisProbability, Complex.sq_norm] using rightNormalized
  have crossBound :
      (∑ index, ‖left index‖ * ‖right index‖) ≤ 1 := by
    have cauchy := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun index => ‖left index‖) (fun index => ‖right index‖)
    simpa [leftSquares, rightSquares] using cauchy
  have amplitudeSumSquares :
      (∑ index, amplitudeSum index ^ 2) ≤ 4 := by
    simp only [amplitudeSum, add_sq, Finset.sum_add_distrib,
      leftSquares, rightSquares]
    have crossTwice :
        (∑ index, 2 * ‖left index‖ * ‖right index‖) ≤ 2 := by
      calc
        (∑ index, 2 * ‖left index‖ * ‖right index‖) =
            2 * ∑ index, ‖left index‖ * ‖right index‖ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro index _
              ring
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left crossBound (by norm_num)
        _ = 2 := by norm_num
    linarith
  have amplitudeSumSqrt :
      Real.sqrt (∑ index, amplitudeSum index ^ 2) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by norm_num, ?_⟩
    norm_num
    exact amplitudeSumSquares
  have amplitudeDifferenceSquares :
      (∑ index, amplitudeDifference index ^ 2) ≤
        ∑ index, ‖left index - right index‖ ^ 2 := by
    exact Finset.sum_le_sum fun index _ => by
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2
        (abs_norm_sub_norm_le (left index) (right index))
  have amplitudeDifferenceSqrt :
      Real.sqrt (∑ index, amplitudeDifference index ^ 2) ≤
        l2Distance left right := by
    rw [l2Distance]
    apply Real.sqrt_le_sqrt
    simpa [← Complex.sq_norm] using amplitudeDifferenceSquares
  have productSum :
      (∑ index, amplitudeDifference index * amplitudeSum index) ≤
        2 * l2Distance left right := by
    have cauchy := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      amplitudeDifference amplitudeSum
    calc
      (∑ index, amplitudeDifference index * amplitudeSum index) ≤
          Real.sqrt (∑ index, amplitudeDifference index ^ 2) *
            Real.sqrt (∑ index, amplitudeSum index ^ 2) := cauchy
      _ ≤ l2Distance left right * 2 := by
        exact mul_le_mul amplitudeDifferenceSqrt amplitudeSumSqrt
          (Real.sqrt_nonneg _) (l2Distance_nonnegative _ _)
      _ = 2 * l2Distance left right := by ring
  have probabilityAsProduct :
      (∑ index, |basisProbability left index - basisProbability right index|) =
        ∑ index, amplitudeDifference index * amplitudeSum index := by
    apply Finset.sum_congr rfl
    intro index _
    change |Complex.normSq (left index) - Complex.normSq (right index)| =
      |‖left index‖ - ‖right index‖| *
        (‖left index‖ + ‖right index‖)
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    rw [show ‖left index‖ ^ 2 - ‖right index‖ ^ 2 =
      (‖left index‖ - ‖right index‖) *
        (‖left index‖ + ‖right index‖) by ring]
    rw [abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    totalVariationDistance left right =
        (1 / 2 : ℝ) *
          ∑ index, |basisProbability left index - basisProbability right index| := rfl
    _ = (1 / 2 : ℝ) *
        ∑ index, amplitudeDifference index * amplitudeSum index := by
          rw [probabilityAsProduct]
    _ ≤ (1 / 2 : ℝ) * (2 * l2Distance left right) := by
      exact mul_le_mul_of_nonneg_left productSum (by norm_num)
    _ = l2Distance left right := by ring

/-- L2距離で誤差を評価する状態準備component。 -/
structure L2StatePreparationComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) where
  /-- 状態準備回路。 -/
  circuit : Circuit Gate
  /-- 回路から独立な初期状態。 -/
  initialState : State basis
  /-- 回路から独立な目標状態。 -/
  targetState : State basis
  /-- L2誤差上限。 -/
  error : ℝ
  /-- 誤差上限は非負。 -/
  error_nonnegative : 0 ≤ error
  /-- 準備後状態と目標状態のL2距離上限。 -/
  correct : l2Distance
    (applyOperator (circuit.denote gateOperator) initialState) targetState ≤ error

/-- 計算基底測定分布の全変動距離で誤差を評価する状態準備component。 -/
structure TotalVariationStatePreparationComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) where
  /-- 状態準備回路。 -/
  circuit : Circuit Gate
  /-- 回路から独立な初期状態。 -/
  initialState : State basis
  /-- 回路から独立な目標状態。 -/
  targetState : State basis
  /-- 全変動距離の誤差上限。 -/
  error : ℝ
  /-- 誤差上限は非負。 -/
  error_nonnegative : 0 ≤ error
  /-- 準備後分布と目標分布の全変動距離上限。 -/
  correct : totalVariationDistance
    (applyOperator (circuit.denote gateOperator) initialState) targetState ≤ error

/-- 正規化証拠を用いてL2状態準備契約を計算基底測定TV契約へ変換する。 -/
def L2StatePreparationComponent.toTotalVariation
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : L2StatePreparationComponent gateOperator)
    (actualNormalized : IsNormalizedState
      (applyOperator (component.circuit.denote gateOperator) component.initialState))
    (targetNormalized : IsNormalizedState component.targetState) :
    TotalVariationStatePreparationComponent gateOperator where
  circuit := component.circuit
  initialState := component.initialState
  targetState := component.targetState
  error := component.error
  error_nonnegative := component.error_nonnegative
  correct :=
    (totalVariationDistance_le_l2Distance
      actualNormalized targetNormalized).trans component.correct

end

end VerifiedCircuitCore
