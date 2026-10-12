import QLean.Circuits.Foundation.Metrics

/-!
# 有限行列のL2作用素誤差model

supremumを選択関数で構成せず、全正規化前状態に対する作用不等式そのものを
operator norm上界として採用する。逐次積では必要なcontraction条件を明示する。
-/

namespace VerifiedCircuitCore

noncomputable section

open scoped Matrix.Norms.L2Operator

/-- 通常の状態関数を有限次元EuclideanSpaceへ同一視する。 -/
def toEuclideanState {basis : Type*} (state : State basis) :
    EuclideanSpace ℂ basis :=
  WithLp.toLp 2 state

/-- 有限行列をL2 EuclideanSpace上の線形写像として作用させる。 -/
def matrixL2Action {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : Operator basis) :
    EuclideanSpace ℂ basis →ₗ[ℂ] EuclideanSpace ℂ basis :=
  Matrix.toLpLin 2 2 operator

/-- 状態のL2 norm。 -/
def stateL2Norm {basis : Type*} [Fintype basis] (state : State basis) : ℝ :=
  Real.sqrt (∑ index, Complex.normSq (state index))

/-- 状態L2 normはEuclideanSpaceでのnormと一致する。 -/
theorem stateL2Norm_eq_euclideanNorm
    {basis : Type*} [Fintype basis] (state : State basis) :
    stateL2Norm state = ‖toEuclideanState state‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [stateL2Norm, toEuclideanState, ← Complex.sq_norm]

/-- A normalized finite state has L2 norm one. -/
theorem stateL2Norm_eq_one_of_normalized
    {basis : Type*} [Fintype basis]
    {state : State basis} (normalized : IsNormalizedState state) :
    stateL2Norm state = 1 := by
  rw [stateL2Norm]
  have probabilitySum :
      (∑ index, Complex.normSq (state index)) = 1 := by
    simpa [IsNormalizedState, basisProbability] using normalized
  rw [probabilitySum]
  norm_num

/-- L2 norm one implies the finite-state normalization predicate. -/
theorem isNormalizedState_of_stateL2Norm_eq_one
    {basis : Type*} [Fintype basis]
    {state : State basis} (normOne : stateL2Norm state = 1) :
    IsNormalizedState state := by
  have sumNonnegative :
      0 ≤ ∑ index, Complex.normSq (state index) :=
    Finset.sum_nonneg fun index _ => Complex.normSq_nonneg (state index)
  have squared := congrArg (fun value : ℝ => value ^ 2) normOne
  rw [stateL2Norm, Real.sq_sqrt sumNonnegative] at squared
  simpa [IsNormalizedState, basisProbability] using squared

/-- Matrix L2 action agrees with the ordinary finite-state action under the
canonical Euclidean-space identification. -/
@[simp] theorem matrixL2Action_toEuclideanState
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : Operator basis) (state : State basis) :
    matrixL2Action operator (toEuclideanState state) =
      toEuclideanState (applyOperator operator state) := by
  ext index
  simp [matrixL2Action, toEuclideanState, applyOperator,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- 二状態のL2距離は差状態のL2 normである。 -/
theorem l2Distance_eq_stateL2Norm_sub
    {basis : Type*} [Fintype basis] (left right : State basis) :
    l2Distance left right = stateL2Norm (left - right) := by
  rfl

/-- 行列差が全Euclidean状態へ誤差`error`以下で作用するという具体的作用素近似関係。 -/
def OperatorL2Approx {basis : Type*} [Fintype basis] [DecidableEq basis]
    (actual target : Operator basis) (error : ℝ) : Prop :=
  ∀ state : EuclideanSpace ℂ basis,
    ‖matrixL2Action (actual - target) state‖ ≤ error * ‖state‖

/-- 行列が全状態のL2 normを増加させないというcontraction条件。 -/
def IsL2Contraction {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : Operator basis) : Prop :=
  ∀ state : EuclideanSpace ℂ basis,
    ‖matrixL2Action operator state‖ ≤ ‖state‖

/-- A bound on the concrete matrix L2 operator norm of the difference gives
the relational `OperatorL2Approx` contract. -/
theorem operatorL2Approx_of_l2_opNorm_sub_le
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {actual target : Operator basis} {error : ℝ}
    (bound : ‖actual - target‖ ≤ error) :
    OperatorL2Approx actual target error := by
  intro state
  have actionBound := (actual - target).l2_opNorm_mulVec state
  rw [show matrixL2Action (actual - target) state =
      (EuclideanSpace.equiv basis ℂ).symm
        (Matrix.mulVec (actual - target) state.ofLp) by rfl]
  exact actionBound.trans
    (mul_le_mul_of_nonneg_right bound (norm_nonneg state))

/-- An L2 operator norm bound by one gives the contraction contract. -/
theorem isL2Contraction_of_l2_opNorm_le
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {operator : Operator basis} (bound : ‖operator‖ ≤ 1) :
    IsL2Contraction operator := by
  intro state
  have actionBound := operator.l2_opNorm_mulVec state
  simpa [matrixL2Action, Matrix.toLpLin_apply] using
    actionBound.trans (by
      simpa using mul_le_mul_of_nonneg_right bound (norm_nonneg state))

/-- Every finite unitary matrix is an L2 isometry and hence a contraction. -/
theorem isL2Contraction_of_mem_unitaryGroup
    {basis : Type*} [Fintype basis] [DecidableEq basis] [Nonempty basis]
    {operator : Operator basis}
    (unitary : operator ∈ Matrix.unitaryGroup basis ℂ) :
    IsL2Contraction operator := by
  have unitaryProduct : Matrix.conjTranspose operator * operator = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp unitary
  have normSquare : ‖operator‖ * ‖operator‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, unitaryProduct]
    simp
  have normLeOne : ‖operator‖ ≤ 1 := by
    nlinarith [norm_nonneg operator]
  exact isL2Contraction_of_l2_opNorm_le normLeOne

/-- 行列L2作用は加法を保存する。 -/
@[simp] theorem matrixL2Action_add
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (left right : Operator basis) :
    matrixL2Action (left + right) = matrixL2Action left + matrixL2Action right := by
  exact (Matrix.toLpLin 2 2).map_add left right

/-- 行列L2作用は零作用素を保存する。 -/
@[simp] theorem matrixL2Action_zero
    {basis : Type*} [Fintype basis] [DecidableEq basis] :
    matrixL2Action (0 : Operator basis) = 0 := by
  exact (Matrix.toLpLin 2 2).map_zero

/-- 行列積のL2作用は線形写像合成である。 -/
theorem matrixL2Action_mul
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (second first : Operator basis) :
    matrixL2Action (second * first) =
      matrixL2Action second ∘ₗ matrixL2Action first := by
  exact Matrix.toLpLin_mul_same 2 second first

/-- Every finite unitary matrix preserves the Euclidean L2 norm exactly. -/
theorem matrixL2Action_norm_eq_of_mem_unitaryGroup
    {basis : Type*} [Fintype basis] [DecidableEq basis] [Nonempty basis]
    {operator : Operator basis}
    (unitary : operator ∈ Matrix.unitaryGroup basis ℂ)
    (state : EuclideanSpace ℂ basis) :
    ‖matrixL2Action operator state‖ = ‖state‖ := by
  apply le_antisymm
  · exact isL2Contraction_of_mem_unitaryGroup unitary state
  · have unitaryProduct : Matrix.conjTranspose operator * operator = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp unitary
    have adjointUnitary :
        Matrix.conjTranspose operator ∈ Matrix.unitaryGroup basis ℂ := by
      rw [Matrix.mem_unitaryGroup_iff']
      simpa [Matrix.star_eq_conjTranspose] using
        (Matrix.mem_unitaryGroup_iff).mp unitary
    have adjointContraction :=
      isL2Contraction_of_mem_unitaryGroup adjointUnitary
    calc
      ‖state‖ = ‖matrixL2Action (1 : Operator basis) state‖ := by
        simp [matrixL2Action, Matrix.toLpLin_one]
      _ = ‖matrixL2Action
          (Matrix.conjTranspose operator * operator) state‖ := by
        rw [unitaryProduct]
      _ = ‖matrixL2Action (Matrix.conjTranspose operator)
          (matrixL2Action operator state)‖ := by
        rw [matrixL2Action_mul, LinearMap.comp_apply]
      _ ≤ ‖matrixL2Action operator state‖ :=
        adjointContraction _

/-- Unitary matrix action preserves the state L2 norm. -/
theorem stateL2Norm_applyOperator_eq_of_mem_unitaryGroup
    {basis : Type*} [Fintype basis] [DecidableEq basis] [Nonempty basis]
    {operator : Operator basis}
    (unitary : operator ∈ Matrix.unitaryGroup basis ℂ)
    (state : State basis) :
    stateL2Norm (applyOperator operator state) = stateL2Norm state := by
  rw [stateL2Norm_eq_euclideanNorm, stateL2Norm_eq_euclideanNorm,
    ← matrixL2Action_toEuclideanState]
  exact matrixL2Action_norm_eq_of_mem_unitaryGroup unitary _

/-- Unitary matrix action preserves finite-state normalization. -/
theorem IsNormalizedState.applyOperator_of_mem_unitaryGroup
    {basis : Type*} [Fintype basis] [DecidableEq basis] [Nonempty basis]
    {operator : Operator basis} {state : State basis}
    (normalized : IsNormalizedState state)
    (unitary : operator ∈ Matrix.unitaryGroup basis ℂ) :
    IsNormalizedState (applyOperator operator state) :=
  isNormalizedState_of_stateL2Norm_eq_one
    ((stateL2Norm_applyOperator_eq_of_mem_unitaryGroup unitary state).trans
      (stateL2Norm_eq_one_of_normalized normalized))

/-- `OperatorL2Approx`の反射律。 -/
theorem operatorL2Approx_refl
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : Operator basis) : OperatorL2Approx operator operator 0 := by
  intro state
  simp

/-- `OperatorL2Approx`は誤差上限を増やしても保たれる。 -/
theorem operatorL2Approx_weaken
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {actual target : Operator basis} {smaller larger : ℝ}
    (approximation : OperatorL2Approx actual target smaller)
    (bound : smaller ≤ larger) : OperatorL2Approx actual target larger := by
  intro state
  exact (approximation state).trans
    (mul_le_mul_of_nonneg_right bound (norm_nonneg _))

/-- `OperatorL2Approx`の三角不等式。 -/
theorem operatorL2Approx_triangle
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {first second third : Operator basis} {firstError secondError : ℝ}
    (firstApprox : OperatorL2Approx first second firstError)
    (secondApprox : OperatorL2Approx second third secondError) :
    OperatorL2Approx first third (firstError + secondError) := by
  intro state
  have decomposition : first - third = (first - second) + (second - third) := by
    abel
  rw [decomposition, matrixL2Action_add, LinearMap.add_apply]
  calc
    ‖matrixL2Action (first - second) state +
        matrixL2Action (second - third) state‖ ≤
        ‖matrixL2Action (first - second) state‖ +
          ‖matrixL2Action (second - third) state‖ := norm_add_le _ _
    _ ≤ firstError * ‖state‖ + secondError * ‖state‖ :=
      add_le_add (firstApprox state) (secondApprox state)
    _ = (firstError + secondError) * ‖state‖ := by ring

/-- 恒等行列はL2 contractionである。 -/
theorem identity_isL2Contraction
    {basis : Type*} [Fintype basis] [DecidableEq basis] :
    IsL2Contraction (1 : Operator basis) := by
  intro state
  simp [matrixL2Action, Matrix.toLpLin_one]

/-- L2 contraction同士の行列積もL2 contractionである。 -/
theorem mul_isL2Contraction
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {second first : Operator basis}
    (secondContraction : IsL2Contraction second)
    (firstContraction : IsL2Contraction first) :
    IsL2Contraction (second * first) := by
  intro state
  rw [matrixL2Action_mul, LinearMap.comp_apply]
  exact (secondContraction _).trans (firstContraction state)

/-- An execution-order product of contractions is a contraction. -/
theorem operatorSequence_isL2Contraction
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {operators : List (Operator basis)}
    (each : ∀ operator ∈ operators, IsL2Contraction operator) :
    IsL2Contraction (operatorSequence operators) := by
  induction operators with
  | nil => simpa [operatorSequence] using
      (identity_isL2Contraction (basis := basis))
  | cons first rest inductionHypothesis =>
      simp only [operatorSequence]
      exact mul_isL2Contraction
        (inductionHypothesis fun operator member => each operator (by simp [member]))
        (each first (by simp))

/-- Additive error assigned to two pairwise-related operator lists.  The
fallback cases are irrelevant under a `List.Forall₂` length certificate. -/
def pairedOperatorSequenceError {leftItem rightItem : Type*}
    (pairError : leftItem → rightItem → ℝ) :
    List leftItem → List rightItem → ℝ
  | first :: rest, second :: remaining =>
      pairError first second +
        pairedOperatorSequenceError pairError rest remaining
  | _, _ => 0

/-- Pairwise nonnegative local errors have a nonnegative accumulated error. -/
theorem pairedOperatorSequenceError_nonnegative
    {leftItem rightItem : Type*}
    {relation : leftItem → rightItem → Prop}
    {pairError : leftItem → rightItem → ℝ}
    {left : List leftItem} {right : List rightItem}
    (related : List.Forall₂ relation left right)
    (eachNonnegative : ∀ {first second}, relation first second →
      0 ≤ pairError first second) :
    0 ≤ pairedOperatorSequenceError pairError left right := by
  induction related with
  | nil => simp [pairedOperatorSequenceError]
  | cons pairRelated _ inductionHypothesis =>
      simp only [pairedOperatorSequenceError]
      exact add_nonneg (eachNonnegative pairRelated) inductionHypothesis

/-- contraction条件下で二作用素近似の逐次誤差は加算できる。 -/
theorem operatorL2Approx_mul
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {actualFirst targetFirst actualSecond targetSecond : Operator basis}
    {firstError secondError : ℝ}
    (firstApprox : OperatorL2Approx actualFirst targetFirst firstError)
    (secondApprox : OperatorL2Approx actualSecond targetSecond secondError)
    (_firstErrorNonnegative : 0 ≤ firstError)
    (secondErrorNonnegative : 0 ≤ secondError)
    (actualFirstContraction : IsL2Contraction actualFirst)
    (targetSecondContraction : IsL2Contraction targetSecond) :
    OperatorL2Approx (actualSecond * actualFirst) (targetSecond * targetFirst)
      (firstError + secondError) := by
  intro state
  have decomposition :
      actualSecond * actualFirst - targetSecond * targetFirst =
        (actualSecond - targetSecond) * actualFirst +
          targetSecond * (actualFirst - targetFirst) := by
    noncomm_ring
  rw [decomposition, matrixL2Action_add, LinearMap.add_apply,
    matrixL2Action_mul, matrixL2Action_mul, LinearMap.comp_apply,
    LinearMap.comp_apply]
  calc
    ‖matrixL2Action (actualSecond - targetSecond)
          (matrixL2Action actualFirst state) +
        matrixL2Action targetSecond
          (matrixL2Action (actualFirst - targetFirst) state)‖ ≤
        ‖matrixL2Action (actualSecond - targetSecond)
          (matrixL2Action actualFirst state)‖ +
        ‖matrixL2Action targetSecond
          (matrixL2Action (actualFirst - targetFirst) state)‖ := norm_add_le _ _
    _ ≤ secondError * ‖matrixL2Action actualFirst state‖ +
        ‖matrixL2Action (actualFirst - targetFirst) state‖ :=
      add_le_add (secondApprox _) (targetSecondContraction _)
    _ ≤ secondError * ‖state‖ + firstError * ‖state‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (actualFirstContraction state)
          secondErrorNonnegative)
        (firstApprox state)
    _ = (firstError + secondError) * ‖state‖ := by ring

/-- Pairwise L2 approximations compose in execution order, with the explicit
sum of local errors.  The contraction premises are the exact hypotheses used
by the multiplication rule. -/
theorem operatorSequence_l2Approx_of_forall₂
    {basis leftItem rightItem : Type*}
    [Fintype basis] [DecidableEq basis]
    {relation : leftItem → rightItem → Prop}
    (leftOperator : leftItem → Operator basis)
    (rightOperator : rightItem → Operator basis)
    (pairError : leftItem → rightItem → ℝ)
    {left : List leftItem} {right : List rightItem}
    (related : List.Forall₂ relation left right)
    (pairApprox : ∀ {first second}, relation first second →
      OperatorL2Approx (leftOperator first) (rightOperator second)
        (pairError first second))
    (pairErrorNonnegative : ∀ {first second}, relation first second →
      0 ≤ pairError first second)
    (leftContraction : ∀ first, IsL2Contraction (leftOperator first))
    (rightContraction : ∀ second, IsL2Contraction (rightOperator second)) :
    OperatorL2Approx
      (operatorSequence (left.map leftOperator))
      (operatorSequence (right.map rightOperator))
      (pairedOperatorSequenceError pairError left right) := by
  induction related with
  | nil =>
      simpa [operatorSequence, pairedOperatorSequenceError] using
        (operatorL2Approx_refl (1 : Operator basis))
  | @cons first second rest remaining pairRelated restRelated
      inductionHypothesis =>
      simp only [List.map_cons, operatorSequence,
        pairedOperatorSequenceError]
      exact operatorL2Approx_mul
        (pairApprox pairRelated)
        inductionHypothesis
        (pairErrorNonnegative pairRelated)
        (pairedOperatorSequenceError_nonnegative restRelated
          pairErrorNonnegative)
        (leftContraction first)
        (operatorSequence_isL2Contraction fun operator member => by
          rcases List.mem_map.mp member with ⟨item, _, rfl⟩
          exact rightContraction item)

/-- 全状態不等式から得る具体的なcontraction-aware作用素誤差model。 -/
def l2OperatorErrorModel
    (basis : Type*) [Fintype basis] [DecidableEq basis] :
    OperatorErrorModel basis where
  approx := OperatorL2Approx
  refl := operatorL2Approx_refl
  weaken := operatorL2Approx_weaken
  triangle := operatorL2Approx_triangle
  isContraction := IsL2Contraction
  identity_contraction := identity_isL2Contraction
  multiplication_contraction := mul_isL2Contraction
  multiplication := operatorL2Approx_mul

/-- 作用素L2誤差証明を任意入力状態のL2誤差へ適用する。 -/
theorem OperatorL2Approx.apply_state
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {actual target : Operator basis} {error : ℝ}
    (approximation : OperatorL2Approx actual target error) (state : State basis) :
    l2Distance (applyOperator actual state) (applyOperator target state) ≤
      error * stateL2Norm state := by
  have actionEquality :
      matrixL2Action (actual - target) (toEuclideanState state) =
        toEuclideanState (applyOperator actual state - applyOperator target state) := by
    ext index
    simp [matrixL2Action, toEuclideanState, applyOperator,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  have bound := approximation (toEuclideanState state)
  rw [actionEquality] at bound
  simpa [l2Distance_eq_stateL2Norm_sub, stateL2Norm_eq_euclideanNorm] using bound

/-- On a normalized input, an L2 operator approximation between unitaries
directly bounds the total-variation distance of computational-basis outputs. -/
theorem OperatorL2Approx.totalVariationDistance_apply_state_le
    {basis : Type*} [Fintype basis] [DecidableEq basis] [Nonempty basis]
    {actual target : Operator basis} {error : ℝ}
    (approximation : OperatorL2Approx actual target error)
    (actualUnitary : actual ∈ Matrix.unitaryGroup basis ℂ)
    (targetUnitary : target ∈ Matrix.unitaryGroup basis ℂ)
    {state : State basis} (normalized : IsNormalizedState state) :
    totalVariationDistance
        (applyOperator actual state) (applyOperator target state) ≤ error := by
  have actualNormalized :=
    normalized.applyOperator_of_mem_unitaryGroup actualUnitary
  have targetNormalized :=
    normalized.applyOperator_of_mem_unitaryGroup targetUnitary
  calc
    totalVariationDistance
        (applyOperator actual state) (applyOperator target state) ≤
      l2Distance (applyOperator actual state) (applyOperator target state) :=
        totalVariationDistance_le_l2Distance
          actualNormalized targetNormalized
    _ ≤ error * stateL2Norm state := approximation.apply_state state
    _ = error := by rw [stateL2Norm_eq_one_of_normalized normalized, mul_one]

/-- concrete L2 modelの近似作用素componentから入力状態誤差を直接取り出す。 -/
theorem ApproxOperatorComponent.apply_state_l2Bound
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ApproxOperatorComponent gateOperator (l2OperatorErrorModel basis))
    (state : State basis) :
    l2Distance
        (applyOperator (component.circuit.denote gateOperator) state)
        (applyOperator component.target state) ≤
      component.error * stateL2Norm state :=
  OperatorL2Approx.apply_state component.correct state

end

end VerifiedCircuitCore
