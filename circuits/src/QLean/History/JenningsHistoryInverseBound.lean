import QLean.History.JenningsHistoryWellPosed

/-! A finite causal-height bound, independent of the number of configurations.
No enumeration of the generator matrix or numerical matrix inversion is used. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace JenningsHistoryInverseBound

open Matrix JenningsHistory
open scoped BigOperators Matrix.Norms.L2Operator

def causalRank {d c R : Nat} (index : HistoryIndex d c R) : Nat :=
  index.clock.val * R + index.order.val

theorem causalRank_lt {d c R : Nat} (index : HistoryIndex d c R) :
    causalRank index < c * R := by
  have := index.clock.isLt
  have := index.order.isLt
  unfold causalRank
  nlinarith

theorem causal_remainder_entry {d c r m R : Nat}
    (spec : HistorySpec d c r m R) (row col : HistoryIndex d c R)
    (notLater : causalRank row ≤ causalRank col) :
    (1 - historyMatrix spec) row col = 0 := by
  have noClock : row.clock.val ≠ col.clock.val + 1 := by
    intro next
    have := row.order.isLt
    have := col.order.isLt
    unfold causalRank at notLater
    nlinarith
  have noOrder : row.clock = col.clock → col.order.val + 1 ≠ row.order.val := by
    intro same next
    unfold causalRank at notLater
    rw [same] at notLater
    omega
  have diagonal : l0Entry row col = (1 : HistoryMatrix d c R) row col := by
    simp only [l0Entry, Matrix.one_apply]
    congr 1
    apply propext
    constructor
    · rintro ⟨hc, ho, hs⟩
      cases row
      cases col
      simp_all
    · intro equal
      subst col
      exact ⟨rfl, rfl, rfl⟩
  simp only [Matrix.sub_apply, historyMatrix, diagonal, l2Entry, if_neg noClock]
  by_cases same : row.clock = col.clock
  · simp [l1Entry, same, taylorDeltaEntry, idleDeltaEntry, noOrder same]
  · simp [l1Entry, same]

theorem pow_entry_zero_of_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι ℝ) (rank : ι → Nat)
    (strict : ∀ row col, rank row ≤ rank col → matrix row col = 0)
    (n : Nat) : ∀ row col, rank row < rank col + n →
      (matrix ^ n) row col = 0 := by
  induction n with
  | zero =>
      intro row col lower
      have distinct : row ≠ col := by intro equal; subst col; omega
      simp [distinct]
  | succ n ih =>
      intro row col lower
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro middle _
      by_cases zero : rank middle ≤ rank col
      · rw [strict middle col zero, mul_zero]
      · rw [ih row middle (by omega), zero_mul]

theorem causal_remainder_nilpotent {d c r m R : Nat}
    (spec : HistorySpec d c r m R) :
    (1 - historyMatrix spec) ^ (c * R) = 0 := by
  ext row col
  exact pow_entry_zero_of_rank (1 - historyMatrix spec) causalRank
    (causal_remainder_entry spec) (c * R) row col
    (lt_of_lt_of_le (causalRank_lt row) (Nat.le_add_left _ _))

theorem history_inverse_geometric {d c r m R : Nat}
    (spec : HistorySpec d c r m R) :
    (historyMatrix spec)⁻¹ =
      ∑ k ∈ Finset.range (c * R), (1 - historyMatrix spec) ^ k := by
  have product := geom_sum_mul_neg (1 - historyMatrix spec) (c * R)
  simp only [sub_sub_cancel, causal_remainder_nilpotent, sub_zero] at product
  exact Matrix.inv_eq_left_inv product

theorem history_inverse_norm_le {d c r m R : Nat}
    [Nonempty (HistoryIndex d c R)]
    (spec : HistorySpec d c r m R) (bound : ℝ)
    (_bound_nonneg : 0 ≤ bound) (historyNorm : ‖historyMatrix spec‖ ≤ bound) :
    ‖(historyMatrix spec)⁻¹‖ ≤
      ∑ k ∈ Finset.range (c * R), (1 + bound) ^ k := by
  rw [history_inverse_geometric]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  apply (norm_pow_le _ _).trans
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc
    ‖1 - historyMatrix spec‖ ≤ ‖(1 : HistoryMatrix d c R)‖ + ‖historyMatrix spec‖ :=
      norm_sub_le _ _
    _ ≤ 1 + bound := by simpa using add_le_add_left historyNorm 1

theorem scaled_history_inverse_norm_le {d c r m R : Nat}
    [Nonempty (HistoryIndex d c R)]
    (spec : HistorySpec d c r m R) (alpha bound : ℝ)
    (alpha_pos : 0 < alpha) (alpha_le : alpha ≤ bound)
    (historyNorm : ‖historyMatrix spec‖ ≤ bound) :
    ‖(scaledHistory spec alpha)⁻¹‖ ≤ (1 + bound) ^ (c * R) := by
  have inverse : (scaledHistory spec alpha)⁻¹ = alpha • (historyMatrix spec)⁻¹ :=
    Matrix.inv_eq_left_inv
      (JenningsHistoryWellPosed.scaledHistoryLeftInverse_mul spec alpha alpha_pos.ne')
  rw [inverse, norm_smul, Real.norm_of_nonneg alpha_pos.le]
  have bounded := history_inverse_norm_le spec bound
    (alpha_pos.le.trans alpha_le) historyNorm
  have sum_nonneg : 0 ≤ ∑ k ∈ Finset.range (c * R), (1 + bound) ^ k := by
    apply Finset.sum_nonneg
    intro k _
    exact pow_nonneg (by linarith) _
  have geometric := geom_sum_mul_add bound (c * R)
  rw [add_comm bound 1] at geometric
  calc
    alpha * ‖(historyMatrix spec)⁻¹‖ ≤
        alpha * ∑ k ∈ Finset.range (c * R), (1 + bound) ^ k :=
      mul_le_mul_of_nonneg_left bounded alpha_pos.le
    _ ≤ bound * ∑ k ∈ Finset.range (c * R), (1 + bound) ^ k :=
      mul_le_mul_of_nonneg_right alpha_le sum_nonneg
    _ ≤ (1 + bound) ^ (c * R) := by nlinarith

end JenningsHistoryInverseBound
