import QLean.History.Jennings.PureSpec

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace JenningsHistoryWellPosed

open Matrix
open JenningsHistory

/-- Lexicographic order used only to expose the causal, lower-triangular
shape of the Jennings history matrix. -/
def historyIndexEquivProduct (d c R : Nat) :
    HistoryIndex d c R ≃ Lex (Fin c × Lex (Fin R × Fin d)) where
  toFun index := toLex (index.clock, toLex (index.order, index.state))
  invFun index :=
    { clock := (ofLex index).1
      order := (ofLex (ofLex index).2).1
      state := (ofLex (ofLex index).2).2 }
  left_inv index := by cases index; rfl
  right_inv index := by cases index; rfl

local instance historyIndexLinearOrder (d c R : Nat) :
    LinearOrder (HistoryIndex d c R) :=
  Equiv.linearOrder (historyIndexEquivProduct d c R)

theorem lex_pair_lt_iff {alpha beta : Type*}
    [LinearOrder alpha] [LinearOrder beta]
    (a c : alpha) (b d : beta) :
    toLex (a, b) < toLex (c, d) ↔ a < c ∨ (a = c ∧ b < d) := by
  constructor
  · intro h
    cases h with
    | left _ _ hac => exact Or.inl hac
    | right _ hbd => exact Or.inr ⟨rfl, hbd⟩
  · rintro (hac | ⟨rfl, hbd⟩)
    · exact Prod.Lex.left _ _ hac
    · exact Prod.Lex.right _ hbd

/-- The Jennings history matrix is lower triangular in causal
`(clock, order, state)` order. -/
theorem historyMatrix_lowerTriangular {d c r m R : Nat}
    (spec : HistorySpec d c r m R) :
    (historyMatrix spec).BlockTriangular OrderDual.toDual := by
  intro row col h
  change row < col at h
  change toLex (row.clock, toLex (row.order, row.state)) <
    toLex (col.clock, toLex (col.order, col.state)) at h
  rcases (lex_pair_lt_iff _ _ _ _).1 h with
    hclock | ⟨hclock, hrest⟩
  · have clockNe : row.clock ≠ col.clock := ne_of_lt hclock
    have notSuccessor : row.clock.val ≠ col.clock.val + 1 := by omega
    simp [historyMatrix, l0Entry, l1Entry, l2Entry,
      clockNe, notSuccessor]
  · rcases (lex_pair_lt_iff _ _ _ _).1 hrest with
      horder | ⟨horder, hstate⟩
    · have orderNe : row.order ≠ col.order := ne_of_lt horder
      have notPrevious : col.order.val + 1 ≠ row.order.val := by omega
      simp [historyMatrix, l0Entry, l1Entry, l2Entry,
        taylorDeltaEntry, idleDeltaEntry,
        hclock, orderNe, notPrevious]
    · have stateNe : row.state ≠ col.state := ne_of_lt hstate
      simp [historyMatrix, l0Entry, l1Entry, l2Entry,
        taylorDeltaEntry, idleDeltaEntry,
        hclock, horder, stateNe]

/-- Every diagonal entry is exactly one, independently of the generator. -/
theorem historyMatrix_diagonal {d c r m R : Nat}
    (spec : HistorySpec d c r m R) (index : HistoryIndex d c R) :
    historyMatrix spec index index = 1 := by
  simp [historyMatrix, l0Entry, l1Entry, l2Entry,
    taylorDeltaEntry, idleDeltaEntry]

/-- The determinant of every finite Jennings history matrix is one. -/
theorem historyMatrix_det {d c r m R : Nat}
    (spec : HistorySpec d c r m R) :
    Matrix.det (historyMatrix spec) = 1 := by
  rw [Matrix.det_of_lowerTriangular (historyMatrix spec)
    (historyMatrix_lowerTriangular spec)]
  simp [historyMatrix_diagonal]

theorem historyMatrix_det_isUnit {d c r m R : Nat}
    (spec : HistorySpec d c r m R) :
    IsUnit (Matrix.det (historyMatrix spec)) := by
  rw [historyMatrix_det spec]
  exact isUnit_one

theorem wellPosed_of_det_isUnit {index : Type*}
    [Fintype index] [DecidableEq index]
    (matrix : Matrix index index ℝ) (hdet : IsUnit matrix.det) :
    wellPosed matrix := by
  constructor
  · intro left right equal
    have transported := congrArg (fun vector => matrix⁻¹.mulVec vector) equal
    simpa [linearApply, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul matrix hdet] using transported
  · intro target
    refine ⟨matrix⁻¹.mulVec target, ?_⟩
    simp [linearApply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv matrix hdet]

noncomputable section

/-- Explicit left inverse of the normalized history block. -/
def scaledHistoryLeftInverse {d c r m R : Nat}
    (spec : HistorySpec d c r m R) (alpha : ℝ) :
    HistoryMatrix d c R :=
  alpha • (historyMatrix spec)⁻¹

theorem scaledHistoryLeftInverse_mul {d c r m R : Nat}
    (spec : HistorySpec d c r m R) (alpha : ℝ) (hAlpha : alpha ≠ 0) :
    scaledHistoryLeftInverse spec alpha * scaledHistory spec alpha = 1 := by
  ext row col
  simp only [scaledHistoryLeftInverse, scaledHistory, Matrix.mul_apply,
    Matrix.smul_apply]
  calc
    (∑ index, (alpha * (historyMatrix spec)⁻¹ row index) *
        (historyMatrix spec index col / alpha)) =
        ∑ index, (historyMatrix spec)⁻¹ row index *
          historyMatrix spec index col := by
      apply Finset.sum_congr rfl
      intro index member
      field_simp
    _ = ((historyMatrix spec)⁻¹ * historyMatrix spec) row col := by
      rfl
    _ = (1 : HistoryMatrix d c R) row col := by
      rw [Matrix.nonsing_inv_mul (historyMatrix spec)
        (historyMatrix_det_isUnit spec)]

/-- Explicit left inverse of the Dalzell one-dimensional extension. -/
def dalzellExtendedLeftInverse {d c r m R : Nat}
    (spec : HistorySpec d c r m R) (alpha nu : ℝ) :
    ExtendedMatrix d c R
  | Sum.inl row, Sum.inl col => scaledHistoryLeftInverse spec alpha row col
  | Sum.inr _, Sum.inr _ => nu
  | _, _ => 0

theorem dalzellExtendedLeftInverse_mul {d c r m R : Nat}
    (spec : HistorySpec d c r m R) (alpha nu : ℝ)
    (hAlpha : alpha ≠ 0) (hNu : nu ≠ 0) :
    dalzellExtendedLeftInverse spec alpha nu *
      dalzellExtendedH spec alpha nu = 1 := by
  ext row col
  cases row with
  | inl row =>
      cases col with
      | inl col =>
          simpa [Matrix.mul_apply, Matrix.one_apply,
            dalzellExtendedLeftInverse, dalzellExtendedH,
            Fintype.sum_sum_type] using
            congrFun (congrFun
              (scaledHistoryLeftInverse_mul spec alpha hAlpha) row) col
      | inr col =>
          simp [Matrix.mul_apply, dalzellExtendedLeftInverse,
            dalzellExtendedH, Fintype.sum_sum_type]
  | inr row =>
      cases col with
      | inl col =>
          simp [Matrix.mul_apply, dalzellExtendedLeftInverse,
            dalzellExtendedH, Fintype.sum_sum_type]
      | inr col =>
          cases row
          cases col
          simp [Matrix.mul_apply, dalzellExtendedLeftInverse,
            dalzellExtendedH, Fintype.sum_sum_type, hNu]

/-- Nonzero normalization scalars make the complete extended history matrix
invertible. -/
theorem dalzellExtendedH_det_isUnit {d c r m R : Nat}
    (spec : HistorySpec d c r m R) (alpha nu : ℝ)
    (hAlpha : alpha ≠ 0) (hNu : nu ≠ 0) :
    IsUnit (dalzellExtendedH spec alpha nu).det := by
  rw [isUnit_iff_ne_zero]
  exact Matrix.det_ne_zero_of_left_inverse
    (dalzellExtendedLeftInverse_mul spec alpha nu hAlpha hNu)

theorem dalzellExtendedH_wellPosed {d c r m R : Nat}
    (spec : HistorySpec d c r m R) (alpha nu : ℝ)
    (hAlpha : alpha ≠ 0) (hNu : nu ≠ 0) :
    wellPosed (dalzellExtendedH spec alpha nu) :=
  wellPosed_of_det_isUnit _
    (dalzellExtendedH_det_isUnit spec alpha nu hAlpha hNu)

end

end JenningsHistoryWellPosed
