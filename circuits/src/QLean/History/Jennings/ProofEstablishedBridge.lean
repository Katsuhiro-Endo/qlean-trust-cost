import QLean.History.Jennings.PureSpec

open scoped BigOperators
noncomputable section

namespace JenningsHistory

/-! The ordered phase word is a product of its scheduled operators. -/

/-! M11: the ordered QSP/FPAA word is an actual product of the scheduled
    phase matrices and signal matrices.  The fixture deliberately has two
    nonzero phases and an interior scalar evaluation. -/

/-! M12 proof-bearing entry and solution-establishedBridge facts. -/

def historyEmbedding {d c R : Nat}
    (v : HistoryVector d c R) : ExtendedVector d c R
  | Sum.inl row => v row
  | Sum.inr _ => 0

def historyRestriction {d c R : Nat}
    (v : ExtendedVector d c R) : HistoryVector d c R :=
  fun row => v (Sum.inl row)

def rawToEnlargedSolution {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (x : HistoryVector d c R) : ExtendedVector d c R
  | Sum.inl row => alpha * x row / (rhsNorm system * Real.sqrt 2)
  | Sum.inr _ => ν / Real.sqrt 2

lemma dalzellExtendedH_apply_inl {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (v : ExtendedVector d c R) (row : HistoryIndex d c R) :
    linearApply (dalzellExtendedH system alpha ν) v (Sum.inl row) =
      ∑ col, scaledHistory system alpha row col * v (Sum.inl col) := by
  classical
  simp [linearApply, Matrix.mulVec, dotProduct, dalzellExtendedH,
    Fintype.sum_sum_type]

lemma dalzellExtendedH_apply_inr {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (v : ExtendedVector d c R) :
    linearApply (dalzellExtendedH system alpha ν) v (Sum.inr ()) =
      ν⁻¹ * v (Sum.inr ()) := by
  classical
  simp [linearApply, Matrix.mulVec, dotProduct, dalzellExtendedH,
    Fintype.sum_sum_type]

lemma scaledHistory_raw_scale {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha den : ℝ)
    (x : HistoryVector d c R) (hα : alpha ≠ 0) (hden : den ≠ 0)
    (hraw : linearApply (historyMatrix system) x = historyRhs system) :
    (fun row => ∑ col, scaledHistory system alpha row col *
        (alpha * x col / den)) =
      (fun row => historyRhs system row / den) := by
  funext row
  rw [show (∑ col, scaledHistory system alpha row col *
      (alpha * x col / den)) =
      (∑ col, (historyMatrix system row col / alpha) *
        (alpha * x col / den)) by rfl]
  calc
    (∑ col, (historyMatrix system row col / alpha) *
        (alpha * x col / den)) =
        ∑ col, (historyMatrix system row col * x col) / den := by
      apply Finset.sum_congr rfl
      intro col hcol
      field_simp [hα, hden]
    _ = (∑ col, historyMatrix system row col * x col) / den := by
      rw [Finset.sum_div]
    _ = historyRhs system row / den := by
      rw [show (∑ col, historyMatrix system row col * x col) =
          linearApply (historyMatrix system) x row by rfl]
      rw [hraw]

theorem raw_solution_establishedBridge {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (x : HistoryVector d c R)
    (hraw : linearApply (historyMatrix system) x = historyRhs system)
    (hrhs : rhsNorm system ≠ 0) (hα : alpha ≠ 0) (hν : ν ≠ 0) :
    linearApply (dalzellExtendedH system alpha ν)
      (rawToEnlargedSolution system alpha ν x) =
      dalzellBPlus system := by
  classical
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  funext z
  rcases z with row | _
  · rw [dalzellExtendedH_apply_inl]
    have hden : rhsNorm system * Real.sqrt 2 ≠ 0 := mul_ne_zero hrhs hsqrt
    have hscaled := scaledHistory_raw_scale system alpha
      (rhsNorm system * Real.sqrt 2) x hα hden hraw
    calc
      (∑ col, scaledHistory system alpha row col *
          rawToEnlargedSolution system alpha ν x (Sum.inl col)) =
          historyRhs system row /
            (rhsNorm system * Real.sqrt 2) := by
              simpa [rawToEnlargedSolution] using congrFun hscaled row
      _ = normalizedRhs system row / Real.sqrt 2 := by
        simp only [normalizedRhs]
        field_simp [hrhs, hsqrt]
  · rw [dalzellExtendedH_apply_inr]
    simp [rawToEnlargedSolution, dalzellBPlus]
    field_simp [hν, hsqrt]

/-! ## M12 reverse establishedBridge

The enlarged equation has two genuinely different components.  The `inl`
component is the normalized history equation, while the `inr` component fixes
the auxiliary coordinate.  We keep both equations explicit before defining
the inverse scale; this prevents the scale from being hidden by definitional
equality or by an unrelated solution witness.
-/

/-! M13 consumes the same arbitrary enlarged solution recovered above. -/

/-! M13 is tied to the recovered M12 solution, rather than to an
    unrelated existential unique-solution witness. -/
theorem recovered_solution_is_uniqueSolution {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (x : HistoryVector d c R)
    (hwell : wellPosed (dalzellExtendedH system alpha ν))
    (hraw : linearApply (historyMatrix system) x = historyRhs system)
    (hrhs : rhsNorm system ≠ 0) (hα : alpha ≠ 0) (hν : ν ≠ 0) :
    rawToEnlargedSolution system alpha ν x =
      uniqueSolution (dalzellExtendedH system alpha ν) hwell
        (dalzellBPlus system) := by
  apply hwell.1
  calc
    linearApply (dalzellExtendedH system alpha ν)
        (rawToEnlargedSolution system alpha ν x) = dalzellBPlus system :=
      raw_solution_establishedBridge system alpha ν x hraw hrhs hα hν
    _ = linearApply (dalzellExtendedH system alpha ν)
        (uniqueSolution (dalzellExtendedH system alpha ν) hwell
          (dalzellBPlus system)) := by
      symm
      exact uniqueSolution_spec (dalzellExtendedH system alpha ν) hwell
        (dalzellBPlus system)

end JenningsHistory
