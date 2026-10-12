import QLean.History.Jennings.M13

open scoped BigOperators
noncomputable section

namespace ConcreteHistoryInput

open JenningsHistory
open GramOperator

abbrev ExtendedIndex (d c R : Nat) := JenningsHistory.ExtendedIndex d c R
abbrev ExtendedMatrix (d c R : Nat) := JenningsHistory.ExtendedMatrix d c R
abbrev ExtendedVector (d c R : Nat) := JenningsHistory.ExtendedVector d c R

def m13XAlpha {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha : ℝ)
    (x : HistoryVector d c R) : HistoryVector d c R :=
  (alpha / rhsNorm system) • x

def m13ExtensionBasis {d c R : Nat} : ExtendedVector d c R
  | Sum.inl _ => 0
  | Sum.inr _ => 1

def m13HistoryProjector {d c R : Nat} : ExtendedMatrix d c R
  | Sum.inl row, Sum.inl col => if row = col then 1 else 0
  | _, _ => 0

def m13ReflectionOutput {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (hdet : IsUnit (enlargedMatrix system alpha ν).det) :
    ExtendedVector d c R :=
  (idealKernelReflection system alpha ν hdet).mulVec m13ExtensionBasis

theorem m13HistoryProjector_mulVec {d c R : Nat}
    (v : ExtendedVector d c R) :
    (m13HistoryProjector (d := d) (c := c) (R := R)).mulVec v =
      historyEmbedding (historyRestriction v) := by
  classical
  funext i
  cases i with
  | inl row =>
      simp [m13HistoryProjector, historyEmbedding, historyRestriction,
        Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  | inr u =>
      simp [m13HistoryProjector, historyEmbedding, Matrix.mulVec, dotProduct]

lemma unitNormSquared_smul {ι : Type*} [Fintype ι]
    (c : ℝ) (v : ι → ℝ) :
    unitNormSquared (c • v) = c ^ 2 * unitNormSquared v := by
  classical
  simp only [unitNormSquared, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, (c * v i) * (c * v i)) =
        ∑ i, c ^ 2 * (v i * v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c ^ 2 * ∑ i, v i * v i := by
      rw [Finset.mul_sum]

lemma m13ExtensionBasis_dot {d c R : Nat}
    (v : ExtendedVector d c R) :
    (∑ i, v i * m13ExtensionBasis (d := d) (c := c) (R := R) i) =
      v (Sum.inr ()) := by
  classical
  simp [m13ExtensionBasis, Fintype.sum_sum_type]

lemma m13_split_norm_squared {d c R : Nat}
    (v : HistoryVector d c R) (ν : ℝ) :
    unitNormSquared
        (historyEmbedding v + ν • m13ExtensionBasis (d := d) (c := c) (R := R)) =
      unitNormSquared v + ν ^ 2 := by
  classical
  simp [unitNormSquared, historyEmbedding, m13ExtensionBasis,
    Fintype.sum_sum_type, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma kernelProjector_smul {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (c : ℝ) (hc : c ≠ 0) :
    kernelProjector (c • v) = kernelProjector v := by
  classical
  ext i j
  simp only [kernelProjector, Pi.smul_apply, smul_eq_mul]
  have hden :
      (∑ k, (c * v k) * (c * v k)) =
        c ^ 2 * (∑ k, v k * v k) := by
    calc
      (∑ k, (c * v k) * (c * v k)) =
          ∑ k, c ^ 2 * (v k * v k) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = c ^ 2 * (∑ k, v k * v k) := by
        rw [Finset.mul_sum]
  rw [hden]
  field_simp [hc]

lemma normalizedVector_kernelProjector {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (hv : v ≠ 0) :
    kernelProjector (normalizedVector v) = kernelProjector v := by
  have hpos : 0 < unitNormSquared v := unitNormSquared_pos v hv
  have hsqrt : 0 < Real.sqrt (unitNormSquared v) := Real.sqrt_pos.mpr hpos
  exact kernelProjector_smul v (Real.sqrt (unitNormSquared v))⁻¹
    (inv_ne_zero (ne_of_gt hsqrt))

lemma kernelReflection_mulVec_raw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v w : ι → ℝ) (hv : v ≠ 0) :
    (kernelReflection v).mulVec w =
      (2 * (∑ j, v j * w j) / unitNormSquared v) • v - w := by
  classical
  have hpos : 0 < unitNormSquared v := unitNormSquared_pos v hv
  have hden : unitNormSquared v ≠ 0 := ne_of_gt hpos
  rw [kernelReflection, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, kernelProjector_apply_formula]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp [unitNormSquared]
  field_simp [hden]

lemma idealKernelReflection_eq_raw {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (hdet : IsUnit (enlargedMatrix system alpha ν).det)
    (hb : unitNorm (bPlus system)) :
    idealKernelReflection system alpha ν hdet =
      kernelReflection (m13KernelVector system alpha ν hdet) := by
  have hg : m13KernelVector system alpha ν hdet ≠ 0 :=
    m13KernelVector_nonzero system alpha ν hdet hb
  unfold idealKernelReflection gHat kernelReflection
  rw [normalizedVector_kernelProjector _ hg]

theorem m13Kernel_decomposition {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (x : HistoryVector d c R)
    (hwell : wellPosed (enlargedMatrix system alpha ν))
    (hdet : IsUnit (enlargedMatrix system alpha ν).det)
    (hraw : linearApply (historyMatrix system) x = historyRhs system)
    (hrhs : rhsNorm system ≠ 0) (hα : alpha ≠ 0) (hν : ν ≠ 0) :
    m13KernelVector system alpha ν hdet =
      (Real.sqrt 2)⁻¹ •
        (historyEmbedding (m13XAlpha system alpha x) +
          ν • m13ExtensionBasis (d := d) (c := c) (R := R)) := by
  rw [← recovered_solution_eq_m13KernelVector system alpha ν x
    hwell hdet hraw hrhs hα hν]
  ext z
  cases z with
  | inl row =>
      simp [rawToEnlargedSolution, m13XAlpha, historyEmbedding,
        m13ExtensionBasis]
      have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      field_simp [hrhs, hsqrt]
  | inr u =>
      simp [rawToEnlargedSolution, m13XAlpha, historyEmbedding,
        m13ExtensionBasis]
      have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      field_simp [hν, hsqrt]

lemma m13_inv_sqrt_two_sq : (Real.sqrt (2 : ℝ))⁻¹ ^ 2 = (2 : ℝ)⁻¹ := by
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
    norm_num
  rw [inv_pow, hsqrt_sq]

theorem m13KernelVector_normSquared {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (x : HistoryVector d c R)
    (hwell : wellPosed (enlargedMatrix system alpha ν))
    (hdet : IsUnit (enlargedMatrix system alpha ν).det)
    (hraw : linearApply (historyMatrix system) x = historyRhs system)
    (hrhs : rhsNorm system ≠ 0) (hα : alpha ≠ 0) (hν : ν ≠ 0) :
    unitNormSquared (m13KernelVector system alpha ν hdet) =
      (unitNormSquared (m13XAlpha system alpha x) + ν ^ 2) / 2 := by
  rw [m13Kernel_decomposition system alpha ν x hwell hdet hraw hrhs hα hν]
  rw [unitNormSquared_smul]
  rw [m13_split_norm_squared]
  rw [m13_inv_sqrt_two_sq]
  ring

lemma m13KernelVector_dot_extensionBasis {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (x : HistoryVector d c R)
    (hwell : wellPosed (enlargedMatrix system alpha ν))
    (hdet : IsUnit (enlargedMatrix system alpha ν).det)
    (hraw : linearApply (historyMatrix system) x = historyRhs system)
    (hrhs : rhsNorm system ≠ 0) (hα : alpha ≠ 0) (hν : ν ≠ 0) :
    (∑ i, m13KernelVector system alpha ν hdet i *
      m13ExtensionBasis (d := d) (c := c) (R := R) i) =
        ν / Real.sqrt 2 := by
  rw [m13Kernel_decomposition system alpha ν x hwell hdet hraw hrhs hα hν]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  calc
    (∑ i, (Real.sqrt 2)⁻¹ *
        (historyEmbedding (m13XAlpha system alpha x) i +
          ν * m13ExtensionBasis (d := d) (c := c) (R := R) i) *
        m13ExtensionBasis (d := d) (c := c) (R := R) i) =
        (Real.sqrt 2)⁻¹ *
          (∑ i, (historyEmbedding (m13XAlpha system alpha x) i +
            ν * m13ExtensionBasis (d := d) (c := c) (R := R) i) *
            m13ExtensionBasis (d := d) (c := c) (R := R) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (Real.sqrt 2)⁻¹ * ν := by
      rw [m13ExtensionBasis_dot]
      simp [historyEmbedding, m13ExtensionBasis]
    _ = ν / Real.sqrt 2 := by
      ring

theorem m13ReflectionOutput_formula {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (x : HistoryVector d c R)
    (hwell : wellPosed (enlargedMatrix system alpha ν))
    (hdet : IsUnit (enlargedMatrix system alpha ν).det)
    (hraw : linearApply (historyMatrix system) x = historyRhs system)
    (hrhs : rhsNorm system ≠ 0) (hα : alpha ≠ 0) (hν : ν ≠ 0)
    (hb : unitNorm (bPlus system)) :
    m13ReflectionOutput system alpha ν hdet =
      (2 * ν /
          (unitNormSquared (m13XAlpha system alpha x) + ν ^ 2)) •
          historyEmbedding (m13XAlpha system alpha x) +
        ((ν ^ 2 - unitNormSquared (m13XAlpha system alpha x)) /
          (unitNormSquared (m13XAlpha system alpha x) + ν ^ 2)) •
          m13ExtensionBasis (d := d) (c := c) (R := R) := by
  have hg : m13KernelVector system alpha ν hdet ≠ 0 :=
    m13KernelVector_nonzero system alpha ν hdet hb
  have hxnonneg : 0 ≤ unitNormSquared (m13XAlpha system alpha x) := by
    unfold unitNormSquared
    exact Finset.sum_nonneg (fun i hi => mul_self_nonneg _)
  have hνsq : 0 < ν ^ 2 := sq_pos_of_ne_zero hν
  have hsum : unitNormSquared (m13XAlpha system alpha x) + ν ^ 2 ≠ 0 := by
    nlinarith
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  unfold m13ReflectionOutput
  rw [idealKernelReflection_eq_raw system alpha ν hdet hb]
  rw [kernelReflection_mulVec_raw _ _ hg]
  rw [m13KernelVector_dot_extensionBasis system alpha ν x hwell hdet
    hraw hrhs hα hν]
  rw [m13KernelVector_normSquared system alpha ν x hwell hdet hraw hrhs hα hν]
  rw [m13Kernel_decomposition system alpha ν x hwell hdet hraw hrhs hα hν]
  ext z
  cases z with
  | inl row =>
      simp [historyEmbedding, m13ExtensionBasis, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      field_simp [hsum, hsqrt]
      all_goals rw [hsqrt_sq]
  | inr u =>
      simp [historyEmbedding, m13ExtensionBasis, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      field_simp [hsum, hsqrt]
      all_goals rw [hsqrt_sq]
      all_goals ring

end ConcreteHistoryInput
