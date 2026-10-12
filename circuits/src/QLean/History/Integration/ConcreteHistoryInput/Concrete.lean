import QLean.History.Integration.ConcreteHistoryInput.M13cFixed

open scoped BigOperators
noncomputable section

namespace ConcreteHistoryInput

open JenningsHistory
open GramOperator
open ConcreteHistoryInput

abbrev ExtE (d c R : Nat) := EuclideanSpace ℝ (ConcreteHistoryInput.ExtendedIndex d c R)

def toE {ι : Type*} (v : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 v

def extToE {d c R : Nat}
    (v : ConcreteHistoryInput.ExtendedVector d c R) : ExtE d c R :=
  toE v

noncomputable def matrixEMap {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := by
  classical
  exact
    { toFun := fun v => toE (M.mulVec v.ofLp)
      map_add' := by
        intro v w
        rw [show (v + w).ofLp = v.ofLp + w.ofLp by rfl]
        rw [Matrix.mulVec_add]
        rfl
      map_smul' := by
        intro a v
        change toE (M.mulVec (a • v).ofLp) = a • toE (M.mulVec v.ofLp)
        rw [show (a • v).ofLp = a • v.ofLp by rfl]
        rw [Matrix.mulVec_smul]
        rfl }

noncomputable def m13IdealReflectionEMap {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (hdet : IsUnit (enlargedMatrix system alpha ν).det) :
    ExtE d c R →ₗ[ℝ] ExtE d c R :=
  matrixEMap (idealKernelReflection system alpha ν hdet)

noncomputable def m13HistoryProjectorEMap {d c R : Nat} :
    ExtE d c R →ₗ[ℝ] ExtE d c R :=
  matrixEMap (m13HistoryProjector (d := d) (c := c) (R := R))

def m13ExtensionBasisE {d c R : Nat} : ExtE d c R :=
  extToE (m13ExtensionBasis (d := d) (c := c) (R := R))

def m13ConcreteIdealHistoryTarget {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (x : HistoryVector d c R) : ExtE d c R :=
  extToE
    ((2 * ν /
        (unitNormSquared (m13XAlpha system alpha x) + ν ^ 2)) •
      historyEmbedding (m13XAlpha system alpha x))

theorem m13ExtensionBasisE_norm {d c R : Nat} :
    ‖m13ExtensionBasisE (d := d) (c := c) (R := R)‖ ≤ 1 := by
  have hsq : ‖m13ExtensionBasisE (d := d) (c := c) (R := R)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change ∑ i, ‖m13ExtensionBasis (d := d) (c := c) (R := R) i‖ ^ 2 = 1
    simp [m13ExtensionBasis, Fintype.sum_sum_type,
      Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg (m13ExtensionBasisE (d := d) (c := c) (R := R))]

theorem m13ConcreteIdealHistoryTarget_eq_actual {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (x : HistoryVector d c R)
    (hwell : wellPosed (enlargedMatrix system alpha ν))
    (hdet : IsUnit (enlargedMatrix system alpha ν).det)
    (hraw : linearApply (historyMatrix system) x = historyRhs system)
    (hrhs : rhsNorm system ≠ 0) (hα : alpha ≠ 0) (hν : ν ≠ 0)
    (hb : unitNorm (bPlus system)) :
    m13HistoryProjectorEMap (d := d) (c := c) (R := R)
        (m13IdealReflectionEMap system alpha ν hdet
          (m13ExtensionBasisE (d := d) (c := c) (R := R))) =
      m13ConcreteIdealHistoryTarget system alpha ν x := by
  classical
  apply congrArg (fun v : ConcreteHistoryInput.ExtendedVector d c R => extToE v)
  simp only [m13IdealReflectionEMap, matrixEMap,
    LinearMap.coe_mk, AddHom.coe_mk, m13ExtensionBasisE, extToE]
  change
    (m13HistoryProjector (d := d) (c := c) (R := R)).mulVec
        ((idealKernelReflection system alpha ν hdet).mulVec
          (m13ExtensionBasis (d := d) (c := c) (R := R))) =
      (2 * ν /
        (unitNormSquared (m13XAlpha system alpha x) + ν ^ 2)) •
        historyEmbedding (m13XAlpha system alpha x)
  change
    (m13HistoryProjector (d := d) (c := c) (R := R)).mulVec
        (m13ReflectionOutput system alpha ν hdet) =
      (2 * ν /
        (unitNormSquared (m13XAlpha system alpha x) + ν ^ 2)) •
        historyEmbedding (m13XAlpha system alpha x)
  rw [m13ReflectionOutput_formula system alpha ν x hwell hdet hraw hrhs hα hν hb]
  rw [m13HistoryProjector_mulVec]
  funext z
  cases z with
  | inl row =>
      simp [JenningsHistory.historyEmbedding, JenningsHistory.historyRestriction,
        ConcreteHistoryInput.m13ExtensionBasis, Pi.smul_apply, smul_eq_mul]
  | inr u =>
      simp [JenningsHistory.historyEmbedding, Pi.smul_apply, smul_eq_mul]

end ConcreteHistoryInput
