import QLean.History.Jennings.PureSpec
import QLean.History.Jennings.ProofEstablishedBridge

open scoped BigOperators
noncomputable section

namespace GramOperator

open JenningsHistory

/-! M13 consumes the accepted M12 Dalzell system without importing any
    circuit, compiler, recorded-gate, or canonical declaration. -/

abbrev ExtendedIndex (d c R : Nat) := JenningsHistory.ExtendedIndex d c R
abbrev ExtendedMatrix (d c R : Nat) :=
  Matrix (ExtendedIndex d c R) (ExtendedIndex d c R) ℝ
abbrev ExtendedVector (d c R : Nat) := ExtendedIndex d c R → ℝ

def enlargedMatrix {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ) : ExtendedMatrix d c R :=
  dalzellExtendedH system alpha ν

def bPlus {d c r m R : Nat}
    (system : HistorySpec d c r m R) : ExtendedVector d c R :=
  dalzellBPlus system

def gNuOperator {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ) : ExtendedMatrix d c R :=
  qBPlusMatrix (bPlus system) * enlargedMatrix system alpha ν

def matrixApply {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℝ) (vector : ι → ℝ) : ι → ℝ :=
  matrix.mulVec vector

theorem wellPosed_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι ℝ) (hwell : wellPosed matrix) :
    IsUnit matrix.det := by
  have hbij : Function.Bijective (Matrix.toLin' matrix) := by
    have hfun : ⇑(Matrix.toLin' matrix) = linearApply matrix := by
      funext v
      simp [linearApply]
    rw [hfun]
    exact hwell
  let e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
    LinearEquiv.ofBijective (Matrix.toLin' matrix) hbij
  let inverseMatrix : Matrix ι ι ℝ :=
    LinearMap.toMatrix' e.symm.toLinearMap
  have hright : matrix * inverseMatrix = 1 := by
    apply (Matrix.toLin' (R := ℝ)).injective
    calc
      Matrix.toLin' (matrix * inverseMatrix) =
          Matrix.toLin' matrix ∘ₗ Matrix.toLin' inverseMatrix :=
        Matrix.toLin'_mul matrix inverseMatrix
      _ = Matrix.toLin' matrix ∘ₗ e.symm.toLinearMap := by
        rw [Matrix.toLin'_toMatrix']
      _ = LinearMap.id := by
        apply LinearMap.ext
        intro v
        exact e.apply_symm_apply v
      _ = Matrix.toLin' (1 : Matrix ι ι ℝ) := by
        symm
        exact Matrix.toLin'_one
  exact isUnit_iff_ne_zero.mpr (Matrix.det_ne_zero_of_right_inverse hright)

/-! This is the exact inverse-based vector required by M13.  The accepted
    M12 invertibility witness is explicit as `hdet`; no existential witness is
    substituted for this vector. -/
def m13KernelVector {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (_hdet : IsUnit (enlargedMatrix system alpha ν).det) :
    ExtendedVector d c R :=
  (enlargedMatrix system alpha ν)⁻¹.mulVec (bPlus system)

lemma inverse_apply_spec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι ℝ) (rhs : ι → ℝ)
    (hdet : IsUnit matrix.det) :
    matrixApply matrix (matrix⁻¹.mulVec rhs) = rhs := by
  change matrix.mulVec (matrix⁻¹.mulVec rhs) = rhs
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv matrix hdet]
  exact Matrix.one_mulVec rhs

lemma unitNorm_ne_zero {ι : Type*} [Fintype ι]
    (vector : ι → ℝ) (hunit : unitNorm vector) : vector ≠ 0 := by
  intro hzero
  subst vector
  simp [unitNorm, unitNormSquared] at hunit

lemma inverse_apply_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrix : Matrix ι ι ℝ) (rhs : ι → ℝ)
    (hdet : IsUnit matrix.det) (hrhs : unitNorm rhs) :
    matrix⁻¹.mulVec rhs ≠ 0 := by
  intro hzero
  apply unitNorm_ne_zero rhs hrhs
  have hspec := inverse_apply_spec matrix rhs hdet
  rw [hzero] at hspec
  simpa [matrixApply] using hspec.symm

lemma unitNormSquared_pos {ι : Type*} [Fintype ι]
    (vector : ι → ℝ) (hvector : vector ≠ 0) :
    0 < unitNormSquared vector := by
  classical
  unfold unitNormSquared
  have hex : ∃ i, vector i ≠ 0 := by
    by_contra h
    apply hvector
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  rcases hex with ⟨i, hi⟩
  apply Finset.sum_pos' (s := Finset.univ)
  · intro j hj
    exact mul_self_nonneg (vector j)
  · exact ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

def normalizedVector {ι : Type*} [Fintype ι]
    (vector : ι → ℝ) : ι → ℝ :=
  (Real.sqrt (unitNormSquared vector))⁻¹ • vector

lemma normalizedVector_unitNorm {ι : Type*} [Fintype ι]
    (vector : ι → ℝ) (hvector : vector ≠ 0) :
    unitNorm (normalizedVector vector) := by
  classical
  have hpos : 0 < unitNormSquared vector := unitNormSquared_pos vector hvector
  have hsqrt : 0 < Real.sqrt (unitNormSquared vector) := Real.sqrt_pos.mpr hpos
  have hsqrt_ne : Real.sqrt (unitNormSquared vector) ≠ 0 := ne_of_gt hsqrt
  have hsqrt_sq : (Real.sqrt (unitNormSquared vector)) ^ 2 =
      unitNormSquared vector := Real.sq_sqrt (le_of_lt hpos)
  unfold unitNorm normalizedVector
  simp only [unitNormSquared, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ x, ((Real.sqrt (∑ i, vector i * vector i))⁻¹ * vector x) *
        ((Real.sqrt (∑ i, vector i * vector i))⁻¹ * vector x)) =
        ∑ x, (Real.sqrt (∑ i, vector i * vector i))⁻¹ ^ 2 *
          (vector x * vector x) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (Real.sqrt (∑ i, vector i * vector i))⁻¹ ^ 2 *
          (∑ x, vector x * vector x) := by
      rw [Finset.mul_sum]
    _ = 1 := by
      rw [inv_pow]
      change (Real.sqrt (unitNormSquared vector) ^ 2)⁻¹ *
        unitNormSquared vector = 1
      rw [hsqrt_sq]
      field_simp

def gHat {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (hdet : IsUnit (enlargedMatrix system alpha ν).det) :
    ExtendedVector d c R :=
  normalizedVector (m13KernelVector system alpha ν hdet)

theorem gHat_unitNorm {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (hdet : IsUnit (enlargedMatrix system alpha ν).det)
    (hb : unitNorm (bPlus system)) :
    unitNorm (gHat system alpha ν hdet) := by
  exact normalizedVector_unitNorm
    (m13KernelVector system alpha ν hdet)
    (inverse_apply_ne_zero (enlargedMatrix system alpha ν)
      (bPlus system) hdet hb)

def idealKernelReflection {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (hdet : IsUnit (enlargedMatrix system alpha ν).det) :
    ExtendedMatrix d c R :=
  kernelReflection (gHat system alpha ν hdet)

def KernelOrthogonal {ι : Type*} [Fintype ι]
    (kernel y : ι → ℝ) : Prop :=
  (∑ i, kernel i * y i) = 0

theorem m13KernelVector_apply {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (hdet : IsUnit (enlargedMatrix system alpha ν).det) :
    matrixApply (enlargedMatrix system alpha ν)
        (m13KernelVector system alpha ν hdet) = bPlus system := by
  exact inverse_apply_spec (enlargedMatrix system alpha ν) (bPlus system) hdet

theorem m13KernelVector_nonzero {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (hdet : IsUnit (enlargedMatrix system alpha ν).det)
    (hb : unitNorm (bPlus system)) :
    m13KernelVector system alpha ν hdet ≠ 0 := by
  exact inverse_apply_ne_zero (enlargedMatrix system alpha ν)
    (bPlus system) hdet hb

theorem m13KernelVector_eq_uniqueSolution {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (hwell : wellPosed (enlargedMatrix system alpha ν))
    (hdet : IsUnit (enlargedMatrix system alpha ν).det) :
    m13KernelVector system alpha ν hdet =
      uniqueSolution (enlargedMatrix system alpha ν) hwell (bPlus system) := by
  apply hwell.1
  calc
    matrixApply (enlargedMatrix system alpha ν)
        (m13KernelVector system alpha ν hdet) = bPlus system :=
      m13KernelVector_apply system alpha ν hdet
    _ = matrixApply (enlargedMatrix system alpha ν)
        (uniqueSolution (enlargedMatrix system alpha ν) hwell (bPlus system)) := by
      symm
      exact uniqueSolution_spec (enlargedMatrix system alpha ν) hwell (bPlus system)

theorem gNu_kernel_iff {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (hwell : wellPosed (enlargedMatrix system alpha ν))
    (hdet : IsUnit (enlargedMatrix system alpha ν).det)
    (hb : unitNorm (bPlus system)) (y : ExtendedVector d c R) :
    matrixApply (gNuOperator system alpha ν) y = 0 ↔
      KernelMember (m13KernelVector system alpha ν hdet) y := by
  rw [m13KernelVector_eq_uniqueSolution system alpha ν hwell hdet]
  exact g_kernel_member_iff (enlargedMatrix system alpha ν) (bPlus system)
    hwell hb y

theorem recovered_solution_eq_m13KernelVector {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ)
    (x : HistoryVector d c R)
    (hwell : wellPosed (enlargedMatrix system alpha ν))
    (hdet : IsUnit (enlargedMatrix system alpha ν).det)
    (hraw : linearApply (historyMatrix system) x = historyRhs system)
    (hrhs : rhsNorm system ≠ 0) (hα : alpha ≠ 0) (hν : ν ≠ 0) :
    rawToEnlargedSolution system alpha ν x =
      m13KernelVector system alpha ν hdet := by
  calc
    rawToEnlargedSolution system alpha ν x =
        uniqueSolution (enlargedMatrix system alpha ν) hwell (bPlus system) := by
      exact recovered_solution_is_uniqueSolution system alpha ν x hwell hraw hrhs hα hν
    _ = m13KernelVector system alpha ν hdet :=
      (m13KernelVector_eq_uniqueSolution system alpha ν hwell hdet).symm

end GramOperator
