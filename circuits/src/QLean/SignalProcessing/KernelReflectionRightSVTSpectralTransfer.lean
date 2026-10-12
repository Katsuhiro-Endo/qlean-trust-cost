import QLean.SignalProcessing.KernelReflectionQSVTKernelReflection
import Mathlib.Analysis.Matrix.Spectrum
import QLean.SignalProcessing.KernelQSPGeneralQSPIntegration

open scoped BigOperators
noncomputable section

namespace DalzellDilation

open JenningsHistory
open GramOperator
open ConcreteHistoryInput
open TypedNegativeCases

def gramMatrix130 {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) : Matrix ι ι ℝ := G.transpose * G

lemma gram_isHermitian130 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) : (gramMatrix130 G).IsHermitian := by
  ext i j
  simp [gramMatrix130, Matrix.conjTranspose, Matrix.mul_apply]

theorem gramHermitian130 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) : (gramMatrix130 G).IsHermitian :=
  gram_isHermitian130 G

noncomputable def gramBasis130 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) :=
  (gramHermitian130 G).eigenvectorBasis

def gramEigenvalue130 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (j : ι) : ℝ :=
  (gramHermitian130 G).eigenvalues j

lemma gram_basis_dot_self130 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (j : ι) :
    dotProduct ((gramBasis130 G j).ofLp) ((gramBasis130 G j).ofLp) = 1 := by
  have hn : ‖gramBasis130 G j‖ = 1 :=
    (gramHermitian130 G).eigenvectorBasis.orthonormal.norm_eq_one j
  have hn2 := congrArg (fun x : ℝ => x ^ 2) hn
  rw [EuclideanSpace.norm_sq_eq] at hn2
  simpa [gramBasis130, Real.norm_eq_abs, sq_abs, dotProduct, pow_two] using hn2

lemma gram_quadratic130 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (j : ι) :
    dotProduct ((gramBasis130 G j).ofLp)
        ((gramMatrix130 G).mulVec ((gramBasis130 G j).ofLp)) =
      unitNormSquared (G.mulVec ((gramBasis130 G j).ofLp)) := by
  rw [show gramMatrix130 G = G.transpose * G by rfl]
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_transpose]
  rfl

lemma gram_eigenvalue_nonneg130 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (j : ι) :
    0 ≤ gramEigenvalue130 G j := by
  let hG := gramHermitian130 G
  let e : ι → ℝ := (gramBasis130 G j).ofLp
  have heval : (gramMatrix130 G).mulVec e =
      gramEigenvalue130 G j • e := by
    exact hG.mulVec_eigenvectorBasis j
  have hdot : dotProduct e e = 1 := by
    exact gram_basis_dot_self130 G j
  have hq := gram_quadratic130 G j
  have hEq : gramEigenvalue130 G j =
      unitNormSquared (G.mulVec e) := by
    calc
      gramEigenvalue130 G j = gramEigenvalue130 G j * 1 := by ring
      _ = gramEigenvalue130 G j * dotProduct e e := by rw [hdot]
      _ = dotProduct e (gramEigenvalue130 G j • e) := by
        simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = dotProduct e ((gramMatrix130 G).mulVec e) := by rw [heval]
      _ = unitNormSquared (G.mulVec e) := hq
  rw [hEq]
  unfold unitNormSquared
  exact Finset.sum_nonneg (fun i hi => mul_self_nonneg _)

lemma euclidean_norm_sq_raw130 {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι) :
    ‖v‖ ^ 2 = unitNormSquared v.ofLp := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [unitNormSquared, Real.norm_eq_abs, pow_two]

def diagonalApply130 {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (v : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => a i * v.ofLp i)

lemma diagonal_norm_bound130 {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (ha : ∀ i, |a i| ≤ η) (v : EuclideanSpace ℝ ι) :
    ‖diagonalApply130 a v‖ ≤ η * ‖v‖ := by
  have hsq : ‖diagonalApply130 a v‖ ^ 2 ≤ η ^ 2 * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rw [EuclideanSpace.norm_sq_eq]
    simp only [diagonalApply130, Real.norm_eq_abs, pow_two]
    have hsum :
        (∑ i, |a i * v.ofLp i| * |a i * v.ofLp i|) ≤
          ∑ i, η * η * (|v.ofLp i| * |v.ofLp i|) := by
      apply Finset.sum_le_sum
      intro i hi
      have habs : |a i| * |v.ofLp i| ≤ η * |v.ofLp i| := by
        exact mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)
      have hleft : 0 ≤ |a i| * |v.ofLp i| :=
        mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hright : 0 ≤ η * |v.ofLp i| :=
        mul_nonneg hη (abs_nonneg _)
      have hsq' :
          (|a i| * |v.ofLp i|) ^ 2 ≤
            (η * |v.ofLp i|) ^ 2 := by
        nlinarith
      simpa [abs_mul, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq'
    calc
      ∑ x, |a x * v.ofLp x| * |a x * v.ofLp x| ≤
          ∑ x, η * η * (|v.ofLp x| * |v.ofLp x|) := hsum
      _ = η * η * ∑ x, |v.ofLp x| * |v.ofLp x| := by
        rw [Finset.mul_sum]
  have hleft : 0 ≤ ‖diagonalApply130 a v‖ := norm_nonneg _
  have hright : 0 ≤ η * ‖v‖ := mul_nonneg hη (norm_nonneg _)
  nlinarith [hsq]

noncomputable def gramFilterAction130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (P : ℝ → ℝ)
    (v : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (gramBasis130 G).repr.symm
    (diagonalApply130
      (fun j => P (Real.sqrt (gramEigenvalue130 G j)))
      ((gramBasis130 G).repr v))

noncomputable def gramKernelReflectionAction130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ)
    (v : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (gramBasis130 G).repr.symm
    (diagonalApply130
      (fun j => if gramEigenvalue130 G j = 0 then (1 : ℝ) else -1)
      ((gramBasis130 G).repr v))

lemma gramFilterAction_basis130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (P : ℝ → ℝ) (j : ι) :
    gramFilterAction130 G P (gramBasis130 G j) =
      P (Real.sqrt (gramEigenvalue130 G j)) • gramBasis130 G j := by
  apply (gramBasis130 G).repr.injective
  simp only [gramFilterAction130, LinearIsometryEquiv.apply_symm_apply]
  rw [(gramBasis130 G).repr.map_smul]
  rw [OrthonormalBasis.repr_self (gramBasis130 G) j]
  ext k
  by_cases hkj : k = j
  · subst k
    simp [diagonalApply130]
  · simp [diagonalApply130, hkj]

lemma gramKernelReflectionAction_basis130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (j : ι) :
    gramKernelReflectionAction130 G (gramBasis130 G j) =
      (if gramEigenvalue130 G j = 0 then (1 : ℝ) else -1) •
        gramBasis130 G j := by
  apply (gramBasis130 G).repr.injective
  simp only [gramKernelReflectionAction130, LinearIsometryEquiv.apply_symm_apply]
  rw [(gramBasis130 G).repr.map_smul]
  rw [OrthonormalBasis.repr_self (gramBasis130 G) j]
  ext k
  by_cases hkj : k = j
  · subst k
    by_cases hz : gramEigenvalue130 G j = 0
    · simp [diagonalApply130, hz]
    · simp [diagonalApply130, hz]
  · by_cases hz : gramEigenvalue130 G j = 0
    · simp [diagonalApply130, hkj, hz]
    · simp [diagonalApply130, hkj, hz]

def kernelOrthogonalFn130 {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) (v : ι → ℝ) : Prop :=
  ∀ k, G.mulVec k = 0 → dotProduct v k = 0

def rightSingularGapFn130 {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) (δ : ℝ) : Prop :=
  ∀ v, kernelOrthogonalFn130 G v →
    δ * rawNorm130 v ≤ rawNorm130 (G.mulVec v)

lemma gram_dot_swap130 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (u v : ι → ℝ) :
    dotProduct u ((gramMatrix130 G).mulVec v) =
      dotProduct v ((gramMatrix130 G).mulVec u) := by
  calc
    dotProduct u ((gramMatrix130 G).mulVec v) =
        dotProduct u (G.transpose.mulVec (G.mulVec v)) := by
          rw [show gramMatrix130 G = G.transpose * G by rfl]
          rw [← Matrix.mulVec_mulVec]
    _ = Matrix.vecMul u G.transpose ⬝ᵥ (G.mulVec v) := by
          rw [Matrix.dotProduct_mulVec]
    _ = dotProduct (G.mulVec u) (G.mulVec v) := by
          rw [Matrix.vecMul_transpose]
    _ = dotProduct (G.mulVec v) (G.mulVec u) := dotProduct_comm _ _
    _ = Matrix.vecMul v G.transpose ⬝ᵥ (G.mulVec u) := by
          rw [Matrix.vecMul_transpose]
    _ = dotProduct v (G.transpose.mulVec (G.mulVec u)) := by
          rw [← Matrix.dotProduct_mulVec]
    _ = dotProduct v ((gramMatrix130 G).mulVec u) := by
          rw [show gramMatrix130 G = G.transpose * G by rfl]
          rw [← Matrix.mulVec_mulVec]

lemma gram_basis_kernel_orthogonal130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (j : ι)
    (hj : gramEigenvalue130 G j ≠ 0) :
    kernelOrthogonalFn130 G ((gramBasis130 G j).ofLp) := by
  intro k hk
  let e : ι → ℝ := (gramBasis130 G j).ofLp
  have heval : (gramMatrix130 G).mulVec e =
      gramEigenvalue130 G j • e := by
    exact (gramHermitian130 G).mulVec_eigenvectorBasis j
  have hgramk : (gramMatrix130 G).mulVec k = 0 := by
    rw [show gramMatrix130 G = G.transpose * G by rfl]
    rw [← Matrix.mulVec_mulVec]
    rw [hk]
    simp
  have hswap := gram_dot_swap130 G k e
  rw [heval, hgramk] at hswap
  have hscalar : gramEigenvalue130 G j * dotProduct k e = 0 := by
    calc
      gramEigenvalue130 G j * dotProduct k e =
          dotProduct k (gramEigenvalue130 G j • e) := by
            simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = dotProduct e 0 := hswap
      _ = 0 := by simp
  have hzero : dotProduct k e = 0 := by
    exact (mul_eq_zero.mp hscalar).resolve_left hj
  simpa [dotProduct_comm] using hzero

lemma gram_eigenvalue_eq_unitNormSquared130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (j : ι) :
    gramEigenvalue130 G j =
      unitNormSquared (G.mulVec ((gramBasis130 G j).ofLp)) := by
  let hG := gramHermitian130 G
  let e : ι → ℝ := (gramBasis130 G j).ofLp
  have heval : (gramMatrix130 G).mulVec e =
      gramEigenvalue130 G j • e := by
    exact hG.mulVec_eigenvectorBasis j
  have hdot : dotProduct e e = 1 := by
    exact gram_basis_dot_self130 G j
  have hq := gram_quadratic130 G j
  calc
    gramEigenvalue130 G j = gramEigenvalue130 G j * 1 := by ring
    _ = gramEigenvalue130 G j * dotProduct e e := by rw [hdot]
    _ = dotProduct e (gramEigenvalue130 G j • e) := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = dotProduct e ((gramMatrix130 G).mulVec e) := by rw [heval]
    _ = unitNormSquared (G.mulVec e) := hq

lemma gram_basis_rawNorm_one130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (j : ι) :
    rawNorm130 ((gramBasis130 G j).ofLp) = 1 := by
  have hn : ‖gramBasis130 G j‖ = 1 :=
    (gramHermitian130 G).eigenvectorBasis.orthonormal.norm_eq_one j
  have hs := euclidean_norm_sq_raw130 (gramBasis130 G j)
  rw [hn] at hs
  have hunit : unitNormSquared ((gramBasis130 G j).ofLp) = 1 := by
    nlinarith
  simp [rawNorm130, hunit]

lemma gram_basis_sqrt_eq_rawNorm130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (j : ι) :
    Real.sqrt (gramEigenvalue130 G j) =
      rawNorm130 (G.mulVec ((gramBasis130 G j).ofLp)) := by
  rw [gram_eigenvalue_eq_unitNormSquared130 G j]
  rfl

lemma gram_basis_sqrt_le_one130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (j : ι)
    (hGnorm : RawOperatorNormBound130 G 1) :
    Real.sqrt (gramEigenvalue130 G j) ≤ 1 := by
  have h := hGnorm ((gramBasis130 G j).ofLp)
  have hb := gram_basis_rawNorm_one130 G j
  rw [gram_basis_sqrt_eq_rawNorm130 G j]
  simpa [hb] using h

lemma gram_basis_sqrt_ge_delta130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (j : ι) (δ : ℝ)
    (hgap : rightSingularGapFn130 G δ)
    (hj : gramEigenvalue130 G j ≠ 0) :
    δ ≤ Real.sqrt (gramEigenvalue130 G j) := by
  have h := hgap ((gramBasis130 G j).ofLp)
    (gram_basis_kernel_orthogonal130 G j hj)
  have hb := gram_basis_rawNorm_one130 G j
  rw [gram_basis_sqrt_eq_rawNorm130 G j]
  rw [hb] at h
  nlinarith

lemma gram_filter_coefficient_bound130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (P : ℝ → ℝ)
    (δ η : ℝ) (hη : 0 ≤ η)
    (hP0 : P 0 = 1)
    (hPgap : ∀ σ, δ ≤ σ → σ ≤ 1 → |P σ + 1| ≤ η)
    (hGnorm : RawOperatorNormBound130 G 1)
    (hgap : rightSingularGapFn130 G δ) (j : ι) :
    |P (Real.sqrt (gramEigenvalue130 G j)) -
        (if gramEigenvalue130 G j = 0 then (1 : ℝ) else -1)| ≤ η := by
  by_cases hj : gramEigenvalue130 G j = 0
  · simpa [hj, hP0] using hη
  · have hlo := gram_basis_sqrt_ge_delta130 G j δ hgap hj
    have hhi := gram_basis_sqrt_le_one130 G j hGnorm
    have hbound := hPgap (Real.sqrt (gramEigenvalue130 G j)) hlo hhi
    simpa [hj, sub_neg_eq_add] using hbound

lemma diagonal_sub_apply130 {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (v : EuclideanSpace ℝ ι) :
    diagonalApply130 a v - diagonalApply130 b v =
      diagonalApply130 (fun i => a i - b i) v := by
  ext i
  simp [diagonalApply130]
  ring

/-- A finite-spectrum response bound transports directly to the associated
real Gram functional calculi.  Neither response is defined from a circuit. -/
theorem gram_filter_difference_bound130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (P Q : ℝ → ℝ)
    (η : ℝ) (hη : 0 ≤ η)
    (hcoeff : ∀ j,
      |P (Real.sqrt (gramEigenvalue130 G j)) -
        Q (Real.sqrt (gramEigenvalue130 G j))| ≤ η)
    (v : EuclideanSpace ℝ ι) :
    ‖gramFilterAction130 G P v - gramFilterAction130 G Q v‖ ≤ η * ‖v‖ := by
  let b := gramBasis130 G
  let a : ι → ℝ := fun j => P (Real.sqrt (gramEigenvalue130 G j))
  let r : ι → ℝ := fun j => Q (Real.sqrt (gramEigenvalue130 G j))
  have hrepr : b.repr
        (gramFilterAction130 G P v - gramFilterAction130 G Q v) =
      diagonalApply130 (fun j => a j - r j) (b.repr v) := by
    dsimp [b]
    rw [(gramBasis130 G).repr.map_sub]
    simp only [gramFilterAction130, LinearIsometryEquiv.apply_symm_apply]
    rw [diagonal_sub_apply130]
  calc
    ‖gramFilterAction130 G P v - gramFilterAction130 G Q v‖ =
        ‖b.repr (gramFilterAction130 G P v -
          gramFilterAction130 G Q v)‖ :=
      (b.repr.norm_map _).symm
    _ = ‖diagonalApply130 (fun j => a j - r j) (b.repr v)‖ := by
      rw [hrepr]
    _ ≤ η * ‖b.repr v‖ :=
      diagonal_norm_bound130 (fun j => a j - r j) η hη
        (fun j => hcoeff j) (b.repr v)
    _ = η * ‖v‖ := by rw [b.repr.norm_map]

theorem gram_filter_reflection_bound130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (P : ℝ → ℝ)
    (δ η : ℝ) (hη : 0 ≤ η)
    (hP0 : P 0 = 1)
    (hPgap : ∀ σ, δ ≤ σ → σ ≤ 1 → |P σ + 1| ≤ η)
    (hGnorm : RawOperatorNormBound130 G 1)
    (hgap : rightSingularGapFn130 G δ)
    (v : EuclideanSpace ℝ ι) :
    ‖gramFilterAction130 G P v - gramKernelReflectionAction130 G v‖ ≤
      η * ‖v‖ := by
  let b := gramBasis130 G
  let a : ι → ℝ := fun j => P (Real.sqrt (gramEigenvalue130 G j))
  let r : ι → ℝ := fun j =>
    if gramEigenvalue130 G j = 0 then (1 : ℝ) else -1
  have hcoeff : ∀ j, |a j - r j| ≤ η := by
    intro j
    exact gram_filter_coefficient_bound130 G P δ η hη hP0 hPgap hGnorm hgap j
  have hrepr : b.repr
        (gramFilterAction130 G P v - gramKernelReflectionAction130 G v) =
      diagonalApply130 (fun j => a j - r j) (b.repr v) := by
    dsimp [b]
    rw [(gramBasis130 G).repr.map_sub]
    simp only [gramFilterAction130, gramKernelReflectionAction130,
      LinearIsometryEquiv.apply_symm_apply]
    rw [diagonal_sub_apply130]
  calc
    ‖gramFilterAction130 G P v - gramKernelReflectionAction130 G v‖ =
        ‖b.repr (gramFilterAction130 G P v -
          gramKernelReflectionAction130 G v)‖ :=
      (b.repr.norm_map _).symm
    _ = ‖diagonalApply130 (fun j => a j - r j) (b.repr v)‖ := by
      rw [hrepr]
    _ ≤ η * ‖b.repr v‖ :=
      diagonal_norm_bound130 (fun j => a j - r j) η hη hcoeff (b.repr v)
    _ = η * ‖v‖ := by rw [b.repr.norm_map]

def matrixActionLinear130 {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  { toFun := fun v => WithLp.toLp 2 (M.mulVec v.ofLp)
    map_add' := by
      intro v w
      ext i
      simp [Matrix.mulVec_add]
    map_smul' := by
      intro c v
      ext i
      simp [Matrix.mulVec_smul] }

def diagonalLinear130 {ι : Type*} [Fintype ι]
    (a : ι → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  { toFun := diagonalApply130 a
    map_add' := by
      intro v w
      ext i
      simp [diagonalApply130]
      ring
    map_smul' := by
      intro c v
      ext i
      simp [diagonalApply130]
      ring }

noncomputable def gramFilterLinear130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (P : ℝ → ℝ) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (gramBasis130 G).repr.symm.toLinearMap.comp
    ((diagonalLinear130
      (fun j => P (Real.sqrt (gramEigenvalue130 G j)))).comp
      (gramBasis130 G).repr.toLinearMap)

noncomputable def gramKernelReflectionLinear130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (gramBasis130 G).repr.symm.toLinearMap.comp
    ((diagonalLinear130
      (fun j => if gramEigenvalue130 G j = 0 then (1 : ℝ) else -1)).comp
      (gramBasis130 G).repr.toLinearMap)

lemma gramFilterLinear_apply130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (P : ℝ → ℝ)
    (v : EuclideanSpace ℝ ι) :
    gramFilterLinear130 G P v = gramFilterAction130 G P v := by
  rfl

lemma gramKernelReflectionLinear_apply130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ)
    (v : EuclideanSpace ℝ ι) :
    gramKernelReflectionLinear130 G v = gramKernelReflectionAction130 G v := by
  rfl

lemma kernelReflection_mulVec_member130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (K y : ι → ℝ) (hK : unitNorm K)
    (hy : KernelMember K y) :
    (kernelReflection K).mulVec y = y := by
  have hp := (kernelProjector_member_iff K y hK).2 hy
  change (2 • kernelProjector K - (1 : Matrix ι ι ℝ)).mulVec y = y
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hp, Matrix.one_mulVec]
  funext i
  simp only [Pi.smul_apply, Pi.sub_apply]
  ring

lemma kernelReflection_mulVec_orthogonal130 {ι : Type*} [Fintype ι]
    [DecidableEq ι] (K y : ι → ℝ) (hK : unitNorm K)
    (hy : KernelOrthogonal K y) :
    (kernelReflection K).mulVec y = -y := by
  have hp := (kernelProjector_zero_iff K y hK).2 (by
    simpa [KernelOrthogonal] using hy)
  change (2 • kernelProjector K - (1 : Matrix ι ι ℝ)).mulVec y = -y
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hp, Matrix.one_mulVec]
  funext i
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply]
  ring

lemma euclidean_toLp_zero130 {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (hv : unitNormSquared v = 0) : v = 0 := by
  let w : EuclideanSpace ℝ ι := WithLp.toLp 2 v
  have hw_sq := euclidean_norm_sq_raw130 w
  have hw_norm : ‖w‖ ^ 2 = 0 := by
    simpa [w, unitNormSquared, Real.norm_eq_abs, pow_two] using hw_sq.trans hv
  have hw_norm_zero : ‖w‖ = 0 := by nlinarith
  have hw : w = 0 := norm_eq_zero.mp hw_norm_zero
  have hfun : w.ofLp = (0 : EuclideanSpace ℝ ι).ofLp :=
    congrArg (fun z : EuclideanSpace ℝ ι => z.ofLp) hw
  simpa [w] using hfun

theorem gramKernelReflection_eq_kernelReflection130 {ι : Type*}
    [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (K : ι → ℝ)
    (hK : unitNorm K)
    (hkernel : ∀ y, G.mulVec y = 0 ↔ KernelMember K y)
    (v : EuclideanSpace ℝ ι) :
    gramKernelReflectionAction130 G v =
      WithLp.toLp 2 ((kernelReflection K).mulVec v.ofLp) := by
  have hlin : gramKernelReflectionLinear130 G =
      matrixActionLinear130 (kernelReflection K) := by
    apply Module.Basis.ext (gramBasis130 G).toBasis
    intro j
    let e : ι → ℝ := (gramBasis130 G j).ofLp
    by_cases hj : gramEigenvalue130 G j = 0
    · have hq : unitNormSquared (G.mulVec e) = 0 := by
        rw [← gram_eigenvalue_eq_unitNormSquared130 G j]
        exact hj
      have hGzero : G.mulVec e = 0 := euclidean_toLp_zero130 _ hq
      have hmem : KernelMember K e := (hkernel e).1 hGzero
      have hleft := gramKernelReflectionAction_basis130 G j
      have hright := kernelReflection_mulVec_member130 K e hK hmem
      change gramKernelReflectionLinear130 G (gramBasis130 G j) =
        matrixActionLinear130 (kernelReflection K) (gramBasis130 G j)
      rw [gramKernelReflectionLinear_apply130, hleft]
      simp [hj, hright, matrixActionLinear130, e]
    · have hGK : G.mulVec K = 0 := by
        apply (hkernel K).2
        exact ⟨1, by simp⟩
      have horthFn := gram_basis_kernel_orthogonal130 G j hj
      have horth : KernelOrthogonal K e := by
        simpa [KernelOrthogonal, dotProduct, e, mul_comm] using horthFn K hGK
      have hleft := gramKernelReflectionAction_basis130 G j
      have hright := kernelReflection_mulVec_orthogonal130 K e hK horth
      change gramKernelReflectionLinear130 G (gramBasis130 G j) =
        matrixActionLinear130 (kernelReflection K) (gramBasis130 G j)
      rw [gramKernelReflectionLinear_apply130, hleft]
      simp [hj, hright, matrixActionLinear130, e]
  have hv := congrArg (fun L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι => L v) hlin
  simpa [gramKernelReflectionLinear_apply130, matrixActionLinear130] using hv

lemma kernelMember_normalizedVector_iff130 {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (hx : x ≠ 0) :
    KernelMember x y ↔ KernelMember (normalizedVector x) y := by
  let a : ℝ := (Real.sqrt (unitNormSquared x))⁻¹
  have hpos : 0 < unitNormSquared x := unitNormSquared_pos x hx
  have hsqrt : 0 < Real.sqrt (unitNormSquared x) := Real.sqrt_pos.mpr hpos
  have ha : a ≠ 0 := by
    dsimp [a]
    exact inv_ne_zero (ne_of_gt hsqrt)
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c / a, ?_⟩
    rw [hc]
    simp only [normalizedVector, a, smul_smul]
    field_simp [ha]
  · rintro ⟨c, hc⟩
    refine ⟨c * a, ?_⟩
    rw [hc]
    simp only [normalizedVector, a, smul_smul]

theorem gNu_kernel_reflection_eq_gram130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) (v : EuclideanSpace ℝ
      (GramOperator.ExtendedIndex d c R)) :
    gramKernelReflectionAction130
        (gNuOperator I.base.system I.base.alpha I.base.nu)
        v =
      WithLp.toLp 2 ((idealKernelReflection I.base.system
        I.base.alpha I.base.nu I.base.hdet).mulVec v.ofLp) := by
  let G : Matrix (GramOperator.ExtendedIndex d c R)
      (GramOperator.ExtendedIndex d c R) ℝ :=
    gNuOperator I.base.system I.base.alpha I.base.nu
  let K : GramOperator.ExtendedIndex d c R → ℝ :=
    gHat I.base.system I.base.alpha I.base.nu I.base.hdet
  have hmv : m13KernelVector I.base.system I.base.alpha
      I.base.nu I.base.hdet ≠ 0 :=
    m13KernelVector_nonzero I.base.system I.base.alpha
      I.base.nu I.base.hdet I.base.hb
  have hkernel : ∀ y, G.mulVec y = 0 ↔ KernelMember K y := by
    intro y
    have hg := gNu_kernel_iff I.base.system I.base.alpha I.base.nu
      I.base.hwell I.base.hdet I.base.hb y
    change matrixApply (gNuOperator I.base.system I.base.alpha I.base.nu) y = 0 ↔ _
    rw [hg]
    simpa [K, gHat] using (kernelMember_normalizedVector_iff130
      (m13KernelVector I.base.system I.base.alpha I.base.nu I.base.hdet) y hmv)
  have hgeneric := gramKernelReflection_eq_kernelReflection130 G K
    (gHat_unitNorm I.base.system I.base.alpha I.base.nu
      I.base.hdet I.base.hb) hkernel v
  simpa [G, K, idealKernelReflection] using hgeneric

theorem gNu_gram_filter_reflection_bound130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) (P : ℝ → ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hP0 : P 0 = 1)
    (hPgap : ∀ σ, deltaKR130 I ≤ σ → σ ≤ 1 → |P σ + 1| ≤ η)
    (v : EuclideanSpace ℝ (GramOperator.ExtendedIndex d c R)) :
    ‖gramFilterAction130
        (gNuOperator I.base.system I.base.alpha I.base.nu) P v -
      WithLp.toLp 2 ((idealKernelReflection I.base.system
        I.base.alpha I.base.nu I.base.hdet).mulVec v.ofLp)‖ ≤
      η * ‖v‖ := by
  let G : Matrix (GramOperator.ExtendedIndex d c R)
      (GramOperator.ExtendedIndex d c R) ℝ :=
    gNuOperator I.base.system I.base.alpha I.base.nu
  have hgap : rightSingularGapFn130 G (deltaKR130 I) := by
    intro w hw
    apply rightSingularLowerGap130 I w
    simpa [KernelOrthogonal130, kernelOrthogonalFn130, dotProduct, G,
      mul_comm] using hw
  have hbound := gram_filter_reflection_bound130 G P
    (deltaKR130 I) η hη hP0 hPgap (gNu_norm_le_one I) hgap v
  rw [← gNu_kernel_reflection_eq_gram130 I v]
  exact hbound

/-! ## Circuit-independent scalar filter from the accepted KernelQSP response

The spectral transfer above is intentionally stated for an arbitrary real
function.  The following total scalar is the exact accepted fixed-point
response on the nonzero spectral sector, with its success-probability input
clipped to the transition region.  The kernel value is set separately to the
required value `1`; no executable circuit or complex amplitude is introduced.
-/

lemma fixedPointFailureResponse_zero130
    (params : KernelQSP.KernelGeneralParameters126) :
    SpectralSamplingProof.Analytic.fixedPointChebyshevFailureResponse
        (KernelQSP.fixedPointParametersGeneral126 params) 0 = 1 := by
  rw [SpectralSamplingProof.Analytic.fixedPointChebyshevFailureResponse_eq_scaled_sequence]
  have hsource :
      SpectralSamplingProof.Analytic.fixedPointSourceAmplitude (0 : ℝ) = 1 := by
    simp [SpectralSamplingProof.Analytic.fixedPointSourceAmplitude]
  rw [hsource]
  exact SpectralSamplingProof.Analytic.fixedPointScaledChebyshevSequence_at_one_queryLength _

lemma scaled_sqrt_le_one130
    (fp : SpectralSamplingProof.Analytic.FixedPointChebyshevParameters)
    {q : ℝ}
    (hqtrans : fp.transitionWidth ≤ q)
    (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |fp.scale * Real.sqrt (max 0 (1 - q))| ≤ 1 := by
  let u : ℝ := Real.arcosh (1 / fp.failureAmplitude) /
      (fp.queryLength : ℝ)
  have harg : 1 ≤ 1 / fp.failureAmplitude := by
    apply (le_div_iff₀ fp.failureAmplitude_positive).2
    simpa using le_of_lt fp.failureAmplitude_lt_one
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg (Real.arcosh_nonneg harg) (by positivity)
  have hcpos : 0 < Real.cosh u := Real.cosh_pos u
  have hidentity : 1 - (Real.tanh u) ^ 2 =
      (1 / Real.cosh u) ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq u]
  have hnonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hqmax : max 0 (1 - q) = 1 - q :=
    max_eq_right hnonneg
  have htrans : (Real.tanh u) ^ 2 ≤ q := by
    simpa [u,
      SpectralSamplingProof.Analytic.FixedPointChebyshevParameters.transitionWidth]
      using hqtrans
  have hsq : 1 - q ≤ (1 / Real.cosh u) ^ 2 := by
    rw [← hidentity]
    linarith
  have hsqrt : Real.sqrt (1 - q) ≤ 1 / Real.cosh u := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · exact hsq
  have hmul := mul_le_mul_of_nonneg_left hsqrt (le_of_lt hcpos)
  have hprod : 0 ≤ fp.scale * Real.sqrt (max 0 (1 - q)) := by
    dsimp [SpectralSamplingProof.Analytic.FixedPointChebyshevParameters.scale]
    positivity
  rw [abs_of_nonneg hprod]
  have hcancel : Real.cosh u * (1 / Real.cosh u) = 1 := by
    field_simp
  calc
    fp.scale * Real.sqrt (max 0 (1 - q)) =
        Real.cosh u * Real.sqrt (1 - q) := by
      simp [SpectralSamplingProof.Analytic.FixedPointChebyshevParameters.scale,
        u, hqmax]
    _ ≤ Real.cosh u * (1 / Real.cosh u) := hmul
    _ = 1 := hcancel

lemma fixedPointFailureResponse_abs_le_target130
    (params : KernelQSP.KernelGeneralParameters126) {q : ℝ}
    (hqtrans :
      (KernelQSP.fixedPointParametersGeneral126 params).transitionWidth ≤ q)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |SpectralSamplingProof.Analytic.fixedPointChebyshevFailureResponse
        (KernelQSP.fixedPointParametersGeneral126 params) q| ≤
      params.targetError := by
  let fp := KernelQSP.fixedPointParametersGeneral126 params
  rw [SpectralSamplingProof.Analytic.fixedPointChebyshevFailureResponse_eq_scaled_sequence]
  unfold SpectralSamplingProof.Analytic.fixedPointScaledChebyshevSequence
  have hcoord : |fp.scale *
      SpectralSamplingProof.Analytic.fixedPointSourceAmplitude q| ≤ 1 := by
    have hs := scaled_sqrt_le_one130 fp hqtrans hq0 hq1
    simpa [fp, SpectralSamplingProof.Analytic.fixedPointSourceAmplitude] using hs
  have hc := Polynomial.Chebyshev.abs_eval_T_real_le_one
      (fp.queryLength : ℤ) hcoord
  calc
    |fp.failureAmplitude *
        Polynomial.eval (fp.scale *
          SpectralSamplingProof.Analytic.fixedPointSourceAmplitude q)
          (Polynomial.Chebyshev.T ℝ (fp.queryLength : ℤ))| =
      fp.failureAmplitude *
        |Polynomial.eval (fp.scale *
          SpectralSamplingProof.Analytic.fixedPointSourceAmplitude q)
          (Polynomial.Chebyshev.T ℝ (fp.queryLength : ℤ))| := by
            rw [abs_mul, abs_of_pos fp.failureAmplitude_positive]
    _ ≤ fp.failureAmplitude * 1 := by
      exact mul_le_mul_of_nonneg_left hc
        (le_of_lt fp.failureAmplitude_positive)
    _ = params.targetError := by
      simp [fp, KernelQSP.fixedPointParametersGeneral126]

lemma fixedPointTransitionWidth_lt_one130
    (params : KernelQSP.KernelGeneralParameters126) :
    (KernelQSP.fixedPointParametersGeneral126 params).transitionWidth < 1 := by
  exact Real.tanh_sq_lt_one _

lemma kappaH_ge_one130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) : 1 ≤ I.kappaH := by
  exact le_trans I.one_le_nu
    (le_trans I.nu_le_historyInverseNorm I.historyInverseNorm_le_kappaH)

lemma deltaKR130_le_one {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) : deltaKR130 I ≤ 1 := by
  rw [deltaKR130]
  exact (inv_le_one₀ I.kappaH_pos).2 (kappaH_ge_one130 I)

noncomputable def kernelFilterParameters130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) (eta : ℝ)
    (_heta_pos : 0 < eta) (_heta_lt_two : eta < 2) :
    KernelQSP.KernelGeneralParameters126 where
  gap := deltaKR130 I
  targetError := eta / 2
  gap_pos := deltaKR130_pos I
  gap_le_one := deltaKR130_le_one I
  targetError_pos := by positivity
  targetError_lt_one := by linarith

end DalzellDilation
