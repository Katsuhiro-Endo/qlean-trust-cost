import QLean.SignalProcessing.M13bGramBasisStrictPair
import QLean.Circuits.Foundation.OperatorL2Error

set_option autoImplicit false

namespace M13bBoundaryNoLeak

open VerifiedCircuitCore

def euclideanColumn {ι : Type*} (x : ι → ℂ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 x

lemma inner_pi_complex {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    inner ℂ (euclideanColumn x) (euclideanColumn y) =
      ∑ i, star (x i) * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, y i * star (x i)) = ∑ i, star (x i) * y i
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma inner_mulVec_left {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (x : n → ℂ) (y : m → ℂ) :
    inner ℂ (euclideanColumn (A.mulVec x)) (euclideanColumn y) =
      inner ℂ (euclideanColumn x)
        (euclideanColumn ((Matrix.conjTranspose A).mulVec y)) := by
  rw [inner_pi_complex, inner_pi_complex]
  change star (A.mulVec x) ⬝ᵥ y =
    star x ⬝ᵥ (Matrix.conjTranspose A).mulVec y
  calc
    star (A.mulVec x) ⬝ᵥ y =
        Matrix.vecMul (star x) (Matrix.conjTranspose A) ⬝ᵥ y := by
      rw [Matrix.vecMul_conjTranspose]
      simp
    _ = star x ⬝ᵥ (Matrix.conjTranspose A).mulVec y :=
      (Matrix.dotProduct_mulVec (star x) (Matrix.conjTranspose A) y).symm

theorem unitary_isometry_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : Matrix.conjTranspose U * U = 1)
    (x y : ι → ℂ) :
    inner ℂ (euclideanColumn (U.mulVec x))
      (euclideanColumn (U.mulVec y)) =
      inner ℂ (euclideanColumn x) (euclideanColumn y) := by
  rw [inner_mulVec_left]
  rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

theorem isometry_inner {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq clean] (E : Matrix basis clean ℂ)
    (hE : Matrix.conjTranspose E * E = 1) (x y : clean → ℂ) :
    inner ℂ (euclideanColumn (E.mulVec x))
      (euclideanColumn (E.mulVec y)) =
      inner ℂ (euclideanColumn x) (euclideanColumn y) := by
  rw [inner_mulVec_left]
  rw [Matrix.mulVec_mulVec, hE, Matrix.one_mulVec]

theorem no_leakage_of_unit_saturation
    {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    (U : Matrix basis basis ℂ) (E : Matrix basis clean ℂ)
    (hU : Matrix.conjTranspose U * U = 1)
    (hE : Matrix.conjTranspose E * E = 1)
    (v u : clean → ℂ)
    (hcompress : (Matrix.conjTranspose E).mulVec (U.mulVec (E.mulVec v)) = u)
    (hv : inner ℂ (euclideanColumn v) (euclideanColumn v) = 1)
    (hu : inner ℂ (euclideanColumn u) (euclideanColumn u) = 1) :
    U.mulVec (E.mulVec v) = E.mulVec u := by
  let x := U.mulVec (E.mulVec v)
  let y := E.mulVec u
  have hxx : inner ℂ (euclideanColumn x) (euclideanColumn x) = 1 := by
    rw [show x = U.mulVec (E.mulVec v) by rfl]
    rw [unitary_isometry_inner U hU]
    rw [isometry_inner E hE]
    exact hv
  have hyy : inner ℂ (euclideanColumn y) (euclideanColumn y) = 1 := by
    rw [show y = E.mulVec u by rfl]
    rw [isometry_inner E hE]
    exact hu
  have hyx : inner ℂ (euclideanColumn y) (euclideanColumn x) = 1 := by
    rw [show y = E.mulVec u by rfl]
    rw [inner_mulVec_left]
    rw [show x = U.mulVec (E.mulVec v) by rfl]
    rw [hcompress]
    exact hu
  have hnormx : ‖euclideanColumn x‖ = 1 := by
    have hsq := congrArg Complex.re hxx
    rw [inner_self_eq_norm_sq_to_K] at hsq
    have hsq' : ‖euclideanColumn x‖ ^ 2 = 1 := by exact_mod_cast hsq
    clear hsq
    rw [pow_two] at hsq'
    nlinarith [hsq', norm_nonneg (euclideanColumn x)]
  have hnormy : ‖euclideanColumn y‖ = 1 := by
    have hsq := congrArg Complex.re hyy
    rw [inner_self_eq_norm_sq_to_K] at hsq
    have hsq' : ‖euclideanColumn y‖ ^ 2 = 1 := by exact_mod_cast hsq
    clear hsq
    rw [pow_two] at hsq'
    nlinarith [hsq', norm_nonneg (euclideanColumn y)]
  have hdiff : ‖euclideanColumn x - euclideanColumn y‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ) (euclideanColumn x) (euclideanColumn y),
      hnormx, hnormy]
    have hre := congrArg Complex.re hyx
    have hxy : inner ℂ (euclideanColumn x) (euclideanColumn y) = 1 := by
      calc
        inner ℂ (euclideanColumn x) (euclideanColumn y) =
            star (inner ℂ (euclideanColumn y) (euclideanColumn x)) :=
          (inner_conj_symm (euclideanColumn x) (euclideanColumn y)).symm
        _ = star 1 := by rw [hyx]
        _ = 1 := by simp
    rw [hxy]
    norm_num
  have hzero : ‖euclideanColumn x - euclideanColumn y‖ = 0 := by
    nlinarith [norm_nonneg (euclideanColumn x - euclideanColumn y)]
  have heq : euclideanColumn x = euclideanColumn y :=
    sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have hraw := congrArg (fun z : EuclideanSpace ℂ basis => z.ofLp) heq
  simpa [euclideanColumn, x, y] using hraw

end M13bBoundaryNoLeak
