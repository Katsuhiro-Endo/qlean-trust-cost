import QLean.Circuits.Foundation.WireEmbedding
import VerifiedMath.Basis

/-!
# Constructive two-frame columns from one strict singular pair

This module is intentionally independent of P18.  It records the algebraic
construction used by a unitary dilation of a clean block `G = E† U E`:

`S0 = E v`, `T1 = E u`, `T0 = (U S0 - σ T1) / g`, and
`S1 = (U† T1 - σ S0) / g`, where `g² + σ² = 1` and `g ≠ 0`.

No cross-image matrix entry is postulated.  The later P18 rebind must prove
the clean-block singular-pair equations and the strict branch `g ≠ 0`.
-/

namespace NativeSingularPairTwoFrame

open VerifiedCircuitCore

noncomputable section

abbrev Column (basis : Type*) := State basis

/-- The clean compression of a physical operator. -/
def cleanBlock {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    (U : Operator basis) (E : Matrix basis clean ℂ) : Operator clean :=
  Matrix.conjTranspose E * U * E

/-- Matrix whose `logical` column is the physical computational-basis ket at
`embedding logical`.  It is the canonical linear extension of a finite basis
embedding. -/
def basisKetEmbeddingMatrix {basis clean : Type*} [DecidableEq basis]
    (embedding : clean ↪ basis) : Matrix basis clean ℂ :=
  VerifiedMath.Basis.embeddingMatrix embedding

/-- A computational-basis embedding is an isometry. -/
theorem basisKetEmbeddingMatrix_isometry {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (embedding : clean ↪ basis) :
    Matrix.conjTranspose (basisKetEmbeddingMatrix embedding) *
        basisKetEmbeddingMatrix embedding = 1 := by
  classical
  ext left right
  by_cases equal : left = right
  · subst right
    simp [basisKetEmbeddingMatrix, Matrix.mul_apply, basisKet]
  · have reverse : right ≠ left := Ne.symm equal
    simp [basisKetEmbeddingMatrix, Matrix.mul_apply, basisKet, equal, reverse]

/-- Compressing an operator by a computational-basis embedding reads exactly
the corresponding physical matrix entry. -/
theorem cleanBlock_basisKetEmbeddingMatrix_apply {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (operator : Operator basis) (embedding : clean ↪ basis)
    (output input : clean) :
    cleanBlock operator (basisKetEmbeddingMatrix embedding) output input =
      operator (embedding output) (embedding input) := by
  classical
  simp [cleanBlock, basisKetEmbeddingMatrix, Matrix.mul_apply, basisKet]

def cleanProjector {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    (E : Matrix basis clean ℂ) : Operator basis :=
  E * Matrix.conjTranspose E

/-- Matrix entry of the image projector associated with a computational-basis
embedding. -/
theorem cleanProjector_basisKetEmbeddingMatrix_entry {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (embedding : clean ↪ basis) (output input : basis) :
    (cleanProjector (basisKetEmbeddingMatrix embedding)) output input =
      if output = input then
        if ∃ logical : clean, input = embedding logical then 1 else 0
      else 0 := by
  classical
  unfold cleanProjector
  by_cases same : output = input
  · subst output
    by_cases inside : ∃ logical : clean, input = embedding logical
    · rcases inside with ⟨logical, rfl⟩
      simp [basisKetEmbeddingMatrix, Matrix.mul_apply, basisKet]
    · simp only [Matrix.mul_apply, basisKetEmbeddingMatrix,
        Matrix.conjTranspose_apply, basisKet]
      rw [Finset.sum_eq_zero]
      · simp [inside]
      · intro logical _
        have notMatch : input ≠ embedding logical := by
          intro equal
          exact inside ⟨logical, equal⟩
        simp [notMatch]
  · have reverse : input ≠ output := Ne.symm same
    simp only [Matrix.mul_apply, basisKetEmbeddingMatrix,
      Matrix.conjTranspose_apply, basisKet]
    rw [Finset.sum_eq_zero]
    · simp [same]
    · intro logical _
      by_cases outputMatch : output = embedding logical
      · by_cases inputMatch : input = embedding logical
        · exact False.elim (same (outputMatch.trans inputMatch.symm))
        · simp [outputMatch, inputMatch]
      · simp [outputMatch]

/-- The exact full-space phase associated with a clean image projector. -/
def imagePhaseOperator {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    (E : Matrix basis clean ℂ) (angle : ℝ) : Operator basis :=
  1 + (Complex.exp (Complex.I * (angle : ℂ)) - 1) • cleanProjector E

/-- Algebraic data for the strict singular-value branch.  The two unitary
identities are retained separately because both are used in the two columns. -/
structure StrictSingularPairData (basis clean : Type*)
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean] where
  U : Operator basis
  E : Matrix basis clean ℂ
  sigma : ℝ
  g : ℝ
  v : Column clean
  u : Column clean
  U_star_right : U * Matrix.conjTranspose U = 1
  U_star_left : Matrix.conjTranspose U * U = 1
  E_isometry : Matrix.conjTranspose E * E = 1
  singular_forward : (cleanBlock U E).mulVec v = Complex.ofReal sigma • u
  singular_adjoint : (Matrix.conjTranspose (cleanBlock U E)).mulVec u =
    Complex.ofReal sigma • v
  completion : g ^ 2 + sigma ^ 2 = 1
  g_ne_zero : g ≠ 0

def sourceZero {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) : Column basis :=
  data.E.mulVec data.v

def targetOne {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) : Column basis :=
  data.E.mulVec data.u

def targetZero {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) : Column basis :=
  (data.g : ℂ)⁻¹ •
    (data.U.mulVec (sourceZero data) - (data.sigma : ℂ) • targetOne data)

def sourceOne {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) : Column basis :=
  (data.g : ℂ)⁻¹ •
    ((Matrix.conjTranspose data.U).mulVec (targetOne data) -
      (data.sigma : ℂ) • sourceZero data)

/-- A two-column matrix written in the source/target coordinate order. -/
def twoColumnFrame {basis : Type*} [DecidableEq (Fin 2)]
    (zero one : Column basis) : Matrix basis (Fin 2) ℂ :=
  fun basis column => if column = 0 then zero basis else one basis

def sourceFrame {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    [DecidableEq (Fin 2)] (data : StrictSingularPairData basis clean) :
    Matrix basis (Fin 2) ℂ :=
  twoColumnFrame (sourceZero data) (sourceOne data)

def targetFrame {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    [DecidableEq (Fin 2)] (data : StrictSingularPairData basis clean) :
    Matrix basis (Fin 2) ℂ :=
  twoColumnFrame (targetZero data) (targetOne data)

/-- The two transfer columns use the orientation
`[[g, -σ], [σ, g]]`. -/
def singularTransferMatrix (sigma g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun row column =>
    if row = 0 then
      if column = 0 then g else -sigma
    else if column = 0 then sigma else g

/-- Dividing the defining equation of `T0` back by `g` gives the first
forward column relation without using any cross-image premise. -/
theorem sourceZero_forward_relation {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    data.U.mulVec (sourceZero data) =
      (data.g : ℂ) • targetZero data + (data.sigma : ℂ) • targetOne data := by
  have hg : (data.g : ℂ) ≠ 0 := by
    exact_mod_cast data.g_ne_zero
  unfold targetZero
  rw [smul_smul, mul_inv_cancel₀ hg, one_smul]
  exact (sub_add_cancel _ _).symm

/-- The adjoint defining equation of `S1` gives the second adjoint column
relation, again without a physical cross-entry hypothesis. -/
theorem targetOne_adjoint_relation {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (Matrix.conjTranspose data.U).mulVec (targetOne data) =
      (data.g : ℂ) • sourceOne data + (data.sigma : ℂ) • sourceZero data := by
  have hg : (data.g : ℂ) ≠ 0 := by
    exact_mod_cast data.g_ne_zero
  unfold sourceOne
  rw [smul_smul, mul_inv_cancel₀ hg, one_smul]
  exact (sub_add_cancel _ _).symm

/-- Any column annihilated by the clean projector is fixed by the exact image
phase.  This is the only phase fact required for the `S1` and `T0` columns. -/
theorem imagePhase_apply_of_projector_zero {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (E : Matrix basis clean ℂ) (angle : ℝ) (column : Column basis)
    (outside : (cleanProjector E).mulVec column = 0) :
    (imagePhaseOperator E angle).mulVec column = column := by
  unfold imagePhaseOperator
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, outside]
  simp

/-- Any column fixed by the clean projector receives exactly the symbolic
phase `exp(i*angle)`. -/
theorem imagePhase_apply_of_projector_one {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (E : Matrix basis clean ℂ) (angle : ℝ) (column : Column basis)
    (inside : (cleanProjector E).mulVec column = column) :
    (imagePhaseOperator E angle).mulVec column =
      Complex.exp (Complex.I * (angle : ℂ)) • column := by
  unfold imagePhaseOperator
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, inside]
  ext i
  simp
  ring

/-- The clean adjoint recovers the coordinate vector from the source-image
column. -/
theorem adjointEmbedding_sourceZero {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (Matrix.conjTranspose data.E).mulVec (sourceZero data) = data.v := by
  unfold sourceZero
  rw [Matrix.mulVec_mulVec, data.E_isometry]
  exact Matrix.one_mulVec _

/-- The clean adjoint likewise recovers the target coordinate vector. -/
theorem adjointEmbedding_targetOne {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (Matrix.conjTranspose data.E).mulVec (targetOne data) = data.u := by
  unfold targetOne
  rw [Matrix.mulVec_mulVec, data.E_isometry]
  exact Matrix.one_mulVec _

/-- Both directly embedded columns lie in the clean projector image. -/
theorem cleanProjector_sourceZero {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (cleanProjector data.E).mulVec (sourceZero data) = sourceZero data := by
  unfold cleanProjector
  rw [← Matrix.mulVec_mulVec, adjointEmbedding_sourceZero]
  rfl

theorem cleanProjector_targetOne {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (cleanProjector data.E).mulVec (targetOne data) = targetOne data := by
  unfold cleanProjector
  rw [← Matrix.mulVec_mulVec, adjointEmbedding_targetOne]
  rfl

/-- The forward singular equation, expressed after applying the physical
clean adjoint. -/
theorem adjointEmbedding_U_sourceZero {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (Matrix.conjTranspose data.E).mulVec (data.U.mulVec (sourceZero data)) =
      (data.sigma : ℂ) • data.u := by
  calc
    (Matrix.conjTranspose data.E).mulVec (data.U.mulVec (sourceZero data)) =
        (Matrix.conjTranspose data.E * data.U * data.E).mulVec data.v := by
      unfold sourceZero
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = (cleanBlock data.U data.E).mulVec data.v := by rfl
    _ = (data.sigma : ℂ) • data.u := data.singular_forward

/-- The adjoint singular equation in the corresponding physical form. -/
theorem adjointEmbedding_Uadjoint_targetOne {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (Matrix.conjTranspose data.E).mulVec
        ((Matrix.conjTranspose data.U).mulVec (targetOne data)) =
      (data.sigma : ℂ) • data.v := by
  have hblockadjoint :
      Matrix.conjTranspose data.E * Matrix.conjTranspose data.U * data.E =
        Matrix.conjTranspose (cleanBlock data.U data.E) := by
    simp [cleanBlock, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  calc
    (Matrix.conjTranspose data.E).mulVec
        ((Matrix.conjTranspose data.U).mulVec (targetOne data)) =
        (Matrix.conjTranspose data.E * Matrix.conjTranspose data.U * data.E).mulVec
          data.u := by
      unfold targetOne
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = (Matrix.conjTranspose (cleanBlock data.U data.E)).mulVec data.u := by
      rw [hblockadjoint]
    _ = (data.sigma : ℂ) • data.v := data.singular_adjoint

/-- The constructed `T0` has no component in the clean image. -/
theorem adjointEmbedding_targetZero_zero {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (Matrix.conjTranspose data.E).mulVec (targetZero data) = 0 := by
  unfold targetZero
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, adjointEmbedding_U_sourceZero,
    Matrix.mulVec_smul, adjointEmbedding_targetOne]
  simp

/-- The constructed `S1` has no component in the clean image. -/
theorem adjointEmbedding_sourceOne_zero {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (Matrix.conjTranspose data.E).mulVec (sourceOne data) = 0 := by
  unfold sourceOne
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub,
    adjointEmbedding_Uadjoint_targetOne, Matrix.mulVec_smul,
    adjointEmbedding_sourceZero]
  simp

/-- Thus the two constructed complementary columns are fixed by the clean
image phase. -/
theorem cleanProjector_targetZero_zero {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (cleanProjector data.E).mulVec (targetZero data) = 0 := by
  unfold cleanProjector
  rw [← Matrix.mulVec_mulVec, adjointEmbedding_targetZero_zero]
  simp

theorem cleanProjector_sourceOne_zero {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (cleanProjector data.E).mulVec (sourceOne data) = 0 := by
  unfold cleanProjector
  rw [← Matrix.mulVec_mulVec, adjointEmbedding_sourceOne_zero]
  simp

/-- Left and right unitarity, in the two vector forms used for frame
completion. -/
theorem U_mul_Uadjoint_apply {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) (column : Column basis) :
    data.U.mulVec ((Matrix.conjTranspose data.U).mulVec column) = column := by
  rw [Matrix.mulVec_mulVec, data.U_star_right]
  exact Matrix.one_mulVec _

theorem Uadjoint_mul_U_apply {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) (column : Column basis) :
    (Matrix.conjTranspose data.U).mulVec (data.U.mulVec column) = column := by
  rw [Matrix.mulVec_mulVec, data.U_star_left]
  exact Matrix.one_mulVec _

/-- The second forward column follows solely from the unitary identities and
`g² + σ² = 1`. -/
theorem sourceOne_forward_relation {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    data.U.mulVec (sourceOne data) =
      -(data.sigma : ℂ) • targetZero data + (data.g : ℂ) • targetOne data := by
  have hg : (data.g : ℂ) ≠ 0 := by
    exact_mod_cast data.g_ne_zero
  have hcompletion : (data.g : ℂ) ^ 2 + (data.sigma : ℂ) ^ 2 = 1 := by
    exact_mod_cast data.completion
  unfold sourceOne
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, U_mul_Uadjoint_apply,
    Matrix.mulVec_smul, sourceZero_forward_relation]
  ext i
  apply (mul_left_cancel₀ hg)
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hg, one_mul]
  linear_combination -(targetOne data i) * hcompletion

/-- The remaining adjoint column follows by the symmetric calculation. -/
theorem targetZero_adjoint_relation {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    (Matrix.conjTranspose data.U).mulVec (targetZero data) =
      (data.g : ℂ) • sourceZero data - (data.sigma : ℂ) • sourceOne data := by
  have hg : (data.g : ℂ) ≠ 0 := by
    exact_mod_cast data.g_ne_zero
  have hcompletion : (data.g : ℂ) ^ 2 + (data.sigma : ℂ) ^ 2 = 1 := by
    exact_mod_cast data.completion
  unfold targetZero
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Uadjoint_mul_U_apply,
    Matrix.mulVec_smul, targetOne_adjoint_relation]
  ext i
  apply (mul_left_cancel₀ hg)
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hg, one_mul]
  linear_combination -(sourceZero data i) * hcompletion

/-- Left multiplication acts columnwise on a two-column frame. -/
theorem operator_mul_twoColumnFrame {basis : Type*} [Fintype basis]
    [DecidableEq basis] [DecidableEq (Fin 2)]
    (operator : Operator basis) (zero one : Column basis) :
    operator * twoColumnFrame zero one =
      twoColumnFrame (operator.mulVec zero) (operator.mulVec one) := by
  ext output column
  fin_cases column <;>
    simp [twoColumnFrame, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- The forward two-column transfer is exactly the real rotation written by
`singularTransferMatrix`. -/
theorem targetFrame_mul_singularTransferMatrix {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    [DecidableEq (Fin 2)] (data : StrictSingularPairData basis clean) :
    targetFrame data * singularTransferMatrix data.sigma data.g =
      twoColumnFrame
        ((data.g : ℂ) • targetZero data + (data.sigma : ℂ) • targetOne data)
        (-(data.sigma : ℂ) • targetZero data + (data.g : ℂ) • targetOne data) := by
  ext output column
  fin_cases column <;>
    simp [targetFrame, twoColumnFrame, singularTransferMatrix, Matrix.mul_apply] <;>
    ring

/-- The strict construction closes the forward two-column equation. -/
theorem strictFrame_forward {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    [DecidableEq (Fin 2)] (data : StrictSingularPairData basis clean) :
    data.U * sourceFrame data =
      targetFrame data * singularTransferMatrix data.sigma data.g := by
  unfold sourceFrame
  rw [operator_mul_twoColumnFrame, targetFrame_mul_singularTransferMatrix,
    sourceZero_forward_relation, sourceOne_forward_relation]

/-- The adjoint transfer matrix is the conjugate transpose of the same real
rotation. -/
theorem sourceFrame_mul_singularTransferMatrix_adjoint {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    [DecidableEq (Fin 2)] (data : StrictSingularPairData basis clean) :
    sourceFrame data * Matrix.conjTranspose
        (singularTransferMatrix data.sigma data.g) =
      twoColumnFrame
        ((data.g : ℂ) • sourceZero data - (data.sigma : ℂ) • sourceOne data)
        ((data.sigma : ℂ) • sourceZero data + (data.g : ℂ) • sourceOne data) := by
  ext output column
  fin_cases column <;>
    simp [sourceFrame, twoColumnFrame, singularTransferMatrix,
      Matrix.conjTranspose_apply, Matrix.mul_apply] <;>
    ring

/-- The strict construction closes the adjoint two-column equation. -/
theorem strictFrame_adjoint {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    [DecidableEq (Fin 2)] (data : StrictSingularPairData basis clean) :
    (Matrix.conjTranspose data.U) * targetFrame data =
      sourceFrame data * Matrix.conjTranspose
        (singularTransferMatrix data.sigma data.g) := by
  unfold targetFrame
  rw [operator_mul_twoColumnFrame,
    sourceFrame_mul_singularTransferMatrix_adjoint,
    targetZero_adjoint_relation, targetOne_adjoint_relation]
  ext output column
  fin_cases column <;> simp [twoColumnFrame, add_comm]

end

end NativeSingularPairTwoFrame
