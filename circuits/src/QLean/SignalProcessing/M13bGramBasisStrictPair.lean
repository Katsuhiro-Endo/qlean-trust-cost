import QLean.SignalProcessing.M13bQSVTLogicalEmbedding
import QLean.SignalProcessing.M13bHermitianOuterScalar
import QLean.SignalProcessing.M13bConjugateControlledCompute
import QLean.SignalProcessing.M13bControlXStateSemantics
import QLean.SignalProcessing.M13bHadamardTrueStateSemantics
import QLean.SignalProcessing.M13bTwoFrameHermitianDilation
import QLean.SignalProcessing.M13bHermitianSuccessReflection
import QLean.SignalProcessing.M13bUnitaritySemanticVerification
import QLean.SignalProcessing.KernelReflectionRightSVTSpectralTransfer

set_option autoImplicit false

namespace M13bGramBasisStrictPair

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness
open NativeSingularPairTwoFrame
open SpectralSamplingProof.Analytic

noncomputable def executableGramOperator119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source) :=
  GramOperator.gNuOperator (ExecutableHistoryExecutableP18.executableSystem119 source)
    (ExecutableHistoryExecutableP18.executableAlpha119 source) assumptions.nu

def realColumn119 {ι : Type*} (v : ι → ℝ) : Column ι :=
  fun i => (v i : ℂ)

theorem realColumn119_smul
    {ι : Type*} (a : ℝ) (v : ι → ℝ) :
    (a : ℂ) • realColumn119 v = realColumn119 (a • v) := by
  ext i
  simp [realColumn119]

theorem executableGNu_mulVec_realColumn119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (v : executableSignalCleanIndex119 source → ℝ) :
    (executableGNuOperator119 source assumptions).mulVec (realColumn119 v) =
      realColumn119 ((executableGramOperator119 source assumptions).mulVec v) := by
  ext i
  simp [executableGNuOperator119, executableGramOperator119, realColumn119,
    Matrix.mulVec, dotProduct]

theorem executableGNu_adjoint_mulVec_realColumn119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (v : executableSignalCleanIndex119 source → ℝ) :
    (Matrix.conjTranspose (executableGNuOperator119 source assumptions)).mulVec
        (realColumn119 v) =
      realColumn119 ((executableGramOperator119 source assumptions).transpose.mulVec v) := by
  ext i
  simp [executableGNuOperator119, executableGramOperator119, realColumn119,
    Matrix.mulVec, Matrix.conjTranspose, dotProduct]

/-! The strict-pair route is deliberately separated from the Gram spectral
route: a strict pair requires a nonzero complementary amplitude. -/

theorem executable_gram_basis_zero_in_kernel119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source)
    (hj : DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 0) :
    (executableGramOperator119 source assumptions).mulVec
        ((DalzellDilation.gramBasis130 (executableGramOperator119 source assumptions) j).ofLp) = 0 := by
  apply DalzellDilation.euclidean_toLp_zero130
  rw [← DalzellDilation.gram_eigenvalue_eq_unitNormSquared130]
  exact hj

noncomputable def executableGramZeroStrictPair119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source)
    (hj : DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 0) :
    ExecutableP18StrictSingularPair119 source assumptions where
  sigma := 0
  g := 1
  v := realColumn119 ((DalzellDilation.gramBasis130 (executableGramOperator119 source assumptions) j).ofLp)
  u := realColumn119 0
  singular_forward := by
    rw [executableGNu_mulVec_realColumn119]
    rw [executable_gram_basis_zero_in_kernel119 source assumptions j hj]
    ext i
    simp [realColumn119]
  singular_adjoint := by
    have hzero : realColumn119 (0 : executableSignalCleanIndex119 source → ℝ) = 0 := by
      ext i
      simp [realColumn119]
    rw [hzero]
    simp
  sigma_nonneg := by norm_num
  g_nonneg := by norm_num
  completion := by norm_num
  g_ne_zero := by norm_num

noncomputable def executableGramPositiveStrictPair119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source)
    (hpos : 0 < DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j)
    (hlt : Real.sqrt (DalzellDilation.gramEigenvalue130
      (executableGramOperator119 source assumptions) j) < 1) :
    ExecutableP18StrictSingularPair119 source assumptions where
  sigma := Real.sqrt (DalzellDilation.gramEigenvalue130
    (executableGramOperator119 source assumptions) j)
  g := Real.sqrt (1 - (Real.sqrt (DalzellDilation.gramEigenvalue130
    (executableGramOperator119 source assumptions) j)) ^ 2)
  v := realColumn119 ((DalzellDilation.gramBasis130 (executableGramOperator119 source assumptions) j).ofLp)
  u := realColumn119 ((Real.sqrt (DalzellDilation.gramEigenvalue130
    (executableGramOperator119 source assumptions) j))⁻¹ •
      (executableGramOperator119 source assumptions).mulVec
        ((DalzellDilation.gramBasis130 (executableGramOperator119 source assumptions) j).ofLp))
  singular_forward := by
    let G := executableGramOperator119 source assumptions
    let ev := DalzellDilation.gramEigenvalue130 G j
    let σ := Real.sqrt ev
    let e := (DalzellDilation.gramBasis130 G j).ofLp
    have hσ : σ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    rw [executableGNu_mulVec_realColumn119]
    rw [realColumn119_smul]
    congr 1
    change G.mulVec e = σ • (σ⁻¹ • G.mulVec e)
    rw [smul_smul]
    rw [mul_inv_cancel₀ hσ, one_smul]
  singular_adjoint := by
    let G := executableGramOperator119 source assumptions
    let ev := DalzellDilation.gramEigenvalue130 G j
    let σ := Real.sqrt ev
    let e := (DalzellDilation.gramBasis130 G j).ofLp
    have hnonneg : 0 ≤ ev := DalzellDilation.gram_eigenvalue_nonneg130 G j
    have hσ : σ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hgram : G.transpose.mulVec (G.mulVec e) = ev • e := by
      have hgram0 := (DalzellDilation.gramHermitian130 G).mulVec_eigenvectorBasis j
      change (DalzellDilation.gramMatrix130 G).mulVec
          ((DalzellDilation.gramBasis130 G j).ofLp) =
        DalzellDilation.gramEigenvalue130 G j •
          ((DalzellDilation.gramBasis130 G j).ofLp) at hgram0
      simpa [DalzellDilation.gramMatrix130, Matrix.mulVec_mulVec, e, ev] using hgram0
    rw [executableGNu_adjoint_mulVec_realColumn119]
    rw [realColumn119_smul]
    congr 1
    change G.transpose.mulVec (σ⁻¹ • G.mulVec e) = σ • e
    calc
      G.transpose.mulVec (σ⁻¹ • G.mulVec e) =
          σ⁻¹ • G.transpose.mulVec (G.mulVec e) := by
            ext i
            simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = σ⁻¹ • (ev • e) := by rw [hgram]
      _ = σ • e := by
        rw [smul_smul]
        congr 1
        change σ⁻¹ * ev = σ
        have hsquare : σ ^ 2 = ev := by
          simpa [σ] using Real.sq_sqrt hnonneg
        rw [← hsquare]
        field_simp [hσ]
  sigma_nonneg := Real.sqrt_nonneg _
  g_nonneg := Real.sqrt_nonneg _
  completion := by
    let ev := DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j
    let σ := Real.sqrt ev
    have hσ_nonneg : 0 ≤ σ := Real.sqrt_nonneg _
    have hinside : 0 ≤ 1 - σ ^ 2 := by nlinarith
    rw [Real.sq_sqrt hinside]
    ring
  g_ne_zero := by
    let ev := DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j
    let σ := Real.sqrt ev
    have hσ_nonneg : 0 ≤ σ := Real.sqrt_nonneg _
    have hinside : 0 < 1 - σ ^ 2 := by nlinarith
    exact ne_of_gt (Real.sqrt_pos.mpr hinside)

/-- Every Gram eigenvector below the boundary gives the strict-pair datum
required by the physical pairwise theorem.  The zero eigenvalue uses the
separate `u = 0` branch; nonzero eigenvalues use the normalized image. -/
noncomputable def executableGramStrictPair119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source)
    (hstrict : Real.sqrt (DalzellDilation.gramEigenvalue130
      (executableGramOperator119 source assumptions) j) < 1) :
    ExecutableP18StrictSingularPair119 source assumptions := by
  by_cases hzero : DalzellDilation.gramEigenvalue130
      (executableGramOperator119 source assumptions) j = 0
  · exact executableGramZeroStrictPair119 source assumptions j hzero
  · apply executableGramPositiveStrictPair119 source assumptions j
    exact lt_of_le_of_ne
      (DalzellDilation.gram_eigenvalue_nonneg130 _ j) (Ne.symm hzero)
    exact hstrict

theorem executable_gram_basis_sqrt_le_one119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source) :
    Real.sqrt (DalzellDilation.gramEigenvalue130
      (executableGramOperator119 source assumptions) j) ≤ 1 := by
  exact DalzellDilation.gram_basis_sqrt_le_one130 _ j
    (DalzellDilation.gNu_norm_le_one
      (ExecutableHistoryExecutableP18.executableP18Input119 source assumptions))

end M13bGramBasisStrictPair
