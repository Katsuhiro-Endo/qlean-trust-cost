import QLean.SignalProcessing.M13bChebyshevCoordinateBridge
import QLean.SignalProcessing.M13bConjugatePhaseWord
import QLean.SignalProcessing.M13bHermitianReflectionScalar
import QLean.SignalProcessing.M13bUnitaritySemanticVerification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace M13bHermitianOuterScalar

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic
open NativeQSPWitnessTransferModel

noncomputable section

abbrev ControlTransferIndex119 := Bool × Fin 2

def controlHadamard119 : Matrix ControlTransferIndex119 ControlTransferIndex119 ℂ :=
  fun row column => if row.2 = column.2 then localH row.1 column.1 else 0

def phaseConjugateBlock119 (T : FixedPointTransferMatrix) :
    Matrix ControlTransferIndex119 ControlTransferIndex119 ℂ :=
  fun row column => if row.1 = column.1 then
    if row.1 then M13bConjugatePhaseWord.entrywiseConj T row.2 column.2
    else T row.2 column.2
  else 0

def sameDirectionHermitianTransfer119 (T : FixedPointTransferMatrix) :
    Matrix ControlTransferIndex119 ControlTransferIndex119 ℂ :=
  controlHadamard119 * phaseConjugateBlock119 T * controlHadamard119

def hermitianSuccessReflectionTransfer119 :
    Matrix ControlTransferIndex119 ControlTransferIndex119 ℂ :=
  Matrix.diagonal fun index =>
    if index = (false, fixedPointSourceIndex) then 1 else -1

def controlSourceBasis119 : ControlTransferIndex119 :=
  (false, fixedPointSourceIndex)

theorem sameDirectionHermitianTransfer119_source_amplitude
    (T : FixedPointTransferMatrix) :
    sameDirectionHermitianTransfer119 T controlSourceBasis119 controlSourceBasis119 =
      ((T fixedPointSourceIndex fixedPointSourceIndex).re : ℂ) := by
  have hsqrt : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  simp [sameDirectionHermitianTransfer119, phaseConjugateBlock119,
    controlHadamard119, controlSourceBasis119,
    M13bConjugatePhaseWord.entrywiseConj, Matrix.mul_apply,
    Fintype.sum_prod_type, fixedPointSourceIndex, localH]
  field_simp
  rw [hsqrt]
  apply Complex.ext
  · simp
    ring
  · simp

theorem outer_scalar_of_unitary_compute
    (C : Matrix ControlTransferIndex119 ControlTransferIndex119 ℂ)
    (hunit : Matrix.conjTranspose C * C = 1) :
    (Matrix.conjTranspose C * hermitianSuccessReflectionTransfer119 * C)
        controlSourceBasis119 controlSourceBasis119 =
      2 * starRingEnd ℂ (C controlSourceBasis119 controlSourceBasis119) *
          C controlSourceBasis119 controlSourceBasis119 - 1 := by
  have hnorm := congrFun (congrFun hunit controlSourceBasis119)
    controlSourceBasis119
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
    hermitianSuccessReflectionTransfer119, controlSourceBasis119,
    Fintype.sum_prod_type, fixedPointSourceIndex] at hnorm ⊢
  linear_combination -hnorm

theorem controlHadamard119_unitary :
    Matrix.conjTranspose controlHadamard119 * controlHadamard119 = 1 := by
  have hlocal : Matrix.conjTranspose localH * localH = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp localH_mem_unitaryGroup
  have hsqrt : ((Real.sqrt 2 : ℂ) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  ext row column
  rcases row with ⟨rowControl, rowIndex⟩
  rcases column with ⟨columnControl, columnIndex⟩
  fin_cases rowControl <;> fin_cases rowIndex <;>
    fin_cases columnControl <;> fin_cases columnIndex <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, controlHadamard119,
      Fintype.sum_prod_type, localH]
  all_goals
    field_simp
    norm_num [hsqrt]

theorem entrywiseConj_unitary (T : FixedPointTransferMatrix)
    (hT : Matrix.conjTranspose T * T = 1) :
    Matrix.conjTranspose (M13bConjugatePhaseWord.entrywiseConj T) *
        M13bConjugatePhaseWord.entrywiseConj T = 1 := by
  have h := congrArg M13bConjugatePhaseWord.entrywiseConj hT
  rw [M13bConjugatePhaseWord.entrywiseConj_mul,
    M13bConjugatePhaseWord.entrywiseConj_one] at h
  have htranspose :
      M13bConjugatePhaseWord.entrywiseConj (Matrix.conjTranspose T) =
        Matrix.conjTranspose (M13bConjugatePhaseWord.entrywiseConj T) := by
    ext row column
    simp [M13bConjugatePhaseWord.entrywiseConj, Matrix.conjTranspose_apply]
  rwa [htranspose] at h

theorem phaseConjugateBlock119_unitary (T : FixedPointTransferMatrix)
    (hT : Matrix.conjTranspose T * T = 1) :
    Matrix.conjTranspose (phaseConjugateBlock119 T) * phaseConjugateBlock119 T = 1 := by
  have hconj := entrywiseConj_unitary T hT
  ext row column
  rcases row with ⟨rowControl, rowIndex⟩
  rcases column with ⟨columnControl, columnIndex⟩
  cases rowControl <;> cases columnControl
  · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseConjugateBlock119,
      Fintype.sum_prod_type, Matrix.one_apply] using
        congrFun (congrFun hT rowIndex) columnIndex
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseConjugateBlock119,
      Fintype.sum_prod_type]
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseConjugateBlock119,
      Fintype.sum_prod_type]
  · simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, phaseConjugateBlock119,
      Fintype.sum_prod_type, Matrix.one_apply] using
        congrFun (congrFun hconj rowIndex) columnIndex

theorem sameDirectionHermitianTransfer119_unitary (T : FixedPointTransferMatrix)
    (hT : Matrix.conjTranspose T * T = 1) :
    Matrix.conjTranspose (sameDirectionHermitianTransfer119 T) *
        sameDirectionHermitianTransfer119 T = 1 := by
  have hhadamard := controlHadamard119_unitary
  have hblock := phaseConjugateBlock119_unitary T hT
  simp only [sameDirectionHermitianTransfer119, Matrix.conjTranspose_mul]
  calc
    (controlHadamard119.conjTranspose *
        ((phaseConjugateBlock119 T).conjTranspose * controlHadamard119.conjTranspose)) *
        (controlHadamard119 * phaseConjugateBlock119 T * controlHadamard119) =
      controlHadamard119.conjTranspose *
        ((phaseConjugateBlock119 T).conjTranspose *
          ((controlHadamard119.conjTranspose * controlHadamard119) *
            (phaseConjugateBlock119 T * controlHadamard119))) := by
        noncomm_ring
    _ = controlHadamard119.conjTranspose *
        ((phaseConjugateBlock119 T).conjTranspose *
          (phaseConjugateBlock119 T * controlHadamard119)) := by rw [hhadamard]; simp
    _ = controlHadamard119.conjTranspose *
        (((phaseConjugateBlock119 T).conjTranspose * phaseConjugateBlock119 T) *
          controlHadamard119) := by rw [Matrix.mul_assoc]
    _ = controlHadamard119.conjTranspose * controlHadamard119 := by rw [hblock]; simp
    _ = 1 := hhadamard

theorem sameDirectionHermitianOuterScalar119 (T : FixedPointTransferMatrix)
    (hT : Matrix.conjTranspose T * T = 1) :
    (Matrix.conjTranspose (sameDirectionHermitianTransfer119 T) *
        hermitianSuccessReflectionTransfer119 * sameDirectionHermitianTransfer119 T)
        controlSourceBasis119 controlSourceBasis119 =
      ((2 * (T fixedPointSourceIndex fixedPointSourceIndex).re ^ 2 - 1 : ℝ) : ℂ) := by
  rw [outer_scalar_of_unitary_compute (sameDirectionHermitianTransfer119 T)
    (sameDirectionHermitianTransfer119_unitary T hT)]
  rw [sameDirectionHermitianTransfer119_source_amplitude]
  have hstar : starRingEnd ℂ
      ((T fixedPointSourceIndex fixedPointSourceIndex).re : ℂ) =
        ((T fixedPointSourceIndex fixedPointSourceIndex).re : ℂ) := by
    simp
  rw [hstar]
  push_cast
  ring

lemma tanh_mono_outer_scalar119 {x y : ℝ} (hxy : x ≤ y) :
    Real.tanh x ≤ Real.tanh y := by
  rw [Real.tanh_eq, Real.tanh_eq]
  have hdx : 0 < Real.exp x + Real.exp (-x) :=
    add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hdy : 0 < Real.exp y + Real.exp (-y) :=
    add_pos (Real.exp_pos _) (Real.exp_pos _)
  apply (div_le_div_iff₀ hdx hdy).2
  have hcross : Real.exp x * Real.exp (-y) ≤
      Real.exp y * Real.exp (-x) := by
    calc
      Real.exp x * Real.exp (-y) = Real.exp (x - y) := by
        rw [Real.exp_sub, Real.exp_neg]
        simp [div_eq_mul_inv]
      _ ≤ Real.exp (y - x) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp y * Real.exp (-x) := by
        rw [Real.exp_sub, Real.exp_neg]
        simp [div_eq_mul_inv]
  nlinarith [hcross]

lemma tanh_le_self_outer_scalar119 {x : ℝ} (hx : 0 ≤ x) :
    Real.tanh x ≤ x := by
  have hmono : StrictMonoOn
      (fun y : ℝ => y * Real.cosh y - Real.sinh y) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun y hy => ?_
    · exact (continuous_id.mul Real.continuous_cosh |>.sub
        Real.continuous_sinh).continuousOn
    · rw [interior_Ici, Set.mem_Ioi] at hy
      have hderiv : HasDerivAt (fun z : ℝ => z * Real.cosh z - Real.sinh z)
          (y * Real.sinh y) y := by
        change HasDerivAt ((id * Real.cosh) - Real.sinh) (y * Real.sinh y) y
        simpa only [id_eq, one_mul, add_sub_cancel_left] using
          ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
            (Real.hasDerivAt_sinh y)
      rw [hderiv.deriv]
      have hsinh : 0 < Real.sinh y := (Real.sinh_pos_iff).2 hy
      nlinarith
  have hbound : 0 ≤ x * Real.cosh x - Real.sinh x := by
    have h := hmono.monotoneOn (by simp) (by simpa using hx) hx
    simpa using h
  rw [Real.tanh_eq_sinh_div_cosh]
  apply (div_le_iff₀ (Real.cosh_pos x)).2
  linarith

lemma cosh_ge_self_outer_scalar119 {x : ℝ} (hx : 1 ≤ x) : x ≤ Real.cosh x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogx := Real.log_le_sub_one_of_pos hx0
  have hlog : Real.log (2 * x) ≤ x := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0)]
    linarith
  have hexp : 2 * x ≤ Real.exp x := by
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by positivity)] at h
    exact h
  rw [Real.cosh_eq]
  have he0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  nlinarith

lemma arcosh_le_self_outer_scalar119 {x : ℝ} (hx : 1 ≤ x) :
    Real.arcosh x ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hcx0 : 0 < Real.cosh x := Real.cosh_pos x
  have hmono : Real.arcosh x ≤ Real.arcosh (Real.cosh x) :=
    (Real.arcosh_le_arcosh hx0 hcx0).2 (cosh_ge_self_outer_scalar119 hx)
  simpa [Real.arcosh_cosh (le_of_lt hx0)] using hmono

lemma transitionWidth_le_sq_gap119
    (params : KernelQSP.KernelGeneralParameters126) :
    (KernelQSP.fixedPointParametersGeneral126 params).transitionWidth ≤
      params.gap ^ 2 := by
  let fp := KernelQSP.fixedPointParametersGeneral126 params
  let e : ℝ := params.targetError
  let g : ℝ := params.gap
  have he : 0 < e := params.targetError_pos
  have he1 : e < 1 := params.targetError_lt_one
  have hg : 0 < g := params.gap_pos
  have hge1 : 1 ≤ 1 / e := by
    rw [le_div_iff₀ he]
    nlinarith
  have ha : Real.arcosh (1 / e) ≤ 1 / e :=
    arcosh_le_self_outer_scalar119 hge1
  have hLspec := KernelQSP.queryLowerBoundGeneral126_spec params
  have hden : 0 < g * e := mul_pos hg he
  have hLpos : 0 < (KernelQSP.L_KRGeneral126 params : ℝ) := by
    exact_mod_cast KernelQSP.L_KRGeneral126_pos params
  have hinv : 1 / e < g * (KernelQSP.queryLowerBoundGeneral126 params : ℝ) := by
    have hq : 1 / (g * e) <
        (KernelQSP.queryLowerBoundGeneral126 params : ℝ) := by
      simpa [g, e, KernelQSP.gapEtaProductGeneral126] using hLspec
    apply (div_lt_iff₀ he).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using (div_lt_iff₀ hden).mp hq
  have hLg : 1 / e < g * (KernelQSP.L_KRGeneral126 params : ℝ) := by
    calc
      1 / e < g * (KernelQSP.queryLowerBoundGeneral126 params : ℝ) := hinv
      _ ≤ g * (KernelQSP.L_KRGeneral126 params : ℝ) := by
        gcongr
        exact_mod_cast KernelQSP.L_KRGeneral126_lower params
  have harg :
      Real.arcosh (1 / e) /
          (KernelQSP.L_KRGeneral126 params : ℝ) ≤ g := by
    apply (div_le_iff₀ hLpos).2
    calc
      Real.arcosh (1 / e) ≤ 1 / e := ha
      _ ≤ g * (KernelQSP.L_KRGeneral126 params : ℝ) := hLg.le
  have harg_nonneg : 0 ≤
      Real.arcosh (1 / e) /
        (KernelQSP.L_KRGeneral126 params : ℝ) := by
    exact div_nonneg (Real.arcosh_nonneg hge1) hLpos.le
  have htanh : Real.tanh (
      Real.arcosh (1 / e) /
        (KernelQSP.L_KRGeneral126 params : ℝ)) ≤ g := by
    calc
      Real.tanh (Real.arcosh (1 / e) /
          (KernelQSP.L_KRGeneral126 params : ℝ)) ≤
          Real.tanh g := tanh_mono_outer_scalar119 harg
      _ ≤ g := tanh_le_self_outer_scalar119 (le_of_lt hg)
  have htanh_nonneg : 0 ≤ Real.tanh (
      Real.arcosh (1 / e) /
        (KernelQSP.L_KRGeneral126 params : ℝ)) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr harg_nonneg)
      (Real.cosh_pos _).le
  simpa [fp, e, g, KernelQSP.fixedPointParametersGeneral126,
    FixedPointChebyshevParameters.transitionWidth] using
    (sq_le_sq₀ htanh_nonneg (le_of_lt hg)).2 htanh

end

end M13bHermitianOuterScalar
