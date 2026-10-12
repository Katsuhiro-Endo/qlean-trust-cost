import QLean.SignalProcessing.KernelReflectionRightSVTSpectralTransfer

/-!
# M13b: outer reflection scalar for Hermitianized compute

This is the filter forced by an outer success-projector reflection after a
Hermitian transfer extraction: if the extracted source scalar is `F`, the
reflection scalar is `2 * F^2 - 1`.  It is defined independently of any
circuit compression claim.  The zero branch is specified separately, as in
KernelReflection, because the strict-pair transfer construction has no zero-singular
frame.
-/

set_option autoImplicit false

namespace M13bHermitianReflectionScalar

open DalzellDilation

noncomputable section

def rho (params : KernelQSP.KernelGeneralParameters126) (sigma : ℝ) : ℝ :=
  if sigma = 0 then 1 else
    2 *
      (SpectralSamplingProof.Analytic.fixedPointChebyshevFailureResponse
        (KernelQSP.fixedPointParametersGeneral126 params)
        (max (KernelQSP.fixedPointParametersGeneral126 params).transitionWidth
          (sigma ^ 2))) ^ 2 - 1

theorem rho_zero (params : KernelQSP.KernelGeneralParameters126) :
    rho params 0 = 1 := by
  simp [rho]

theorem rho_gap
    (params : KernelQSP.KernelGeneralParameters126) {sigma : ℝ}
    (hsigma : params.gap ≤ sigma) (hsigma1 : sigma ≤ 1) :
    |rho params sigma + 1| ≤ 2 * params.targetError ^ 2 := by
  have hsigma_pos : 0 < sigma := lt_of_lt_of_le params.gap_pos hsigma
  rw [rho, if_neg (ne_of_gt hsigma_pos)]
  let q : ℝ := max
    (KernelQSP.fixedPointParametersGeneral126 params).transitionWidth (sigma ^ 2)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact le_trans (sq_nonneg sigma) (le_max_right _ _)
  have hsq1 : sigma ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg sigma]
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact max_le
      (le_of_lt (fixedPointTransitionWidth_lt_one130 params)) hsq1
  have hqtrans :
      (KernelQSP.fixedPointParametersGeneral126 params).transitionWidth ≤ q := by
    dsimp [q]
    exact le_max_left _ _
  let F : ℝ := SpectralSamplingProof.Analytic.fixedPointChebyshevFailureResponse
    (KernelQSP.fixedPointParametersGeneral126 params) q
  have hF : |F| ≤ params.targetError :=
    fixedPointFailureResponse_abs_le_target130 params hqtrans hq0 hq1
  have hF_sq : |F| ^ 2 ≤ params.targetError ^ 2 := by
    have hsub : 0 ≤ params.targetError - |F| := sub_nonneg.mpr hF
    have hadd : 0 ≤ params.targetError + |F| := by
      exact add_nonneg (le_of_lt params.targetError_pos) (abs_nonneg _)
    nlinarith [mul_nonneg hsub hadd]
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  calc
    |2 * F ^ 2 - 1 + 1| = 2 * |F| ^ 2 := by
      rw [show 2 * F ^ 2 - 1 + 1 = 2 * F ^ 2 by ring,
        abs_mul, abs_of_nonneg htwo, abs_sq, sq_abs]
    _ ≤ 2 * params.targetError ^ 2 :=
      mul_le_mul_of_nonneg_left hF_sq htwo

def rhoFromInput
    {d c r m R : Nat} (input : CertifiedM13Input d c r m R)
    (eta : ℝ) (heta_pos : 0 < eta) (heta_lt_two : eta < 2)
    (sigma : ℝ) : ℝ :=
  rho (kernelFilterParameters130 input eta heta_pos heta_lt_two) sigma

theorem rhoFromInput_zero
    {d c r m R : Nat} (input : CertifiedM13Input d c r m R)
    (eta : ℝ) (heta_pos : 0 < eta) (heta_lt_two : eta < 2) :
    rhoFromInput input eta heta_pos heta_lt_two 0 = 1 :=
  rho_zero _

theorem rhoFromInput_gap_quadratic
    {d c r m R : Nat} (input : CertifiedM13Input d c r m R)
    (eta : ℝ) (heta_pos : 0 < eta) (heta_lt_two : eta < 2)
    {sigma : ℝ} (hsigma : deltaKR130 input ≤ sigma) (hsigma1 : sigma ≤ 1) :
    |rhoFromInput input eta heta_pos heta_lt_two sigma + 1| ≤ eta ^ 2 / 2 := by
  have h := rho_gap (kernelFilterParameters130 input eta heta_pos heta_lt_two)
    hsigma hsigma1
  unfold rhoFromInput
  calc
    |rho (kernelFilterParameters130 input eta heta_pos heta_lt_two) sigma + 1| ≤
        2 * (eta / 2) ^ 2 := h
    _ = eta ^ 2 / 2 := by ring

theorem eta_sq_div_two_le_eta
    (eta : ℝ) (heta_pos : 0 < eta) (heta_lt_two : eta < 2) :
    eta ^ 2 / 2 ≤ eta := by
  nlinarith

theorem rhoFromInput_gap
    {d c r m R : Nat} (input : CertifiedM13Input d c r m R)
    (eta : ℝ) (heta_pos : 0 < eta) (heta_lt_two : eta < 2)
    {sigma : ℝ} (hsigma : deltaKR130 input ≤ sigma) (hsigma1 : sigma ≤ 1) :
    |rhoFromInput input eta heta_pos heta_lt_two sigma + 1| ≤ eta := by
  exact le_trans
    (rhoFromInput_gap_quadratic input eta heta_pos heta_lt_two hsigma hsigma1)
    (eta_sq_div_two_le_eta eta heta_pos heta_lt_two)

theorem gNu_rho_reflection_bound
    {d c r m R : Nat} (input : CertifiedM13Input d c r m R)
    (eta : ℝ) (heta_pos : 0 < eta) (heta_lt_two : eta < 2)
    (v : EuclideanSpace ℝ (GramOperator.ExtendedIndex d c R)) :
    ‖gramFilterAction130
        (GramOperator.gNuOperator input.base.system input.base.alpha input.base.nu)
        (rhoFromInput input eta heta_pos heta_lt_two) v -
      WithLp.toLp 2 ((GramOperator.idealKernelReflection input.base.system
        input.base.alpha input.base.nu input.base.hdet).mulVec v.ofLp)‖ ≤
      eta * ‖v‖ := by
  exact gNu_gram_filter_reflection_bound130 input
    (rhoFromInput input eta heta_pos heta_lt_two) eta
    (le_of_lt heta_pos)
    (rhoFromInput_zero input eta heta_pos heta_lt_two)
    (fun sigma hsigma hsigma1 =>
      rhoFromInput_gap input eta heta_pos heta_lt_two hsigma hsigma1)
    v

end

end M13bHermitianReflectionScalar
