import QLean.History.Integration.M13ScientificAdmissibility
import QLean.History.Integration.ConcreteHistoryInput.Concrete

open scoped BigOperators
noncomputable section

namespace DalzellDilation

open JenningsHistory
open GramOperator
open ConcreteHistoryInput
open TypedNegativeCases

/-! The input contract follows the certified normalization.  In
    particular, `base.alpha` is the history scale `alpha_H`; no separate free
    gain is introduced.  The fields below are certified properties of the
    problem instance, while all SVT conclusions remain theorems. -/
structure CertifiedM13Input (d c r m R : Nat) where
  base : M13Admissible d c r m R
  historyInverseNorm : ℝ
  historyInverseNorm_nonneg : 0 ≤ historyInverseNorm
  historyInverseBound : ∀ z : HistoryVector d c R,
    Real.sqrt (unitNormSquared
      ((scaledHistory base.system base.alpha)⁻¹.mulVec z)) ≤
      historyInverseNorm * Real.sqrt (unitNormSquared z)
  one_le_nu : 1 ≤ base.nu
  nu_le_xNorm : base.nu ≤
    Real.sqrt (unitNormSquared
      (m13XAlpha base.system base.alpha base.x))
  xNorm_le_historyInverseNorm :
    Real.sqrt (unitNormSquared
      (m13XAlpha base.system base.alpha base.x)) ≤ historyInverseNorm
  nu_le_historyInverseNorm : base.nu ≤ historyInverseNorm
  historyContraction : ∀ z : HistoryVector d c R,
    unitNormSquared ((scaledHistory base.system base.alpha).mulVec z) ≤
      unitNormSquared z
  kappaH : ℝ
  kappaH_pos : 0 < kappaH
  historyInverseNorm_le_kappaH : historyInverseNorm ≤ kappaH

def deltaKR130 {d c r m R : Nat} (I : CertifiedM13Input d c r m R) : ℝ :=
  I.kappaH⁻¹

theorem deltaKR130_pos {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) : 0 < deltaKR130 I := by
  exact inv_pos.mpr I.kappaH_pos

lemma scaledHistory_wellPosed130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) :
    wellPosed (scaledHistory I.base.system I.base.alpha) := by
  have hinj : Function.Injective
      (linearApply (scaledHistory I.base.system I.base.alpha)) := by
    intro u v huv
    have hEq :
        linearApply (dalzellExtendedH I.base.system I.base.alpha I.base.nu)
          (fun i : JenningsHistory.ExtendedIndex d c R =>
            match i with
            | Sum.inl row => u row
            | Sum.inr _ => 0) =
        linearApply (dalzellExtendedH I.base.system I.base.alpha I.base.nu)
          (fun i : JenningsHistory.ExtendedIndex d c R =>
            match i with
            | Sum.inl row => v row
            | Sum.inr _ => 0) := by
      funext i
      cases i with
      | inl row =>
          simpa [linearApply, Matrix.mulVec, dotProduct, dalzellExtendedH,
            Fintype.sum_sum_type] using congrFun huv row
      | inr _ =>
          simp [linearApply, Matrix.mulVec, dotProduct, dalzellExtendedH,
            Fintype.sum_sum_type]
    have hUV := I.base.hwell.1 hEq
    funext row
    exact congrFun hUV (Sum.inl row)
  have hfun :
      ⇑(Matrix.toLin' (R := ℝ)
        (scaledHistory I.base.system I.base.alpha)) =
        linearApply (scaledHistory I.base.system I.base.alpha) := by
    funext v
    simp [linearApply]
  have hinj' : Function.Injective
      (Matrix.toLin' (R := ℝ)
        (scaledHistory I.base.system I.base.alpha)) := by
    rw [hfun]
    exact hinj
  have hsurj' : Function.Surjective
      (Matrix.toLin' (R := ℝ)
        (scaledHistory I.base.system I.base.alpha)) :=
    (LinearMap.injective_iff_surjective).mp hinj'
  have hsurj : Function.Surjective
      (linearApply (scaledHistory I.base.system I.base.alpha)) := by
    rw [← hfun]
    exact hsurj'
  exact ⟨hinj, hsurj⟩

def extendedRightInverse130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R)
    (y : JenningsHistory.ExtendedVector d c R) : JenningsHistory.ExtendedVector d c R :=
  fun i =>
    match i with
    | Sum.inl row =>
        ((scaledHistory I.base.system I.base.alpha)⁻¹).mulVec
          (fun col => y (Sum.inl col)) row
    | Sum.inr _ => I.base.nu * y (Sum.inr ())

theorem extendedRightInverse130_spec {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R)
    (y : JenningsHistory.ExtendedVector d c R) :
    (dalzellExtendedH I.base.system I.base.alpha I.base.nu).mulVec
        (extendedRightInverse130 I y) = y := by
  have htop := scaledHistory_wellPosed130 I
  have htopdet : IsUnit (scaledHistory I.base.system I.base.alpha).det :=
    GramOperator.wellPosed_isUnit_det (scaledHistory I.base.system I.base.alpha) htop
  funext i
  cases i with
  | inl row =>
      have hmatrix :
          (scaledHistory I.base.system I.base.alpha).mulVec
              (((scaledHistory I.base.system I.base.alpha)⁻¹).mulVec
                (fun col => y (Sum.inl col))) =
            (fun col => y (Sum.inl col)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ htopdet]
        exact Matrix.one_mulVec _
      simpa [extendedRightInverse130, dalzellExtendedH, Matrix.mulVec,
        dotProduct, Fintype.sum_sum_type] using congrFun hmatrix row
  | inr _ =>
      have hscalar : I.base.nu⁻¹ * (I.base.nu * y (Sum.inr ())) =
          y (Sum.inr ()) := by
        field_simp [I.base.hν]
      simpa [extendedRightInverse130, dalzellExtendedH, Matrix.mulVec,
        dotProduct, Fintype.sum_sum_type] using hscalar

lemma unitNormSquared_nonneg130 {ι : Type*} [Fintype ι]
    (v : ι → ℝ) : 0 ≤ unitNormSquared v := by
  unfold unitNormSquared
  exact Finset.sum_nonneg (fun i hi => mul_self_nonneg (v i))

lemma historyInverseBound_sq130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R)
    (z : HistoryVector d c R) :
    unitNormSquared
        ((scaledHistory I.base.system I.base.alpha)⁻¹.mulVec z) ≤
      I.historyInverseNorm ^ 2 * unitNormSquared z := by
  have hz : 0 ≤ unitNormSquared z := unitNormSquared_nonneg130 z
  have hi : 0 ≤ unitNormSquared
      ((scaledHistory I.base.system I.base.alpha)⁻¹.mulVec z) :=
    unitNormSquared_nonneg130 _
  have hs1 := Real.sq_sqrt hi
  have hs2 := Real.sq_sqrt hz
  have hbound := I.historyInverseBound z
  have hleft : 0 ≤ Real.sqrt (unitNormSquared
      ((scaledHistory I.base.system I.base.alpha)⁻¹.mulVec z)) :=
    Real.sqrt_nonneg _
  have hright : 0 ≤ I.historyInverseNorm * Real.sqrt (unitNormSquared z) :=
    mul_nonneg I.historyInverseNorm_nonneg (Real.sqrt_nonneg _)
  have hsq :
      (Real.sqrt (unitNormSquared
        ((scaledHistory I.base.system I.base.alpha)⁻¹.mulVec z))) ^ 2 ≤
        (I.historyInverseNorm * Real.sqrt (unitNormSquared z)) ^ 2 := by
    nlinarith
  calc
    unitNormSquared
        ((scaledHistory I.base.system I.base.alpha)⁻¹.mulVec z) =
        (Real.sqrt (unitNormSquared
          ((scaledHistory I.base.system I.base.alpha)⁻¹.mulVec z))) ^ 2 :=
      hs1.symm
    _ ≤ (I.historyInverseNorm * Real.sqrt (unitNormSquared z)) ^ 2 := hsq
    _ = I.historyInverseNorm ^ 2 * unitNormSquared z := by
      rw [mul_pow, hs2]

theorem extendedRightInverse130_normSq_le {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R)
    (y : JenningsHistory.ExtendedVector d c R) :
    unitNormSquared (extendedRightInverse130 I y) ≤
      I.kappaH ^ 2 * unitNormSquared y := by
  have hhist := historyInverseBound_sq130 I
    (fun row => y (Sum.inl row))
  have hnormsq : I.historyInverseNorm ^ 2 ≤ I.kappaH ^ 2 := by
    nlinarith [I.historyInverseNorm_nonneg,
      I.historyInverseNorm_le_kappaH]
  have htopnonneg : 0 ≤ unitNormSquared
      (fun row => y (Sum.inl row)) := unitNormSquared_nonneg130 _
  have htop :
      unitNormSquared
        ((scaledHistory I.base.system I.base.alpha)⁻¹.mulVec
          (fun row => y (Sum.inl row))) ≤
        I.kappaH ^ 2 * unitNormSquared
          (fun row => y (Sum.inl row)) := by
    exact le_trans hhist
      (mul_le_mul_of_nonneg_right hnormsq htopnonneg)
  have hnu_sq : I.base.nu ^ 2 ≤ I.kappaH ^ 2 := by
    have hnuκ : I.base.nu ≤ I.kappaH :=
      le_trans I.nu_le_historyInverseNorm
        I.historyInverseNorm_le_kappaH
    nlinarith [I.base.hνpos.le, I.kappaH_pos]
  have hybot : 0 ≤ (y (Sum.inr ())) ^ 2 := sq_nonneg _
  have hbot :
      (I.base.nu * y (Sum.inr ())) *
          (I.base.nu * y (Sum.inr ())) ≤
        I.kappaH ^ 2 * (y (Sum.inr ())) * (y (Sum.inr ())) := by
    have hmul := mul_le_mul_of_nonneg_right hnu_sq hybot
    nlinarith
  calc
    unitNormSquared (extendedRightInverse130 I y) =
        unitNormSquared
          ((scaledHistory I.base.system I.base.alpha)⁻¹.mulVec
            (fun row => y (Sum.inl row))) +
          (I.base.nu * y (Sum.inr ())) *
            (I.base.nu * y (Sum.inr ())) := by
      simp [unitNormSquared, extendedRightInverse130,
        Fintype.sum_sum_type]
    _ ≤ I.kappaH ^ 2 * unitNormSquared
          (fun row => y (Sum.inl row)) +
          I.kappaH ^ 2 * (y (Sum.inr ())) * (y (Sum.inr ())) :=
      add_le_add htop hbot
    _ = I.kappaH ^ 2 * unitNormSquared y := by
      simp [unitNormSquared, Fintype.sum_sum_type]
      ring

def rawNorm130 {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (unitNormSquared v)

def bPlusOrthogonal130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R)
    (y : JenningsHistory.ExtendedVector d c R) : Prop :=
  ∑ i, dalzellBPlus I.base.system i * y i = 0

lemma qBPlus_apply_of_orthogonal130 {ι : Type*} [Fintype ι]
    (b y : ι → ℝ) (horth : (∑ i, b i * y i) = 0) :
    qBPlusApply b y = y := by
  rw [qBPlus_apply_formula]
  simp [horth]

lemma qBPlus_output_orthogonal130 {ι : Type*} [Fintype ι]
    (b z : ι → ℝ) (hb : unitNorm b) :
    ∑ i, b i * qBPlusApply b z i = 0 := by
  rw [qBPlus_apply_formula]
  let t : ℝ := ∑ j, b j * z j
  have hb' : (∑ j, b j * b j) = 1 := by
    simpa [unitNorm, unitNormSquared] using hb
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, b i * (z i - t * b i)) =
        ∑ i, (b i * z i - b i * (t * b i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, b i * z i) - t * (∑ i, b i * b i) := by
      rw [Finset.sum_sub_distrib]
      have hsecond :
          (∑ i, b i * (t * b i)) = t * (∑ i, b i * b i) := by
        calc
          (∑ i, b i * (t * b i)) =
              ∑ i, t * (b i * b i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = t * (∑ i, b i * b i) := by
            rw [Finset.mul_sum]
      rw [hsecond]
    _ = 0 := by
      rw [hb']
      dsimp [t]
      ring

def KernelOrthogonal130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R)
    (v : JenningsHistory.ExtendedVector d c R) : Prop :=
  ∀ k : JenningsHistory.ExtendedVector d c R,
    (gNuOperator I.base.system I.base.alpha I.base.nu).mulVec k = 0 →
      ∑ i, v i * k i = 0

def RightSingularLowerGap130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) (delta : ℝ) : Prop :=
  ∀ v : JenningsHistory.ExtendedVector d c R,
    KernelOrthogonal130 I v →
      delta * rawNorm130 v ≤
        rawNorm130 ((gNuOperator I.base.system I.base.alpha I.base.nu).mulVec v)

lemma unitNormSquared_add_orthogonal130 {ι : Type*} [Fintype ι]
    (v k : ι → ℝ) (h : ∑ i, v i * k i = 0) :
    unitNormSquared (v + k) =
      unitNormSquared v + unitNormSquared k := by
  simp only [unitNormSquared, Pi.add_apply]
  calc
    (∑ i, (v i + k i) * (v i + k i)) =
        ∑ i, (v i * v i + 2 * (v i * k i) + k i * k i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, v i * v i) + 2 * (∑ i, v i * k i) +
          ∑ i, k i * k i := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
    _ = unitNormSquared v + unitNormSquared k := by
      rw [h]
      simp [unitNormSquared]

def RightSingularGap130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) (delta : ℝ) : Prop :=
  ∀ y : JenningsHistory.ExtendedVector d c R,
    bPlusOrthogonal130 I y →
      ∃ v : JenningsHistory.ExtendedVector d c R,
        (gNuOperator I.base.system I.base.alpha I.base.nu).mulVec v = y ∧
        rawNorm130 v ≤ delta⁻¹ * rawNorm130 y

theorem rightSingularGap130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) :
    RightSingularGap130 I (deltaKR130 I) := by
  intro y horth
  refine ⟨extendedRightInverse130 I y, ?_, ?_⟩
  · have hright := extendedRightInverse130_spec I y
    have hq := qBPlus_apply_of_orthogonal130
      (dalzellBPlus I.base.system) y horth
    change (qBPlusMatrix (dalzellBPlus I.base.system) *
      dalzellExtendedH I.base.system I.base.alpha I.base.nu).mulVec
        (extendedRightInverse130 I y) = y
    rw [← Matrix.mulVec_mulVec]
    change qBPlusApply (dalzellBPlus I.base.system)
      ((dalzellExtendedH I.base.system I.base.alpha I.base.nu).mulVec
        (extendedRightInverse130 I y)) = y
    rw [hright]
    exact hq
  · have hsq := extendedRightInverse130_normSq_le I y
    have hy : 0 ≤ unitNormSquared y := unitNormSquared_nonneg130 y
    have hv : 0 ≤ unitNormSquared (extendedRightInverse130 I y) :=
      unitNormSquared_nonneg130 _
    have hκ : 0 ≤ I.kappaH := I.kappaH_pos.le
    have hsqrtv := Real.sq_sqrt hv
    have hsqrty := Real.sq_sqrt hy
    have hroot :
        Real.sqrt (unitNormSquared (extendedRightInverse130 I y)) ≤
          I.kappaH * Real.sqrt (unitNormSquared y) := by
      have hright : 0 ≤ I.kappaH * Real.sqrt (unitNormSquared y) :=
        mul_nonneg hκ (Real.sqrt_nonneg _)
      have hsqroot :
          (I.kappaH * Real.sqrt (unitNormSquared y)) ^ 2 =
            I.kappaH ^ 2 * unitNormSquared y := by
        rw [mul_pow, hsqrty]
      nlinarith
    have hdelta : (deltaKR130 I)⁻¹ = I.kappaH := by
      dsimp [deltaKR130]
      field_simp
    simpa [rawNorm130, hdelta] using hroot

theorem rightSingularLowerGap130 {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) :
    RightSingularLowerGap130 I (deltaKR130 I) := by
  intro v hv
  let y : JenningsHistory.ExtendedVector d c R :=
    (gNuOperator I.base.system I.base.alpha I.base.nu).mulVec v
  have horthB : bPlusOrthogonal130 I y := by
    change ∑ i, dalzellBPlus I.base.system i *
      ((gNuOperator I.base.system I.base.alpha I.base.nu).mulVec v) i = 0
    rw [show gNuOperator I.base.system I.base.alpha I.base.nu =
      qBPlusMatrix (dalzellBPlus I.base.system) *
        dalzellExtendedH I.base.system I.base.alpha I.base.nu by rfl]
    rw [← Matrix.mulVec_mulVec]
    change ∑ i, dalzellBPlus I.base.system i *
      qBPlusApply (dalzellBPlus I.base.system)
        ((dalzellExtendedH I.base.system I.base.alpha I.base.nu).mulVec v) i = 0
    exact qBPlus_output_orthogonal130 _ _ I.base.hb
  obtain ⟨w, hw, hwbound⟩ := rightSingularGap130 I y horthB
  have hkernel :
      (gNuOperator I.base.system I.base.alpha I.base.nu).mulVec (w - v) = 0 := by
    rw [Matrix.mulVec_sub, hw]
    exact sub_self _
  have horth : ∑ i, v i * (w - v) i = 0 := hv (w - v) hkernel
  have hsum : unitNormSquared w =
      unitNormSquared v + unitNormSquared (w - v) := by
    have hrewrite : w = v + (w - v) := by abel
    calc
      unitNormSquared w = unitNormSquared (v + (w - v)) :=
        congrArg unitNormSquared hrewrite
      _ = unitNormSquared v + unitNormSquared (w - v) :=
        unitNormSquared_add_orthogonal130 v (w - v) horth
  have hnorm_v_le_w : rawNorm130 v ≤ rawNorm130 w := by
    have hdiffnonneg : 0 ≤ unitNormSquared (w - v) :=
      unitNormSquared_nonneg130 _
    have hsq : unitNormSquared v ≤ unitNormSquared w := by
      nlinarith [hsum]
    simpa [rawNorm130] using (Real.sqrt_le_sqrt hsq)
  have hδ := deltaKR130_pos I
  have hscaled := mul_le_mul_of_nonneg_left
    (le_trans hnorm_v_le_w hwbound) hδ.le
  have hδne : deltaKR130 I ≠ 0 := ne_of_gt hδ
  calc
    deltaKR130 I * rawNorm130 v ≤
        deltaKR130 I * ((deltaKR130 I)⁻¹ * rawNorm130 y) := hscaled
    _ = rawNorm130 y := by
      rw [← mul_assoc, mul_inv_cancel₀ hδne, one_mul]
    _ = rawNorm130
        ((gNuOperator I.base.system I.base.alpha I.base.nu).mulVec v) := by
      rfl

lemma qBPlus_normSq_le {ι : Type*} [Fintype ι]
    (b z : ι → ℝ) (hb : unitNorm b) :
    unitNormSquared (qBPlusApply b z) ≤ unitNormSquared z := by
  rw [qBPlus_apply_formula]
  let t : ℝ := ∑ j, b j * z j
  have hb' : (∑ j, b j * b j) = 1 := by
    simpa [unitNorm, unitNormSquared] using hb
  have hcross : (∑ i, z i * b i) = t := by
    dsimp [t]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsq :
      unitNormSquared (z - t • b) =
        unitNormSquared z - t ^ 2 := by
    simp only [unitNormSquared, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, (z i - t * b i) * (z i - t * b i)) =
          ∑ i, (z i * z i - 2 * t * (z i * b i) +
            t ^ 2 * (b i * b i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = unitNormSquared z - 2 * t * (∑ i, z i * b i) +
            t ^ 2 * (∑ i, b i * b i) := by
        simp only [unitNormSquared]
        calc
          (∑ i, (z i * z i - 2 * t * (z i * b i) +
            t ^ 2 * (b i * b i))) =
              (∑ i, (z i * z i - 2 * t * (z i * b i))) +
                ∑ i, t ^ 2 * (b i * b i) := by
            rw [Finset.sum_add_distrib]
          _ = ((∑ i, z i * z i) -
                ∑ i, 2 * t * (z i * b i)) +
                ∑ i, t ^ 2 * (b i * b i) := by
            congr 1
            rw [Finset.sum_sub_distrib]
          _ = (∑ i, z i * z i) -
                2 * t * (∑ i, z i * b i) +
                t ^ 2 * (∑ i, b i * b i) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = unitNormSquared z - t ^ 2 := by
        rw [hcross, hb']
        dsimp [t]
        ring
  rw [hsq]
  nlinarith [sq_nonneg t]

lemma dalzellExtendedH_normSq_le {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha nu : ℝ)
    (hnu : 1 ≤ nu)
    (hcontract : ∀ z : HistoryVector d c R,
      unitNormSquared ((scaledHistory system alpha).mulVec z) ≤
        unitNormSquared z)
    (z : JenningsHistory.ExtendedVector d c R) :
    unitNormSquared ((dalzellExtendedH system alpha nu).mulVec z) ≤
      unitNormSquared z := by
  have hnu_pos : 0 < nu := lt_of_lt_of_le (by norm_num) hnu
  have hnu_inv_sq : (nu⁻¹) ^ 2 ≤ 1 := by
    have hi : 0 ≤ nu⁻¹ := le_of_lt (inv_pos.mpr hnu_pos)
    have hmul : nu⁻¹ ≤ (1 : ℝ) := by
      exact (inv_le_one₀ hnu_pos).mpr hnu
    nlinarith
  have htop := hcontract (fun row => z (Sum.inl row))
  unfold unitNormSquared at htop ⊢
  simp [dalzellExtendedH, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type] at htop ⊢
  have hbottom : (nu⁻¹ * z (Sum.inr ())) * (nu⁻¹ * z (Sum.inr ())) ≤
      z (Sum.inr ()) * z (Sum.inr ()) := by
    nlinarith [sq_nonneg (z (Sum.inr ())), hnu_inv_sq]
  nlinarith [htop, hbottom]

theorem gNu_normSq_le_one {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) (z : JenningsHistory.ExtendedVector d c R) :
      unitNormSquared ((gNuOperator I.base.system I.base.alpha I.base.nu).mulVec z) ≤
      unitNormSquared z := by
  have hH := dalzellExtendedH_normSq_le I.base.system I.base.alpha I.base.nu
    I.one_le_nu I.historyContraction z
  have hQ := qBPlus_normSq_le (dalzellBPlus I.base.system)
    ((dalzellExtendedH I.base.system I.base.alpha I.base.nu).mulVec z)
    I.base.hb
  change unitNormSquared
      ((qBPlusMatrix (dalzellBPlus I.base.system) *
        dalzellExtendedH I.base.system I.base.alpha I.base.nu).mulVec z) ≤
      unitNormSquared z
  simpa [Matrix.mulVec_mulVec, qBPlusApply] using le_trans hQ hH

def RawOperatorNormBound130 {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (eta : ℝ) : Prop :=
  ∀ z, rawNorm130 (M.mulVec z) ≤ eta * rawNorm130 z

theorem gNu_norm_le_one {d c r m R : Nat}
    (I : CertifiedM13Input d c r m R) :
    RawOperatorNormBound130
      (gNuOperator I.base.system I.base.alpha I.base.nu) 1 := by
  intro z
  have hsq := gNu_normSq_le_one I z
  have hz : 0 ≤ unitNormSquared z := unitNormSquared_nonneg130 z
  have hv : 0 ≤ unitNormSquared
      ((gNuOperator I.base.system I.base.alpha I.base.nu).mulVec z) :=
    unitNormSquared_nonneg130 _
  have hs_v := Real.sq_sqrt hv
  have hs_z := Real.sq_sqrt hz
  have hroot :
      Real.sqrt (unitNormSquared
        ((gNuOperator I.base.system I.base.alpha I.base.nu).mulVec z)) ≤
        Real.sqrt (unitNormSquared z) := by
    nlinarith [Real.sqrt_nonneg
      (unitNormSquared ((gNuOperator I.base.system I.base.alpha I.base.nu).mulVec z)),
      Real.sqrt_nonneg (unitNormSquared z)]
  simpa [rawNorm130] using hroot

end DalzellDilation
