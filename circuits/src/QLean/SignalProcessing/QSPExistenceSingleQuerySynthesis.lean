import QLean.SignalProcessing.QSPExistenceSingleQueryPhaseExtraction

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

def standardStarPolynomial034 (p : Polynomial ℂ) : Polynomial ℂ :=
  p.map (starRingEnd ℂ)

theorem standardStarPolynomial034_coeff
    (p : Polynomial ℂ) (n : ℕ) :
    (standardStarPolynomial034 p).coeff n = star (p.coeff n) := by
  simp [standardStarPolynomial034, Polynomial.coeff_map]

theorem coeff_mul_at_sum_of_degree_le034
    (p q : Polynomial ℂ) (d : ℕ)
    (hp : p.degree ≤ (d : WithBot ℕ))
    (hq : q.degree ≤ (d : WithBot ℕ)) :
    (p * q).coeff (d + d) = p.coeff d * q.coeff d := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_single (d, d)
  · intro b hb hne
    have hsum : b.1 + b.2 = d + d :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    by_cases hfirst : b.1 ≤ d
    · have hsecond : d ≤ b.2 := by omega
      by_cases heq : b.1 = d
      · have : b.2 = d := by omega
        exact (hne (Prod.ext heq this)).elim
      · have hlt : b.1 < d := by omega
        have hgt : d < b.2 := by omega
        have hzero : q.coeff b.2 = 0 := by
          apply Polynomial.coeff_eq_zero_of_degree_lt
          exact lt_of_le_of_lt hq (WithBot.coe_lt_coe.mpr hgt)
        simp [hzero]
    · have hgt : d < b.1 := by omega
      have hzero : p.coeff b.1 = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        exact lt_of_le_of_lt hp (WithBot.coe_lt_coe.mpr hgt)
      simp [hzero]
  · intro hnot
    have hmem : (d, d) ∈ Finset.HasAntidiagonal.antidiagonal (d + d) := by
      apply Finset.HasAntidiagonal.mem_antidiagonal.mpr
      omega
    exact (hnot hmem).elim

theorem standardStarPolynomial034_degree
    (p : Polynomial ℂ) (d : ℕ)
    (hp : p.degree ≤ (d : WithBot ℕ)) :
    (standardStarPolynomial034 p).degree ≤ (d : WithBot ℕ) := by
  rw [standardStarPolynomial034]
  rw [Polynomial.degree_map_eq_of_injective (starRingEnd ℂ).injective]
  exact hp

theorem standardStarPolynomial034_top_coeff_product
    (p : Polynomial ℂ) (d : ℕ)
    (hp : p.degree ≤ (d : WithBot ℕ)) :
    (p * standardStarPolynomial034 p).coeff (d + d) =
      p.coeff d * star (p.coeff d) := by
  rw [coeff_mul_at_sum_of_degree_le034 p (standardStarPolynomial034 p) d hp
    (standardStarPolynomial034_degree p d hp)]
  rw [standardStarPolynomial034_coeff]

def standardParaunitary034 (state : StandardQSPPolynomialState032) : Prop :=
  state.sourceFactor * standardStarPolynomial034 state.sourceFactor +
      standardGoodSquare032 * state.targetFactor *
        standardStarPolynomial034 state.targetFactor = 1

structure StandardAdmissibility034 where
  state : StandardQSPPolynomialState032
  degree : ℕ
  source_degree : state.sourceFactor.degree ≤ (degree : WithBot ℕ)
  target_degree : state.targetFactor.degree ≤ (degree : WithBot ℕ)
  source_parity :
    state.sourceFactor.comp (-(Polynomial.X : Polynomial ℂ)) =
      if degree % 2 = 0 then state.sourceFactor else -state.sourceFactor
  target_parity :
    state.targetFactor.comp (-(Polynomial.X : Polynomial ℂ)) =
      if degree % 2 = 0 then -state.targetFactor else state.targetFactor
  paraunitary : standardParaunitary034 state
  weighted_energy : ∀ x : ℝ, standardWeightedEnergy032 x state = 1
  realReadout : ℝ → ℝ
  real_readout : ∀ x : ℝ,
    (Polynomial.eval (x : ℂ) state.sourceFactor).re = realReadout x

theorem standardStarPolynomial034_completion_source
    (input : GeneralRealQSPPolynomial127) :
    standardStarPolynomial034 (completionStandardState033 input).sourceFactor =
      (completionPair024 input).P.map Complex.ofRealHom -
        Polynomial.C Complex.I *
          (completionPair024 input).B.map Complex.ofRealHom := by
  change
    Polynomial.map (starRingEnd ℂ)
        ((completionPair024 input).P.map Complex.ofRealHom +
          Polynomial.C Complex.I *
            (completionPair024 input).B.map Complex.ofRealHom) =
      (completionPair024 input).P.map Complex.ofRealHom -
        Polynomial.C Complex.I *
          (completionPair024 input).B.map Complex.ofRealHom
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  congr 1
  · ext n
    simp [Polynomial.coeff_map]
  · ext n
    simp [Polynomial.coeff_map]

theorem standardStarPolynomial034_completion_target
    (input : GeneralRealQSPPolynomial127) :
    standardStarPolynomial034 (completionStandardState033 input).targetFactor =
      (completionPair024 input).C.map Complex.ofRealHom := by
  change
    ((completionPair024 input).C.map Complex.ofRealHom).map (starRingEnd ℂ) =
      (completionPair024 input).C.map Complex.ofRealHom
  ext n
  simp [Polynomial.coeff_map]

theorem completionStandardState034_paraunitary
    (input : GeneralRealQSPPolynomial127) :
    standardParaunitary034 (completionStandardState033 input) := by
  have h := congrArg (fun p : Polynomial ℝ => p.map Complex.ofRealHom)
    (completionPair024 input).identity
  unfold standardParaunitary034
  rw [standardStarPolynomial034_completion_source,
    standardStarPolynomial034_completion_target]
  change
    ((completionPair024 input).P.map Complex.ofRealHom +
        Polynomial.C Complex.I *
          (completionPair024 input).B.map Complex.ofRealHom) *
        ((completionPair024 input).P.map Complex.ofRealHom -
          Polynomial.C Complex.I *
            (completionPair024 input).B.map Complex.ofRealHom) +
      standardGoodSquare032 *
        (completionPair024 input).C.map Complex.ofRealHom *
        (completionPair024 input).C.map Complex.ofRealHom = 1
  have h' :
      ((completionPair024 input).P.map Complex.ofRealHom) ^ 2 +
          ((completionPair024 input).B.map Complex.ofRealHom) ^ 2 +
        (1 - (Polynomial.X : Polynomial ℂ) ^ 2) *
          ((completionPair024 input).C.map Complex.ofRealHom) ^ 2 = 1 := by
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X] using h
  have hI : (Polynomial.C Complex.I : Polynomial ℂ) ^ 2 = -1 := by
    rw [← Polynomial.C_pow]
    simp
  calc
    _ = ((completionPair024 input).P.map Complex.ofRealHom) ^ 2 +
          ((completionPair024 input).B.map Complex.ofRealHom) ^ 2 +
        (1 - (Polynomial.X : Polynomial ℂ) ^ 2) *
          ((completionPair024 input).C.map Complex.ofRealHom) ^ 2 := by
      have hprod (A B : Polynomial ℂ) :
          (A + Polynomial.C Complex.I * B) *
              (A - Polynomial.C Complex.I * B) = A ^ 2 + B ^ 2 := by
        calc
          _ = A ^ 2 - (Polynomial.C Complex.I * B) ^ 2 := by ring
          _ = A ^ 2 + B ^ 2 := by
            rw [mul_pow, hI]
            ring
      rw [hprod]
      simp only [standardGoodSquare032]
      ring
    _ = 1 := h'

theorem standardParaunitary034_top_norm_relation
    (state : StandardQSPPolynomialState032) (d : ℕ)
    (hd : 0 < d)
    (hsdeg : state.sourceFactor.degree ≤ (d : WithBot ℕ))
    (htdeg : state.targetFactor.degree < (d : WithBot ℕ))
    (hpara : standardParaunitary034 state) :
    Complex.normSq (state.sourceFactor.coeff d) =
      Complex.normSq (state.targetFactor.coeff (d - 1)) := by
  let S : Polynomial ℂ := state.sourceFactor
  let T : Polynomial ℂ := state.targetFactor
  let Sstar : Polynomial ℂ := standardStarPolynomial034 S
  let Tstar : Polynomial ℂ := standardStarPolynomial034 T
  have hTpred : T.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) :=
    degree_le_pred_of_degree_lt033 T d hd htdeg
  have hTstar : Tstar.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
    exact standardStarPolynomial034_degree T (d - 1) hTpred
  have hUdeg : (T * Tstar).degree < ((d + d : ℕ) : WithBot ℕ) := by
    calc
      (T * Tstar).degree ≤ T.degree + Tstar.degree :=
        Polynomial.degree_mul_le _ _
      _ ≤ ((d - 1 : ℕ) : WithBot ℕ) +
          ((d - 1 : ℕ) : WithBot ℕ) := add_le_add hTpred hTstar
      _ < ((d + d : ℕ) : WithBot ℕ) := by
        exact_mod_cast (by omega : (d - 1) + (d - 1) < d + d)
  have hUzero : (T * Tstar).coeff (d + d) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt hUdeg
  have hUshift :
      (Polynomial.X ^ 2 * (T * Tstar)).coeff (d + d) =
        T.coeff (d - 1) * star (T.coeff (d - 1)) := by
    rw [show d + d = (d - 1) + (d - 1) + 2 by omega,
      Polynomial.coeff_X_pow_mul]
    exact standardStarPolynomial034_top_coeff_product T (d - 1) hTpred
  have hSprod :
      (S * Sstar).coeff (d + d) =
        S.coeff d * star (S.coeff d) :=
    standardStarPolynomial034_top_coeff_product S d hsdeg
  have hpara' :
      S * Sstar + (T * Tstar -
        (Polynomial.X : Polynomial ℂ) ^ 2 * (T * Tstar)) = 1 := by
    have h := hpara
    change S * Sstar +
        (1 - (Polynomial.X : Polynomial ℂ) ^ 2) * T * Tstar = 1 at h
    calc
      S * Sstar + (T * Tstar -
          (Polynomial.X : Polynomial ℂ) ^ 2 * (T * Tstar)) =
          S * Sstar +
            (1 - (Polynomial.X : Polynomial ℂ) ^ 2) * T * Tstar := by ring
      _ = 1 := h
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff (d + d)) hpara'
  rw [Polynomial.coeff_add, Polynomial.coeff_sub, hSprod, hUzero,
    hUshift, Polynomial.coeff_one] at hc
  simp [Nat.ne_of_gt hd] at hc
  have hc' :
      S.coeff d * star (S.coeff d) =
        T.coeff (d - 1) * star (T.coeff (d - 1)) := by
    linear_combination hc
  have hcre := congrArg Complex.re hc'
  simpa [S, T, Complex.normSq_apply, Complex.mul_re] using hcre

theorem standardStarPolynomial034_mul
    (p q : Polynomial ℂ) :
    standardStarPolynomial034 (p * q) =
      standardStarPolynomial034 p * standardStarPolynomial034 q := by
  simp [standardStarPolynomial034, Polynomial.map_mul]

theorem standardStarPolynomial034_add
    (p q : Polynomial ℂ) :
    standardStarPolynomial034 (p + q) =
      standardStarPolynomial034 p + standardStarPolynomial034 q := by
  simp [standardStarPolynomial034, Polynomial.map_add]

theorem standardStarPolynomial034_neg
    (p : Polynomial ℂ) :
    standardStarPolynomial034 (-p) =
      -standardStarPolynomial034 p := by
  simp [standardStarPolynomial034]

theorem standardStarPolynomial034_X :
    standardStarPolynomial034 (Polynomial.X : Polynomial ℂ) = Polynomial.X := by
  simp [standardStarPolynomial034]

theorem standardStarPolynomial034_good :
    standardStarPolynomial034 standardGoodSquare032 =
      standardGoodSquare032 := by
  ext n
  simp [standardStarPolynomial034, standardGoodSquare032]

theorem standardStarPolynomial034_C (phase : ℂ) :
    standardStarPolynomial034 (Polynomial.C phase) =
      Polynomial.C (star phase) := by
  ext n
  simp [standardStarPolynomial034]

theorem standardUnitPhase034_mul_star
    (phase : ℂ) (hunit : standardUnitPhase032 phase) :
    phase * star phase = 1 := by
  have hnorm : Complex.normSq phase = 1 := hunit
  change phase * (starRingEnd ℂ) phase = 1
  rw [Complex.mul_conj]
  simp [hnorm]

theorem standardParaunitary034_sourcePhase
    (state : StandardQSPPolynomialState032) (phase : ℂ)
    (hunit : standardUnitPhase032 phase)
    (hpara : standardParaunitary034 state) :
    standardParaunitary034
      (standardSourcePhase032 phase state) := by
  have hmul := standardUnitPhase034_mul_star phase hunit
  unfold standardParaunitary034 standardSourcePhase032 at *
  rw [standardStarPolynomial034_mul, standardStarPolynomial034_C]
  have hpoly : Polynomial.C phase * Polynomial.C (star phase) =
      (1 : Polynomial ℂ) := by
    rw [← Polynomial.C_mul, hmul, Polynomial.C_1]
  calc
    Polynomial.C phase * state.sourceFactor *
          (Polynomial.C (star phase) *
            standardStarPolynomial034 state.sourceFactor) +
        standardGoodSquare032 * state.targetFactor *
          standardStarPolynomial034 state.targetFactor =
        (Polynomial.C phase * Polynomial.C (star phase)) *
            (state.sourceFactor * standardStarPolynomial034 state.sourceFactor) +
          standardGoodSquare032 * state.targetFactor *
            standardStarPolynomial034 state.targetFactor := by ring
    _ = state.sourceFactor * standardStarPolynomial034 state.sourceFactor +
          standardGoodSquare032 * state.targetFactor *
            standardStarPolynomial034 state.targetFactor := by
      rw [hpoly]
      simp
    _ = 1 := hpara

theorem standardParaunitary034_signalAdjoint
    (state : StandardQSPPolynomialState032)
    (hpara : standardParaunitary034 state) :
    standardParaunitary034 (standardSignalAdjoint032 state) := by
  have hX := standardStarPolynomial034_X
  have hG := standardStarPolynomial034_good
  unfold standardParaunitary034
  change
    (Polynomial.X * state.sourceFactor + standardGoodSquare032 * state.targetFactor) *
          standardStarPolynomial034
            (Polynomial.X * state.sourceFactor + standardGoodSquare032 * state.targetFactor) +
        standardGoodSquare032 * (-state.sourceFactor + Polynomial.X * state.targetFactor) *
          standardStarPolynomial034
            (-state.sourceFactor + Polynomial.X * state.targetFactor) = 1
  have hsourceStar :
      standardStarPolynomial034
          (Polynomial.X * state.sourceFactor + standardGoodSquare032 * state.targetFactor) =
        Polynomial.X * standardStarPolynomial034 state.sourceFactor +
          standardGoodSquare032 * standardStarPolynomial034 state.targetFactor := by
    rw [standardStarPolynomial034_add, standardStarPolynomial034_mul,
      standardStarPolynomial034_mul, hX, hG]
  have htargetStar :
      standardStarPolynomial034
          (-state.sourceFactor + Polynomial.X * state.targetFactor) =
        -standardStarPolynomial034 state.sourceFactor +
          Polynomial.X * standardStarPolynomial034 state.targetFactor := by
    rw [standardStarPolynomial034_add, standardStarPolynomial034_neg,
      standardStarPolynomial034_mul, hX]
  rw [hsourceStar, htargetStar]
  have hpara' := hpara
  change state.sourceFactor * standardStarPolynomial034 state.sourceFactor +
      (1 - (Polynomial.X : Polynomial ℂ) ^ 2) * state.targetFactor *
        standardStarPolynomial034 state.targetFactor = 1 at hpara'
  calc
    (Polynomial.X * state.sourceFactor + standardGoodSquare032 * state.targetFactor) *
          (Polynomial.X * standardStarPolynomial034 state.sourceFactor +
            standardGoodSquare032 * standardStarPolynomial034 state.targetFactor) +
        standardGoodSquare032 * (-state.sourceFactor + Polynomial.X * state.targetFactor) *
          (-standardStarPolynomial034 state.sourceFactor +
            Polynomial.X * standardStarPolynomial034 state.targetFactor) =
        state.sourceFactor * standardStarPolynomial034 state.sourceFactor +
          (1 - (Polynomial.X : Polynomial ℂ) ^ 2) * state.targetFactor *
            standardStarPolynomial034 state.targetFactor := by
      simp only [standardGoodSquare032]
      ring
    _ = 1 := hpara'

def standardTopUnitPhase034
    (state : StandardQSPPolynomialState032) (d : ℕ) : ℂ :=
  if state.sourceFactor.coeff d = 0 then 1
  else state.targetFactor.coeff (d - 1) /
    state.sourceFactor.coeff d

theorem standardTopUnitPhase034_target_zero
    (state : StandardQSPPolynomialState032) (d : ℕ)
    (hrel : Complex.normSq (state.sourceFactor.coeff d) =
      Complex.normSq (state.targetFactor.coeff (d - 1)))
    (hs : state.sourceFactor.coeff d = 0) :
    state.targetFactor.coeff (d - 1) = 0 := by
  have hzero : Complex.normSq (state.targetFactor.coeff (d - 1)) = 0 := by
    rw [← hrel, hs, Complex.normSq_zero]
  exact Complex.normSq_eq_zero.mp hzero

theorem standardTopUnitPhase034_mul_source
    (state : StandardQSPPolynomialState032) (d : ℕ)
    (hrel : Complex.normSq (state.sourceFactor.coeff d) =
      Complex.normSq (state.targetFactor.coeff (d - 1))) :
    standardTopUnitPhase034 state d * state.sourceFactor.coeff d =
      state.targetFactor.coeff (d - 1) := by
  by_cases hs : state.sourceFactor.coeff d = 0
  · have ht := standardTopUnitPhase034_target_zero state d hrel hs
    simp [standardTopUnitPhase034, hs, ht]
  · simp only [standardTopUnitPhase034, if_false, hs]
    exact div_mul_cancel₀ _ hs

theorem standardTopUnitPhase034_unit
    (state : StandardQSPPolynomialState032) (d : ℕ)
    (hrel : Complex.normSq (state.sourceFactor.coeff d) =
      Complex.normSq (state.targetFactor.coeff (d - 1))) :
    standardUnitPhase032 (standardTopUnitPhase034 state d) := by
  by_cases hs : state.sourceFactor.coeff d = 0
  · simp [standardUnitPhase032, standardTopUnitPhase034, hs]
  · have hsrc : Complex.normSq (state.sourceFactor.coeff d) ≠ 0 := by
      exact (Complex.normSq_pos.mpr hs).ne'
    simp only [standardUnitPhase032, standardTopUnitPhase034, if_false, hs]
    rw [Complex.normSq_div]
    rw [← hrel]
    exact div_self hsrc

theorem standardCompNegX_mul034
    (p q : Polynomial ℂ) :
    (p * q).comp (-(Polynomial.X : Polynomial ℂ)) =
      p.comp (-(Polynomial.X : Polynomial ℂ)) *
        q.comp (-(Polynomial.X : Polynomial ℂ)) := by
  apply Polynomial.funext
  intro x
  simp [Polynomial.eval_comp, Polynomial.eval_mul]

theorem standardCompNegX_add034
    (p q : Polynomial ℂ) :
    (p + q).comp (-(Polynomial.X : Polynomial ℂ)) =
      p.comp (-(Polynomial.X : Polynomial ℂ)) +
        q.comp (-(Polynomial.X : Polynomial ℂ)) := by
  apply Polynomial.funext
  intro x
  simp [Polynomial.eval_comp, Polynomial.eval_add]

theorem standardCompNegX_neg034
    (p : Polynomial ℂ) :
    (-p).comp (-(Polynomial.X : Polynomial ℂ)) =
      -p.comp (-(Polynomial.X : Polynomial ℂ)) := by
  apply Polynomial.funext
  intro x
  simp [Polynomial.eval_comp, Polynomial.eval_neg]

theorem standardCompNegX_C034 (phase : ℂ) :
    (Polynomial.C phase).comp (-(Polynomial.X : Polynomial ℂ)) =
      Polynomial.C phase := by
  apply Polynomial.funext
  intro x
  simp

theorem standardCompNegX_X034 :
    (Polynomial.X : Polynomial ℂ).comp (-(Polynomial.X : Polynomial ℂ)) =
      -(Polynomial.X : Polynomial ℂ) := by
  apply Polynomial.funext
  intro x
  simp

theorem standardCompNegX_good034 :
    standardGoodSquare032.comp (-(Polynomial.X : Polynomial ℂ)) =
      standardGoodSquare032 := by
  apply Polynomial.funext
  intro x
  simp [standardGoodSquare032]

theorem standardSourcePhase034_comp_parity
    (state : StandardQSPPolynomialState032) (phase : ℂ) (d : ℕ)
    (hparity : state.sourceFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if d % 2 = 0 then state.sourceFactor else -state.sourceFactor) :
    (standardSourcePhase032 phase state).sourceFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if d % 2 = 0 then
        (standardSourcePhase032 phase state).sourceFactor
      else -(standardSourcePhase032 phase state).sourceFactor := by
  change (Polynomial.C phase * state.sourceFactor).comp
      (-(Polynomial.X : Polynomial ℂ)) = _
  rw [standardCompNegX_mul034, standardCompNegX_C034, hparity]
  by_cases he : d % 2 = 0 <;> simp [standardSourcePhase032, he]

theorem standardSignalAdjoint034_source_comp_parity
    (state : StandardQSPPolynomialState032) (d : ℕ)
    (hd : 0 < d)
    (hsource : state.sourceFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if d % 2 = 0 then state.sourceFactor else -state.sourceFactor)
    (htarget : state.targetFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if d % 2 = 0 then -state.targetFactor else state.targetFactor) :
    (standardSignalAdjoint032 state).sourceFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if (d - 1) % 2 = 0 then
        (standardSignalAdjoint032 state).sourceFactor
      else -(standardSignalAdjoint032 state).sourceFactor := by
  change (Polynomial.X * state.sourceFactor + standardGoodSquare032 *
      state.targetFactor).comp (-(Polynomial.X : Polynomial ℂ)) = _
  rw [standardCompNegX_add034, standardCompNegX_mul034,
    standardCompNegX_mul034, standardCompNegX_X034,
    standardCompNegX_good034, hsource, htarget]
  by_cases he : d % 2 = 0
  · have hp : (d - 1) % 2 ≠ 0 := by omega
    simp [standardSignalAdjoint032, standardGoodSquare032, he, hp]
    all_goals ring
  · have hp : (d - 1) % 2 = 0 := by omega
    simp [standardSignalAdjoint032, standardGoodSquare032, he, hp]

theorem standardSignalAdjoint034_target_comp_parity
    (state : StandardQSPPolynomialState032) (d : ℕ)
    (hd : 0 < d)
    (hsource : state.sourceFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if d % 2 = 0 then state.sourceFactor else -state.sourceFactor)
    (htarget : state.targetFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if d % 2 = 0 then -state.targetFactor else state.targetFactor) :
    (standardSignalAdjoint032 state).targetFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if (d - 1) % 2 = 0 then
        -(standardSignalAdjoint032 state).targetFactor
      else (standardSignalAdjoint032 state).targetFactor := by
  change (-state.sourceFactor + Polynomial.X * state.targetFactor).comp
      (-(Polynomial.X : Polynomial ℂ)) = _
  rw [standardCompNegX_add034, standardCompNegX_neg034,
    standardCompNegX_mul034, standardCompNegX_X034, hsource, htarget]
  by_cases he : d % 2 = 0
  · have hp : (d - 1) % 2 ≠ 0 := by omega
    simp [standardSignalAdjoint032, he, hp]
  · have hp : (d - 1) % 2 = 0 := by omega
    simp [standardSignalAdjoint032, he, hp]
    all_goals ring

theorem standardCoeffZeroOfOppositeParity034
    (p : Polynomial ℂ) (d : ℕ)
    (hcomp : p.comp (-(Polynomial.X : Polynomial ℂ)) =
      if d % 2 = 0 then -p else p) :
    p.coeff d = 0 := by
  have hc := congrArg (fun r : Polynomial ℂ => r.coeff d) hcomp
  rw [coeff_comp_neg_X033] at hc
  by_cases he : d % 2 = 0
  · simp [he, negOnePow_mod_two033] at hc
    have htwo : (2 : ℂ) * p.coeff d = 0 := by
      calc
        (2 : ℂ) * p.coeff d = p.coeff d + p.coeff d := by ring
        _ = p.coeff d + (-p.coeff d) :=
          congrArg (fun z : ℂ => p.coeff d + z) hc
        _ = 0 := add_neg_cancel _
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  · simp [he, negOnePow_mod_two033] at hc
    have htwo : (2 : ℂ) * p.coeff d = 0 := by
      calc
        (2 : ℂ) * p.coeff d = p.coeff d + p.coeff d := by ring
        _ = (-p.coeff d) + p.coeff d :=
          congrArg (fun z : ℂ => z + p.coeff d) hc.symm
        _ = 0 := neg_add_cancel _
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem standardEqZeroOfDegreeLeZeroCoeff034
    (p : Polynomial ℂ)
    (hdeg : p.degree ≤ (0 : WithBot ℕ))
    (hcoeff : p.coeff 0 = 0) :
    p = 0 := by
  by_cases hp : p = 0
  · exact hp
  · have hnat : p.natDegree ≤ 0 :=
      Polynomial.natDegree_le_of_degree_le hdeg
    have hnat0 : p.natDegree = 0 := by omega
    have hleading : p.coeff p.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp
    exfalso
    apply hleading
    simpa [hnat0] using hcoeff

theorem standardTargetDegreeStrict034
    (c : StandardAdmissibility034) :
    c.state.targetFactor.degree < (c.degree : WithBot ℕ) := by
  by_cases hd0 : c.degree = 0
  · have hcoeff := standardCoeffZeroOfOppositeParity034
      c.state.targetFactor 0 (by simpa [hd0] using c.target_parity)
    have hzero := standardEqZeroOfDegreeLeZeroCoeff034
      c.state.targetFactor (by simpa [hd0] using c.target_degree) hcoeff
    simp [hzero]
  · have hdpos : 0 < c.degree := Nat.pos_of_ne_zero hd0
    have hcoeff := standardCoeffZeroOfOppositeParity034
      c.state.targetFactor c.degree c.target_parity
    have hpred := degree_le_pred_of_coeff_zero033
      c.state.targetFactor c.degree hdpos c.target_degree hcoeff
    calc
      c.state.targetFactor.degree ≤ ((c.degree - 1 : ℕ) : WithBot ℕ) := hpred
      _ < (c.degree : WithBot ℕ) := by
        have hnat : c.degree - 1 < c.degree := by omega
        exact WithBot.coe_lt_coe.mpr hnat

theorem standardAdmissibleTopNormRelation034
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    Complex.normSq (c.state.sourceFactor.coeff c.degree) =
      Complex.normSq (c.state.targetFactor.coeff (c.degree - 1)) := by
  exact standardParaunitary034_top_norm_relation c.state c.degree hd
    c.source_degree (standardTargetDegreeStrict034 c) c.paraunitary

noncomputable def standardTopAngle034
    (c : StandardAdmissibility034) (hd : 0 < c.degree) : ℝ :=
  Classical.choose (exists_standardPhase032_of_unit033
    (standardTopUnitPhase034 c.state c.degree)
    (standardTopUnitPhase034_unit c.state c.degree
      (standardAdmissibleTopNormRelation034 c hd)))

theorem standardTopAngle034_spec
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    standardPhase032 (standardTopAngle034 c hd) =
      standardTopUnitPhase034 c.state c.degree := by
  exact Classical.choose_spec (exists_standardPhase032_of_unit033
    (standardTopUnitPhase034 c.state c.degree)
    (standardTopUnitPhase034_unit c.state c.degree
      (standardAdmissibleTopNormRelation034 c hd)))

def standardPhasedState034
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    StandardQSPPolynomialState032 :=
  standardSourcePhase032
    (standardPhase032 (standardTopAngle034 c hd)) c.state

def standardExtractedState034
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    StandardQSPPolynomialState032 :=
  standardSignalAdjoint032 (standardPhasedState034 c hd)

theorem standardPhasedState034_source_degree
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    (standardPhasedState034 c hd).sourceFactor.degree ≤
      (c.degree : WithBot ℕ) := by
  change (Polynomial.C (standardPhase032 (standardTopAngle034 c hd)) *
      c.state.sourceFactor).degree ≤ (c.degree : WithBot ℕ)
  rw [Polynomial.degree_C_mul]
  · exact c.source_degree
  · exact standardUnitPhase032_ne_zero _
      (standardPhase032_unitNormSq _)

theorem standardPhasedState034_source_coeff
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    (standardPhasedState034 c hd).sourceFactor.coeff c.degree =
      c.state.targetFactor.coeff (c.degree - 1) := by
  change (Polynomial.C (standardPhase032 (standardTopAngle034 c hd)) *
      c.state.sourceFactor).coeff c.degree = _
  rw [Polynomial.coeff_C_mul, standardTopAngle034_spec]
  exact standardTopUnitPhase034_mul_source c.state c.degree
    (standardAdmissibleTopNormRelation034 c hd)

theorem standardPhasedState034_source_comp_parity
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    (standardPhasedState034 c hd).sourceFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if c.degree % 2 = 0 then
        (standardPhasedState034 c hd).sourceFactor
      else -(standardPhasedState034 c hd).sourceFactor := by
  change (standardSourcePhase032
      (standardPhase032 (standardTopAngle034 c hd)) c.state).sourceFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) = _
  exact standardSourcePhase034_comp_parity c.state
    (standardPhase032 (standardTopAngle034 c hd)) c.degree c.source_parity

theorem standardPhasedState034_target_comp_parity
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    (standardPhasedState034 c hd).targetFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if c.degree % 2 = 0 then
        -(standardPhasedState034 c hd).targetFactor
      else (standardPhasedState034 c hd).targetFactor := by
  change c.state.targetFactor.comp (-(Polynomial.X : Polynomial ℂ)) = _
  exact c.target_parity

theorem standardExtractedState034_source_top_cancel
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    (standardExtractedState034 c hd).sourceFactor.coeff
        (c.degree + 1) = 0 := by
  unfold standardExtractedState034
  apply standardInverseSourceCoeff_succ_cancel032
  · omega
  · exact standardTargetDegreeStrict034 c
  · exact standardPhasedState034_source_coeff c hd

theorem standardExtractedState034_target_top_cancel
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    (standardExtractedState034 c hd).targetFactor.coeff c.degree = 0 := by
  unfold standardExtractedState034
  change (- (standardPhasedState034 c hd).sourceFactor +
      Polynomial.X * (standardPhasedState034 c hd).targetFactor).coeff
        c.degree = 0
  have hX :
      (Polynomial.X * (standardPhasedState034 c hd).targetFactor).coeff
          c.degree =
        (standardPhasedState034 c hd).targetFactor.coeff
          (c.degree - 1) := by
    rw [← show c.degree - 1 + 1 = c.degree by omega,
      Polynomial.coeff_X_mul]
    have hle : 1 ≤ c.degree := by omega
    simp [Nat.sub_add_cancel hle]
  rw [Polynomial.coeff_add, Polynomial.coeff_neg, hX,
    standardPhasedState034_source_coeff c hd]
  have ht :
      (standardPhasedState034 c hd).targetFactor.coeff
          (c.degree - 1) = c.state.targetFactor.coeff (c.degree - 1) := rfl
  rw [ht]
  ring

theorem standardExtractedState034_source_degree_succ
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    (standardExtractedState034 c hd).sourceFactor.degree ≤
      ((c.degree + 1 : ℕ) : WithBot ℕ) := by
  have hS := standardPhasedState034_source_degree c hd
  have hTlt := standardTargetDegreeStrict034 c
  have hT := degree_le_pred_of_degree_lt033
    c.state.targetFactor c.degree hd hTlt
  have hXS :
      (Polynomial.X * (standardPhasedState034 c hd).sourceFactor).degree ≤
        ((c.degree + 1 : ℕ) : WithBot ℕ) := by
    calc
      (Polynomial.X * (standardPhasedState034 c hd).sourceFactor).degree ≤
          (Polynomial.X : Polynomial ℂ).degree +
            (standardPhasedState034 c hd).sourceFactor.degree :=
        Polynomial.degree_mul_le _ _
      _ ≤ (1 : WithBot ℕ) + (c.degree : WithBot ℕ) := by
        apply add_le_add
        · rw [Polynomial.degree_X]
        · exact hS
      _ = ((c.degree + 1 : ℕ) : WithBot ℕ) := by
        exact_mod_cast (Nat.add_comm 1 c.degree)
  have hGT :
      (standardGoodSquare032 *
          (standardPhasedState034 c hd).targetFactor).degree ≤
        ((c.degree + 1 : ℕ) : WithBot ℕ) := by
    calc
      (standardGoodSquare032 *
          (standardPhasedState034 c hd).targetFactor).degree ≤
          standardGoodSquare032.degree +
            (standardPhasedState034 c hd).targetFactor.degree :=
        Polynomial.degree_mul_le _ _
      _ ≤ (2 : WithBot ℕ) + ((c.degree - 1 : ℕ) : WithBot ℕ) := by
        apply add_le_add standardGoodSquare032_degree_bound
        exact hT
      _ = ((c.degree + 1 : ℕ) : WithBot ℕ) := by
        exact_mod_cast (by omega :
          2 + (c.degree - 1) = c.degree + 1)
  change (Polynomial.X * (standardPhasedState034 c hd).sourceFactor +
      standardGoodSquare032 * (standardPhasedState034 c hd).targetFactor).degree ≤ _
  calc
    _ ≤ max (Polynomial.X * (standardPhasedState034 c hd).sourceFactor).degree
        (standardGoodSquare032 *
          (standardPhasedState034 c hd).targetFactor).degree :=
      Polynomial.degree_add_le _ _
    _ ≤ ((c.degree + 1 : ℕ) : WithBot ℕ) := max_le hXS hGT

theorem standardExtractedState034_target_degree_bound
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    (standardExtractedState034 c hd).targetFactor.degree ≤
      (c.degree : WithBot ℕ) := by
  have hS := standardPhasedState034_source_degree c hd
  have hTlt := standardTargetDegreeStrict034 c
  have hT := degree_le_pred_of_degree_lt033
    c.state.targetFactor c.degree hd hTlt
  have hXT :
      (Polynomial.X * (standardPhasedState034 c hd).targetFactor).degree ≤
        (c.degree : WithBot ℕ) := by
    calc
      (Polynomial.X * (standardPhasedState034 c hd).targetFactor).degree ≤
          (Polynomial.X : Polynomial ℂ).degree +
            (standardPhasedState034 c hd).targetFactor.degree :=
        Polynomial.degree_mul_le _ _
      _ ≤ (1 : WithBot ℕ) + ((c.degree - 1 : ℕ) : WithBot ℕ) := by
        apply add_le_add
        · rw [Polynomial.degree_X]
        · exact hT
      _ = (c.degree : WithBot ℕ) := by
        exact_mod_cast (by omega : 1 + (c.degree - 1) = c.degree)
  change (-(standardPhasedState034 c hd).sourceFactor +
      Polynomial.X * (standardPhasedState034 c hd).targetFactor).degree ≤ _
  calc
    _ ≤ max (-(standardPhasedState034 c hd).sourceFactor).degree
        (Polynomial.X * (standardPhasedState034 c hd).targetFactor).degree :=
      Polynomial.degree_add_le _ _
    _ ≤ (c.degree : WithBot ℕ) := by
      apply max_le
      · simpa using hS
      · exact hXT

theorem standardExtractedState034_degree_drop
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    (standardExtractedState034 c hd).sourceFactor.degree ≤
        ((c.degree - 1 : ℕ) : WithBot ℕ) ∧
      (standardExtractedState034 c hd).targetFactor.degree ≤
        ((c.degree - 1 : ℕ) : WithBot ℕ) := by
  have hsource_succ := standardExtractedState034_source_degree_succ c hd
  have hsource_d := degree_le_pred_of_coeff_zero033
    (standardExtractedState034 c hd).sourceFactor
    (c.degree + 1) (by omega) hsource_succ
    (standardExtractedState034_source_top_cancel c hd)
  have hsource_comp := standardSignalAdjoint034_source_comp_parity
    (standardPhasedState034 c hd) c.degree hd
    (standardPhasedState034_source_comp_parity c hd)
    (standardPhasedState034_target_comp_parity c hd)
  have hsource_coeff := coeff_zero_of_prev_comp_parity033
    (standardExtractedState034 c hd).sourceFactor c.degree hd
    hsource_comp
  have hsource := degree_le_pred_of_coeff_zero033
    (standardExtractedState034 c hd).sourceFactor c.degree hd
    hsource_d hsource_coeff
  have htarget_d := standardExtractedState034_target_degree_bound c hd
  have htarget := degree_le_pred_of_coeff_zero033
    (standardExtractedState034 c hd).targetFactor c.degree hd
    htarget_d (standardExtractedState034_target_top_cancel c hd)
  exact ⟨hsource, htarget⟩

noncomputable def standardExtractedAdmissible034
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    StandardAdmissibility034 := by
  have hdrop := standardExtractedState034_degree_drop c hd
  refine ⟨standardExtractedState034 c hd, c.degree - 1, hdrop.1,
    hdrop.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact standardSignalAdjoint034_source_comp_parity
      (standardPhasedState034 c hd) c.degree hd
      (standardPhasedState034_source_comp_parity c hd)
      (standardPhasedState034_target_comp_parity c hd)
  · exact standardSignalAdjoint034_target_comp_parity
      (standardPhasedState034 c hd) c.degree hd
      (standardPhasedState034_source_comp_parity c hd)
      (standardPhasedState034_target_comp_parity c hd)
  · have hphase := standardParaunitary034_sourcePhase c.state
        (standardPhase032 (standardTopAngle034 c hd))
        (standardPhase032_unitNormSq _)
        c.paraunitary
    exact standardParaunitary034_signalAdjoint
      (standardPhasedState034 c hd) hphase
  · intro x
    change standardWeightedEnergy032 x
      (standardSignalAdjoint032 (standardPhasedState034 c hd)) = 1
    rw [standardWeightedEnergy032_signalAdjoint]
    change standardWeightedEnergy032 x
      (standardSourcePhase032
        (standardPhase032 (standardTopAngle034 c hd)) c.state) = 1
    rw [standardWeightedEnergy032_sourcePhase]
    exact c.weighted_energy x
  · exact fun x => (Polynomial.eval (x : ℂ)
      (standardExtractedState034 c hd).sourceFactor).re
  · intro x
    rfl

noncomputable def completionAdmissible034
    (input : GeneralRealQSPPolynomial127) : StandardAdmissibility034 :=
  ⟨completionStandardState033 input, input.degree,
    completionStandardState033_source_degree input,
    le_of_lt (completionStandardState033_target_degree input),
    completionStandardState033_source_comp_parity input,
    completionStandardState033_target_comp_parity input,
    completionStandardState034_paraunitary input,
    completionStandardState033_weightedEnergy033 input,
    (fun x => Polynomial.eval x (completionPair024 input).P),
    completionStandardState033_real_readout input⟩

theorem standardEqCOfDegreeLeZero034
    (p : Polynomial ℂ)
    (hdeg : p.degree ≤ (0 : WithBot ℕ)) :
    p = Polynomial.C (p.coeff 0) := by
  by_cases hp : p = 0
  · simp [hp]
  · have hnat : p.natDegree ≤ 0 :=
      Polynomial.natDegree_le_of_degree_le hdeg
    have hnat0 : p.natDegree = 0 := by omega
    apply Polynomial.ext
    intro n
    cases n with
    | zero => simp
    | succ n =>
      have hlt : p.natDegree < Nat.succ n := by omega
      rw [Polynomial.coeff_C]
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

theorem standardBaseState034_phase_exists
    (c : StandardAdmissibility034) (hd0 : c.degree = 0) :
    ∃ angle : ℝ,
      standardSourcePhase032 (standardPhase032 angle) standardQ0State032 =
        c.state := by
  have htarget_deg : c.state.targetFactor.degree ≤
      (0 : WithBot ℕ) := by simpa [hd0] using c.target_degree
  have htarget_coeff : c.state.targetFactor.coeff 0 = 0 :=
    standardCoeffZeroOfOppositeParity034 c.state.targetFactor 0
      (by simpa [hd0] using c.target_parity)
  have htarget_zero := standardEqZeroOfDegreeLeZeroCoeff034
    c.state.targetFactor htarget_deg htarget_coeff
  have hsource_const := standardEqCOfDegreeLeZero034
    c.state.sourceFactor (by simpa [hd0] using c.source_degree)
  have hpara := c.paraunitary
  have hsource_prod :
      c.state.sourceFactor *
          standardStarPolynomial034 c.state.sourceFactor = 1 := by
    unfold standardParaunitary034 at hpara
    rw [htarget_zero] at hpara
    simpa using hpara
  have hconst_prod :
      Polynomial.C (c.state.sourceFactor.coeff 0) *
          standardStarPolynomial034
            (Polynomial.C (c.state.sourceFactor.coeff 0)) = 1 := by
    rw [hsource_const] at hsource_prod
    exact hsource_prod
  have hcoeff_prod := congrArg
      (fun p : Polynomial ℂ => p.coeff 0) hconst_prod
  have hnorm : Complex.normSq (c.state.sourceFactor.coeff 0) = 1 := by
    have hscalar :
        c.state.sourceFactor.coeff 0 *
            star (c.state.sourceFactor.coeff 0) = 1 := by
      simpa [standardStarPolynomial034] using hcoeff_prod
    change c.state.sourceFactor.coeff 0 *
        (starRingEnd ℂ) (c.state.sourceFactor.coeff 0) = 1 at hscalar
    rw [Complex.mul_conj] at hscalar
    exact_mod_cast hscalar
  obtain ⟨angle, hangle⟩ := exists_standardPhase032_of_unit033
    (c.state.sourceFactor.coeff 0) hnorm
  refine ⟨angle, ?_⟩
  apply standardPolynomialState_ext032
  · rw [hsource_const, hangle]
    simp [standardSourcePhase032, standardQ0State032]
  · rw [htarget_zero]
    simp [standardSourcePhase032, standardQ0State032]

theorem standardPhase032_neg034 (angle : ℝ) :
    standardPhase032 (-angle) = (standardPhase032 angle)⁻¹ := by
  unfold standardPhase032
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

inductive StandardWordStep034 where
  | signal
  | sourcePhase (angle : ℝ)

def standardApplyWordStep034
    (step : StandardWordStep034)
    (state : StandardQSPPolynomialState032) :
    StandardQSPPolynomialState032 :=
  match step with
  | .signal => standardSignalForward032 state
  | .sourcePhase angle =>
      standardSourcePhase032 (standardPhase032 angle) state

def standardWordEval034
    (word : List StandardWordStep034)
    (state : StandardQSPPolynomialState032) :
    StandardQSPPolynomialState032 :=
  word.foldl (fun current step => standardApplyWordStep034 step current) state

theorem standardWordEval034_append
    (word : List StandardWordStep034)
    (tail : List StandardWordStep034)
    (state : StandardQSPPolynomialState032) :
    standardWordEval034 (word ++ tail) state =
      standardWordEval034 tail (standardWordEval034 word state) := by
  simp [standardWordEval034, List.foldl_append]

theorem standardSourcePhase032_inverse_angle034
    (angle : ℝ) (state : StandardQSPPolynomialState032) :
    standardSourcePhase032 (standardPhase032 (-angle))
        (standardSourcePhase032 (standardPhase032 angle) state) = state := by
  rw [standardPhase032_neg034]
  change standardSourcePhaseInverse032 (standardPhase032 angle)
      (standardSourcePhase032 (standardPhase032 angle) state) = state
  exact standardSourcePhaseInverse032_forward032
    (standardPhase032 angle) (standardPhase032_unitNormSq angle) state

theorem standardExtractedState034_forward_establishedBridge
    (c : StandardAdmissibility034) (hd : 0 < c.degree) :
    standardSignalForward032 (standardExtractedState034 c hd) =
      standardPhasedState034 c hd := by
  change standardSignalForward032
      (standardSignalAdjoint032 (standardPhasedState034 c hd)) = _
  exact standardSignalForward032_adjoint032 _

end
end SpectralSamplingProof.Analytic
