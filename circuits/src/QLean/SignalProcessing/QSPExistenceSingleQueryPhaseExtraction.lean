import QLean.SignalProcessing.QSPExistenceStandardQSPPolynomialModel
import QLean.SignalProcessing.QSPExistencePhaseCarryingCompletion

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## Completion pair in the canonical one-query state model

The completion source is the evaluator-native phase-carrying polynomial
`P + I B`; the target is the real residual factor `C`.  This is a typed
map, rather than a caller-supplied state or a proof-bearing runtime field.
-/

def completionStandardState033
    (input : GeneralRealQSPPolynomial127) :
    StandardQSPPolynomialState032 where
  sourceFactor := (completionPhaseCarryingState028 input).sourceFactor
  targetFactor := (completionPhaseCarryingState028 input).targetFactor

theorem completionStandardState033_source_eval
    (input : GeneralRealQSPPolynomial127) (x : ℝ) :
    Polynomial.eval (x : ℂ)
        (completionStandardState033 input).sourceFactor =
      ((Polynomial.eval x (completionPair024 input).P : ℝ) : ℂ) +
        Complex.I * ((Polynomial.eval x (completionPair024 input).B : ℝ) : ℂ) := by
  simpa [completionStandardState033, polynomialReducedStateEval026] using
    completionPhaseCarryingState028_source_eval input x

theorem completionStandardState033_real_readout
    (input : GeneralRealQSPPolynomial127) (x : ℝ) :
    (Polynomial.eval (x : ℂ)
        (completionStandardState033 input).sourceFactor).re =
      Polynomial.eval x (completionPair024 input).P := by
  rw [completionStandardState033_source_eval]
  simp

theorem completionStandardState033_weightedEnergy033
    (input : GeneralRealQSPPolynomial127) (x : ℝ) :
    standardWeightedEnergy032 x (completionStandardState033 input) = 1 := by
  simpa [standardWeightedEnergy032, completionStandardState033,
    polynomialReducedStateEval026] using
    completionPhaseCarryingState028_weighted_norm input x

/-! ## The top-degree scalar relation

Taking the coefficient at `2*d` in the real completion identity is the
one-query norm relation.  The strict `C` bound is what moves the shifted
`C^2` term to exactly `2*(d-1)`; no full-degree or monicity assumption is
used.
-/

/-! ## Internal phase selection and the first one-query cancellation

The top relation is used only to select a phase inside this typed
completion-to-state map.  No phase or certificate is supplied by a caller.
-/

theorem exists_standardPhase032_of_unit033
    (phase : ℂ) (hunit : standardUnitPhase032 phase) :
    ∃ angle : ℝ, standardPhase032 angle = phase := by
  have hnormsq : ‖phase‖ ^ 2 = 1 := by
    simpa [standardUnitPhase032, Complex.normSq_eq_norm_sq] using hunit
  have hnorm : ‖phase‖ = 1 := by
    nlinarith [norm_nonneg phase]
  refine ⟨phase.arg, ?_⟩
  have hpolar := Complex.norm_mul_exp_arg_mul_I phase
  have hpolar' : (1 : ℂ) * Complex.exp ((phase.arg : ℂ) * Complex.I) = phase := by
    simpa [hnorm] using hpolar
  simpa [standardPhase032, mul_comm] using hpolar'

/-! ## Parity of the mapped completion state

The source carries the common parity of `P` and `B`, while the target carries
the opposite parity of `C`.  These are evaluation equalities because they are
the parity fields of the accepted interval witness; no coefficient shortcut
is used.
-/

theorem degree_le_pred_of_coeff_zero033
    (p : Polynomial ℂ) (d : ℕ) (hd : 0 < d)
    (hdeg : p.degree ≤ (d : WithBot ℕ))
    (hcoeff : p.coeff d = 0) :
    p.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
  by_cases hp : p = 0
  · simp [hp]
  · have hnat : p.natDegree ≤ d :=
      Polynomial.natDegree_le_of_degree_le hdeg
    have hlt : p.natDegree < d := by
      by_contra hnot
      have hge : d ≤ p.natDegree := Nat.le_of_not_gt hnot
      have heq : p.natDegree = d := Nat.le_antisymm hnat hge
      have hleading : p.coeff p.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hp
      apply hleading
      rw [heq]
      exact hcoeff
    have hpred : p.natDegree ≤ d - 1 := by omega
    exact Polynomial.degree_le_of_natDegree_le hpred

theorem degree_le_pred_of_degree_lt033
    (p : Polynomial ℂ) (d : ℕ) (hd : 0 < d)
    (hdeg : p.degree < (d : WithBot ℕ)) :
    p.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
  by_cases hp : p = 0
  · simp [hp]
  · have hnat : p.natDegree < d :=
      (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hdeg
    exact Polynomial.degree_le_of_natDegree_le (by omega)

theorem standardGoodSquare032_degree_bound
    : standardGoodSquare032.degree ≤ (2 : WithBot ℕ) := by
  change (1 - (Polynomial.X : Polynomial ℂ) ^ 2).degree ≤ (2 : WithBot ℕ)
  calc
    (1 - (Polynomial.X : Polynomial ℂ) ^ 2).degree ≤
        max (1 : Polynomial ℂ).degree
          ((Polynomial.X : Polynomial ℂ) ^ 2).degree :=
      Polynomial.degree_sub_le _ _
    _ ≤ (2 : WithBot ℕ) := by
      apply max_le
      · rw [Polynomial.degree_one]
        norm_num
      · rw [Polynomial.degree_X_pow]
        exact le_rfl

theorem completionStandardState033_source_degree
    (input : GeneralRealQSPPolynomial127) :
    (completionStandardState033 input).sourceFactor.degree ≤
      (input.degree : WithBot ℕ) := by
  have hP :
      ((completionPair024 input).P.map Complex.ofRealHom).degree ≤
        (input.degree : WithBot ℕ) := by
    rw [Polynomial.degree_map_eq_of_injective Complex.ofRealHom.injective]
    exact Polynomial.degree_le_of_natDegree_le
      (completionPair024 input).P_degree
  have hB :
      ((completionPair024 input).B.map Complex.ofRealHom).degree ≤
        (input.degree : WithBot ℕ) := by
    rw [Polynomial.degree_map_eq_of_injective Complex.ofRealHom.injective]
    exact (completionPair024 input).B_degree
  change (((completionPair024 input).P.map Complex.ofRealHom) +
      Polynomial.C Complex.I *
        (completionPair024 input).B.map Complex.ofRealHom).degree ≤ _
  calc
    (((completionPair024 input).P.map Complex.ofRealHom) +
        Polynomial.C Complex.I *
          (completionPair024 input).B.map Complex.ofRealHom).degree ≤
        max ((completionPair024 input).P.map Complex.ofRealHom).degree
          (Polynomial.C Complex.I *
            (completionPair024 input).B.map Complex.ofRealHom).degree :=
      Polynomial.degree_add_le _ _
    _ ≤ (input.degree : WithBot ℕ) := by
      apply max_le hP
      calc
        (Polynomial.C Complex.I *
            (completionPair024 input).B.map Complex.ofRealHom).degree =
            ((completionPair024 input).B.map Complex.ofRealHom).degree := by
          rw [Polynomial.degree_C_mul]
          exact Complex.I_ne_zero
        _ ≤ (input.degree : WithBot ℕ) := hB

theorem completionStandardState033_target_degree
    (input : GeneralRealQSPPolynomial127) :
    (completionStandardState033 input).targetFactor.degree <
      (input.degree : WithBot ℕ) := by
  change ((completionPair024 input).C.map Complex.ofRealHom).degree <
      (input.degree : WithBot ℕ)
  rw [Polynomial.degree_map_eq_of_injective Complex.ofRealHom.injective]
  exact (completionPair024 input).C_degree

theorem coeff_comp_neg_X033
    (p : Polynomial ℂ) (n : ℕ) :
    (p.comp (-(Polynomial.X : Polynomial ℂ))).coeff n =
      (-1 : ℂ) ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hcomp :
          (p + q).comp (-(Polynomial.X : Polynomial ℂ)) =
            p.comp (-(Polynomial.X : Polynomial ℂ)) +
              q.comp (-(Polynomial.X : Polynomial ℂ)) := by
        simp [Polynomial.comp, Polynomial.eval₂_add]
      rw [hcomp]
      simp only [Polynomial.coeff_add, hp, hq]
      ring
  | monomial m a =>
      have hcomp :
          ((Polynomial.monomial m) a).comp
              (-(Polynomial.X : Polynomial ℂ)) =
            Polynomial.C a * (-(Polynomial.X : Polynomial ℂ)) ^ m := by
        simp [Polynomial.comp, Polynomial.eval₂_monomial]
      rw [hcomp, Polynomial.coeff_C_mul,
        Polynomial.coeff_monomial]
      rw [neg_pow]
      rw [show (-1 : Polynomial ℂ) = Polynomial.C (-1 : ℂ) by norm_num]
      rw [← Polynomial.C_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow]
      by_cases hnm : n = m
      · subst n
        simp
        ring
      · have hmn : m ≠ n := by
          intro h
          exact hnm h.symm
        simp [hnm, hmn]

theorem comp_neg_X_of_eval_parity033
    (p : Polynomial ℝ) (degree : ℕ)
    (hparity : ∀ x : ℝ,
      Polynomial.eval (-x) p =
        if degree % 2 = 0 then Polynomial.eval x p
        else -Polynomial.eval x p) :
    p.comp (-(Polynomial.X : Polynomial ℝ)) =
      if degree % 2 = 0 then p else -p := by
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_comp]
  by_cases he : degree % 2 = 0
  · simpa [he] using hparity x
  · simpa [he] using hparity x

theorem map_comp_neg_X033
    (p : Polynomial ℝ) :
    (p.map Complex.ofRealHom).comp (-(Polynomial.X : Polynomial ℂ)) =
      (p.comp (-(Polynomial.X : Polynomial ℝ))).map Complex.ofRealHom := by
  have hX :
      Polynomial.map Complex.ofRealHom (-(Polynomial.X : Polynomial ℝ)) =
        -(Polynomial.X : Polynomial ℂ) := by
    simp
  rw [← hX, ← Polynomial.map_comp]

theorem completionStandardState033_source_comp_parity
    (input : GeneralRealQSPPolynomial127) :
    (completionStandardState033 input).sourceFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if input.degree % 2 = 0 then
        (completionStandardState033 input).sourceFactor
      else -(completionStandardState033 input).sourceFactor := by
  have hp := comp_neg_X_of_eval_parity033 input.polynomial input.degree
    input.parity_law
  have hb := comp_neg_X_of_eval_parity033
    (completionWitness024 input).B input.degree
    (completionWitness024 input).B_parity
  have hPmap :
      ((completionPair024 input).P.map Complex.ofRealHom).comp
          (-(Polynomial.X : Polynomial ℂ)) =
        if input.degree % 2 = 0 then
          (completionPair024 input).P.map Complex.ofRealHom
        else -(completionPair024 input).P.map Complex.ofRealHom := by
    calc
      ((completionPair024 input).P.map Complex.ofRealHom).comp
          (-(Polynomial.X : Polynomial ℂ)) =
          ((completionPair024 input).P.comp
            (-(Polynomial.X : Polynomial ℝ))).map Complex.ofRealHom :=
        map_comp_neg_X033 (completionPair024 input).P
      _ = (if input.degree % 2 = 0 then
            (completionPair024 input).P else
            -(completionPair024 input).P).map Complex.ofRealHom := by
        rw [show (completionPair024 input).P.comp
            (-(Polynomial.X : Polynomial ℝ)) =
              if input.degree % 2 = 0 then
                (completionPair024 input).P else
                -(completionPair024 input).P by
          simpa [completionPair024] using hp]
      _ = if input.degree % 2 = 0 then
            (completionPair024 input).P.map Complex.ofRealHom
          else -(completionPair024 input).P.map Complex.ofRealHom := by
        by_cases he : input.degree % 2 = 0 <;> simp [he]
  have hBmap :
      ((completionPair024 input).B.map Complex.ofRealHom).comp
          (-(Polynomial.X : Polynomial ℂ)) =
        if input.degree % 2 = 0 then
          (completionPair024 input).B.map Complex.ofRealHom
        else -(completionPair024 input).B.map Complex.ofRealHom := by
    calc
      ((completionPair024 input).B.map Complex.ofRealHom).comp
          (-(Polynomial.X : Polynomial ℂ)) =
          ((completionPair024 input).B.comp
            (-(Polynomial.X : Polynomial ℝ))).map Complex.ofRealHom :=
        map_comp_neg_X033 (completionPair024 input).B
      _ = (if input.degree % 2 = 0 then
            (completionPair024 input).B else
            -(completionPair024 input).B).map Complex.ofRealHom := by
        rw [show (completionPair024 input).B.comp
            (-(Polynomial.X : Polynomial ℝ)) =
              if input.degree % 2 = 0 then
                (completionPair024 input).B else
                -(completionPair024 input).B by
          simpa [completionPair024] using hb]
      _ = if input.degree % 2 = 0 then
            (completionPair024 input).B.map Complex.ofRealHom
          else -(completionPair024 input).B.map Complex.ofRealHom := by
        by_cases he : input.degree % 2 = 0 <;> simp [he]
  change (((completionPair024 input).P.map Complex.ofRealHom) +
      Polynomial.C Complex.I *
        (completionPair024 input).B.map Complex.ofRealHom).comp
          (-(Polynomial.X : Polynomial ℂ)) = _
  have hsum :
      (((completionPair024 input).P.map Complex.ofRealHom) +
        Polynomial.C Complex.I *
          (completionPair024 input).B.map Complex.ofRealHom).comp
            (-(Polynomial.X : Polynomial ℂ)) =
        ((completionPair024 input).P.map Complex.ofRealHom).comp
            (-(Polynomial.X : Polynomial ℂ)) +
          Polynomial.C Complex.I *
            ((completionPair024 input).B.map Complex.ofRealHom).comp
              (-(Polynomial.X : Polynomial ℂ)) := by
    simp [Polynomial.comp, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C]
  rw [hsum, hPmap, hBmap]
  change _ = if input.degree % 2 = 0 then
      ((completionPair024 input).P.map Complex.ofRealHom) +
        Polynomial.C Complex.I *
          (completionPair024 input).B.map Complex.ofRealHom
    else -(((completionPair024 input).P.map Complex.ofRealHom) +
      Polynomial.C Complex.I *
        (completionPair024 input).B.map Complex.ofRealHom)
  by_cases he : input.degree % 2 = 0
  · simp [he]
  · simp [he]
    ring

theorem completionStandardState033_target_comp_parity
    (input : GeneralRealQSPPolynomial127) :
    (completionStandardState033 input).targetFactor.comp
        (-(Polynomial.X : Polynomial ℂ)) =
      if input.degree % 2 = 0 then
        -(completionStandardState033 input).targetFactor
      else (completionStandardState033 input).targetFactor := by
  have hc0 := comp_neg_X_of_eval_parity033
    (completionWitness024 input).C (input.degree + 1)
    (by
      intro x
      have hc := (completionWitness024 input).C_parity x
      by_cases he : input.degree % 2 = 0
      · have hnext : (input.degree + 1) % 2 ≠ 0 := by omega
        simpa [he, hnext] using hc
      · have hnext : (input.degree + 1) % 2 = 0 := by omega
        simpa [he, hnext] using hc)
  have hc :
      (completionWitness024 input).C.comp
          (-(Polynomial.X : Polynomial ℝ)) =
        if input.degree % 2 = 0 then
          -(completionWitness024 input).C
        else (completionWitness024 input).C := by
    by_cases he : input.degree % 2 = 0
    · have hnext : (input.degree + 1) % 2 ≠ 0 := by omega
      simpa [he, hnext] using hc0
    · have hnext : (input.degree + 1) % 2 = 0 := by omega
      simpa [he, hnext] using hc0
  have hCmap :
      ((completionPair024 input).C.map Complex.ofRealHom).comp
          (-(Polynomial.X : Polynomial ℂ)) =
        if input.degree % 2 = 0 then
          -(completionPair024 input).C.map Complex.ofRealHom
        else (completionPair024 input).C.map Complex.ofRealHom := by
    calc
      ((completionPair024 input).C.map Complex.ofRealHom).comp
          (-(Polynomial.X : Polynomial ℂ)) =
          ((completionPair024 input).C.comp
            (-(Polynomial.X : Polynomial ℝ))).map Complex.ofRealHom :=
        map_comp_neg_X033 (completionPair024 input).C
      _ = (if input.degree % 2 = 0 then
            -(completionPair024 input).C else
            (completionPair024 input).C).map Complex.ofRealHom := by
        rw [show (completionPair024 input).C.comp
            (-(Polynomial.X : Polynomial ℝ)) =
              if input.degree % 2 = 0 then
                -(completionPair024 input).C else
                (completionPair024 input).C by
          simpa [completionPair024] using hc]
      _ = if input.degree % 2 = 0 then
            -(completionPair024 input).C.map Complex.ofRealHom
          else (completionPair024 input).C.map Complex.ofRealHom := by
        by_cases he : input.degree % 2 = 0 <;> simp [he]
  change ((completionPair024 input).C.map Complex.ofRealHom).comp
      (-(Polynomial.X : Polynomial ℂ)) = _
  exact hCmap

theorem negOnePow_mod_two033 (n : ℕ) :
    (-1 : ℂ) ^ n = if n % 2 = 0 then 1 else -1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases he : n % 2 = 0
      · have hnext : (n + 1) % 2 ≠ 0 := by omega
        simp [pow_succ, ih, he, hnext]
      · have hnext : (n + 1) % 2 = 0 := by omega
        simp [pow_succ, ih, he, hnext]

theorem coeff_zero_of_prev_comp_parity033
    (p : Polynomial ℂ) (d : ℕ) (hd : 0 < d)
    (hcomp : p.comp (-(Polynomial.X : Polynomial ℂ)) =
      if (d - 1) % 2 = 0 then p else -p) :
    p.coeff d = 0 := by
  have hc := congrArg (fun r : Polynomial ℂ => r.coeff d) hcomp
  rw [coeff_comp_neg_X033] at hc
  by_cases he : d % 2 = 0
  · have hprev : (d - 1) % 2 ≠ 0 := by omega
    simp [hprev, negOnePow_mod_two033, he] at hc
    have htwoeq : (2 : ℂ) * p.coeff d = 0 := by
      calc
        (2 : ℂ) * p.coeff d = p.coeff d + p.coeff d := by ring
        _ = p.coeff d + (-p.coeff d) := by
          congr 1
        _ = 0 := add_neg_cancel _
    exact (mul_eq_zero.mp htwoeq).resolve_left (by norm_num)
  · have hprev : (d - 1) % 2 = 0 := by omega
    simp [hprev, negOnePow_mod_two033, he] at hc
    have hneg : p.coeff d = -p.coeff d := hc.symm
    have htwoeq : (2 : ℂ) * p.coeff d = 0 := by
      calc
        (2 : ℂ) * p.coeff d = p.coeff d + p.coeff d := by ring
        _ = p.coeff d + (-p.coeff d) := by
          congr 1
        _ = 0 := add_neg_cancel _
    exact (mul_eq_zero.mp htwoeq).resolve_left (by norm_num)

end
end SpectralSamplingProof.Analytic
