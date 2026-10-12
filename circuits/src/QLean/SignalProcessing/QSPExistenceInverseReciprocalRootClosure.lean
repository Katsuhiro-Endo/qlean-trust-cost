import QLean.SignalProcessing.QSPExistenceParityRootPartition
import Mathlib.Algebra.Polynomial.Reverse

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## A fixed-width reciprocal operation

`reflect N` is the coefficient-level reciprocal with a declared width `N`.
It is deliberately used instead of `reverse`: unlike `reverse`, it keeps the
zero-root/degree-defect cases visible and does not silently replace the
declared width by the actual degree.
-/

def invStar127 (z : ℂ) : ℂ := ((starRingEnd ℂ) z)⁻¹

@[simp] lemma invStar127_zero : invStar127 0 = 0 := by
  simp [invStar127]

lemma invStar127_involutive (z : ℂ) : invStar127 (invStar127 z) = z := by
  simp [invStar127]

/-! ## From nonzero evaluation reciprocity to a fixed-width polynomial identity -/

theorem reflect_fixed_of_reciprocal_eval127
    (p : Polynomial ℝ) (N : ℕ) (hdeg : p.natDegree ≤ N)
    (hrecip : ∀ t : ℝ, t ≠ 0 →
      t ^ N * Polynomial.eval (t⁻¹) p = Polynomial.eval t p) :
    p.reflect N = p := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : (Set.Ioi (0 : ℝ)).Infinite := Set.Ioi_infinite 0
  refine hinf.mono ?_
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  letI : Invertible t := invertibleOfNonzero ht0
  letI : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht0)
  have hstep :=
    Polynomial.eval₂_reflect_mul_pow (RingHom.id ℝ) (t⁻¹) N p hdeg
  simp only [invOf_eq_inv] at hstep
  have hmul :
      Polynomial.eval t (p.reflect N) * (t⁻¹) ^ N =
        Polynomial.eval (t⁻¹) p := by
    simpa using hstep
  have hpow : (t⁻¹) ^ N * t ^ N = (1 : ℝ) := by
    rw [← mul_pow]
    simp [ht0]
  calc
    Polynomial.eval t (p.reflect N) =
        (Polynomial.eval t (p.reflect N) * (t⁻¹) ^ N) * t ^ N := by
          rw [mul_assoc, hpow, mul_one]
    _ = Polynomial.eval (t⁻¹) p * t ^ N := by rw [hmul]
    _ = t ^ N * Polynomial.eval (t⁻¹) p := by ring
    _ = Polynomial.eval t p := hrecip t ht0

/-! ## A degree bound for the Cayley numerator

The bound is proved from the homogeneous coefficient expansion, not from a
full-degree assumption.  This is the padding fact needed by `reflect` below.
-/

lemma cayleyNumerator_coeff_sum127 (r : Polynomial ℝ) (d : ℕ) :
    cayleyNumerator127 r d =
      ∑ i ∈ Finset.range (d + 1),
        Polynomial.C (r.coeff i) *
          ((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ i *
          ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (d - i) := by
  classical
  unfold cayleyNumerator127
  induction r using Polynomial.induction_on' with
  | add p q ihp ihq =>
      simp only [Polynomial.homogenize_add, MvPolynomial.eval₂_add,
        Polynomial.coeff_add, map_add]
      rw [ihp, ihq]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  | monomial n a =>
      by_cases hn : n ≤ d
      · rw [Polynomial.homogenize_monomial hn]
        simp only [MvPolynomial.eval₂_monomial]
        rw [Finsupp.prod_fintype]
        · rw [Fin.prod_univ_two]
          simp [cayleySubstitution127]
          rw [Finset.sum_eq_single n]
          · simp
            ring
          · intro i hi hne
            have hne' : n ≠ i := Ne.symm hne
            simp [Polynomial.coeff_monomial, hne']
          · simp [hn]
        · intro i
          by_cases hi : i = 0 <;> simp [hi]
      · rw [Polynomial.homogenize_monomial_of_lt (lt_of_not_ge hn)]
        rw [MvPolynomial.eval₂_zero]
        symm
        apply Finset.sum_eq_zero
        intro i hi
        have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hne : n ≠ i := by omega
        simp [Polynomial.coeff_monomial, hne]

theorem cayleyNumerator_natDegree_le_twice127
    (r : Polynomial ℝ) (d : ℕ) :
    (cayleyNumerator127 r d).natDegree ≤ 2 * d := by
  rw [cayleyNumerator_coeff_sum127]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hi' : i ≤ d := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hleft :
      ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree ≤ 2 := by
    calc
      ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree ≤
          max (1 : Polynomial ℝ).natDegree (Polynomial.X ^ 2).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ = 2 := by simp
  have hright :
      ((1 : Polynomial ℝ) + Polynomial.X ^ 2).natDegree ≤ 2 := by
    calc
      ((1 : Polynomial ℝ) + Polynomial.X ^ 2).natDegree ≤
          max (1 : Polynomial ℝ).natDegree (Polynomial.X ^ 2).natDegree :=
        Polynomial.natDegree_add_le _ _
      _ = 2 := by simp
  calc
    (Polynomial.C (r.coeff i) *
        ((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ i *
        ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (d - i)).natDegree ≤
      (Polynomial.C (r.coeff i) *
        ((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ i).natDegree +
        (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (d - i)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (Polynomial.C (r.coeff i)).natDegree +
          (((1 : Polynomial ℝ) - Polynomial.X ^ 2) ^ i).natDegree +
          (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (d - i)).natDegree := by
      gcongr
      exact Polynomial.natDegree_mul_le
    _ ≤ 0 + 2 * i + 2 * (d - i) := by
      gcongr
      · simp
      · exact Polynomial.natDegree_pow_le.trans
          (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left i hleft)
      · exact Polynomial.natDegree_pow_le.trans
          (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (d - i) hright)
    _ = 2 * d := by omega

/-! ## Concrete fixed-width reflection for the residual -/

def cayleyResidual127 (input : GeneralRealQSPPolynomial127) : Polynomial ℝ :=
  cayleyNumerator127 (intervalResidual127 input) (2 * input.degree)

theorem cayleyResidual127_natDegree_le127
    (input : GeneralRealQSPPolynomial127) :
    (cayleyResidual127 input).natDegree ≤ 4 * input.degree := by
  unfold cayleyResidual127
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (cayleyNumerator_natDegree_le_twice127
      (intervalResidual127 input) (2 * input.degree))

theorem cayleyResidual127_reflect_fixed127
    (input : GeneralRealQSPPolynomial127) :
    (cayleyResidual127 input).reflect (4 * input.degree) =
      cayleyResidual127 input := by
  apply reflect_fixed_of_reciprocal_eval127
      (cayleyResidual127 input) (4 * input.degree)
  · exact cayleyResidual127_natDegree_le127 input
  · intro t ht
    exact cayley_residual_reciprocal_eval127 input t ht

/-! ## Complexification and coefficient conjugation -/

def cayleyResidualComplex127 (input : GeneralRealQSPPolynomial127) : Polynomial ℂ :=
  (cayleyResidual127 input).map Complex.ofRealHom

theorem cayleyResidualComplex127_reflect_fixed127
    (input : GeneralRealQSPPolynomial127) :
    (cayleyResidualComplex127 input).reflect (4 * input.degree) =
      cayleyResidualComplex127 input := by
  unfold cayleyResidualComplex127
  rw [Polynomial.reflect_map]
  rw [cayleyResidual127_reflect_fixed127]

theorem cayleyResidualComplex127_map_star127
    (input : GeneralRealQSPPolynomial127) :
    (cayleyResidualComplex127 input).map (starRingEnd ℂ) =
      cayleyResidualComplex127 input := by
  unfold cayleyResidualComplex127
  rw [Polynomial.map_map]
  ext n
  simp

theorem rootMultiplicity_star_map127
    (p : Polynomial ℂ) (hp : p.map (starRingEnd ℂ) = p) (z : ℂ) :
    Polynomial.rootMultiplicity (star z) p =
      Polynomial.rootMultiplicity z p := by
  have h := Polynomial.eq_rootMultiplicity_map
    (p := p) (f := starRingEnd ℂ) (starRingEnd ℂ).injective z
  simpa [hp] using h.symm

/-! ## Reflection of a nonzero linear factor -/

theorem reflect_linear127 (a : ℂ) :
    ((Polynomial.X : Polynomial ℂ) - Polynomial.C a).reflect 1 =
      1 - Polynomial.C a * Polynomial.X := by
  rw [Polynomial.reflect_sub]
  simp only [Polynomial.reflect_one_X, Polynomial.reflect_C]
  ring

theorem reflect_linear_to_inverse127 (a : ℂ) (ha : a ≠ 0) :
    ((Polynomial.X : Polynomial ℂ) - Polynomial.C a).reflect 1 =
      -Polynomial.C a *
        ((Polynomial.X : Polynomial ℂ) - Polynomial.C a⁻¹) := by
  rw [reflect_linear127]
  have hprod : Polynomial.C a * Polynomial.C a⁻¹ =
      (1 : Polynomial ℂ) := by
    rw [← Polynomial.C_mul]
    simp [ha]
  calc
    1 - Polynomial.C a * Polynomial.X =
        -Polynomial.C a * Polynomial.X + 1 := by ring
    _ = -Polynomial.C a * Polynomial.X +
        Polynomial.C a * Polynomial.C a⁻¹ := by rw [hprod]
    _ = -Polynomial.C a *
        (Polynomial.X - Polynomial.C a⁻¹) := by ring

theorem reflect_factor_pow127 (a : ℂ) (m : ℕ) :
    (((Polynomial.X : Polynomial ℂ) - Polynomial.C a) ^ m).reflect m =
      (((Polynomial.X : Polynomial ℂ) - Polynomial.C a).reflect 1) ^ m := by
  have hlin : ((Polynomial.X : Polynomial ℂ) - Polynomial.C a).natDegree ≤ 1 := by
    simp
  induction m with
  | zero => simp
  | succ m ihm =>
      rw [pow_succ]
      rw [Polynomial.reflect_mul
        (((Polynomial.X : Polynomial ℂ) - Polynomial.C a) ^ m)
        ((Polynomial.X : Polynomial ℂ) - Polynomial.C a)
        (by
          calc
            (((Polynomial.X : Polynomial ℂ) - Polynomial.C a) ^ m).natDegree ≤
                m * 1 := Polynomial.natDegree_pow_le_of_le m hlin
            _ = m := by simp) hlin]
      rw [ihm, pow_succ]

theorem reflect_factor_pow_to_inverse127 (a : ℂ) (ha : a ≠ 0) (m : ℕ) :
    (((Polynomial.X : Polynomial ℂ) - Polynomial.C a) ^ m).reflect m =
      (-Polynomial.C a) ^ m *
        ((Polynomial.X : Polynomial ℂ) - Polynomial.C a⁻¹) ^ m := by
  rw [reflect_factor_pow127, reflect_linear_to_inverse127 a ha, mul_pow]

theorem rootMultiplicity_le_inv_of_reflect_fixed127
    (p : Polynomial ℂ) (N : ℕ) (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ N) (hfix : p.reflect N = p)
    (z : ℂ) (hz : z ≠ 0) :
    p.rootMultiplicity z ≤ p.rootMultiplicity z⁻¹ := by
  obtain ⟨q, hpq, _hq⟩ :=
    p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp z
  have hq0 : q ≠ 0 := by
    intro hq0
    apply hp
    rw [hpq, hq0, mul_zero]
  have hfacdeg :
      (((Polynomial.X : Polynomial ℂ) - Polynomial.C z) ^
          p.rootMultiplicity z).natDegree = p.rootMultiplicity z := by
    rw [(Polynomial.monic_X_sub_C z).natDegree_pow,
      Polynomial.natDegree_X_sub_C, mul_one]
  have hsum :
      p.rootMultiplicity z + q.natDegree = p.natDegree := by
    calc
      p.rootMultiplicity z + q.natDegree =
          (((Polynomial.X : Polynomial ℂ) - Polynomial.C z) ^
            p.rootMultiplicity z).natDegree + q.natDegree := by
              rw [hfacdeg]
      _ = ((((Polynomial.X : Polynomial ℂ) - Polynomial.C z) ^
            p.rootMultiplicity z) * q).natDegree := by
              rw [Polynomial.natDegree_mul]
              · exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero z)
              · exact hq0
      _ = p.natDegree := by rw [← hpq]
  have hmN : p.rootMultiplicity z ≤ N := by omega
  have hqN : q.natDegree ≤ N - p.rootMultiplicity z := by omega
  have hreflect :
      p =
        ((((Polynomial.X : Polynomial ℂ) - Polynomial.C z) ^
          p.rootMultiplicity z).reflect (p.rootMultiplicity z)) *
          q.reflect (N - p.rootMultiplicity z) := by
    calc
      p = p.reflect N := hfix.symm
      _ = ((((Polynomial.X : Polynomial ℂ) - Polynomial.C z) ^
          p.rootMultiplicity z) * q).reflect N := by
            exact congrArg (fun r : Polynomial ℂ => r.reflect N) hpq
      _ = ((((Polynomial.X : Polynomial ℂ) - Polynomial.C z) ^
          p.rootMultiplicity z).reflect (p.rootMultiplicity z)) *
          q.reflect (N - p.rootMultiplicity z) := by
        simpa [Nat.add_sub_of_le hmN] using
          (Polynomial.reflect_mul
            (((Polynomial.X : Polynomial ℂ) - Polynomial.C z) ^
              p.rootMultiplicity z) q hfacdeg.le hqN)
  have hfactor :
      ((((Polynomial.X : Polynomial ℂ) - Polynomial.C z) ^
          p.rootMultiplicity z).reflect (p.rootMultiplicity z)) =
        (-Polynomial.C z) ^ p.rootMultiplicity z *
          ((Polynomial.X : Polynomial ℂ) - Polynomial.C z⁻¹) ^
            p.rootMultiplicity z :=
    reflect_factor_pow_to_inverse127 z hz (p.rootMultiplicity z)
  have hdiv :
      ((Polynomial.X : Polynomial ℂ) - Polynomial.C z⁻¹) ^
          p.rootMultiplicity z ∣ p := by
    refine ⟨(-Polynomial.C z) ^ p.rootMultiplicity z *
        q.reflect (N - p.rootMultiplicity z), ?_⟩
    calc
      p = ((((Polynomial.X : Polynomial ℂ) - Polynomial.C z) ^
          p.rootMultiplicity z).reflect (p.rootMultiplicity z)) *
          q.reflect (N - p.rootMultiplicity z) := hreflect
      _ = ((-Polynomial.C z) ^ p.rootMultiplicity z *
          ((Polynomial.X : Polynomial ℂ) - Polynomial.C z⁻¹) ^
            p.rootMultiplicity z) * q.reflect (N - p.rootMultiplicity z) := by
              rw [hfactor]
      _ = ((Polynomial.X : Polynomial ℂ) - Polynomial.C z⁻¹) ^
          p.rootMultiplicity z *
          ((-Polynomial.C z) ^ p.rootMultiplicity z *
            q.reflect (N - p.rootMultiplicity z)) := by ring
  exact (Polynomial.le_rootMultiplicity_iff hp).2 hdiv

theorem rootMultiplicity_inv_of_reflect_fixed127
    (p : Polynomial ℂ) (N : ℕ) (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ N) (hfix : p.reflect N = p)
    (z : ℂ) (hz : z ≠ 0) :
    p.rootMultiplicity z⁻¹ = p.rootMultiplicity z := by
  apply Nat.le_antisymm
  · simpa [inv_inv] using
      (rootMultiplicity_le_inv_of_reflect_fixed127 p N hp hdeg hfix
        z⁻¹ (inv_ne_zero hz))
  · exact rootMultiplicity_le_inv_of_reflect_fixed127 p N hp hdeg hfix z hz

theorem rootMultiplicity_invStar_cayley127
    (input : GeneralRealQSPPolynomial127) (z : ℂ) :
    (cayleyResidualComplex127 input).rootMultiplicity (invStar127 z) =
      (cayleyResidualComplex127 input).rootMultiplicity z := by
  by_cases hpR : cayleyResidual127 input = 0
  · simp [cayleyResidualComplex127, hpR]
  by_cases hz : z = 0
  · simp [hz, invStar127]
  have hpC : cayleyResidualComplex127 input ≠ 0 := by
    unfold cayleyResidualComplex127
    exact (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hpR
  have hdegC :
      (cayleyResidualComplex127 input).natDegree ≤ 4 * input.degree := by
    unfold cayleyResidualComplex127
    exact Polynomial.natDegree_map_le.trans
      (cayleyResidual127_natDegree_le127 input)
  have hfixC := cayleyResidualComplex127_reflect_fixed127 input
  have hinv := rootMultiplicity_inv_of_reflect_fixed127
    (cayleyResidualComplex127 input) (4 * input.degree) hpC hdegC hfixC
    (star z) (by simp [hz])
  calc
    (cayleyResidualComplex127 input).rootMultiplicity (invStar127 z) =
        (cayleyResidualComplex127 input).rootMultiplicity (star z)⁻¹ := by
          rfl
    _ = (cayleyResidualComplex127 input).rootMultiplicity (star z) := hinv
    _ = (cayleyResidualComplex127 input).rootMultiplicity z :=
      rootMultiplicity_star_map127 (cayleyResidualComplex127 input)
        (cayleyResidualComplex127_map_star127 input) z

theorem cayleyResidualComplex127_roots_invStar_fixed127
    (input : GeneralRealQSPPolynomial127) :
    (cayleyResidualComplex127 input).roots.map invStar127 =
      (cayleyResidualComplex127 input).roots := by
  classical
  have hinj : Function.Injective invStar127 := by
    intro a b hab
    have h := congrArg invStar127 hab
    rw [invStar127_involutive a, invStar127_involutive b] at h
    exact h
  apply (Multiset.ext).2
  intro z
  have hcount := Multiset.count_map_eq_count'
    invStar127 (cayleyResidualComplex127 input).roots hinj (invStar127 z)
  calc
    ((cayleyResidualComplex127 input).roots.map invStar127).count z =
        (cayleyResidualComplex127 input).roots.count (invStar127 z) := by
          simpa only [invStar127_involutive] using hcount
    _ = (cayleyResidualComplex127 input).rootMultiplicity (invStar127 z) :=
      by simp only [Polynomial.count_roots]
    _ = (cayleyResidualComplex127 input).rootMultiplicity z :=
      rootMultiplicity_invStar_cayley127 input z
    _ = (cayleyResidualComplex127 input).roots.count z :=
      by simp only [Polynomial.count_roots]

theorem cayleyNumerator127_roots_invStar_fixed127
    (input : GeneralRealQSPPolynomial127) :
    Multiset.map (fun z : ℂ => ((starRingEnd ℂ) z)⁻¹)
        ((cayleyNumerator127 (intervalResidual127 input)
          (2 * input.degree)).map Complex.ofRealHom).roots =
      ((cayleyNumerator127 (intervalResidual127 input)
          (2 * input.degree)).map Complex.ofRealHom).roots := by
  simpa [cayleyResidualComplex127, cayleyResidual127, invStar127] using
    (cayleyResidualComplex127_roots_invStar_fixed127 input)

end
end SpectralSamplingProof.Analytic
