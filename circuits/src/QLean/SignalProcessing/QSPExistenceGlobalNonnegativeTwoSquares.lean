import QLean.SignalProcessing.QSPExistenceMarkovLukacsRoots
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# Globally nonnegative real polynomials

This scratch source starts the global root-partition boundary needed by a
Markov--Lukacs completion.  The first theorem is independent of the interval
residual: a nonzero real polynomial which is nonnegative on all real inputs
cannot have an odd real root multiplicity.
-/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore
open Filter

noncomputable section

/-! ## A sign-preserving step without interval endpoints -/

lemma global_step127 {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ := by
  refine ⟨δ / 2, ?_, ?_⟩
  · linarith
  · linarith

/-! ## Global evenness of real root multiplicities -/

theorem rootMultiplicity_even_of_nonnegative_global127
    (p : Polynomial ℝ) (hp : p ≠ 0)
    (hnonneg : ∀ y : ℝ, 0 ≤ Polynomial.eval y p)
    {x : ℝ} (_hxroot : p.IsRoot x) :
    Even (p.rootMultiplicity x) := by
  obtain ⟨q, hfactor, hqnotdvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp x
  have hqroot : ¬q.IsRoot x := by
    intro hq
    apply hqnotdvd
    exact (Polynomial.dvd_iff_isRoot).2 hq
  have hqne : Polynomial.eval x q ≠ 0 := by
    intro hq
    apply hqroot
    exact hq
  rcases Nat.even_or_odd (p.rootMultiplicity x) with heven | hodd
  · exact heven
  · exfalso
    rcases lt_or_gt_of_ne hqne with hqneg | hqpos
    · obtain ⟨δ, hδ, hqnear⟩ := polynomial_eval_neg_near127 q hqneg
      obtain ⟨ε, hεpos, hεδ⟩ := global_step127 hδ
      have hdist_right : dist (x + ε) x < δ := by
        rw [Real.dist_eq]
        have heq : (x + ε) - x = ε := by ring
        rw [heq, abs_of_pos hεpos]
        exact hεδ
      have hqright : Polynomial.eval (x + ε) q < 0 :=
        hqnear (x + ε) hdist_right
      have hpowpos : 0 < ε ^ p.rootMultiplicity x :=
        pow_pos hεpos _
      have hp_right :
          Polynomial.eval (x + ε) p =
            ε ^ p.rootMultiplicity x * Polynomial.eval (x + ε) q := by
        calc
          Polynomial.eval (x + ε) p =
              Polynomial.eval (x + ε)
                (((Polynomial.X : Polynomial ℝ) - Polynomial.C x) ^
                  p.rootMultiplicity x * q) := by
              exact congrArg (fun r : Polynomial ℝ => Polynomial.eval (x + ε) r) hfactor
          _ = ((x + ε) - x) ^ p.rootMultiplicity x *
                Polynomial.eval (x + ε) q := by simp
          _ = ε ^ p.rootMultiplicity x * Polynomial.eval (x + ε) q := by
            have heq : (x + ε) - x = ε := by ring
            rw [heq]
      have hpneg : Polynomial.eval (x + ε) p < 0 := by
        rw [hp_right]
        exact mul_neg_of_pos_of_neg hpowpos hqright
      linarith [hnonneg (x + ε)]
    · obtain ⟨δ, hδ, hqnear⟩ := polynomial_eval_pos_near127 q hqpos
      obtain ⟨ε, hεpos, hεδ⟩ := global_step127 hδ
      have hdist_left : dist (x - ε) x < δ := by
        rw [Real.dist_eq]
        have heq : (x - ε) - x = -ε := by ring
        rw [heq, abs_neg, abs_of_pos hεpos]
        exact hεδ
      have hqleft : 0 < Polynomial.eval (x - ε) q :=
        hqnear (x - ε) hdist_left
      have hnegpow : (-ε) ^ p.rootMultiplicity x < 0 := by
        rw [hodd.neg_pow]
        exact neg_lt_zero.mpr (pow_pos hεpos _)
      have hp_left :
          Polynomial.eval (x - ε) p =
            (-ε) ^ p.rootMultiplicity x * Polynomial.eval (x - ε) q := by
        calc
          Polynomial.eval (x - ε) p =
              Polynomial.eval (x - ε)
                (((Polynomial.X : Polynomial ℝ) - Polynomial.C x) ^
                  p.rootMultiplicity x * q) := by
              exact congrArg (fun r : Polynomial ℝ => Polynomial.eval (x - ε) r) hfactor
          _ = ((x - ε) - x) ^ p.rootMultiplicity x *
                Polynomial.eval (x - ε) q := by simp
          _ = (-ε) ^ p.rootMultiplicity x * Polynomial.eval (x - ε) q := by
            have heq : (x - ε) - x = -ε := by ring
            rw [heq]
      have hpneg : Polynomial.eval (x - ε) p < 0 := by
        rw [hp_left]
        exact mul_neg_of_neg_of_pos hnegpow hqleft
      linarith [hnonneg (x - ε)]

/-! ## A finite involution partition, independent of polynomial identities -/

/-! ## Complexification preserves the real-root multiplicity -/

theorem complexify_star_invariant127 (p : Polynomial ℝ) :
    (p.map Complex.ofRealHom).map (starRingEnd ℂ) =
      p.map Complex.ofRealHom := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
      simp [Polynomial.map_add, ihp, ihq]
  | monomial n a =>
      simp

theorem complexified_rootMultiplicity_ofReal127
    (p : Polynomial ℝ) {x : ℝ} :
    (p.map Complex.ofRealHom).rootMultiplicity (x : ℂ) =
      p.rootMultiplicity x := by
  by_cases hp : p = 0
  · simp [hp]
  · obtain ⟨q, hfactor, hqnotdvd⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp x
    have hq : q ≠ 0 := by
      intro hqzero
      apply hqnotdvd
      simp [hqzero]
    have hmapfactor :
        p.map Complex.ofRealHom =
          ((Polynomial.X : Polynomial ℂ) - Polynomial.C (x : ℂ)) ^
              p.rootMultiplicity x * q.map Complex.ofRealHom := by
      calc
        p.map Complex.ofRealHom =
            (((Polynomial.X : Polynomial ℝ) - Polynomial.C x) ^
                p.rootMultiplicity x * q).map Complex.ofRealHom := by
          exact congrArg (fun r : Polynomial ℝ => r.map Complex.ofRealHom) hfactor
        _ = ((Polynomial.X : Polynomial ℂ) - Polynomial.C (x : ℂ)) ^
              p.rootMultiplicity x * q.map Complex.ofRealHom := by
          rw [Polynomial.map_mul, Polynomial.map_pow]
          congr 1
          simp
    have hpmap : p.map Complex.ofRealHom ≠ 0 := by
      intro hpmapzero
      apply hp
      exact (Polynomial.map_eq_zero_iff Complex.ofRealHom.injective).mp hpmapzero
    have hqmap : q.map Complex.ofRealHom ≠ 0 := by
      intro hqmapzero
      apply hq
      exact (Polynomial.map_eq_zero_iff Complex.ofRealHom.injective).mp hqmapzero
    have hqroot :
        ¬(q.map Complex.ofRealHom).IsRoot (x : ℂ) := by
      intro hqrootmap
      apply hqnotdvd
      exact (Polynomial.dvd_iff_isRoot).2
        ((Polynomial.isRoot_map_iff Complex.ofRealHom.injective).mp hqrootmap)
    have hqrm :
        (q.map Complex.ofRealHom).rootMultiplicity (x : ℂ) = 0 := by
      have hnotpos :
          ¬0 < (q.map Complex.ofRealHom).rootMultiplicity (x : ℂ) := by
        intro hpos
        apply hqroot
        exact (Polynomial.rootMultiplicity_pos hqmap).mp hpos
      omega
    have hprod :
        (((Polynomial.X : Polynomial ℂ) - Polynomial.C (x : ℂ)) ^
              p.rootMultiplicity x * q.map Complex.ofRealHom) ≠ 0 := by
      rw [← hmapfactor]
      exact hpmap
    calc
      (p.map Complex.ofRealHom).rootMultiplicity (x : ℂ) =
          (((Polynomial.X : Polynomial ℂ) - Polynomial.C (x : ℂ)) ^
              p.rootMultiplicity x * q.map Complex.ofRealHom).rootMultiplicity (x : ℂ) := by
        exact congrArg
          (fun r : Polynomial ℂ => r.rootMultiplicity (x : ℂ)) hmapfactor
      _ = (((Polynomial.X : Polynomial ℂ) - Polynomial.C (x : ℂ)) ^
              p.rootMultiplicity x).rootMultiplicity (x : ℂ) +
          (q.map Complex.ofRealHom).rootMultiplicity (x : ℂ) := by
        exact Polynomial.rootMultiplicity_mul hprod
      _ = p.rootMultiplicity x := by
        rw [Polynomial.rootMultiplicity_X_sub_C_pow, hqrm, Nat.add_zero]

/-! ## The spectral-factor root multiset -/

def rootProduct127 (s : Multiset ℂ) : Polynomial ℂ :=
  (s.map (fun z => (Polynomial.X : Polynomial ℂ) - Polynomial.C z)).prod

theorem rootProduct_star_map127 (s : Multiset ℂ) :
    (rootProduct127 s).map (starRingEnd ℂ) =
      rootProduct127 (s.map star) := by
  induction s using Multiset.induction_on with
  | empty => simp [rootProduct127]
  | cons a s ih =>
      simp only [rootProduct127, Multiset.map_cons, Multiset.prod_cons]
      rw [Polynomial.map_mul]
      change Polynomial.map (starRingEnd ℂ)
          ((Polynomial.X : Polynomial ℂ) - Polynomial.C a) *
            Polynomial.map (starRingEnd ℂ) (rootProduct127 s) =
        ((Polynomial.X : Polynomial ℂ) - Polynomial.C (star a)) *
          rootProduct127 (Multiset.map star s)
      rw [ih]
      congr 1
      simp [Polynomial.map_sub]

/-! ## The root partition for a complexified nonnegative polynomial -/

theorem complexified_rootMultiplicity_even_of_nonnegative_global127
    (p : Polynomial ℝ) (hp : p ≠ 0)
    (hnonneg : ∀ y : ℝ, 0 ≤ Polynomial.eval y p)
    {z : ℂ} (hzroot : (p.map Complex.ofRealHom).IsRoot z)
    (hzfix : star z = z) :
    Even ((p.map Complex.ofRealHom).rootMultiplicity z) := by
  have hzreal : (z.re : ℂ) = z := by
    exact Complex.conj_eq_iff_re.mp hzfix
  have hzroot_real :
      (p.map Complex.ofRealHom).IsRoot (z.re : ℂ) := by
    rw [hzreal]
    exact hzroot
  have hroot_real : p.IsRoot z.re :=
    (Polynomial.isRoot_map_iff Complex.ofRealHom.injective).mp hzroot_real
  have heven_real : Even (p.rootMultiplicity z.re) :=
    rootMultiplicity_even_of_nonnegative_global127 p hp hnonneg hroot_real
  rw [← hzreal, complexified_rootMultiplicity_ofReal127]
  exact heven_real

theorem complexified_roots_star_closed127
    (p : Polynomial ℝ) :
    Multiset.map star (p.map Complex.ofRealHom).roots =
      (p.map Complex.ofRealHom).roots := by
  have hsplit : (p.map Complex.ofRealHom).Splits :=
    IsAlgClosed.splits (p.map Complex.ofRealHom)
  have hroots :=
    hsplit.roots_map (starRingEnd ℂ)
  rw [complexify_star_invariant127 p] at hroots
  change Multiset.map (⇑(starRingEnd ℂ))
      (p.map Complex.ofRealHom).roots =
    (p.map Complex.ofRealHom).roots
  exact hroots.symm

/-! ## Root products and leading-coefficient normalization -/

theorem rootProduct_add127 (s t : Multiset ℂ) :
    rootProduct127 (s + t) = rootProduct127 s * rootProduct127 t := by
  simp [rootProduct127, Multiset.map_add, Multiset.prod_add]

def spectralFactor127
    (p : Polynomial ℝ) (q : Multiset ℂ) : Polynomial ℂ :=
  Polynomial.C (Real.sqrt p.leadingCoeff : ℂ) * rootProduct127 q

theorem complex_spectral_factor_of_root_partition127
    (p : Polynomial ℝ) (_hp : p ≠ 0)
    (hcoeff : 0 ≤ p.leadingCoeff)
    {q : Multiset ℂ}
    (hpartition :
      (p.map Complex.ofRealHom).roots = q + Multiset.map star q) :
    p.map Complex.ofRealHom =
      spectralFactor127 p q *
        (spectralFactor127 p q).map (starRingEnd ℂ) := by
  have hsplit : (p.map Complex.ofRealHom).Splits :=
    IsAlgClosed.splits (p.map Complex.ofRealHom)
  have hrootfactor :
      p.map Complex.ofRealHom =
        Polynomial.C (p.leadingCoeff : ℂ) *
          (rootProduct127 q *
            (rootProduct127 q).map (starRingEnd ℂ)) := by
    calc
      p.map Complex.ofRealHom =
          Polynomial.C (p.map Complex.ofRealHom).leadingCoeff *
            rootProduct127 (p.map Complex.ofRealHom).roots := by
        simpa [rootProduct127] using
          (Polynomial.Splits.eq_prod_roots hsplit)
      _ = Polynomial.C (p.leadingCoeff : ℂ) *
            rootProduct127 (q + Multiset.map star q) := by
        rw [hpartition, Polynomial.leadingCoeff_map]
        rfl
      _ = Polynomial.C (p.leadingCoeff : ℂ) *
            (rootProduct127 q * rootProduct127 (Multiset.map star q)) := by
        rw [rootProduct_add127]
      _ = Polynomial.C (p.leadingCoeff : ℂ) *
            (rootProduct127 q *
              (rootProduct127 q).map (starRingEnd ℂ)) := by
        rw [rootProduct_star_map127]
  have hsqrt : (Real.sqrt p.leadingCoeff : ℝ) ^ 2 = p.leadingCoeff :=
    Real.sq_sqrt hcoeff
  have hsqrtC :
      (Real.sqrt p.leadingCoeff : ℂ) ^ 2 = (p.leadingCoeff : ℂ) := by
    rw [← Complex.ofReal_pow, hsqrt]
  have hproduct :
      spectralFactor127 p q *
          (spectralFactor127 p q).map (starRingEnd ℂ) =
        p.map Complex.ofRealHom := by
    calc
      spectralFactor127 p q *
          (spectralFactor127 p q).map (starRingEnd ℂ) =
          (Polynomial.C (Real.sqrt p.leadingCoeff : ℂ) * rootProduct127 q) *
            (Polynomial.C (Real.sqrt p.leadingCoeff : ℂ) *
              (rootProduct127 q).map (starRingEnd ℂ)) := by
        simp [spectralFactor127, Polynomial.map_mul,
          Polynomial.map_C, rootProduct_star_map127]
      _ = (Polynomial.C (Real.sqrt p.leadingCoeff : ℂ) *
            Polynomial.C (Real.sqrt p.leadingCoeff : ℂ)) *
            (rootProduct127 q *
              (rootProduct127 q).map (starRingEnd ℂ)) := by
        ring
      _ = Polynomial.C ((Real.sqrt p.leadingCoeff : ℂ) ^ 2) *
            (rootProduct127 q *
              (rootProduct127 q).map (starRingEnd ℂ)) := by
        rw [← Polynomial.C_mul]
        simp only [pow_two]
      _ = Polynomial.C (p.leadingCoeff : ℂ) *
            (rootProduct127 q *
              (rootProduct127 q).map (starRingEnd ℂ)) := by
        rw [hsqrtC]
      _ = p.map Complex.ofRealHom := hrootfactor.symm
  exact hproduct.symm

def realPartPolynomial127 (q : Polynomial ℂ) : Polynomial ℝ :=
  Polynomial.ofFinsupp
    (AddMonoidAlgebra.ofCoeff
      (Finsupp.mapRange Complex.re (by simp) q.toFinsupp.coeff))

def imagPartPolynomial127 (q : Polynomial ℂ) : Polynomial ℝ :=
  Polynomial.ofFinsupp
    (AddMonoidAlgebra.ofCoeff
      (Finsupp.mapRange Complex.im (by simp) q.toFinsupp.coeff))

theorem complex_coeff_decomposition127 (z : ℂ) :
    z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
  apply Complex.ext <;> simp

theorem polynomial_coeff_decomposition127 (q : Polynomial ℂ) :
    q =
      (realPartPolynomial127 q).map Complex.ofRealHom +
        Polynomial.C Complex.I * (imagPartPolynomial127 q).map Complex.ofRealHom := by
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_add, Polynomial.coeff_map,
    Polynomial.coeff_C_mul, realPartPolynomial127,
    imagPartPolynomial127, Polynomial.coeff_ofFinsupp,
    Finsupp.mapRange_apply]
  exact complex_coeff_decomposition127 (q.coeff n)

theorem polynomial_star_decomposition127 (q : Polynomial ℂ) :
    q.map (starRingEnd ℂ) =
      (realPartPolynomial127 q).map Complex.ofRealHom -
        Polynomial.C Complex.I *
          (imagPartPolynomial127 q).map Complex.ofRealHom := by
  calc
    q.map (starRingEnd ℂ) =
        ((realPartPolynomial127 q).map Complex.ofRealHom +
          Polynomial.C Complex.I *
            (imagPartPolynomial127 q).map Complex.ofRealHom).map
              (starRingEnd ℂ) := by
      exact congrArg (fun r : Polynomial ℂ => r.map (starRingEnd ℂ))
        (polynomial_coeff_decomposition127 q)
    _ = (realPartPolynomial127 q).map Complex.ofRealHom -
          Polynomial.C Complex.I *
            (imagPartPolynomial127 q).map Complex.ofRealHom := by
      have hreal (a : Polynomial ℝ) :
          (a.map Complex.ofRealHom).map (starRingEnd ℂ) =
            a.map Complex.ofRealHom := by
        rw [Polynomial.map_map]
        congr 1
        ext x
        simp
      have himag (a : Polynomial ℝ) :
          (a.map Complex.ofRealHom).map (starRingEnd ℂ) =
            a.map Complex.ofRealHom := by
        exact hreal a
      have hstarI : (starRingEnd ℂ) Complex.I = -Complex.I := by
        apply Complex.ext <;> simp
      have hCneg : Polynomial.C (-Complex.I) = -Polynomial.C Complex.I := by
        rw [Polynomial.C_neg]
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        hreal, himag, hstarI, hCneg]
      ring

theorem real_two_squares_of_complex_factor127
    (p : Polynomial ℝ) (q : Polynomial ℂ)
    (hfactor : p.map Complex.ofRealHom =
      q * q.map (starRingEnd ℂ)) :
    p = realPartPolynomial127 q ^ 2 + imagPartPolynomial127 q ^ 2 := by
  let a : Polynomial ℂ :=
    (realPartPolynomial127 q).map Complex.ofRealHom
  let b : Polynomial ℂ :=
    (imagPartPolynomial127 q).map Complex.ofRealHom
  have hq : q = a + Polynomial.C Complex.I * b := by
    exact polynomial_coeff_decomposition127 q
  have hqstar : q.map (starRingEnd ℂ) = a - Polynomial.C Complex.I * b := by
    exact polynomial_star_decomposition127 q
  have hprod :
      q * q.map (starRingEnd ℂ) =
        (a + Polynomial.C Complex.I * b) *
          (a - Polynomial.C Complex.I * b) := by
    exact congrArg₂ (fun u v : Polynomial ℂ => u * v) hq hqstar
  have hI2 : (Polynomial.C Complex.I : Polynomial ℂ) ^ 2 = -1 := by
    rw [pow_two, ← Polynomial.C_mul]
    simp
  have hsum :
      (a + Polynomial.C Complex.I * b) *
          (a - Polynomial.C Complex.I * b) = a ^ 2 + b ^ 2 := by
    ring_nf
    rw [hI2]
    ring
  have hmapsum :
      (realPartPolynomial127 q ^ 2 +
          imagPartPolynomial127 q ^ 2).map Complex.ofRealHom =
        a ^ 2 + b ^ 2 := by
    simp [a, b, Polynomial.map_add, Polynomial.map_pow]
  have hmap :
      p.map Complex.ofRealHom =
        (realPartPolynomial127 q ^ 2 +
          imagPartPolynomial127 q ^ 2).map Complex.ofRealHom := by
    calc
      p.map Complex.ofRealHom = q * q.map (starRingEnd ℂ) := hfactor
      _ = (a + Polynomial.C Complex.I * b) *
            (a - Polynomial.C Complex.I * b) := hprod
      _ = a ^ 2 + b ^ 2 := hsum
      _ = (realPartPolynomial127 q ^ 2 +
          imagPartPolynomial127 q ^ 2).map Complex.ofRealHom := hmapsum.symm
  exact (Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective) hmap

theorem leadingCoeff_nonneg_of_nonnegative_global127
    (p : Polynomial ℝ) (hp : p ≠ 0)
    (hnonneg : ∀ y : ℝ, 0 ≤ Polynomial.eval y p) :
    0 ≤ p.leadingCoeff := by
  by_cases hdeg : p.degree = 0
  · have h0 := hnonneg 0
    rw [Polynomial.eq_C_of_degree_eq_zero hdeg, Polynomial.eval_C] at h0
    have hnd : p.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hdeg.le
    rw [← Polynomial.coeff_natDegree, hnd]
    exact h0
  · have hdegpos : 0 < p.degree :=
      lt_of_le_of_ne (by
        rw [Polynomial.degree_eq_natDegree hp]
        exact WithBot.coe_nonneg.mpr (Nat.zero_le _)) (Ne.symm hdeg)
    by_contra hnot
    have hlt : p.leadingCoeff < 0 := lt_of_not_ge hnot
    have ht : Tendsto (fun x : ℝ => Polynomial.eval x p) atTop atBot :=
      p.tendsto_atBot_of_leadingCoeff_nonpos hdegpos hlt.le
    have hevneg : ∀ᶠ x : ℝ in atTop,
        Polynomial.eval x p < 0 :=
      ht.eventually (eventually_lt_atBot (0 : ℝ))
    have hevnon : ∀ᶠ x : ℝ in atTop,
        0 ≤ Polynomial.eval x p :=
      Filter.Eventually.of_forall hnonneg
    have hevfalse : ∀ᶠ x : ℝ in atTop, False :=
      hevneg.and hevnon |>.mono (fun x hx =>
        (not_lt_of_ge hx.2) hx.1)
    obtain ⟨x, hx⟩ := Filter.Eventually.exists hevfalse
    exact hx

theorem realPart_natDegree_le127 (q : Polynomial ℂ) :
    (realPartPolynomial127 q).natDegree ≤ q.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hzero : q.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hn
  simp only [realPartPolynomial127, Polynomial.coeff_ofFinsupp,
    Finsupp.mapRange_apply]
  have hzero' : q.toFinsupp.coeff n = 0 := hzero
  rw [hzero']
  rfl

theorem imagPart_natDegree_le127 (q : Polynomial ℂ) :
    (imagPartPolynomial127 q).natDegree ≤ q.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hzero : q.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hn
  simp only [imagPartPolynomial127, Polynomial.coeff_ofFinsupp,
    Finsupp.mapRange_apply]
  have hzero' : q.toFinsupp.coeff n = 0 := hzero
  rw [hzero']
  rfl

theorem rootProduct_natDegree_le127 (s : Multiset ℂ) :
    (rootProduct127 s).natDegree ≤ s.card := by
  rw [rootProduct127]
  calc
    ((s.map (fun z : ℂ =>
        (Polynomial.X : Polynomial ℂ) - Polynomial.C z)).prod).natDegree ≤
        (s.map (fun z : ℂ =>
          ((Polynomial.X : Polynomial ℂ) - Polynomial.C z).natDegree)).sum :=
      (by
        simpa only [Multiset.map_map, Function.comp_def] using
          (Polynomial.natDegree_multiset_prod_le
            (s.map (fun z : ℂ =>
              (Polynomial.X : Polynomial ℂ) - Polynomial.C z))))
    _ = s.card := by simp

theorem spectralFactor_natDegree_le127
    (p : Polynomial ℝ) (s : Multiset ℂ) :
    (spectralFactor127 p s).natDegree ≤ s.card := by
  unfold spectralFactor127
  calc
    (Polynomial.C (Real.sqrt p.leadingCoeff : ℂ) * rootProduct127 s).natDegree ≤
        (Polynomial.C (Real.sqrt p.leadingCoeff : ℂ)).natDegree +
          (rootProduct127 s).natDegree := Polynomial.natDegree_mul_le
    _ ≤ s.card := by simp [rootProduct_natDegree_le127]

/-! ## A Cayley/homogenization bridge for interval nonnegativity -/

def cayleySubstitution127 : Fin 2 → Polynomial ℝ :=
  fun i => if i = 0 then
    (1 : Polynomial ℝ) - Polynomial.X ^ 2
  else (1 : Polynomial ℝ) + Polynomial.X ^ 2

def cayleyNumerator127 (r : Polynomial ℝ) (d : ℕ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C cayleySubstitution127
    (Polynomial.homogenize r d)

theorem cayley_eval127 (r : Polynomial ℝ) (d : ℕ) (t : ℝ) :
    Polynomial.eval t (cayleyNumerator127 r d) =
      MvPolynomial.eval
        (fun i : Fin 2 =>
          if i = 0 then (1 - t ^ 2 : ℝ) else (1 + t ^ 2))
        (Polynomial.homogenize r d) := by
  unfold cayleyNumerator127
  rw [MvPolynomial.polynomial_eval_eval₂]
  congr 1
  · ext x
    simp
  · funext i
    by_cases hi : i = 0 <;>
      simp [cayleySubstitution127, hi, Polynomial.eval_sub,
        Polynomial.eval_add, Polynomial.eval_pow]

theorem cayley_eval_homogenized127
    (r : Polynomial ℝ) (d : ℕ) (hd : r.natDegree ≤ d) (t : ℝ) :
    Polynomial.eval t (cayleyNumerator127 r d) =
      Polynomial.eval ((1 - t ^ 2) / (1 + t ^ 2)) r *
        (1 + t ^ 2) ^ d := by
  rw [cayley_eval127]
  apply Polynomial.eval_homogenize hd
  · simp
    nlinarith [sq_nonneg t]

theorem cayley_even127
    (r : Polynomial ℝ) (d : ℕ) (hd : r.natDegree ≤ d) (t : ℝ) :
    Polynomial.eval (-t) (cayleyNumerator127 r d) =
      Polynomial.eval t (cayleyNumerator127 r d) := by
  rw [cayley_eval_homogenized127 r d hd (-t)]
  rw [cayley_eval_homogenized127 r d hd t]
  have hsq : (-t : ℝ) ^ 2 = t ^ 2 := by ring
  simp [hsq]

theorem cayley_nonnegative127
    (r : Polynomial ℝ) (d : ℕ) (hd : r.natDegree ≤ d)
    (hnonneg : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → 0 ≤ Polynomial.eval x r) :
    ∀ t : ℝ, 0 ≤ Polynomial.eval t (cayleyNumerator127 r d) := by
  intro t
  have hden : 0 < (1 + t ^ 2 : ℝ) := by
    nlinarith [sq_nonneg t]
  have hlower : (-1 : ℝ) ≤ (1 - t ^ 2) / (1 + t ^ 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg t]
  have hupper : (1 - t ^ 2) / (1 + t ^ 2) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg t]
  rw [cayley_eval_homogenized127 r d hd t]
  exact mul_nonneg (hnonneg _ hlower hupper) (pow_nonneg hden.le d)

end
end SpectralSamplingProof.Analytic
