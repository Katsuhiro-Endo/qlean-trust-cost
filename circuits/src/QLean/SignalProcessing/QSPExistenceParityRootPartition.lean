import QLean.SignalProcessing.QSPExistenceGlobalNonnegativeTwoSquares
import QLean.SignalProcessing.QSPExistenceRealIntervalCompletion

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## Orbit chunks for the commuting star/negation action -/

lemma star_involutive127 : Function.Involutive (starRingEnd ℂ) := by
  intro z
  simp

lemma neg_injective127 : Function.Injective (fun z : ℂ => -z) := by
  intro x y h
  simpa using congrArg Neg.neg h

/-! ## Cayley root closure for an even real polynomial -/

theorem cayley_even_polynomial127
    (r : Polynomial ℝ) (d : ℕ) (hd : r.natDegree ≤ d) :
    (cayleyNumerator127 r d).comp (-(Polynomial.X : Polynomial ℝ)) =
      cayleyNumerator127 r d := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_comp]
  simpa using cayley_even127 r d hd t

theorem complexified_cayley_even_polynomial127
    (r : Polynomial ℝ) (d : ℕ) (hd : r.natDegree ≤ d) :
    ((cayleyNumerator127 r d).map Complex.ofRealHom).comp
        (-(Polynomial.X : Polynomial ℂ)) =
      (cayleyNumerator127 r d).map Complex.ofRealHom := by
  have hnegmap :
      Polynomial.map Complex.ofRealHom (-(Polynomial.X : Polynomial ℝ)) =
        -(Polynomial.X : Polynomial ℂ) := by
    ext n
    simp
  rw [← hnegmap]
  rw [← Polynomial.map_comp]
  rw [cayley_even_polynomial127 r d hd]

theorem complexified_cayley_roots_neg_closed127
    (r : Polynomial ℝ) (d : ℕ) (hd : r.natDegree ≤ d) :
    Multiset.map (fun z : ℂ => -z)
        ((cayleyNumerator127 r d).map Complex.ofRealHom).roots =
      ((cayleyNumerator127 r d).map Complex.ofRealHom).roots := by
  rw [← Polynomial.roots_comp_neg_X]
  rw [complexified_cayley_even_polynomial127 r d hd]

theorem intervalResidual127_natDegree_le_twice127
    (input : GeneralRealQSPPolynomial127) :
    (intervalResidual127 input).natDegree ≤ 2 * input.degree := by
  unfold intervalResidual127
  calc
    ((1 : Polynomial ℝ) - input.polynomial ^ 2).natDegree ≤
        max (1 : Polynomial ℝ).natDegree (input.polynomial ^ 2).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ max 0 (2 * input.polynomial.natDegree) := by
      apply max_le_max
      · simp
      · exact Polynomial.natDegree_pow_le
    _ ≤ 2 * input.degree := by
      apply max_le
      · omega
      · exact Nat.mul_le_mul_left 2 input.degree_bound

theorem cayley_residual_reciprocal_eval127
    (input : GeneralRealQSPPolynomial127) (t : ℝ) (ht : t ≠ 0) :
    t ^ (4 * input.degree) *
        Polynomial.eval (t⁻¹)
          (cayleyNumerator127 (intervalResidual127 input) (2 * input.degree)) =
      Polynomial.eval t
        (cayleyNumerator127 (intervalResidual127 input) (2 * input.degree)) := by
  have hd : (intervalResidual127 input).natDegree ≤ 2 * input.degree :=
    intervalResidual127_natDegree_le_twice127 input
  rw [cayley_eval_homogenized127 _ _ hd (t⁻¹)]
  rw [cayley_eval_homogenized127 _ _ hd t]
  have hden : (1 + t ^ 2 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg t]
  have hinv : (t⁻¹) ^ 2 = (t ^ 2)⁻¹ := by
    simp [pow_two]
  have harg :
      (1 - (t⁻¹) ^ 2) / (1 + (t⁻¹) ^ 2) =
        -((1 - t ^ 2) / (1 + t ^ 2)) := by
    rw [hinv]
    field_simp [ht, hden]
    ring
  have heven :
      Polynomial.eval
          (-((1 - t ^ 2) / (1 + t ^ 2)))
          (intervalResidual127 input) =
        Polynomial.eval ((1 - t ^ 2) / (1 + t ^ 2))
          (intervalResidual127 input) := by
    exact intervalResidual127_even input _
  rw [harg, heven]
  have hinvden :
      1 + (t⁻¹) ^ 2 = (1 + t ^ 2) / (t ^ 2) := by
    field_simp [ht]
    ring
  have htpow : (t ^ 2) ^ (2 * input.degree) =
      t ^ (4 * input.degree) := by
    rw [← pow_mul]
    congr 1
    ring
  have hscalar :
      t ^ (4 * input.degree) * (1 + (t⁻¹) ^ 2) ^
          (2 * input.degree) =
        (1 + t ^ 2) ^ (2 * input.degree) := by
    rw [hinvden, div_pow, htpow]
    field_simp [ht]
  calc
    t ^ (4 * input.degree) *
          (Polynomial.eval ((1 - t ^ 2) / (1 + t ^ 2))
            (intervalResidual127 input) *
          (1 + (t⁻¹) ^ 2) ^ (2 * input.degree)) =
        Polynomial.eval ((1 - t ^ 2) / (1 + t ^ 2))
            (intervalResidual127 input) *
          (t ^ (4 * input.degree) *
            (1 + (t⁻¹) ^ 2) ^ (2 * input.degree)) := by ring
    _ = Polynomial.eval ((1 - t ^ 2) / (1 + t ^ 2))
            (intervalResidual127 input) *
          (1 + t ^ 2) ^ (2 * input.degree) := by rw [hscalar]

end
end SpectralSamplingProof.Analytic
