import QLean.SignalProcessing.QSPExistenceRealIntervalCompletion

/-!
# Interior roots of the interval residual

This file proves the local sign lemma used by a Markov--Lukacs
factorization.  After the exact root factor is removed, the remaining
quotient has a stable sign in a small metric neighbourhood.  An odd root
factor would then make the nonnegative residual negative on one side of an
interior point.
-/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## Continuity and a controlled interior step -/

lemma polynomial_eval_pos_near127
    (q : Polynomial ℝ) {x : ℝ} (hq : 0 < Polynomial.eval x q) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, dist y x < δ → 0 < Polynomial.eval y q := by
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp (q.continuous.continuousAt))
      (Polynomial.eval x q / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hclose' := hclose hy
  rw [Real.dist_eq] at hclose'
  have hbounds := abs_lt.mp hclose'
  linarith [hbounds.1]

lemma polynomial_eval_neg_near127
    (q : Polynomial ℝ) {x : ℝ} (hq : Polynomial.eval x q < 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, dist y x < δ → Polynomial.eval y q < 0 := by
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.mp (q.continuous.continuousAt))
      (-Polynomial.eval x q / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hclose' := hclose hy
  rw [Real.dist_eq] at hclose'
  have hbounds := abs_lt.mp hclose'
  linarith [hbounds.2]

/-! ## Real-to-complex root pairing -/

/-! ## Endpoint roots are kept separate from interior roots -/

/-! ## The odd-multiplicity contradiction -/

/-! ## The residual specialization and reflection facts -/

end
end SpectralSamplingProof.Analytic
