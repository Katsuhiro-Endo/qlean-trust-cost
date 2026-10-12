import QLean.SignalProcessing.QSPExistenceGeneralQSPExistence

/-!
# Real interval completion boundary

This file isolates the algebraic first step of a real QSP completion.  The
completion witness is typed data: its degree and parity obligations are
explicit, and the zero polynomial uses the `WithBot` degree.  The proved part
records the exact residual polynomial `1 - P^2`, its interval
non-negativity, and its evenness.  These facts are the inputs needed by a
later Markov--Lukacs/Fejer--Riesz factorization proof.
-/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## The residual polynomial -/

/-- The real residual associated with a bounded real QSP polynomial. -/
def intervalResidual127
    (input : GeneralRealQSPPolynomial127) : Polynomial ℝ :=
  (1 : Polynomial ℝ) - input.polynomial ^ 2

theorem intervalResidual127_eval
    (input : GeneralRealQSPPolynomial127) (x : ℝ) :
    Polynomial.eval x (intervalResidual127 input) =
      1 - (Polynomial.eval x input.polynomial) ^ 2 := by
  simp [intervalResidual127]

theorem intervalResidual127_bounds
    (input : GeneralRealQSPPolynomial127)
    {x : ℝ} (lower : -1 ≤ x) (upper : x ≤ 1) :
    -1 ≤ Polynomial.eval x input.polynomial ∧
      Polynomial.eval x input.polynomial ≤ 1 := by
  have habs := input.bounded_on_unitInterval x lower upper
  constructor
  · exact le_trans (neg_le_neg habs) (neg_abs_le _)
  · exact le_trans (le_abs_self _) habs

theorem intervalResidual127_nonnegative
    (input : GeneralRealQSPPolynomial127)
    {x : ℝ} (lower : -1 ≤ x) (upper : x ≤ 1) :
    0 ≤ Polynomial.eval x (intervalResidual127 input) := by
  rw [intervalResidual127_eval]
  have hb := intervalResidual127_bounds input lower upper
  nlinarith [sq_nonneg (Polynomial.eval x input.polynomial)]

theorem intervalResidual127_even
    (input : GeneralRealQSPPolynomial127) (x : ℝ) :
    Polynomial.eval (-x) (intervalResidual127 input) =
      Polynomial.eval x (intervalResidual127 input) := by
  rw [intervalResidual127_eval, intervalResidual127_eval]
  have hp := input.parity_law x
  by_cases hdegree : input.degree % 2 = 0
  · simp [hdegree] at hp
    rw [hp]
  · simp [hdegree] at hp
    rw [hp]
    ring

/-! ## The typed factorization target -/

/-- Degree/parity data required by the later degree-reducing QSP extraction.

The fields are requirements on a witness, not facts silently attached to a
runtime phase plan.  The `WithBot` degree bounds make zero components valid at
degree zero, and the two parity laws are opposite as required by the
Markov--Lukacs decomposition. -/
structure IntervalCompletionWitness127
    (input : GeneralRealQSPPolynomial127) where
  B : Polynomial ℝ
  C : Polynomial ℝ
  identity : intervalResidual127 input =
    B ^ 2 + (1 - (Polynomial.X : Polynomial ℝ) ^ 2) * C ^ 2
  B_degree : B.degree ≤ (input.degree : WithBot ℕ)
  C_degree : C.degree < (input.degree : WithBot ℕ)
  B_parity : ∀ x : ℝ,
    Polynomial.eval (-x) B =
      if input.degree % 2 = 0 then Polynomial.eval x B
      else -Polynomial.eval x B
  C_parity : ∀ x : ℝ,
    Polynomial.eval (-x) C =
      if input.degree % 2 = 0 then -Polynomial.eval x C
      else Polynomial.eval x C

/-! ## Small fully-applied inputs -/

/-! ## Explicit factorization sanity cases -/

/-! ## Fully inhabited regression witnesses -/

end
end SpectralSamplingProof.Analytic
