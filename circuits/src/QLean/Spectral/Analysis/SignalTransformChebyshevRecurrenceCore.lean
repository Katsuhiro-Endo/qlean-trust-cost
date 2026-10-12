import QLean.Spectral.Analysis.SignalTransformPhaseRecurrenceSpecifications

/-!
# Core polynomial reduction for the fixed-point phase word

This pure checkpoint contains only the general recurrence and polynomial
reduction.  Low-degree trigonometry is intentionally kept in the subsequent
S3c-B module.  In particular, the final polynomial equality remains an honest
`Prop`, not a certificate field or an axiom.
-/

namespace SpectralSamplingProof.Analytic

noncomputable section

def fixedPointScaledChebyshevSequence
    (parameters : FixedPointChebyshevParameters)
    (order : ℤ) (failureCoordinate : ℝ) : ℝ :=
  parameters.failureAmplitude *
    Polynomial.eval (parameters.scale * failureCoordinate)
      (Polynomial.Chebyshev.T ℝ order)

theorem fixedPointChebyshevFailureResponse_eq_scaled_sequence
    (parameters : FixedPointChebyshevParameters)
    (successProbability : ℝ) :
    fixedPointChebyshevFailureResponse parameters successProbability =
      fixedPointScaledChebyshevSequence parameters
        (parameters.queryLength : ℤ)
        (fixedPointSourceAmplitude successProbability) := by
  rfl

theorem fixedPointScaledChebyshevSequence_at_one_queryLength
    (parameters : FixedPointChebyshevParameters) :
    fixedPointScaledChebyshevSequence parameters
        (parameters.queryLength : ℤ) 1 = 1 := by
  let u : ℝ :=
    Real.arcosh (1 / parameters.failureAmplitude) /
      (parameters.queryLength : ℝ)
  have queryLength_ne_zero : (parameters.queryLength : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt parameters.queryLength_positive)
  have failureAmplitude_ne_zero : parameters.failureAmplitude ≠ 0 :=
    ne_of_gt parameters.failureAmplitude_positive
  have reciprocal_ge_one : 1 ≤ 1 / parameters.failureAmplitude := by
    apply (le_div_iff₀ parameters.failureAmplitude_positive).2
    simpa using le_of_lt parameters.failureAmplitude_lt_one
  have length_mul_u :
      (parameters.queryLength : ℝ) * u =
        Real.arcosh (1 / parameters.failureAmplitude) := by
    dsimp [u]
    field_simp [queryLength_ne_zero]
  have cosh_arcosh :
      Real.cosh (Real.arcosh (1 / parameters.failureAmplitude)) =
        1 / parameters.failureAmplitude :=
    Real.cosh_arcosh reciprocal_ge_one
  have target_at_scale :
      Polynomial.eval parameters.scale
          (Polynomial.Chebyshev.T ℝ
            (parameters.queryLength : ℤ)) =
        1 / parameters.failureAmplitude := by
    change
      Polynomial.eval (Real.cosh u)
          (Polynomial.Chebyshev.T ℝ
            (parameters.queryLength : ℤ)) = _
    rw [Polynomial.Chebyshev.T_real_cosh]
    rw [show ((parameters.queryLength : ℤ) : ℝ) * u =
      (parameters.queryLength : ℝ) * u by norm_num]
    rw [length_mul_u, cosh_arcosh]
  unfold fixedPointScaledChebyshevSequence
  simp only [mul_one]
  rw [target_at_scale]
  field_simp [failureAmplitude_ne_zero]

end

end SpectralSamplingProof.Analytic
