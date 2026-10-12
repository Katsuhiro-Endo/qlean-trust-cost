import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Pure scalar responses used by signal-transform applications

This module contains only real-valued response data.  It deliberately has no
finite-phase operator, scientific-ledger, R3, circuit, or application-root
dependency.
-/

namespace SpectralSamplingProof.Analytic

noncomputable section

def chebyshevT (order : Nat) (value : ℝ) : ℝ :=
  Polynomial.eval value (Polynomial.Chebyshev.T ℝ (order : ℕ))

structure FixedPointChebyshevParameters where
  failureAmplitude : ℝ
  queryLength : Nat
  failureAmplitude_positive : 0 < failureAmplitude
  failureAmplitude_lt_one : failureAmplitude < 1
  queryLength_positive : 0 < queryLength
  queryLength_odd : queryLength % 2 = 1

def FixedPointChebyshevParameters.scale
    (parameters : FixedPointChebyshevParameters) : ℝ :=
  Real.cosh
    (Real.arcosh (1 / parameters.failureAmplitude) /
      (parameters.queryLength : ℝ))

def FixedPointChebyshevParameters.transitionWidth
    (parameters : FixedPointChebyshevParameters) : ℝ :=
  Real.tanh
    (Real.arcosh (1 / parameters.failureAmplitude) /
      (parameters.queryLength : ℝ)) ^ 2

def fixedPointChebyshevFailureResponse
    (parameters : FixedPointChebyshevParameters)
    (successProbability : ℝ) : ℝ :=
  parameters.failureAmplitude *
    chebyshevT parameters.queryLength
      (parameters.scale * Real.sqrt (max 0 (1 - successProbability)))

end

end SpectralSamplingProof.Analytic
