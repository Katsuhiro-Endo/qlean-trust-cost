import QLean.SignalProcessing.QSPExistenceQSPPhaseExtraction

namespace SpectralSamplingProof.Analytic

noncomputable section

/-! ## A polynomial-valued form of the actual reduced step -/

structure PolynomialReducedState026 where
  sourceFactor : Polynomial ℂ
  targetFactor : Polynomial ℂ

def polynomialReducedStateEval026
    (x : ℂ) (state : PolynomialReducedState026) : FixedPointReducedState where
  sourceFactor := Polynomial.eval x state.sourceFactor
  targetFactor := Polynomial.eval x state.targetFactor

end
end SpectralSamplingProof.Analytic
