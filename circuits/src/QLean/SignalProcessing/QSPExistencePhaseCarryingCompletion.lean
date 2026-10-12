import QLean.SignalProcessing.QSPExistenceCompletionPairExtractionMap

namespace SpectralSamplingProof.Analytic

noncomputable section

/-!  A phase-carrying polynomial column.  Its first coordinate is the
    evaluator-native complex readout `P + I B`; its second coordinate is the
    real residual factor `C`.  The positive square-root matrix entry from the
    previous stage is intentionally not used. -/

def completionPhaseCarryingState028
    (input : GeneralRealQSPPolynomial127) : PolynomialReducedState026 where
  sourceFactor :=
    (completionPair024 input).P.map Complex.ofRealHom +
      Polynomial.C Complex.I *
        (completionPair024 input).B.map Complex.ofRealHom
  targetFactor :=
    (completionPair024 input).C.map Complex.ofRealHom

theorem completionPhaseCarryingState028_source_eval
    (input : GeneralRealQSPPolynomial127) (x : ℝ) :
    (polynomialReducedStateEval026 (x : ℂ)
        (completionPhaseCarryingState028 input)).sourceFactor =
      ((Polynomial.eval x (completionPair024 input).P : ℝ) : ℂ) +
        Complex.I * ((Polynomial.eval x (completionPair024 input).B : ℝ) : ℂ) := by
  change Polynomial.eval (x : ℂ)
      ((completionPair024 input).P.map Complex.ofRealHom +
        Polynomial.C Complex.I *
          (completionPair024 input).B.map Complex.ofRealHom) = _
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [eval_real_map_complex027, eval_real_map_complex027]

theorem completionPhaseCarryingState028_target_eval
    (input : GeneralRealQSPPolynomial127) (x : ℝ) :
    (polynomialReducedStateEval026 (x : ℂ)
        (completionPhaseCarryingState028 input)).targetFactor =
      ((Polynomial.eval x (completionPair024 input).C : ℝ) : ℂ) := by
  change Polynomial.eval (x : ℂ)
      ((completionPair024 input).C.map Complex.ofRealHom) = _
  exact eval_real_map_complex027 _ _

theorem completionPhaseCarryingState028_weighted_norm
    (input : GeneralRealQSPPolynomial127) (x : ℝ) :
    Complex.normSq ((polynomialReducedStateEval026 (x : ℂ)
        (completionPhaseCarryingState028 input)).sourceFactor) +
      (1 - x ^ 2) *
        Complex.normSq ((polynomialReducedStateEval026 (x : ℂ)
          (completionPhaseCarryingState028 input)).targetFactor) =
      1 := by
  rw [completionPhaseCarryingState028_source_eval,
    completionPhaseCarryingState028_target_eval]
  simp [Complex.normSq_apply]
  have h := completionPair_eval_identity024 input x
  nlinarith

end
end SpectralSamplingProof.Analytic
