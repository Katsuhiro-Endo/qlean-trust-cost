import QLean.SignalProcessing.QSPExistencePolynomialActualStepBridge

namespace SpectralSamplingProof.Analytic

noncomputable section

/-!  The accepted completion contributes the real polynomial entries `P`, `B`,
    and `C`.  The state below deliberately records the polynomial residual
    companion `B` as its second coordinate; the matrix target entry is kept
    separate because it is a square root, not silently identified with `B`. -/

theorem eval_real_map_complex027
    (p : Polynomial ℝ) (x : ℝ) :
    Polynomial.eval (x : ℂ) (p.map Complex.ofRealHom) =
      ((Polynomial.eval x p : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  simpa using (Polynomial.eval₂_at_apply (p := p) Complex.ofRealHom x)

end
end SpectralSamplingProof.Analytic
