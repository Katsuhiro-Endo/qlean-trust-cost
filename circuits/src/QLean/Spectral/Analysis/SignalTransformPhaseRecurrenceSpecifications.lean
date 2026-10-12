import QLean.Spectral.Analysis.SignalTransformPhaseScheduleSpecifications

/-!
# Algebraic recurrence behind a fixed-point phase word

This pure module removes the 2-by-2 matrix bookkeeping from the remaining
Chebyshev proof.  After the initial signal query, every state has the form

`(bad * sourceFactor, good * targetFactor)`.

The recurrence below is derived from the exact S3a source word, not postulated
as a response certificate.  Its `sourceFactor` is the sole polynomial/Laurent
quantity which the subsequent Chebyshev induction must identify.
-/

namespace SpectralSamplingProof.Analytic

noncomputable section

/-- Reduced coordinates after factoring out the physical bad/good amplitudes. -/
structure FixedPointReducedState where
  sourceFactor : ℂ
  targetFactor : ℂ

end

end SpectralSamplingProof.Analytic
