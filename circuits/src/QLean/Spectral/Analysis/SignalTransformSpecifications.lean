import QLean.Circuits.Foundation.FinitePhaseTransformAnalytic

/-! Circuit-independent scalar-response and phase-word vocabulary. -/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## S1: target scalar response -/

inductive SignalResponseParity where
  | even
  | odd
  | unrestricted
  deriving DecidableEq, Repr

/-- The scientific scalar function `P(x)` and the domain on which it is used. -/
structure TargetScalarResponseSpecification where
  parameterDomain : ℝ → Prop
  response : ℝ → ℝ
  parity : SignalResponseParity

def TargetScalarResponseSpecification.parityLaw
    (target : TargetScalarResponseSpecification) : Prop :=
  match target.parity with
  | .even => ∀ value, target.response (-value) = target.response value
  | .odd => ∀ value, target.response (-value) = -target.response value
  | .unrestricted => True

/-! ## S2: degree and query length -/

/-! ## S3: mathematical phase synthesis -/

/-! ## S4: phase-convention conversion -/

/-! ## S5: exact recorded finite product -/

/-! ## S6: strong block-encoding transformation -/

/-! ## S7: ideal response and non-duplicated error certificate -/

end

end SpectralSamplingProof.Analytic
