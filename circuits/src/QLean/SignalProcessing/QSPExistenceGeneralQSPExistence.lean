import QLean.Spectral.Analysis.SignalTransformQSPExistenceSpecifications
import VerifiedMath.Quantum.QSP

/-! Real-polynomial input data and phase-word counts for QSP synthesis.

Admissible polynomials are converted to the internal synthesis representation
without changing their degree, parity, or interval bounds. -/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## Generic real polynomial input -/

/-- A real polynomial together with the degree, parity, and interval bound
required by the real QSP completion statement. -/
structure GeneralRealQSPPolynomial127 where
  polynomial : Polynomial ℝ
  degree : Nat
  degree_bound : polynomial.natDegree ≤ degree
  parity_law : ∀ x : ℝ,
    Polynomial.eval (-x) polynomial =
      if degree % 2 = 0 then Polynomial.eval x polynomial
      else - Polynomial.eval x polynomial
  bounded_on_unitInterval : ∀ x : ℝ, -1 ≤ x → x ≤ 1 →
    |Polynomial.eval x polynomial| ≤ 1

/-- The legacy synthesis interface receives precisely the independent,
human-approved real-polynomial data.  In particular, this conversion neither
chooses phases nor assumes a response theorem. -/
def GeneralRealQSPPolynomial127.ofApproved
    (input : VerifiedMath.Quantum.QSP.AdmissibleRealPolynomial) :
    GeneralRealQSPPolynomial127 where
  polynomial := input.polynomial
  degree := input.degree
  degree_bound := input.degree_bound
  parity_law := input.parity_law
  bounded_on_unitInterval := input.bounded_on_unitInterval

/-! ## Source-order accounting and exact existence target -/

/-- Number of signal queries in the actual source-ordered evaluator word. -/
def signalCount127 : List FixedPointRoleAwarePhaseStep → Nat
  | [] => 0
  | .signal _ :: rest => signalCount127 rest + 1
  | .projectorPhase _ _ :: rest => signalCount127 rest

/-- Number of projector phases in the actual source-ordered evaluator word. -/
def projectorPhaseCount127 : List FixedPointRoleAwarePhaseStep → Nat
  | [] => 0
  | .signal _ :: rest => projectorPhaseCount127 rest
  | .projectorPhase _ _ :: rest => projectorPhaseCount127 rest + 1







end
end SpectralSamplingProof.Analytic
