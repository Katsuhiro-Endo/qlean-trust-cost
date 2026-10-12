import VerifiedMath.Quantum.QSP

/-! Finite polynomial syntax and its independent mathematical interpretation.
The expression and query degree are executable data. Interpretation and
admissibility are used only by proofs and the existence-based provider. -/

set_option autoImplicit false
set_option warningAsError true

namespace VerifiedMath.Quantum.QSP

theorem approvedPolynomial_ext {left right : AdmissibleRealPolynomial}
    (polynomial : left.polynomial = right.polynomial)
    (degree : left.degree = right.degree) : left = right := by
  cases left
  cases right
  cases polynomial
  cases degree
  rfl

inductive ScalarExpression where
  | rational (value : ℚ)
  | add (left right : ScalarExpression)
  | mul (left right : ScalarExpression)
  | div (numerator denominator : ScalarExpression)
  | cosh (argument : ScalarExpression)
  | arcosh (argument : ScalarExpression)
  deriving DecidableEq, Repr

noncomputable def ScalarExpression.interpret : ScalarExpression → ℝ
  | .rational value => value
  | .add left right => left.interpret + right.interpret
  | .mul left right => left.interpret * right.interpret
  | .div numerator denominator => numerator.interpret / denominator.interpret
  | .cosh argument => Real.cosh argument.interpret
  | .arcosh argument => Real.arcosh argument.interpret

inductive PolynomialExpression where
  | constant (value : ScalarExpression)
  | variable
  | add (left right : PolynomialExpression)
  | mul (left right : PolynomialExpression)
  | compose (outer inner : PolynomialExpression)
  | chebyshev (degree : Nat)
  deriving DecidableEq, Repr

noncomputable def PolynomialExpression.interpret : PolynomialExpression → Polynomial ℝ
  | .constant value => Polynomial.C value.interpret
  | .variable => Polynomial.X
  | .add left right => left.interpret + right.interpret
  | .mul left right => left.interpret * right.interpret
  | .compose outer inner => outer.interpret.comp inner.interpret
  | .chebyshev degree => Polynomial.Chebyshev.T ℝ (degree : ℤ)

/-- Proof fields are erased at execution. Neither the polynomial interpretation
nor a phase sequence is executable input data. -/
structure FinitePolynomialRequest where
  expression : PolynomialExpression
  degree : Nat
  degree_bound : expression.interpret.natDegree ≤ degree
  parity_law : ∀ x : ℝ,
    Polynomial.eval (-x) expression.interpret =
      if degree % 2 = 0 then Polynomial.eval x expression.interpret
      else -Polynomial.eval x expression.interpret
  bounded_on_unitInterval : ∀ x : ℝ, -1 ≤ x → x ≤ 1 →
    |Polynomial.eval x expression.interpret| ≤ 1

noncomputable def FinitePolynomialRequest.approved
    (request : FinitePolynomialRequest) : AdmissibleRealPolynomial where
  polynomial := request.expression.interpret
  degree := request.degree
  degree_bound := request.degree_bound
  parity_law := request.parity_law
  bounded_on_unitInterval := request.bounded_on_unitInterval

/-- A generic interpretation boundary, independent of scientific applications.
It is invoked by the theoretical provider, not by the finite circuit builder. -/
class PolynomialInterpretation (Request : Type) where
  approved : Request → AdmissibleRealPolynomial

instance : PolynomialInterpretation AdmissibleRealPolynomial := ⟨id⟩

noncomputable instance : PolynomialInterpretation FinitePolynomialRequest :=
  ⟨FinitePolynomialRequest.approved⟩

abbrev RequestPhaseProvider (Request AngleType : Type) := Request → Word AngleType

/-- A provider for finite polynomial requests, independent of any application.
The angle representation is chosen by the caller; no circuit or science data
is part of this function type. -/
abbrev FinitePhaseProvider (AngleType : Type) :=
  RequestPhaseProvider FinitePolynomialRequest AngleType

/-- Number of freely supplied phase entries in the fixed alternating schedule. -/
def FinitePolynomialRequest.phaseCount (request : FinitePolynomialRequest) : Nat :=
  request.degree + 1

end VerifiedMath.Quantum.QSP
