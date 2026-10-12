import Mathlib

/-! Exact finite decimals and symbolic angle expressions. -/

namespace SpectralSamplingProof.Analytic

/-- 実数注入を持たない厳密な有限小数。 -/
structure ExactScientificDecimal where
  mantissa : Int
  scale : Nat
  deriving DecidableEq, Repr

/-- phase/angle familyを有限式で保持する回路非依存構文。 -/
inductive ScientificAngleExpr where
  | rational (numerator : Int) (denominator : Nat) (positive : 0 < denominator)
  | decimal (value : ExactScientificDecimal)
  | symbol (name : String)
  | pi
  | add (left right : ScientificAngleExpr)
  | mul (left right : ScientificAngleExpr)
  | div (numerator denominator : ScientificAngleExpr)
  | pow (base exponent : ScientificAngleExpr)
  | neg (value : ScientificAngleExpr)
  | sqrt (value : ScientificAngleExpr)
  | acos (value : ScientificAngleExpr)
  deriving DecidableEq, Repr

end SpectralSamplingProof.Analytic
