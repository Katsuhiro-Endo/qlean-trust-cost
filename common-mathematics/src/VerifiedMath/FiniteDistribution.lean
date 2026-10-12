import Mathlib

/-! Operations on finite real weight functions. -/

set_option autoImplicit false

namespace VerifiedMath.FiniteDistribution

open scoped BigOperators

noncomputable section

@[simp] def totalVariation {outcome : Type*} [Fintype outcome]
    (left right : outcome → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ value, |left value - right value|

end

end VerifiedMath.FiniteDistribution
