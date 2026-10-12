import Mathlib

/-! Basic operations on finite complex vectors. -/

set_option autoImplicit false

namespace VerifiedMath.FiniteComplex

open scoped BigOperators

noncomputable section

/-- Squared L2 mass of a finite complex vector. -/
def mass {basis : Type*} [Fintype basis] (state : basis → ℂ) : ℝ :=
  ∑ index, Complex.normSq (state index)

/-- Euclidean norm of a finite complex vector. -/
def norm {basis : Type*} [Fintype basis] (state : basis → ℂ) : ℝ :=
  Real.sqrt (mass state)

end

end VerifiedMath.FiniteComplex
