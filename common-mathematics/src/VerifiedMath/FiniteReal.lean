import Mathlib

/-! Basic operations on finite real vectors. -/

set_option autoImplicit false

namespace VerifiedMath.FiniteReal

open scoped BigOperators

noncomputable section

/-- Squared Euclidean norm of a finite real vector. -/
def normSquared {index : Type*} [Fintype index]
    (vector : index → ℝ) : ℝ :=
  ∑ i, vector i * vector i

/-- Total normalization operation; the zero vector remains zero. -/
def normalize {index : Type*} [Fintype index]
    (vector : index → ℝ) : index → ℝ :=
  (Real.sqrt (normSquared vector))⁻¹ • vector

/-- Rank-one matrix determined by a finite real vector and its squared norm. -/
def lineProjector {index : Type*} [Fintype index]
    (vector : index → ℝ) : Matrix index index ℝ :=
  fun row column => vector row * vector column / normSquared vector

end

end VerifiedMath.FiniteReal
