import Mathlib

/-! Canonical coercions from finite real matrices and vectors to complex ones. -/

set_option autoImplicit false

namespace VerifiedMath.Complexification

noncomputable section

def matrix {row column : Type*}
    (value : Matrix row column ℝ) : Matrix row column ℂ :=
  fun r c => (value r c : ℂ)

def state {index : Type*} (value : index → ℝ) : index → ℂ :=
  fun i => (value i : ℂ)

def euclideanVector {index : Type*}
    (value : EuclideanSpace ℝ index) : index → ℂ :=
  fun i => (value i : ℂ)

end

end VerifiedMath.Complexification
