import Mathlib

/-! Computational basis vectors and matrices induced by finite embeddings. -/

set_option autoImplicit false

namespace VerifiedMath.Basis

noncomputable section

abbrev vector {index scalar : Type*} [DecidableEq index]
    [Zero scalar] [One scalar] (selected : index) : index → scalar :=
  fun candidate => if candidate = selected then 1 else 0

@[simp] theorem vector_apply {index scalar : Type*} [DecidableEq index]
    [Zero scalar] [One scalar] (selected candidate : index) :
    (vector (scalar := scalar) selected) candidate =
      if candidate = selected then 1 else 0 := rfl

/-- Canonical linear extension of an injective basis encoding. -/
abbrev embeddingMatrix {source target scalar : Type*}
    [DecidableEq target] [Zero scalar] [One scalar]
    (embedding : source ↪ target) : Matrix target source scalar :=
  fun output input => if output = embedding input then 1 else 0

end

end VerifiedMath.Basis
