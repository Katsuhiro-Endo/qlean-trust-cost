import VerifiedMath.FiniteComplex

/-! Reusable finite-dimensional approximation and projected-state relations. -/

set_option autoImplicit false

namespace VerifiedMath.OperatorRelations

open Matrix
open VerifiedMath.FiniteComplex

noncomputable section

def RealLogicalActionApprox {basis : Type*} [Fintype basis]
    (complexify : EuclideanSpace ℝ basis → basis → ℂ)
    (implementation : Matrix basis basis ℂ)
    (target : EuclideanSpace ℝ basis → EuclideanSpace ℝ basis)
    (tolerance : ℝ) : Prop :=
  ∀ state,
    VerifiedMath.FiniteComplex.norm
      (implementation.mulVec (complexify state) - complexify (target state)) ≤
      tolerance * ‖state‖

def StateApprox {basis : Type*} [Fintype basis]
    (implementation target : basis → ℂ) (tolerance : ℝ) : Prop :=
  VerifiedMath.FiniteComplex.norm
    (fun index => implementation index - target index) ≤ tolerance

end

end VerifiedMath.OperatorRelations
