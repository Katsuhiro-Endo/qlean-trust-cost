import VerifiedMath.Quantum.QSPFiniteRequest

/-! Decidable word-shape checks. They constrain only roles, directions and
length, and never certify the numerical accuracy of externally supplied phases. -/

set_option autoImplicit false
set_option warningAsError true

namespace VerifiedMath.Quantum.QSP

inductive StepShape where
  | signal (direction : Direction)
  | projectorPhase (role : Role)
  deriving DecidableEq, Repr

def Step.shape {Angle : Type} : Step Angle → StepShape
  | .signal direction => .signal direction
  | .projectorPhase role _ => .projectorPhase role

def alternatingShapeFrom : Nat → Nat → List StepShape
  | _, 0 => []
  | offset, count + 1 =>
      .projectorPhase (if offset % 2 = 0 then .source else .target) ::
      (if count = 0 then [] else
        .signal (if offset % 2 = 0 then .forward else .adjoint) ::
          alternatingShapeFrom (offset + 1) count)

def FinitePolynomialRequest.expectedShape (request : FinitePolynomialRequest) : List StepShape :=
  alternatingShapeFrom 0 request.phaseCount

def shapeCost (signal phase : Nat) : List StepShape → Nat
  | [] => 0
  | .signal _ :: rest => signal + shapeCost signal phase rest
  | .projectorPhase _ :: rest => phase + shapeCost signal phase rest

theorem alternatingShapeFrom_cost (signal phase offset count : Nat) :
    shapeCost signal phase (alternatingShapeFrom offset count) =
      (count - 1) * signal + count * phase := by
  induction count generalizing offset with
  | zero => simp [alternatingShapeFrom, shapeCost]
  | succ count ih =>
      cases count with
      | zero => simp [alternatingShapeFrom, shapeCost]
      | succ count =>
          change phase + (signal + shapeCost signal phase
            (alternatingShapeFrom (offset + 1) (count + 1))) = _
          rw [ih]
          simp only [Nat.add_sub_cancel, Nat.add_mul, one_mul]
          omega

theorem shapeCost_of_planned {Angle : Type} (request : FinitePolynomialRequest)
    (word : Word Angle) (shape : word.map Step.shape = request.expectedShape)
    (signal phase : Nat) :
    shapeCost signal phase (word.map Step.shape) =
      request.degree * signal + (request.degree + 1) * phase := by
  rw [shape]
  exact alternatingShapeFrom_cost signal phase 0 (request.degree + 1)

end VerifiedMath.Quantum.QSP
