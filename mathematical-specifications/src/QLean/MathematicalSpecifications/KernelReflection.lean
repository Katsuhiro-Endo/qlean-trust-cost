import QLean.MathematicalSpecifications.HistoryLinearSystem
import VerifiedMath.FiniteReal

/-!
# Independent kernel-reflection specification

This file defines the ideal reflection used after the Jennings history
linear system.  It contains no circuit syntax, phase word, physical wire,
or implementation index.  The extra coordinate is the scalar coordinate in
the Dalzell extension.
-/

set_option autoImplicit false

namespace QLean.MathematicalSpecifications.KernelReflection

open Matrix
open scoped BigOperators

noncomputable section

abbrev HistoryIndex (state : Type*) (clockCount orderCount : Nat) :=
  HistoryLinearSystem.Index state clockCount orderCount

abbrev ExtendedIndex (state : Type*) (clockCount orderCount : Nat) :=
  Sum (HistoryIndex state clockCount orderCount) Unit

abbrev ExtendedVector (state : Type*) (clockCount orderCount : Nat) :=
  ExtendedIndex state clockCount orderCount → ℝ

abbrev ExtendedMatrix (state : Type*) (clockCount orderCount : Nat) :=
  Matrix (ExtendedIndex state clockCount orderCount)
    (ExtendedIndex state clockCount orderCount) ℝ

def normSquared {index : Type*} [Fintype index]
    (vector : index → ℝ) : ℝ :=
  VerifiedMath.FiniteReal.normSquared vector

def rightHandSideNorm {state : Type*} [Fintype state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : HistoryLinearSystem.Data state clockCount taylorOrder
      physicalSteps orderCount) : ℝ :=
  Real.sqrt (VerifiedMath.FiniteReal.normSquared (HistoryLinearSystem.rightHandSide data))

def normalizedRightHandSide {state : Type*} [Fintype state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : HistoryLinearSystem.Data state clockCount taylorOrder
      physicalSteps orderCount) :
    HistoryIndex state clockCount orderCount → ℝ :=
  VerifiedMath.FiniteReal.normalize (HistoryLinearSystem.rightHandSide data)

/-- Equivalence with the former quotient formula, with no nonzero premise.
In particular the equality includes the zero right-hand side. -/
theorem normalizedRightHandSide_eq_quotient {state : Type*} [Fintype state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : HistoryLinearSystem.Data state clockCount taylorOrder
      physicalSteps orderCount) (row : HistoryIndex state clockCount orderCount) :
    normalizedRightHandSide data row =
      HistoryLinearSystem.rightHandSide data row / rightHandSideNorm data := by
  simp [normalizedRightHandSide, VerifiedMath.FiniteReal.normalize,
    rightHandSideNorm, div_eq_mul_inv, mul_comm]

/-- Block-diagonal Dalzell extension of the normalized history operator. -/
def extendedOperator {state : Type*} [Fintype state] [DecidableEq state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : HistoryLinearSystem.Data state clockCount taylorOrder
      physicalSteps orderCount) (alpha nu : ℝ) :
    ExtendedMatrix state clockCount orderCount
  | Sum.inl row, Sum.inl column =>
      HistoryLinearSystem.operator data.toMatrixData row column / alpha
  | Sum.inr _, Sum.inr _ => nu⁻¹
  | _, _ => 0

/-- Normalized history right-hand side with the scalar extension coordinate. -/
def bPlus {state : Type*} [Fintype state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : HistoryLinearSystem.Data state clockCount taylorOrder
      physicalSteps orderCount) :
    ExtendedVector state clockCount orderCount
  | Sum.inl row => normalizedRightHandSide data row / Real.sqrt 2
  | Sum.inr _ => 1 / Real.sqrt 2

/-- The exact inverse image of `b⁺`.  The determinant witness records the
mathematical well-posedness needed by the correctness theorem; no circuit
object occurs in this definition. -/
def kernelVector {state : Type*} [Fintype state] [DecidableEq state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : HistoryLinearSystem.Data state clockCount taylorOrder
      physicalSteps orderCount) (alpha nu : ℝ)
    (_invertible : IsUnit (extendedOperator data alpha nu).det) :
    ExtendedVector state clockCount orderCount :=
  (extendedOperator data alpha nu)⁻¹.mulVec (bPlus data)

def normalizedKernel {state : Type*} [Fintype state] [DecidableEq state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : HistoryLinearSystem.Data state clockCount taylorOrder
      physicalSteps orderCount) (alpha nu : ℝ)
    (invertible : IsUnit (extendedOperator data alpha nu).det) :
    ExtendedVector state clockCount orderCount :=
  VerifiedMath.FiniteReal.normalize (kernelVector data alpha nu invertible)

/-- Human-approved ideal action: `+1` on the selected kernel direction and
`-1` on its orthogonal complement. -/
def idealReflection {state : Type*} [Fintype state] [DecidableEq state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : HistoryLinearSystem.Data state clockCount taylorOrder
      physicalSteps orderCount) (alpha nu : ℝ)
    (invertible : IsUnit (extendedOperator data alpha nu).det) :
    ExtendedMatrix state clockCount orderCount :=
  2 • VerifiedMath.FiniteReal.lineProjector (normalizedKernel data alpha nu invertible) - 1

end

end QLean.MathematicalSpecifications.KernelReflection
