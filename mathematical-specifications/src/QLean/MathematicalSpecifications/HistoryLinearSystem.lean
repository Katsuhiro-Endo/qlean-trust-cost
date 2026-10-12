import VerifiedMath.Basis
import VerifiedMath.FiniteComplex
import VerifiedMath.FiniteDistribution

/-!
# Independent Jennings history linear system

This file is the human-reviewable mathematical definition of the finite
history equation.  Its state coordinate is an arbitrary mathematical type;
in particular it is not an implementation register, a `Fin d` chosen by a
circuit compiler, or a physical wire layout.
-/

set_option autoImplicit false

namespace QLean.MathematicalSpecifications.HistoryLinearSystem

open Matrix
open scoped BigOperators

noncomputable section

/-- A coordinate of the history vector: time block, Taylor/idle order and
one coordinate of the independently specified state space. -/
structure Index (state : Type*) (clockCount orderCount : Nat) where
  clock : Fin clockCount
  order : Fin orderCount
  state : state
  deriving DecidableEq, Fintype

/-- Mathematical inputs that determine the Jennings matrix.  In particular,
this record contains no initial state: the matrix is independent of the
right-hand side of the linear system.  `physicalSteps` separates Taylor
propagation blocks from the subsequent idle blocks. -/
structure MatrixData (state : Type*) (clockCount taylorOrder physicalSteps
    orderCount : Nat) where
  step : ℝ
  generator : Matrix state state ℝ
  order_lt : taylorOrder < orderCount
  physical_pos : 0 < physicalSteps
  physical_lt : physicalSteps < clockCount

/-- Complete Jennings equation data.  The initial state belongs only to the
right-hand side; all matrix coefficients are inherited from `MatrixData`. -/
structure Data (state : Type*) (clockCount taylorOrder physicalSteps
    orderCount : Nat) extends
    MatrixData state clockCount taylorOrder physicalSteps orderCount where
  initial : state → ℝ

abbrev Vector (state : Type*) (clockCount orderCount : Nat) :=
  Index state clockCount orderCount → ℝ

abbrev MatrixOf (state : Type*) (clockCount orderCount : Nat) :=
  Matrix (Index state clockCount orderCount)
    (Index state clockCount orderCount) ℝ

def stateIdentityEntry {state : Type*} [DecidableEq state]
    (row column : state) : ℝ :=
  if row = column then 1 else 0

def taylorDeltaEntry {state : Type*} [DecidableEq state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : MatrixData state clockCount taylorOrder physicalSteps orderCount)
    (rowOrder columnOrder : Fin orderCount)
    (rowState columnState : state) : ℝ :=
  if rowOrder.val > 0 ∧ columnOrder.val + 1 = rowOrder.val ∧
      rowOrder.val ≤ taylorOrder then
    -data.step * data.generator rowState columnState / (rowOrder.val : ℝ)
  else 0

def idleDeltaEntry {state : Type*} [DecidableEq state]
    {orderCount : Nat} (rowOrder columnOrder : Fin orderCount)
    (rowState columnState : state) : ℝ :=
  if rowOrder.val > 0 ∧ columnOrder.val + 1 = rowOrder.val then
    -stateIdentityEntry rowState columnState
  else 0

def diagonalEntry {state : Type*} [DecidableEq state]
    {clockCount orderCount : Nat}
    (row column : Index state clockCount orderCount) : ℝ :=
  if row.clock = column.clock ∧ row.order = column.order ∧
      row.state = column.state then 1 else 0

def withinBlockEntry {state : Type*} [DecidableEq state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : MatrixData state clockCount taylorOrder physicalSteps orderCount)
    (row column : Index state clockCount orderCount) : ℝ :=
  if row.clock = column.clock then
    if row.clock.val < physicalSteps then
      taylorDeltaEntry data row.order column.order row.state column.state
    else
      idleDeltaEntry row.order column.order row.state column.state
  else 0

def betweenBlockEntry {state : Type*} [DecidableEq state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (_data : MatrixData state clockCount taylorOrder physicalSteps orderCount)
    (row column : Index state clockCount orderCount) : ℝ :=
  if row.clock.val = column.clock.val + 1 then
    if row.clock.val ≤ physicalSteps then
      if row.order.val = 0 ∧ column.order.val ≤ taylorOrder ∧
          row.state = column.state then -1 else 0
    else
      if row.order.val = 0 ∧ column.order.val + 1 = orderCount ∧
          row.state = column.state then -1 else 0
  else 0

/-- The independently specified history-system matrix. -/
def operator {state : Type*} [DecidableEq state]
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : MatrixData state clockCount taylorOrder physicalSteps orderCount) :
    MatrixOf state clockCount orderCount :=
  fun row column =>
    diagonalEntry row column + withinBlockEntry data row column +
      betweenBlockEntry data row column

/-- The independently specified history-system right-hand side. -/
def rightHandSide {state : Type*}
    {clockCount taylorOrder physicalSteps orderCount : Nat}
    (data : Data state clockCount taylorOrder physicalSteps orderCount) :
    Vector state clockCount orderCount :=
  fun row =>
    if row.clock.val = 0 ∧ row.order.val = 0 then data.initial row.state else 0

end

end QLean.MathematicalSpecifications.HistoryLinearSystem
