import QLean.MathematicalSpecifications.HistoryLinearSystem
import QLean.History.Jennings.PureSpec

/-!
# Jennings history-system representation transport

The mathematical system is indexed by the approved state type.  The circuit
library uses `Fin d`.  This module proves that reindexing by an explicit
equivalence preserves every matrix and right-hand-side entry.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Correspondence.HistoryLinearSystemTransport

open QLean.MathematicalSpecifications.HistoryLinearSystem

noncomputable section

/-- Translate independent history data to the finite-numbered representation
used by the circuit implementation. -/
def toCircuitData {state : Type*} {d clockCount taylorOrder physicalSteps
    orderCount : Nat} (stateEquiv : state ≃ Fin d)
    (data : Data state clockCount taylorOrder physicalSteps orderCount) :
    JenningsHistory.HistorySpec d clockCount taylorOrder physicalSteps
      orderCount where
  step := data.step
  generator := fun row column =>
    data.generator (stateEquiv.symm row) (stateEquiv.symm column)
  initial := fun index => data.initial (stateEquiv.symm index)
  order_lt := data.order_lt
  physical_pos := data.physical_pos
  physical_lt := data.physical_lt

/-- Coordinatewise equivalence between the independent and circuit history
index sets. -/
def indexEquiv {state : Type*} {d clockCount orderCount : Nat}
    (stateEquiv : state ≃ Fin d) :
    Index state clockCount orderCount ≃
      JenningsHistory.HistoryIndex d clockCount orderCount where
  toFun index :=
    { clock := index.clock, order := index.order, state := stateEquiv index.state }
  invFun index :=
    { clock := index.clock, order := index.order,
      state := stateEquiv.symm index.state }
  left_inv index := by
    cases index
    simp
  right_inv index := by
    cases index
    simp

/-- Exact entrywise preservation of the independently approved history
operator. -/
theorem operator_entry_transport {state : Type*} [DecidableEq state]
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : Data state clockCount taylorOrder physicalSteps orderCount)
    (row column : Index state clockCount orderCount) :
    JenningsHistory.historyMatrix (toCircuitData stateEquiv data)
        (indexEquiv stateEquiv row) (indexEquiv stateEquiv column) =
      operator data.toMatrixData row column := by
  simp [JenningsHistory.historyMatrix, operator,
    JenningsHistory.l0Entry, diagonalEntry,
    JenningsHistory.l1Entry, withinBlockEntry,
    JenningsHistory.l2Entry, betweenBlockEntry,
    JenningsHistory.taylorDeltaEntry, taylorDeltaEntry,
    JenningsHistory.idleDeltaEntry, idleDeltaEntry,
    JenningsHistory.stateIdentityEntry, stateIdentityEntry,
    toCircuitData, indexEquiv]

/-- Exact entrywise preservation of the independently approved right-hand
side. -/
theorem rightHandSide_entry_transport {state : Type*}
    {d clockCount taylorOrder physicalSteps orderCount : Nat}
    (stateEquiv : state ≃ Fin d)
    (data : Data state clockCount taylorOrder physicalSteps orderCount)
    (row : Index state clockCount orderCount) :
    JenningsHistory.historyRhs (toCircuitData stateEquiv data)
      (indexEquiv stateEquiv row) = rightHandSide data row := by
  simp [JenningsHistory.historyRhs, rightHandSide, toCircuitData,
    indexEquiv]

end

end QLean.Correspondence.HistoryLinearSystemTransport
