import QLean.Spectral.Circuits.HistoryBlock
import QLean.Spectral.Analysis.R12OperatorDag
import QLean.Generator.Implementation.ProbabilityGeneratorCoreExactAdapter

/-!
# Source-faithful P15 Taylor selected block

This module fixes the L2 source order from
`probability_history_block_encoding_circuit` lines 681--807.  The probability
generator call is kept as one distinguished controlled P17 contract.  Its
shared externally-controlled compiler is intentionally an interface until the
Q/core decoder certificate is public; every other stage is constructed from a
shared leaf component and the frozen history layout.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

/-- Proof fields needed to instantiate the shared P41 comparison on fixed
registers. -/
structure HistoryTaylorLessThanEvidence {qubits width : Nat}
    (lhs rhs borrow : Register qubits width) (target : Fin qubits) where
  widthPositive : 0 < width
  lhsRhsDifferent : ∀ left right, lhs.wire left ≠ rhs.wire right
  lhsBorrowDifferent : ∀ left right, lhs.wire left ≠ borrow.wire right
  rhsBorrowDifferent : ∀ left right, rhs.wire left ≠ borrow.wire right
  targetLhsDifferent : ∀ index, target ≠ lhs.wire index
  targetRhsDifferent : ∀ index, target ≠ rhs.wire index
  targetBorrowDifferent : ∀ index, target ≠ borrow.wire index

def HistoryTaylorLessThanEvidence.toSpec {qubits width : Nat}
    {lhs rhs borrow : Register qubits width} {target : Fin qubits}
    (evidence : HistoryTaylorLessThanEvidence lhs rhs borrow target) :
    UnsignedLessThanXorSpec qubits width where
  widthPositive := evidence.widthPositive
  lhs := lhs
  rhs := rhs
  borrow := borrow
  target := target
  lhsRhsDifferent := evidence.lhsRhsDifferent
  lhsBorrowDifferent := evidence.lhsBorrowDifferent
  rhsBorrowDifferent := evidence.rhsBorrowDifferent
  targetLhsDifferent := evidence.targetLhsDifferent
  targetRhsDifferent := evidence.targetRhsDifferent
  targetBorrowDifferent := evidence.targetBorrowDifferent

/-- Pairwise layout evidence for the frozen P15 controlled degree increment. -/
structure HistoryTaylorDegreeIncrementEvidence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  addend_accumulator_disjoint : ∀ left right,
    (historyOrderIncrementAddendRegister layout).wire left ≠
      (historyOrderAccumulatorRegister layout).wire right
  carry_ne_addend : ∀ index,
    historyOrderIncrementCarry layout ≠
      (historyOrderIncrementAddendRegister layout).wire index
  carry_ne_accumulator : ∀ index,
    historyOrderIncrementCarry layout ≠
      (historyOrderAccumulatorRegister layout).wire index
  control_ne_addend : ∀ index,
    historyActiveWire layout ≠
      (historyOrderIncrementAddendRegister layout).wire index
  control_ne_accumulator : ∀ index,
    historyActiveWire layout ≠
      (historyOrderAccumulatorRegister layout).wire index
  control_ne_carry :
    historyActiveWire layout ≠ historyOrderIncrementCarry layout

def historyTaylorDegreeIncrementSpec
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryTaylorDegreeIncrementEvidence layout) :
    ControlledAddConstantMod2PowSpec qubits
      (historyOrderTailWidth parameters) where
  addend := historyOrderIncrementAddendRegister layout
  accumulator := historyOrderAccumulatorRegister layout
  carry := historyOrderIncrementCarry layout
  addend_accumulator_disjoint := evidence.addend_accumulator_disjoint
  carry_ne_addend := evidence.carry_ne_addend
  carry_ne_accumulator := evidence.carry_ne_accumulator
  control := historyActiveWire layout
  constant := 1
  control_ne_addend := evidence.control_ne_addend
  control_ne_accumulator := evidence.control_ne_accumulator
  control_ne_carry := evidence.control_ne_carry

/-- The exact inequalities and recorded angles not derivable definitionally
from the frozen register slices. -/
structure HistoryTaylorL2Evidence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  clockTimeLessThan : HistoryTaylorLessThanEvidence layout.clock
    (historyBoundRegister layout) (historyBorrowRegister layout)
    (historyLessThanTimeWire layout)
  clockIdleEndLessThan : HistoryTaylorLessThanEvidence layout.clock
    (historyBoundRegister layout) (historyBorrowRegister layout)
    (historyLessThanIdleEndWire layout)
  degreeOrderLessThan : HistoryTaylorLessThanEvidence layout.order
    (historyOrderBoundRegister layout)
    (historyOrderMaskedConstantRegister layout)
    (historyEqualityFlag layout)
  degreeIncrement : HistoryTaylorDegreeIncrementEvidence layout
  branch_ne_ltIdleEnd :
    historyBranchWire layout ≠ historyLessThanIdleEndWire layout
  branch_ne_coefficientSignal :
    historyBranchWire layout ≠ layout.coefficientSignal
  ltIdleEnd_ne_coefficientSignal :
    historyLessThanIdleEndWire layout ≠ layout.coefficientSignal
  active_ne_equality : historyActiveWire layout ≠ historyEqualityFlag layout
  active_ne_orderBoundary :
    historyActiveWire layout ≠ layout.orderBoundarySignal
  equality_ne_orderBoundary :
    historyEqualityFlag layout ≠ layout.orderBoundarySignal
  ltIdleEnd_ne_idle :
    historyLessThanIdleEndWire layout ≠ historyIdleFlag layout
  ltTime_ne_idle :
    historyLessThanTimeWire layout ≠ historyIdleFlag layout
  active_ne_coefficientSignal :
    historyActiveWire layout ≠ layout.coefficientSignal
  coefficientControl_ne_coefficientSignal :
    historyCoefficientControl layout ≠ layout.coefficientSignal
  coefficientAngles : Fin parameters.taylorOrder → AngleExpr
  idleCoefficientAngle : AngleExpr

end SpectralSamplingProof.Components
