import QLean.Spectral.Circuits.HistoryBlock
import QLean.Circuits.Foundation.OperatorLocality

/-!
# P16 history-clock clean refinement

This module keeps the full-dirty seven-stage Exact parent in `HistoryBlock`
separate from the coherent work-zero refinement.  Every stage below is lifted
from its public Exact child by support locality; no matrix expansion is used.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

def historySelectorEqualityClassicalStage
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ClassicalReversibleStage qubits :=
  ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
    (historyRegisterWires layout.selector) [] 2 (historyBranchWire layout)

def historyDegreeZeroEqualityClassicalStage
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ClassicalReversibleStage qubits :=
  ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
    (historyRegisterWires layout.order)
    (historyRegisterWires (historyEqualityWork layout)) 0
    (historyEqualityFlag layout)

def historyProjectorConjunctionClassicalStage
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ClassicalReversibleStage qubits :=
  ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
    [historyBranchWire layout, historyEqualityFlag layout] []
    (historyCoefficientControl layout)

end SpectralSamplingProof.Components
