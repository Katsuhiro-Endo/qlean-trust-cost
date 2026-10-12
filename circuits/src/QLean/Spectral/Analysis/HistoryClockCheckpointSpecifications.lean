import QLean.Spectral.Analysis.HistoryBlock
import QLean.Circuits.Foundation.ClassicalArithmeticCorrectnessAnalytic
import QLean.Circuits.Foundation.ControlledConstantAdderAnalytic

/-!
# H3 / P16 clock-and-idling understanding specification

This pure module is the human-facing checkpoint for the clock/idling child of
the history block.  It intentionally depends only on the remote-green analytic
`HistoryBlock` baseline.  Circuit syntax, denotation, components, and catalog
definitions do not occur here.

The full recorded operator and the clean semantic operator are different
objects.  Both expose the same seven source-order slots, while the clean object
uses independently supplied clean child targets and a common work-zero
predicate.
-/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

/-!
## Boolean views of the three nontrivial clock stages

These definitions deliberately expose the mathematical action without
repeating the reversible compiler stream.  I03 has one genuinely quantum
output (the coefficient `Ry`), so its reference action is a state.  I06 and
I07 are deterministic basis maps.
-/

/-- I06's local clean boundary.  This is deliberately separate from H3's
common protected-wire boundary: the simplified Boolean action below is used
only when equality and conjunction work enter zero. -/
abbrev h3I06CleanInputPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyProjectorControlCleanPredicate layout

/-- On the I06-local clean boundary, the projector signal is flipped exactly
for the branch-selected, nonzero-order sector. -/
def h3I06ProjectorPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : Bool :=
  input (historyBranchWire layout) &&
    !(ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order) 0 input)

/-- Direct I06 basis action after equality/conjunction compute-use-uncompute,
with applicability governed by `h3I06CleanInputPredicate`. -/
def h3I06BasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire layout.projectorSignal (h3I06ProjectorPredicate layout input) input

end SpectralSamplingProof.Analytic
