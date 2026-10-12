import QLean.Spectral.Circuits.HistoryClockClean
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Generator.Implementation.CoreAdapter

/-!
# H3 branch-uncompute source order

This leaf records the source-faithful corrected H3 word. I05 is an internal
compute/uncompute substep of I06, not a top-level H3 child. The corrected
word therefore has I01, I02, I03, I04, I06, I07, followed by I01 again to
uncompute the selector branch.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

/-- The repaired word returns to the same complete H4/P15 auxiliary
boundary, while retaining the pre-existing H3 clean interface. -/
def historyClockBranchUncomputedStrongOutputPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  historyTaylorAuxiliaryBoundaryPredicate layout basis ∧
    historyClockCleanPredicate layout basis

/-- The full auxiliary boundary includes every wire protected by the older
H3 clean predicate. -/
theorem historyTaylorAuxiliaryBoundaryPredicate_implies_historyClockCleanPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits)
    (inside : historyTaylorAuxiliaryBoundaryPredicate layout basis) :
    historyClockCleanPredicate layout basis := by
  intro wire member
  exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem layout basis inside
    wire (historyClockCleanProtectedWire_mem_workspace layout wire member)

end

end SpectralSamplingProof.Components

