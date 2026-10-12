import QLean.Circuits.Foundation.BitonicCleanAnalytic
import QLean.Circuits.Foundation.BitonicNetworkAnalytic
import QLean.Circuits.Foundation.ReversibleLogic
import QLean.Circuits.Foundation.ReversibleLogicCleanAnalytic
import QLean.Circuits.Foundation.Combinators

/-!
# Clean and coherent components for bitonic compare-swap sequences
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Refine an arbitrary full-space exact child to the shared coherent bitonic
contract using only its clean-basis action.  The child target may have a
different dirty-work action from the independent clean reference. -/
def bitonicCompareSwapSequenceCleanSubspaceMapComponentOfExact
    {qubits width wordCount historyCount : Nat}
    (symbolValue : String → ℝ)
    (plan : BitonicCompareSwapCleanPlan qubits width wordCount historyCount)
    (strict : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue))
    (strictBasis : ∀ input, plan.cleanInput input →
      applyOperator strict.target (basisKet input) =
        basisKet (plan.reference input)) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  SubspaceMapComponent.ofBasisSpan
    (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue)
    strict.circuit (deterministicOperator plan.reference)
    plan.cleanInput plan.coherentOutputCondition
    (by
      intro input clean
      rw [strict.correct, applyOperator_deterministicOperator_basisKet]
      exact strictBasis input clean)
    (by
      intro input clean
      rw [applyOperator_deterministicOperator_basisKet]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      exact plan.coherentOutputCondition_correct input clean)

end

end VerifiedCircuitCore
