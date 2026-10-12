import QLean.Circuits.Foundation.BitonicScheduleCorrectnessAnalytic
import QLean.Circuits.Foundation.BitonicPermutationCorrectnessAnalytic

/-!
# Clean semantic plans for physical bitonic compare-swap sequences

The plan records only the layout-independent relation between a typed sorting
schedule, a physical compare-swap sequence, and its basis action.  Gate syntax
and compiler correctness remain in the implementation module.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Proof-bearing semantic interface between a physical compare-swap sequence
and a typed bitonic value schedule.  Applications instantiate wire layouts;
the shared plan owns the sortedness and restoration consequences. -/
structure BitonicCompareSwapCleanPlan
    (qubits width wordCount historyCount : Nat) where
  specs : List (ControlledWordCompareSwapSpec qubits width)
  schedule : List (BitonicCompareExchangeWithHistory wordCount historyCount)
  scheduleLength_eq_specs : schedule.length = specs.length
  readValues : QubitBasis qubits → Fin wordCount → Nat
  cleanInput : QubitBasis qubits → Prop
  workRestored : QubitBasis qubits → Prop
  restoration : QubitBasis qubits → QubitBasis qubits → Prop
  readValues_correct : ∀ input, cleanInput input →
    readValues (bitonicCompareSwapSequenceBasisAction specs input) =
      runTypedBitonicValues schedule (readValues input)
  schedule_sorts : ∀ values : Fin wordCount → Nat,
    IsSortedFin (runTypedBitonicValues schedule values)
  workRestored_correct : ∀ input, cleanInput input →
    workRestored (bitonicCompareSwapSequenceBasisAction specs input)
  restoration_correct : ∀ input, cleanInput input →
    restoration input (bitonicCompareSwapSequenceBasisAction specs input)

namespace BitonicCompareSwapCleanPlan

/-- Direct independent basis reference implemented by the physical specs. -/
def reference {qubits width wordCount historyCount : Nat}
    (plan : BitonicCompareSwapCleanPlan qubits width wordCount historyCount) :
    QubitBasis qubits → QubitBasis qubits :=
  bitonicCompareSwapSequenceBasisAction plan.specs

/-- Sortedness required of the clean classical output. -/
def outputCondition {qubits width wordCount historyCount : Nat}
    (plan : BitonicCompareSwapCleanPlan qubits width wordCount historyCount)
    (output : QubitBasis qubits) : Prop :=
  IsSortedFin (plan.readValues output)

/-- Coherent output sector: sorted values together with restored work. -/
def coherentOutputCondition {qubits width wordCount historyCount : Nat}
    (plan : BitonicCompareSwapCleanPlan qubits width wordCount historyCount)
    (output : QubitBasis qubits) : Prop :=
  plan.outputCondition output ∧ plan.workRestored output

theorem outputCondition_correct
    {qubits width wordCount historyCount : Nat}
    (plan : BitonicCompareSwapCleanPlan qubits width wordCount historyCount)
    (input : QubitBasis qubits) (clean : plan.cleanInput input) :
    plan.outputCondition (plan.reference input) := by
  unfold outputCondition reference
  rw [plan.readValues_correct input clean]
  exact plan.schedule_sorts _

theorem coherentOutputCondition_correct
    {qubits width wordCount historyCount : Nat}
    (plan : BitonicCompareSwapCleanPlan qubits width wordCount historyCount)
    (input : QubitBasis qubits) (clean : plan.cleanInput input) :
    plan.coherentOutputCondition (plan.reference input) := by
  exact ⟨plan.outputCondition_correct input clean,
    plan.workRestored_correct input clean⟩

end BitonicCompareSwapCleanPlan

end

end VerifiedCircuitCore
