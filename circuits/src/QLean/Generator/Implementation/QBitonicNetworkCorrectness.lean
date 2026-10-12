import QLean.Generator.Analysis.BitonicTotalStage
import QLean.Generator.Implementation.BitonicSortLayout
import QLean.Generator.Implementation.BitonicPermutationCorrectness
import QLean.Circuits.Foundation.BitonicScheduleCorrectnessAnalytic
import QLean.Circuits.Foundation.BitonicPermutationCorrectnessAnalytic

/-!
# Q bitonic schedule adapters

The layout-independent sorting and multiplicity theorems come from the shared
core.  This module retains only the Q power-of-two cast and history attachment
transport.
-/

namespace ProbabilityGeneratorQProof

/-- Executing a schedule cast along a word-count equality only reindexes the
input and output finite word indices. -/
theorem runBareBitonicValues_map_cast
    {sourceWidth targetWidth : Nat} {α : Type*} [LinearOrder α]
    (widthEquality : sourceWidth = targetWidth)
    (schedule : List (BareBitonicCompareExchange sourceWidth))
    (values : Fin targetWidth → α) :
    VerifiedCircuitCore.runBareBitonicValues
        (schedule.map
          (VerifiedCircuitCore.BitonicCompareExchange.cast widthEquality)) values =
      fun index =>
        VerifiedCircuitCore.runBareBitonicValues schedule
          (fun source => values (Fin.cast widthEquality source))
          (Fin.cast widthEquality.symm index) := by
  subst targetWidth
  funext index
  simp only [Fin.cast_refl]
  induction schedule generalizing values with
  | nil => rfl
  | cons instruction schedule inductionHypothesis =>
      simp only [List.map_cons, VerifiedCircuitCore.runBareBitonicValues]
      have castInstruction :
          VerifiedCircuitCore.BitonicCompareExchange.cast rfl instruction =
            instruction := by
        cases instruction
        rfl
      rw [castInstruction]
      simpa only [id_eq] using
        inductionHypothesis
          (VerifiedCircuitCore.bareBitonicValueStep instruction values)

/-- Erasing Q history slots gives the shared cast bare schedule. -/
theorem qSchedule_map_eraseHistory (p : QParameters) :
    (BitonicTotalProgram.qSchedule p).map
        VerifiedCircuitCore.BitonicCompareExchangeWithHistory.eraseHistory =
      BitonicTotalProgram.qBareSchedule p := by
  unfold BitonicTotalProgram.qSchedule BitonicTotalProgram.attachHistory
  exact VerifiedCircuitCore.attachBitonicHistoryFrom_map_eraseHistory
    (by simp [QParameters.sortFlagWidth, QParameters.sortWordCount]) 0 _

/-- History allocation does not change the Q schedule's pure value action. -/
theorem runTyped_qSchedule_eq_runBare_qBare
    (p : QParameters) {α : Type*} [LinearOrder α]
    (values : Fin p.sortWordCount → α) :
    runTypedBitonicValues (BitonicTotalProgram.qSchedule p) values =
      VerifiedCircuitCore.runBareBitonicValues
        (BitonicTotalProgram.qBareSchedule p) values := by
  rw [VerifiedCircuitCore.runTypedBitonicValues_eq_runBare_eraseHistory]
  rw [qSchedule_map_eraseHistory]

/-- The shared Q schedule sorts every natural-valued candidate sequence. -/
theorem qTypedBitonicSchedule_sorts_nat
    (p : QParameters) (values : Fin p.sortWordCount → Nat) :
    IsSortedFin
      (runTypedBitonicValues (qTypedBitonicSchedule p) values) := by
  change IsSortedFin
    (runTypedBitonicValues (BitonicTotalProgram.qSchedule p) values)
  rw [runTyped_qSchedule_eq_runBare_qBare]
  let level := Nat.clog 2 p.K
  let widthEquality :
      VerifiedCircuitCore.bitonicNetworkWidth level = p.sortWordCount := by
    simp [level, QParameters.sortWordCount,
      VerifiedCircuitCore.bitonicNetworkWidth_eq_pow]
  rw [show BitonicTotalProgram.qBareSchedule p =
      (VerifiedCircuitCore.bitonicSortSchedule level true).map
        (VerifiedCircuitCore.BitonicCompareExchange.cast widthEquality) by
    rfl]
  rw [runBareBitonicValues_map_cast]
  have sorted := VerifiedCircuitCore.bitonicSortSchedule_sorts_nat level
    (fun source => values (Fin.cast widthEquality source))
  intro left right order
  have castOrder :
      (Fin.cast widthEquality.symm left).val ≤
        (Fin.cast widthEquality.symm right).val := by
    simpa using order
  exact sorted (Fin.cast widthEquality.symm left)
    (Fin.cast widthEquality.symm right) castOrder

/-- The shared Q schedule preserves every finite candidate-value count. -/
theorem qTypedBitonicSchedule_preserves_valueCount
    (p : QParameters) {α : Type*} [LinearOrder α]
    (target : α) (values : Fin p.sortWordCount → α) :
    finiteValueCount target
        (runTypedBitonicValues (qTypedBitonicSchedule p) values) =
      finiteValueCount target values := by
  change finiteValueCount target
      (runTypedBitonicValues (BitonicTotalProgram.qSchedule p) values) = _
  rw [runTyped_qSchedule_eq_runBare_qBare]
  apply VerifiedCircuitCore.finiteValueCount_runBareBitonicValues
  intro instruction member
  unfold BitonicTotalProgram.qBareSchedule at member
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  intro equal
  apply (VerifiedCircuitCore.bitonicSortSchedule_all_distinct
    (Nat.clog 2 p.K) true source sourceMember)
  apply Fin.ext
  simpa [BitonicTotalProgram.cast,
    VerifiedCircuitCore.BitonicCompareExchange.cast] using
    congrArg Fin.val equal

end ProbabilityGeneratorQProof
