import QLean.Circuits.Foundation.BitonicScheduleCorrectnessAnalytic

/-!
# bitonic compare--exchangeの個数保存

巨大な値列を列挙せず、compare--exchangeが二添字の置換または恒等写像であることから、
各値の出現個数がschedule全体で保存されることを証明する。
-/

namespace VerifiedCircuitCore

/-- 有限添字付き値列における、指定値の出現個数。 -/
def finiteValueCount {index value : Type*} [Fintype index]
    [DecidableEq value] (target : value) (values : index → value) : Nat :=
  ∑ position, if values position = target then 1 else 0

/-- swap条件が成立するとき、compare--exchangeは二添字置換との合成に等しい。 -/
theorem typedBitonicValueStep_eq_comp_swap_of_swap
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (values : Fin wordCount → α)
    (different : instruction.left ≠ instruction.right)
    (swap : if instruction.ascending then
        values instruction.right < values instruction.left
      else values instruction.left < values instruction.right) :
    typedBitonicValueStep instruction values =
      values ∘ Equiv.swap instruction.left instruction.right := by
  funext index
  unfold typedBitonicValueStep
  simp only [swap, decide_true, if_true]
  by_cases isLeft : index = instruction.left
  · subst index
    simp [Function.update, different]
  · by_cases isRight : index = instruction.right
    · subst index
      simp [Function.update]
    · simp [Function.update, isLeft, isRight,
        Equiv.swap_apply_of_ne_of_ne isLeft isRight]

/-- swap条件が不成立なら、compare--exchangeは恒等写像である。 -/
theorem typedBitonicValueStep_eq_self_of_not_swap
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (values : Fin wordCount → α)
    (notSwap : ¬(if instruction.ascending then
        values instruction.right < values instruction.left
      else values instruction.left < values instruction.right)) :
    typedBitonicValueStep instruction values = values := by
  unfold typedBitonicValueStep
  simp only [notSwap, decide_false, Bool.false_eq_true, if_false]

/-- 一個のcompare--exchangeは任意の値の出現個数を保存する。 -/
theorem finiteValueCount_typedBitonicValueStep
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (different : instruction.left ≠ instruction.right)
    (target : α) (values : Fin wordCount → α) :
    finiteValueCount target (typedBitonicValueStep instruction values) =
      finiteValueCount target values := by
  by_cases swap : if instruction.ascending then
      values instruction.right < values instruction.left
    else values instruction.left < values instruction.right
  · rw [typedBitonicValueStep_eq_comp_swap_of_swap instruction values
      different swap]
    unfold finiteValueCount
    simp only [Function.comp_apply]
    exact Equiv.sum_comp (Equiv.swap instruction.left instruction.right)
      (fun position => if values position = target then 1 else 0)
  · rw [typedBitonicValueStep_eq_self_of_not_swap instruction values swap]

/-- 全命令の左右添字が異なるscheduleは、任意の値の出現個数を保存する。 -/
theorem finiteValueCount_runTypedBitonicValues
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (schedule : List
      (BitonicCompareExchangeWithHistory wordCount historyCount))
    (distinct : ∀ instruction ∈ schedule,
      instruction.left ≠ instruction.right)
    (target : α) (values : Fin wordCount → α) :
    finiteValueCount target (runTypedBitonicValues schedule values) =
      finiteValueCount target values := by
  induction schedule generalizing values with
  | nil => rfl
  | cons instruction schedule inductionHypothesis =>
      simp only [runTypedBitonicValues]
      rw [inductionHypothesis]
      · exact finiteValueCount_typedBitonicValueStep instruction
          (distinct instruction (by simp)) target values
      · intro next member
        exact distinct next (by simp [member])

/-- A distinct history-free compare-exchange schedule preserves every finite
value count. -/
theorem finiteValueCount_runBareBitonicValues
    {wordCount : Nat} {α : Type*} [LinearOrder α]
    (schedule : List (BitonicCompareExchange wordCount))
    (distinct : ∀ instruction ∈ schedule,
      instruction.left ≠ instruction.right)
    (target : α) (values : Fin wordCount → α) :
    finiteValueCount target (runBareBitonicValues schedule values) =
      finiteValueCount target values := by
  rw [← runTyped_unitSchedule_eq_runBare schedule values]
  apply finiteValueCount_runTypedBitonicValues
  intro instruction member
  rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
  exact distinct original originalMember

/-- The standard bitonic sorting schedule preserves every finite value count. -/
theorem bitonicSortSchedule_preserves_valueCount
    (level : Nat) (ascending : Bool) {α : Type*} [LinearOrder α]
    (target : α) (values : Fin (bitonicNetworkWidth level) → α) :
    finiteValueCount target
        (runBareBitonicValues (bitonicSortSchedule level ascending) values) =
      finiteValueCount target values :=
  finiteValueCount_runBareBitonicValues
    (bitonicSortSchedule level ascending)
    (bitonicSortSchedule_all_distinct level ascending) target values

/-- Attaching history slots preserves the left/right distinctness of every
instruction. -/
theorem attachBitonicHistoryFrom_all_distinct
    {wordCount historyCount : Nat} (positiveHistory : 0 < historyCount)
    (offset : Nat) (schedule : List (BitonicCompareExchange wordCount))
    (distinct : ∀ instruction ∈ schedule,
      instruction.left ≠ instruction.right) :
    ∀ instruction ∈ attachBitonicHistoryFrom positiveHistory offset schedule,
      instruction.left ≠ instruction.right := by
  intro instruction member
  apply distinct instruction.eraseHistory
  rw [← attachBitonicHistoryFrom_map_eraseHistory
    positiveHistory offset schedule]
  exact List.mem_map.mpr ⟨instruction, member, rfl⟩

end VerifiedCircuitCore
