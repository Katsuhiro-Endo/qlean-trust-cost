import QLean.Generator.Implementation.QSortedCandidateBridge

/-!
# 有限関数の一点更新と値の出現個数

候補wordを一個だけ変更するevent回路で再利用する、型に依存しない有限和補題。
-/

namespace ProbabilityGeneratorQProof

/--
有限関数の一添字を更新するとき、更新後countに旧値の指示値を足したものは、
更新前countに新値の指示値を足したものへ一致する。
-/
theorem finiteValueCount_update_one_balance_general
    {index value : Type*} [Fintype index] [DecidableEq index]
    [DecidableEq value]
    (target : value) (values : index → value) (selected : index) (newValue : value) :
    finiteValueCount target
          (fun position => if position = selected then newValue else values position) +
        (if values selected = target then 1 else 0) =
      finiteValueCount target values +
        (if newValue = target then 1 else 0) := by
  unfold finiteValueCount
  let oldTerm := fun position : index => if values position = target then 1 else 0
  let newTerm := fun position : index =>
    if (if position = selected then newValue else values position) = target then 1 else 0
  have oldAsSum : oldTerm selected =
      ∑ position : index, if position = selected then oldTerm selected else 0 := by
    simp
  have newAsSum : (if newValue = target then 1 else 0) =
      ∑ position : index,
        if position = selected then (if newValue = target then 1 else 0) else 0 := by
    simp
  change (∑ position : index, newTerm position) + oldTerm selected =
    (∑ position : index, oldTerm position) +
      (if newValue = target then 1 else 0)
  rw [oldAsSum, newAsSum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro position _
  by_cases equal : position = selected
  · subst position
    simp [newTerm, oldTerm, Nat.add_comm]
  · simp [newTerm, oldTerm, equal]

end ProbabilityGeneratorQProof
