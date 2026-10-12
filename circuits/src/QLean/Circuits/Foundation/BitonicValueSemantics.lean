import QLean.Circuits.Foundation.BitonicNetworkAnalytic

/-!
# bitonic比較ネットワークの純粋な一般意味論

量子回路や行列から独立して、型付きcompare--exchange命令列が有限word列へ与える
作用を定義する。後続の正しさ証明はこの意味論上で行い、全基底や巨大行列を列挙しない。
-/

namespace VerifiedCircuitCore

/-- 型付き命令一個を、任意の線形順序を持つ有限word列へ作用させる。 -/
def typedBitonicValueStep {wordCount historyCount : Nat} {α : Type*}
    [LinearOrder α]
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (values : Fin wordCount → α) : Fin wordCount → α :=
  let shouldSwap := if instruction.ascending then
    values instruction.right < values instruction.left
  else values instruction.left < values instruction.right
  if decide shouldSwap then
    Function.update
      (Function.update values instruction.left (values instruction.right))
      instruction.right (values instruction.left)
  else values

/-- 型付きcompare--exchange命令列を実行順に畳み込む。 -/
def runTypedBitonicValues {wordCount historyCount : Nat} {α : Type*}
    [LinearOrder α] :
    List (BitonicCompareExchangeWithHistory wordCount historyCount) →
      (Fin wordCount → α) → Fin wordCount → α
  | [], values => values
  | instruction :: schedule, values =>
      runTypedBitonicValues schedule
        (typedBitonicValueStep instruction values)

/-- 有限word列が添字順に非減少であることを表す。 -/
def IsSortedFin {wordCount : Nat} {α : Type*} [LE α]
    (values : Fin wordCount → α) : Prop :=
  ∀ left right, left.val ≤ right.val → values left ≤ values right

/-- 有限word列が添字順に非増加であることを表す。 -/
def IsReverseSortedFin {wordCount : Nat} {α : Type*} [LE α]
    (values : Fin wordCount → α) : Prop :=
  ∀ left right, left.val ≤ right.val → values right ≤ values left

/-- Boolean方向に応じて非減少または非増加を選ぶ有限列の整列述語。 -/
def IsSortedDirectionFin {wordCount : Nat} {α : Type*} [LE α]
    (ascending : Bool) (values : Fin wordCount → α) : Prop :=
  if ascending then IsSortedFin values else IsReverseSortedFin values

/-- 自然数を閾値より大きいか否かでBoolean列へ写す。 -/
def thresholdValues {wordCount : Nat} (threshold : Nat)
    (values : Fin wordCount → Nat) : Fin wordCount → Bool :=
  fun index => decide (threshold < values index)

/-- 比較交換で左wordを読むと、昇順なら最小値、降順なら最大値になる。 -/
theorem typedBitonicValueStep_left
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (values : Fin wordCount → α)
    (different : instruction.left ≠ instruction.right) :
    typedBitonicValueStep instruction values instruction.left =
      if instruction.ascending then
        min (values instruction.left) (values instruction.right)
      else max (values instruction.left) (values instruction.right) := by
  unfold typedBitonicValueStep
  cases ascending : instruction.ascending with
  | true =>
    simp only [if_true]
    by_cases swap : values instruction.right < values instruction.left
    · simp [swap, Function.update, different, min_eq_right (le_of_lt swap)]
    · have ordered : values instruction.left ≤ values instruction.right :=
        le_of_not_gt swap
      simp [swap, ordered]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    by_cases swap : values instruction.left < values instruction.right
    · simp [swap, Function.update, different,
        max_eq_right (le_of_lt swap)]
    · have ordered : values instruction.right ≤ values instruction.left :=
        le_of_not_gt swap
      simp [swap, ordered]

/-- 比較交換で右wordを読むと、昇順なら最大値、降順なら最小値になる。 -/
theorem typedBitonicValueStep_right
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (values : Fin wordCount → α)
    (_different : instruction.left ≠ instruction.right) :
    typedBitonicValueStep instruction values instruction.right =
      if instruction.ascending then
        max (values instruction.left) (values instruction.right)
      else min (values instruction.left) (values instruction.right) := by
  unfold typedBitonicValueStep
  cases ascending : instruction.ascending with
  | true =>
    simp only [if_true]
    by_cases swap : values instruction.right < values instruction.left
    · simp [swap, Function.update,
        max_eq_left (le_of_lt swap)]
    · have ordered : values instruction.left ≤ values instruction.right :=
        le_of_not_gt swap
      simp [swap, ordered]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    by_cases swap : values instruction.left < values instruction.right
    · simp [swap, Function.update,
        min_eq_left (le_of_lt swap)]
    · have ordered : values instruction.right ≤ values instruction.left :=
        le_of_not_gt swap
      simp [swap, ordered]

/-- 比較対象外のwordは一個のcompare--exchangeで変化しない。 -/
theorem typedBitonicValueStep_other
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (values : Fin wordCount → α) (index : Fin wordCount)
    (notLeft : index ≠ instruction.left)
    (notRight : index ≠ instruction.right) :
    typedBitonicValueStep instruction values index = values index := by
  unfold typedBitonicValueStep
  cases instruction.ascending <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals split <;> simp [Function.update, notLeft, notRight]

/-- 自然数の最小値を閾値化するとBooleanの最小値に一致する。 -/
theorem threshold_min (threshold left right : Nat) :
    decide (threshold < min left right) =
      min (decide (threshold < left)) (decide (threshold < right)) := by
  by_cases order : left ≤ right
  · rw [min_eq_left order]
    by_cases leftPasses : threshold < left
    · have rightPasses : threshold < right := lt_of_lt_of_le leftPasses order
      simp [leftPasses, rightPasses]
    · simp [leftPasses]
  · have reverse : right ≤ left := le_of_not_ge order
    rw [min_eq_right reverse]
    by_cases rightPasses : threshold < right
    · have leftPasses : threshold < left := lt_of_lt_of_le rightPasses reverse
      simp [leftPasses, rightPasses]
    · simp [rightPasses]

/-- 自然数の最大値を閾値化するとBooleanの最大値に一致する。 -/
theorem threshold_max (threshold left right : Nat) :
    decide (threshold < max left right) =
      max (decide (threshold < left)) (decide (threshold < right)) := by
  by_cases order : left ≤ right
  · rw [max_eq_right order]
    by_cases rightPasses : threshold < right
    · simp [rightPasses]
    · have leftFails : ¬ threshold < left := fun leftPasses =>
        rightPasses (lt_of_lt_of_le leftPasses order)
      simp [leftFails, rightPasses]
  · have reverse : right ≤ left := le_of_not_ge order
    rw [max_eq_left reverse]
    by_cases leftPasses : threshold < left
    · simp [leftPasses]
    · have rightFails : ¬ threshold < right := fun rightPasses =>
        leftPasses (lt_of_lt_of_le rightPasses reverse)
      simp [leftPasses, rightFails]

/-- 閾値化は一個のcompare--exchangeと可換である。 -/
theorem thresholdValues_typedBitonicValueStep
    {wordCount historyCount : Nat}
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (different : instruction.left ≠ instruction.right)
    (threshold : Nat) (values : Fin wordCount → Nat) :
    thresholdValues threshold (typedBitonicValueStep instruction values) =
      typedBitonicValueStep instruction (thresholdValues threshold values) := by
  funext index
  by_cases isLeft : index = instruction.left
  · subst index
    unfold thresholdValues
    rw [typedBitonicValueStep_left instruction values different]
    rw [typedBitonicValueStep_left instruction
      (fun index => decide (threshold < values index)) different]
    split <;> simp
  · by_cases isRight : index = instruction.right
    · subst index
      unfold thresholdValues
      rw [typedBitonicValueStep_right instruction values different]
      rw [typedBitonicValueStep_right instruction
        (fun index => decide (threshold < values index)) different]
      split <;> simp
    · unfold thresholdValues
      rw [typedBitonicValueStep_other instruction values index isLeft isRight]
      rw [typedBitonicValueStep_other instruction
        (fun index => decide (threshold < values index)) index isLeft isRight]

/-- 全命令が異なる二添字を比較するなら、閾値化は命令列全体と可換である。 -/
theorem thresholdValues_runTypedBitonicValues
    {wordCount historyCount : Nat}
    (schedule : List
      (BitonicCompareExchangeWithHistory wordCount historyCount))
    (distinct : ∀ instruction ∈ schedule,
      instruction.left ≠ instruction.right)
    (threshold : Nat) (values : Fin wordCount → Nat) :
    thresholdValues threshold (runTypedBitonicValues schedule values) =
      runTypedBitonicValues schedule (thresholdValues threshold values) := by
  induction schedule generalizing values with
  | nil => rfl
  | cons instruction schedule inductionHypothesis =>
      simp only [runTypedBitonicValues]
      rw [inductionHypothesis]
      · rw [thresholdValues_typedBitonicValueStep instruction
          (distinct instruction (by simp)) threshold values]
      · intro next member
        exact distinct next (by simp [member])

/-- 二つのcompare--exchange命令が互いの左右添字を共有しないことを表す。 -/
def BitonicInstructionsDisjoint
    {wordCount historyCount : Nat}
    (first second : BitonicCompareExchangeWithHistory wordCount historyCount) : Prop :=
  first.left ≠ second.left ∧ first.left ≠ second.right ∧
    first.right ≠ second.left ∧ first.right ≠ second.right

/-- 指定添字に触れない命令列は、その添字の値を保存する。 -/
theorem runTypedBitonicValues_other
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (schedule : List
      (BitonicCompareExchangeWithHistory wordCount historyCount))
    (values : Fin wordCount → α) (index : Fin wordCount)
    (outside : ∀ instruction ∈ schedule,
      index ≠ instruction.left ∧ index ≠ instruction.right) :
    runTypedBitonicValues schedule values index = values index := by
  induction schedule generalizing values with
  | nil => rfl
  | cons instruction schedule inductionHypothesis =>
      simp only [runTypedBitonicValues]
      rw [inductionHypothesis]
      · exact typedBitonicValueStep_other instruction values index
          (outside instruction (by simp)).1
          (outside instruction (by simp)).2
      · intro next member
        exact outside next (by simp [member])

/-- 二入力が左右添字上で一致すれば、同じ命令の左右出力も一致する。 -/
theorem typedBitonicValueStep_endpoint_congr
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (different : instruction.left ≠ instruction.right)
    (first second : Fin wordCount → α)
    (leftAgree : first instruction.left = second instruction.left)
    (rightAgree : first instruction.right = second instruction.right)
    (index : Fin wordCount)
    (endpoint : index = instruction.left ∨ index = instruction.right) :
    typedBitonicValueStep instruction first index =
      typedBitonicValueStep instruction second index := by
  rcases endpoint with leftEndpoint | rightEndpoint
  · subst index
    rw [typedBitonicValueStep_left instruction first different]
    rw [typedBitonicValueStep_left instruction second different]
    rw [leftAgree, rightAgree]
  · subst index
    rw [typedBitonicValueStep_right instruction first different]
    rw [typedBitonicValueStep_right instruction second different]
    rw [leftAgree, rightAgree]

/--
pairwiseに交差しない命令列では、所属命令の左右添字における最終値は、その命令一個の
元入力への作用に等しい。
-/
theorem runTypedBitonicValues_at_disjoint_member
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α] :
    ∀ (schedule : List
        (BitonicCompareExchangeWithHistory wordCount historyCount))
      (target : BitonicCompareExchangeWithHistory wordCount historyCount),
      schedule.Pairwise BitonicInstructionsDisjoint →
      target ∈ schedule →
      target.left ≠ target.right →
      ∀ (values : Fin wordCount → α) (index : Fin wordCount),
        (index = target.left ∨ index = target.right) →
        runTypedBitonicValues schedule values index =
          typedBitonicValueStep target values index := by
  intro schedule
  induction schedule with
  | nil =>
      intro target _ member
      simp at member
  | cons instruction schedule inductionHypothesis =>
      intro target pairwise member targetDifferent values index endpoint
      have pairwiseParts := List.pairwise_cons.mp pairwise
      by_cases equal : target = instruction
      · subst instruction
        simp only [runTypedBitonicValues]
        apply runTypedBitonicValues_other
        intro next nextMember
        have disjoint := pairwiseParts.1 next nextMember
        rcases endpoint with leftEndpoint | rightEndpoint
        · subst index
          exact ⟨disjoint.1, disjoint.2.1⟩
        · subst index
          exact ⟨disjoint.2.2.1, disjoint.2.2.2⟩
      · have tailMember : target ∈ schedule := by
          simpa [equal] using member
        simp only [runTypedBitonicValues]
        rw [inductionHypothesis target pairwiseParts.2 tailMember targetDifferent
          (typedBitonicValueStep instruction values) index endpoint]
        have disjoint := pairwiseParts.1 target tailMember
        apply typedBitonicValueStep_endpoint_congr target targetDifferent
        · exact typedBitonicValueStep_other instruction values target.left
            disjoint.1.symm disjoint.2.2.1.symm
        · exact typedBitonicValueStep_other instruction values target.right
            disjoint.2.1.symm disjoint.2.2.2.symm
        · exact endpoint

/--
全閾値Boolean像が昇順なら、元の自然数word列も昇順である（0--1原理の順序反映部）。
-/
theorem isSortedFin_of_thresholds
    {wordCount : Nat} (values : Fin wordCount → Nat)
    (sortedThresholds : ∀ threshold,
      IsSortedFin (thresholdValues threshold values)) :
    IsSortedFin values := by
  intro left right indexOrder
  by_contra notOrdered
  have strict : values right < values left := Nat.lt_of_not_ge notOrdered
  have boolOrder := sortedThresholds (values right) left right indexOrder
  simp [thresholdValues, strict] at boolOrder
  have impossible : ¬ (true ≤ false) := by decide
  exact impossible boolOrder

/-- 昇順Boolean列は、あるcutoffより前がfalse、以後がtrueという形を持つ。 -/
theorem bool_sorted_ascending_cutoff
    {wordCount : Nat} (values : Fin wordCount → Bool)
    (sorted : IsSortedFin values) :
    ∃ cutoff, cutoff ≤ wordCount ∧
      ∀ index : Fin wordCount,
        values index = decide (cutoff ≤ index.val) := by
  classical
  by_cases anyTrue : ∃ index : Fin wordCount, values index = true
  · let predicate : Nat → Prop := fun index =>
      ∃ inRange : index < wordCount,
        values ⟨index, inRange⟩ = true
    have existsPredicate : ∃ index, predicate index := by
      rcases anyTrue with ⟨index, trueAt⟩
      exact ⟨index.val, index.isLt, trueAt⟩
    let cutoff := Nat.find existsPredicate
    have cutoffSpec := Nat.find_spec existsPredicate
    rcases cutoffSpec with ⟨cutoffLt, trueAtCutoff⟩
    refine ⟨cutoff, Nat.le_of_lt cutoffLt, ?_⟩
    intro index
    by_cases afterCutoff : cutoff ≤ index.val
    · have orderAtIndex := sorted ⟨cutoff, cutoffLt⟩ index afterCutoff
      rw [trueAtCutoff] at orderAtIndex
      have valueTrue : values index = true := by
        cases valueAt : values index
        · rw [valueAt] at orderAtIndex
          have impossible : ¬ (true ≤ false) := by decide
          exact False.elim (impossible orderAtIndex)
        · rfl
      simp [afterCutoff, valueTrue]
    · have beforeCutoff : index.val < cutoff := Nat.lt_of_not_ge afterCutoff
      have valueFalse : values index = false := by
        cases valueAt : values index
        · rfl
        · have earlierPredicate : predicate index.val :=
            ⟨index.isLt, valueAt⟩
          have minimum := Nat.find_min' existsPredicate earlierPredicate
          omega
      simp [afterCutoff, valueFalse]
  · refine ⟨wordCount, Nat.le_refl _, ?_⟩
    intro index
    have valueFalse : values index = false := by
      cases valueAt : values index
      · rfl
      · exact False.elim (anyTrue ⟨index, valueAt⟩)
    simp [valueFalse, Nat.not_le_of_lt index.isLt]

/-- 降順Boolean列は、あるcutoffより前がtrue、以後がfalseという形を持つ。 -/
theorem bool_sorted_descending_cutoff
    {wordCount : Nat} (values : Fin wordCount → Bool)
    (sorted : IsReverseSortedFin values) :
    ∃ cutoff, cutoff ≤ wordCount ∧
      ∀ index : Fin wordCount,
        values index = decide (index.val < cutoff) := by
  classical
  by_cases anyFalse : ∃ index : Fin wordCount, values index = false
  · let predicate : Nat → Prop := fun index =>
      ∃ inRange : index < wordCount,
        values ⟨index, inRange⟩ = false
    have existsPredicate : ∃ index, predicate index := by
      rcases anyFalse with ⟨index, falseAt⟩
      exact ⟨index.val, index.isLt, falseAt⟩
    let cutoff := Nat.find existsPredicate
    have cutoffSpec := Nat.find_spec existsPredicate
    rcases cutoffSpec with ⟨cutoffLt, falseAtCutoff⟩
    refine ⟨cutoff, Nat.le_of_lt cutoffLt, ?_⟩
    intro index
    by_cases beforeCutoff : index.val < cutoff
    · have valueTrue : values index = true := by
        cases valueAt : values index
        · have earlierPredicate : predicate index.val :=
            ⟨index.isLt, valueAt⟩
          have minimum := Nat.find_min' existsPredicate earlierPredicate
          omega
        · rfl
      simp [beforeCutoff, valueTrue]
    · have afterCutoff : cutoff ≤ index.val := Nat.le_of_not_gt beforeCutoff
      have orderAtIndex := sorted ⟨cutoff, cutoffLt⟩ index afterCutoff
      rw [falseAtCutoff] at orderAtIndex
      have valueFalse : values index = false := by
        cases valueAt : values index
        · rfl
        · rw [valueAt] at orderAtIndex
          have impossible : ¬ (true ≤ false) := by decide
          exact False.elim (impossible orderAtIndex)
      simp [beforeCutoff, valueFalse]
  · refine ⟨wordCount, Nat.le_refl _, ?_⟩
    intro index
    have valueTrue : values index = true := by
      cases valueAt : values index
      · exact False.elim (anyFalse ⟨index, valueAt⟩)
      · rfl
    simp [valueTrue, index.isLt]

/-- 同じ長さの二つの有限列を、前半と後半として連結する。 -/
def joinFinHalves {half : Nat} {α : Type*}
    (left right : Fin half → α) : Fin (2 * half) → α :=
  fun index =>
    if firstHalf : index.val < half then
      left ⟨index.val, firstHalf⟩
    else
      right ⟨index.val - half, by omega⟩

/-- 巡回区間の開始位置を0へ移した剰余座標。 -/
def cyclicCoordinate (wordCount offset index : Nat) : Nat :=
  (index + wordCount - offset) % wordCount

/-- Boolean列のtrue位置が巡回区間一個であることを表す。 -/
def IsCyclicTrueInterval {wordCount : Nat}
    (values : Fin wordCount → Bool) : Prop :=
  ∃ offset : Fin wordCount, ∃ count,
    count ≤ wordCount ∧
      ∀ index : Fin wordCount,
        values index = decide
          (cyclicCoordinate wordCount offset.val index.val < count)

/-- 昇順Boolean前半と降順Boolean後半の連結は巡回true区間になる。 -/
theorem join_sorted_halves_isCyclicTrueInterval
    {half : Nat} (positive : 0 < half)
    (left right : Fin half → Bool)
    (leftSorted : IsSortedFin left)
    (rightSorted : IsReverseSortedFin right) :
    IsCyclicTrueInterval (joinFinHalves left right) := by
  rcases bool_sorted_ascending_cutoff left leftSorted with
    ⟨leftCutoff, leftCutoffLe, leftShape⟩
  rcases bool_sorted_descending_cutoff right rightSorted with
    ⟨rightCutoff, rightCutoffLe, rightShape⟩
  let offset : Fin (2 * half) := ⟨leftCutoff, by omega⟩
  let count := half - leftCutoff + rightCutoff
  refine ⟨offset, count, by omega, ?_⟩
  intro index
  dsimp only [offset]
  unfold cyclicCoordinate
  by_cases firstHalf : index.val < half
  · rw [show joinFinHalves left right index =
        left ⟨index.val, firstHalf⟩ by
      simp [joinFinHalves, firstHalf]]
    rw [leftShape ⟨index.val, firstHalf⟩]
    by_cases beforeCutoff : index.val < leftCutoff
    · have coordinateLt :
          index.val + 2 * half - leftCutoff < 2 * half := by omega
      rw [Nat.mod_eq_of_lt coordinateLt]
      have leftFails : ¬ leftCutoff ≤ index.val :=
        Nat.not_le_of_lt beforeCutoff
      have intervalFails :
          ¬ index.val + 2 * half - leftCutoff <
            half - leftCutoff + rightCutoff := by omega
      simp [count, leftFails, intervalFails]
    · have afterCutoff : leftCutoff ≤ index.val :=
        Nat.le_of_not_gt beforeCutoff
      rw [Nat.mod_eq_sub_mod]
      · rw [Nat.mod_eq_of_lt]
        · have intervalPasses :
              index.val + 2 * half - leftCutoff - 2 * half <
                half - leftCutoff + rightCutoff := by omega
          simp [count, afterCutoff, intervalPasses]
        · omega
      · omega
  · have secondHalf : half ≤ index.val := Nat.le_of_not_gt firstHalf
    have localLt : index.val - half < half := by omega
    rw [show joinFinHalves left right index =
        right ⟨index.val - half, localLt⟩ by
      simp [joinFinHalves, firstHalf]]
    rw [rightShape ⟨index.val - half, localLt⟩]
    rw [Nat.mod_eq_sub_mod]
    · rw [Nat.mod_eq_of_lt]
      · by_cases rightPasses : index.val - half < rightCutoff
        · have intervalPasses :
              index.val + 2 * half - leftCutoff - 2 * half <
                half - leftCutoff + rightCutoff := by omega
          simp [count, rightPasses, intervalPasses]
        · have intervalFails :
              ¬ index.val + 2 * half - leftCutoff - 2 * half <
                half - leftCutoff + rightCutoff := by omega
          simp [count, rightPasses, intervalFails]
      · omega
    · omega

/--
長さ`2*h`のブロック内で距離`h`だけ進めた剰余は、前半から後半、後半から前半へ移る。
-/
theorem add_half_mod_two_mul
    (h remainder : Nat) (inRange : remainder < 2 * h) :
    (remainder + h) % (2 * h) =
      if remainder < h then remainder + h else remainder - h := by
  by_cases firstHalf : remainder < h
  · rw [if_pos firstHalf, Nat.mod_eq_of_lt]
    omega
  · rw [if_neg firstHalf]
    rw [Nat.mod_eq_sub_mod]
    · rw [Nat.mod_eq_of_lt]
      · omega
      · omega
    · omega

/-- 巡回座標で添字を半周期ずらすと、座標自身も半周期だけ巡回する。 -/
theorem cyclicCoordinate_add_half
    (half offset index : Nat) (positive : 0 < half)
    (offsetLt : offset < 2 * half) (indexLt : index < half) :
    cyclicCoordinate (2 * half) offset (index + half) =
      (cyclicCoordinate (2 * half) offset index + half) % (2 * half) := by
  unfold cyclicCoordinate
  by_cases offsetLeIndex : offset ≤ index
  · have firstCanSubtract : 2 * half ≤ index + 2 * half - offset := by
      omega
    have firstRemainderLt :
        index + 2 * half - offset - 2 * half < 2 * half := by omega
    have secondCanSubtract :
        2 * half ≤ index + half + 2 * half - offset := by omega
    have secondRemainderLt :
        index + half + 2 * half - offset - 2 * half < 2 * half := by omega
    rw [Nat.mod_eq_sub_mod firstCanSubtract,
      Nat.mod_eq_of_lt firstRemainderLt]
    rw [Nat.mod_eq_sub_mod secondCanSubtract,
      Nat.mod_eq_of_lt secondRemainderLt]
    rw [Nat.mod_eq_of_lt]
    · omega
    · omega
  · have indexLtOffset : index < offset := Nat.lt_of_not_ge offsetLeIndex
    have firstNumeratorLt : index + 2 * half - offset < 2 * half := by omega
    rw [Nat.mod_eq_of_lt firstNumeratorLt]
    by_cases offsetLePartner : offset ≤ index + half
    · have secondCanSubtract :
          2 * half ≤ index + half + 2 * half - offset := by omega
      have secondRemainderLt :
          index + half + 2 * half - offset - 2 * half < 2 * half := by omega
      rw [Nat.mod_eq_sub_mod secondCanSubtract,
        Nat.mod_eq_of_lt secondRemainderLt]
      rw [Nat.mod_eq_sub_mod]
      · rw [Nat.mod_eq_of_lt]
        · omega
        · omega
      · omega
    · have partnerLtOffset : index + half < offset :=
        Nat.lt_of_not_ge offsetLePartner
      have secondNumeratorLt :
          index + half + 2 * half - offset < 2 * half := by omega
      rw [Nat.mod_eq_of_lt secondNumeratorLt]
      rw [Nat.mod_eq_of_lt]
      · omega
      · omega

/-- 長さ`2*h`の巡回座標を`h`で剰余化すると、半区間上の巡回座標になる。 -/
theorem cyclicCoordinate_mod_half
    (half offset index : Nat) (positive : 0 < half)
    (offsetLt : offset < 2 * half) :
    cyclicCoordinate (2 * half) offset index % half =
      cyclicCoordinate half (offset % half) index := by
  unfold cyclicCoordinate
  rw [Nat.mod_mod_of_dvd]
  · by_cases offsetFirstHalf : offset < half
    · rw [Nat.mod_eq_of_lt offsetFirstHalf]
      have numeratorEquality :
          index + 2 * half - offset =
            (index + half - offset) + half := by omega
      rw [numeratorEquality, Nat.add_mod]
      simp
    · have halfLeOffset : half ≤ offset := Nat.le_of_not_gt offsetFirstHalf
      have reducedOffsetLt : offset - half < half := by omega
      rw [Nat.mod_eq_sub_mod halfLeOffset,
        Nat.mod_eq_of_lt reducedOffsetLt]
      have recoverOffset : half + (offset - half) = offset :=
        Nat.add_sub_of_le halfLeOffset
      have numeratorEquality :
          index + 2 * half - offset =
            index + half - (offset - half) := by omega
      rw [numeratorEquality]
  · exact ⟨2, by ring⟩

/-- 距離`half`の昇順比較後に前半へ置かれるBoolean値。 -/
def halfCompareLower {half : Nat} (ascending : Bool)
    (values : Fin (2 * half) → Bool) : Fin half → Bool :=
  fun index =>
    let partner : Fin (2 * half) := ⟨index.val + half, by omega⟩
    let original : Fin (2 * half) := ⟨index.val, by omega⟩
    if ascending then
      min (values original) (values partner)
    else max (values original) (values partner)

/-- 距離`half`の昇順比較後に後半へ置かれるBoolean値。 -/
def halfCompareUpper {half : Nat} (ascending : Bool)
    (values : Fin (2 * half) → Bool) : Fin half → Bool :=
  fun index =>
    let partner : Fin (2 * half) := ⟨index.val + half, by omega⟩
    let original : Fin (2 * half) := ⟨index.val, by omega⟩
    if ascending then
      max (values original) (values partner)
    else min (values original) (values partner)

/--
巡回true区間の半周期pairの最小値は、半長上で`count-half`個の巡回true区間になる。
-/
theorem cyclicBooleanPair_min
    (half coordinate count : Nat)
    (coordinateLt : coordinate < 2 * half) :
    min (decide (coordinate < count))
        (decide ((coordinate + half) % (2 * half) < count)) =
      decide (coordinate % half < count - half) := by
  rw [add_half_mod_two_mul half coordinate coordinateLt]
  by_cases firstHalf : coordinate < half
  · rw [if_pos firstHalf, Nat.mod_eq_of_lt firstHalf]
    by_cases countSmall : count ≤ half
    · have partnerFails : ¬ coordinate + half < count := by omega
      have resultFails : ¬ coordinate < count - half := by omega
      simp [partnerFails, resultFails]
    · have halfLtCount : half < count := Nat.lt_of_not_ge countSmall
      by_cases resultPasses : coordinate < count - half
      · have originalPasses : coordinate < count := by omega
        have partnerPasses : coordinate + half < count := by omega
        simp [originalPasses, partnerPasses, resultPasses]
      · have partnerFails : ¬ coordinate + half < count := by omega
        simp [partnerFails, resultPasses]
  · have halfLeCoordinate : half ≤ coordinate := Nat.le_of_not_gt firstHalf
    rw [if_neg firstHalf]
    rw [Nat.mod_eq_sub_mod halfLeCoordinate, Nat.mod_eq_of_lt]
    · by_cases countSmall : count ≤ half
      · have originalFails : ¬ coordinate < count := by omega
        have resultFails : ¬ coordinate - half < count - half := by omega
        simp [originalFails, resultFails]
      · have halfLtCount : half < count := Nat.lt_of_not_ge countSmall
        have partnerPasses : coordinate - half < count := by omega
        by_cases resultPasses : coordinate - half < count - half
        · have originalPasses : coordinate < count := by omega
          simp [originalPasses, partnerPasses, resultPasses]
        · have originalFails : ¬ coordinate < count := by omega
          simp [originalFails, resultPasses]
    · omega

/--
巡回true区間の半周期pairの最大値は、半長上で`min count half`個の巡回true区間になる。
-/
theorem cyclicBooleanPair_max
    (half coordinate count : Nat)
    (coordinateLt : coordinate < 2 * half) :
    max (decide (coordinate < count))
        (decide ((coordinate + half) % (2 * half) < count)) =
      decide (coordinate % half < min count half) := by
  rw [add_half_mod_two_mul half coordinate coordinateLt]
  by_cases firstHalf : coordinate < half
  · rw [if_pos firstHalf, Nat.mod_eq_of_lt firstHalf]
    by_cases countSmall : count ≤ half
    · rw [min_eq_left countSmall]
      have partnerFails : ¬ coordinate + half < count := by omega
      by_cases originalPasses : coordinate < count <;>
        simp [originalPasses, partnerFails]
    · have halfLeCount : half ≤ count := Nat.le_of_not_ge countSmall
      rw [min_eq_right halfLeCount]
      have originalPasses : coordinate < count := by omega
      simp [firstHalf, originalPasses]
  · have halfLeCoordinate : half ≤ coordinate := Nat.le_of_not_gt firstHalf
    rw [if_neg firstHalf]
    rw [Nat.mod_eq_sub_mod halfLeCoordinate, Nat.mod_eq_of_lt]
    · by_cases countSmall : count ≤ half
      · rw [min_eq_left countSmall]
        have originalFails : ¬ coordinate < count := by omega
        by_cases partnerPasses : coordinate - half < count <;>
          simp [originalFails, partnerPasses]
      · have halfLeCount : half ≤ count := Nat.le_of_not_ge countSmall
        rw [min_eq_right halfLeCount]
        have partnerPasses : coordinate - half < count := by omega
        have reducedCoordinateLt : coordinate - half < half := by omega
        simp [partnerPasses, reducedCoordinateLt]
    · omega

/-- half-cleaner前半の値を、半長の巡回座標とtrue個数で陽に表す。 -/
theorem halfCompareLower_shape
    {half : Nat} (positive : 0 < half) (ascending : Bool)
    (values : Fin (2 * half) → Bool)
    (offset : Fin (2 * half)) (count : Nat)
    (shape : ∀ index : Fin (2 * half),
      values index = decide
        (cyclicCoordinate (2 * half) offset.val index.val < count))
    (index : Fin half) :
    halfCompareLower ascending values index =
      decide (cyclicCoordinate half (offset.val % half) index.val <
        if ascending then count - half else min count half) := by
  let original : Fin (2 * half) := ⟨index.val, by omega⟩
  let partner : Fin (2 * half) := ⟨index.val + half, by omega⟩
  let coordinate := cyclicCoordinate (2 * half) offset.val index.val
  have coordinateLt : coordinate < 2 * half := by
    exact Nat.mod_lt _ (by omega)
  have partnerCoordinate :
      cyclicCoordinate (2 * half) offset.val (index.val + half) =
        (coordinate + half) % (2 * half) := by
    exact cyclicCoordinate_add_half half offset.val index.val positive
      offset.isLt index.isLt
  have projectedCoordinate :
      coordinate % half =
        cyclicCoordinate half (offset.val % half) index.val := by
    exact cyclicCoordinate_mod_half half offset.val index.val positive offset.isLt
  cases ascending with
  | false =>
      simp only [halfCompareLower, Bool.false_eq_true, if_false]
      rw [shape original, shape partner]
      change max (decide (coordinate < count))
          (decide (cyclicCoordinate (2 * half) offset.val
            (index.val + half) < count)) = _
      rw [partnerCoordinate]
      rw [cyclicBooleanPair_max half coordinate count coordinateLt]
      rw [projectedCoordinate]
  | true =>
      simp only [halfCompareLower, if_true]
      rw [shape original, shape partner]
      change min (decide (coordinate < count))
          (decide (cyclicCoordinate (2 * half) offset.val
            (index.val + half) < count)) = _
      rw [partnerCoordinate]
      rw [cyclicBooleanPair_min half coordinate count coordinateLt]
      rw [projectedCoordinate]

/-- half-cleaner後半の値を、半長の巡回座標とtrue個数で陽に表す。 -/
theorem halfCompareUpper_shape
    {half : Nat} (positive : 0 < half) (ascending : Bool)
    (values : Fin (2 * half) → Bool)
    (offset : Fin (2 * half)) (count : Nat)
    (shape : ∀ index : Fin (2 * half),
      values index = decide
        (cyclicCoordinate (2 * half) offset.val index.val < count))
    (index : Fin half) :
    halfCompareUpper ascending values index =
      decide (cyclicCoordinate half (offset.val % half) index.val <
        if ascending then min count half else count - half) := by
  let original : Fin (2 * half) := ⟨index.val, by omega⟩
  let partner : Fin (2 * half) := ⟨index.val + half, by omega⟩
  let coordinate := cyclicCoordinate (2 * half) offset.val index.val
  have coordinateLt : coordinate < 2 * half := by
    exact Nat.mod_lt _ (by omega)
  have partnerCoordinate :
      cyclicCoordinate (2 * half) offset.val (index.val + half) =
        (coordinate + half) % (2 * half) := by
    exact cyclicCoordinate_add_half half offset.val index.val positive
      offset.isLt index.isLt
  have projectedCoordinate :
      coordinate % half =
        cyclicCoordinate half (offset.val % half) index.val := by
    exact cyclicCoordinate_mod_half half offset.val index.val positive offset.isLt
  cases ascending with
  | false =>
      simp only [halfCompareUpper, Bool.false_eq_true, if_false]
      rw [shape original, shape partner]
      change min (decide (coordinate < count))
          (decide (cyclicCoordinate (2 * half) offset.val
            (index.val + half) < count)) = _
      rw [partnerCoordinate]
      rw [cyclicBooleanPair_min half coordinate count coordinateLt]
      rw [projectedCoordinate]
  | true =>
      simp only [halfCompareUpper, if_true]
      rw [shape original, shape partner]
      change max (decide (coordinate < count))
          (decide (cyclicCoordinate (2 * half) offset.val
            (index.val + half) < count)) = _
      rw [partnerCoordinate]
      rw [cyclicBooleanPair_max half coordinate count coordinateLt]
      rw [projectedCoordinate]

/-- half-cleaner前半は、入力が巡回true区間なら半長の巡回true区間になる。 -/
theorem halfCompareLower_isCyclicTrueInterval
    {half : Nat} (positive : 0 < half) (ascending : Bool)
    (values : Fin (2 * half) → Bool)
    (bitonic : IsCyclicTrueInterval values) :
    IsCyclicTrueInterval (halfCompareLower ascending values) := by
  rcases bitonic with ⟨offset, count, countLe, shape⟩
  let childOffset : Fin half := ⟨offset.val % half, Nat.mod_lt _ positive⟩
  cases ascending with
  | false =>
      refine ⟨childOffset, min count half, min_le_right _ _, ?_⟩
      intro index
      simpa [childOffset] using
        halfCompareLower_shape positive false values offset count shape index
  | true =>
      refine ⟨childOffset, count - half, by omega, ?_⟩
      intro index
      simpa [childOffset] using
        halfCompareLower_shape positive true values offset count shape index

/-- half-cleaner後半は、入力が巡回true区間なら半長の巡回true区間になる。 -/
theorem halfCompareUpper_isCyclicTrueInterval
    {half : Nat} (positive : 0 < half) (ascending : Bool)
    (values : Fin (2 * half) → Bool)
    (bitonic : IsCyclicTrueInterval values) :
    IsCyclicTrueInterval (halfCompareUpper ascending values) := by
  rcases bitonic with ⟨offset, count, countLe, shape⟩
  let childOffset : Fin half := ⟨offset.val % half, Nat.mod_lt _ positive⟩
  cases ascending with
  | false =>
      refine ⟨childOffset, count - half, by omega, ?_⟩
      intro index
      simpa [childOffset] using
        halfCompareUpper_shape positive false values offset count shape index
  | true =>
      refine ⟨childOffset, min count half, min_le_right _ _, ?_⟩
      intro index
      simpa [childOffset] using
        halfCompareUpper_shape positive true values offset count shape index

/--
half-cleaner後は、昇順なら前半全体が後半全体以下、降順なら後半全体が前半全体以下になる。
-/
theorem halfCompare_separated
    {half : Nat} (positive : 0 < half) (ascending : Bool)
    (values : Fin (2 * half) → Bool)
    (bitonic : IsCyclicTrueInterval values) :
    if ascending then
      ∀ left right,
        halfCompareLower ascending values left ≤
          halfCompareUpper ascending values right
    else
      ∀ left right,
        halfCompareUpper ascending values right ≤
          halfCompareLower ascending values left := by
  rcases bitonic with ⟨offset, count, countLe, shape⟩
  cases ascending with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      intro left right
      by_cases countSmall : count ≤ half
      · have upperFalse : halfCompareUpper false values right = false := by
          rw [halfCompareUpper_shape positive false values offset count shape right]
          have zeroCount : count - half = 0 := Nat.sub_eq_zero_of_le countSmall
          simp [zeroCount]
        simp [upperFalse]
      · have halfLeCount : half ≤ count := Nat.le_of_not_ge countSmall
        have lowerTrue : halfCompareLower false values left = true := by
          rw [halfCompareLower_shape positive false values offset count shape left]
          rw [min_eq_right halfLeCount]
          have coordinateLt :
              cyclicCoordinate half (offset.val % half) left.val < half :=
            Nat.mod_lt _ positive
          simp [coordinateLt]
        simp [lowerTrue]
  | true =>
      simp only [if_true]
      intro left right
      by_cases countSmall : count ≤ half
      · have lowerFalse : halfCompareLower true values left = false := by
          rw [halfCompareLower_shape positive true values offset count shape left]
          have zeroCount : count - half = 0 := Nat.sub_eq_zero_of_le countSmall
          simp [zeroCount]
        simp [lowerFalse]
      · have halfLeCount : half ≤ count := Nat.le_of_not_ge countSmall
        have upperTrue : halfCompareUpper true values right = true := by
          rw [halfCompareUpper_shape positive true values offset count shape right]
          rw [min_eq_right halfLeCount]
          have coordinateLt :
              cyclicCoordinate half (offset.val % half) right.val < half :=
            Nat.mod_lt _ positive
          simp [coordinateLt]
        simp [upperTrue]

/-- 同方向に整列済みで相互分離された二半分を連結すると、全体も同方向に整列する。 -/
theorem joinFinHalves_sortedDirection
    {half : Nat} (ascending : Bool)
    (left right : Fin half → Bool)
    (leftSorted : IsSortedDirectionFin ascending left)
    (rightSorted : IsSortedDirectionFin ascending right)
    (separated : if ascending then
      ∀ leftIndex rightIndex, left leftIndex ≤ right rightIndex
    else
      ∀ leftIndex rightIndex, right rightIndex ≤ left leftIndex) :
    IsSortedDirectionFin ascending (joinFinHalves left right) := by
  cases ascending with
  | false =>
      simp only [IsSortedDirectionFin, Bool.false_eq_true, if_false] at leftSorted rightSorted separated ⊢
      intro first second indexOrder
      by_cases firstInLeft : first.val < half
      · by_cases secondInLeft : second.val < half
        · rw [show joinFinHalves left right first =
              left ⟨first.val, firstInLeft⟩ by
            simp [joinFinHalves, firstInLeft]]
          rw [show joinFinHalves left right second =
              left ⟨second.val, secondInLeft⟩ by
            simp [joinFinHalves, secondInLeft]]
          exact leftSorted _ _ indexOrder
        · have secondLocalLt : second.val - half < half := by omega
          rw [show joinFinHalves left right first =
              left ⟨first.val, firstInLeft⟩ by
            simp [joinFinHalves, firstInLeft]]
          rw [show joinFinHalves left right second =
              right ⟨second.val - half, secondLocalLt⟩ by
            simp [joinFinHalves, secondInLeft]]
          exact separated _ _
      · have secondOutside : ¬ second.val < half := by omega
        have firstLocalLt : first.val - half < half := by omega
        have secondLocalLt : second.val - half < half := by omega
        rw [show joinFinHalves left right first =
            right ⟨first.val - half, firstLocalLt⟩ by
          simp [joinFinHalves, firstInLeft]]
        rw [show joinFinHalves left right second =
            right ⟨second.val - half, secondLocalLt⟩ by
          simp [joinFinHalves, secondOutside]]
        exact rightSorted ⟨first.val - half, firstLocalLt⟩
          ⟨second.val - half, secondLocalLt⟩
          (Nat.sub_le_sub_right indexOrder half)
  | true =>
      simp only [IsSortedDirectionFin, if_true] at leftSorted rightSorted separated ⊢
      intro first second indexOrder
      by_cases firstInLeft : first.val < half
      · by_cases secondInLeft : second.val < half
        · rw [show joinFinHalves left right first =
              left ⟨first.val, firstInLeft⟩ by
            simp [joinFinHalves, firstInLeft]]
          rw [show joinFinHalves left right second =
              left ⟨second.val, secondInLeft⟩ by
            simp [joinFinHalves, secondInLeft]]
          exact leftSorted _ _ indexOrder
        · have secondLocalLt : second.val - half < half := by omega
          rw [show joinFinHalves left right first =
              left ⟨first.val, firstInLeft⟩ by
            simp [joinFinHalves, firstInLeft]]
          rw [show joinFinHalves left right second =
              right ⟨second.val - half, secondLocalLt⟩ by
            simp [joinFinHalves, secondInLeft]]
          exact separated _ _
      · have secondOutside : ¬ second.val < half := by omega
        have firstLocalLt : first.val - half < half := by omega
        have secondLocalLt : second.val - half < half := by omega
        rw [show joinFinHalves left right first =
            right ⟨first.val - half, firstLocalLt⟩ by
          simp [joinFinHalves, firstInLeft]]
        rw [show joinFinHalves left right second =
            right ⟨second.val - half, secondLocalLt⟩ by
          simp [joinFinHalves, secondOutside]]
        exact rightSorted ⟨first.val - half, firstLocalLt⟩
          ⟨second.val - half, secondLocalLt⟩
          (Nat.sub_le_sub_right indexOrder half)

/--
巡回Boolean区間をhalf-cleanerで分割し、両半分を再帰的に同方向へmergeする純粋関数。
-/
def recursiveBoolBitonicMerge :
    (level : Nat) → (ascending : Bool) →
      (Fin (bitonicNetworkWidth level) → Bool) →
        Fin (bitonicNetworkWidth level) → Bool
  | 0, _, values => values
  | level + 1, ascending, values =>
      joinFinHalves
        (recursiveBoolBitonicMerge level ascending
          (halfCompareLower ascending values))
        (recursiveBoolBitonicMerge level ascending
          (halfCompareUpper ascending values))

/-- half-cleaner前半の各出力値は、元のpairのどちらか一方から来る。 -/
theorem halfCompareLower_from_input
    {half : Nat} (ascending : Bool)
    (values : Fin (2 * half) → Bool) (index : Fin half) :
    ∃ source : Fin (2 * half),
      halfCompareLower ascending values index = values source := by
  let original : Fin (2 * half) := ⟨index.val, by omega⟩
  let partner : Fin (2 * half) := ⟨index.val + half, by omega⟩
  cases ascending with
  | false =>
      by_cases ordered : values original ≤ values partner
      · refine ⟨partner, ?_⟩
        simp [halfCompareLower, original, partner, max_eq_right ordered]
      · have reverse : values partner ≤ values original := le_of_not_ge ordered
        refine ⟨original, ?_⟩
        simp [halfCompareLower, original, partner, max_eq_left reverse]
  | true =>
      by_cases ordered : values original ≤ values partner
      · refine ⟨original, ?_⟩
        simp [halfCompareLower, original, partner, min_eq_left ordered]
      · have reverse : values partner ≤ values original := le_of_not_ge ordered
        refine ⟨partner, ?_⟩
        simp [halfCompareLower, original, partner, min_eq_right reverse]

/-- half-cleaner後半の各出力値は、元のpairのどちらか一方から来る。 -/
theorem halfCompareUpper_from_input
    {half : Nat} (ascending : Bool)
    (values : Fin (2 * half) → Bool) (index : Fin half) :
    ∃ source : Fin (2 * half),
      halfCompareUpper ascending values index = values source := by
  let original : Fin (2 * half) := ⟨index.val, by omega⟩
  let partner : Fin (2 * half) := ⟨index.val + half, by omega⟩
  cases ascending with
  | false =>
      by_cases ordered : values original ≤ values partner
      · refine ⟨original, ?_⟩
        simp [halfCompareUpper, original, partner, min_eq_left ordered]
      · have reverse : values partner ≤ values original := le_of_not_ge ordered
        refine ⟨partner, ?_⟩
        simp [halfCompareUpper, original, partner, min_eq_right reverse]
  | true =>
      by_cases ordered : values original ≤ values partner
      · refine ⟨partner, ?_⟩
        simp [halfCompareUpper, original, partner, max_eq_right ordered]
      · have reverse : values partner ≤ values original := le_of_not_ge ordered
        refine ⟨original, ?_⟩
        simp [halfCompareUpper, original, partner, max_eq_left reverse]

/-- 再帰的bitonic mergeの各出力値は、同じ局所入力列のいずれか一要素である。 -/
theorem recursiveBoolBitonicMerge_from_input :
    ∀ (level : Nat) (ascending : Bool)
      (values : Fin (bitonicNetworkWidth level) → Bool)
      (index : Fin (bitonicNetworkWidth level)),
      ∃ source, recursiveBoolBitonicMerge level ascending values index =
        values source := by
  intro level
  induction level with
  | zero =>
      intro ascending values index
      exact ⟨index, rfl⟩
  | succ level inductionHypothesis =>
      intro ascending values index
      let half := bitonicNetworkWidth level
      by_cases firstHalf : index.val < half
      · let localIndex : Fin half := ⟨index.val, firstHalf⟩
        rcases inductionHypothesis ascending
            (halfCompareLower ascending values) localIndex with
          ⟨halfSource, sourceEquality⟩
        rcases halfCompareLower_from_input ascending values halfSource with
          ⟨source, halfEquality⟩
        refine ⟨source, ?_⟩
        change joinFinHalves
            (recursiveBoolBitonicMerge level ascending
              (halfCompareLower ascending values))
            (recursiveBoolBitonicMerge level ascending
              (halfCompareUpper ascending values)) index = values source
        rw [show joinFinHalves
              (recursiveBoolBitonicMerge level ascending
                (halfCompareLower ascending values))
              (recursiveBoolBitonicMerge level ascending
                (halfCompareUpper ascending values)) index =
            recursiveBoolBitonicMerge level ascending
              (halfCompareLower ascending values) localIndex by
          simp [joinFinHalves, firstHalf, localIndex, half]]
        exact sourceEquality.trans halfEquality
      · have secondHalf : half ≤ index.val := Nat.le_of_not_gt firstHalf
        have indexLt := index.isLt
        change index.val < 2 * half at indexLt
        have localLt : index.val - half < half := by omega
        let localIndex : Fin half := ⟨index.val - half, localLt⟩
        rcases inductionHypothesis ascending
            (halfCompareUpper ascending values) localIndex with
          ⟨halfSource, sourceEquality⟩
        rcases halfCompareUpper_from_input ascending values halfSource with
          ⟨source, halfEquality⟩
        refine ⟨source, ?_⟩
        change joinFinHalves
            (recursiveBoolBitonicMerge level ascending
              (halfCompareLower ascending values))
            (recursiveBoolBitonicMerge level ascending
              (halfCompareUpper ascending values)) index = values source
        rw [show joinFinHalves
              (recursiveBoolBitonicMerge level ascending
                (halfCompareLower ascending values))
              (recursiveBoolBitonicMerge level ascending
                (halfCompareUpper ascending values)) index =
            recursiveBoolBitonicMerge level ascending
              (halfCompareUpper ascending values) localIndex by
          simp [joinFinHalves, firstHalf, localIndex, half]]
        exact sourceEquality.trans halfEquality

/-- 任意levelの再帰的Boolean bitonic mergeは、巡回区間を指定方向へ整列する。 -/
theorem recursiveBoolBitonicMerge_sorted :
    ∀ (level : Nat) (ascending : Bool)
      (values : Fin (bitonicNetworkWidth level) → Bool),
      IsCyclicTrueInterval values →
        IsSortedDirectionFin ascending
          (recursiveBoolBitonicMerge level ascending values) := by
  intro level
  induction level with
  | zero =>
      intro ascending values _
      cases ascending with
      | false =>
          simp only [IsSortedDirectionFin, Bool.false_eq_true, if_false]
          intro left right _
          have leftLt := left.isLt
          have rightLt := right.isLt
          change left.val < 1 at leftLt
          change right.val < 1 at rightLt
          have equal : left = right := Fin.ext (by omega)
          subst right
          exact le_refl _
      | true =>
          simp only [IsSortedDirectionFin, if_true]
          intro left right _
          have leftLt := left.isLt
          have rightLt := right.isLt
          change left.val < 1 at leftLt
          change right.val < 1 at rightLt
          have equal : left = right := Fin.ext (by omega)
          subst right
          exact le_refl _
  | succ level inductionHypothesis =>
      intro ascending values bitonic
      let half := bitonicNetworkWidth level
      have positive : 0 < half := bitonicNetworkWidth_pos level
      have lowerBitonic :
          IsCyclicTrueInterval (halfCompareLower ascending values) :=
        halfCompareLower_isCyclicTrueInterval positive ascending values bitonic
      have upperBitonic :
          IsCyclicTrueInterval (halfCompareUpper ascending values) :=
        halfCompareUpper_isCyclicTrueInterval positive ascending values bitonic
      have lowerSorted := inductionHypothesis ascending
        (halfCompareLower ascending values) lowerBitonic
      have upperSorted := inductionHypothesis ascending
        (halfCompareUpper ascending values) upperBitonic
      have separated := halfCompare_separated positive ascending values bitonic
      exact joinFinHalves_sortedDirection ascending
        (recursiveBoolBitonicMerge level ascending
          (halfCompareLower ascending values))
        (recursiveBoolBitonicMerge level ascending
          (halfCompareUpper ascending values))
        lowerSorted upperSorted (by
          cases ascending with
          | false =>
              simp only [Bool.false_eq_true, if_false] at separated ⊢
              intro leftIndex rightIndex
              rcases recursiveBoolBitonicMerge_from_input level false
                  (halfCompareLower false values) leftIndex with
                ⟨leftSource, leftEquality⟩
              rcases recursiveBoolBitonicMerge_from_input level false
                  (halfCompareUpper false values) rightIndex with
                ⟨rightSource, rightEquality⟩
              rw [leftEquality, rightEquality]
              exact separated leftSource rightSource
          | true =>
              simp only [if_true] at separated ⊢
              intro leftIndex rightIndex
              rcases recursiveBoolBitonicMerge_from_input level true
                  (halfCompareLower true values) leftIndex with
                ⟨leftSource, leftEquality⟩
              rcases recursiveBoolBitonicMerge_from_input level true
                  (halfCompareUpper true values) rightIndex with
                ⟨rightSource, rightEquality⟩
              rw [leftEquality, rightEquality]
              exact separated leftSource rightSource)

/-- 長さ`2*half`の有限列から前半を取り出す。 -/
def lowerFinHalf {half : Nat} {α : Type*}
    (values : Fin (2 * half) → α) : Fin half → α :=
  fun index => values ⟨index.val, by omega⟩

/-- 長さ`2*half`の有限列から後半を取り出す。 -/
def upperFinHalf {half : Nat} {α : Type*}
    (values : Fin (2 * half) → α) : Fin half → α :=
  fun index => values ⟨index.val + half, by omega⟩

/-- 任意Boolean入力を二分し、逆方向sortとbitonic mergeを再帰する純粋Batcher sorter。 -/
def recursiveBoolBitonicSort :
    (level : Nat) →
      (Fin (bitonicNetworkWidth level) → Bool) →
        Fin (bitonicNetworkWidth level) → Bool
  | 0, values => values
  | level + 1, values =>
      recursiveBoolBitonicMerge (level + 1) true
        (joinFinHalves
          (recursiveBoolBitonicSort level (lowerFinHalf values))
          (recursiveBoolBitonicMerge level false
            (recursiveBoolBitonicSort level (upperFinHalf values))))

/-- 任意level・任意Boolean入力について、純粋Batcher sorterの出力は昇順である。 -/
theorem recursiveBoolBitonicSort_sorted :
    ∀ (level : Nat)
      (values : Fin (bitonicNetworkWidth level) → Bool),
      IsSortedFin (recursiveBoolBitonicSort level values) := by
  intro level
  induction level with
  | zero =>
      intro values left right _
      have leftLt := left.isLt
      have rightLt := right.isLt
      change left.val < 1 at leftLt
      change right.val < 1 at rightLt
      have equal : left = right := Fin.ext (by omega)
      subst right
      exact le_refl _
  | succ level inductionHypothesis =>
      intro values
      let sortedLeft := recursiveBoolBitonicSort level (lowerFinHalf values)
      let ascendingRight :=
        recursiveBoolBitonicSort level (upperFinHalf values)
      let sortedRight := recursiveBoolBitonicMerge level false ascendingRight
      have leftSorted : IsSortedFin sortedLeft := by
        exact inductionHypothesis (lowerFinHalf values)
      have rightAscending : IsSortedFin ascendingRight := by
        exact inductionHypothesis (upperFinHalf values)
      have rightAscendingCyclic : IsCyclicTrueInterval ascendingRight := by
        rcases bool_sorted_ascending_cutoff ascendingRight rightAscending with
          ⟨cutoff, cutoffLe, shape⟩
        by_cases allFalse : cutoff = bitonicNetworkWidth level
        · subst cutoff
          let offset : Fin (bitonicNetworkWidth level) :=
            ⟨0, bitonicNetworkWidth_pos level⟩
          refine ⟨offset, 0, Nat.zero_le _, ?_⟩
          intro index
          rw [shape index]
          have cutoffFails :
              ¬ bitonicNetworkWidth level ≤ index.val :=
            Nat.not_le_of_lt index.isLt
          simp [cyclicCoordinate, offset, cutoffFails]
        · have cutoffLt : cutoff < bitonicNetworkWidth level :=
            Nat.lt_of_le_of_ne cutoffLe allFalse
          let offset : Fin (bitonicNetworkWidth level) :=
            ⟨cutoff, cutoffLt⟩
          let count := bitonicNetworkWidth level - cutoff
          refine ⟨offset, count, by omega, ?_⟩
          intro index
          rw [shape index]
          unfold cyclicCoordinate
          dsimp only [offset, count]
          by_cases beforeCutoff : index.val < cutoff
          · have coordinateLt :
                index.val + bitonicNetworkWidth level - cutoff <
                  bitonicNetworkWidth level := by omega
            rw [Nat.mod_eq_of_lt coordinateLt]
            have leftFails : ¬ cutoff ≤ index.val :=
              Nat.not_le_of_lt beforeCutoff
            have rightFails :
                ¬ index.val + bitonicNetworkWidth level - cutoff <
                  bitonicNetworkWidth level - cutoff := by omega
            simp [leftFails, rightFails]
          · have afterCutoff : cutoff ≤ index.val :=
              Nat.le_of_not_gt beforeCutoff
            rw [Nat.mod_eq_sub_mod]
            · rw [Nat.mod_eq_of_lt]
              · have rightPasses :
                    index.val + bitonicNetworkWidth level - cutoff -
                        bitonicNetworkWidth level <
                      bitonicNetworkWidth level - cutoff := by omega
                simp [afterCutoff, rightPasses]
              · omega
            · omega
      have rightSortedDirection : IsReverseSortedFin sortedRight := by
        have merged := recursiveBoolBitonicMerge_sorted level false
          ascendingRight rightAscendingCyclic
        simpa [IsSortedDirectionFin, sortedRight] using merged
      have joinedBitonic :
          IsCyclicTrueInterval (joinFinHalves sortedLeft sortedRight) := by
        exact join_sorted_halves_isCyclicTrueInterval
          (bitonicNetworkWidth_pos level) sortedLeft sortedRight
          leftSorted rightSortedDirection
      have mergedSorted := recursiveBoolBitonicMerge_sorted (level + 1) true
        (joinFinHalves sortedLeft sortedRight) joinedBitonic
      simpa [recursiveBoolBitonicSort, sortedLeft, ascendingRight, sortedRight,
        IsSortedDirectionFin] using mergedSorted

/--
左右を昇順・降順へ再帰sortしてから、全体を指定方向へmergeする標準の方向付きBatcher sorter。
-/
def recursiveBoolBitonicSortDirection :
    (level : Nat) → (ascending : Bool) →
      (Fin (bitonicNetworkWidth level) → Bool) →
        Fin (bitonicNetworkWidth level) → Bool
  | 0, _, values => values
  | level + 1, ascending, values =>
      recursiveBoolBitonicMerge (level + 1) ascending
        (joinFinHalves
          (recursiveBoolBitonicSortDirection level true (lowerFinHalf values))
          (recursiveBoolBitonicSortDirection level false (upperFinHalf values)))

/-- 標準の方向付き純粋Batcher sorterは、任意入力を指定方向へ整列する。 -/
theorem recursiveBoolBitonicSortDirection_sorted :
    ∀ (level : Nat) (ascending : Bool)
      (values : Fin (bitonicNetworkWidth level) → Bool),
      IsSortedDirectionFin ascending
        (recursiveBoolBitonicSortDirection level ascending values) := by
  intro level
  induction level with
  | zero =>
      intro ascending values
      cases ascending with
      | false =>
          simp only [IsSortedDirectionFin, Bool.false_eq_true, if_false]
          intro left right _
          have leftLt := left.isLt
          have rightLt := right.isLt
          change left.val < 1 at leftLt
          change right.val < 1 at rightLt
          have equal : left = right := Fin.ext (by omega)
          subst right
          exact le_refl _
      | true =>
          simp only [IsSortedDirectionFin, if_true]
          intro left right _
          have leftLt := left.isLt
          have rightLt := right.isLt
          change left.val < 1 at leftLt
          change right.val < 1 at rightLt
          have equal : left = right := Fin.ext (by omega)
          subst right
          exact le_refl _
  | succ level inductionHypothesis =>
      intro ascending values
      let sortedLeft := recursiveBoolBitonicSortDirection level true
        (lowerFinHalf values)
      let sortedRight := recursiveBoolBitonicSortDirection level false
        (upperFinHalf values)
      have leftSortedDirection := inductionHypothesis true (lowerFinHalf values)
      have rightSortedDirection := inductionHypothesis false (upperFinHalf values)
      have leftSorted : IsSortedFin sortedLeft := by
        simpa [IsSortedDirectionFin, sortedLeft] using leftSortedDirection
      have rightSorted : IsReverseSortedFin sortedRight := by
        simpa [IsSortedDirectionFin, sortedRight] using rightSortedDirection
      have joinedBitonic :
          IsCyclicTrueInterval (joinFinHalves sortedLeft sortedRight) :=
        join_sorted_halves_isCyclicTrueInterval
          (bitonicNetworkWidth_pos level) sortedLeft sortedRight
          leftSorted rightSorted
      have merged := recursiveBoolBitonicMerge_sorted (level + 1) ascending
        (joinFinHalves sortedLeft sortedRight) joinedBitonic
      simpa [recursiveBoolBitonicSortDirection, sortedLeft, sortedRight] using merged

end VerifiedCircuitCore
