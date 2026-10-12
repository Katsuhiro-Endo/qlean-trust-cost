import QLean.Circuits.Foundation.BitonicValueSemantics

/-!
# 再帰的bitonic scheduleの一般実行意味論

history割当て前の`BitonicCompareExchange`を履歴幅1の型付き命令へ埋め込み、
再帰的Batcher scheduleの実行が純粋なhalf-cleaner・merge・sort関数と一致することを、
任意の線形順序上で証明する。行列や有限状態の列挙は用いない。
-/

namespace VerifiedCircuitCore

/-- historyなし命令を、唯一のhistory添字0を持つ型付き命令へ埋め込む。 -/
def BitonicCompareExchange.toUnitTyped {wordCount : Nat}
    (instruction : BitonicCompareExchange wordCount) :
    BitonicCompareExchangeWithHistory wordCount 1 :=
  { left := instruction.left
    right := instruction.right
    ascending := instruction.ascending
    history := 0 }

/-- historyなし命令一個の、任意の線形順序上での純粋な比較交換作用。 -/
def bareBitonicValueStep {wordCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchange wordCount)
    (values : Fin wordCount → α) : Fin wordCount → α :=
  typedBitonicValueStep instruction.toUnitTyped values

/-- historyなし命令列を実行順に畳み込む。 -/
def runBareBitonicValues {wordCount : Nat} {α : Type*} [LinearOrder α] :
    List (BitonicCompareExchange wordCount) →
      (Fin wordCount → α) → Fin wordCount → α
  | [], values => values
  | instruction :: schedule, values =>
      runBareBitonicValues schedule (bareBitonicValueStep instruction values)

/-- Bare命令列の実行は、history幅1へ変換した型付き命令列の実行に一致する。 -/
theorem runTyped_unitSchedule_eq_runBare
    {wordCount : Nat} {α : Type*} [LinearOrder α] :
    ∀ (schedule : List (BitonicCompareExchange wordCount))
      (values : Fin wordCount → α),
    runTypedBitonicValues (schedule.map
      BitonicCompareExchange.toUnitTyped) values =
      runBareBitonicValues schedule values
  | [], _ => rfl
  | _ :: schedule, values => by
      simp only [List.map_cons, runTypedBitonicValues, runBareBitonicValues,
        bareBitonicValueStep]
      exact runTyped_unitSchedule_eq_runBare schedule _

/-- 同じ半幅の二列を連結した列の前半を読む。 -/
@[simp] theorem joinFinHalves_left_apply
    {half : Nat} {α : Type*} (left right : Fin half → α)
    (index : Fin half) :
    joinFinHalves left right ⟨index.val, by omega⟩ = left index := by
  simp [joinFinHalves]

/-- 同じ半幅の二列を連結した列の後半を読む。 -/
@[simp] theorem joinFinHalves_right_apply
    {half : Nat} {α : Type*} (left right : Fin half → α)
    (index : Fin half) :
    joinFinHalves left right ⟨index.val + half, by omega⟩ = right index := by
  simp [joinFinHalves]

/-- half-cleaner後に前半へ置かれる、一般線形順序上の値。 -/
def halfCompareLowerValues {half : Nat} {α : Type*} [LinearOrder α]
    (ascending : Bool) (values : Fin (2 * half) → α) : Fin half → α :=
  fun index =>
    let original : Fin (2 * half) := ⟨index.val, by omega⟩
    let partner : Fin (2 * half) := ⟨index.val + half, by omega⟩
    if ascending then min (values original) (values partner)
    else max (values original) (values partner)

/-- half-cleaner後に後半へ置かれる、一般線形順序上の値。 -/
def halfCompareUpperValues {half : Nat} {α : Type*} [LinearOrder α]
    (ascending : Bool) (values : Fin (2 * half) → α) : Fin half → α :=
  fun index =>
    let original : Fin (2 * half) := ⟨index.val, by omega⟩
    let partner : Fin (2 * half) := ⟨index.val + half, by omega⟩
    if ascending then max (values original) (values partner)
    else min (values original) (values partner)

/-- half-cleanerの一対をhistory幅1の型付き命令として構成する。 -/
def unitHalfCleanerInstruction (half : Nat) (ascending : Bool)
    (index : Fin half) : BitonicCompareExchangeWithHistory (2 * half) 1 :=
  { left := ⟨index.val, by omega⟩
    right := ⟨index.val + half, by omega⟩
    ascending := ascending
    history := 0 }

/-- half-cleanerをhistory幅1へ変換すると、型付き一対命令のmapそのものになる。 -/
theorem unitTyped_bitonicHalfCleaner_eq
    (level : Nat) (ascending : Bool) :
    (bitonicHalfCleaner level ascending).map
        BitonicCompareExchange.toUnitTyped =
      (List.finRange (bitonicNetworkWidth level)).map
        (unitHalfCleanerInstruction (bitonicNetworkWidth level) ascending) := by
  simp [bitonicHalfCleaner, BitonicCompareExchange.toUnitTyped,
    unitHalfCleanerInstruction]

/-- 異なるhalf-cleaner pairは左右いずれの端点も共有しない。 -/
private theorem unitHalfCleaner_pairwise_aux
    (half : Nat) (ascending : Bool) :
    ∀ (indices : List (Fin half)), indices.Nodup →
      (indices.map (unitHalfCleanerInstruction half ascending)).Pairwise
        BitonicInstructionsDisjoint
  | [], _ => by simp
  | index :: indices, nodup => by
      have parts := List.nodup_cons.mp nodup
      simp only [List.map_cons, List.pairwise_cons]
      constructor
      · intro other member
        rcases List.mem_map.mp member with ⟨otherIndex, otherMember, rfl⟩
        have different : index ≠ otherIndex := by
          intro equal
          subst otherIndex
          exact parts.1 otherMember
        have indexLt := index.isLt
        have otherLt := otherIndex.isLt
        unfold BitonicInstructionsDisjoint
        constructor
        · intro equal
          apply different
          apply Fin.ext
          have values := congrArg Fin.val equal
          simpa [unitHalfCleanerInstruction] using values
        constructor
        · intro equal
          have values := congrArg Fin.val equal
          simp [unitHalfCleanerInstruction] at values
          omega
        constructor
        · intro equal
          have values := congrArg Fin.val equal
          simp [unitHalfCleanerInstruction] at values
          omega
        · intro equal
          apply different
          apply Fin.ext
          have values := congrArg Fin.val equal
          simpa [unitHalfCleanerInstruction] using Nat.add_right_cancel values
      · exact unitHalfCleaner_pairwise_aux half ascending indices parts.2

/-- 再帰幅のhalf-cleaner命令はpairwiseに端点を共有しない。 -/
theorem unitTyped_bitonicHalfCleaner_pairwise
    (level : Nat) (ascending : Bool) :
    ((bitonicHalfCleaner level ascending).map
      BitonicCompareExchange.toUnitTyped).Pairwise
        BitonicInstructionsDisjoint := by
  rw [unitTyped_bitonicHalfCleaner_eq]
  exact unitHalfCleaner_pairwise_aux _ _ _
    (List.nodup_finRange (bitonicNetworkWidth level))

/-- half-cleanerの各命令は異なる二つのwordを比較する。 -/
theorem unitHalfCleanerInstruction_distinct
    (half : Nat) (ascending : Bool) (index : Fin half) :
    (unitHalfCleanerInstruction half ascending index).left ≠
      (unitHalfCleanerInstruction half ascending index).right := by
  intro equal
  have values := congrArg Fin.val equal
  simp [unitHalfCleanerInstruction] at values
  omega

/-- bare half-cleanerの実行は、各pairのmin/maxを前後半へ配置する。 -/
theorem runBare_bitonicHalfCleaner
    (level : Nat) (ascending : Bool) {α : Type*} [LinearOrder α]
    (values : Fin (2 * bitonicNetworkWidth level) → α) :
    runBareBitonicValues (bitonicHalfCleaner level ascending) values =
      joinFinHalves (halfCompareLowerValues ascending values)
        (halfCompareUpperValues ascending values) := by
  rw [← runTyped_unitSchedule_eq_runBare]
  rw [unitTyped_bitonicHalfCleaner_eq]
  funext outputIndex
  let half := bitonicNetworkWidth level
  by_cases firstHalf : outputIndex.val < half
  · let localIndex : Fin half := ⟨outputIndex.val, firstHalf⟩
    let target := unitHalfCleanerInstruction half ascending localIndex
    have targetMember : target ∈
        (List.finRange half).map (unitHalfCleanerInstruction half ascending) := by
      exact List.mem_map.mpr ⟨localIndex, List.mem_finRange _, rfl⟩
    have endpoint : outputIndex = target.left := by
      apply Fin.ext
      rfl
    have action := runTypedBitonicValues_at_disjoint_member
      ((List.finRange half).map (unitHalfCleanerInstruction half ascending))
      target (unitHalfCleaner_pairwise_aux half ascending _
        (List.nodup_finRange half)) targetMember
      (unitHalfCleanerInstruction_distinct half ascending localIndex)
      values outputIndex (Or.inl endpoint)
    rw [action, endpoint]
    rw [typedBitonicValueStep_left target values
      (unitHalfCleanerInstruction_distinct half ascending localIndex)]
    change (if ascending then
        min (values target.left) (values target.right)
      else max (values target.left) (values target.right)) = _
    rw [show joinFinHalves (halfCompareLowerValues ascending values)
          (halfCompareUpperValues ascending values) target.left =
        halfCompareLowerValues ascending values localIndex by
      change joinFinHalves (halfCompareLowerValues ascending values)
          (halfCompareUpperValues ascending values)
          ⟨localIndex.val, by omega⟩ = _
      exact joinFinHalves_left_apply
        (halfCompareLowerValues ascending values)
        (halfCompareUpperValues ascending values) localIndex]
    simp [halfCompareLowerValues, target, unitHalfCleanerInstruction, half]
  · have secondHalf : half ≤ outputIndex.val := Nat.le_of_not_gt firstHalf
    have localLt : outputIndex.val - half < half := by
      have outputLt := outputIndex.isLt
      change outputIndex.val < 2 * half at outputLt
      omega
    let localIndex : Fin half := ⟨outputIndex.val - half, localLt⟩
    let target := unitHalfCleanerInstruction half ascending localIndex
    have targetMember : target ∈
        (List.finRange half).map (unitHalfCleanerInstruction half ascending) := by
      exact List.mem_map.mpr ⟨localIndex, List.mem_finRange _, rfl⟩
    have endpoint : outputIndex = target.right := by
      apply Fin.ext
      dsimp [target, unitHalfCleanerInstruction, localIndex]
      omega
    have action := runTypedBitonicValues_at_disjoint_member
      ((List.finRange half).map (unitHalfCleanerInstruction half ascending))
      target (unitHalfCleaner_pairwise_aux half ascending _
        (List.nodup_finRange half)) targetMember
      (unitHalfCleanerInstruction_distinct half ascending localIndex)
      values outputIndex (Or.inr endpoint)
    rw [action, endpoint]
    rw [typedBitonicValueStep_right target values
      (unitHalfCleanerInstruction_distinct half ascending localIndex)]
    change (if ascending then
        max (values target.left) (values target.right)
      else min (values target.left) (values target.right)) = _
    rw [show joinFinHalves (halfCompareLowerValues ascending values)
          (halfCompareUpperValues ascending values) target.right =
        halfCompareUpperValues ascending values localIndex by
      change joinFinHalves (halfCompareLowerValues ascending values)
          (halfCompareUpperValues ascending values)
          ⟨localIndex.val + half, by omega⟩ = _
      exact joinFinHalves_right_apply
        (halfCompareLowerValues ascending values)
        (halfCompareUpperValues ascending values) localIndex]
    simp [halfCompareUpperValues, target, unitHalfCleanerInstruction, half]

/-- Bare命令の左右添字が異なることを表す。 -/
def BareBitonicInstructionDistinct {wordCount : Nat}
    (instruction : BitonicCompareExchange wordCount) : Prop :=
  instruction.left ≠ instruction.right

/-- half-cleanerの全Bare命令は異なる二添字を比較する。 -/
theorem bitonicHalfCleaner_all_distinct
    (level : Nat) (ascending : Bool) :
    ∀ instruction ∈ bitonicHalfCleaner level ascending,
      BareBitonicInstructionDistinct instruction := by
  intro instruction member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  intro equal
  have values := congrArg Fin.val equal
  simp at values
  omega

/-- 左半への埋込みは左右添字の相異性を保存する。 -/
theorem BareBitonicInstructionDistinct.liftLeft
    {wordCount : Nat} {instruction : BitonicCompareExchange wordCount}
    (distinct : BareBitonicInstructionDistinct instruction) :
    BareBitonicInstructionDistinct instruction.liftLeft := by
  intro equal
  apply distinct
  apply Fin.ext
  have values := congrArg Fin.val equal
  simpa [BitonicCompareExchange.liftLeft] using values

/-- 右半への埋込みは左右添字の相異性を保存する。 -/
theorem BareBitonicInstructionDistinct.liftRight
    {wordCount : Nat} {instruction : BitonicCompareExchange wordCount}
    (distinct : BareBitonicInstructionDistinct instruction) :
    BareBitonicInstructionDistinct instruction.liftRight := by
  intro equal
  apply distinct
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp [BitonicCompareExchange.liftRight] at values
  omega

/-- Bare命令一個の左半埋込みは、連結列の左半だけへ元命令を作用させる。 -/
theorem bareBitonicValueStep_liftLeft_join
    {wordCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchange wordCount)
    (distinct : BareBitonicInstructionDistinct instruction)
    (left right : Fin wordCount → α) :
    bareBitonicValueStep instruction.liftLeft (joinFinHalves left right) =
      joinFinHalves (bareBitonicValueStep instruction left) right := by
  funext outputIndex
  let original := instruction.toUnitTyped
  let lifted := instruction.liftLeft.toUnitTyped
  have originalDistinct : original.left ≠ original.right := distinct
  have liftedDistinct : lifted.left ≠ lifted.right := distinct.liftLeft
  change typedBitonicValueStep lifted (joinFinHalves left right) outputIndex =
    joinFinHalves (typedBitonicValueStep original left) right outputIndex
  by_cases firstHalf : outputIndex.val < wordCount
  · let localIndex : Fin wordCount := ⟨outputIndex.val, firstHalf⟩
    by_cases isLeft : localIndex = instruction.left
    · have endpoint : outputIndex = lifted.left := by
        apply Fin.ext
        have values := congrArg Fin.val isLeft
        simpa [localIndex, lifted, BitonicCompareExchange.toUnitTyped,
          BitonicCompareExchange.liftLeft] using values
      rw [endpoint]
      rw [typedBitonicValueStep_left lifted (joinFinHalves left right)
        liftedDistinct]
      rw [show joinFinHalves (typedBitonicValueStep original left) right
            lifted.left = typedBitonicValueStep original left original.left by
        change joinFinHalves (typedBitonicValueStep original left) right
          ⟨instruction.left.val, by omega⟩ = _
        exact joinFinHalves_left_apply
          (typedBitonicValueStep original left) right instruction.left]
      rw [typedBitonicValueStep_left original left originalDistinct]
      simp [original, lifted,
        BitonicCompareExchange.toUnitTyped,
        BitonicCompareExchange.liftLeft]
    · by_cases isRight : localIndex = instruction.right
      · have endpoint : outputIndex = lifted.right := by
          apply Fin.ext
          have values := congrArg Fin.val isRight
          simpa [localIndex, lifted, BitonicCompareExchange.toUnitTyped,
            BitonicCompareExchange.liftLeft] using values
        rw [endpoint]
        rw [typedBitonicValueStep_right lifted (joinFinHalves left right)
          liftedDistinct]
        rw [show joinFinHalves (typedBitonicValueStep original left) right
              lifted.right = typedBitonicValueStep original left original.right by
          change joinFinHalves (typedBitonicValueStep original left) right
            ⟨instruction.right.val, by omega⟩ = _
          exact joinFinHalves_left_apply
            (typedBitonicValueStep original left) right instruction.right]
        rw [typedBitonicValueStep_right original left originalDistinct]
        simp [original, lifted,
          BitonicCompareExchange.toUnitTyped,
          BitonicCompareExchange.liftLeft]
      · rw [typedBitonicValueStep_other lifted (joinFinHalves left right)]
        · have outputEq : outputIndex =
              (⟨localIndex.val, by omega⟩ : Fin (2 * wordCount)) := by
            apply Fin.ext
            rfl
          rw [outputEq]
          rw [show joinFinHalves left right
                (⟨localIndex.val, by omega⟩ : Fin (2 * wordCount)) =
              left localIndex by
            exact joinFinHalves_left_apply left right localIndex]
          rw [show joinFinHalves (typedBitonicValueStep original left) right
                (⟨localIndex.val, by omega⟩ : Fin (2 * wordCount)) =
              typedBitonicValueStep original left localIndex by
            exact joinFinHalves_left_apply
              (typedBitonicValueStep original left) right localIndex]
          rw [typedBitonicValueStep_other original left localIndex]
          · simpa [original, BitonicCompareExchange.toUnitTyped] using isLeft
          · simpa [original, BitonicCompareExchange.toUnitTyped] using isRight
        · intro equal
          apply isLeft
          apply Fin.ext
          have values := congrArg Fin.val equal
          simpa [lifted, BitonicCompareExchange.toUnitTyped,
            BitonicCompareExchange.liftLeft] using values
        · intro equal
          apply isRight
          apply Fin.ext
          have values := congrArg Fin.val equal
          simpa [lifted, BitonicCompareExchange.toUnitTyped,
            BitonicCompareExchange.liftLeft] using values
  · have secondHalf : wordCount ≤ outputIndex.val := Nat.le_of_not_gt firstHalf
    have localLt : outputIndex.val - wordCount < wordCount := by
      have outputLt := outputIndex.isLt
      omega
    let localIndex : Fin wordCount := ⟨outputIndex.val - wordCount, localLt⟩
    have outputEq : outputIndex =
        (⟨localIndex.val + wordCount, by omega⟩ : Fin (2 * wordCount)) := by
      apply Fin.ext
      dsimp [localIndex]
      omega
    rw [typedBitonicValueStep_other lifted (joinFinHalves left right)]
    · rw [outputEq]
      simp
    · intro equal
      have values := congrArg Fin.val equal
      simp [lifted, BitonicCompareExchange.toUnitTyped,
        BitonicCompareExchange.liftLeft] at values
      omega
    · intro equal
      have values := congrArg Fin.val equal
      simp [lifted, BitonicCompareExchange.toUnitTyped,
        BitonicCompareExchange.liftLeft] at values
      omega

/-- Bare命令一個の右半埋込みは、連結列の右半だけへ元命令を作用させる。 -/
theorem bareBitonicValueStep_liftRight_join
    {wordCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchange wordCount)
    (distinct : BareBitonicInstructionDistinct instruction)
    (left right : Fin wordCount → α) :
    bareBitonicValueStep instruction.liftRight (joinFinHalves left right) =
      joinFinHalves left (bareBitonicValueStep instruction right) := by
  funext outputIndex
  let original := instruction.toUnitTyped
  let lifted := instruction.liftRight.toUnitTyped
  have originalDistinct : original.left ≠ original.right := distinct
  have liftedDistinct : lifted.left ≠ lifted.right := distinct.liftRight
  change typedBitonicValueStep lifted (joinFinHalves left right) outputIndex =
    joinFinHalves left (typedBitonicValueStep original right) outputIndex
  by_cases firstHalf : outputIndex.val < wordCount
  · let localIndex : Fin wordCount := ⟨outputIndex.val, firstHalf⟩
    have outputEq : outputIndex =
        (⟨localIndex.val, by omega⟩ : Fin (2 * wordCount)) := by
      apply Fin.ext
      rfl
    rw [typedBitonicValueStep_other lifted (joinFinHalves left right)]
    · rw [outputEq]
      simp
    · intro equal
      have values := congrArg Fin.val equal
      simp [lifted, BitonicCompareExchange.toUnitTyped,
        BitonicCompareExchange.liftRight] at values
      omega
    · intro equal
      have values := congrArg Fin.val equal
      simp [lifted, BitonicCompareExchange.toUnitTyped,
        BitonicCompareExchange.liftRight] at values
      omega
  · have secondHalf : wordCount ≤ outputIndex.val := Nat.le_of_not_gt firstHalf
    have localLt : outputIndex.val - wordCount < wordCount := by
      have outputLt := outputIndex.isLt
      omega
    let localIndex : Fin wordCount := ⟨outputIndex.val - wordCount, localLt⟩
    have outputEq : outputIndex =
        (⟨localIndex.val + wordCount, by omega⟩ : Fin (2 * wordCount)) := by
      apply Fin.ext
      dsimp [localIndex]
      omega
    by_cases isLeft : localIndex = instruction.left
    · have endpoint : outputIndex = lifted.left := by
        apply Fin.ext
        have values := congrArg Fin.val isLeft
        simp [localIndex, lifted, BitonicCompareExchange.toUnitTyped,
          BitonicCompareExchange.liftRight] at values ⊢
        omega
      rw [endpoint]
      rw [typedBitonicValueStep_left lifted (joinFinHalves left right)
        liftedDistinct]
      rw [show joinFinHalves left (typedBitonicValueStep original right)
            lifted.left = typedBitonicValueStep original right original.left by
        change joinFinHalves left (typedBitonicValueStep original right)
          ⟨instruction.left.val + wordCount, by omega⟩ = _
        exact joinFinHalves_right_apply left
          (typedBitonicValueStep original right) instruction.left]
      rw [typedBitonicValueStep_left original right originalDistinct]
      simp [original, lifted,
        BitonicCompareExchange.toUnitTyped,
        BitonicCompareExchange.liftRight]
    · by_cases isRight : localIndex = instruction.right
      · have endpoint : outputIndex = lifted.right := by
          apply Fin.ext
          have values := congrArg Fin.val isRight
          simp [localIndex, lifted, BitonicCompareExchange.toUnitTyped,
            BitonicCompareExchange.liftRight] at values ⊢
          omega
        rw [endpoint]
        rw [typedBitonicValueStep_right lifted (joinFinHalves left right)
          liftedDistinct]
        rw [show joinFinHalves left (typedBitonicValueStep original right)
              lifted.right = typedBitonicValueStep original right original.right by
          change joinFinHalves left (typedBitonicValueStep original right)
            ⟨instruction.right.val + wordCount, by omega⟩ = _
          exact joinFinHalves_right_apply left
            (typedBitonicValueStep original right) instruction.right]
        rw [typedBitonicValueStep_right original right originalDistinct]
        simp [original, lifted,
          BitonicCompareExchange.toUnitTyped,
          BitonicCompareExchange.liftRight]
      · rw [typedBitonicValueStep_other lifted (joinFinHalves left right)]
        · rw [outputEq]
          rw [show joinFinHalves left right
                (⟨localIndex.val + wordCount, by omega⟩ : Fin (2 * wordCount)) =
              right localIndex by
            exact joinFinHalves_right_apply left right localIndex]
          rw [show joinFinHalves left (typedBitonicValueStep original right)
                (⟨localIndex.val + wordCount, by omega⟩ : Fin (2 * wordCount)) =
              typedBitonicValueStep original right localIndex by
            exact joinFinHalves_right_apply left
              (typedBitonicValueStep original right) localIndex]
          rw [typedBitonicValueStep_other original right localIndex]
          · simpa [original, BitonicCompareExchange.toUnitTyped] using isLeft
          · simpa [original, BitonicCompareExchange.toUnitTyped] using isRight
        · intro equal
          apply isLeft
          apply Fin.ext
          have rewritten :
              (⟨localIndex.val + wordCount, by omega⟩ : Fin (2 * wordCount)) =
                lifted.left := outputEq.symm.trans equal
          have values := congrArg Fin.val rewritten
          simp [lifted, BitonicCompareExchange.toUnitTyped,
            BitonicCompareExchange.liftRight] at values
          omega
        · intro equal
          apply isRight
          apply Fin.ext
          have rewritten :
              (⟨localIndex.val + wordCount, by omega⟩ : Fin (2 * wordCount)) =
                lifted.right := outputEq.symm.trans equal
          have values := congrArg Fin.val rewritten
          simp [lifted, BitonicCompareExchange.toUnitTyped,
            BitonicCompareExchange.liftRight] at values
          omega

/-- Bare命令列実行はschedule連結を順次実行へ写す。 -/
theorem runBareBitonicValues_append
    {wordCount : Nat} {α : Type*} [LinearOrder α] :
    ∀ (first second : List (BitonicCompareExchange wordCount))
      (values : Fin wordCount → α),
    runBareBitonicValues (first ++ second) values =
      runBareBitonicValues second (runBareBitonicValues first values)
  | [], _, _ => rfl
  | _ :: first, second, values => by
      simp only [List.cons_append, runBareBitonicValues]
      exact runBareBitonicValues_append first second _

/-- 左半へ埋め込んだ命令列は、連結列の左半だけへ元scheduleを実行する。 -/
theorem runBareBitonicValues_map_liftLeft
    {wordCount : Nat} {α : Type*} [LinearOrder α] :
    ∀ (schedule : List (BitonicCompareExchange wordCount)),
      (∀ instruction ∈ schedule, BareBitonicInstructionDistinct instruction) →
      ∀ (left right : Fin wordCount → α),
      runBareBitonicValues
          (schedule.map BitonicCompareExchange.liftLeft)
          (joinFinHalves left right) =
        joinFinHalves (runBareBitonicValues schedule left) right
  | [], _, _, _ => rfl
  | instruction :: schedule, distinct, left, right => by
      simp only [List.map_cons, runBareBitonicValues]
      rw [bareBitonicValueStep_liftLeft_join instruction
        (distinct instruction (by simp))]
      rw [runBareBitonicValues_map_liftLeft schedule (by
        intro next member
        exact distinct next (by simp [member]))]

/-- 右半へ埋め込んだ命令列は、連結列の右半だけへ元scheduleを実行する。 -/
theorem runBareBitonicValues_map_liftRight
    {wordCount : Nat} {α : Type*} [LinearOrder α] :
    ∀ (schedule : List (BitonicCompareExchange wordCount)),
      (∀ instruction ∈ schedule, BareBitonicInstructionDistinct instruction) →
      ∀ (left right : Fin wordCount → α),
      runBareBitonicValues
          (schedule.map BitonicCompareExchange.liftRight)
          (joinFinHalves left right) =
        joinFinHalves left (runBareBitonicValues schedule right)
  | [], _, _, _ => rfl
  | instruction :: schedule, distinct, left, right => by
      simp only [List.map_cons, runBareBitonicValues]
      rw [bareBitonicValueStep_liftRight_join instruction
        (distinct instruction (by simp))]
      rw [runBareBitonicValues_map_liftRight schedule (by
        intro next member
        exact distinct next (by simp [member]))]

/-- 再帰merge scheduleの全命令は異なる二添字を比較する。 -/
theorem bitonicMergeSchedule_all_distinct :
    ∀ (level : Nat) (ascending : Bool)
      (instruction : BitonicCompareExchange (bitonicNetworkWidth level)),
      instruction ∈ bitonicMergeSchedule level ascending →
        BareBitonicInstructionDistinct instruction := by
  intro level
  induction level with
  | zero =>
      intro ascending instruction member
      simp [bitonicMergeSchedule] at member
  | succ level inductionHypothesis =>
      intro ascending instruction member
      change instruction ∈
        bitonicHalfCleaner level ascending ++
          (bitonicMergeSchedule level ascending).map
            BitonicCompareExchange.liftLeft ++
          (bitonicMergeSchedule level ascending).map
            BitonicCompareExchange.liftRight at member
      rcases List.mem_append.mp member with prefixMember | rightMember
      · rcases List.mem_append.mp prefixMember with halfMember | leftMember
        · exact bitonicHalfCleaner_all_distinct level ascending
            instruction halfMember
        · rcases List.mem_map.mp leftMember with ⟨source, sourceMember, rfl⟩
          exact (inductionHypothesis ascending source sourceMember).liftLeft
      · rcases List.mem_map.mp rightMember with ⟨source, sourceMember, rfl⟩
        exact (inductionHypothesis ascending source sourceMember).liftRight

/-- 再帰sort scheduleの全命令は異なる二添字を比較する。 -/
theorem bitonicSortSchedule_all_distinct :
    ∀ (level : Nat) (ascending : Bool)
      (instruction : BitonicCompareExchange (bitonicNetworkWidth level)),
      instruction ∈ bitonicSortSchedule level ascending →
        BareBitonicInstructionDistinct instruction := by
  intro level
  induction level with
  | zero =>
      intro ascending instruction member
      simp [bitonicSortSchedule] at member
  | succ level inductionHypothesis =>
      intro ascending instruction member
      let merge : List (BitonicCompareExchange
          (2 * bitonicNetworkWidth level)) := by
        simpa [bitonicNetworkWidth,
          VerifiedCircuitCore.bitonicNetworkWidth] using
          bitonicMergeSchedule (level + 1) ascending
      change instruction ∈
        (bitonicSortSchedule level true).map
            BitonicCompareExchange.liftLeft ++
          (bitonicSortSchedule level false).map
            BitonicCompareExchange.liftRight ++
          merge at member
      rcases List.mem_append.mp member with prefixMember | mergeMember
      · rcases List.mem_append.mp prefixMember with leftMember | rightMember
        · rcases List.mem_map.mp leftMember with ⟨source, sourceMember, rfl⟩
          exact (inductionHypothesis true source sourceMember).liftLeft
        · rcases List.mem_map.mp rightMember with ⟨source, sourceMember, rfl⟩
          exact (inductionHypothesis false source sourceMember).liftRight
      · have originalMember : instruction ∈
            bitonicMergeSchedule (level + 1) ascending := by
          simpa [merge, bitonicNetworkWidth,
            VerifiedCircuitCore.bitonicNetworkWidth] using mergeMember
        exact bitonicMergeSchedule_all_distinct (level + 1) ascending
          instruction originalMember

/-- 任意の倍幅有限列は、自身の前半と後半を連結すると復元される。 -/
theorem joinFinHalves_lower_upper
    {half : Nat} {α : Type*} (values : Fin (2 * half) → α) :
    joinFinHalves (lowerFinHalf values) (upperFinHalf values) = values := by
  funext index
  by_cases firstHalf : index.val < half
  · simp [joinFinHalves, lowerFinHalf, firstHalf]
  · have halfLe : half ≤ index.val := Nat.le_of_not_gt firstHalf
    have reduced : index.val - half + half = index.val := by omega
    simp [joinFinHalves, upperFinHalf, firstHalf]
    congr

/-- 左半埋込みscheduleを任意の倍幅列へ作用させた形。 -/
theorem runBareBitonicValues_map_liftLeft_full
    {wordCount : Nat} {α : Type*} [LinearOrder α]
    (schedule : List (BitonicCompareExchange wordCount))
    (distinct : ∀ instruction ∈ schedule,
      BareBitonicInstructionDistinct instruction)
    (values : Fin (2 * wordCount) → α) :
    runBareBitonicValues
        (schedule.map BitonicCompareExchange.liftLeft) values =
      joinFinHalves
        (runBareBitonicValues schedule (lowerFinHalf values))
        (upperFinHalf values) := by
  calc
    runBareBitonicValues
        (schedule.map BitonicCompareExchange.liftLeft) values =
        runBareBitonicValues
          (schedule.map BitonicCompareExchange.liftLeft)
          (joinFinHalves (lowerFinHalf values) (upperFinHalf values)) := by
      rw [joinFinHalves_lower_upper]
    _ = joinFinHalves
          (runBareBitonicValues schedule (lowerFinHalf values))
          (upperFinHalf values) :=
      runBareBitonicValues_map_liftLeft (α := α) schedule distinct
        (lowerFinHalf values) (upperFinHalf values)

/-- 任意線形順序上の再帰的bitonic merge参照関数。 -/
def recursiveBitonicMergeValues {α : Type*} [LinearOrder α] :
    (level : Nat) → (ascending : Bool) →
      (Fin (bitonicNetworkWidth level) → α) →
        Fin (bitonicNetworkWidth level) → α
  | 0, _, values => values
  | level + 1, ascending, values =>
      joinFinHalves
        (recursiveBitonicMergeValues level ascending
          (halfCompareLowerValues ascending values))
        (recursiveBitonicMergeValues level ascending
          (halfCompareUpperValues ascending values))

/-- 任意線形順序上の、方向を指定した再帰的Batcher sort参照関数。 -/
def recursiveBitonicSortDirectionValues {α : Type*} [LinearOrder α] :
    (level : Nat) → (ascending : Bool) →
      (Fin (bitonicNetworkWidth level) → α) →
        Fin (bitonicNetworkWidth level) → α
  | 0, _, values => values
  | level + 1, ascending, values =>
      recursiveBitonicMergeValues (level + 1) ascending
        (joinFinHalves
          (recursiveBitonicSortDirectionValues level true
            (lowerFinHalf values))
          (recursiveBitonicSortDirectionValues level false
            (upperFinHalf values)))

/-- Bare再帰merge scheduleの実行は一般再帰merge参照関数に一致する。 -/
theorem runBare_recursiveBitonicMerge_eq :
    ∀ (level : Nat) (ascending : Bool) {α : Type*} [LinearOrder α]
      (values : Fin (bitonicNetworkWidth level) → α),
    runBareBitonicValues (bitonicMergeSchedule level ascending) values =
      recursiveBitonicMergeValues level ascending values := by
  intro level
  induction level with
  | zero =>
      intro ascending α order values
      rfl
  | succ level inductionHypothesis =>
      intro ascending α order values
      simp only [bitonicNetworkWidth,
        VerifiedCircuitCore.bitonicNetworkWidth] at values ⊢
      simp only [bitonicMergeSchedule, recursiveBitonicMergeValues]
      rw [runBareBitonicValues_append]
      rw [runBareBitonicValues_append]
      rw [runBare_bitonicHalfCleaner]
      rw [runBareBitonicValues_map_liftLeft _
        (bitonicMergeSchedule_all_distinct level ascending)]
      rw [runBareBitonicValues_map_liftRight _
        (bitonicMergeSchedule_all_distinct level ascending)]
      rw [inductionHypothesis ascending]
      rw [inductionHypothesis ascending]

/-- Bare再帰sort scheduleの実行は一般方向付きBatcher参照関数に一致する。 -/
theorem runBare_recursiveBitonicSort_eq :
    ∀ (level : Nat) (ascending : Bool) {α : Type*} [LinearOrder α]
      (values : Fin (bitonicNetworkWidth level) → α),
    runBareBitonicValues (bitonicSortSchedule level ascending) values =
      recursiveBitonicSortDirectionValues level ascending values := by
  intro level
  induction level with
  | zero =>
      intro ascending α order values
      rfl
  | succ level inductionHypothesis =>
      intro ascending α order values
      simp only [bitonicNetworkWidth,
        VerifiedCircuitCore.bitonicNetworkWidth] at values ⊢
      simp only [bitonicSortSchedule,
        recursiveBitonicSortDirectionValues]
      rw [runBareBitonicValues_append]
      rw [runBareBitonicValues_append]
      rw [runBareBitonicValues_map_liftLeft_full _
        (bitonicSortSchedule_all_distinct level true)]
      rw [runBareBitonicValues_map_liftRight _
        (bitonicSortSchedule_all_distinct level false)]
      rw [inductionHypothesis true]
      rw [inductionHypothesis false]
      have merged := runBare_recursiveBitonicMerge_eq (level + 1) ascending
        (joinFinHalves
          (recursiveBitonicSortDirectionValues level true
            (lowerFinHalf values))
          (recursiveBitonicSortDirectionValues level false
            (upperFinHalf values)))
      simpa only [id_eq, bitonicNetworkWidth,
        VerifiedCircuitCore.bitonicNetworkWidth] using merged

/-- Boolean上の一般half-cleaner前半は既存のBoolean参照関数に一致する。 -/
theorem halfCompareLowerValues_bool_eq
    {half : Nat} (ascending : Bool)
    (values : Fin (2 * half) → Bool) :
    halfCompareLowerValues ascending values =
      halfCompareLower ascending values := by
  rfl

/-- Boolean上の一般half-cleaner後半は既存のBoolean参照関数に一致する。 -/
theorem halfCompareUpperValues_bool_eq
    {half : Nat} (ascending : Bool)
    (values : Fin (2 * half) → Bool) :
    halfCompareUpperValues ascending values =
      halfCompareUpper ascending values := by
  rfl

/-- 一般再帰mergeのBoolean特殊化は既存の`recursiveBoolBitonicMerge`に一致する。 -/
theorem recursiveBitonicMergeValues_bool_eq :
    ∀ (level : Nat) (ascending : Bool)
      (values : Fin (bitonicNetworkWidth level) → Bool),
    recursiveBitonicMergeValues level ascending values =
      recursiveBoolBitonicMerge level ascending values := by
  intro level
  induction level with
  | zero =>
      intro ascending values
      rfl
  | succ level inductionHypothesis =>
      intro ascending values
      simp only [recursiveBitonicMergeValues, recursiveBoolBitonicMerge]
      rw [halfCompareLowerValues_bool_eq]
      rw [halfCompareUpperValues_bool_eq]
      rw [inductionHypothesis ascending]
      rw [inductionHypothesis ascending]

/-- 一般方向付きsortのBoolean特殊化は既存のBoolean参照関数に一致する。 -/
theorem recursiveBitonicSortDirectionValues_bool_eq :
    ∀ (level : Nat) (ascending : Bool)
      (values : Fin (bitonicNetworkWidth level) → Bool),
    recursiveBitonicSortDirectionValues level ascending values =
      recursiveBoolBitonicSortDirection level ascending values := by
  intro level
  induction level with
  | zero =>
      intro ascending values
      rfl
  | succ level inductionHypothesis =>
      intro ascending values
      simp only [recursiveBitonicSortDirectionValues,
        recursiveBoolBitonicSortDirection]
      rw [recursiveBitonicMergeValues_bool_eq]
      rw [inductionHypothesis true]
      rw [inductionHypothesis false]

/-- Bare再帰merge scheduleのBoolean実行は既存の再帰merge参照関数に一致する。 -/
theorem runBare_recursiveBitonicMerge_bool_eq
    (level : Nat) (ascending : Bool)
    (values : Fin (bitonicNetworkWidth level) → Bool) :
    runBareBitonicValues (bitonicMergeSchedule level ascending) values =
      recursiveBoolBitonicMerge level ascending values := by
  rw [runBare_recursiveBitonicMerge_eq]
  exact recursiveBitonicMergeValues_bool_eq level ascending values

/-- Bare再帰sort scheduleのBoolean実行は既存の方向付きsort参照関数に一致する。 -/
theorem runBare_recursiveBitonicSort_bool_eq
    (level : Nat) (ascending : Bool)
    (values : Fin (bitonicNetworkWidth level) → Bool) :
    runBareBitonicValues (bitonicSortSchedule level ascending) values =
      recursiveBoolBitonicSortDirection level ascending values := by
  rw [runBare_recursiveBitonicSort_eq]
  exact recursiveBitonicSortDirectionValues_bool_eq level ascending values

/-- The standard merge schedule implements the recursive merge reference over
any linear order. -/
theorem runBitonicMergeSchedule_eq_recursiveReference
    (level : Nat) (ascending : Bool) {α : Type*} [LinearOrder α]
    (values : Fin (bitonicNetworkWidth level) → α) :
    runBareBitonicValues (bitonicMergeSchedule level ascending) values =
      recursiveBitonicMergeValues level ascending values :=
  runBare_recursiveBitonicMerge_eq level ascending values

/-- The standard sorting schedule implements the recursive sorting reference
over any linear order. -/
theorem runBitonicSortSchedule_eq_recursiveReference
    (level : Nat) (ascending : Bool) {α : Type*} [LinearOrder α]
    (values : Fin (bitonicNetworkWidth level) → α) :
    runBareBitonicValues (bitonicSortSchedule level ascending) values =
      recursiveBitonicSortDirectionValues level ascending values :=
  runBare_recursiveBitonicSort_eq level ascending values

/-- The standard sorting schedule sorts every Boolean input in its requested
direction. -/
theorem runBitonicSortSchedule_sorts_bool
    (level : Nat) (ascending : Bool)
    (values : Fin (bitonicNetworkWidth level) → Bool) :
    IsSortedDirectionFin ascending
      (runBareBitonicValues (bitonicSortSchedule level ascending) values) := by
  rw [runBare_recursiveBitonicSort_bool_eq]
  exact recursiveBoolBitonicSortDirection_sorted level ascending values

/-- Thresholding a natural-valued input commutes with any distinct raw
compare-exchange schedule. -/
theorem thresholdValues_runBareBitonicValues
    {wordCount : Nat} (schedule : List (BitonicCompareExchange wordCount))
    (distinct : ∀ instruction ∈ schedule,
      instruction.left ≠ instruction.right)
    (threshold : Nat) (values : Fin wordCount → Nat) :
    thresholdValues threshold (runBareBitonicValues schedule values) =
      runBareBitonicValues schedule (thresholdValues threshold values) := by
  let typedSchedule := schedule.map BitonicCompareExchange.toUnitTyped
  calc
    thresholdValues threshold (runBareBitonicValues schedule values) =
        thresholdValues threshold
          (runTypedBitonicValues typedSchedule values) := by
      rw [runTyped_unitSchedule_eq_runBare]
    _ = runTypedBitonicValues typedSchedule
          (thresholdValues threshold values) := by
      apply thresholdValues_runTypedBitonicValues
      intro instruction member
      rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
      exact distinct original originalMember
    _ = runBareBitonicValues schedule
          (thresholdValues threshold values) :=
      runTyped_unitSchedule_eq_runBare schedule _

/-- The ascending standard sorting schedule sorts every natural-valued input. -/
theorem bitonicSortSchedule_sorts_nat
    (level : Nat) (values : Fin (bitonicNetworkWidth level) → Nat) :
    IsSortedFin
      (runBareBitonicValues (bitonicSortSchedule level true) values) := by
  apply isSortedFin_of_thresholds
  intro threshold
  rw [thresholdValues_runBareBitonicValues
    (bitonicSortSchedule level true)
    (bitonicSortSchedule_all_distinct level true)]
  simpa [IsSortedDirectionFin] using
    runBitonicSortSchedule_sorts_bool level true
      (thresholdValues threshold values)

/-- Erase the history slot of a typed compare-exchange instruction. -/
def BitonicCompareExchangeWithHistory.eraseHistory
    {wordCount historyCount : Nat}
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount) :
    BitonicCompareExchange wordCount where
  left := instruction.left
  right := instruction.right
  ascending := instruction.ascending

/-- History indices do not affect the pure value action of one instruction. -/
theorem typedBitonicValueStep_eraseHistory
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (instruction : BitonicCompareExchangeWithHistory wordCount historyCount)
    (values : Fin wordCount → α) :
    typedBitonicValueStep instruction values =
      bareBitonicValueStep instruction.eraseHistory values := by
  rfl

/-- Erasing history from a typed schedule preserves its pure value action. -/
theorem runTypedBitonicValues_eq_runBare_eraseHistory
    {wordCount historyCount : Nat} {α : Type*} [LinearOrder α]
    (schedule : List
      (BitonicCompareExchangeWithHistory wordCount historyCount))
    (values : Fin wordCount → α) :
    runTypedBitonicValues schedule values =
      runBareBitonicValues
        (schedule.map BitonicCompareExchangeWithHistory.eraseHistory) values := by
  induction schedule generalizing values with
  | nil => rfl
  | cons instruction schedule inductionHypothesis =>
      simp only [runTypedBitonicValues, List.map_cons, runBareBitonicValues]
      rw [typedBitonicValueStep_eraseHistory]
      exact inductionHypothesis _

/-- Attaching history slots and then erasing them returns the original
schedule. -/
theorem attachBitonicHistoryFrom_map_eraseHistory
    {wordCount historyCount : Nat} (positiveHistory : 0 < historyCount)
    (offset : Nat) (schedule : List (BitonicCompareExchange wordCount)) :
    (attachBitonicHistoryFrom positiveHistory offset schedule).map
        BitonicCompareExchangeWithHistory.eraseHistory = schedule := by
  induction schedule generalizing offset with
  | nil => rfl
  | cons instruction schedule inductionHypothesis =>
      simp [attachBitonicHistoryFrom,
        BitonicCompareExchangeWithHistory.eraseHistory, inductionHypothesis]

end VerifiedCircuitCore
