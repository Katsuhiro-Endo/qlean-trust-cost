import QLean.Generator.Analysis.UniformPreparationPlan

/-!
# 証明付き非2冪一様準備計画

生のexport用計画と同じ再帰式で、各命令へ型安全性証明を付ける。`List.attach`に依存せず、
証明を消した命令列が生の計画へ完全一致することも示す。
-/

namespace ProbabilityGeneratorQProof

/-- 一命令へ最高位Bool制御を一個追加する。 -/
def addHighestControl (width : Nat) (expected : Bool)
    (instruction : UniformRotationInstruction) : UniformRotationInstruction :=
  { instruction with controls := (width, expected) :: instruction.controls }

/-- 下位well-formed命令へ最高位制御を追加すると全体幅でwell-formedになる。 -/
theorem addHighestControl_wellFormed
    {width : Nat} (expected : Bool)
    (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    (addHighestControl width expected instruction).WellFormed (width + 1) :=
  UniformRotationInstruction.wellFormed_addControl wellFormed expected

/-- 最高位制御を追加した証明付き命令列。 -/
def addHighestControlInstructions
    {width : Nat} (expected : Bool)
    (instructions : List {instruction : UniformRotationInstruction //
      instruction.WellFormed width}) :
    List {instruction : UniformRotationInstruction //
      instruction.WellFormed (width + 1)} :=
  instructions.map fun instruction =>
    ⟨addHighestControl width expected instruction.1,
      addHighestControl_wellFormed expected instruction.1 instruction.2⟩

/-- 証明付き一命令へ最高位Bool制御を追加する。 -/
def addHighestControlInstruction
    {width : Nat} (expected : Bool)
    (instruction : {instruction : UniformRotationInstruction //
      instruction.WellFormed width}) :
    {instruction : UniformRotationInstruction //
      instruction.WellFormed (width + 1)} :=
  ⟨addHighestControl width expected instruction.1,
    addHighestControl_wellFormed expected instruction.1 instruction.2⟩

/-- 最高位制御付き証明列から証明を消す操作は、生の命令列への制御追加に等しい。 -/
theorem addHighestControlInstructions_values
    {width : Nat} (expected : Bool)
    (instructions : List {instruction : UniformRotationInstruction //
      instruction.WellFormed width}) :
    (addHighestControlInstructions expected instructions).map Subtype.val =
      (instructions.map Subtype.val).map (addHighestControl width expected) := by
  induction instructions with
  | nil => rfl
  | cons instruction instructions inductionHypothesis =>
      simp only [addHighestControlInstructions, List.map_cons]
      congr 1

/-- 二分木nodeの左部分木に入る有効leaf数。 -/
def uniformLeftCount (width validCount : Nat) : Nat :=
  min validCount (2 ^ width)

/-- 二分木nodeの右部分木に入る有効leaf数。 -/
def uniformRightCount (width validCount : Nat) : Nat :=
  validCount - uniformLeftCount width validCount

/-- 二分木nodeの根で実行する無制御回転命令。 -/
def uniformRootInstruction (width validCount : Nat) : UniformRotationInstruction :=
  ⟨width, [], uniformSplitAngle
    (uniformLeftCount width validCount) (uniformRightCount width validCount)⟩

/-- 根命令は幅`width+1`に対してwell-formedである。 -/
theorem uniformRootInstruction_wellFormed (width validCount : Nat) :
    (uniformRootInstruction width validCount).WellFormed (width + 1) := by
  simp [uniformRootInstruction, UniformRotationInstruction.WellFormed]

/-- 根命令をwell-formed証明と組にした命令。 -/
def attachedUniformRootInstruction (width validCount : Nat) :
    {instruction : UniformRotationInstruction //
      instruction.WellFormed (width + 1)} :=
  ⟨uniformRootInstruction width validCount,
    uniformRootInstruction_wellFormed width validCount⟩

/-- 左部分木の有効leaf数は下位幅の容量以下である。 -/
theorem uniformLeftCount_le_capacity (width validCount : Nat) :
    uniformLeftCount width validCount ≤ 2 ^ width := by
  exact min_le_right _ _

/-- 親nodeが容量内なら右部分木の有効leaf数も下位幅の容量以下である。 -/
theorem uniformRightCount_le_capacity
    (width validCount : Nat) (capacity : validCount ≤ 2 ^ (width + 1)) :
    uniformRightCount width validCount ≤ 2 ^ width := by
  unfold uniformRightCount uniformLeftCount
  rw [Nat.pow_succ] at capacity
  omega

/-- 生の計画と同じ再帰式で各命令にwell-formed証明を付ける。 -/
def attachedUniformRotationPlan :
    (width validCount : Nat) → validCount ≤ 2 ^ width →
      List {instruction : UniformRotationInstruction //
        instruction.WellFormed width}
  | 0, _, _ => []
  | width + 1, validCount, capacity =>
      if _zero : validCount = 0 then
        []
      else
        attachedUniformRootInstruction width validCount ::
          (addHighestControlInstructions false
              (attachedUniformRotationPlan width
                (uniformLeftCount width validCount)
                (uniformLeftCount_le_capacity width validCount)) ++
            addHighestControlInstructions true
              (attachedUniformRotationPlan width
                (uniformRightCount width validCount)
                (uniformRightCount_le_capacity width validCount capacity)))
termination_by width => width

/-- 正の有効leaf数に対する証明付き計画の根・左枝・右枝分解。 -/
theorem attachedUniformRotationPlan_succ
    (width validCount : Nat) (capacity : validCount ≤ 2 ^ (width + 1))
    (positive : 0 < validCount) :
    attachedUniformRotationPlan (width + 1) validCount capacity =
      attachedUniformRootInstruction width validCount ::
        (addHighestControlInstructions false
            (attachedUniformRotationPlan width
              (uniformLeftCount width validCount)
              (uniformLeftCount_le_capacity width validCount)) ++
          addHighestControlInstructions true
            (attachedUniformRotationPlan width
              (uniformRightCount width validCount)
              (uniformRightCount_le_capacity width validCount capacity))) := by
  rw [attachedUniformRotationPlan]
  rw [dif_neg (Nat.ne_of_gt positive)]

/-- 証明付き計画から証明を消すとexport対象の生の回転計画へ完全に戻る。 -/
theorem attachedUniformRotationPlan_values
    (width validCount : Nat) (capacity : validCount ≤ 2 ^ width) :
    (attachedUniformRotationPlan width validCount capacity).map Subtype.val =
      uniformRotationPlan width validCount := by
  induction width generalizing validCount with
  | zero =>
      simp only [attachedUniformRotationPlan, uniformRotationPlan, List.map_nil]
  | succ width inductionHypothesis =>
      by_cases zero : validCount = 0
      · rw [attachedUniformRotationPlan, uniformRotationPlan]
        rw [dif_pos zero, dif_pos zero]
        rfl
      · rw [attachedUniformRotationPlan, uniformRotationPlan]
        rw [dif_neg zero, dif_neg zero]
        simp only [List.map_cons, List.map_append]
        congr 1
        rw [addHighestControlInstructions_values,
          addHighestControlInstructions_values]
        rw [inductionHypothesis, inductionHypothesis]
        rfl

end ProbabilityGeneratorQProof
