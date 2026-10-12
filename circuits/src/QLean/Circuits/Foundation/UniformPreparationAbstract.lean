import QLean.Circuits.Foundation.UniformPreparationAttachedPlan

/-!
# 非2冪一様準備の抽象selector意味論

物理wireとscratchを取り除いた有限selector基底上で、回転計画をtarget bit二項作用として
評価する。ここで証明した二分木振幅を、物理回路の疎意味論へ後で移送する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 幅`width`の抽象selector計算基底。 -/
abbrev AbstractSelectorBasis (width : Nat) := Fin width → Bool

/-- 抽象selector基底の指定bitだけを置換する。 -/
def replaceSelectorBit {width : Nat}
    (basis : AbstractSelectorBasis width) (target : Fin width) (value : Bool) :
    AbstractSelectorBasis width :=
  fun index => if index = target then value else basis index

/-- 置換した抽象selectorをtargetで読むと指定値になる。 -/
@[simp] theorem replaceSelectorBit_target
    {width : Nat} (basis : AbstractSelectorBasis width)
    (target : Fin width) (value : Bool) :
    replaceSelectorBit basis target value target = value := by
  simp [replaceSelectorBit]

/-- target以外の抽象selector bitは置換で変わらない。 -/
@[simp] theorem replaceSelectorBit_other
    {width : Nat} (basis : AbstractSelectorBasis width)
    (target index : Fin width) (value : Bool) (different : index ≠ target) :
    replaceSelectorBit basis target value index = basis index := by
  simp [replaceSelectorBit, different]

/-- well-formed命令のNat制御列が抽象selector基底と一致するかを判定する。 -/
def abstractControlsSatisfied
    {width : Nat}
    (instruction : {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (basis : AbstractSelectorBasis width) : Bool :=
  instruction.1.controls.attach.all fun control =>
    decide (basis ⟨control.1.1, instruction.2.2.1 control.1 control.2⟩ = control.1.2)

/-- 一個のwell-formed回転命令を抽象状態関数へ作用させる。 -/
def applyAbstractUniformInstruction
    {width : Nat}
    (instruction : {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (state : AbstractSelectorBasis width → ℂ) :
    AbstractSelectorBasis width → ℂ :=
  fun output =>
    if abstractControlsSatisfied instruction output then
      ∑ inputBit : Bool,
        localRy instruction.1.angle.uniformValue
            (output ⟨instruction.1.target, instruction.2.1⟩) inputBit *
          state (replaceSelectorBit output
            ⟨instruction.1.target, instruction.2.1⟩ inputBit)
    else state output

/-- 抽象一命令作用は状態のスカラー倍と可換である。 -/
theorem applyAbstractUniformInstruction_smul
    {width : Nat}
    (instruction : {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (scalar : ℂ) (state : AbstractSelectorBasis width → ℂ) :
    applyAbstractUniformInstruction instruction (scalar • state) =
      scalar • applyAbstractUniformInstruction instruction state := by
  funext output
  unfold applyAbstractUniformInstruction
  by_cases enabled : abstractControlsSatisfied instruction output
  · simp only [enabled, if_true, Pi.smul_apply]
    simp_rw [Fintype.sum_bool]
    ring
  · simp [enabled]

/-- well-formed命令列を実行順に抽象状態へ作用させる。 -/
def runAbstractUniformInstructions
    {width : Nat}
    (instructions : List {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (state : AbstractSelectorBasis width → ℂ) :
    AbstractSelectorBasis width → ℂ :=
  instructions.foldl
    (fun current instruction =>
      applyAbstractUniformInstruction instruction current)
    state

/-- 抽象命令列作用も状態のスカラー倍と可換である。 -/
theorem runAbstractUniformInstructions_smul
    {width : Nat}
    (instructions : List {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (scalar : ℂ) (state : AbstractSelectorBasis width → ℂ) :
    runAbstractUniformInstructions instructions (scalar • state) =
      scalar • runAbstractUniformInstructions instructions state := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction instructions inductionHypothesis =>
      simp only [runAbstractUniformInstructions, List.foldl_cons]
      rw [applyAbstractUniformInstruction_smul]
      exact inductionHypothesis _

/-- 幅`width`の全0抽象selector基底。 -/
def zeroSelectorBasis (width : Nat) : AbstractSelectorBasis width := fun _ => false

/-- 抽象selectorの全0 ket。 -/
def zeroSelectorKet (width : Nat) : AbstractSelectorBasis width → ℂ :=
  basisKet (zeroSelectorBasis width)

/-- 最高位bitと残りの下位bitへ抽象selector基底を分解する同値。 -/
def splitHighestSelectorEquiv (width : Nat) :
    AbstractSelectorBasis (width + 1) ≃
      Bool × AbstractSelectorBasis width where
  toFun basis := (basis (Fin.last width), fun index => basis index.castSucc)
  invFun pair := Fin.lastCases pair.1 pair.2
  left_inv basis := by
    funext index
    refine Fin.lastCases ?_ (fun lower => ?_) index
    · simp
    · simp
  right_inv pair := by
    apply Prod.ext
    · simp
    · funext index
      simp

/-- 最高位bitと下位selector基底を結合する。 -/
def combineHighestSelector {width : Nat}
    (highest : Bool) (lower : AbstractSelectorBasis width) :
    AbstractSelectorBasis (width + 1) :=
  (splitHighestSelectorEquiv width).symm (highest, lower)

/-- 結合基底の最高位bitは指定値である。 -/
@[simp] theorem combineHighestSelector_last
    {width : Nat} (highest : Bool) (lower : AbstractSelectorBasis width) :
    combineHighestSelector highest lower (Fin.last width) = highest := by
  change ((splitHighestSelectorEquiv width).symm (highest, lower)) (Fin.last width) = _
  have pair := (splitHighestSelectorEquiv width).apply_symm_apply (highest, lower)
  exact congrArg Prod.fst pair

/-- 結合基底の下位bitは元の下位基底に等しい。 -/
@[simp] theorem combineHighestSelector_castSucc
    {width : Nat} (highest : Bool) (lower : AbstractSelectorBasis width)
    (index : Fin width) :
    combineHighestSelector highest lower index.castSucc = lower index := by
  change ((splitHighestSelectorEquiv width).symm (highest, lower)) index.castSucc = _
  have pair := (splitHighestSelectorEquiv width).apply_symm_apply (highest, lower)
  exact congrFun (congrArg Prod.snd pair) index

/-- 最高位を固定した結合写像は下位基底について単射である。 -/
theorem combineHighestSelector_injective
    {width : Nat} (highest : Bool) :
    Function.Injective
      (combineHighestSelector (width := width) highest) := by
  intro first second equal
  have pairEqual := (splitHighestSelectorEquiv width).symm.injective equal
  exact congrArg Prod.snd pairEqual

/-- 全0下位基底へ偽の最高位を結合すると一段大きい全0基底になる。 -/
theorem combineHighestSelector_zero (width : Nat) :
    combineHighestSelector false (zeroSelectorBasis width) =
      zeroSelectorBasis (width + 1) := by
  funext index
  refine Fin.lastCases ?_ (fun lower => ?_) index
  · simp [zeroSelectorBasis]
  · simp [zeroSelectorBasis]

/-- 偽の最高位branchで全0 ketを読むことは下位全0 ketに等しい。 -/
theorem zeroSelectorKet_combine_false
    {width : Nat} (lower : AbstractSelectorBasis width) :
    zeroSelectorKet (width + 1) (combineHighestSelector false lower) =
      zeroSelectorKet width lower := by
  unfold zeroSelectorKet basisKet
  rw [← combineHighestSelector_zero width]
  by_cases equal : lower = zeroSelectorBasis width
  · subst lower
    simp [VerifiedMath.Basis.vector]
  · have combinedDifferent :
        combineHighestSelector false lower ≠
          combineHighestSelector false (zeroSelectorBasis width) := by
      intro combinedEqual
      exact equal (combineHighestSelector_injective false combinedEqual)
    simp [VerifiedMath.Basis.vector, equal, combinedDifferent]

/-- 真の最高位branchは全0 ketの台から外れる。 -/
theorem zeroSelectorKet_combine_true
    {width : Nat} (lower : AbstractSelectorBasis width) :
    zeroSelectorKet (width + 1) (combineHighestSelector true lower) = 0 := by
  unfold zeroSelectorKet basisKet
  simp only [VerifiedMath.Basis.vector]
  rw [if_neg]
  intro equal
  have lastEqual := congrFun equal (Fin.last width)
  simp [zeroSelectorBasis] at lastEqual

/-- 結合基底の最高位を置換すると、指定した最高位で結合した基底になる。 -/
theorem replaceSelectorBit_combineHighest_last
    {width : Nat} (highest value : Bool)
    (lower : AbstractSelectorBasis width) :
    replaceSelectorBit (combineHighestSelector highest lower)
        (Fin.last width) value =
      combineHighestSelector value lower := by
  funext index
  refine Fin.lastCases ?_ (fun lowerIndex => ?_) index
  · simp [replaceSelectorBit]
  · rw [replaceSelectorBit_other]
    · simp
    · intro equal
      have valueEqual := congrArg Fin.val equal
      simp at valueEqual
      omega

/-- 抽象状態を最高位bit固定の下位状態として読む。 -/
def highestBranchState {width : Nat}
    (highest : Bool) (state : AbstractSelectorBasis (width + 1) → ℂ) :
    AbstractSelectorBasis width → ℂ :=
  fun lower => state (combineHighestSelector highest lower)

/-- 最高位制御付き命令の制御条件は最高位一致と下位条件の論理積である。 -/
theorem abstractControlsSatisfied_addHighestControl
    {width : Nat} (expected : Bool)
    (instruction : {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (highest : Bool) (lower : AbstractSelectorBasis width) :
    abstractControlsSatisfied (addHighestControlInstruction expected instruction)
        (combineHighestSelector highest lower) =
      (decide (highest = expected) &&
        abstractControlsSatisfied instruction lower) := by
  unfold abstractControlsSatisfied addHighestControlInstruction addHighestControl
  simp only [List.attach_cons, List.all_cons]
  have highestIndex :
      (⟨width, Nat.lt_succ_self width⟩ : Fin (width + 1)) = Fin.last width := by
    rfl
  rw [highestIndex, combineHighestSelector_last]
  congr 1
  rw [List.all_map]
  apply List.all_congr rfl
  intro control
  exact congrArg (fun bit : Bool => decide (bit = control.1.2))
    (combineHighestSelector_castSucc highest lower
      ⟨control.1.1, instruction.2.2.1 control.1 control.2⟩)

/-- 最高位を保ったまま下位targetを置換することは、結合後の対応bit置換に等しい。 -/
theorem replaceSelectorBit_combineHighest
    {width : Nat} (highest : Bool) (lower : AbstractSelectorBasis width)
    (target : Fin width) (value : Bool) :
    replaceSelectorBit (combineHighestSelector highest lower) target.castSucc value =
      combineHighestSelector highest (replaceSelectorBit lower target value) := by
  funext index
  refine Fin.lastCases ?_ (fun lowerIndex => ?_) index
  · simp only [replaceSelectorBit, combineHighestSelector_last]
    rw [if_neg]
    intro equal
    have valueEqual := congrArg Fin.val equal
    simp at valueEqual
    omega
  · by_cases equal : lowerIndex = target
    · subst lowerIndex
      simp
    · simp [replaceSelectorBit, equal, Fin.castSucc_inj]

/-- 最高位制御付き一命令は一致branchだけで元の下位命令を作用させる。 -/
theorem applyAbstractUniformInstruction_addHighestControl
    {width : Nat} (expected : Bool)
    (instruction : {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (state : AbstractSelectorBasis (width + 1) → ℂ)
    (highest : Bool) (output : AbstractSelectorBasis width) :
    applyAbstractUniformInstruction
        (addHighestControlInstruction expected instruction)
        state (combineHighestSelector highest output) =
      if highest = expected then
        applyAbstractUniformInstruction instruction
          (highestBranchState highest state) output
      else state (combineHighestSelector highest output) := by
  unfold applyAbstractUniformInstruction
  rw [abstractControlsSatisfied_addHighestControl]
  by_cases highEqual : highest = expected
  · simp only [highEqual, decide_true, if_true]
    have targetIndex :
        (⟨(addHighestControlInstruction expected instruction).1.target,
            (addHighestControlInstruction expected instruction).2.1⟩ :
          Fin (width + 1)) =
          (⟨instruction.1.target, instruction.2.1⟩ : Fin width).castSucc := by
      rfl
    rw [targetIndex, combineHighestSelector_castSucc]
    simp only [Bool.true_and]
    by_cases enabled : abstractControlsSatisfied instruction output
    · simp only [enabled, if_true]
      apply Finset.sum_congr rfl
      intro inputBit _
      rw [replaceSelectorBit_combineHighest]
      rfl
    · simp [enabled, highestBranchState]
  · simp [highEqual]

/-- 最高位制御付き命令列は一致branchだけで元の下位命令列を作用させる。 -/
theorem runAbstractUniformInstructions_addHighestControl
    {width : Nat} (expected : Bool)
    (instructions : List {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (state : AbstractSelectorBasis (width + 1) → ℂ)
    (highest : Bool) :
    highestBranchState highest
        (runAbstractUniformInstructions
          (addHighestControlInstructions expected instructions) state) =
      if highest = expected then
        runAbstractUniformInstructions instructions (highestBranchState highest state)
      else highestBranchState highest state := by
  induction instructions generalizing state with
  | nil => simp [runAbstractUniformInstructions, addHighestControlInstructions]
  | cons instruction instructions inductionHypothesis =>
      change highestBranchState highest
          (runAbstractUniformInstructions
            (addHighestControlInstructions expected instructions)
            (applyAbstractUniformInstruction
              (addHighestControlInstruction expected instruction)
              state)) =
        if highest = expected then
          runAbstractUniformInstructions instructions
            (applyAbstractUniformInstruction instruction
              (highestBranchState highest state))
        else highestBranchState highest state
      rw [inductionHypothesis]
      by_cases highEqual : highest = expected
      · simp only [highEqual, if_true]
        congr 1
        funext output
        change applyAbstractUniformInstruction
            (addHighestControlInstruction expected instruction)
            state (combineHighestSelector expected output) = _
        rw [applyAbstractUniformInstruction_addHighestControl]
        simp only [if_true]
      · simp only [highEqual, if_false]
        funext output
        change applyAbstractUniformInstruction
            (addHighestControlInstruction expected instruction)
            state (combineHighestSelector highest output) = _
        rw [applyAbstractUniformInstruction_addHighestControl]
        simp only [highEqual, if_false]
        rfl

/-- 抽象一様準備計画を全0 ketへ作用させた状態。 -/
def abstractUniformPreparedState (width validCount : Nat)
    (capacity : validCount ≤ 2 ^ width) :
    AbstractSelectorBasis width → ℂ :=
  runAbstractUniformInstructions
    (attachedUniformRotationPlan width validCount capacity)
    (zeroSelectorKet width)

/-- 抽象命令列の連結は、前半を実行してから後半を実行することに等しい。 -/
theorem runAbstractUniformInstructions_append
    {width : Nat}
    (first second : List {instruction : UniformRotationInstruction //
      instruction.WellFormed width})
    (state : AbstractSelectorBasis width → ℂ) :
    runAbstractUniformInstructions (first ++ second) state =
      runAbstractUniformInstructions second
        (runAbstractUniformInstructions first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first inductionHypothesis =>
      change runAbstractUniformInstructions (first ++ second)
          (applyAbstractUniformInstruction instruction state) = _
      exact inductionHypothesis _

/-- 根回転後の偽branch振幅は余弦係数を掛けた下位全0 ketである。 -/
theorem applyAbstractUniformRoot_false
    (width validCount : Nat) (lower : AbstractSelectorBasis width) :
    applyAbstractUniformInstruction
        (attachedUniformRootInstruction width validCount)
        (zeroSelectorKet (width + 1))
        (combineHighestSelector false lower) =
      (Real.cos ((uniformSplitAngle
          (uniformLeftCount width validCount)
          (uniformRightCount width validCount)).uniformValue / 2) : ℂ) *
        zeroSelectorKet width lower := by
  unfold applyAbstractUniformInstruction abstractControlsSatisfied
  simp only [attachedUniformRootInstruction, uniformRootInstruction,
    List.attach_nil, List.all_nil, if_true, Fintype.sum_bool]
  have highestIndex :
      (⟨width, Nat.lt_succ_self width⟩ : Fin (width + 1)) = Fin.last width := by
    rfl
  rw [highestIndex, combineHighestSelector_last]
  rw [replaceSelectorBit_combineHighest_last,
    replaceSelectorBit_combineHighest_last,
    zeroSelectorKet_combine_false, zeroSelectorKet_combine_true]
  simp [localRy]

/-- 根回転後の真branch振幅は正弦係数を掛けた下位全0 ketである。 -/
theorem applyAbstractUniformRoot_true
    (width validCount : Nat) (lower : AbstractSelectorBasis width) :
    applyAbstractUniformInstruction
        (attachedUniformRootInstruction width validCount)
        (zeroSelectorKet (width + 1))
        (combineHighestSelector true lower) =
      (Real.sin ((uniformSplitAngle
          (uniformLeftCount width validCount)
          (uniformRightCount width validCount)).uniformValue / 2) : ℂ) *
        zeroSelectorKet width lower := by
  unfold applyAbstractUniformInstruction abstractControlsSatisfied
  simp only [attachedUniformRootInstruction, uniformRootInstruction,
    List.attach_nil, List.all_nil, if_true, Fintype.sum_bool]
  have highestIndex :
      (⟨width, Nat.lt_succ_self width⟩ : Fin (width + 1)) = Fin.last width := by
    rfl
  rw [highestIndex, combineHighestSelector_last]
  rw [replaceSelectorBit_combineHighest_last,
    replaceSelectorBit_combineHighest_last,
    zeroSelectorKet_combine_false, zeroSelectorKet_combine_true]
  simp [localRy]

/-- 回転木が表す疎状態を、最高位と下位部分木の再帰だけで定義する。 -/
def uniformTreeState :
    (width validCount : Nat) → validCount ≤ 2 ^ width →
      AbstractSelectorBasis width → ℂ
  | 0, _, _ => zeroSelectorKet 0
  | width + 1, validCount, capacity =>
      if _zero : validCount = 0 then
        zeroSelectorKet (width + 1)
      else
        fun basis =>
          if basis (Fin.last width) then
            (Real.sin ((uniformSplitAngle
                (uniformLeftCount width validCount)
                (uniformRightCount width validCount)).uniformValue / 2) : ℂ) *
              uniformTreeState width (uniformRightCount width validCount)
                (uniformRightCount_le_capacity width validCount capacity)
                (fun index => basis index.castSucc)
          else
            (Real.cos ((uniformSplitAngle
                (uniformLeftCount width validCount)
                (uniformRightCount width validCount)).uniformValue / 2) : ℂ) *
              uniformTreeState width (uniformLeftCount width validCount)
                (uniformLeftCount_le_capacity width validCount)
                (fun index => basis index.castSucc)
termination_by width => width

/-- 任意基底は、その最高位と下位bitを再結合すると元へ戻る。 -/
theorem combineHighestSelector_of_basis
    {width : Nat} (basis : AbstractSelectorBasis (width + 1)) :
    combineHighestSelector (basis (Fin.last width))
        (fun index => basis index.castSucc) = basis := by
  exact (splitHighestSelectorEquiv width).symm_apply_apply basis

/-- 証明付き回転計画の抽象評価は再帰的な回転木状態に完全一致する。 -/
theorem abstractUniformPreparedState_eq_uniformTreeState
    (width validCount : Nat) (capacity : validCount ≤ 2 ^ width) :
    abstractUniformPreparedState width validCount capacity =
      uniformTreeState width validCount capacity := by
  induction width generalizing validCount with
  | zero =>
      simp [abstractUniformPreparedState, attachedUniformRotationPlan,
        runAbstractUniformInstructions, uniformTreeState]
  | succ width inductionHypothesis =>
      by_cases zero : validCount = 0
      · subst validCount
        unfold abstractUniformPreparedState
        rw [attachedUniformRotationPlan, dif_pos rfl]
        simp only [runAbstractUniformInstructions, List.foldl_nil]
        rw [uniformTreeState, dif_pos rfl]
      · have positive : 0 < validCount := Nat.pos_of_ne_zero zero
        unfold abstractUniformPreparedState
        rw [attachedUniformRotationPlan_succ width validCount capacity positive]
        change runAbstractUniformInstructions
            (addHighestControlInstructions false
                (attachedUniformRotationPlan width
                  (uniformLeftCount width validCount)
                  (uniformLeftCount_le_capacity width validCount)) ++
              addHighestControlInstructions true
                (attachedUniformRotationPlan width
                  (uniformRightCount width validCount)
                  (uniformRightCount_le_capacity width validCount capacity)))
            (applyAbstractUniformInstruction
              (attachedUniformRootInstruction width validCount)
              (zeroSelectorKet (width + 1))) = _
        rw [runAbstractUniformInstructions_append]
        funext basis
        rw [← combineHighestSelector_of_basis basis]
        let lower : AbstractSelectorBasis width :=
          fun index => basis index.castSucc
        let highest : Bool := basis (Fin.last width)
        change highestBranchState highest
            (runAbstractUniformInstructions
              (addHighestControlInstructions true
                (attachedUniformRotationPlan width
                  (uniformRightCount width validCount)
                  (uniformRightCount_le_capacity width validCount capacity)))
              (runAbstractUniformInstructions
                (addHighestControlInstructions false
                  (attachedUniformRotationPlan width
                    (uniformLeftCount width validCount)
                    (uniformLeftCount_le_capacity width validCount)))
                (applyAbstractUniformInstruction
                  (attachedUniformRootInstruction width validCount)
                  (zeroSelectorKet (width + 1))))) lower =
          uniformTreeState (width + 1) validCount capacity
            (combineHighestSelector highest lower)
        cases highest with
        | false =>
            rw [runAbstractUniformInstructions_addHighestControl]
            simp only [Bool.false_eq_true, if_false]
            rw [runAbstractUniformInstructions_addHighestControl]
            simp only [if_true]
            have rootBranch :
                highestBranchState false
                    (applyAbstractUniformInstruction
                      (attachedUniformRootInstruction width validCount)
                      (zeroSelectorKet (width + 1))) =
                  (Real.cos ((uniformSplitAngle
                    (uniformLeftCount width validCount)
                    (uniformRightCount width validCount)).uniformValue / 2) : ℂ) •
                    zeroSelectorKet width := by
              funext output
              simp only [highestBranchState, Pi.smul_apply]
              exact applyAbstractUniformRoot_false width validCount output
            rw [rootBranch, runAbstractUniformInstructions_smul]
            change ((Real.cos ((uniformSplitAngle
                (uniformLeftCount width validCount)
                (uniformRightCount width validCount)).uniformValue / 2) : ℂ) •
              abstractUniformPreparedState width
                (uniformLeftCount width validCount)
                (uniformLeftCount_le_capacity width validCount)) lower = _
            rw [inductionHypothesis]
            rw [uniformTreeState, dif_neg zero]
            simp [combineHighestSelector_last, Bool.false_eq_true,
              combineHighestSelector_castSucc, Pi.smul_apply, smul_eq_mul]
        | true =>
            rw [runAbstractUniformInstructions_addHighestControl]
            simp only [if_true]
            rw [runAbstractUniformInstructions_addHighestControl]
            simp only [Bool.true_eq_false, if_false]
            have rootBranch :
                highestBranchState true
                    (applyAbstractUniformInstruction
                      (attachedUniformRootInstruction width validCount)
                      (zeroSelectorKet (width + 1))) =
                  (Real.sin ((uniformSplitAngle
                    (uniformLeftCount width validCount)
                    (uniformRightCount width validCount)).uniformValue / 2) : ℂ) •
                    zeroSelectorKet width := by
              funext output
              simp only [highestBranchState, Pi.smul_apply]
              exact applyAbstractUniformRoot_true width validCount output
            rw [rootBranch, runAbstractUniformInstructions_smul]
            change ((Real.sin ((uniformSplitAngle
                (uniformLeftCount width validCount)
                (uniformRightCount width validCount)).uniformValue / 2) : ℂ) •
              abstractUniformPreparedState width
                (uniformRightCount width validCount)
                (uniformRightCount_le_capacity width validCount capacity)) lower = _
            rw [inductionHypothesis]
            rw [uniformTreeState, dif_neg zero]
            simp [combineHighestSelector_last,
              combineHighestSelector_castSucc, Pi.smul_apply, smul_eq_mul]

/-- selector bit列をlittle-endian自然数へ復号する。 -/
def selectorValue : (width : Nat) → AbstractSelectorBasis width → Nat
  | 0, _ => 0
  | width + 1, basis =>
      (if basis (Fin.last width) then 2 ^ width else 0) +
        selectorValue width (fun index => basis index.castSucc)

/-- selector復号値は常に幅`width`の容量未満である。 -/
theorem selectorValue_lt_capacity :
    ∀ (width : Nat) (basis : AbstractSelectorBasis width),
      selectorValue width basis < 2 ^ width
  | 0, _ => by simp [selectorValue]
  | width + 1, basis => by
      rw [selectorValue, Nat.pow_succ]
      have lowerBound := selectorValue_lt_capacity width
        (fun index => basis index.castSucc)
      split <;> omega

/-- selector復号値の範囲内test bitは、元の抽象selector bitそのものである。 -/
theorem selectorValue_testBit :
    ∀ (width : Nat) (basis : AbstractSelectorBasis width)
      (index : Fin width),
      (selectorValue width basis).testBit index.val = basis index
  | 0, _, index => Fin.elim0 index
  | width + 1, basis, index => by
      let lower : AbstractSelectorBasis width :=
        fun lowerIndex => basis lowerIndex.castSucc
      have lowerBound : selectorValue width lower < 2 ^ width :=
        selectorValue_lt_capacity width lower
      have valueShape :
          selectorValue (width + 1) basis =
            2 ^ width * (basis (Fin.last width)).toNat + selectorValue width lower := by
        simp only [selectorValue, lower]
        cases basis (Fin.last width) <;> simp
      rw [valueShape]
      refine Fin.lastCases ?_ (fun lowerIndex => ?_) index
      · rw [Nat.testBit_two_pow_mul_add _ lowerBound]
        cases highest : basis (Fin.last width) <;> simp
      · rw [Nat.testBit_two_pow_mul_add _ lowerBound]
        simp only [Fin.val_castSucc, lowerIndex.isLt, if_true]
        exact selectorValue_testBit width lower lowerIndex

/-- 最高位と下位bitを結合した基底の復号値。 -/
theorem selectorValue_combineHighest
    {width : Nat} (highest : Bool) (lower : AbstractSelectorBasis width) :
    selectorValue (width + 1) (combineHighestSelector highest lower) =
      (if highest then 2 ^ width else 0) + selectorValue width lower := by
  simp [selectorValue]

/-- 有効leaf数の左右分割は元のleaf数を保存する。 -/
theorem uniformLeftCount_add_rightCount (width validCount : Nat) :
    uniformLeftCount width validCount + uniformRightCount width validCount =
      validCount := by
  unfold uniformRightCount
  have leftBound : uniformLeftCount width validCount ≤ validCount := by
    unfold uniformLeftCount
    exact min_le_left _ _
  omega

/-- 有効leaf数が正なら左部分木にも少なくとも一leafある。 -/
theorem uniformLeftCount_positive
    (width validCount : Nat) (positive : 0 < validCount) :
    0 < uniformLeftCount width validCount := by
  unfold uniformLeftCount
  have capacityPositive : 0 < 2 ^ width := pow_pos (by omega) _
  omega

/-- 正のnodeでは左右leaf数の和も正である。 -/
theorem uniformChildCounts_positive
    (width validCount : Nat) (positive : 0 < validCount) :
    0 < uniformLeftCount width validCount +
      uniformRightCount width validCount := by
  rw [uniformLeftCount_add_rightCount]
  exact positive

/-- 根回転の余弦係数を親leaf数を分母とする形へ正規化する。 -/
theorem cos_uniformRoot_eq_sqrt_ratio
    (width validCount : Nat) (positive : 0 < validCount) :
    Real.cos ((uniformSplitAngle
        (uniformLeftCount width validCount)
        (uniformRightCount width validCount)).uniformValue / 2) =
      Real.sqrt ((uniformLeftCount width validCount : ℝ) / validCount) := by
  unfold AngleExpr.uniformValue
  rw [cos_half_uniformSplitAngle (fun _ => 0) _ _
    (uniformChildCounts_positive width validCount positive)]
  congr 2
  norm_cast
  exact uniformLeftCount_add_rightCount width validCount

/-- 根回転の正弦係数を親leaf数を分母とする形へ正規化する。 -/
theorem sin_uniformRoot_eq_sqrt_ratio
    (width validCount : Nat) (positive : 0 < validCount) :
    Real.sin ((uniformSplitAngle
        (uniformLeftCount width validCount)
        (uniformRightCount width validCount)).uniformValue / 2) =
      Real.sqrt ((uniformRightCount width validCount : ℝ) / validCount) := by
  unfold AngleExpr.uniformValue
  rw [sin_half_uniformSplitAngle (fun _ => 0) _ _
    (uniformChildCounts_positive width validCount positive)]
  congr 2
  norm_cast
  exact uniformLeftCount_add_rightCount width validCount

/-- 正整数`part,total`に対する平方根比と部分木正規化係数の積。 -/
theorem sqrt_ratio_mul_inverse_sqrt
    (part total : Nat) (partPositive : 0 < part) (totalPositive : 0 < total) :
    (Real.sqrt ((part : ℝ) / (total : ℝ)) : ℂ) *
        ((1 / Real.sqrt (part : ℝ) : ℝ) : ℂ) =
      ((1 / Real.sqrt (total : ℝ) : ℝ) : ℂ) := by
  norm_cast
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ part)]
  have partSqrtPositive : 0 < Real.sqrt (part : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast partPositive)
  have totalSqrtPositive : 0 < Real.sqrt (total : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast totalPositive)
  field_simp

/-- 有効leafだけに`1/√validCount`を置きpaddingを0にする理想selector状態。 -/
def idealUniformSelectorState
    (width validCount : Nat) : AbstractSelectorBasis width → ℂ :=
  fun basis =>
    if selectorValue width basis < validCount then
      ((1 / Real.sqrt (validCount : ℝ) : ℝ) : ℂ)
    else 0

/-- 下位復号値は左部分木内にあることと親の偽branchで有効であることが同値。 -/
theorem selectorValue_lt_leftCount_iff
    (width validCount : Nat) (lower : AbstractSelectorBasis width) :
    selectorValue width lower < uniformLeftCount width validCount ↔
      selectorValue width lower < validCount := by
  unfold uniformLeftCount
  by_cases withinCapacity : validCount ≤ 2 ^ width
  · rw [min_eq_left withinCapacity]
  · have capacityLeValidCount : 2 ^ width ≤ validCount :=
      Nat.le_of_not_ge withinCapacity
    rw [min_eq_right capacityLeValidCount]
    have valueBound := selectorValue_lt_capacity width lower
    have valueValid := lt_of_lt_of_le valueBound capacityLeValidCount
    simp [valueBound, valueValid]

/-- 正のleaf数では、回転木状態は有効leaf上の厳密な一様状態である。 -/
theorem uniformTreeState_eq_idealUniformSelectorState
    (width validCount : Nat) (capacity : validCount ≤ 2 ^ width)
    (positive : 0 < validCount) :
    uniformTreeState width validCount capacity =
      idealUniformSelectorState width validCount := by
  induction width generalizing validCount with
  | zero =>
      have validCountEqual : validCount = 1 := by
        norm_num at capacity
        omega
      subst validCount
      funext basis
      have basisEqual : basis = zeroSelectorBasis 0 := Subsingleton.elim _ _
      simp [uniformTreeState, idealUniformSelectorState, selectorValue,
        zeroSelectorKet, basisKet, basisEqual]
  | succ width inductionHypothesis =>
      have nonzero : validCount ≠ 0 := Nat.ne_of_gt positive
      funext basis
      rw [uniformTreeState, dif_neg nonzero]
      let lower : AbstractSelectorBasis width :=
        fun index => basis index.castSucc
      cases highEqual : basis (Fin.last width)
      · rw [if_neg (by simp)]
        rw [cos_uniformRoot_eq_sqrt_ratio width validCount positive]
        rw [inductionHypothesis
          (uniformLeftCount width validCount)
          (uniformLeftCount_le_capacity width validCount)
          (uniformLeftCount_positive width validCount positive)]
        have valueEqual :
            selectorValue (width + 1) basis = selectorValue width lower := by
          simp [selectorValue, highEqual, lower]
        have supportIff := selectorValue_lt_leftCount_iff width validCount lower
        unfold idealUniformSelectorState
        rw [valueEqual]
        by_cases support : selectorValue width lower < validCount
        · have childSupport := supportIff.mpr support
          rw [if_pos childSupport, if_pos support]
          exact sqrt_ratio_mul_inverse_sqrt
            (uniformLeftCount width validCount) validCount
            (uniformLeftCount_positive width validCount positive) positive
        · have childOutside :
              ¬selectorValue width lower < uniformLeftCount width validCount :=
            fun childSupport => support (supportIff.mp childSupport)
          have childOutside' :
              ¬selectorValue width (fun index => basis index.castSucc) <
                uniformLeftCount width validCount := by
            simpa [lower] using childOutside
          rw [if_neg childOutside', if_neg support]
          simp
      · simp only [if_true]
        rw [sin_uniformRoot_eq_sqrt_ratio width validCount positive]
        by_cases rightZero : uniformRightCount width validCount = 0
        · have validCountLeCapacity : validCount ≤ 2 ^ width := by
            unfold uniformRightCount at rightZero
            have validCountLeLeft :
                validCount ≤ uniformLeftCount width validCount :=
              Nat.sub_eq_zero_iff_le.mp rightZero
            exact le_trans validCountLeLeft (min_le_right _ _)
          have outside :
              ¬selectorValue (width + 1) basis < validCount := by
            rw [selectorValue]
            simp only [highEqual, if_true]
            omega
          unfold idealUniformSelectorState
          simp [rightZero, outside]
        · have rightPositive : 0 < uniformRightCount width validCount :=
            Nat.pos_of_ne_zero rightZero
          rw [inductionHypothesis
            (uniformRightCount width validCount)
            (uniformRightCount_le_capacity width validCount capacity)
            rightPositive]
          have capacityLtValidCount : 2 ^ width < validCount := by
            by_contra notLess
            have validCountLeCapacity : validCount ≤ 2 ^ width :=
              Nat.le_of_not_gt notLess
            apply rightZero
            unfold uniformRightCount uniformLeftCount
            simp [min_eq_left validCountLeCapacity]
          have leftEqual : uniformLeftCount width validCount = 2 ^ width := by
            unfold uniformLeftCount
            exact min_eq_right (Nat.le_of_lt capacityLtValidCount)
          have valueEqual :
              selectorValue (width + 1) basis =
                2 ^ width + selectorValue width lower := by
            simp [selectorValue, highEqual, lower]
          have supportIff :
              selectorValue width lower < uniformRightCount width validCount ↔
                selectorValue (width + 1) basis < validCount := by
            rw [valueEqual]
            have rightEqual :
                uniformRightCount width validCount = validCount - 2 ^ width := by
              unfold uniformRightCount
              rw [leftEqual]
            rw [rightEqual]
            omega
          unfold idealUniformSelectorState
          by_cases support : selectorValue (width + 1) basis < validCount
          · have childSupport := supportIff.mpr support
            rw [if_pos childSupport, if_pos support]
            exact sqrt_ratio_mul_inverse_sqrt
              (uniformRightCount width validCount) validCount
              rightPositive positive
          · have childOutside :
                ¬selectorValue width lower < uniformRightCount width validCount :=
              fun childSupport => support (supportIff.mp childSupport)
            have childOutside' :
                ¬selectorValue width (fun index => basis index.castSucc) <
                  uniformRightCount width validCount := by
              simpa [lower] using childOutside
            rw [if_neg childOutside', if_neg support]
            simp

/-- 証明付き非2冪一様準備は、有効leafだけに厳密な一様振幅を作る。 -/
theorem abstractUniformPreparedState_correct
    (width validCount : Nat) (capacity : validCount ≤ 2 ^ width)
    (positive : 0 < validCount) :
    abstractUniformPreparedState width validCount capacity =
      idealUniformSelectorState width validCount := by
  rw [abstractUniformPreparedState_eq_uniformTreeState]
  exact uniformTreeState_eq_idealUniformSelectorState
    width validCount capacity positive

end

end VerifiedCircuitCore
