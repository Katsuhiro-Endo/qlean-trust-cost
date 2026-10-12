import QLean.Generator.Implementation.QTopLevelStatePipeline
import QLean.Generator.Implementation.QSelectorBitBridge
import Mathlib.Tactic

/-!
# selector基底と全物理基底の有限和橋渡し

selector外を任意背景に固定した`JointBasis`と`AbstractSelectorBasis`を型安全なwire写像で
同一視する。さらに、全物理基底上の有限和からselector外不一致の零項を除き、抽象基底、
有効な`QSelector`へ再添字付けする。量子状態の巨大行列や全基底の列挙は用いない。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 任意背景のselector wireだけを指定した抽象bit列で上書きした物理基底。 -/
noncomputable def selectorBasisOver
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorBasis : AbstractSelectorBasis p.selectorWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  Function.extend selectorWire selectorBasis background

/-- selector wire写像が単射なら、埋め込んだ物理基底から指定selector bitを厳密に読める。 -/
theorem selectorBasisOver_apply_selector
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorBasis : AbstractSelectorBasis p.selectorWidth)
    (index : Fin p.selectorWidth) :
    selectorBasisOver p selectorWire background selectorBasis
        (selectorWire index) = selectorBasis index := by
  unfold selectorBasisOver Function.extend
  let witness : ∃ candidate, selectorWire candidate = selectorWire index := ⟨index, rfl⟩
  rw [dif_pos witness]
  congr 1
  exact selectorInjective (Classical.choose_spec witness)

/-- selector slice外では、埋め込んだ物理基底は背景基底と一致する。 -/
theorem selectorBasisOver_apply_outside
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorBasis : AbstractSelectorBasis p.selectorWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ selectorSliceWires p selectorWire) :
    selectorBasisOver p selectorWire background selectorBasis wire = background wire := by
  unfold selectorBasisOver Function.extend
  rw [dif_neg]
  intro witness
  rcases witness with ⟨index, wireEqual⟩
  apply outside
  exact List.mem_map.mpr ⟨index, List.mem_finRange _, wireEqual⟩

/-- 埋め込んだ物理基底はselector外で指定背景と一致する。 -/
theorem selectorBasisOver_outsideMatches
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorBasis : AbstractSelectorBasis p.selectorWidth) :
    OutsideSelectorMatches p selectorWire background
      (selectorBasisOver p selectorWire background selectorBasis) := by
  intro wire outside
  exact selectorBasisOver_apply_outside p selectorWire background selectorBasis wire outside

/-- selector wire写像が単射なら、物理埋込みをselectorへ射影すると元の抽象基底へ戻る。 -/
@[simp] theorem projectSelectorBasis_selectorBasisOver
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorBasis : AbstractSelectorBasis p.selectorWidth) :
    projectSelectorBasis p selectorWire
        (selectorBasisOver p selectorWire background selectorBasis) = selectorBasis := by
  funext index
  exact selectorBasisOver_apply_selector p selectorWire selectorInjective background
    selectorBasis index

/-- selector外一致基底は、そのselector射影を背景上へ埋め戻すと元の物理基底へ戻る。 -/
theorem selectorBasisOver_project_eq
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p selectorWire background basis) :
    selectorBasisOver p selectorWire background
      (projectSelectorBasis p selectorWire basis) = basis := by
  funext wire
  by_cases member : wire ∈ selectorSliceWires p selectorWire
  · rcases List.mem_map.mp member with ⟨index, _, wireEqual⟩
    subst wire
    exact selectorBasisOver_apply_selector p selectorWire selectorInjective background
      (projectSelectorBasis p selectorWire basis) index
  · rw [selectorBasisOver_apply_outside p selectorWire background _ wire member]
    exact (outside wire member).symm

/-- selector外が背景に一致する物理基底の有限型。 -/
abbrev SelectorBackgroundFiber
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background : JointBasis p.ancillaWidth p.systemWidth) :=
  {basis : JointBasis p.ancillaWidth p.systemWidth //
    OutsideSelectorMatches p selectorWire background basis}

/-- selector外背景一致条件を有限和フィルタで使うための決定可能性。 -/
noncomputable instance outsideSelectorMatchesDecidable
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background basis : JointBasis p.ancillaWidth p.systemWidth) :
    Decidable (OutsideSelectorMatches p selectorWire background basis) :=
  Classical.propDecidable _

/-- 単射なselector wire上で、抽象selector基底と背景固定物理基底は同値である。 -/
noncomputable def selectorBackgroundFiberEquiv
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    AbstractSelectorBasis p.selectorWidth ≃
      SelectorBackgroundFiber p selectorWire background where
  toFun selectorBasis :=
    ⟨selectorBasisOver p selectorWire background selectorBasis,
      selectorBasisOver_outsideMatches p selectorWire background selectorBasis⟩
  invFun basis := projectSelectorBasis p selectorWire basis.1
  left_inv selectorBasis :=
    projectSelectorBasis_selectorBasisOver p selectorWire selectorInjective background
      selectorBasis
  right_inv basis := by
    apply Subtype.ext
    exact selectorBasisOver_project_eq p selectorWire selectorInjective background
      basis.1 basis.2

/-- 背景固定物理基底上の有限和を、全抽象selector基底上の有限和へ再添字付けする。 -/
theorem sum_selectorBackgroundFiber_eq_sum_abstract
    {M : Type*} [AddCommMonoid M]
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (f : JointBasis p.ancillaWidth p.systemWidth → M) :
    (∑ basis : SelectorBackgroundFiber p selectorWire background, f basis.1) =
      ∑ selectorBasis : AbstractSelectorBasis p.selectorWidth,
        f (selectorBasisOver p selectorWire background selectorBasis) := by
  symm
  exact Equiv.sum_comp
    (selectorBackgroundFiberEquiv p selectorWire selectorInjective background)
    (fun basis => f basis.1)

/-- selector外不一致で0となる全物理基底和を、抽象selector基底和へ再添字付けする。 -/
theorem sum_jointBasis_eq_sum_abstract_of_zero_outside
    {M : Type*} [AddCommMonoid M]
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (f : JointBasis p.ancillaWidth p.systemWidth → M)
    (zeroOutside : ∀ basis,
      ¬OutsideSelectorMatches p selectorWire background basis → f basis = 0) :
    (∑ basis, f basis) =
      ∑ selectorBasis : AbstractSelectorBasis p.selectorWidth,
        f (selectorBasisOver p selectorWire background selectorBasis) := by
  let matching : Finset (JointBasis p.ancillaWidth p.systemWidth) :=
    Finset.univ.filter fun basis =>
      OutsideSelectorMatches p selectorWire background basis
  calc
    (∑ basis, f basis) = ∑ basis ∈ matching, f basis := by
      symm
      apply Finset.sum_subset
      · intro basis basisMember
        simp [matching] at basisMember ⊢
      · intro basis _ notMatching
        apply zeroOutside basis
        simpa [matching] using notMatching
    _ = ∑ basis : SelectorBackgroundFiber p selectorWire background, f basis.1 := by
      apply Finset.sum_subtype
      intro basis
      simp [matching]
    _ = ∑ selectorBasis : AbstractSelectorBasis p.selectorWidth,
        f (selectorBasisOver p selectorWire background selectorBasis) :=
      sum_selectorBackgroundFiber_eq_sum_abstract p selectorWire selectorInjective
        background f

/-- `liftSelectorStateOver`を含む全物理基底和を全抽象selector基底和へ移す。 -/
theorem sum_liftSelectorStateOver_mul_eq_sum_abstract
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorState : AbstractSelectorBasis p.selectorWidth → ℂ)
    (weight : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    (∑ basis,
      liftSelectorStateOver p selectorWire background selectorState basis * weight basis) =
      ∑ selectorBasis : AbstractSelectorBasis p.selectorWidth,
        selectorState selectorBasis *
          weight (selectorBasisOver p selectorWire background selectorBasis) := by
  rw [sum_jointBasis_eq_sum_abstract_of_zero_outside p selectorWire
    selectorInjective background]
  · apply Fintype.sum_congr
    intro selectorBasis
    simp [liftSelectorStateOver,
      selectorBasisOver_outsideMatches p selectorWire background selectorBasis,
      projectSelectorBasis_selectorBasisOver p selectorWire selectorInjective background]
  · intro basis outside
    simp [liftSelectorStateOver, outside]

/-- 共役した`liftSelectorStateOver`を含む内積型の全物理基底和を抽象和へ移す。 -/
theorem sum_star_liftSelectorStateOver_mul_eq_sum_abstract
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorState : AbstractSelectorBasis p.selectorWidth → ℂ)
    (weight : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    (∑ basis,
      star (liftSelectorStateOver p selectorWire background selectorState basis) *
        weight basis) =
      ∑ selectorBasis : AbstractSelectorBasis p.selectorWidth,
        star (selectorState selectorBasis) *
          weight (selectorBasisOver p selectorWire background selectorBasis) := by
  rw [sum_jointBasis_eq_sum_abstract_of_zero_outside p selectorWire
    selectorInjective background]
  · apply Fintype.sum_congr
    intro selectorBasis
    simp [liftSelectorStateOver,
      selectorBasisOver_outsideMatches p selectorWire background selectorBasis,
      projectSelectorBasis_selectorBasisOver p selectorWire selectorInjective background]
  · intro basis outside
    simp [liftSelectorStateOver, outside]

/-- 自然数をlittle-endianの固定幅抽象selector基底へ符号化する。 -/
def selectorBasisOfNat (width value : Nat) : AbstractSelectorBasis width :=
  fun index => value.testBit index.val

/-- 容量内自然数を抽象selector基底へ符号化して復号すると元の値へ戻る。 -/
theorem selectorValue_selectorBasisOfNat
    (width value : Nat) (valueInRange : value < 2 ^ width) :
    selectorValue width (selectorBasisOfNat width value) = value := by
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases inRange : index < width
  · let finiteIndex : Fin width := ⟨index, inRange⟩
    rw [selectorValue_testBit width (selectorBasisOfNat width value) finiteIndex]
    rfl
  · have widthLe : width ≤ index := Nat.le_of_not_gt inRange
    have decodedLt : selectorValue width (selectorBasisOfNat width value) < 2 ^ index :=
      lt_of_lt_of_le
        (selectorValue_lt_capacity width (selectorBasisOfNat width value))
        (Nat.pow_le_pow_right (by decide) widthLe)
    have valueLt : value < 2 ^ index :=
      lt_of_lt_of_le valueInRange
        (Nat.pow_le_pow_right (by decide) widthLe)
    rw [Nat.testBit_lt_two_pow decodedLt, Nat.testBit_lt_two_pow valueLt]

/-- 抽象selector基底を復号して同じ幅へ再符号化すると元のbit関数へ戻る。 -/
@[simp] theorem selectorBasisOfNat_selectorValue
    (width : Nat) (selectorBasis : AbstractSelectorBasis width) :
    selectorBasisOfNat width (selectorValue width selectorBasis) = selectorBasis := by
  funext index
  exact selectorValue_testBit width selectorBasis index

/-- 値が`selectorCount`未満である有効抽象selector基底の有限型。 -/
abbrev ActiveAbstractSelectorBasis (p : QParameters) :=
  {basis : AbstractSelectorBasis p.selectorWidth //
    selectorValue p.selectorWidth basis < p.selectorCount}

/-- 有効抽象selector基底と`QSelector = Fin selectorCount`の同値。 -/
def activeAbstractSelectorEquiv (p : QParameters) :
    ActiveAbstractSelectorBasis p ≃ QSelector p where
  toFun basis := ⟨selectorValue p.selectorWidth basis.1, basis.2⟩
  invFun selector := by
    refine ⟨selectorBasisOfNat p.selectorWidth selector.val, ?_⟩
    rw [selectorValue_selectorBasisOfNat p.selectorWidth selector.val
      (qSelector_lt_capacity p selector)]
    exact selector.isLt
  left_inv basis := by
    apply Subtype.ext
    exact selectorBasisOfNat_selectorValue p.selectorWidth basis.1
  right_inv selector := by
    apply Fin.ext
    exact selectorValue_selectorBasisOfNat p.selectorWidth selector.val
      (qSelector_lt_capacity p selector)

/-- 有効抽象selector基底上の有限和を`QSelector`上の有限和へ再添字付けする。 -/
theorem sum_activeAbstractSelectorBasis_eq_sum_qSelector
    {M : Type*} [AddCommMonoid M]
    (p : QParameters)
    (f : AbstractSelectorBasis p.selectorWidth → M) :
    (∑ basis : ActiveAbstractSelectorBasis p, f basis.1) =
      ∑ selector : QSelector p,
        f (selectorBasisOfNat p.selectorWidth selector.val) := by
  exact Fintype.sum_equiv (activeAbstractSelectorEquiv p)
    (fun basis : ActiveAbstractSelectorBasis p => f basis.1)
    (fun selector : QSelector p =>
      f (selectorBasisOfNat p.selectorWidth selector.val)) (by
        intro basis
        simp [activeAbstractSelectorEquiv])

/-- selector外背景一致と`selectorCount`未満を合わせた物理基底の受理条件。 -/
def SelectorBasisAcceptedOver
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  OutsideSelectorMatches p selectorWire background basis ∧
    selectorValue p.selectorWidth
      (projectSelectorBasis p selectorWire basis) < p.selectorCount

/-- selector物理基底の受理条件を有限和フィルタで使うための決定可能性。 -/
noncomputable instance selectorBasisAcceptedOverDecidable
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background basis : JointBasis p.ancillaWidth p.systemWidth) :
    Decidable (SelectorBasisAcceptedOver p selectorWire background basis) :=
  Classical.propDecidable _

/-- 指定背景上で有効selector値を持つ受理物理基底の有限型。 -/
abbrev AcceptedSelectorJointBasis
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background : JointBasis p.ancillaWidth p.systemWidth) :=
  {basis : JointBasis p.ancillaWidth p.systemWidth //
    SelectorBasisAcceptedOver p selectorWire background basis}

/-- 単射selector wire上で、`QSelector`と受理物理基底は厳密に同値である。 -/
noncomputable def qSelectorAcceptedJointBasisEquiv
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    QSelector p ≃ AcceptedSelectorJointBasis p selectorWire background where
  toFun selector := by
    let selectorBasis := selectorBasisOfNat p.selectorWidth selector.val
    let basis := selectorBasisOver p selectorWire background selectorBasis
    have outside : OutsideSelectorMatches p selectorWire background basis :=
      selectorBasisOver_outsideMatches p selectorWire background selectorBasis
    have projected : projectSelectorBasis p selectorWire basis = selectorBasis :=
      projectSelectorBasis_selectorBasisOver p selectorWire selectorInjective background
        selectorBasis
    have active : selectorValue p.selectorWidth
        (projectSelectorBasis p selectorWire basis) < p.selectorCount := by
      rw [projected, selectorValue_selectorBasisOfNat p.selectorWidth selector.val
        (qSelector_lt_capacity p selector)]
      exact selector.isLt
    exact ⟨basis, outside, active⟩
  invFun basis :=
    ⟨selectorValue p.selectorWidth
      (projectSelectorBasis p selectorWire basis.1), basis.2.2⟩
  left_inv selector := by
    apply Fin.ext
    change selectorValue p.selectorWidth
        (projectSelectorBasis p selectorWire
          (selectorBasisOver p selectorWire background
            (selectorBasisOfNat p.selectorWidth selector.val))) = selector.val
    rw [projectSelectorBasis_selectorBasisOver p selectorWire selectorInjective background]
    exact selectorValue_selectorBasisOfNat p.selectorWidth selector.val
      (qSelector_lt_capacity p selector)
  right_inv basis := by
    apply Subtype.ext
    change selectorBasisOver p selectorWire background
        (selectorBasisOfNat p.selectorWidth
          (selectorValue p.selectorWidth
            (projectSelectorBasis p selectorWire basis.1))) = basis.1
    rw [selectorBasisOfNat_selectorValue]
    exact selectorBasisOver_project_eq p selectorWire selectorInjective background
      basis.1 basis.2.1

/-- 受理物理基底上の有限和を`QSelector`上の有限和へ再添字付けする。 -/
theorem sum_acceptedSelectorJointBasis_eq_sum_qSelector
    {M : Type*} [AddCommMonoid M]
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (f : JointBasis p.ancillaWidth p.systemWidth → M) :
    (∑ basis : AcceptedSelectorJointBasis p selectorWire background, f basis.1) =
      ∑ selector : QSelector p,
        f (selectorBasisOver p selectorWire background
          (selectorBasisOfNat p.selectorWidth selector.val)) := by
  symm
  exact Equiv.sum_comp
    (qSelectorAcceptedJointBasisEquiv p selectorWire selectorInjective background)
    (fun basis => f basis.1)

/-- 受理条件外で0となる全物理基底和を`QSelector`上の有限和へ移す。 -/
theorem sum_jointBasis_eq_sum_qSelector_of_zero_unaccepted
    {M : Type*} [AddCommMonoid M]
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (f : JointBasis p.ancillaWidth p.systemWidth → M)
    (zeroUnaccepted : ∀ basis,
      ¬SelectorBasisAcceptedOver p selectorWire background basis → f basis = 0) :
    (∑ basis, f basis) =
      ∑ selector : QSelector p,
        f (selectorBasisOver p selectorWire background
          (selectorBasisOfNat p.selectorWidth selector.val)) := by
  let accepted : Finset (JointBasis p.ancillaWidth p.systemWidth) :=
    Finset.univ.filter fun basis =>
      SelectorBasisAcceptedOver p selectorWire background basis
  calc
    (∑ basis, f basis) = ∑ basis ∈ accepted, f basis := by
      symm
      apply Finset.sum_subset
      · intro basis basisMember
        simp [accepted] at basisMember ⊢
      · intro basis _ notAccepted
        apply zeroUnaccepted basis
        simpa [accepted] using notAccepted
    _ = ∑ basis : AcceptedSelectorJointBasis p selectorWire background,
        f basis.1 := by
      apply Finset.sum_subtype
      intro basis
      simp [accepted]
    _ = ∑ selector : QSelector p,
        f (selectorBasisOver p selectorWire background
          (selectorBasisOfNat p.selectorWidth selector.val)) :=
      sum_acceptedSelectorJointBasis_eq_sum_qSelector p selectorWire
        selectorInjective background f

/-- `qRowUniformOverlap`の全物理基底和は、ちょうど`selectorCount = 6K`項の和である。 -/
theorem qRowUniformOverlap_eq_qSelector_sum
    (p : QParameters)
    (system : RegisterBasis p.systemWidth)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    qRowUniformOverlap p system state =
      ∑ selector : QSelector p,
        ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
          state (selectorBasisOver p (rowSelectorWire p)
            (zeroAncillaJointBasis p system)
            (selectorBasisOfNat p.selectorWidth selector.val)) := by
  rw [qRowUniformOverlap_eq_accepted_sum]
  change (∑ basis,
    if SelectorBasisAcceptedOver p (rowSelectorWire p)
        (zeroAncillaJointBasis p system) basis then
      ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) * state basis
    else 0) = _
  rw [sum_jointBasis_eq_sum_qSelector_of_zero_unaccepted p (rowSelectorWire p)
    (sharedRowSelectorWire_injective p) (zeroAncillaJointBasis p system)]
  · apply Fintype.sum_congr
    intro selector
    have outside := selectorBasisOver_outsideMatches p (rowSelectorWire p)
      (zeroAncillaJointBasis p system)
      (selectorBasisOfNat p.selectorWidth selector.val)
    have projected := projectSelectorBasis_selectorBasisOver p (rowSelectorWire p)
      (sharedRowSelectorWire_injective p) (zeroAncillaJointBasis p system)
      (selectorBasisOfNat p.selectorWidth selector.val)
    have decoded := selectorValue_selectorBasisOfNat p.selectorWidth selector.val
      (qSelector_lt_capacity p selector)
    simp [SelectorBasisAcceptedOver, outside, projected, decoded, selector.isLt]
  · intro basis notAccepted
    simp [notAccepted]

/-- 抽象selector物理埋込みは、単射wire写像の下でそれ自身も単射である。 -/
theorem selectorBasisOver_injective
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    Function.Injective (selectorBasisOver p selectorWire background) := by
  intro left right equal
  have projected := congrArg (projectSelectorBasis p selectorWire) equal
  simpa only [projectSelectorBasis_selectorBasisOver p selectorWire selectorInjective
    background] using projected

/-- canonical column selectorの任意背景上埋込みは単射である。 -/
theorem columnSelectorBasisOver_injective
    (p : QParameters)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    Function.Injective (selectorBasisOver p (columnSelectorWire p) background) :=
  selectorBasisOver_injective p (columnSelectorWire p)
    (sharedColumnSelectorWire_injective p) background

/-- canonical row selectorの任意背景上埋込みは単射である。 -/
theorem rowSelectorBasisOver_injective
    (p : QParameters)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    Function.Injective (selectorBasisOver p (rowSelectorWire p) background) :=
  selectorBasisOver_injective p (rowSelectorWire p)
    (sharedRowSelectorWire_injective p) background

/-- 全0背景に対するselector外一致条件は、既存のselector外全0条件と同値である。 -/
theorem outsideSelectorMatches_zeroJointBasis_iff
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth) :
    OutsideSelectorMatches p selectorWire (zeroJointBasis p) basis ↔
      OutsideSelectorZero p selectorWire basis := by
  rfl

/-- 全0背景固定物理基底と抽象selector基底の同値。 -/
noncomputable def zeroBackgroundSelectorFiberEquiv
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire) :
    AbstractSelectorBasis p.selectorWidth ≃
      SelectorBackgroundFiber p selectorWire (zeroJointBasis p) :=
  selectorBackgroundFiberEquiv p selectorWire selectorInjective (zeroJointBasis p)

/-- canonical column selectorについて任意背景固定物理基底との同値を得る。 -/
noncomputable def columnSelectorBackgroundFiberEquiv
    (p : QParameters)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    AbstractSelectorBasis p.selectorWidth ≃
      SelectorBackgroundFiber p (columnSelectorWire p) background :=
  selectorBackgroundFiberEquiv p (columnSelectorWire p)
    (sharedColumnSelectorWire_injective p) background

/-- canonical row selectorについて任意背景固定物理基底との同値を得る。 -/
noncomputable def rowSelectorBackgroundFiberEquiv
    (p : QParameters)
    (background : JointBasis p.ancillaWidth p.systemWidth) :
    AbstractSelectorBasis p.selectorWidth ≃
      SelectorBackgroundFiber p (rowSelectorWire p) background :=
  selectorBackgroundFiberEquiv p (rowSelectorWire p)
    (sharedRowSelectorWire_injective p) background

end

end ProbabilityGeneratorQProof
