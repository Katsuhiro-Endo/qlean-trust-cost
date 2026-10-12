import QLean.MathematicalSpecifications.DelimiterEncoding

/-!
# Verification lemmas for the delimiter encoding

These proofs justify injectivity and the decoder laws used by correspondence
proofs.  They do not change the definitions in `DelimiterEncoding` and are
therefore excluded from the human approval reading set.
-/

set_option autoImplicit false

namespace QLean.MathematicalSpecifications.Targets

open QLean.MathematicalSpecifications.CoalescingWalkModel

noncomputable section

private theorem bitVec_eq_of_getLsb_eq {width : Nat}
    {left right : BitVec width}
    (equalBits : ∀ bit, left.getLsb bit = right.getLsb bit) :
    left = right := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases inRange : bit < width
  · simpa [BitVec.getLsb] using equalBits ⟨bit, inRange⟩
  · have widthLe : width ≤ bit := Nat.le_of_not_gt inRange
    have capacityLe : 2 ^ width ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide) widthLe
    have leftLt : left.toNat < 2 ^ bit := lt_of_lt_of_le left.isLt capacityLe
    have rightLt : right.toNat < 2 ^ bit := lt_of_lt_of_le right.isLt capacityLe
    rw [Nat.testBit_lt_two_pow leftLt, Nat.testBit_lt_two_pow rightLt]

private theorem siteBit_ext (parameters : CoalescingWalkModel.Parameters)
    {left right : CoalescingWalkModel.Site parameters}
    (equalBits : ∀ bit,
      siteBit parameters left bit = siteBit parameters right bit) :
    left = right := by
  have vectorEqual :
      siteBitVector parameters left = siteBitVector parameters right :=
    bitVec_eq_of_getLsb_eq equalBits
  have codeEqual := congrArg BitVec.toFin vectorEqual
  simpa [siteBitVector] using codeEqual

private def delimiterIndex (parameters : CoalescingWalkModel.Parameters)
    (configuration : CoalescingWalkModel.Configuration parameters) :
    Fin (delimiterWidth parameters) := by
  refine ⟨siteWordWidth parameters * configuration.1.card, ?_⟩
  have cardLe : configuration.1.card ≤ parameters.K := configuration.2.2
  have productLe := Nat.mul_le_mul_left (siteWordWidth parameters) cardLe
  simp only [delimiterWidth]
  omega

private def configurationWordIndex (parameters : CoalescingWalkModel.Parameters)
    (configuration : CoalescingWalkModel.Configuration parameters)
    (slot : Fin configuration.1.card)
    (bit : Fin (siteWordWidth parameters)) :
    Fin (delimiterWidth parameters) := by
  refine ⟨siteWordWidth parameters * slot.val + bit.val, ?_⟩
  have firstLt :
      siteWordWidth parameters * slot.val + bit.val <
        siteWordWidth parameters * (slot.val + 1) := by
    rw [Nat.mul_succ]
    exact Nat.add_lt_add_left bit.isLt _
  have secondLe :
      siteWordWidth parameters * (slot.val + 1) ≤
        siteWordWidth parameters * configuration.1.card :=
    Nat.mul_le_mul_left _ (Nat.succ_le_of_lt slot.isLt)
  have cardLe : configuration.1.card ≤ parameters.K := configuration.2.2
  have thirdLe := Nat.mul_le_mul_left (siteWordWidth parameters) cardLe
  simp only [delimiterWidth]
  omega

@[simp] private theorem configurationEncoding_delimiter
    (parameters : CoalescingWalkModel.Parameters)
    (configuration : CoalescingWalkModel.Configuration parameters) :
    configurationEncoding parameters configuration
      (delimiterIndex parameters configuration) = true := by
  simp [configurationEncoding, delimiterIndex]

private theorem configurationEncoding_after_delimiter
    (parameters : CoalescingWalkModel.Parameters)
    (configuration : CoalescingWalkModel.Configuration parameters)
    (physicalBit : Fin (delimiterWidth parameters))
    (after : siteWordWidth parameters * configuration.1.card < physicalBit.val) :
    configurationEncoding parameters configuration physicalBit = false := by
  simp [configurationEncoding, Nat.not_lt.mpr (Nat.le_of_lt after),
    ne_of_gt after]

private theorem configurationEncoding_word
    (parameters : CoalescingWalkModel.Parameters)
    (configuration : CoalescingWalkModel.Configuration parameters)
    (slot : Fin configuration.1.card)
    (wordBit : Fin (siteWordWidth parameters)) :
    configurationEncoding parameters configuration
        (configurationWordIndex parameters configuration slot wordBit) =
      siteBit parameters (CoalescingWalkModel.siteAt configuration slot) wordBit := by
  have before :
      siteWordWidth parameters * slot.val + wordBit.val <
        siteWordWidth parameters * configuration.1.card := by
    have firstLt :
        siteWordWidth parameters * slot.val + wordBit.val <
          siteWordWidth parameters * (slot.val + 1) := by
      rw [Nat.mul_succ]
      exact Nat.add_lt_add_left wordBit.isLt _
    exact lt_of_lt_of_le firstLt
      (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt slot.isLt))
  simp only [configurationEncoding, configurationWordIndex, before, dif_pos]
  let decodedSlot : Fin configuration.1.card :=
    ⟨(siteWordWidth parameters * slot.val + wordBit.val) /
        siteWordWidth parameters,
      (Nat.div_lt_iff_lt_mul (by
        simp [siteWordWidth, parameters.q_pos])).2
        (by simpa [Nat.mul_comm] using before)⟩
  let decodedBit : Fin (siteWordWidth parameters) :=
    ⟨(siteWordWidth parameters * slot.val + wordBit.val) %
        siteWordWidth parameters,
      Nat.mod_lt _ (by simp [siteWordWidth, parameters.q_pos])⟩
  change siteBit parameters
      (CoalescingWalkModel.siteAt configuration decodedSlot) decodedBit =
    siteBit parameters (CoalescingWalkModel.siteAt configuration slot) wordBit
  have slotEqual : decodedSlot = slot := by
    apply Fin.ext
    dsimp [decodedSlot]
    rw [Nat.mul_add_div (by simp [siteWordWidth, parameters.q_pos])]
    simp [Nat.div_eq_of_lt wordBit.isLt]
  have bitEqual : decodedBit = wordBit := by
    apply Fin.ext
    dsimp [decodedBit]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt wordBit.isLt
  rw [slotEqual, bitEqual]

private theorem configurationEncoding_card_eq
    (parameters : CoalescingWalkModel.Parameters)
    {left right : CoalescingWalkModel.Configuration parameters}
    (equalEncoding : configurationEncoding parameters left =
      configurationEncoding parameters right) :
    left.1.card = right.1.card := by
  have widthPositive : 0 < siteWordWidth parameters := by
    simp [siteWordWidth, parameters.q_pos]
  have notLeftSmaller : ¬left.1.card < right.1.card := by
    intro smaller
    have after : siteWordWidth parameters * left.1.card <
        (delimiterIndex parameters right).val := by
      change siteWordWidth parameters * left.1.card <
        siteWordWidth parameters * right.1.card
      exact Nat.mul_lt_mul_of_pos_left smaller widthPositive
    have valueEqual := congrFun equalEncoding (delimiterIndex parameters right)
    rw [configurationEncoding_after_delimiter parameters left _ after] at valueEqual
    simp at valueEqual
  have notRightSmaller : ¬right.1.card < left.1.card := by
    intro smaller
    have after : siteWordWidth parameters * right.1.card <
        (delimiterIndex parameters left).val := by
      change siteWordWidth parameters * right.1.card <
        siteWordWidth parameters * left.1.card
      exact Nat.mul_lt_mul_of_pos_left smaller widthPositive
    have valueEqual := congrFun equalEncoding (delimiterIndex parameters left)
    rw [configurationEncoding_after_delimiter parameters right _ after] at valueEqual
    simp at valueEqual
  omega

private theorem configurationEncoding_siteAt_eq
    (parameters : CoalescingWalkModel.Parameters)
    {left right : CoalescingWalkModel.Configuration parameters}
    (equalEncoding : configurationEncoding parameters left =
      configurationEncoding parameters right)
    (slot : Fin left.1.card) :
    CoalescingWalkModel.siteAt left slot =
      CoalescingWalkModel.siteAt right
        (Fin.cast (configurationEncoding_card_eq parameters equalEncoding) slot) := by
  apply siteBit_ext parameters
  intro wordBit
  let rightSlot : Fin right.1.card :=
    Fin.cast (configurationEncoding_card_eq parameters equalEncoding) slot
  have indexEqual :
      configurationWordIndex parameters left slot wordBit =
        configurationWordIndex parameters right rightSlot wordBit := by
    apply Fin.ext
    simp [configurationWordIndex, rightSlot]
  calc
    siteBit parameters (CoalescingWalkModel.siteAt left slot) wordBit =
        configurationEncoding parameters left
          (configurationWordIndex parameters left slot wordBit) := by
      symm
      exact configurationEncoding_word parameters left slot wordBit
    _ = configurationEncoding parameters right
          (configurationWordIndex parameters left slot wordBit) := by
      rw [equalEncoding]
    _ = configurationEncoding parameters right
          (configurationWordIndex parameters right rightSlot wordBit) := by
      rw [indexEqual]
    _ = siteBit parameters (CoalescingWalkModel.siteAt right rightSlot) wordBit :=
      configurationEncoding_word parameters right rightSlot wordBit

/-- The mathematical delimiter encoding is injective for all approved `q,K`. -/
theorem configurationEncoding_injective
    (parameters : CoalescingWalkModel.Parameters) :
    Function.Injective (configurationEncoding parameters) := by
  intro left right equalEncoding
  have cardEqual := configurationEncoding_card_eq parameters equalEncoding
  apply Subtype.ext
  apply Finset.ext
  intro site
  constructor
  · intro memberLeft
    let leftSlot : Fin left.1.card :=
      (left.1.orderIsoOfFin rfl).symm ⟨site, memberLeft⟩
    let rightSlot : Fin right.1.card := Fin.cast cardEqual leftSlot
    have leftValue : CoalescingWalkModel.siteAt left leftSlot = site := by
      change ((left.1.orderIsoOfFin rfl) leftSlot).1 = site
      have inverse := (left.1.orderIsoOfFin rfl).apply_symm_apply ⟨site, memberLeft⟩
      exact congrArg Subtype.val inverse
    have corresponding :=
      configurationEncoding_siteAt_eq parameters equalEncoding leftSlot
    have rightMember : CoalescingWalkModel.siteAt right rightSlot ∈ right.1 :=
      ((right.1.orderIsoOfFin rfl) rightSlot).2
    rw [leftValue] at corresponding
    rw [corresponding]
    simpa [rightSlot] using rightMember
  · intro memberRight
    let rightSlot : Fin right.1.card :=
      (right.1.orderIsoOfFin rfl).symm ⟨site, memberRight⟩
    let leftSlot : Fin left.1.card := Fin.cast cardEqual.symm rightSlot
    have rightValue : CoalescingWalkModel.siteAt right rightSlot = site := by
      change ((right.1.orderIsoOfFin rfl) rightSlot).1 = site
      have inverse := (right.1.orderIsoOfFin rfl).apply_symm_apply ⟨site, memberRight⟩
      exact congrArg Subtype.val inverse
    have corresponding :=
      configurationEncoding_siteAt_eq parameters equalEncoding leftSlot
    have castBack : Fin.cast cardEqual leftSlot = rightSlot := by
      apply Fin.ext
      rfl
    rw [castBack, rightValue] at corresponding
    have leftMember : CoalescingWalkModel.siteAt left leftSlot ∈ left.1 :=
      ((left.1.orderIsoOfFin rfl) leftSlot).2
    rw [corresponding] at leftMember
    exact leftMember

theorem configurationEncoding_isLegal
    (parameters : CoalescingWalkModel.Parameters)
    (configuration : CoalescingWalkModel.Configuration parameters) :
    IsLegalDelimiter parameters (configurationEncoding parameters configuration) :=
  ⟨configuration, rfl⟩

@[simp] theorem decodeConfiguration_encoding
    (parameters : CoalescingWalkModel.Parameters)
    (configuration : CoalescingWalkModel.Configuration parameters) :
    decodeConfiguration parameters (configurationEncoding parameters configuration) =
      some configuration := by
  classical
  rw [decodeConfiguration,
    dif_pos (configurationEncoding_isLegal parameters configuration)]
  congr 1
  apply configurationEncoding_injective parameters
  exact Classical.choose_spec
    (configurationEncoding_isLegal parameters configuration)

theorem decodeConfiguration_eq_some_iff
    (parameters : CoalescingWalkModel.Parameters)
    {bits : DelimiterWord parameters}
    {configuration : CoalescingWalkModel.Configuration parameters} :
    decodeConfiguration parameters bits = some configuration ↔
      configurationEncoding parameters configuration = bits := by
  classical
  constructor
  · intro decoded
    unfold decodeConfiguration at decoded
    split at decoded
    · rename_i legal
      simp only [Option.some.injEq] at decoded
      subst configuration
      exact Classical.choose_spec legal
    · simp at decoded
  · intro encoded
    subst bits
    exact decodeConfiguration_encoding parameters configuration

theorem decodeConfiguration_eq_none_iff
    (parameters : CoalescingWalkModel.Parameters)
    {bits : DelimiterWord parameters} :
    decodeConfiguration parameters bits = none ↔
      ¬IsLegalDelimiter parameters bits := by
  classical
  unfold decodeConfiguration
  split <;> simp_all

end

end QLean.MathematicalSpecifications.Targets
