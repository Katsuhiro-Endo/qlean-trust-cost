import QLean.Generator.Analysis.QParameters
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Order
import Mathlib.Tactic

/-!
# delimiter配置符号と物理system空間

一般`q,K`の周期格子配置を、技術レポートどおり`2qK+1` bitのdelimiter符号へ写す。
site wordだけを二進展開し、配置全体をdense basis番号へ変換しない。
-/

namespace ProbabilityGeneratorQProof

open QParameters

/-- `G × G`周期格子上のsiteを、座標対の辞書順に一致する有限値で表す。 -/
abbrev QSite (p : QParameters) := Fin (p.G * p.G)

/-- 粒子数が1以上`K`以下である合法配置。 -/
abbrev QConfiguration (p : QParameters) :=
  {sites : Finset (QSite p) // 1 ≤ sites.card ∧ sites.card ≤ p.K}

/-- 一つのsite wordが持つ状態数は`2^(2q)`に等しい。 -/
theorem siteCapacity_eq (p : QParameters) :
    p.G * p.G = 2 ^ p.wordWidth := by
  simp [QParameters.G, QParameters.wordWidth, pow_add, two_mul]

/-- 座標対と`2q` bit wordの有限値との明示的な同値。 -/
def siteCodeEquiv (p : QParameters) : QSite p ≃ Fin (2 ^ p.wordWidth) where
  toFun site := Fin.cast (siteCapacity_eq p) site
  invFun code := Fin.cast (siteCapacity_eq p).symm code
  left_inv site := by simp
  right_inv code := by simp

/-- siteをlittle-endianの`2q` bit wordへ変換する。 -/
def siteBitVector (p : QParameters) (site : QSite p) : BitVec p.wordWidth :=
  BitVec.ofFin (siteCodeEquiv p site)

/-- site wordの指定little-endian bitを読む。 -/
def siteBit (p : QParameters) (site : QSite p) (bit : Fin p.wordWidth) : Bool :=
  (siteBitVector p site).getLsb bit

/-- 有限bit vectorは全little-endian bitの値によって一意に決まる。 -/
theorem bitVec_eq_of_getLsb_eq {width : Nat} {left right : BitVec width}
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

/-- 全bitが一致する二つのsite wordは同じsiteを表す。 -/
theorem siteBit_ext (p : QParameters) {left right : QSite p}
    (equalBits : ∀ bit, siteBit p left bit = siteBit p right bit) :
    left = right := by
  have vectorEqual : siteBitVector p left = siteBitVector p right :=
    bitVec_eq_of_getLsb_eq equalBits
  have codeEqual := congrArg BitVec.toFin vectorEqual
  simpa [siteBitVector] using (siteCodeEquiv p).injective codeEqual

namespace QConfiguration

/-- 配置のsiteを昇順slot番号で参照する。 -/
def siteAt {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin configuration.1.card) : QSite p :=
  ((configuration.1.orderIsoOfFin rfl) slot).1

/-- 昇順slot参照は単射である。 -/
theorem siteAt_injective {p : QParameters} (configuration : QConfiguration p) :
    Function.Injective configuration.siteAt := by
  intro left right equal
  apply (configuration.1.orderIsoOfFin rfl).injective
  apply Subtype.ext
  exact equal

end QConfiguration

/-- delimiter符号内で配置の終端1-bitが置かれる位置。 -/
def delimiterIndex {p : QParameters} (configuration : QConfiguration p) :
    Fin p.systemWidth := by
  refine ⟨p.wordWidth * configuration.1.card, ?_⟩
  have cardLe : configuration.1.card ≤ p.K := configuration.2.2
  have productLe := Nat.mul_le_mul_left p.wordWidth cardLe
  simp only [QParameters.systemWidth]
  omega

/-- 指定slotとword内bitに対応するsystem register上の位置。 -/
def configurationWordIndex {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin configuration.1.card) (bit : Fin p.wordWidth) :
    Fin p.systemWidth := by
  refine ⟨p.wordWidth * slot.val + bit.val, ?_⟩
  have firstLt : p.wordWidth * slot.val + bit.val <
      p.wordWidth * (slot.val + 1) := by
    rw [Nat.mul_succ]
    exact Nat.add_lt_add_left bit.isLt _
  have secondLe : p.wordWidth * (slot.val + 1) ≤
      p.wordWidth * configuration.1.card :=
    Nat.mul_le_mul_left p.wordWidth (Nat.succ_le_of_lt slot.isLt)
  have cardLe : configuration.1.card ≤ p.K := configuration.2.2
  have thirdLe := Nat.mul_le_mul_left p.wordWidth cardLe
  simp only [QParameters.systemWidth]
  omega

/-- 合法配置を、昇順site wordと一個のdelimiter bitからなる物理bit列へ符号化する。 -/
def delimiterEncoding {p : QParameters} (configuration : QConfiguration p) :
    RegisterBasis p.systemWidth :=
  fun physicalBit =>
    if beforeDelimiter : physicalBit.val < p.wordWidth * configuration.1.card then
      let slot : Fin configuration.1.card :=
        ⟨physicalBit.val / p.wordWidth,
          (Nat.div_lt_iff_lt_mul (by simp [QParameters.wordWidth, p.q_pos])).2
            (by simpa [Nat.mul_comm] using beforeDelimiter)⟩
      let wordBit : Fin p.wordWidth :=
        ⟨physicalBit.val % p.wordWidth,
          Nat.mod_lt _ (by simp [QParameters.wordWidth, p.q_pos])⟩
      siteBit p (configuration.siteAt slot) wordBit
    else
      decide (physicalBit.val = p.wordWidth * configuration.1.card)

/-- 合法配置のdelimiter位置には必ず1が入る。 -/
@[simp] theorem delimiterEncoding_delimiter
    {p : QParameters} (configuration : QConfiguration p) :
    delimiterEncoding configuration (delimiterIndex configuration) = true := by
  simp [delimiterEncoding, delimiterIndex]

/-- delimiterより後ろのpadding bitはすべて0である。 -/
theorem delimiterEncoding_after_delimiter
    {p : QParameters} (configuration : QConfiguration p)
    (physicalBit : Fin p.systemWidth)
    (after : p.wordWidth * configuration.1.card < physicalBit.val) :
    delimiterEncoding configuration physicalBit = false := by
  simp [delimiterEncoding, Nat.not_lt.mpr (Nat.le_of_lt after), ne_of_gt after]

/-- delimiterより前の指定slot/bitには、そのsite wordの対応bitが入る。 -/
theorem delimiterEncoding_word
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin configuration.1.card) (wordBit : Fin p.wordWidth) :
    delimiterEncoding configuration (configurationWordIndex configuration slot wordBit) =
      siteBit p (configuration.siteAt slot) wordBit := by
  have before : p.wordWidth * slot.val + wordBit.val <
      p.wordWidth * configuration.1.card := by
    have firstLt : p.wordWidth * slot.val + wordBit.val <
        p.wordWidth * (slot.val + 1) := by
      rw [Nat.mul_succ]
      exact Nat.add_lt_add_left wordBit.isLt _
    exact lt_of_lt_of_le firstLt
      (Nat.mul_le_mul_left p.wordWidth (Nat.succ_le_of_lt slot.isLt))
  simp only [delimiterEncoding, configurationWordIndex, before, dif_pos]
  let decodedSlot : Fin configuration.1.card :=
    ⟨(p.wordWidth * slot.val + wordBit.val) / p.wordWidth,
      (Nat.div_lt_iff_lt_mul (by simp [QParameters.wordWidth, p.q_pos])).2
        (by simpa [Nat.mul_comm] using before)⟩
  let decodedBit : Fin p.wordWidth :=
    ⟨(p.wordWidth * slot.val + wordBit.val) % p.wordWidth,
      Nat.mod_lt _ (by simp [QParameters.wordWidth, p.q_pos])⟩
  change siteBit p (configuration.siteAt decodedSlot) decodedBit =
    siteBit p (configuration.siteAt slot) wordBit
  have slotEqual : decodedSlot = slot := by
    apply Fin.ext
    dsimp [decodedSlot]
    rw [Nat.mul_add_div (by simp [QParameters.wordWidth, p.q_pos])]
    simp [Nat.div_eq_of_lt wordBit.isLt]
  have bitEqual : decodedBit = wordBit := by
    apply Fin.ext
    dsimp [decodedBit]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt wordBit.isLt
  rw [slotEqual, bitEqual]

/-- delimiter符号の一致から、二つの配置の粒子数が一致する。 -/
theorem delimiterEncoding_card_eq
    {p : QParameters} {left right : QConfiguration p}
    (equalEncoding : delimiterEncoding left = delimiterEncoding right) :
    left.1.card = right.1.card := by
  have wordWidthPositive : 0 < p.wordWidth := by
    simp [QParameters.wordWidth, p.q_pos]
  have notLeftSmaller : ¬left.1.card < right.1.card := by
    intro smaller
    have after : p.wordWidth * left.1.card < (delimiterIndex right).val := by
      change p.wordWidth * left.1.card < p.wordWidth * right.1.card
      exact Nat.mul_lt_mul_of_pos_left smaller wordWidthPositive
    have valueEqual := congrFun equalEncoding (delimiterIndex right)
    rw [delimiterEncoding_after_delimiter left (delimiterIndex right) after] at valueEqual
    simp at valueEqual
  have notRightSmaller : ¬right.1.card < left.1.card := by
    intro smaller
    have after : p.wordWidth * right.1.card < (delimiterIndex left).val := by
      change p.wordWidth * right.1.card < p.wordWidth * left.1.card
      exact Nat.mul_lt_mul_of_pos_left smaller wordWidthPositive
    have valueEqual := congrFun equalEncoding (delimiterIndex left)
    rw [delimiterEncoding_after_delimiter right (delimiterIndex left) after] at valueEqual
    simp at valueEqual
  omega

/-- 同じdelimiter符号を持つ二つの配置では、対応する昇順slotのsiteが一致する。 -/
theorem delimiterEncoding_siteAt_eq
    {p : QParameters} {left right : QConfiguration p}
    (equalEncoding : delimiterEncoding left = delimiterEncoding right)
    (slot : Fin left.1.card) :
    left.siteAt slot =
      right.siteAt (Fin.cast (delimiterEncoding_card_eq equalEncoding) slot) := by
  apply siteBit_ext
  intro wordBit
  let rightSlot : Fin right.1.card :=
    Fin.cast (delimiterEncoding_card_eq equalEncoding) slot
  have indexEqual :
      configurationWordIndex left slot wordBit =
        configurationWordIndex right rightSlot wordBit := by
    apply Fin.ext
    simp [configurationWordIndex, rightSlot]
  calc
    siteBit p (left.siteAt slot) wordBit =
        delimiterEncoding left (configurationWordIndex left slot wordBit) := by
      symm
      exact delimiterEncoding_word left slot wordBit
    _ = delimiterEncoding right (configurationWordIndex left slot wordBit) := by
      rw [equalEncoding]
    _ = delimiterEncoding right (configurationWordIndex right rightSlot wordBit) := by
      rw [indexEqual]
    _ = siteBit p (right.siteAt rightSlot) wordBit :=
      delimiterEncoding_word right rightSlot wordBit

/-- delimiter符号は一般`q,K`の全合法配置上で単射である。 -/
theorem delimiterEncoding_injective {p : QParameters} :
    Function.Injective (@delimiterEncoding p) := by
  intro left right equalEncoding
  have cardEqual := delimiterEncoding_card_eq equalEncoding
  apply Subtype.ext
  apply Finset.ext
  intro site
  constructor
  · intro memberLeft
    let leftSlot : Fin left.1.card :=
      (left.1.orderIsoOfFin rfl).symm ⟨site, memberLeft⟩
    let rightSlot : Fin right.1.card := Fin.cast cardEqual leftSlot
    have leftValue : left.siteAt leftSlot = site := by
      change ((left.1.orderIsoOfFin rfl) leftSlot).1 = site
      have inverse := (left.1.orderIsoOfFin rfl).apply_symm_apply ⟨site, memberLeft⟩
      exact congrArg Subtype.val inverse
    have corresponding := delimiterEncoding_siteAt_eq equalEncoding leftSlot
    have rightMember : right.siteAt rightSlot ∈ right.1 :=
      ((right.1.orderIsoOfFin rfl) rightSlot).2
    rw [leftValue] at corresponding
    rw [corresponding]
    simpa [rightSlot] using rightMember
  · intro memberRight
    let rightSlot : Fin right.1.card :=
      (right.1.orderIsoOfFin rfl).symm ⟨site, memberRight⟩
    let leftSlot : Fin left.1.card := Fin.cast cardEqual.symm rightSlot
    have rightValue : right.siteAt rightSlot = site := by
      change ((right.1.orderIsoOfFin rfl) rightSlot).1 = site
      have inverse := (right.1.orderIsoOfFin rfl).apply_symm_apply ⟨site, memberRight⟩
      exact congrArg Subtype.val inverse
    have corresponding := delimiterEncoding_siteAt_eq equalEncoding leftSlot
    have castBack : Fin.cast cardEqual leftSlot = rightSlot := by
      apply Fin.ext
      rfl
    rw [castBack, rightValue] at corresponding
    have leftMember : left.siteAt leftSlot ∈ left.1 :=
      ((left.1.orderIsoOfFin rfl) leftSlot).2
    rw [corresponding] at leftMember
    exact leftMember

/-- bit列がある合法delimiter符号であることを表す述語。 -/
def IsLegalDelimiter {p : QParameters} (bits : RegisterBasis p.systemWidth) : Prop :=
  ∃ configuration : QConfiguration p, delimiterEncoding configuration = bits

/-- 符号化した合法配置は合法delimiter述語を満たす。 -/
theorem delimiterEncoding_isLegal {p : QParameters} (configuration : QConfiguration p) :
    IsLegalDelimiter (delimiterEncoding configuration) :=
  ⟨configuration, rfl⟩

noncomputable section

/-- 物理bit列が合法delimiter符号なら対応配置を返し、不合法なら`none`を返す。 -/
def decodeDelimiter {p : QParameters} (bits : RegisterBasis p.systemWidth) :
    Option (QConfiguration p) := by
  classical
  exact if legal : IsLegalDelimiter bits then
      some (Classical.choose legal)
    else
      none

/-- 合法配置を符号化してdecodeすると元の配置へ厳密に戻る。 -/
@[simp] theorem decodeDelimiter_encoding
    {p : QParameters} (configuration : QConfiguration p) :
    decodeDelimiter (delimiterEncoding configuration) = some configuration := by
  classical
  rw [decodeDelimiter, dif_pos (delimiterEncoding_isLegal configuration)]
  congr 1
  apply delimiterEncoding_injective
  exact Classical.choose_spec (delimiterEncoding_isLegal configuration)

/-- decoderが値を返したとき、その再符号化は入力bit列に一致する。 -/
theorem decodeDelimiter_eq_some_iff
    {p : QParameters} {bits : RegisterBasis p.systemWidth}
    {configuration : QConfiguration p} :
    decodeDelimiter bits = some configuration ↔
      delimiterEncoding configuration = bits := by
  classical
  constructor
  · intro decoded
    unfold decodeDelimiter at decoded
    split at decoded
    · rename_i legal
      simp only [Option.some.injEq] at decoded
      subst configuration
      exact Classical.choose_spec legal
    · simp at decoded
  · intro encoded
    subst bits
    exact decodeDelimiter_encoding configuration

/-- decoderが`none`を返すことと、bit列が不合法であることは同値である。 -/
theorem decodeDelimiter_eq_none_iff
    {p : QParameters} {bits : RegisterBasis p.systemWidth} :
    decodeDelimiter bits = none ↔ ¬IsLegalDelimiter bits := by
  classical
  unfold decodeDelimiter
  split <;> simp_all

end

end ProbabilityGeneratorQProof
