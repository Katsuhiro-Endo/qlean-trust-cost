import QLean.Generator.Implementation.QOracleEndToEnd

/-!
# compact decoder の合法性完全性

compact decoder が基底上で受理する Bool 条件を明示し、その条件が delimiter 符号の
存在と同値であることを示す。証明は可変幅の行列を展開せず、Bool 列と有限集合だけを
扱う。
-/

namespace ProbabilityGeneratorQProof

open QParameters

namespace ReversibleCircuit

/-- 任意の物理 bit 列に対して compact decoder が計算する degree bit 列。 -/
def decoderDegreeBits (p : QParameters) (bits : List Bool) : List Bool :=
  degreeBoundaryBits p.wordWidth bits (suffixOrBits bits) 0
    (List.replicate p.K false)

/-- 任意の物理 bit 列に対して compact decoder が計算する隣接比較の good bit 列。 -/
def decoderGoodBits (p : QParameters) (bits : List Bool) : List Bool :=
  decoderExpectedGoodBits (decoderDegreeBits p bits) 0
    (splitBitWords p.wordWidth p.K bits)

/-- compact decoder が純粋 Bool 意味論で受理する条件。 -/
def DecoderAccepts (p : QParameters) (bits : List Bool) : Prop :=
  boolParity (decoderDegreeBits p bits) = true ∧
    (decoderGoodBits p bits).all id = true

/-- 合法 delimiter 符号の degree bit 列は粒子数 one-hot に一致する。 -/
theorem decoderDegreeBits_delimiterEncoding
    {p : QParameters} (configuration : QConfiguration p) :
    decoderDegreeBits p (registerBitList (delimiterEncoding configuration)) =
      degreeOneHotFrom p.K configuration.1.card 0 := by
  exact degreeBoundaryBits_delimiterEncoding_oneHot configuration p.K 0

/-- 合法 delimiter 符号の good bit 列はすべて真である。 -/
theorem decoderGoodBits_delimiterEncoding
    {p : QParameters} (configuration : QConfiguration p) :
    decoderGoodBits p (registerBitList (delimiterEncoding configuration)) =
      List.replicate (p.K - 1) true := by
  rw [decoderGoodBits, decoderDegreeBits_delimiterEncoding]
  exact decoderExpectedGoodBits_delimiterEncoding configuration

/-- 合法 delimiter 符号は純粋 decoder 述語に受理される。 -/
theorem decoderAccepts_delimiterEncoding
    {p : QParameters} (configuration : QConfiguration p) :
    DecoderAccepts p (registerBitList (delimiterEncoding configuration)) := by
  constructor
  · rw [decoderDegreeBits_delimiterEncoding]
    exact boolParity_degreeOneHot_configuration configuration
  · rw [decoderGoodBits_delimiterEncoding]
    simp

/-- 全 bit が一致する有限 register 基底は等しい。 -/
theorem registerBasis_eq_of_registerBitList_eq
    {width : Nat} {left right : RegisterBasis width}
    (equalBits : registerBitList left = registerBitList right) :
    left = right := by
  funext index
  have valueEqual := congrArg (fun bits => bits[index.val]?) equalBits
  simpa [registerBitList, index.isLt] using valueEqual

/-- Bool word を同じ幅の有限 site に復号する。 -/
def siteOfWord (p : QParameters) (word : List Bool)
    (length_eq : word.length = p.wordWidth) : QSite p :=
  ⟨littleEndianNat word, by
    rw [siteCapacity_eq, ← length_eq]
    exact littleEndianNat_lt_pow word⟩

/-- 復号した site の番号は元 word の little-endian 値である。 -/
@[simp] theorem siteOfWord_val (p : QParameters) (word : List Bool)
    (length_eq : word.length = p.wordWidth) :
    (siteOfWord p word length_eq).val = littleEndianNat word := rfl

/-- 復号した site を再び bit 列へ戻すと元 word に一致する。 -/
theorem siteBits_siteOfWord (p : QParameters) (word : List Bool)
    (length_eq : word.length = p.wordWidth) :
    List.ofFn (fun bit => siteBit p (siteOfWord p word length_eq) bit) = word := by
  apply littleEndianNat_injective_of_length_eq
  · simpa using length_eq.symm
  · rw [littleEndianNat_siteBits, siteOfWord_val]

/-- 指定した粒子数の one-hot degree 列の suffix parity は active 境界を判定する。 -/
theorem degreeOneHot_suffixParity
    (count particleCount slot : Nat) (slotBound : slot ≤ count)
    (particleBound : particleCount ≤ count) :
    boolParity ((degreeOneHotFrom count particleCount 0).drop slot) =
      decide (slot < particleCount) := by
  rw [boolParity_degreeOneHotFrom_drop count particleCount 0 slot]
  · simp [particleBound]
  · exact slotBound

/-- parity が真なら Bool 列には少なくとも一個の真が含まれる。 -/
theorem true_mem_of_boolParity_eq_true (bits : List Bool)
    (parity : boolParity bits = true) : true ∈ bits := by
  induction bits with
  | nil => simp [boolParity] at parity
  | cons bit bits inductionHypothesis =>
      cases bit
      · simp only [boolParity] at parity
        exact List.mem_cons_of_mem false (inductionHypothesis parity)
      · simp

/-- clean な全0 degree 列から真の境界 bit が出たなら、その境界番号を取り出せる。 -/
theorem true_mem_degreeBoundaryBits_replicate_false
    (wordWidth : Nat) (inputBits suffixBits : List Bool) (degree count : Nat)
    (member : true ∈ degreeBoundaryBits wordWidth inputBits suffixBits degree
      (List.replicate count false)) :
    ∃ offset < count,
      degreeBoundaryBit wordWidth inputBits suffixBits (degree + offset) = true := by
  induction count generalizing degree with
  | zero => simp [degreeBoundaryBits] at member
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, degreeBoundaryBits]
        at member
      by_cases boundary : degreeBoundaryBit wordWidth inputBits suffixBits degree = true
      · exact ⟨0, by omega, by simpa using boundary⟩
      · have tail : true ∈ degreeBoundaryBits wordWidth inputBits suffixBits
            (degree + 1) (List.replicate count false) := by
          simpa [boundary] using member
        rcases inductionHypothesis (degree + 1) tail with ⟨offset, offsetLt, value⟩
        exact ⟨offset + 1, by omega, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using value⟩

/-- 一個の真の degree 境界から、delimiter bit と後続全0という形を取り出す。 -/
theorem delimiterShape_of_degreeBoundaryBit
    (wordWidth : Nat) (bits : List Bool) (degree : Nat)
    (boundary : degreeBoundaryBit wordWidth bits (suffixOrBits bits) degree = true) :
    bits[wordWidth * (degree + 1)]?.getD false = true ∧
      (bits.drop (wordWidth * (degree + 1) + 1)).any id = false := by
  rw [degreeBoundaryBit_eq_getD, suffixOrBits_getD] at boundary
  simpa using boundary

/-- delimiter の形が決まれば、clean な degree 列はその位置の one-hot になる。 -/
theorem degreeBoundaryBits_eq_oneHot_of_shape
    (wordWidth bitsDegree count degree : Nat) (bits : List Bool)
    (wordWidthPositive : 0 < wordWidth)
    (delimiterValue : bits[wordWidth * bitsDegree]?.getD false = true)
    (afterDelimiterZero : (bits.drop (wordWidth * bitsDegree + 1)).any id = false) :
    degreeBoundaryBits wordWidth bits (suffixOrBits bits) degree
        (List.replicate count false) =
      degreeOneHotFrom count bitsDegree degree := by
  induction count generalizing degree with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, degreeBoundaryBits, degreeOneHotFrom,
        Bool.not_false]
      rw [degreeBoundaryBit_oneHot_of_delimiter wordWidth bitsDegree degree bits
        wordWidthPositive delimiterValue afterDelimiterZero]
      rw [inductionHypothesis (degree + 1)]
      cases decide (degree + 1 = bitsDegree) <;> rfl

/-- 要素がすべて真の Bool 列は同じ長さの真の反復列に等しい。 -/
theorem eq_replicate_true_of_all_eq_true (bits : List Bool)
    (allTrue : bits.all id = true) :
    bits = List.replicate bits.length true := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      simp only [List.all_cons, Bool.and_eq_true] at allTrue
      have bitTrue : bit = true := by simpa using allTrue.1
      subst bit
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
      exact inductionHypothesis allTrue.2

/-- `decoderExpectedGoodBits` は隣接 word ごとに一個の bit を返す。 -/
@[simp] theorem decoderExpectedGoodBits_length (degreeBits : List Bool) :
    ∀ (slot : Nat) (words : List (List Bool)),
      (decoderExpectedGoodBits degreeBits slot words).length = words.length - 1
  | _, [] => rfl
  | _, [_] => rfl
  | slot, left :: right :: words => by
      simp [decoderExpectedGoodBits,
        decoderExpectedGoodBits_length degreeBits (slot + 1) (right :: words)]

/-- one-hot degree の下で good 列が全真なら、必要な active word は狭義昇順である。 -/
theorem wordsStrictWhenRequired_of_expectedGood
    (degreeCount particleCount slot : Nat) (words : List (List Bool))
    (particleBound : particleCount ≤ degreeCount)
    (wordsFit : slot + words.length ≤ degreeCount)
    (allGood : decoderExpectedGoodBits
      (degreeOneHotFrom degreeCount particleCount 0) slot words =
        List.replicate (words.length - 1) true) :
    wordsStrictWhenRequired particleCount slot words := by
  induction words generalizing slot with
  | nil => trivial
  | cons left tail inductionHypothesis =>
      cases tail with
      | nil => trivial
      | cons right words =>
          have lengthDrop : (left :: right :: words).length - 1 =
              (right :: words).length := by simp
          rw [lengthDrop, show (right :: words).length = words.length + 1 by simp,
            List.replicate_succ] at allGood
          simp only [decoderExpectedGoodBits, List.cons.injEq] at allGood
          constructor
          · intro required
            have parity := degreeOneHot_suffixParity degreeCount particleCount
              (slot + 1) (by omega) particleBound
            rw [parity] at allGood
            simp [required] at allGood
            exact allGood.1
          · have tailFit : slot + 1 + (right :: words).length ≤ degreeCount := by
              simp only [List.length_cons] at wordsFit ⊢
              omega
            apply inductionHypothesis (slot + 1) tailFit
            simpa using allGood.2

/-- system 幅の Bool 列を分割した各 word は正確に `wordWidth` bit を持つ。 -/
theorem splitBitWords_word_length
    (wordWidth wordCount : Nat) (bits : List Bool)
    (bitsLength : bits.length = wordWidth * wordCount + 1)
    {word : List Bool}
    (member : word ∈ splitBitWords wordWidth wordCount bits) :
    word.length = wordWidth := by
  rcases List.mem_map.mp member with ⟨slot, slotMember, rfl⟩
  have slotLt : slot < wordCount := by simpa using slotMember
  rw [List.length_take]
  apply Nat.min_eq_left
  rw [List.length_drop, bitsLength]
  have blockLe : slot * wordWidth + wordWidth ≤ wordWidth * wordCount := by
    have := Nat.mul_le_mul_right wordWidth (Nat.succ_le_of_lt slotLt)
    simpa [Nat.succ_mul, Nat.mul_comm, Nat.add_comm] using this
  omega

/-- 任意長の Bool word をsite範囲へ剰余で埋め込む全域的な復号関数。 -/
def decodedSiteWord (p : QParameters) (word : List Bool) : QSite p :=
  ⟨littleEndianNat word % (p.G * p.G), Nat.mod_lt _ (by
    have gPositive : 0 < p.G := by simp [QParameters.G]
    exact Nat.mul_pos gPositive gPositive)⟩

/-- 正しい幅のwordでは全域的site復号の剰余は発生しない。 -/
theorem decodedSiteWord_val_of_length (p : QParameters) (word : List Bool)
    (length_eq : word.length = p.wordWidth) :
    (decodedSiteWord p word).val = littleEndianNat word := by
  apply Nat.mod_eq_of_lt
  rw [siteCapacity_eq, ← length_eq]
  exact littleEndianNat_lt_pow word

/-- 正しい幅のwordをsiteへ復号してbitへ戻すと元wordに一致する。 -/
theorem siteBits_decodedSiteWord (p : QParameters) (word : List Bool)
    (length_eq : word.length = p.wordWidth) :
    List.ofFn (fun bit => siteBit p (decodedSiteWord p word) bit) = word := by
  apply littleEndianNat_injective_of_length_eq
  · simpa using length_eq.symm
  · rw [littleEndianNat_siteBits, decodedSiteWord_val_of_length p word length_eq]

/-- active prefixの隣接狭義昇順条件は、その数値列の`IsChain`を与える。 -/
theorem wordsStrictWhenRequired_isChain_take
    (particleCount slot : Nat) (words : List (List Bool))
    (strict : wordsStrictWhenRequired particleCount slot words) :
    ((words.take (particleCount - slot)).map littleEndianNat).IsChain (· < ·) := by
  induction words generalizing slot with
  | nil => simp
  | cons left tail inductionHypothesis =>
      cases tail with
      | nil =>
          cases particleCount - slot <;> simp
      | cons right words =>
          by_cases required : slot + 1 < particleCount
          · have takeHead : particleCount - slot =
                (particleCount - (slot + 1)) + 1 := by omega
            rw [takeHead, List.take_succ_cons, List.map_cons]
            have tailChain := inductionHypothesis (slot + 1) strict.2
            have tailPositive : 0 < particleCount - (slot + 1) := by omega
            cases tailCount : particleCount - (slot + 1) with
            | zero => omega
            | succ count =>
                simp only [tailCount, List.take_succ_cons, List.map_cons,
                  List.isChain_cons_cons] at tailChain ⊢
                exact ⟨strict.1 required, tailChain⟩
          · by_cases active : slot < particleCount
            · have countOne : particleCount - slot = 1 := by omega
              simp [countOne]
            · have countZero : particleCount - slot = 0 := by omega
              simp [countZero]

/-- active prefixの数値的`IsChain`は推移性により全対の`Pairwise`狭義昇順になる。 -/
theorem wordsStrictWhenRequired_pairwise_take
    (particleCount slot : Nat) (words : List (List Bool))
    (strict : wordsStrictWhenRequired particleCount slot words) :
    ((words.take (particleCount - slot)).map littleEndianNat).Pairwise (· < ·) :=
  (wordsStrictWhenRequired_isChain_take particleCount slot words strict).pairwise

/-- system bit列の先頭`particleCount` wordを有限site列へ復号する。 -/
def activeDecodedSites (p : QParameters) (bits : List Bool)
    (particleCount : Nat) : List (QSite p) :=
  ((splitBitWords p.wordWidth p.K bits).take particleCount).map
    (decodedSiteWord p)

/-- `particleCount ≤ K`なら復号したactive site列の長さは粒子数に一致する。 -/
theorem activeDecodedSites_length (p : QParameters) (bits : List Bool)
    (particleCount : Nat) (particleBound : particleCount ≤ p.K) :
    (activeDecodedSites p bits particleCount).length = particleCount := by
  simp [activeDecodedSites, splitBitWords, particleBound]

/-- 正しいsystem幅から切り出したactive site列は、strict word列なら狭義昇順である。 -/
theorem activeDecodedSites_pairwise
    (p : QParameters) (bits : List Bool) (particleCount : Nat)
    (bitsLength : bits.length = p.systemWidth)
    (strict : wordsStrictWhenRequired particleCount 0
      (splitBitWords p.wordWidth p.K bits)) :
    (activeDecodedSites p bits particleCount).Pairwise (· < ·) := by
  let words := splitBitWords p.wordWidth p.K bits
  have numericPairwise :
      ((words.take particleCount).map littleEndianNat).Pairwise (· < ·) := by
    simpa [words] using
      wordsStrictWhenRequired_pairwise_take particleCount 0 words strict
  have wordPairwise : (words.take particleCount).Pairwise
      (fun left right => littleEndianNat left < littleEndianNat right) := by
    simpa only [List.pairwise_map] using numericPairwise
  rw [activeDecodedSites]
  simp only [List.pairwise_map]
  apply wordPairwise.imp_of_mem
  intro left right leftInPrefix rightInPrefix ordered
  have leftMember : left ∈ words := by
    exact List.mem_of_mem_take leftInPrefix
  have rightMember : right ∈ words := by
    exact List.mem_of_mem_take rightInPrefix
  have leftLength : left.length = p.wordWidth := by
    apply splitBitWords_word_length p.wordWidth p.K bits
    · simpa [QParameters.systemWidth] using bitsLength
    · simpa [words] using leftMember
  have rightLength : right.length = p.wordWidth := by
    apply splitBitWords_word_length p.wordWidth p.K bits
    · simpa [QParameters.systemWidth] using bitsLength
    · simpa [words] using rightMember
  change (decodedSiteWord p left).val < (decodedSiteWord p right).val
  rw [decodedSiteWord_val_of_length p left leftLength,
    decodedSiteWord_val_of_length p right rightLength]
  exact ordered

/-- 狭義昇順なsite列は重複を持たない。 -/
theorem nodup_of_pairwise_lt {α : Type} [Preorder α]
    (sites : List α) (ordered : sites.Pairwise (· < ·)) : sites.Nodup := by
  exact ordered.imp (fun less => ne_of_lt less)

/-- 昇順site列から、同じ要素を持つ合法配置を構成する。 -/
def configurationFromSites {p : QParameters} (sites : List (QSite p))
    (nonempty : 1 ≤ sites.length) (withinCapacity : sites.length ≤ p.K)
    (nodup : sites.Nodup) : QConfiguration p :=
  ⟨sites.toFinset, by
    rw [List.toFinset_card_of_nodup nodup]
    exact ⟨nonempty, withinCapacity⟩⟩

/-- site列から構成した配置の粒子数は元の列長に一致する。 -/
@[simp] theorem configurationFromSites_card {p : QParameters}
    (sites : List (QSite p)) (nonempty : 1 ≤ sites.length)
    (withinCapacity : sites.length ≤ p.K) (nodup : sites.Nodup) :
    (configurationFromSites sites nonempty withinCapacity nodup).1.card =
      sites.length := by
  exact List.toFinset_card_of_nodup nodup

/-- 狭義昇順site列から作った配置の昇順slot参照は元の列参照に一致する。 -/
theorem configurationFromSites_siteAt {p : QParameters}
    (sites : List (QSite p)) (nonempty : 1 ≤ sites.length)
    (withinCapacity : sites.length ≤ p.K) (nodup : sites.Nodup)
    (ordered : sites.Pairwise (· < ·))
    (slot : Fin (configurationFromSites sites nonempty withinCapacity nodup).1.card) :
    (configurationFromSites sites nonempty withinCapacity nodup).siteAt slot =
      sites.get ⟨slot.val, by
        simpa using slot.isLt⟩ := by
  let configuration := configurationFromSites sites nonempty withinCapacity nodup
  change Fin sites.toFinset.card at slot
  change ((sites.toFinset.orderIsoOfFin rfl) slot).1 = _
  rw [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  have weakOrdered : sites.Pairwise (· ≤ ·) :=
    ordered.imp (fun less => le_of_lt less)
  have sortEqual : sites.toFinset.sort (· ≤ ·) = sites :=
    (List.toFinset_sort (· ≤ ·) nodup).2 weakOrdered
  simp [sortEqual]

/-- active site列の有限添字参照は対応する分割wordのsite復号に一致する。 -/
theorem activeDecodedSites_get (p : QParameters) (bits : List Bool)
    (particleCount : Nat) (particleBound : particleCount ≤ p.K)
    (slot : Fin particleCount) :
    (activeDecodedSites p bits particleCount).get
        ⟨slot.val, by
          rw [activeDecodedSites_length p bits particleCount particleBound]
          exact slot.isLt⟩ =
      decodedSiteWord p
        ((splitBitWords p.wordWidth p.K bits).get
          ⟨slot.val, by
            simpa [splitBitWords] using lt_of_lt_of_le slot.isLt particleBound⟩) := by
  simp [activeDecodedSites]

/-- 正しい幅の復号wordについて、一bitの読出しも元wordの同じ位置に一致する。 -/
theorem siteBit_decodedSiteWord (p : QParameters) (word : List Bool)
    (length_eq : word.length = p.wordWidth) (bit : Fin p.wordWidth) :
    siteBit p (decodedSiteWord p word) bit = word[bit.val]?.getD false := by
  have equalWords := siteBits_decodedSiteWord p word length_eq
  have equalBit := congrArg (fun bits => bits[bit.val]?) equalWords
  simpa [bit.isLt] using congrArg (fun value => value.getD false) equalBit

/-- suffixの論理和が偽なら、そのsuffix内の各物理bitも偽である。 -/
theorem getD_false_of_any_drop_false (bits : List Bool) (start index : Nat)
    (after : start ≤ index) (allZero : (bits.drop start).any id = false) :
    bits[index]?.getD false = false := by
  cases value : bits[index]?.getD false with
  | false => rfl
  | true =>
      have laterTrue := any_drop_eq_true_of_le_getD bits start index after value
      rw [allZero] at laterTrue
      contradiction

/-- delimiter形とstrict active wordsから作った配置は、元の各物理bitを再現する。 -/
theorem delimiterEncoding_configurationFromActiveSites_bit
    (p : QParameters) (bits : List Bool) (particleCount : Nat)
    (bitsLength : bits.length = p.systemWidth)
    (particlePositive : 1 ≤ particleCount)
    (particleBound : particleCount ≤ p.K)
    (delimiterValue : bits[p.wordWidth * particleCount]?.getD false = true)
    (afterDelimiterZero :
      (bits.drop (p.wordWidth * particleCount + 1)).any id = false)
    (strict : wordsStrictWhenRequired particleCount 0
      (splitBitWords p.wordWidth p.K bits))
    (physical : Fin p.systemWidth) :
    let sites := activeDecodedSites p bits particleCount
    let ordered := activeDecodedSites_pairwise p bits particleCount bitsLength strict
    let nodup := nodup_of_pairwise_lt sites ordered
    let configuration := configurationFromSites sites
      (by rw [activeDecodedSites_length p bits particleCount particleBound]
          exact particlePositive)
      (by rw [activeDecodedSites_length p bits particleCount particleBound]
          exact particleBound)
      nodup
    delimiterEncoding configuration physical =
      bits[physical.val]?.getD false := by
  dsimp only
  let sites := activeDecodedSites p bits particleCount
  have sitesLength : sites.length = particleCount := by
    exact activeDecodedSites_length p bits particleCount particleBound
  have ordered : sites.Pairwise (· < ·) := by
    exact activeDecodedSites_pairwise p bits particleCount bitsLength strict
  have nodup : sites.Nodup := nodup_of_pairwise_lt sites ordered
  have sitesNonempty : 1 ≤ sites.length := by omega
  have sitesBound : sites.length ≤ p.K := by omega
  let configuration := configurationFromSites sites sitesNonempty sitesBound nodup
  have configurationCard : configuration.1.card = particleCount := by
    rw [show configuration.1.card = sites.length by
      simp [configuration]]
    exact sitesLength
  change delimiterEncoding configuration physical = bits[physical.val]?.getD false
  by_cases before : physical.val < p.wordWidth * particleCount
  · simp only [delimiterEncoding, configurationCard, before, dif_pos]
    let slot : Fin particleCount :=
      ⟨physical.val / p.wordWidth,
        (Nat.div_lt_iff_lt_mul (by simp [QParameters.wordWidth, p.q_pos])).2
          (by simpa [Nat.mul_comm] using before)⟩
    let wordBit : Fin p.wordWidth :=
      ⟨physical.val % p.wordWidth,
        Nat.mod_lt _ (by simp [QParameters.wordWidth, p.q_pos])⟩
    let configurationSlot : Fin configuration.1.card :=
      ⟨slot.val, by simp [configurationCard, slot.isLt]⟩
    have siteValue : configuration.siteAt configurationSlot =
        decodedSiteWord p
          ((splitBitWords p.wordWidth p.K bits).get
            ⟨slot.val, by
              simpa [splitBitWords] using
                lt_of_lt_of_le slot.isLt particleBound⟩) := by
      rw [configurationFromSites_siteAt sites sitesNonempty sitesBound nodup ordered]
      simpa [sites, configurationSlot] using
        activeDecodedSites_get p bits particleCount particleBound slot
    change siteBit p (configuration.siteAt configurationSlot) wordBit =
      bits[physical.val]?.getD false
    rw [siteValue]
    let word := (splitBitWords p.wordWidth p.K bits).get
      ⟨slot.val, by simpa [splitBitWords] using
        lt_of_lt_of_le slot.isLt particleBound⟩
    have wordMember : word ∈ splitBitWords p.wordWidth p.K bits :=
      List.get_mem _ _
    have wordLength : word.length = p.wordWidth := by
      exact splitBitWords_word_length p.wordWidth p.K bits
        (by simpa [QParameters.systemWidth] using bitsLength) wordMember
    rw [siteBit_decodedSiteWord p word wordLength wordBit]
    have wordEqual : word =
        (bits.drop (slot.val * p.wordWidth)).take p.wordWidth := by
      simp [word, splitBitWords]
    rw [wordEqual]
    rw [List.getElem?_take, if_pos wordBit.isLt, List.getElem?_drop]
    rw [show slot.val * p.wordWidth + wordBit.val = physical.val by
      simp [slot, wordBit, Nat.mul_comm, Nat.div_add_mod]]
  · simp only [delimiterEncoding, configurationCard, before]
    by_cases atDelimiter : physical.val = p.wordWidth * particleCount
    · simp [atDelimiter, delimiterValue]
    · have after : p.wordWidth * particleCount + 1 ≤ physical.val := by omega
      have valueZero := getD_false_of_any_drop_false bits
        (p.wordWidth * particleCount + 1) physical.val after afterDelimiterZero
      simp [atDelimiter, valueZero]

/-- delimiter形とstrict active wordsを満たす有限register基底は合法delimiter符号である。 -/
theorem isLegalDelimiter_of_shape_and_strict
    (p : QParameters) (basis : RegisterBasis p.systemWidth)
    (particleCount : Nat) (particlePositive : 1 ≤ particleCount)
    (particleBound : particleCount ≤ p.K)
    (delimiterValue :
      (registerBitList basis)[p.wordWidth * particleCount]?.getD false = true)
    (afterDelimiterZero :
      ((registerBitList basis).drop
        (p.wordWidth * particleCount + 1)).any id = false)
    (strict : wordsStrictWhenRequired particleCount 0
      (splitBitWords p.wordWidth p.K (registerBitList basis))) :
    IsLegalDelimiter basis := by
  let bits := registerBitList basis
  have bitsLength : bits.length = p.systemWidth := by simp [bits, registerBitList]
  let sites := activeDecodedSites p bits particleCount
  have sitesLength : sites.length = particleCount :=
    activeDecodedSites_length p bits particleCount particleBound
  have ordered : sites.Pairwise (· < ·) :=
    activeDecodedSites_pairwise p bits particleCount bitsLength strict
  have nodup : sites.Nodup := nodup_of_pairwise_lt sites ordered
  have sitesNonempty : 1 ≤ sites.length := by omega
  have sitesBound : sites.length ≤ p.K := by omega
  let configuration := configurationFromSites sites sitesNonempty sitesBound nodup
  refine ⟨configuration, ?_⟩
  funext physical
  have bitEqual := delimiterEncoding_configurationFromActiveSites_bit p bits
    particleCount bitsLength particlePositive particleBound delimiterValue
    afterDelimiterZero strict physical
  rw [registerBitList_getD basis physical.val, dif_pos physical.isLt] at bitEqual
  exact bitEqual

/-- 純粋decoderが受理する任意のsystem基底は、ある合法配置のdelimiter符号である。 -/
theorem isLegalDelimiter_of_decoderAccepts
    (p : QParameters) (basis : RegisterBasis p.systemWidth)
    (accepted : DecoderAccepts p (registerBitList basis)) :
    IsLegalDelimiter basis := by
  let bits := registerBitList basis
  have bitsLength : bits.length = p.systemWidth := by simp [bits, registerBitList]
  have degreeParity : boolParity (decoderDegreeBits p bits) = true := accepted.1
  have degreeMember : true ∈ decoderDegreeBits p bits :=
    true_mem_of_boolParity_eq_true (decoderDegreeBits p bits) degreeParity
  rcases true_mem_degreeBoundaryBits_replicate_false p.wordWidth bits
      (suffixOrBits bits) 0 p.K degreeMember with
    ⟨offset, offsetLt, boundary⟩
  let particleCount := offset + 1
  have particlePositive : 1 ≤ particleCount := by omega
  have particleBound : particleCount ≤ p.K := by omega
  have shape := delimiterShape_of_degreeBoundaryBit p.wordWidth bits offset
    (by simpa using boundary)
  have delimiterValue :
      bits[p.wordWidth * particleCount]?.getD false = true := by
    simpa [particleCount] using shape.1
  have afterDelimiterZero :
      (bits.drop (p.wordWidth * particleCount + 1)).any id = false := by
    simpa [particleCount] using shape.2
  have degreeEqual : decoderDegreeBits p bits =
      degreeOneHotFrom p.K particleCount 0 := by
    exact degreeBoundaryBits_eq_oneHot_of_shape p.wordWidth particleCount p.K 0
      bits (by simp [QParameters.wordWidth, p.q_pos]) delimiterValue
      afterDelimiterZero
  have goodAll : (decoderGoodBits p bits).all id = true := accepted.2
  have goodReplicate : decoderGoodBits p bits =
      List.replicate (p.K - 1) true := by
    have allResult := eq_replicate_true_of_all_eq_true (decoderGoodBits p bits) goodAll
    simpa [decoderGoodBits, splitBitWords] using allResult
  have expectedGood :
      decoderExpectedGoodBits (degreeOneHotFrom p.K particleCount 0) 0
          (splitBitWords p.wordWidth p.K bits) =
        List.replicate (p.K - 1) true := by
    simpa [decoderGoodBits, degreeEqual] using goodReplicate
  have strict : wordsStrictWhenRequired particleCount 0
      (splitBitWords p.wordWidth p.K bits) := by
    apply wordsStrictWhenRequired_of_expectedGood p.K particleCount 0
      (splitBitWords p.wordWidth p.K bits) particleBound
    · simp [splitBitWords]
    · simpa [splitBitWords] using expectedGood
  exact isLegalDelimiter_of_shape_and_strict p basis particleCount
    particlePositive particleBound (by simpa [bits] using delimiterValue)
    (by simpa [bits] using afterDelimiterZero) (by simpa [bits] using strict)

/-- 純粋compact decoderの受理条件は合法delimiter述語と完全に同値である。 -/
theorem decoderAccepts_iff_isLegalDelimiter
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    DecoderAccepts p (registerBitList basis) ↔ IsLegalDelimiter basis := by
  constructor
  · exact isLegalDelimiter_of_decoderAccepts p basis
  · rintro ⟨configuration, encoded⟩
    subst basis
    exact decoderAccepts_delimiterEncoding configuration

/-- 任意system基底のdegree decode出力は純粋な`decoderDegreeBits`に一致する。 -/
theorem readWires_degreeDecode_system_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input
    readWires (oracleDegreeWires p) decoded =
      decoderDegreeBits p (registerBitList basis) := by
  dsimp only
  have result := readWires_xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p)
    (decoderSuffixWires p) (oracleDegreeWires p) (zeroAncillaJointBasis p basis)
    (by simp) (systemWires_disjoint_decoderSuffix p)
    (systemWires_disjoint_degree p)
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p) (oracleDegreeWires_nodup p)
    (readWires_decoderSuffix_zeroAncilla p basis)
    (readWires_oracleDegree_zeroAncilla p basis)
  simpa [decoderDegreeBits, readWires_systemWires_zeroAncilla p basis] using result

/-- 任意system基底のdegree decode後も比較workは全0である。 -/
theorem oracleCompare_zero_after_degreeDecode_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input
    ∀ wire ∈ oracleCompareWorkWires p, decoded wire = false := by
  dsimp only
  intro wire member
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth (systemWires p)
    (decoderSuffixWires p) (oracleDegreeWires p) wire
    (zeroAncillaJointBasis p basis) (by simp)
    (systemWires_disjoint_decoderSuffix p) (systemWires_disjoint_degree p)
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p)]
  · rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl
  · exact (List.disjoint_left.mp (systemWires_disjoint_compareWork p).symm member)
  · exact (List.disjoint_left.mp
      (decoderSuffixWires_disjoint_compareWork p).symm member)
  · exact (List.disjoint_left.mp
      (oracleDegreeWires_disjoint_compareWork p).symm member)

/-- 任意system基底のdegree decode後もAND workは全0である。 -/
theorem oracleAndWork_zero_after_degreeDecode_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input
    ∀ wire ∈ oracleAndWorkWires p, decoded wire = false := by
  dsimp only
  intro wire member
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth (systemWires p)
    (decoderSuffixWires p) (oracleDegreeWires p) wire
    (zeroAncillaJointBasis p basis) (by simp)
    (systemWires_disjoint_decoderSuffix p) (systemWires_disjoint_degree p)
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p)]
  · exact zeroAncilla_oracleAndWork_member p basis member
  · exact (List.disjoint_left.mp (systemWires_disjoint_andWork p).symm member)
  · exact (List.disjoint_left.mp
      (decoderSuffixWires_disjoint_andWork p).symm member)
  · exact (List.disjoint_left.mp
      (oracleDegreeWires_disjoint_andWork p).symm member)

/-- 任意system基底のdegree-valid回路はdegree parityだけを標的へXORする。 -/
theorem decoderDegreeValid_after_degreeDecode_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded =
      if boolParity (decoderDegreeBits p (registerBitList basis)) then
        xBasisAction (decoderDegreeValidWire p) decoded
      else decoded := by
  dsimp only
  have targetAbsent : decoderDegreeValidWire p ∉ oracleDegreeWires p := by
    intro member
    exact (List.disjoint_left.mp (oracleDegreeWires_disjoint_andWork p) member)
      (decoderDegreeValid_mem_andWork p)
  rw [show decoderDegreeValidCircuit (oracleDegreeWires p)
      (decoderDegreeValidWire p) =
      xorSourceParityIntoTargetCircuit (oracleDegreeWires p) (decoderDegreeValidWire p) by rfl]
  rw [runBasis_xorSourceParityIntoTargetCircuit (oracleDegreeWires p)
    (decoderDegreeValidWire p) _ targetAbsent]
  rw [readWires_degreeDecode_system_basis p basis]

/-- 任意system基底の実比較列は純粋な`decoderGoodBits`を出力する。 -/
theorem decoderComparison_good_after_degreeDecode_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    readWires (decoderGoodWires p)
        ((decoderComparisonSequence degree (oracleCompareWorkWires p)
          (decoderAndScratchWires p) 0 words (decoderLessWires p)
          (decoderNeedWires p) (decoderGoodWires p)).runBasis
          reversibleGatePermutation decoded) =
      decoderGoodBits p (registerBitList basis) := by
  dsimp only
  let input := zeroAncillaJointBasis p basis
  let inputWires := systemWires p
  let suffix := decoderSuffixWires p
  let degree := oracleDegreeWires p
  let compare := oracleCompareWorkWires p
  let scratch := decoderAndScratchWires p
  let words := splitSystemWords p.wordWidth p.K inputWires
  let less := decoderLessWires p
  let need := decoderNeedWires p
  let good := decoderGoodWires p
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires suffix degree).runBasis
      reversibleGatePermutation input
  have inputDisjointSuffix : inputWires.Disjoint suffix := by
    simpa [inputWires, suffix] using systemWires_disjoint_decoderSuffix p
  have inputDisjointDegree : inputWires.Disjoint degree := by
    simpa [inputWires, degree] using systemWires_disjoint_degree p
  have suffixDisjointDegree : suffix.Disjoint degree := by
    simpa [suffix, degree] using
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
  have sameLength : inputWires.length = suffix.length := by simp [inputWires, suffix]
  have degreeValues : readWires degree decoded =
      decoderDegreeBits p (registerBitList basis) := by
    simpa [degree, decoded, input, inputWires, suffix] using
      readWires_degreeDecode_system_basis p basis
  have wordValues : words.map (fun word => readWires word decoded) =
      splitBitWords p.wordWidth p.K (registerBitList basis) := by
    calc
      words.map (fun word => readWires word decoded) =
          words.map (fun word => readWires word input) := by
        apply List.map_congr_left
        intro word wordMember
        apply List.map_congr_left
        intro wire wireMember
        apply runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_input_wire p.wordWidth inputWires suffix
          degree wire input inputDisjointSuffix inputDisjointDegree
          suffixDisjointDegree
        rcases List.mem_map.mp wordMember with ⟨slot, _, rfl⟩
        exact List.mem_of_mem_drop (List.mem_of_mem_take wireMember)
      _ = splitBitWords p.wordWidth p.K (registerBitList basis) := by
        simpa [words, inputWires, input] using
          readWires_splitSystemWords_system_zeroAncilla p basis
  have compareAfterZero : ∀ wire ∈ compare, decoded wire = false := by
    simpa [compare, decoded, degree, input] using
      oracleCompare_zero_after_degreeDecode_basis p basis
  have andAfterZero : ∀ wire ∈ oracleAndWorkWires p, decoded wire = false := by
    simpa [decoded, degree, input] using
      oracleAndWork_zero_after_degreeDecode_basis p basis
  have compareZero : readWires compare decoded =
      List.replicate compare.length false :=
    readWires_eq_replicate_false_of_forall compare decoded compareAfterZero
  have scratchZero : ∀ wire ∈ scratch, decoded wire = false := by
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p (by simp [scratch, member]))
  have lessZero : readWires less decoded = List.replicate less.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p
      (by simp [less, decoderComparisonFlagWires, member]))
  have needZero : readWires need decoded = List.replicate need.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p
      (by simp [need, decoderComparisonFlagWires, member]))
  have goodZero : readWires good decoded = List.replicate good.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p
      (by simp [good, decoderComparisonFlagWires, member]))
  have wordCount : words.length = good.length + 1 := by
    simp [words, good, inputWires, splitSystemWords]
    have := p.K_pos
    omega
  have lessCount : less.length = good.length := by simp [less, good]
  have needCount : need.length = good.length := by simp [need, good]
  have wordLengths : ∀ word ∈ words, word.length = compare.length := by
    intro word member
    rw [show word.length = p.wordWidth by
      exact splitSystemWords_system_word_length p word
        (by simpa [words, inputWires] using member)]
    simp [compare]
  have supportNodup :
      (decoderComparisonSupport degree compare scratch words less need good).Nodup := by
    simpa [degree, compare, scratch, words, less, need, good, inputWires] using
      decoderComparisonSupport_system_nodup p
  have circuitGood := readWires_decoderComparisonSequence_good degree compare scratch
    0 words less need good decoded wordCount lessCount needCount wordLengths
    supportNodup compareZero scratchZero lessZero needZero goodZero
    (by simpa [compare, scratch] using decoderAndScratchWires_wordWidth_le p)
  calc
    readWires good
        ((decoderComparisonSequence degree compare scratch 0 words less need good).runBasis
          reversibleGatePermutation decoded) =
        decoderExpectedGoodBits (readWires degree decoded) 0
          (words.map fun word => readWires word decoded) := circuitGood
    _ = decoderGoodBits p (registerBitList basis) := by
      rw [degreeValues, wordValues]
      rfl

/-- 任意system基底の実比較列は共有AND scratchを全0へ戻す。 -/
theorem decoderComparison_scratch_clean_after_degreeDecode_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let compared :=
      (decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation decoded
    ∀ wire ∈ decoderAndScratchWires p, compared wire = false := by
  dsimp only
  let input := zeroAncillaJointBasis p basis
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let compare := oracleCompareWorkWires p
  let scratch := decoderAndScratchWires p
  let less := decoderLessWires p
  let need := decoderNeedWires p
  let good := decoderGoodWires p
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  have compareZero : readWires compare decoded =
      List.replicate compare.length false :=
    readWires_eq_replicate_false_of_forall compare decoded (by
      simpa [compare, decoded, degree, input] using
        oracleCompare_zero_after_degreeDecode_basis p basis)
  have andZero : ∀ wire ∈ oracleAndWorkWires p, decoded wire = false := by
    simpa [decoded, degree, input] using
      oracleAndWork_zero_after_degreeDecode_basis p basis
  have scratchZero : ∀ wire ∈ scratch, decoded wire = false := by
    intro wire member
    exact andZero wire (decoderComparisonAndMember p (by simp [scratch, member]))
  have lessZero : readWires less decoded = List.replicate less.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andZero wire (decoderComparisonAndMember p
      (by simp [less, decoderComparisonFlagWires, member]))
  have needZero : readWires need decoded = List.replicate need.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andZero wire (decoderComparisonAndMember p
      (by simp [need, decoderComparisonFlagWires, member]))
  have goodZero : readWires good decoded = List.replicate good.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andZero wire (decoderComparisonAndMember p
      (by simp [good, decoderComparisonFlagWires, member]))
  have wordCount : words.length = good.length + 1 := by
    simp [words, good, splitSystemWords]
    have := p.K_pos
    omega
  have lessCount : less.length = good.length := by simp [less, good]
  have needCount : need.length = good.length := by simp [need, good]
  have wordLengths : ∀ word ∈ words, word.length = compare.length := by
    intro word member
    rw [show word.length = p.wordWidth by
      exact splitSystemWords_system_word_length p word (by simpa [words] using member)]
    simp [compare]
  have supportNodup :
      (decoderComparisonSupport degree compare scratch words less need good).Nodup := by
    simpa [degree, compare, scratch, words, less, need, good] using
      decoderComparisonSupport_system_nodup p
  exact runBasis_decoderComparisonSequence_scratch_clean degree compare scratch 0
    words less need good decoded wordCount lessCount needCount wordLengths
    supportNodup compareZero scratchZero lessZero needZero goodZero
    (by simpa [compare, scratch] using decoderAndScratchWires_wordWidth_le p)

/-- degree-valid計算は任意基底でも比較回路のsupport上の結果を変えない。 -/
theorem decoderComparison_after_degreeValid_agrees_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
      (decoderAndScratchWires p) words (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p)
    let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
      (decoderAndScratchWires p) 0 words (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p)
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let degreePrepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    BasisAgreeOn support
      (comparison.runBasis reversibleGatePermutation degreePrepared)
      (comparison.runBasis reversibleGatePermutation decoded) := by
  dsimp only
  let input := zeroAncillaJointBasis p basis
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have preparedEq : degreePrepared =
      if boolParity (decoderDegreeBits p (registerBitList basis)) then
        xBasisAction (decoderDegreeValidWire p) decoded
      else decoded := by
    simpa [degreePrepared, decoded, degree, input] using
      decoderDegreeValid_after_degreeDecode_basis p basis
  have beforeAgree : BasisAgreeOn support degreePrepared decoded := by
    intro wire member
    rw [preparedEq]
    split
    · apply xBasisAction_other
      intro equal
      subst wire
      exact decoderDegreeValid_not_mem_comparisonSupport_system p (by
        simpa [support, degree, words] using member)
    · rfl
  apply Circuit.runBasis_congr_on_of_usesOnly support comparison
  · simpa [support, comparison, degree, words] using
      decoderComparisonSequence_usesOnly_system p
  · exact beforeAgree

/-- degree-valid計算後の任意基底でもgood列は純粋`decoderGoodBits`に一致する。 -/
theorem decoderComparison_good_after_degreeValid_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let degreePrepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    readWires (decoderGoodWires p)
      ((decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation degreePrepared) =
      decoderGoodBits p (registerBitList basis) := by
  dsimp only
  let input := zeroAncillaJointBasis p basis
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have agree : BasisAgreeOn support
      (comparison.runBasis reversibleGatePermutation degreePrepared)
      (comparison.runBasis reversibleGatePermutation decoded) := by
    simpa [support, comparison, degreePrepared, decoded, degree, words, input] using
      decoderComparison_after_degreeValid_agrees_basis p basis
  calc
    readWires (decoderGoodWires p)
        (comparison.runBasis reversibleGatePermutation degreePrepared) =
        readWires (decoderGoodWires p)
          (comparison.runBasis reversibleGatePermutation decoded) := by
      apply List.map_congr_left
      intro wire member
      exact agree wire (by simp [support, decoderComparisonSupport, member])
    _ = decoderGoodBits p (registerBitList basis) := by
      simpa [comparison, decoded, degree, words, input] using
        decoderComparison_good_after_degreeDecode_basis p basis

/-- degree-valid計算後の任意基底でも比較scratchは全0へ戻る。 -/
theorem decoderComparison_scratch_clean_after_degreeValid_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let degreePrepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    let compared :=
      (decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation degreePrepared
    ∀ wire ∈ decoderAndScratchWires p, compared wire = false := by
  dsimp only
  let input := zeroAncillaJointBasis p basis
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have agree : BasisAgreeOn support
      (comparison.runBasis reversibleGatePermutation degreePrepared)
      (comparison.runBasis reversibleGatePermutation decoded) := by
    simpa [support, comparison, degreePrepared, decoded, degree, words, input] using
      decoderComparison_after_degreeValid_agrees_basis p basis
  intro wire member
  calc
    comparison.runBasis reversibleGatePermutation degreePrepared wire =
        comparison.runBasis reversibleGatePermutation decoded wire :=
      agree wire (by simp [support, decoderComparisonSupport, member])
    _ = false := by
      exact decoderComparison_scratch_clean_after_degreeDecode_basis p basis
        wire member

/-- 比較後のdegree-valid wireは任意基底のdegree parityそのものである。 -/
theorem decoderDegreeValid_after_comparison_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let degreePrepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    let compared :=
      (decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation degreePrepared
    compared (decoderDegreeValidWire p) =
      boolParity (decoderDegreeBits p (registerBitList basis)) := by
  dsimp only
  let input := zeroAncillaJointBasis p basis
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have outside : decoderDegreeValidWire p ∉ support := by
    simpa [support, degree, words] using
      decoderDegreeValid_not_mem_comparisonSupport_system p
  rw [Circuit.runBasis_outside_of_usesOnly support comparison
    (by simpa [support, comparison, degree, words] using
      decoderComparisonSequence_usesOnly_system p) degreePrepared
    (decoderDegreeValidWire p) outside]
  have preparedEq : degreePrepared =
      if boolParity (decoderDegreeBits p (registerBitList basis)) then
        xBasisAction (decoderDegreeValidWire p) decoded
      else decoded := by
    simpa [degreePrepared, decoded, degree, input] using
      decoderDegreeValid_after_degreeDecode_basis p basis
  have decodedFalse : decoded (decoderDegreeValidWire p) = false := by
    exact oracleAndWork_zero_after_degreeDecode_basis p basis
      (decoderDegreeValidWire p) (decoderDegreeValid_mem_andWork p)
  rw [preparedEq]
  cases parity : boolParity (decoderDegreeBits p (registerBitList basis)) <;>
    simp [decodedFalse, xBasisAction_target]

/-- 任意system基底の合法性computeは純粋受理Boolをtemporary wireへ書く。 -/
theorem decoderLegalityCompute_temporary_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    (decoderLegalityCompute words degree (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p) (decoderDegreeValidWire p)
      (decoderLegalTemporaryWire p)).runBasis reversibleGatePermutation decoded
        (decoderLegalTemporaryWire p) =
      (boolParity (decoderDegreeBits p (registerBitList basis)) &&
        (decoderGoodBits p (registerBitList basis)).all id) := by
  dsimp only
  let input := zeroAncillaJointBasis p basis
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  let compared := comparison.runBasis reversibleGatePermutation degreePrepared
  let controls := decoderDegreeValidWire p :: decoderGoodWires p
  let scratch := decoderAndScratchWires p
  let target := decoderLegalTemporaryWire p
  change (positiveMultiControlledX controls scratch target).runBasis
    reversibleGatePermutation compared target = _
  have scratchZero : ∀ wire ∈ scratch, compared wire = false := by
    simpa [scratch, compared, comparison, degreePrepared, decoded, degree, words,
      input] using decoderComparison_scratch_clean_after_degreeValid_basis p basis
  rw [runBasis_positiveMultiControlledX controls scratch target compared
    (by simpa [controls, scratch] using decoderAllGood_enoughScratch p)
    (by simpa [controls, scratch, target] using decoderAllGood_layout_nodup p)
    scratchZero]
  have controlsValue : allWiresTrue controls compared =
      (boolParity (decoderDegreeBits p (registerBitList basis)) &&
        (decoderGoodBits p (registerBitList basis)).all id) := by
    have degreeValue : compared (decoderDegreeValidWire p) =
        boolParity (decoderDegreeBits p (registerBitList basis)) := by
      simpa [compared, comparison, degreePrepared, decoded, degree, words, input] using
        decoderDegreeValid_after_comparison_basis p basis
    have goodValue : readWires (decoderGoodWires p) compared =
        decoderGoodBits p (registerBitList basis) := by
      simpa [compared, comparison, degreePrepared, decoded, degree, words, input] using
        decoderComparison_good_after_degreeValid_basis p basis
    change (compared (decoderDegreeValidWire p) ::
      readWires (decoderGoodWires p) compared).all id = _
    rw [degreeValue, goodValue]
    rfl
  rw [controlsValue]
  have outsideTarget : target ∉ support := by
    simpa [target, support, degree, words] using
      decoderLegalTemporary_not_mem_comparisonSupport_system p
  have comparedTarget : compared target = degreePrepared target :=
    Circuit.runBasis_outside_of_usesOnly support comparison
      (by simpa [support, comparison, degree, words] using
        decoderComparisonSequence_usesOnly_system p)
      degreePrepared target outsideTarget
  have preparedEq : degreePrepared =
      if boolParity (decoderDegreeBits p (registerBitList basis)) then
        xBasisAction (decoderDegreeValidWire p) decoded
      else decoded := by
    simpa [degreePrepared, decoded, degree, input] using
      decoderDegreeValid_after_degreeDecode_basis p basis
  have targetNeDegree : target ≠ decoderDegreeValidWire p := by
    have fresh := (List.nodup_cons.mp (decoderAllGood_layout_nodup p)).1
    have degreeNeTarget :
        decoderDegreeValidWire p ≠ decoderLegalTemporaryWire p := by
      intro equal
      exact fresh (by simp [equal])
    simpa [target] using degreeNeTarget.symm
  have preparedTarget : degreePrepared target = decoded target := by
    rw [preparedEq]
    split
    · exact xBasisAction_other (decoderDegreeValidWire p) target
        targetNeDegree decoded
    · rfl
  have decodedTarget : decoded target = false := by
    exact oracleAndWork_zero_after_degreeDecode_basis p basis target
      (by simpa [target] using decoderLegalTemporary_mem_andWork p)
  cases acceptedValue :
      (boolParity (decoderDegreeBits p (registerBitList basis)) &&
        (decoderGoodBits p (registerBitList basis)).all id)
  · simp only [Bool.false_eq_true, if_false]
    rw [comparedTarget, preparedTarget, decodedTarget]
  · simp only [if_true, xBasisAction_target]
    rw [comparedTarget, preparedTarget, decodedTarget]
    rfl

/-- 正本compact decoderの保持用legal wireは純粋受理Boolと厳密に一致する。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_basis
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    let input := zeroAncillaJointBasis p basis
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
      reversibleGatePermutation input (oracleLegalWire p) =
      (boolParity (decoderDegreeBits p (registerBitList basis)) &&
        (decoderGoodBits p (registerBitList basis)).all id) := by
  dsimp only
  let input := zeroAncillaJointBasis p basis
  let degree := oracleDegreeWires p
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let compute := decoderLegalityCompute words degree (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p) (oracleCompareWorkWires p)
    (decoderAndScratchWires p) (decoderDegreeValidWire p)
    (decoderLegalTemporaryWire p)
  let use := safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)
  let support := decoderLegalitySupport p
  change (Circuit.computeUseUncompute id compute use).runBasis
    reversibleGatePermutation decoded (oracleLegalWire p) = _
  have computeUses : circuitUsesOnly support compute := by
    simpa [support, compute, words, degree] using decoderLegalityCompute_usesOnly_system p
  have legalOutside : oracleLegalWire p ∉ support := by
    simpa [support] using oracleLegal_not_mem_decoderLegalitySupport p
  have temporaryMember : decoderLegalTemporaryWire p ∈ support := by
    have andMember := decoderLegalTemporary_mem_andWork p
    simp [support, decoderLegalitySupport, andMember]
  have sourceDifferent : decoderLegalTemporaryWire p ≠ oracleLegalWire p := by
    intro equal
    apply legalOutside
    simpa [equal] using temporaryMember
  have usePreserves : BasisAgreeOn support
      (use.runBasis reversibleGatePermutation
        (compute.runBasis reversibleGatePermutation decoded))
      (compute.runBasis reversibleGatePermutation decoded) := by
    simpa [support, use] using decoderLegalityUse_preservesSupport p
      (compute.runBasis reversibleGatePermutation decoded)
  rw [Circuit.computeUseUncompute_local_clean support compute use decoded computeUses
    usePreserves]
  rw [restoreSupport_outside support decoded
    (use.runBasis reversibleGatePermutation
      (compute.runBasis reversibleGatePermutation decoded))
    (oracleLegalWire p) legalOutside]
  rw [show use = safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p) by rfl]
  rw [runBasis_safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)
    sourceDifferent]
  rw [cnotBasisAction_target]
  have temporaryValue : compute.runBasis reversibleGatePermutation decoded
      (decoderLegalTemporaryWire p) =
      (boolParity (decoderDegreeBits p (registerBitList basis)) &&
        (decoderGoodBits p (registerBitList basis)).all id) := by
    simpa [compute, decoded, degree, words, input] using
      decoderLegalityCompute_temporary_basis p basis
  have computedLegal : compute.runBasis reversibleGatePermutation decoded
      (oracleLegalWire p) = decoded (oracleLegalWire p) :=
    Circuit.runBasis_outside_of_usesOnly support compute computeUses decoded
      (oracleLegalWire p) legalOutside
  have decodedLegal : decoded (oracleLegalWire p) = false := by
    change
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input (oracleLegalWire p) = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth (systemWires p)
      (decoderSuffixWires p) degree (oracleLegalWire p) input (by simp)
      (systemWires_disjoint_decoderSuffix p) (systemWires_disjoint_degree p)
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
      (decoderSuffixWires_nodup p)]
    · rfl
    · intro member
      exact legalOutside (by simp [support, decoderLegalitySupport, member])
    · intro member
      exact legalOutside (by simp [support, decoderLegalitySupport, member])
    · intro member
      exact legalOutside (by simp [support, decoderLegalitySupport, degree, member])
  rw [temporaryValue, computedLegal, decodedLegal]
  cases boolParity (decoderDegreeBits p (registerBitList basis)) <;>
    cases (decoderGoodBits p (registerBitList basis)).all id <;> rfl

/-- 全0ancillaの任意system基底で、実legal wireが真であることと合法delimiterは同値である。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_iff_isLegalDelimiter
    (p : QParameters) (basis : RegisterBasis p.systemWidth) :
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
        reversibleGatePermutation (zeroAncillaJointBasis p basis)
        (oracleLegalWire p) = true ↔
      IsLegalDelimiter basis := by
  rw [xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_basis p basis]
  simpa [DecoderAccepts, Bool.and_eq_true] using
    decoderAccepts_iff_isLegalDelimiter p basis

end ReversibleCircuit

end ProbabilityGeneratorQProof
