import QLean.Generator.Implementation.QOracleEventReferenceBridge
import QLean.Generator.Implementation.QBitonicCircuitCorrectness

/-!
# 整列済み candidate の有限多重集合橋渡し

一般の有限関数について、値ごとの出現個数と昇順性から関数自体を一意に定める。
固定幅の全 word や全計算基底は列挙せず、`List.ofFn` の置換だけを用いる。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 有限関数の値出現個数は、その `List.ofFn` 表現の `count` に一致する。 -/
theorem finiteValueCount_eq_count_ofFn {n : Nat} (target : Nat)
    (values : Fin n → Nat) :
    finiteValueCount target values = (List.ofFn values).count target := by
  induction n with
  | zero => simp [finiteValueCount]
  | succ n inductionHypothesis =>
      rw [finiteValueCount, Fin.sum_univ_succ, List.ofFn_succ, List.count_cons]
      rw [← inductionHypothesis (fun index => values index.succ)]
      simp only [finiteValueCount]
      rw [Nat.add_comm]
      simp

/-- 指定値を取る添字がなければ、有限値出現個数は 0 である。 -/
theorem finiteValueCount_eq_zero_of_forall_ne
    {index value : Type*} [Fintype index] [DecidableEq value]
    (target : value) (values : index → value)
    (absent : ∀ position, values position ≠ target) :
    finiteValueCount target values = 0 := by
  unfold finiteValueCount
  apply Finset.sum_eq_zero
  intro position _
  simp [absent position]

/-- 指定値を取る添字が一意に存在すれば、有限値出現個数は 1 である。 -/
theorem finiteValueCount_eq_one_of_unique
    {index value : Type*} [Fintype index] [DecidableEq index]
    [DecidableEq value]
    (target : value) (values : index → value)
    (witness : index) (atWitness : values witness = target)
    (unique : ∀ position, values position = target → position = witness) :
    finiteValueCount target values = 1 := by
  unfold finiteValueCount
  rw [Finset.sum_eq_single witness]
  · simp [atWitness]
  · intro position _ different
    rw [if_neg (fun equal => different (unique position equal))]
  · simp

/-- 昇順な有限関数は、各値の出現個数がすべて同じなら互いに同一である。 -/
theorem sortedFin_eq_of_valueCount_eq {n : Nat}
    (left right : Fin n → Nat)
    (leftSorted : IsSortedFin left) (rightSorted : IsSortedFin right)
    (counts : ∀ target, finiteValueCount target left =
      finiteValueCount target right) :
    left = right := by
  have permutation : (List.ofFn left).Perm (List.ofFn right) := by
    rw [List.perm_iff_count]
    intro target
    rw [← finiteValueCount_eq_count_ofFn target left,
      ← finiteValueCount_eq_count_ofFn target right]
    exact counts target
  have leftPairwise : (List.ofFn left).Pairwise (· ≤ ·) := by
    rw [List.pairwise_iff_get]
    intro i j less
    let i' : Fin n := ⟨i.val, by simpa using i.isLt⟩
    let j' : Fin n := ⟨j.val, by simpa using j.isLt⟩
    have ordered := leftSorted i' j' (Nat.le_of_lt less)
    simpa [i', j'] using ordered
  have rightPairwise : (List.ofFn right).Pairwise (· ≤ ·) := by
    rw [List.pairwise_iff_get]
    intro i j less
    let i' : Fin n := ⟨i.val, by simpa using i.isLt⟩
    let j' : Fin n := ⟨j.val, by simpa using j.isLt⟩
    have ordered := rightSorted i' j' (Nat.le_of_lt less)
    simpa [i', j'] using ordered
  have listsEqual : List.ofFn left = List.ofFn right :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ leftLe rightLe =>
      Nat.le_antisymm leftLe rightLe) leftPairwise rightPairwise permutation
  funext index
  have atIndex := congrArg (fun values => values[index.val]?) listsEqual
  simpa using atIndex

/-- site word の bit 列化は任意の正の `q` で単射である。 -/
theorem siteWordBits_injective (p : QParameters) :
    Function.Injective (siteWordBits p) := by
  intro left right wordsEqual
  apply Fin.ext
  rw [← littleEndianNat_siteWordBits p left,
    wordsEqual, littleEndianNat_siteWordBits p right]

/-- 合法配置を昇順 site 値と末尾 marker 値へ埋め込む canonical candidate 関数。 -/
def configurationCandidateValue (p : QParameters)
    (configuration : QConfiguration p) (word : Fin p.sortWordCount) : Nat :=
  if active : word.val < configuration.1.card then
    (configuration.siteAt ⟨word.val, active⟩).val
  else
    2 ^ p.wordWidth

/-- canonical candidate の有効 word は対応する昇順 site 値である。 -/
theorem configurationCandidateValue_active
    (p : QParameters) (configuration : QConfiguration p)
    (word : Fin p.sortWordCount)
    (active : word.val < configuration.1.card) :
    configurationCandidateValue p configuration word =
      (configuration.siteAt ⟨word.val, active⟩).val := by
  simp [configurationCandidateValue, active]

/-- canonical candidate の padding word は data 範囲外の marker 値である。 -/
theorem configurationCandidateValue_padding
    (p : QParameters) (configuration : QConfiguration p)
    (word : Fin p.sortWordCount)
    (padding : configuration.1.card ≤ word.val) :
    configurationCandidateValue p configuration word = 2 ^ p.wordWidth := by
  simp [configurationCandidateValue, Nat.not_lt.mpr padding]

/-- 一つの物理 site 値は marker 値 `2^wordWidth` より小さい。 -/
theorem qSite_val_lt_marker (p : QParameters) (site : QSite p) :
    site.val < 2 ^ p.wordWidth := by
  have capacity : p.G * p.G = 2 ^ p.wordWidth := by
    simp [QParameters.G, QParameters.wordWidth, two_mul, pow_add]
  simpa [capacity] using site.isLt

/-- 合法配置の canonical candidate 関数は padding を含め全域で昇順である。 -/
theorem configurationCandidateValue_sorted
    (p : QParameters) (configuration : QConfiguration p) :
    IsSortedFin (configurationCandidateValue p configuration) := by
  intro left right ordered
  by_cases leftActive : left.val < configuration.1.card
  · by_cases rightActive : right.val < configuration.1.card
    · rw [configurationCandidateValue_active p configuration left leftActive,
        configurationCandidateValue_active p configuration right rightActive]
      by_cases equalValues : left.val = right.val
      · have equalWords : left = right := Fin.ext equalValues
        subst right
        exact Nat.le_refl _
      · have strict : left.val < right.val := by
          have weak : left.val ≤ right.val := ordered
          omega
        exact Nat.le_of_lt (configuration_siteAt_val_lt configuration (by
          simpa using strict))
    · rw [configurationCandidateValue_active p configuration left leftActive,
        configurationCandidateValue_padding p configuration right
          (Nat.le_of_not_gt rightActive)]
      exact Nat.le_of_lt
        (qSite_val_lt_marker p (configuration.siteAt ⟨left.val, leftActive⟩))
  · have rightInactive : ¬right.val < configuration.1.card := by
      intro rightActive
      have weak : left.val ≤ right.val := ordered
      omega
    rw [configurationCandidateValue_padding p configuration left
        (Nat.le_of_not_gt leftActive),
      configurationCandidateValue_padding p configuration right
        (Nat.le_of_not_gt rightInactive)]

/--
marker 未満の値の canonical candidate 出現個数は、その番号の site が配置にあれば 1、
なければ 0 である。
-/
theorem finiteValueCount_configurationCandidateValue_lt_marker
    (p : QParameters) (configuration : QConfiguration p)
    (target : Nat) (targetLt : target < 2 ^ p.wordWidth) :
    finiteValueCount target (configurationCandidateValue p configuration) =
      if ∃ site : QSite p, site ∈ configuration.1 ∧ site.val = target then
        1 else 0 := by
  by_cases existsSite :
      ∃ site : QSite p, site ∈ configuration.1 ∧ site.val = target
  · rcases existsSite with ⟨site, siteMember, siteValue⟩
    let smallSlot :=
      (configuration.1.orderIsoOfFin rfl).symm ⟨site, siteMember⟩
    have smallBelowSort : smallSlot.val < p.sortWordCount :=
      lt_of_lt_of_le smallSlot.isLt
        (le_trans configuration.2.2 p.K_le_sortWordCount)
    let word : Fin p.sortWordCount := ⟨smallSlot.val, smallBelowSort⟩
    have wordActive : word.val < configuration.1.card := smallSlot.isLt
    have wordSite : configuration.siteAt ⟨word.val, wordActive⟩ = site := by
      exact congrArg Subtype.val
        ((configuration.1.orderIsoOfFin rfl).apply_symm_apply
          ⟨site, siteMember⟩)
    have atWord : configurationCandidateValue p configuration word = target := by
      rw [configurationCandidateValue_active p configuration word wordActive,
        wordSite, siteValue]
    have unique : ∀ position,
        configurationCandidateValue p configuration position = target →
          position = word := by
      intro position positionValue
      have positionActive : position.val < configuration.1.card := by
        by_contra inactive
        rw [configurationCandidateValue_padding p configuration position
          (Nat.le_of_not_gt inactive)] at positionValue
        omega
      rw [configurationCandidateValue_active p configuration position
        positionActive] at positionValue
      have sitesEqual :
          configuration.siteAt ⟨position.val, positionActive⟩ = site := by
        apply Fin.ext
        rw [positionValue, siteValue]
      have slotsEqual := configuration.siteAt_injective
        (sitesEqual.trans wordSite.symm)
      exact Fin.ext
        (congrArg (fun index : Fin configuration.1.card => index.val) slotsEqual)
    rw [if_pos ⟨site, siteMember, siteValue⟩]
    exact finiteValueCount_eq_one_of_unique target
      (configurationCandidateValue p configuration) word atWord unique
  · rw [if_neg existsSite]
    apply finiteValueCount_eq_zero_of_forall_ne
    intro position positionValue
    by_cases active : position.val < configuration.1.card
    · apply existsSite
      refine ⟨configuration.siteAt ⟨position.val, active⟩, ?_, ?_⟩
      · exact ((configuration.1.orderIsoOfFin rfl)
          ⟨position.val, active⟩).2
      · rw [← positionValue]
        exact (configurationCandidateValue_active p configuration position active).symm
    · rw [configurationCandidateValue_padding p configuration position
        (Nat.le_of_not_gt active)] at positionValue
      omega

/-- marker より大きい値は canonical candidate 関数に出現しない。 -/
theorem finiteValueCount_configurationCandidateValue_gt_marker
    (p : QParameters) (configuration : QConfiguration p)
    (target : Nat) (markerLt : 2 ^ p.wordWidth < target) :
    finiteValueCount target (configurationCandidateValue p configuration) = 0 := by
  apply finiteValueCount_eq_zero_of_forall_ne
  intro position valueEqual
  by_cases active : position.val < configuration.1.card
  · rw [configurationCandidateValue_active p configuration position active]
        at valueEqual
    have belowMarker :=
      qSite_val_lt_marker p (configuration.siteAt ⟨position.val, active⟩)
    omega
  · rw [configurationCandidateValue_padding p configuration position
      (Nat.le_of_not_gt active)] at valueEqual
    omega

/-- canonical candidate 値に対応する marker 込み little-endian bit 列。 -/
def configurationCandidateBits (p : QParameters)
    (configuration : QConfiguration p) (word : Fin p.sortWordCount) : List Bool :=
  if active : word.val < configuration.1.card then
    siteWordBits p (configuration.siteAt ⟨word.val, active⟩) ++ [false]
  else
    List.replicate p.wordWidth false ++ [true]

/-- 任意長の全 0 little-endian bit 列の自然数値は 0 である。 -/
@[simp] theorem littleEndianNat_replicate_false (length : Nat) :
    littleEndianNat (List.replicate length false) = 0 := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      simp [List.replicate_succ, littleEndianNat, inductionHypothesis]

/-- canonical candidate bit 列の長さは物理 candidate word 幅に一致する。 -/
@[simp] theorem configurationCandidateBits_length
    (p : QParameters) (configuration : QConfiguration p)
    (word : Fin p.sortWordCount) :
    (configurationCandidateBits p configuration word).length = p.wordWidth + 1 := by
  by_cases active : word.val < configuration.1.card <;>
    simp [configurationCandidateBits, active]

/-- canonical candidate bit 列の little-endian 値は canonical candidate 値である。 -/
theorem littleEndianNat_configurationCandidateBits
    (p : QParameters) (configuration : QConfiguration p)
    (word : Fin p.sortWordCount) :
    littleEndianNat (configurationCandidateBits p configuration word) =
      configurationCandidateValue p configuration word := by
  by_cases active : word.val < configuration.1.card
  · simp [configurationCandidateBits, configurationCandidateValue, active,
      littleEndianNat_append, littleEndianNat_siteWordBits, littleEndianNat]
  · simp [configurationCandidateBits, configurationCandidateValue, active,
      littleEndianNat_append, littleEndianNat]

/--
実 candidate 値が canonical 値関数に点ごとに一致すれば、marker 込み全 bit 列も
canonical bit 列に一意に一致する。
-/
theorem candidateWord_eq_configurationCandidateBits_of_value_eq
    (p : QParameters) (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesEqual : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (word : Fin p.sortWordCount) :
    readWires (candidateWordAt p word) input =
      configurationCandidateBits p configuration word := by
  apply littleEndianNat_injective_of_length_eq
  · simp [readWires]
  · rw [show littleEndianNat (readWires (candidateWordAt p word) input) =
        qCandidateValue p input word by rfl]
    rw [valuesEqual]
    exact (littleEndianNat_configurationCandidateBits p configuration word).symm

/-- canonical 値一致から、有効 candidate の marker が偽であることが従う。 -/
theorem candidateMarker_false_of_value_eq
    (p : QParameters) (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesEqual : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (word : Fin p.sortWordCount)
    (active : word.val < configuration.1.card) :
    input (candidateMarkerWire p word) = false := by
  have fullWord := candidateWord_eq_configurationCandidateBits_of_value_eq
    p configuration input valuesEqual word
  have marker := congrArg (fun bits => bits[p.wordWidth]?) fullWord
  simpa [readWires, candidateWordAt, candidateMarkerWire,
    configurationCandidateBits, active] using marker

/-- canonical 値一致から、padding candidate の data が全 0 であることが従う。 -/
theorem candidateData_zero_of_value_eq_padding
    (p : QParameters) (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesEqual : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (word : Fin p.sortWordCount)
    (padding : configuration.1.card ≤ word.val) :
    readWires ((candidateWordAt p word).take p.wordWidth) input =
      List.replicate p.wordWidth false := by
  have fullWord := candidateWord_eq_configurationCandidateBits_of_value_eq
    p configuration input valuesEqual word
  have dataWord := congrArg (List.take p.wordWidth) fullWord
  simpa [readWires, configurationCandidateBits, Nat.not_lt.mpr padding] using dataWord

/-- canonical 値一致から、padding candidate の marker が真であることが従う。 -/
theorem candidateMarker_true_of_value_eq_padding
    (p : QParameters) (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesEqual : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (word : Fin p.sortWordCount)
    (padding : configuration.1.card ≤ word.val) :
    input (candidateMarkerWire p word) = true := by
  have fullWord := candidateWord_eq_configurationCandidateBits_of_value_eq
    p configuration input valuesEqual word
  have marker := congrArg (fun bits => bits[p.wordWidth]?) fullWord
  simpa [readWires, candidateWordAt, candidateMarkerWire,
    configurationCandidateBits, Nat.not_lt.mpr padding] using marker

/--
実 candidate 値が canonical 関数に点ごとに一致するなら、有効 word の data bit 列は
対応する site word と厳密に一致する。
-/
theorem candidateData_eq_siteWordBits_of_value_eq
    (p : QParameters) (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesEqual : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (word : Fin p.sortWordCount)
    (active : word.val < configuration.1.card) :
    readWires ((candidateWordAt p word).take p.wordWidth) input =
      siteWordBits p (configuration.siteAt ⟨word.val, active⟩) := by
  let site := configuration.siteAt ⟨word.val, active⟩
  have valueEqual : qCandidateValue p input word = site.val := by
    rw [valuesEqual]
    exact configurationCandidateValue_active p configuration word active
  have fullWord : readWires (candidateWordAt p word) input =
      siteWordBits p site ++ [false] := by
    apply littleEndianNat_injective_of_length_eq
    · simp [readWires]
    · rw [show littleEndianNat (readWires (candidateWordAt p word) input) =
          qCandidateValue p input word by rfl]
      rw [valueEqual, littleEndianNat_append,
        littleEndianNat_siteWordBits]
      simp [littleEndianNat]
  have dataWord := congrArg (List.take p.wordWidth) fullWord
  simpa [readWires] using dataWord

/--
sort 前 candidate 多重集合が合法配置の canonical 多重集合と一致するなら、正本
bitonic sort 後の candidate 値関数は canonical 昇順関数に点ごとに一致する。
-/
theorem qBitonicSort_candidateValue_eq_configurationCandidateValue
    (p : QParameters) (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (flagsZero : readWires (sortCompareWorkWires p) input =
      List.replicate (sortCompareWorkWires p).length false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p, input wire = false)
    (historiesZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      input ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) = false)
    (counts : ∀ target,
      finiteValueCount target (qCandidateValue p input) =
        finiteValueCount target
          (configurationCandidateValue p configuration)) :
    qCandidateValue p
        ((reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
          reversibleGatePermutation input) =
      configurationCandidateValue p configuration := by
  apply sortedFin_eq_of_valueCount_eq
  · exact reversiblySortCandidateWordsAndRestoreHistoryCircuit_sorts_candidates p input flagsZero
      scratchZero historiesZero
  · exact configurationCandidateValue_sorted p configuration
  · intro target
    rw [reversiblySortCandidateWordsAndRestoreHistoryCircuit_preserves_candidate_valueCount p input
      flagsZero scratchZero historiesZero target]
    exact counts target

end ReversibleCircuit

end ProbabilityGeneratorQProof
