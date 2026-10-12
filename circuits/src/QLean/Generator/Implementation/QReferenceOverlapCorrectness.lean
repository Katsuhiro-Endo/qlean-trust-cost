import QLean.Generator.Analysis.QOracleReference
import Mathlib.Tactic

/-!
# column/row参照関数のselector内積

実回路とは独立に、column参照が受理したselectorをrow参照で逆検査する有限和を定義する。
二つの対角copyと各active物理eventを一回ずつ数え、その正規化内積が既存の
`RowSelectorPathFiniteSumSuccessBlockSpec`へ厳密に一致することを示す。
-/

namespace ProbabilityGeneratorQProof

open QParameters
open Matrix

/-- column結果をrow側で逆検査した一selectorの符号付き寄与。 -/
def referenceAcceptedSelectorWeight {p : QParameters}
    (output input : QConfiguration p) (selector : QSelector p) : ℚ :=
  match columnReference input selector with
  | none => 0
  | some columnResult =>
      match rowReference output columnResult.rowSelector with
      | none => 0
      | some rowResult =>
          if columnResult.output = output ∧ rowResult.input = input ∧
              rowResult.columnSelector = selector then
            if columnResult.negative then -1 else 1
          else
            0

/-- occupied siteとcopy番号から対角selectorを構成する。 -/
def diagonalSelectorOfMember {p : QParameters}
    (input : QConfiguration p) (source : {site // site ∈ input.1})
    (copy : Fin 2) : QSelector p :=
  selectorOfSlotOffset (slotOfMember input source.1 source.2)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩

/-- active物理eventから、その衝突状態に対応する唯一のcolumn selectorを構成する。 -/
def columnSelectorOfActiveEvent {p : QParameters}
    (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) : QSelector p :=
  selectorForEvent input event.1 active event.2

/-- 一つのactive物理eventに対する参照関数内積の寄与。 -/
def activeEventReferenceWeight {p : QParameters}
    (output input : QConfiguration p) (event : QEvent p) : ℚ :=
  if active : event.1 ∈ input.1 then
    referenceAcceptedSelectorWeight output input
      (columnSelectorOfActiveEvent input event active)
  else
    0

/-- 二つの対角copyと全active物理eventを一回ずつ足す未正規化参照内積。 -/
def configurationCanonicalReferenceRawOverlap {p : QParameters}
    (output input : QConfiguration p) : ℚ :=
  (∑ source : {site // site ∈ input.1}, ∑ copy : Fin 2,
    referenceAcceptedSelectorWeight output input
      (diagonalSelectorOfMember input source copy)) +
  ∑ event ∈ configurationEvents input,
    activeEventReferenceWeight output input event

/-- `6K`一様準備に対応して未正規化参照内積を正規化する。 -/
def configurationReferenceNormalizedOverlap {p : QParameters}
    (output input : QConfiguration p) : ℚ :=
  (∑ selector : QSelector p,
    referenceAcceptedSelectorWeight output input selector) / (6 * (p.K : ℚ))

/-- 全`6K` selectorを明示的に足す未正規化参照内積。 -/
def configurationReferenceRawOverlap {p : QParameters}
    (output input : QConfiguration p) : ℚ :=
  ∑ selector : QSelector p,
    referenceAcceptedSelectorWeight output input selector

/-- selectorで選択された実在slotは、そのsiteのcanonical slot番号に一致する。 -/
theorem selectorSlot_eq_slotOfMember_of_selected
    {p : QParameters} (input : QConfiguration p) (slot : Fin p.K)
    (source : QSite p) (member : source ∈ input.1)
    (selected : configurationSlot? input slot = some ⟨source, member⟩) :
    slot = slotOfMember input source member := by
  unfold configurationSlot? at selected
  split at selected
  · rename_i present
    simp only [Option.some.injEq] at selected
    let smallSlot := (input.1.orderIsoOfFin rfl).symm ⟨source, member⟩
    have smallEqual : (⟨slot.val, present⟩ : Fin input.1.card) = smallSlot := by
      apply (input.1.orderIsoOfFin rfl).injective
      simpa [smallSlot] using selected
    apply Fin.ext
    simpa [slotOfMember, smallSlot] using congrArg Fin.val smallEqual
  · simp at selected

/-- 非対角offsetは、そこから読んだ方向と衝突bitのevent offsetへ戻る。 -/
theorem eventOffset_selectorParts {p : QParameters} (selector : QSelector p)
    (notDiagonal : ¬(selectorOffset selector).val < 2) :
    eventOffset (selectorDirection selector)
      (selectorRequestsCollision selector) = selectorOffset selector := by
  apply Fin.ext
  let offset := (selectorOffset selector).val
  have offsetLt : offset < 6 := (selectorOffset selector).isLt
  have offsetLower : 2 ≤ offset := Nat.le_of_not_gt notDiagonal
  by_cases rightDirection : offset < 4
  · by_cases collision : offset % 2 = 1
    · simp [eventOffset, selectorDirection, selectorRequestsCollision,
        offset, rightDirection, collision]
      omega
    · simp [eventOffset, selectorDirection, selectorRequestsCollision,
        offset, rightDirection, collision]
      omega
  · by_cases collision : offset % 2 = 1
    · simp [eventOffset, selectorDirection, selectorRequestsCollision,
        offset, rightDirection, collision]
      omega
    · simp [eventOffset, selectorDirection, selectorRequestsCollision,
        offset, rightDirection, collision]
      omega

/-- column参照はcanonical event selectorに対してcanonical row selectorを返す。 -/
theorem columnReference_selectorForEvent_exact
    {p : QParameters} (input : QConfiguration p)
    (source : QSite p) (member : source ∈ input.1)
    (direction : QDirection) :
    columnReference input (selectorForEvent input source member direction) =
      some ⟨eventOutput input source direction,
        rowSelectorForEvent input source member direction, false⟩ := by
  let selector := selectorForEvent input source member direction
  have selected : configurationSlot? input (selectorSlot selector) =
      some ⟨source, member⟩ := by
    simp [selector, selectorForEvent]
  have notDiagonal : ¬(selectorOffset selector).val < 2 := by
    simpa [selector, selectorForEvent] using
      eventOffset_not_diagonal direction
        (decide (moveSite source direction ∈ input.1.erase source))
  have branchCorrect :
      (decide (moveSite source (selectorDirection selector) ∈
        input.1.erase source) : Bool) = selectorRequestsCollision selector := by
    simp [selector, selectorForEvent]
  change columnReference input selector =
    some ⟨eventOutput input source direction,
      rowSelectorForEvent input source member direction, false⟩
  unfold columnReference
  rw [selected]
  simp only [notDiagonal, dite_false]
  rw [dif_pos branchCorrect]
  simp [selector, selectorForEvent, rowSelectorForEvent, eventOutput,
    eventCollision]

/-- canonical対角selectorの参照寄与は、同じ配置への二つの負のcopyである。 -/
theorem referenceAcceptedSelectorWeight_diagonal
    {p : QParameters} (output input : QConfiguration p)
    (source : {site // site ∈ input.1}) (copy : Fin 2) :
    referenceAcceptedSelectorWeight output input
        (diagonalSelectorOfMember input source copy) =
      if output = input then -1 else 0 := by
  let selector := diagonalSelectorOfMember input source copy
  have columnValue : columnReference input selector =
      some ⟨input, selector, true⟩ := by
    simpa [selector, diagonalSelectorOfMember] using
      columnReference_diagonal input source.1 source.2 copy
  rw [referenceAcceptedSelectorWeight, columnValue]
  by_cases same : output = input
  · subst output
    have rowValue : rowReference input selector = some ⟨input, selector⟩ := by
      simpa [selector, diagonalSelectorOfMember] using
        rowReference_diagonal input source.1 source.2 copy
    simp [rowValue, selector]
  · have notReverse : input ≠ output := Ne.symm same
    cases rowValue : rowReference output selector <;>
      simp [rowValue, same, notReverse]

/-- canonical active event selectorはcolumn/rowの両参照で受理され、更新一致を一回数える。 -/
theorem referenceAcceptedSelectorWeight_event
    {p : QParameters} (output input : QConfiguration p)
    (source : QSite p) (member : source ∈ input.1)
    (direction : QDirection) :
    referenceAcceptedSelectorWeight output input
        (selectorForEvent input source member direction) =
      if eventOutput input source direction = output then 1 else 0 := by
  let columnSelector := selectorForEvent input source member direction
  let rowSelector := rowSelectorForEvent input source member direction
  have columnValue : columnReference input columnSelector =
      some ⟨eventOutput input source direction, rowSelector, false⟩ := by
    simpa [columnSelector, rowSelector] using
      columnReference_selectorForEvent_exact input source member direction
  rw [referenceAcceptedSelectorWeight, columnValue]
  by_cases outputMatches : eventOutput input source direction = output
  · subst output
    have rowValue : rowReference (eventOutput input source direction) rowSelector =
        some ⟨input, columnSelector⟩ := by
      simpa [columnSelector, rowSelector] using
        rowReference_rowSelectorForEvent input source member direction
    simp [rowValue, columnSelector]
  · cases rowValue : rowReference output rowSelector <;>
      simp [rowValue, outputMatches]

/-- 選択slotが存在しなければ、そのselectorはcolumn参照関数で受理されない。 -/
theorem referenceAcceptedSelectorWeight_of_missing
    {p : QParameters} (output input : QConfiguration p)
    (selector : QSelector p)
    (missing : configurationSlot? input (selectorSlot selector) = none) :
    referenceAcceptedSelectorWeight output input selector = 0 := by
  unfold referenceAcceptedSelectorWeight columnReference
  rw [missing]

/-- 実在slotの対角offsetは、そのsiteのcanonicalな二つの対角selectorの一つである。 -/
theorem referenceAcceptedSelectorWeight_of_selected_diagonal
    {p : QParameters} (output input : QConfiguration p)
    (selector : QSelector p) (source : QSite p) (member : source ∈ input.1)
    (selected : configurationSlot? input (selectorSlot selector) =
      some ⟨source, member⟩)
    (diagonal : (selectorOffset selector).val < 2) :
    referenceAcceptedSelectorWeight output input selector =
      if output = input then -1 else 0 := by
  let copy : Fin 2 := ⟨(selectorOffset selector).val, diagonal⟩
  have slotEqual : selectorSlot selector = slotOfMember input source member :=
    selectorSlot_eq_slotOfMember_of_selected input (selectorSlot selector)
      source member selected
  have selectorEqual : selector = diagonalSelectorOfMember input ⟨source, member⟩ copy := by
    symm
    calc
      diagonalSelectorOfMember input ⟨source, member⟩ copy =
          selectorOfSlotOffset (selectorSlot selector) (selectorOffset selector) := by
        unfold diagonalSelectorOfMember
        congr 1
        exact slotEqual.symm
      _ = selector := selectorOfSlotOffset_parts selector
  calc
    referenceAcceptedSelectorWeight output input selector =
        referenceAcceptedSelectorWeight output input
          (diagonalSelectorOfMember input ⟨source, member⟩ copy) := by rw [selectorEqual]
    _ = if output = input then -1 else 0 :=
      referenceAcceptedSelectorWeight_diagonal output input ⟨source, member⟩ copy

/-- 実在slotの非対角offsetで衝突bitが正しければ、唯一のcanonical event selectorである。 -/
theorem referenceAcceptedSelectorWeight_of_selected_event
    {p : QParameters} (output input : QConfiguration p)
    (selector : QSelector p) (source : QSite p) (member : source ∈ input.1)
    (selected : configurationSlot? input (selectorSlot selector) =
      some ⟨source, member⟩)
    (notDiagonal : ¬(selectorOffset selector).val < 2)
    (branchCorrect : eventCollision input source (selectorDirection selector) =
      selectorRequestsCollision selector) :
    referenceAcceptedSelectorWeight output input selector =
      if eventOutput input source (selectorDirection selector) = output then 1 else 0 := by
  have slotEqual : selectorSlot selector = slotOfMember input source member :=
    selectorSlot_eq_slotOfMember_of_selected input (selectorSlot selector)
      source member selected
  have offsetEqual : eventOffset (selectorDirection selector)
      (eventCollision input source (selectorDirection selector)) =
        selectorOffset selector := by
    rw [branchCorrect]
    exact eventOffset_selectorParts selector notDiagonal
  have selectorEqual : selector =
      selectorForEvent input source member (selectorDirection selector) := by
    symm
    calc
      selectorForEvent input source member (selectorDirection selector) =
          selectorOfSlotOffset (selectorSlot selector) (selectorOffset selector) := by
        unfold selectorForEvent
        change selectorOfSlotOffset (slotOfMember input source member)
            (eventOffset (selectorDirection selector)
              (eventCollision input source (selectorDirection selector))) = _
        rw [slotEqual, offsetEqual]
      _ = selector := selectorOfSlotOffset_parts selector
  calc
    referenceAcceptedSelectorWeight output input selector =
        referenceAcceptedSelectorWeight output input
          (selectorForEvent input source member (selectorDirection selector)) := by
      exact congrArg (referenceAcceptedSelectorWeight output input) selectorEqual
    _ = if eventOutput input source (selectorDirection selector) = output then 1 else 0 :=
      referenceAcceptedSelectorWeight_event output input source member
        (selectorDirection selector)

/-- 実在slotの非対角offsetでも衝突要求が誤れば寄与は0である。 -/
theorem referenceAcceptedSelectorWeight_of_selected_wrong_branch
    {p : QParameters} (output input : QConfiguration p)
    (selector : QSelector p) (source : QSite p) (member : source ∈ input.1)
    (selected : configurationSlot? input (selectorSlot selector) =
      some ⟨source, member⟩)
    (notDiagonal : ¬(selectorOffset selector).val < 2)
    (branchWrong : eventCollision input source (selectorDirection selector) ≠
      selectorRequestsCollision selector) :
    referenceAcceptedSelectorWeight output input selector = 0 := by
  unfold referenceAcceptedSelectorWeight columnReference
  rw [selected]
  simp only [notDiagonal, dite_false]
  have branchWrong' :
      (decide (moveSite source (selectorDirection selector) ∈ input.1.erase source) : Bool) ≠
        selectorRequestsCollision selector := by
    simpa only [eventCollision] using branchWrong
  rw [dif_neg branchWrong']

/-- 任意selectorの寄与をslot存在・対角・衝突branchだけで特徴付ける。 -/
theorem referenceAcceptedSelectorWeight_eq_spec
    {p : QParameters} (output input : QConfiguration p)
    (selector : QSelector p) :
    referenceAcceptedSelectorWeight output input selector =
      match configurationSlot? input (selectorSlot selector) with
      | none => 0
      | some source =>
          if (selectorOffset selector).val < 2 then
            if output = input then -1 else 0
          else if eventCollision input source.1 (selectorDirection selector) =
              selectorRequestsCollision selector then
            if eventOutput input source.1 (selectorDirection selector) = output then 1 else 0
          else
            0 := by
  cases selected : configurationSlot? input (selectorSlot selector) with
  | none =>
      simpa [selected] using
        referenceAcceptedSelectorWeight_of_missing output input selector selected
  | some source =>
      by_cases diagonal : (selectorOffset selector).val < 2
      · simpa [selected, diagonal] using
          referenceAcceptedSelectorWeight_of_selected_diagonal output input selector
            source.1 source.2 selected diagonal
      · by_cases branchCorrect :
          eventCollision input source.1 (selectorDirection selector) =
            selectorRequestsCollision selector
        · simpa [selected, diagonal, branchCorrect] using
            referenceAcceptedSelectorWeight_of_selected_event output input selector
              source.1 source.2 selected diagonal branchCorrect
        · simpa [selected, diagonal, branchCorrect] using
            referenceAcceptedSelectorWeight_of_selected_wrong_branch output input selector
              source.1 source.2 selected diagonal branchCorrect

/-- selectorを`slot × offset`へ分解する有限型同値。 -/
def selectorSlotOffsetEquiv (p : QParameters) :
    QSelector p ≃ Fin p.K × Fin 6 where
  toFun selector := (selectorSlot selector, selectorOffset selector)
  invFun pair := selectorOfSlotOffset pair.1 pair.2
  left_inv selector := selectorOfSlotOffset_parts selector
  right_inv pair := by
    rcases pair with ⟨slot, offset⟩
    simp

/-- 一つの実在siteに対応する、対角2本と右・上event各1本のcanonical寄与。 -/
def sourceCanonicalReferenceWeight {p : QParameters}
    (output input : QConfiguration p) (source : {site // site ∈ input.1}) : ℚ :=
  2 * (if output = input then -1 else 0) +
    (if eventOutput input source.1 .right = output then 1 else 0) +
    (if eventOutput input source.1 .up = output then 1 else 0)

/-- 一つのsiteから出る右・上二eventのcanonicalな正寄与。 -/
def siteEventReferenceWeight {p : QParameters}
    (output input : QConfiguration p) (site : QSite p) : ℚ :=
  (if eventOutput input site .right = output then 1 else 0) +
    (if eventOutput input site .up = output then 1 else 0)

/-- 存在しないslotを0とした、一slot分のcanonical参照寄与。 -/
def slotCanonicalReferenceWeight {p : QParameters}
    (output input : QConfiguration p) (slot : Fin p.K) : ℚ :=
  match configurationSlot? input slot with
  | none => 0
  | some source => sourceCanonicalReferenceWeight output input source

/-- 一slotの六offset和は、対角2本と右・上の正しい衝突branch各1本だけを残す。 -/
theorem sum_referenceAcceptedSelectorWeight_offsets
    {p : QParameters} (output input : QConfiguration p) (slot : Fin p.K) :
    (∑ offset : Fin 6,
      referenceAcceptedSelectorWeight output input
        (selectorOfSlotOffset slot offset)) =
      slotCanonicalReferenceWeight output input slot := by
  cases selected : configurationSlot? input slot with
  | none =>
      simp only [referenceAcceptedSelectorWeight_eq_spec]
      simp [slotCanonicalReferenceWeight, selected]
  | some source =>
      by_cases same : output = input <;>
        cases rightCollision : eventCollision input source.1 .right <;>
        cases upCollision : eventCollision input source.1 .up <;>
        simp [referenceAcceptedSelectorWeight_eq_spec, slotCanonicalReferenceWeight,
          sourceCanonicalReferenceWeight, selected, same, rightCollision, upCollision,
          Fin.sum_univ_succ, selectorDirection, selectorRequestsCollision,
          ] <;> ring

/-- 全`6K` selector和は、まず`K`個のslotごとの六offset和へ再添字付けできる。 -/
theorem configurationReferenceRawOverlap_eq_sum_slots
    {p : QParameters} (output input : QConfiguration p) :
    configurationReferenceRawOverlap output input =
      ∑ slot : Fin p.K, slotCanonicalReferenceWeight output input slot := by
  unfold configurationReferenceRawOverlap
  rw [Fintype.sum_equiv (selectorSlotOffsetEquiv p)
    (fun selector => referenceAcceptedSelectorWeight output input selector)
    (fun pair => referenceAcceptedSelectorWeight output input
      (selectorOfSlotOffset pair.1 pair.2))]
  · rw [Fintype.sum_prod_type]
    apply Fintype.sum_congr
    intro slot
    exact sum_referenceAcceptedSelectorWeight_offsets output input slot
  · intro selector
    simp [selectorSlotOffsetEquiv]

/-- 配置内に実在する`Fin K` slotとoccupied siteの昇順有限型同値。 -/
def presentSlotEquiv {p : QParameters} (input : QConfiguration p) :
    {slot : Fin p.K // slot.val < input.1.card} ≃ {site : QSite p // site ∈ input.1} where
  toFun slot := input.1.orderIsoOfFin rfl ⟨slot.1.val, slot.2⟩
  invFun source := by
    let smallSlot := (input.1.orderIsoOfFin rfl).symm source
    exact ⟨⟨smallSlot.val, lt_of_lt_of_le smallSlot.isLt input.2.2⟩, smallSlot.isLt⟩
  left_inv slot := by
    apply Subtype.ext
    apply Fin.ext
    simp
  right_inv source := by
    exact (input.1.orderIsoOfFin rfl).apply_symm_apply source

/-- 実在slotを参照関数で読むと、`presentSlotEquiv`が返すoccupied siteになる。 -/
theorem configurationSlot_presentSlotEquiv
    {p : QParameters} (input : QConfiguration p)
    (slot : {slot : Fin p.K // slot.val < input.1.card}) :
    configurationSlot? input slot.1 = some (presentSlotEquiv input slot) := by
  unfold configurationSlot?
  rw [dif_pos slot.2]
  rfl

/-- `K` slot和では存在しない末尾slotが0となり、occupied site和だけが残る。 -/
theorem sum_slotCanonicalReferenceWeight_eq_sum_sources
    {p : QParameters} (output input : QConfiguration p) :
    (∑ slot : Fin p.K, slotCanonicalReferenceWeight output input slot) =
      ∑ source : {site : QSite p // site ∈ input.1},
        sourceCanonicalReferenceWeight output input source := by
  let presentSlots : Finset (Fin p.K) :=
    Finset.univ.filter fun slot => slot.val < input.1.card
  calc
    (∑ slot : Fin p.K, slotCanonicalReferenceWeight output input slot) =
        ∑ slot ∈ presentSlots, slotCanonicalReferenceWeight output input slot := by
      symm
      apply Finset.sum_subset
      · intro slot slotMember
        simp [presentSlots] at slotMember ⊢
      · intro slot _ notPresent
        have absent : ¬slot.val < input.1.card := by
          simpa [presentSlots] using notPresent
        simp [slotCanonicalReferenceWeight, configurationSlot?, absent]
    _ = ∑ slot : {slot : Fin p.K // slot.val < input.1.card},
        slotCanonicalReferenceWeight output input slot.1 := by
      apply Finset.sum_subtype
      intro slot
      simp [presentSlots]
    _ = ∑ source : {site : QSite p // site ∈ input.1},
        sourceCanonicalReferenceWeight output input source := by
      apply Fintype.sum_equiv (presentSlotEquiv input)
      intro slot
      simp [slotCanonicalReferenceWeight,
        configurationSlot_presentSlotEquiv input slot]

/-- 一つのactive eventの参照寄与は、更新先が指定出力なら1、そうでなければ0である。 -/
theorem activeEventReferenceWeight_eq_indicator
    {p : QParameters} (output input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) :
    activeEventReferenceWeight output input event =
      if updateConfiguration input event = output then 1 else 0 := by
  unfold activeEventReferenceWeight
  rw [dif_pos active]
  simpa [columnSelectorOfActiveEvent, eventOutput] using
    referenceAcceptedSelectorWeight_event output input event.1 active event.2

/-- 右・上の二方向を`Fin 2`へ移す固定有限型同値。 -/
def directionEquivFinTwo : QDirection ≃ Fin 2 where
  toFun
    | .right => 0
    | .up => 1
  invFun
    | ⟨0, _⟩ => .right
    | ⟨_ + 1, _⟩ => .up
  left_inv direction := by cases direction <;> rfl
  right_inv index := by
    rcases index with ⟨value, bound⟩
    cases value with
    | zero => rfl
    | succ value =>
        have valueZero : value = 0 := by omega
        subst value
        rfl

/-- 二方向上の有限和を右項と上項の和へ分解する。 -/
theorem sum_qDirection_two (f : QDirection → ℚ) :
    (∑ direction : QDirection, f direction) = f .right + f .up := by
  calc
    (∑ direction : QDirection, f direction) =
        ∑ index : Fin 2, f (directionEquivFinTwo.symm index) := by
      apply Fintype.sum_equiv directionEquivFinTwo
      intro direction
      cases direction <;> rfl
    _ = f .right + f .up := by
      rw [Fin.sum_univ_two]
      rfl

/-- `configurationEvents`上の参照和はoccupied siteごとの右・上event和である。 -/
theorem sum_activeEventReferenceWeight_eq_sum_sites
    {p : QParameters} (output input : QConfiguration p) :
    (∑ event ∈ configurationEvents input,
      activeEventReferenceWeight output input event) =
      ∑ site ∈ input.1, siteEventReferenceWeight output input site := by
  calc
    (configurationEvents input).sum
        (activeEventReferenceWeight output input) =
        input.1.sum (fun site =>
          ∑ direction : QDirection,
            activeEventReferenceWeight output input (site, direction)) := by
      exact Finset.sum_product input.1 Finset.univ
        (fun event => activeEventReferenceWeight output input event)
    _ = input.1.sum (siteEventReferenceWeight output input) := by
      apply Finset.sum_congr rfl
      intro site siteMember
      rw [sum_qDirection_two]
      rw [activeEventReferenceWeight_eq_indicator output input (site, .right) siteMember]
      rw [activeEventReferenceWeight_eq_indicator output input (site, .up) siteMember]
      rfl

/-- 一occupied siteの二つの対角copyの参照寄与は対角値の2倍である。 -/
theorem sum_diagonalReferenceWeight_copies
    {p : QParameters} (output input : QConfiguration p)
    (source : {site : QSite p // site ∈ input.1}) :
    (∑ copy : Fin 2,
      referenceAcceptedSelectorWeight output input
        (diagonalSelectorOfMember input source copy)) =
      2 * (if output = input then -1 else 0) := by
  rw [Fin.sum_univ_two]
  simp only [referenceAcceptedSelectorWeight_diagonal]
  ring

/-- canonical参照和はoccupied siteごとの対角2本と右・上eventの和に等しい。 -/
theorem configurationCanonicalReferenceRawOverlap_eq_sum_sources
    {p : QParameters} (output input : QConfiguration p) :
    configurationCanonicalReferenceRawOverlap output input =
      ∑ source : {site : QSite p // site ∈ input.1},
        sourceCanonicalReferenceWeight output input source := by
  unfold configurationCanonicalReferenceRawOverlap
  rw [sum_activeEventReferenceWeight_eq_sum_sites]
  have eventSubtype :
      (∑ site ∈ input.1, siteEventReferenceWeight output input site) =
        ∑ source : {site : QSite p // site ∈ input.1},
          siteEventReferenceWeight output input source.1 := by
    apply Finset.sum_subtype
    intro site
    rfl
  rw [eventSubtype]
  simp_rw [sum_diagonalReferenceWeight_copies]
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro source
  simp [sourceCanonicalReferenceWeight, siteEventReferenceWeight]
  ring

/-- 全`6K` selector和は対角2本とactive物理event各1本のcanonical和に厳密に等しい。 -/
theorem configurationReferenceRawOverlap_eq_configurationCanonicalReferenceRawOverlap
    {p : QParameters} (output input : QConfiguration p) :
    configurationReferenceRawOverlap output input =
      configurationCanonicalReferenceRawOverlap output input := by
  rw [configurationReferenceRawOverlap_eq_sum_slots]
  rw [sum_slotCanonicalReferenceWeight_eq_sum_sources]
  exact (configurationCanonicalReferenceRawOverlap_eq_sum_sources output input).symm

/-- active eventの参照寄与和は、指定出力へ到達する物理event数に等しい。 -/
theorem sum_activeEventReferenceWeight_eq_transitionCount
    {p : QParameters} (output input : QConfiguration p) :
    (∑ event ∈ configurationEvents input,
      activeEventReferenceWeight output input event) =
      (TechnicalReportQ.transitionCount configurationEvents updateConfiguration
        output input : ℚ) := by
  calc
    (∑ event ∈ configurationEvents input,
        activeEventReferenceWeight output input event) =
        ∑ event ∈ configurationEvents input,
          if updateConfiguration input event = output then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro event eventMember
      have active : event.1 ∈ input.1 := by
        exact (Finset.mem_product.mp eventMember).1
      exact activeEventReferenceWeight_eq_indicator output input event active
    _ = (TechnicalReportQ.transitionCount configurationEvents updateConfiguration
        output input : ℚ) := by
      rw [Finset.sum_boole]
      rfl

/-- canonical参照和は既存の未正規化selector内積公式そのものである。 -/
theorem configurationCanonicalReferenceRawOverlap_eq_configurationRawSelectorOverlap
    {p : QParameters} (output input : QConfiguration p) :
    configurationCanonicalReferenceRawOverlap output input =
      configurationRawSelectorOverlap output input := by
  unfold configurationCanonicalReferenceRawOverlap configurationRawSelectorOverlap
  rw [sum_activeEventReferenceWeight_eq_transitionCount]
  simp_rw [sum_diagonalReferenceWeight_copies]
  unfold TechnicalReportQ.rawSelectorOverlap configurationParticleCount
  by_cases same : output = input
  · simp [same]
    ring
  · simp [same]

/-- column/row参照関数から直接足した全selector和は既存の未正規化内積に等しい。 -/
theorem configurationReferenceRawOverlap_eq_configurationRawSelectorOverlap
    {p : QParameters} (output input : QConfiguration p) :
    configurationReferenceRawOverlap output input =
      configurationRawSelectorOverlap output input := by
  rw [configurationReferenceRawOverlap_eq_configurationCanonicalReferenceRawOverlap]
  exact configurationCanonicalReferenceRawOverlap_eq_configurationRawSelectorOverlap
    output input

/-- 全`6K`参照和を`6K`で割った値は既存の正規化selector内積に等しい。 -/
theorem configurationReferenceNormalizedOverlap_eq_configurationNormalizedSelectorOverlap
    {p : QParameters} (output input : QConfiguration p) :
    configurationReferenceNormalizedOverlap output input =
      configurationNormalizedSelectorOverlap output input := by
  unfold configurationReferenceNormalizedOverlap configurationNormalizedSelectorOverlap
  unfold TechnicalReportQ.normalizedSelectorOverlap
  change configurationReferenceRawOverlap output input / (6 * (p.K : ℚ)) =
    configurationRawSelectorOverlap output input / (6 * (p.K : ℚ))
  rw [configurationReferenceRawOverlap_eq_configurationRawSelectorOverlap]

/-- 参照関数の全selector和を物理delimiter空間へ埋め込んだ正規化演算子。 -/
noncomputable def embeddedReferenceSelectorOverlap (p : QParameters) :
    Operator (RegisterBasis p.systemWidth) :=
  Matrix.of fun output input =>
    match decodeDelimiter output, decodeDelimiter input with
    | some outputConfiguration, some inputConfiguration =>
        (configurationReferenceNormalizedOverlap outputConfiguration
          inputConfiguration : ℂ)
    | _, _ => 0

/-- 参照関数から直接構成した物理演算子は既存の`RowSelectorPathFiniteSumSuccessBlockSpec`に等しい。 -/
theorem embeddedReferenceSelectorOverlap_eq_RowSelectorPathFiniteSumSuccessBlockSpec
    (p : QParameters) :
    embeddedReferenceSelectorOverlap p = RowSelectorPathFiniteSumSuccessBlockSpec p := by
  ext output input
  simp only [embeddedReferenceSelectorOverlap, RowSelectorPathFiniteSumSuccessBlockSpec, Matrix.of_apply]
  cases outputDecoded : decodeDelimiter output with
  | none => simp
  | some outputConfiguration =>
      cases inputDecoded : decodeDelimiter input with
      | none => simp
      | some inputConfiguration =>
          simp [
            configurationReferenceNormalizedOverlap_eq_configurationNormalizedSelectorOverlap]

end ProbabilityGeneratorQProof
