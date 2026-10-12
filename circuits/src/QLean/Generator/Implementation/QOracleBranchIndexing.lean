import QLean.Generator.Implementation.QOracleSequenceSkeleton
import QLean.Generator.Implementation.QReferenceOverlapCorrectness
import Mathlib.Tactic

/-!
# Q oracle 分岐列の型安全な添字付け

`6K` 本の column/row 分岐を selector の `slot × offset` 分解で添字付けする。
一般の `K` に依存する列挙は行わず、各 slot 内の固定長六分岐だけを局所的に扱う。
-/

namespace ProbabilityGeneratorQProof

/-- 長さ六の関数を、offset `0,1,...,5` の順のリストへ変換する。 -/
private def sixEntryList {α : Type*} (entry : Fin 6 → α) : List α :=
  [entry 0, entry 1, entry 2, entry 3, entry 4, entry 5]

/-- 固定長六の局所リストは、同じ関数から作った `List.ofFn` である。 -/
private theorem sixEntryList_eq_ofFn {α : Type*} (entry : Fin 6 → α) :
    sixEntryList entry = List.ofFn entry := by
  simp [sixEntryList, List.ofFn_succ]

/-- slot ごとの固定長六リストを連結すると、`6 * K` の商・剰余による添字列になる。 -/
private theorem flatMap_sixEntryList_eq_ofFn {α : Type*} (K : ℕ)
    (entry : Fin K → Fin 6 → α) :
    (List.finRange K).flatMap (fun slot => sixEntryList (entry slot)) =
      List.ofFn (fun index : Fin (6 * K) =>
        entry ⟨index.val / 6, by
          rw [Nat.div_lt_iff_lt_mul (by decide)]
          omega⟩
          ⟨index.val % 6, Nat.mod_lt _ (by decide)⟩) := by
  simp_rw [sixEntryList_eq_ofFn]
  induction K with
  | zero => simp
  | succ K inductionHypothesis =>
      have finRangeSucc : List.finRange (K + 1) =
          (List.finRange K).map Fin.castSucc ++ [Fin.last K] := by
        unfold List.finRange
        rw [List.ofFn_add]
        simp
        constructor
        · funext slot
          apply Fin.ext
          rfl
        · apply Fin.ext
          rfl
      rw [finRangeSucc]
      simp only [List.flatMap_append, List.flatMap_map, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [inductionHypothesis (fun slot offset => entry slot.castSucc offset)]
      simp only [Nat.mul_add, Nat.mul_one]
      rw [List.ofFn_add]
      congr 1
      apply List.ofFn_inj.mpr
      funext offset
      congr 1
      · apply Fin.ext
        simp
        omega
      · apply Fin.ext
        simpa using (Nat.mod_eq_of_lt offset.isLt).symm

/-- column の一つの slot と offset が指定する型安全な分岐回路。 -/
def dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset (p : QParameters) (slot : Fin p.K)
    (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  if diagonal : offset.val < 2 then
    columnDiagonalResultComputeUseUncomputeCircuit p slot ⟨offset.val, diagonal⟩
  else
    applyColumnEventReferenceAndRestoreWorkCircuit p slot offset

/-- row の一つの slot と offset が指定する型安全な分岐回路。 -/
def dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset (p : QParameters) (slot : Fin p.K)
    (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  if diagonal : offset.val < 2 then
    rowDiagonalResultComputeUseUncomputeCircuit p slot ⟨offset.val, diagonal⟩
  else
    applyRowEventReferenceAndRestoreWorkCircuit p slot offset

/-- selector が指定する column 分岐回路。 -/
def dispatchColumnSelectorToDiagonalOrEventCircuit (p : QParameters) (selector : QSelector p) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset p (selectorSlot selector)
    (selectorOffset selector)

/-- selector が指定する row 分岐回路。 -/
def dispatchRowSelectorToDiagonalOrEventCircuit (p : QParameters) (selector : QSelector p) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset p (selectorSlot selector)
    (selectorOffset selector)

/-- column の固定六分岐は slot/offset 添字関数の局所リストである。 -/
private theorem columnOracleBranchChunk_eq (p : QParameters) (slot : Fin p.K) :
    [columnDiagonalResultComputeUseUncomputeCircuit p slot 0, columnDiagonalResultComputeUseUncomputeCircuit p slot 1,
      applyColumnEventReferenceAndRestoreWorkCircuit p slot 2, applyColumnEventReferenceAndRestoreWorkCircuit p slot 3,
      applyColumnEventReferenceAndRestoreWorkCircuit p slot 4, applyColumnEventReferenceAndRestoreWorkCircuit p slot 5] =
      sixEntryList (dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset p slot) := by
  simp [sixEntryList, dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset]

/-- row の固定六分岐は slot/offset 添字関数の局所リストである。 -/
private theorem rowOracleBranchChunk_eq (p : QParameters) (slot : Fin p.K) :
    [rowDiagonalResultComputeUseUncomputeCircuit p slot 0, rowDiagonalResultComputeUseUncomputeCircuit p slot 1,
      applyRowEventReferenceAndRestoreWorkCircuit p slot 2, applyRowEventReferenceAndRestoreWorkCircuit p slot 3,
      applyRowEventReferenceAndRestoreWorkCircuit p slot 4, applyRowEventReferenceAndRestoreWorkCircuit p slot 5] =
      sixEntryList (dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset p slot) := by
  simp [sixEntryList, dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset]

/-- column 分岐列全体は selector 順の `List.ofFn` である。 -/
theorem columnOracleBranchList_eq_ofFn (p : QParameters) :
    columnOracleBranchList p = List.ofFn (dispatchColumnSelectorToDiagonalOrEventCircuit p) := by
  unfold columnOracleBranchList
  simp_rw [columnOracleBranchChunk_eq]
  rw [flatMap_sixEntryList_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext selector
  rfl

/-- row 分岐列全体は selector 順の `List.ofFn` である。 -/
theorem rowOracleBranchList_eq_ofFn (p : QParameters) :
    rowOracleBranchList p = List.ofFn (dispatchRowSelectorToDiagonalOrEventCircuit p) := by
  unfold rowOracleBranchList
  simp_rw [rowOracleBranchChunk_eq]
  rw [flatMap_sixEntryList_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext selector
  rfl

/-- 対角 offset の column 分岐は、型安全な二値 copy 添字を持つ対角分岐である。 -/
@[simp] theorem dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) (diagonal : offset.val < 2) :
    dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset p slot offset =
      columnDiagonalResultComputeUseUncomputeCircuit p slot ⟨offset.val, diagonal⟩ := by
  simp [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset, diagonal]

/-- 非対角 offset の column 分岐は、同じ offset を持つ event 分岐である。 -/
@[simp] theorem dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_event (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) (event : ¬offset.val < 2) :
    dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset p slot offset =
      applyColumnEventReferenceAndRestoreWorkCircuit p slot offset := by
  simp [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset, event]

/-- 対角 offset の row 分岐は、型安全な二値 copy 添字を持つ対角分岐である。 -/
@[simp] theorem dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) (diagonal : offset.val < 2) :
    dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset p slot offset =
      rowDiagonalResultComputeUseUncomputeCircuit p slot ⟨offset.val, diagonal⟩ := by
  simp [dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset, diagonal]

/-- 非対角 offset の row 分岐は、同じ offset を持つ event 分岐である。 -/
@[simp] theorem dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_event (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) (event : ¬offset.val < 2) :
    dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset p slot offset =
      applyRowEventReferenceAndRestoreWorkCircuit p slot offset := by
  simp [dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset, event]

/-- column 分岐列の selector 番目の要素は、その selector の型安全な分岐である。 -/
theorem columnOracleBranchList_getElem (p : QParameters)
    (selector : QSelector p) :
    (columnOracleBranchList p)[selector.val]'(by
      rw [columnOracleBranchList_length]
      exact selector.isLt) = dispatchColumnSelectorToDiagonalOrEventCircuit p selector := by
  simp [columnOracleBranchList_eq_ofFn]

/-- row 分岐列の selector 番目の要素は、その selector の型安全な分岐である。 -/
theorem rowOracleBranchList_getElem (p : QParameters)
    (selector : QSelector p) :
    (rowOracleBranchList p)[selector.val]'(by
      rw [rowOracleBranchList_length]
      exact selector.isLt) = dispatchRowSelectorToDiagonalOrEventCircuit p selector := by
  simp [rowOracleBranchList_eq_ofFn]

/-- column 分岐列を selector 位置の直前・active 分岐・直後へ分解する。 -/
theorem columnOracleBranchList_split_at (p : QParameters)
    (selector : QSelector p) :
    columnOracleBranchList p =
      (columnOracleBranchList p).take selector.val ++
        (dispatchColumnSelectorToDiagonalOrEventCircuit p selector ::
          (columnOracleBranchList p).drop (selector.val + 1)) := by
  calc
    columnOracleBranchList p =
        (columnOracleBranchList p).take selector.val ++
          (columnOracleBranchList p).drop selector.val :=
      (List.take_append_drop selector.val (columnOracleBranchList p)).symm
    _ = (columnOracleBranchList p).take selector.val ++
        ((columnOracleBranchList p)[selector.val]'(by
            rw [columnOracleBranchList_length]
            exact selector.isLt) ::
          (columnOracleBranchList p).drop (selector.val + 1)) := by
      rw [List.drop_eq_getElem_cons]
    _ = (columnOracleBranchList p).take selector.val ++
        (dispatchColumnSelectorToDiagonalOrEventCircuit p selector ::
          (columnOracleBranchList p).drop (selector.val + 1)) := by
      rw [columnOracleBranchList_getElem]

/-- row 分岐列を selector 位置の直前・active 分岐・直後へ分解する。 -/
theorem rowOracleBranchList_split_at (p : QParameters)
    (selector : QSelector p) :
    rowOracleBranchList p =
      (rowOracleBranchList p).take selector.val ++
        (dispatchRowSelectorToDiagonalOrEventCircuit p selector ::
          (rowOracleBranchList p).drop (selector.val + 1)) := by
  calc
    rowOracleBranchList p =
        (rowOracleBranchList p).take selector.val ++
          (rowOracleBranchList p).drop selector.val :=
      (List.take_append_drop selector.val (rowOracleBranchList p)).symm
    _ = (rowOracleBranchList p).take selector.val ++
        ((rowOracleBranchList p)[selector.val]'(by
            rw [rowOracleBranchList_length]
            exact selector.isLt) ::
          (rowOracleBranchList p).drop (selector.val + 1)) := by
      rw [List.drop_eq_getElem_cons]
    _ = (rowOracleBranchList p).take selector.val ++
        (dispatchRowSelectorToDiagonalOrEventCircuit p selector ::
          (rowOracleBranchList p).drop (selector.val + 1)) := by
      rw [rowOracleBranchList_getElem]

/-- selector の `6 * slot + offset` 定数は selector 自身の自然数値に等しい。 -/
theorem selectorConstant_eq_selectorVal {p : QParameters}
    (selector : QSelector p) :
    6 * (selectorSlot selector).val + (selectorOffset selector).val =
      selector.val := by
  simpa [selectorOfSlotOffset] using
    congrArg Fin.val (selectorOfSlotOffset_parts selector)

/-- 異なる selector は slot または offset の少なくとも一方が異なる。 -/
theorem selectorSlotOffset_ne_of_ne {p : QParameters}
    {left right : QSelector p} (different : left ≠ right) :
    selectorSlot left ≠ selectorSlot right ∨
      selectorOffset left ≠ selectorOffset right := by
  by_contra sameParts
  push Not at sameParts
  apply different
  apply (selectorSlotOffsetEquiv p).injective
  exact Prod.ext sameParts.1 sameParts.2

/-- 異なる selector の `6 * slot + offset` 定数は、定数一意性により異なる。 -/
theorem selectorConstant_ne_of_selector_ne {p : QParameters}
    {left right : QSelector p} (different : left ≠ right) :
    6 * (selectorSlot left).val + (selectorOffset left).val ≠
      6 * (selectorSlot right).val + (selectorOffset right).val :=
  selectorConstant_ne_of_slot_offset_ne
    (selectorSlot left) (selectorSlot right)
    (selectorOffset left) (selectorOffset right)
    (selectorSlotOffset_ne_of_ne different)

/-- active selector より前の selector は、active と異なる slot/offset 対を持つ。 -/
theorem selectorSlotOffset_ne_of_before {p : QParameters}
    {before active : QSelector p} (position : before.val < active.val) :
    selectorSlot before ≠ selectorSlot active ∨
      selectorOffset before ≠ selectorOffset active :=
  selectorSlotOffset_ne_of_ne (Fin.ne_of_lt position)

/-- active selector より後の selector は、active と異なる slot/offset 対を持つ。 -/
theorem selectorSlotOffset_ne_of_after {p : QParameters}
    {active after : QSelector p} (position : active.val < after.val) :
    selectorSlot after ≠ selectorSlot active ∨
      selectorOffset after ≠ selectorOffset active :=
  selectorSlotOffset_ne_of_ne (Ne.symm (Fin.ne_of_lt position))

/-- active より前の selector 定数は、slot/offset 定数一意性により active と異なる。 -/
theorem selectorConstant_ne_of_before {p : QParameters}
    {before active : QSelector p} (position : before.val < active.val) :
    6 * (selectorSlot before).val + (selectorOffset before).val ≠
      6 * (selectorSlot active).val + (selectorOffset active).val :=
  selectorConstant_ne_of_slot_offset_ne
    (selectorSlot before) (selectorSlot active)
    (selectorOffset before) (selectorOffset active)
    (selectorSlotOffset_ne_of_before position)

/-- active より後の selector 定数は、slot/offset 定数一意性により active と異なる。 -/
theorem selectorConstant_ne_of_after {p : QParameters}
    {active after : QSelector p} (position : active.val < after.val) :
    6 * (selectorSlot after).val + (selectorOffset after).val ≠
      6 * (selectorSlot active).val + (selectorOffset active).val :=
  selectorConstant_ne_of_slot_offset_ne
    (selectorSlot after) (selectorSlot active)
    (selectorOffset after) (selectorOffset active)
    (selectorSlotOffset_ne_of_after position)

end ProbabilityGeneratorQProof
