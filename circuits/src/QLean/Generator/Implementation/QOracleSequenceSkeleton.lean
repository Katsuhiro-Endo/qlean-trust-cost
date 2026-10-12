import QLean.Generator.Implementation.QOracleCircuit
import QLean.Generator.Implementation.CircuitSequenceCorrectness

/-!
# Q oracle の全分岐列と最外側 C--U--U 構造

column/row oracle に並ぶ `K × 6` 個の型安全な分岐を名前付きリストとして取り出し、
正本 oracle が persistent decode を compute/uncompute する回路に構文的に一致することを示す。
-/

namespace ProbabilityGeneratorQProof

/-- 全slotの二つの対角分岐と四つのevent分岐を実行順に並べたcolumn分岐列。 -/
def columnOracleBranchList (p : QParameters) :
    List (Circuit (ReversibleGate p.ancillaWidth p.systemWidth)) :=
  (List.finRange p.K).flatMap fun slot =>
    [columnDiagonalResultComputeUseUncomputeCircuit p slot 0, columnDiagonalResultComputeUseUncomputeCircuit p slot 1,
      applyColumnEventReferenceAndRestoreWorkCircuit p slot 2, applyColumnEventReferenceAndRestoreWorkCircuit p slot 3,
      applyColumnEventReferenceAndRestoreWorkCircuit p slot 4, applyColumnEventReferenceAndRestoreWorkCircuit p slot 5]

/-- 全slotの二つの対角分岐と四つのevent分岐を実行順に並べたrow分岐列。 -/
def rowOracleBranchList (p : QParameters) :
    List (Circuit (ReversibleGate p.ancillaWidth p.systemWidth)) :=
  (List.finRange p.K).flatMap fun slot =>
    [rowDiagonalResultComputeUseUncomputeCircuit p slot 0, rowDiagonalResultComputeUseUncomputeCircuit p slot 1,
      applyRowEventReferenceAndRestoreWorkCircuit p slot 2, applyRowEventReferenceAndRestoreWorkCircuit p slot 3,
      applyRowEventReferenceAndRestoreWorkCircuit p slot 4, applyRowEventReferenceAndRestoreWorkCircuit p slot 5]

/-- column oracleの分岐数はpaddingを含むselector数`6K`に厳密一致する。 -/
@[simp] theorem columnOracleBranchList_length (p : QParameters) :
    (columnOracleBranchList p).length = p.selectorCount := by
  simp [columnOracleBranchList, QParameters.selectorCount]
  omega

/-- row oracleの分岐数はpaddingを含むselector数`6K`に厳密一致する。 -/
@[simp] theorem rowOracleBranchList_length (p : QParameters) :
    (rowOracleBranchList p).length = p.selectorCount := by
  simp [rowOracleBranchList, QParameters.selectorCount]
  omega

/-- column正本oracleはpersistent compute、全分岐use、persistent uncomputeのC--U--Uである。 -/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_eq_computeUseUncompute (p : QParameters) :
    applyColumnOracleReferenceAndRestoreWorkCircuit p =
      Circuit.computeUseUncompute id
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false)
        (Circuit.sequence (columnOracleBranchList p)) := by
  rfl

/-- row正本oracleはpersistent compute、全分岐use、persistent uncomputeのC--U--Uである。 -/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_eq_computeUseUncompute (p : QParameters) :
    applyRowOracleReferenceAndRestoreWorkCircuit p =
      Circuit.computeUseUncompute id
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true)
        (Circuit.sequence (rowOracleBranchList p)) := by
  rfl

/-- `6 * slot + offset`符号は`offset < 6`の範囲でslotとoffsetの組を一意に決める。 -/
theorem slot_offset_eq_of_selectorConstant_eq
    {p : QParameters} (leftSlot rightSlot : Fin p.K)
    (leftOffset rightOffset : Fin 6)
    (equal : 6 * leftSlot.val + leftOffset.val =
      6 * rightSlot.val + rightOffset.val) :
    leftSlot = rightSlot ∧ leftOffset = rightOffset := by
  constructor
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

/-- slotまたはoffsetが異なる二分岐のselector定数は異なる。 -/
theorem selectorConstant_ne_of_slot_offset_ne
    {p : QParameters} (leftSlot rightSlot : Fin p.K)
    (leftOffset rightOffset : Fin 6)
    (different : leftSlot ≠ rightSlot ∨ leftOffset ≠ rightOffset) :
    6 * leftSlot.val + leftOffset.val ≠
      6 * rightSlot.val + rightOffset.val := by
  intro equal
  rcases slot_offset_eq_of_selectorConstant_eq leftSlot rightSlot
    leftOffset rightOffset equal with ⟨slotEqual, offsetEqual⟩
  exact different.elim (· slotEqual) (· offsetEqual)

end ProbabilityGeneratorQProof
