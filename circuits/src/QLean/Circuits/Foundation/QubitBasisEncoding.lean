import QLean.Circuits.Foundation.Foundations

/-!
# little-endian 計算基底と有限添字の標準同値

wire 0 を最下位 bit とする規約で、`QubitBasis q` と `Fin (2 ^ q)` を対応させる。
作用素の両方向 reindex も同じ規約から定義する。
-/

namespace VerifiedCircuitCore

/-- little-endian bit 列を自然数へ変換する。 -/
def qubitBasisLittleEndianIndex : (q : Nat) → QubitBasis q → Nat
  | 0, _ => 0
  | q + 1, basis =>
      Nat.bit (basis 0)
        (qubitBasisLittleEndianIndex q fun wire => basis wire.succ)

/-- `q` bit の little-endian 添字は常に `2 ^ q` 未満である。 -/
theorem qubitBasisLittleEndianIndex_lt : ∀ {q : Nat} (basis : QubitBasis q),
    qubitBasisLittleEndianIndex q basis < 2 ^ q := by
  intro q
  induction q with
  | zero =>
      intro basis
      simp [qubitBasisLittleEndianIndex]
  | succ q inductionHypothesis =>
      intro basis
      have tailBound := inductionHypothesis (fun wire => basis wire.succ)
      cases value : basis 0 <;>
        simp [qubitBasisLittleEndianIndex, value, Nat.pow_succ] <;> omega

/-- 有限添字を little-endian 計算基底へ戻す。 -/
def qubitBasisOfLittleEndianIndex {q : Nat}
    (index : Fin (2 ^ q)) : QubitBasis q :=
  fun wire => index.val.testBit wire.val

/-- bit 列を添字化して戻すと元の bit 列に一致する。 -/
theorem qubitBasisOfLittleEndianIndex_index {q : Nat} (basis : QubitBasis q) :
    qubitBasisOfLittleEndianIndex
      ⟨qubitBasisLittleEndianIndex q basis,
        qubitBasisLittleEndianIndex_lt basis⟩ = basis := by
  funext wire
  induction q with
  | zero => exact Fin.elim0 wire
  | succ q inductionHypothesis =>
      refine Fin.cases ?_ (fun tailWire => ?_) wire
      · simp [qubitBasisOfLittleEndianIndex, qubitBasisLittleEndianIndex]
      · simpa [qubitBasisOfLittleEndianIndex, qubitBasisLittleEndianIndex,
          Nat.testBit_bit_succ] using
          inductionHypothesis (fun inner => basis inner.succ) tailWire

/-- Reading a little-endian encoded natural at an in-range bit recovers the
corresponding computational-basis wire. -/
@[simp] theorem qubitBasisLittleEndianIndex_testBit {q : Nat}
    (basis : QubitBasis q) (wire : Fin q) :
    (qubitBasisLittleEndianIndex q basis).testBit wire.val = basis wire := by
  have recovered := congrFun (qubitBasisOfLittleEndianIndex_index basis) wire
  simpa [qubitBasisOfLittleEndianIndex] using recovered

/-- `2 ^ q` 未満の添字を bit 列化して戻すと元の添字に一致する。 -/
theorem qubitBasisLittleEndianIndex_basis {q : Nat} (index : Fin (2 ^ q)) :
    qubitBasisLittleEndianIndex q (qubitBasisOfLittleEndianIndex index) =
      index.val := by
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases inWidth : bit < q
  · let wire : Fin q := ⟨bit, inWidth⟩
    have recovered := congrFun
      (qubitBasisOfLittleEndianIndex_index
        (qubitBasisOfLittleEndianIndex index)) wire
    simpa [qubitBasisOfLittleEndianIndex, wire] using recovered
  · have widthLe : q ≤ bit := Nat.le_of_not_gt inWidth
    have indexBoundAtBit : index.val < 2 ^ bit :=
      lt_of_lt_of_le index.isLt (Nat.pow_le_pow_right (by decide) widthLe)
    have encodedBoundAtBit :
        qubitBasisLittleEndianIndex q (qubitBasisOfLittleEndianIndex index) <
          2 ^ bit :=
      lt_of_lt_of_le
        (qubitBasisLittleEndianIndex_lt (qubitBasisOfLittleEndianIndex index))
        (Nat.pow_le_pow_right (by decide) widthLe)
    rw [Nat.testBit_eq_false_of_lt encodedBoundAtBit,
      Nat.testBit_eq_false_of_lt indexBoundAtBit]

/-- wire 0 を最下位 bit とする計算基底と `Fin (2 ^ q)` の標準同値。 -/
def qubitBasisLittleEndianEquiv (q : Nat) :
    QubitBasis q ≃ Fin (2 ^ q) where
  toFun basis :=
    ⟨qubitBasisLittleEndianIndex q basis,
      qubitBasisLittleEndianIndex_lt basis⟩
  invFun := qubitBasisOfLittleEndianIndex
  left_inv := qubitBasisOfLittleEndianIndex_index
  right_inv index := Fin.ext (qubitBasisLittleEndianIndex_basis index)

/-- `Fin (2 ^ q)` 上の作用素を little-endian 計算基底上へ reindex する。 -/
noncomputable def reindexOperatorFromLittleEndian {q : Nat}
    (operator : Operator (Fin (2 ^ q))) : Operator (QubitBasis q) :=
  Matrix.reindex (qubitBasisLittleEndianEquiv q).symm
    (qubitBasisLittleEndianEquiv q).symm operator

/-- little-endian 計算基底上の作用素を `Fin (2 ^ q)` 上へ reindex する。 -/
noncomputable def reindexOperatorToLittleEndian {q : Nat}
    (operator : Operator (QubitBasis q)) : Operator (Fin (2 ^ q)) :=
  Matrix.reindex (qubitBasisLittleEndianEquiv q)
    (qubitBasisLittleEndianEquiv q) operator

/-- `Fin` 作用素を計算基底へ移した行列要素の評価式。 -/
@[simp] theorem reindexOperatorFromLittleEndian_apply {q : Nat}
    (operator : Operator (Fin (2 ^ q))) (output input : QubitBasis q) :
    reindexOperatorFromLittleEndian operator output input =
      operator (qubitBasisLittleEndianEquiv q output)
        (qubitBasisLittleEndianEquiv q input) := rfl

/-- 計算基底作用素を `Fin` へ移した行列要素の評価式。 -/
@[simp] theorem reindexOperatorToLittleEndian_apply {q : Nat}
    (operator : Operator (QubitBasis q)) (output input : Fin (2 ^ q)) :
    reindexOperatorToLittleEndian operator output input =
      operator ((qubitBasisLittleEndianEquiv q).symm output)
        ((qubitBasisLittleEndianEquiv q).symm input) := rfl

end VerifiedCircuitCore
