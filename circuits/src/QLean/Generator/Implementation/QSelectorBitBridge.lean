import QLean.Generator.Analysis.UniformPreparationQLayout
import QLean.Generator.Implementation.QOracleCorrectness

/-!
# 一様selector値とoracle固定幅bit列の接続

一様準備で使う関数基底`AbstractSelectorBasis`と、可逆oracleが読むlittle-endianの
`constantBits`を接続する。行列や全基底を列挙せず、Natのtest bit外延性だけを使う。
-/

namespace ProbabilityGeneratorQProof

open ReversibleCircuit

/-- 抽象selector基底をwire番号順のBoolリストへ変換する。 -/
def abstractSelectorBits {width : Nat}
    (basis : AbstractSelectorBasis width) : List Bool :=
  List.ofFn basis

/-- 抽象selector bit列の長さはselector幅である。 -/
@[simp] theorem abstractSelectorBits_length
    {width : Nat} (basis : AbstractSelectorBasis width) :
    (abstractSelectorBits basis).length = width := by
  simp [abstractSelectorBits]

/--
容量内の定数について、抽象selector bit列が固定幅定数bit列と一致することと、
`selectorValue`がその定数に等しいことは同値である。
-/
theorem abstractSelectorBits_eq_constantBits_iff
    {width constant : Nat} (basis : AbstractSelectorBasis width)
    (constantInRange : constant < 2 ^ width) :
    abstractSelectorBits basis = constantBits constant width ↔
      selectorValue width basis = constant := by
  constructor
  · intro bitsEqual
    apply Nat.eq_of_testBit_eq
    intro index
    by_cases inRange : index < width
    · let finiteIndex : Fin width := ⟨index, inRange⟩
      have elementEqual := congrArg (fun bits => bits[index]?) bitsEqual
      have basisBit :
          (abstractSelectorBits basis)[index]? = some (basis finiteIndex) := by
        simp [abstractSelectorBits, inRange, finiteIndex]
      have constantBit :
          (constantBits constant width)[index]? =
            some (constant.testBit index) :=
        constantBits_getElem? constant width index inRange
      rw [basisBit, constantBit] at elementEqual
      have decodedBit := selectorValue_testBit width basis finiteIndex
      have bitEqual : basis finiteIndex = constant.testBit index :=
        Option.some.inj elementEqual
      exact decodedBit.trans bitEqual
    · have widthLe : width ≤ index := Nat.le_of_not_gt inRange
      have decodedLt : selectorValue width basis < 2 ^ index :=
        lt_of_lt_of_le (selectorValue_lt_capacity width basis)
          (Nat.pow_le_pow_right (by decide) widthLe)
      have constantLt : constant < 2 ^ index :=
        lt_of_lt_of_le constantInRange
          (Nat.pow_le_pow_right (by decide) widthLe)
      rw [Nat.testBit_lt_two_pow decodedLt, Nat.testBit_lt_two_pow constantLt]
  · intro valueEqual
    apply List.ext_getElem?
    intro index
    by_cases inRange : index < width
    · let finiteIndex : Fin width := ⟨index, inRange⟩
      rw [constantBits_getElem? constant width index inRange]
      simp only [abstractSelectorBits, List.getElem?_ofFn, inRange, dite_true]
      have decodedBit := selectorValue_testBit width basis finiteIndex
      rw [valueEqual] at decodedBit
      have bitEqual : basis finiteIndex = constant.testBit index := decodedBit.symm
      simpa [finiteIndex] using congrArg some bitEqual
    · have leftNone : (abstractSelectorBits basis)[index]? = none := by
        simp [abstractSelectorBits, inRange]
      have rightNone : (constantBits constant width)[index]? = none := by
        apply List.getElem?_eq_none
        simpa [constantBits] using Nat.le_of_not_gt inRange
      rw [leftNone, rightNone]

/-- 物理selector wire列の読出しは、射影した抽象selectorのBool列に一致する。 -/
theorem readWires_selectorSliceWires
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth) :
    ReversibleCircuit.readWires (selectorSliceWires p selectorWire) basis =
      abstractSelectorBits (projectSelectorBasis p selectorWire basis) := by
  apply List.ext_getElem?
  intro index
  by_cases inRange : index < p.selectorWidth
  · simp [ReversibleCircuit.readWires, selectorSliceWires,
      abstractSelectorBits, projectSelectorBasis, inRange]
  · simp [ReversibleCircuit.readWires, selectorSliceWires,
      abstractSelectorBits, inRange]

/--
容量内のselector定数について、物理wire列の固定幅一致条件は射影selector値の一致に等しい。
-/
theorem readWires_selectorSlice_eq_constantBits_iff
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (constant : Nat) (constantInRange : constant < 2 ^ p.selectorWidth) :
    ReversibleCircuit.readWires (selectorSliceWires p selectorWire) basis =
        ReversibleCircuit.constantBits constant p.selectorWidth ↔
      selectorValue p.selectorWidth
          (projectSelectorBasis p selectorWire basis) = constant := by
  rw [readWires_selectorSliceWires]
  exact abstractSelectorBits_eq_constantBits_iff _ constantInRange

/-- 有効selector値は固定幅selector容量内にある。 -/
theorem qSelector_lt_capacity (p : QParameters) (selector : QSelector p) :
    selector.val < 2 ^ p.selectorWidth :=
  lt_of_lt_of_le selector.isLt p.selectorCount_le_capacity

/-- column selector wire列は一般selector slice列のcanonical実体である。 -/
theorem columnSelectorWires_eq_selectorSliceWires (p : QParameters) :
    columnSelectorWires p = selectorSliceWires p (columnSelectorWire p) := by
  rfl

/-- row selector wire列は一般selector slice列のcanonical実体である。 -/
theorem rowSelectorWires_eq_selectorSliceWires (p : QParameters) :
    rowSelectorWires p = selectorSliceWires p (rowSelectorWire p) := by
  rfl

/--
clean scratch上のcolumn selector比較は、射影した抽象selector値が容量内定数に等しいとき
だけselected flagを反転する。
-/
theorem runBasis_columnSelectorEqualsConstant_value
    (p : QParameters) (basis : JointBasis p.ancillaWidth p.systemWidth)
    (constant : Nat) (constantInRange : constant < 2 ^ p.selectorWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, basis wire = false) :
    (selectorEqualsConstant (columnSelectorWires p) (decoderAndScratchWires p)
        constant (oracleSelectedWire p)).runBasis reversibleGatePermutation basis =
      if decide
          (selectorValue p.selectorWidth
            (projectSelectorBasis p (columnSelectorWire p) basis) = constant) then
        xBasisAction (oracleSelectedWire p) basis
      else basis := by
  have result := ReversibleCircuit.runBasis_selectorEqualsConstant_bits
    (columnSelectorWires p) (decoderAndScratchWires p) constant
    (oracleSelectedWire p) basis
    (by simpa [columnSelectorWires] using
      ReversibleCircuit.selectorWidth_le_decoderAndScratch_add_one p)
    (ReversibleCircuit.columnSelector_decoderScratch_selected_nodup p)
    scratchZero
  rw [columnSelectorWires_eq_selectorSliceWires] at result
  have selectorLength :
      (selectorSliceWires p (columnSelectorWire p)).length = p.selectorWidth := by
    simp [selectorSliceWires]
  simp only [selectorLength] at result
  simp only [readWires_selectorSlice_eq_constantBits_iff
    p (columnSelectorWire p) basis constant constantInRange] at result
  simpa [columnSelectorWires_eq_selectorSliceWires] using result

/--
clean scratch上のrow selector比較は、射影した抽象selector値が容量内定数に等しいとき
だけselected flagを反転する。
-/
theorem runBasis_rowSelectorEqualsConstant_value
    (p : QParameters) (basis : JointBasis p.ancillaWidth p.systemWidth)
    (constant : Nat) (constantInRange : constant < 2 ^ p.selectorWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, basis wire = false) :
    (selectorEqualsConstant (rowSelectorWires p) (decoderAndScratchWires p)
        constant (oracleSelectedWire p)).runBasis reversibleGatePermutation basis =
      if decide
          (selectorValue p.selectorWidth
            (projectSelectorBasis p (rowSelectorWire p) basis) = constant) then
        xBasisAction (oracleSelectedWire p) basis
      else basis := by
  have result := ReversibleCircuit.runBasis_selectorEqualsConstant_bits
    (rowSelectorWires p) (decoderAndScratchWires p) constant
    (oracleSelectedWire p) basis
    (by simpa [rowSelectorWires] using
      ReversibleCircuit.selectorWidth_le_decoderAndScratch_add_one p)
    (ReversibleCircuit.rowSelector_decoderScratch_selected_nodup p)
    scratchZero
  rw [rowSelectorWires_eq_selectorSliceWires] at result
  have selectorLength :
      (selectorSliceWires p (rowSelectorWire p)).length = p.selectorWidth := by
    simp [selectorSliceWires]
  simp only [selectorLength] at result
  simp only [readWires_selectorSlice_eq_constantBits_iff
    p (rowSelectorWire p) basis constant constantInRange] at result
  simpa [rowSelectorWires_eq_selectorSliceWires] using result

end ProbabilityGeneratorQProof
