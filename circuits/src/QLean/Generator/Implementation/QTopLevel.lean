import QLean.Generator.Implementation.CircuitUtilities
import QLean.Generator.Analysis.QParameters

/-!
# Q回路最上位の明示的な基本ゲート部品

COPY、振幅判別`D_amp`、active制御の整列`C_align`、最終Xを、すべて
`X/H/Ry/CNOT/Toffoli`の葉だけからなる正本回路として構成する。
-/

namespace ProbabilityGeneratorQProof

open QParameters

/-- 型安全なQ layoutのcolumn key wire。 -/
def columnKeyWire (p : QParameters) (index : Fin p.systemWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).columnKey.ancillaWire index

/-- 型安全なQ layoutのrow selector wire。 -/
def rowSelectorWire (p : QParameters) (index : Fin p.selectorWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).rowSelector.ancillaWire index

/-- 型安全なQ layoutのcolumn selector wire。 -/
def columnSelectorWire (p : QParameters) (index : Fin p.selectorWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).columnSelector.ancillaWire index

/-- 型安全なQ layoutのkey signal wire。 -/
def keySignalWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).keySignal.ancillaWire 0

/-- 型安全なQ layoutのamplitude signal wire。 -/
def amplitudeSignalWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).amplitudeSignal.ancillaWire 0

/-- 型安全なQ layoutのrow output wire。 -/
def rowOutputWire (p : QParameters) (index : Fin p.systemWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).rowOutput.ancillaWire index

/-- 型安全なQ layoutのselector output wire。 -/
def selectorOutputWire (p : QParameters) (index : Fin p.selectorWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).selectorOutput.ancillaWire index

/-- 型安全なQ layoutのnegative flag wire。 -/
def negativeWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).negative.ancillaWire 0

/-- 型安全なQ layoutのactive flag wire。 -/
def activeWire (p : QParameters) : Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).active.ancillaWire 0

/-- wireの相異性証明で使う全体通し番号。 -/
def wireNumber {ancillaQubits systemQubits : Nat} :
    Wire ancillaQubits systemQubits → Nat
  | .ancilla index => index.val
  | .system index => ancillaQubits + index.val

/-- active flagとamplitude signalは異なるwireである。 -/
theorem activeWire_ne_amplitudeSignalWire (p : QParameters) :
    activeWire p ≠ amplitudeSignalWire p := by
  intro equal
  have values := congrArg wireNumber equal
  simp [activeWire, amplitudeSignalWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber,
    QParameters.systemWidth] at values
  omega

/-- negative flagとamplitude signalは異なるwireである。 -/
theorem negativeWire_ne_amplitudeSignalWire (p : QParameters) :
    negativeWire p ≠ amplitudeSignalWire p := by
  intro equal
  have values := congrArg wireNumber equal
  simp [negativeWire, amplitudeSignalWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber,
    QParameters.systemWidth] at values
  omega

/-- amplitude signalとkey signalは異なるwireである。 -/
theorem amplitudeSignalWire_ne_keySignalWire (p : QParameters) :
    amplitudeSignalWire p ≠ keySignalWire p := by
  intro equal
  have values := congrArg wireNumber equal
  simp [amplitudeSignalWire, keySignalWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at values

/-- system配置をcolumn keyへbitwise XOR copyする基本ゲート回路。 -/
def xorSystemIntoColumnKeyPrimitiveCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  Circuit.fromList <| (List.finRange p.systemWidth).map fun index =>
    PrimitiveGate.cnot (.system index) (columnKeyWire p index) (by
      intro equal
      cases equal)

/-- activeとnegativeを符号付きamplitude signalへ変換する4ゲート回路。 -/
def copyActiveIntoAmplitudeAndPhaseByNegativeCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  Circuit.fromList
    [PrimitiveGate.cnot (activeWire p) (amplitudeSignalWire p)
        (activeWire_ne_amplitudeSignalWire p),
      PrimitiveGate.h (amplitudeSignalWire p),
      PrimitiveGate.cnot (negativeWire p) (amplitudeSignalWire p)
        (negativeWire_ne_amplitudeSignalWire p),
      PrimitiveGate.h (amplitudeSignalWire p)]

/-- amplitude signalとcolumn keyの各wireは異なる。 -/
theorem amplitudeSignalWire_ne_columnKeyWire
    (p : QParameters) (index : Fin p.systemWidth) :
    amplitudeSignalWire p ≠ columnKeyWire p index := by
  intro equal
  have values := congrArg wireNumber equal
  simp [amplitudeSignalWire, columnKeyWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at values
  omega

/-- amplitude signalとrow outputの各wireは異なる。 -/
theorem amplitudeSignalWire_ne_rowOutputWire
    (p : QParameters) (index : Fin p.systemWidth) :
    amplitudeSignalWire p ≠ rowOutputWire p index := by
  intro equal
  have values := congrArg wireNumber equal
  simp [amplitudeSignalWire, rowOutputWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at values
  omega

/-- amplitude signalとselector outputの各wireは異なる。 -/
theorem amplitudeSignalWire_ne_selectorOutputWire
    (p : QParameters) (index : Fin p.selectorWidth) :
    amplitudeSignalWire p ≠ selectorOutputWire p index := by
  intro equal
  have values := congrArg wireNumber equal
  simp [amplitudeSignalWire, selectorOutputWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at values
  omega

/-- amplitude signalとrow selectorの各wireは異なる。 -/
theorem amplitudeSignalWire_ne_rowSelectorWire
    (p : QParameters) (index : Fin p.selectorWidth) :
    amplitudeSignalWire p ≠ rowSelectorWire p index := by
  intro equal
  have values := congrArg wireNumber equal
  simp [amplitudeSignalWire, rowSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at values
  omega

/-- selector outputとrow selectorの対応wireは異なる。 -/
theorem selectorOutputWire_ne_rowSelectorWire
    (p : QParameters) (index : Fin p.selectorWidth) :
    selectorOutputWire p index ≠ rowSelectorWire p index := by
  intro equal
  have values := congrArg wireNumber equal
  simp [selectorOutputWire, rowSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at values
  omega

/-- active branchで`E ^= C_key`を行うToffoli列。 -/
def controlledXorColumnKeyIntoSystemCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  Circuit.fromList <| (List.finRange p.systemWidth).map fun index =>
    PrimitiveGate.toffoli (amplitudeSignalWire p) (columnKeyWire p index)
      (.system index)
      (amplitudeSignalWire_ne_columnKeyWire p index)
      (by intro equal; cases equal)
      (by intro equal; cases equal)

/-- active branchで`E ^= R_out`を行うToffoli列。 -/
def controlledXorRowOutputIntoSystemCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  Circuit.fromList <| (List.finRange p.systemWidth).map fun index =>
    PrimitiveGate.toffoli (amplitudeSignalWire p) (rowOutputWire p index)
      (.system index)
      (amplitudeSignalWire_ne_rowOutputWire p index)
      (by intro equal; cases equal)
      (by intro equal; cases equal)

/-- active branchで`L_row ^= L_out`を行うToffoli列。 -/
def controlledXorSelectorOutputIntoRowSelectorCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  Circuit.fromList <| (List.finRange p.selectorWidth).map fun index =>
    PrimitiveGate.toffoli (amplitudeSignalWire p) (selectorOutputWire p index)
      (rowSelectorWire p index)
      (amplitudeSignalWire_ne_selectorOutputWire p index)
      (amplitudeSignalWire_ne_rowSelectorWire p index)
      (selectorOutputWire_ne_rowSelectorWire p index)

/-- `C_align`全体を技術レポートの実行順で合成する。 -/
def controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  .seq (controlledXorColumnKeyIntoSystemCircuit p) <|
  .seq (controlledXorRowOutputIntoSystemCircuit p) <|
  .seq (controlledXorSelectorOutputIntoRowSelectorCircuit p) <|
  .gate (.cnot (amplitudeSignalWire p) (keySignalWire p)
    (amplitudeSignalWire_ne_keySignalWire p))

/-- 終端でactive amplitude signalを反転して成功値を0へ戻すX回路。 -/
def flipAmplitudeSignalPrimitiveCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  .gate (.x (amplitudeSignalWire p))

/-- COPY、`D_amp`、`C_align`、最終Xはいずれもユニタリである。 -/
theorem explicitTopLevelComponents_unitary (p : QParameters) :
    (xorSystemIntoColumnKeyPrimitiveCircuit p).toIdealOperator primitiveGateOperator ∈
        Matrix.unitaryGroup (JointBasis p.ancillaWidth p.systemWidth) ℂ ∧
    (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).toIdealOperator primitiveGateOperator ∈
        Matrix.unitaryGroup (JointBasis p.ancillaWidth p.systemWidth) ℂ ∧
    (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p).toIdealOperator primitiveGateOperator ∈
        Matrix.unitaryGroup (JointBasis p.ancillaWidth p.systemWidth) ℂ ∧
    (flipAmplitudeSignalPrimitiveCircuit p).toIdealOperator primitiveGateOperator ∈
        Matrix.unitaryGroup (JointBasis p.ancillaWidth p.systemWidth) ℂ := by
  constructor
  · exact primitiveCircuit_mem_unitaryGroup _
  constructor
  · exact primitiveCircuit_mem_unitaryGroup _
  constructor <;> exact primitiveCircuit_mem_unitaryGroup _

end ProbabilityGeneratorQProof
