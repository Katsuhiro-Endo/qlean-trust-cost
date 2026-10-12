import QLean.Generator.Analysis.QComponentAnalyticSpecs
import QLean.Generator.Analysis.PrimitiveBasisReferences

/-!
# Q最上位可逆部品の回路非依存な解析置換

COPY、alignment、終端反転を、Bool計算基底上のX/CNOT/Toffoli置換だけから定義する。
ここでは回路構文や回路評価を参照せず、有限な解析置換列の合成だけを扱う。
-/

namespace ProbabilityGeneratorQProof

/-- 解析wireの相異性だけを判定するancilla/system通し番号。 -/
def analyticWireNumber {ancillaQubits systemQubits : Nat} :
    Wire ancillaQubits systemQubits → Nat
  | .ancilla index => index.val
  | .system index => ancillaQubits + index.val

/-- 解析仕様が読むcolumn key wireを、正本layoutだけから定める。 -/
def analyticColumnKeyWire (p : QParameters) (index : Fin p.systemWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).columnKey.ancillaWire index

/-- 解析仕様が読むrow selector wireを、正本layoutだけから定める。 -/
def analyticRowSelectorWire (p : QParameters) (index : Fin p.selectorWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).rowSelector.ancillaWire index

/-- 解析仕様が読むkey signal wireを、正本layoutだけから定める。 -/
def analyticKeySignalWire (p : QParameters) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).keySignal.ancillaWire 0

/-- 解析仕様が読むamplitude signal wireを、正本layoutだけから定める。 -/
def analyticAmplitudeSignalWire (p : QParameters) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).amplitudeSignal.ancillaWire 0

/-- 解析仕様が読むrow output wireを、正本layoutだけから定める。 -/
def analyticRowOutputWire (p : QParameters) (index : Fin p.systemWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).rowOutput.ancillaWire index

/-- 解析仕様が読むselector output wireを、正本layoutだけから定める。 -/
def analyticSelectorOutputWire (p : QParameters) (index : Fin p.selectorWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).selectorOutput.ancillaWire index

/-- 解析amplitude signalとcolumn keyの各wireは異なる。 -/
theorem analyticAmplitudeSignalWire_ne_columnKeyWire
    (p : QParameters) (index : Fin p.systemWidth) :
    analyticAmplitudeSignalWire p ≠ analyticColumnKeyWire p index := by
  intro equal
  have values := congrArg analyticWireNumber equal
  simp [analyticAmplitudeSignalWire, analyticColumnKeyWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, analyticWireNumber] at values
  omega

/-- 解析amplitude signalとrow outputの各wireは異なる。 -/
theorem analyticAmplitudeSignalWire_ne_rowOutputWire
    (p : QParameters) (index : Fin p.systemWidth) :
    analyticAmplitudeSignalWire p ≠ analyticRowOutputWire p index := by
  intro equal
  have values := congrArg analyticWireNumber equal
  simp [analyticAmplitudeSignalWire, analyticRowOutputWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, analyticWireNumber] at values
  omega

/-- 解析amplitude signalとselector outputの各wireは異なる。 -/
theorem analyticAmplitudeSignalWire_ne_selectorOutputWire
    (p : QParameters) (index : Fin p.selectorWidth) :
    analyticAmplitudeSignalWire p ≠ analyticSelectorOutputWire p index := by
  intro equal
  have values := congrArg analyticWireNumber equal
  simp [analyticAmplitudeSignalWire, analyticSelectorOutputWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, analyticWireNumber] at values
  omega

/-- 解析amplitude signalとrow selectorの各wireは異なる。 -/
theorem analyticAmplitudeSignalWire_ne_rowSelectorWire
    (p : QParameters) (index : Fin p.selectorWidth) :
    analyticAmplitudeSignalWire p ≠ analyticRowSelectorWire p index := by
  intro equal
  have values := congrArg analyticWireNumber equal
  simp [analyticAmplitudeSignalWire, analyticRowSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, analyticWireNumber] at values
  omega

/-- 解析amplitude signalとkey signalのwireは異なる。 -/
theorem analyticAmplitudeSignalWire_ne_keySignalWire
    (p : QParameters) :
    analyticAmplitudeSignalWire p ≠ analyticKeySignalWire p := by
  intro equal
  have values := congrArg analyticWireNumber equal
  simp [analyticAmplitudeSignalWire, analyticKeySignalWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, analyticWireNumber] at values

/-- 解析selector outputとrow selectorの対応wireは異なる。 -/
theorem analyticSelectorOutputWire_ne_rowSelectorWire
    (p : QParameters) (index : Fin p.selectorWidth) :
    analyticSelectorOutputWire p index ≠ analyticRowSelectorWire p index := by
  intro equal
  have values := congrArg analyticWireNumber equal
  simp [analyticSelectorOutputWire, analyticRowSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, analyticWireNumber] at values
  omega

/-- 実行順に並んだ解析置換を、一個の基底置換へ合成する。 -/
def analyticPermutationSequence {basis : Type*} :
    List (Equiv.Perm basis) → Equiv.Perm basis
  | [] => 1
  | first :: rest => analyticPermutationSequence rest * first

/-- 解析置換列の作用は、先頭置換の後に残りの置換列を作用させる。 -/
@[simp] theorem analyticPermutationSequence_cons_apply
    {basis : Type*} (first : Equiv.Perm basis)
    (rest : List (Equiv.Perm basis)) (input : basis) :
    analyticPermutationSequence (first :: rest) input =
      analyticPermutationSequence rest (first input) := by
  rfl

/-- systemからcolumn keyへの各bitwise XORを表すCNOT基底置換列。 -/
def xorSystemIntoColumnKeyAnalyticSteps (p : QParameters) :
    List (Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth)) :=
  (List.finRange p.systemWidth).map fun index =>
    cnotBasisEquiv (.system index) (analyticColumnKeyWire p index) (by
      intro equal
      cases equal)

/-- systemからcolumn keyへのbitwise XORを表す回路非依存な解析置換。 -/
def xorSystemIntoColumnKeyAnalyticPermutation (p : QParameters) :
    Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth) :=
  analyticPermutationSequence (xorSystemIntoColumnKeyAnalyticSteps p)

/-- amplitude signal制御でcolumn keyをsystemへXORする解析Toffoli列。 -/
def controlledXorColumnKeyIntoSystemAnalyticSteps (p : QParameters) :
    List (Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth)) :=
  (List.finRange p.systemWidth).map fun index =>
    toffoliBasisEquiv (analyticAmplitudeSignalWire p) (analyticColumnKeyWire p index)
      (.system index)
      (analyticAmplitudeSignalWire_ne_columnKeyWire p index)
      (by intro equal; cases equal)
      (by intro equal; cases equal)

/-- amplitude signal制御でrow outputをsystemへXORする解析Toffoli列。 -/
def controlledXorRowOutputIntoSystemAnalyticSteps (p : QParameters) :
    List (Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth)) :=
  (List.finRange p.systemWidth).map fun index =>
    toffoliBasisEquiv (analyticAmplitudeSignalWire p) (analyticRowOutputWire p index)
      (.system index)
      (analyticAmplitudeSignalWire_ne_rowOutputWire p index)
      (by intro equal; cases equal)
      (by intro equal; cases equal)

/-- amplitude signal制御でselector outputをrow selectorへXORする解析Toffoli列。 -/
def controlledXorSelectorOutputIntoRowSelectorAnalyticSteps (p : QParameters) :
    List (Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth)) :=
  (List.finRange p.selectorWidth).map fun index =>
    toffoliBasisEquiv (analyticAmplitudeSignalWire p)
      (analyticSelectorOutputWire p index)
      (analyticRowSelectorWire p index)
      (analyticAmplitudeSignalWire_ne_selectorOutputWire p index)
      (analyticAmplitudeSignalWire_ne_rowSelectorWire p index)
      (analyticSelectorOutputWire_ne_rowSelectorWire p index)

/-- alignment終端でamplitude signalをkey signalへXORする解析CNOT置換。 -/
def xorAmplitudeSignalIntoKeySignalAnalyticStep (p : QParameters) :
    Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth) :=
  cnotBasisEquiv (analyticAmplitudeSignalWire p) (analyticKeySignalWire p)
    (analyticAmplitudeSignalWire_ne_keySignalWire p)

/-- alignment全体を表す回路非依存な解析置換。 -/
def controlledXorOracleOutputsIntoAlignedRegistersAnalyticPermutation (p : QParameters) :
    Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth) :=
  xorAmplitudeSignalIntoKeySignalAnalyticStep p *
    (analyticPermutationSequence (controlledXorSelectorOutputIntoRowSelectorAnalyticSteps p) *
      (analyticPermutationSequence (controlledXorRowOutputIntoSystemAnalyticSteps p) *
        analyticPermutationSequence (controlledXorColumnKeyIntoSystemAnalyticSteps p)))

/-- 終端amplitude反転を表す回路非依存な解析X置換。 -/
def flipAmplitudeSignalAnalyticPermutation (p : QParameters) :
    Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth) :=
  xBasisEquiv (analyticAmplitudeSignalWire p)

end ProbabilityGeneratorQProof
