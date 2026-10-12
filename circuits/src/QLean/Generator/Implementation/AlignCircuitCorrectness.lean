import QLean.Generator.Implementation.AmplitudeDiscriminatorCorrectness

/-!
# 整列回路と終端反転の可逆基底意味論

量子位相回路の前後にある`C_align`と終端Xを、任意幅の計算基底置換として扱う。
-/

namespace ProbabilityGeneratorQProof

open ReversibleCircuit

/-- column keyをsystemへactive制御XORする可逆回路。 -/
def controlledXorColumnKeyIntoSystemReversibleCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  Circuit.fromList <| (List.finRange p.systemWidth).map fun index =>
    ReversibleGate.toffoli (amplitudeSignalWire p) (columnKeyWire p index)
      (.system index)
      (amplitudeSignalWire_ne_columnKeyWire p index)
      (by intro equal; cases equal)
      (by intro equal; cases equal)

/-- row outputをsystemへactive制御XORする可逆回路。 -/
def controlledXorRowOutputIntoSystemReversibleCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  Circuit.fromList <| (List.finRange p.systemWidth).map fun index =>
    ReversibleGate.toffoli (amplitudeSignalWire p) (rowOutputWire p index)
      (.system index)
      (amplitudeSignalWire_ne_rowOutputWire p index)
      (by intro equal; cases equal)
      (by intro equal; cases equal)

/-- selector outputをrow selectorへactive制御XORする可逆回路。 -/
def controlledXorSelectorOutputIntoRowSelectorReversibleCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  Circuit.fromList <| (List.finRange p.selectorWidth).map fun index =>
    ReversibleGate.toffoli (amplitudeSignalWire p) (selectorOutputWire p index)
      (rowSelectorWire p index)
      (amplitudeSignalWire_ne_selectorOutputWire p index)
      (amplitudeSignalWire_ne_rowSelectorWire p index)
      (selectorOutputWire_ne_rowSelectorWire p index)

/-- `C_align`全体の可逆計算基底回路。 -/
def controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .seq (controlledXorColumnKeyIntoSystemReversibleCircuit p) <|
  .seq (controlledXorRowOutputIntoSystemReversibleCircuit p) <|
  .seq (controlledXorSelectorOutputIntoRowSelectorReversibleCircuit p) <|
  .gate (.cnot (amplitudeSignalWire p) (keySignalWire p)
    (amplitudeSignalWire_ne_keySignalWire p))

/-- 終端amplitude反転の可逆計算基底回路。 -/
def flipAmplitudeSignalReversibleCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .gate (.x (amplitudeSignalWire p))

/-- column key整列の正本基本ゲート列は可逆回路翻訳そのものである。 -/
theorem controlledXorColumnKeyIntoSystemCircuit_eq_reversible (p : QParameters) :
    controlledXorColumnKeyIntoSystemCircuit p =
      ReversibleCircuit.toPrimitive (controlledXorColumnKeyIntoSystemReversibleCircuit p) := by
  unfold controlledXorColumnKeyIntoSystemCircuit
  unfold controlledXorColumnKeyIntoSystemReversibleCircuit ReversibleCircuit.toPrimitive
  rw [Circuit.map_fromList]
  simp [List.map_map, Function.comp_def, ReversibleGate.toPrimitive]

/-- row output整列の正本基本ゲート列は可逆回路翻訳そのものである。 -/
theorem controlledXorRowOutputIntoSystemCircuit_eq_reversible (p : QParameters) :
    controlledXorRowOutputIntoSystemCircuit p =
      ReversibleCircuit.toPrimitive (controlledXorRowOutputIntoSystemReversibleCircuit p) := by
  unfold controlledXorRowOutputIntoSystemCircuit
  unfold controlledXorRowOutputIntoSystemReversibleCircuit ReversibleCircuit.toPrimitive
  rw [Circuit.map_fromList]
  simp [List.map_map, Function.comp_def, ReversibleGate.toPrimitive]

/-- selector整列の正本基本ゲート列は可逆回路翻訳そのものである。 -/
theorem controlledXorSelectorOutputIntoRowSelectorCircuit_eq_reversible (p : QParameters) :
    controlledXorSelectorOutputIntoRowSelectorCircuit p =
      ReversibleCircuit.toPrimitive (controlledXorSelectorOutputIntoRowSelectorReversibleCircuit p) := by
  unfold controlledXorSelectorOutputIntoRowSelectorCircuit
  unfold controlledXorSelectorOutputIntoRowSelectorReversibleCircuit ReversibleCircuit.toPrimitive
  rw [Circuit.map_fromList]
  simp [List.map_map, Function.comp_def, ReversibleGate.toPrimitive]

/-- `C_align`正本回路全体は可逆基底回路の基本ゲート翻訳に一致する。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_eq_reversible (p : QParameters) :
    controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p = ReversibleCircuit.toPrimitive (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p) := by
  simp only [controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit, controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit, ReversibleCircuit.toPrimitive,
    Circuit.map]
  rw [controlledXorColumnKeyIntoSystemCircuit_eq_reversible,
    controlledXorRowOutputIntoSystemCircuit_eq_reversible,
    controlledXorSelectorOutputIntoRowSelectorCircuit_eq_reversible]
  rfl

/-- 終端X正本回路は可逆基底回路の基本ゲート翻訳に一致する。 -/
theorem flipAmplitudeSignalPrimitiveCircuit_eq_reversible (p : QParameters) :
    flipAmplitudeSignalPrimitiveCircuit p =
      ReversibleCircuit.toPrimitive (flipAmplitudeSignalReversibleCircuit p) := by
  rfl

/-- `C_align`の行列意味論は、基底実行関数が与える置換行列である。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_operator_eq_permMatrix (p : QParameters) :
    (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p).toIdealOperator primitiveGateOperator =
      ((controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).toBasisPermutation reversibleGatePermutation).permMatrix ℂ := by
  rw [controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_eq_reversible]
  exact ReversibleCircuit.toPrimitive_operator_eq_permMatrix _

/-- `C_align`の各基底振幅は一意な基底遷移だけで1になる。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_basisAmplitude
    (p : QParameters)
    (input output : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p).toIdealOperator primitiveGateOperator output input =
      if output = (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input
      then 1 else 0 := by
  rw [controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_eq_reversible]
  exact reversibleCircuit_basisAmplitude _ _ _

/-- 終端Xの各基底振幅は一意な基底反転だけで1になる。 -/
theorem flipAmplitudeSignalPrimitiveCircuit_basisAmplitude
    (p : QParameters)
    (input output : JointBasis p.ancillaWidth p.systemWidth) :
    (flipAmplitudeSignalPrimitiveCircuit p).toIdealOperator primitiveGateOperator output input =
      if output =
          (flipAmplitudeSignalReversibleCircuit p).runBasis
            reversibleGatePermutation input
      then 1 else 0 := by
  rw [flipAmplitudeSignalPrimitiveCircuit_eq_reversible]
  exact reversibleCircuit_basisAmplitude _ _ _

end ProbabilityGeneratorQProof
