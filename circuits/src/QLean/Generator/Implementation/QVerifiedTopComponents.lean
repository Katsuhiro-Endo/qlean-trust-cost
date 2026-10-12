import QLean.Generator.Implementation.ComponentCombinators
import QLean.Generator.Analysis.QTopLevelAnalyticSpecs
import QLean.Generator.Implementation.QTopLevelCorrectness
import QLean.Generator.Implementation.QTopLevelSharedCoreCopyAdapter
import QLean.Generator.Implementation.AlignCircuitCorrectness

/-!
# Q回路最上位部品の解析仕様付きcomponent

system-to-column-key COPY、振幅判定、整列、終端反転を、実装回路とは独立な
置換または解析作用素と対応付ける。可逆部品では参照用可逆回路の基底置換を先に証明し、
正本の基本ゲート回路にはその逆置換行列を目標とする全作用素契約を与える。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

/-- ゲート列の基底実行は、各葉の解析置換列を実行順に合成した作用と一致する。 -/
theorem runBasis_fromList_eq_analyticPermutationSequence
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (gates : List Gate) (input : basis) :
    (Circuit.fromList gates).runBasis gatePermutation input =
      analyticPermutationSequence (gates.map gatePermutation) input := by
  rw [Circuit.runBasis_fromList]
  induction gates generalizing input with
  | nil => rfl
  | cons gate gates inductionHypothesis =>
      exact inductionHypothesis (gatePermutation gate input)

/-- COPY参照回路を同じ実行順の可逆CNOT葉リストとして表す。 -/
theorem xorSystemIntoColumnKeyReversibleCircuit_eq_fromList (p : QParameters) :
    xorSystemIntoColumnKeyReversibleCircuit p =
      Circuit.fromList ((List.finRange p.systemWidth).map fun index =>
        ReversibleGate.cnot (.system index) (columnKeyWire p index) (by
          intro equal
          cases equal)) := by
  let indices := List.finRange p.systemWidth
  change ReversibleCircuit.xorCopy
      (indices.map Wire.system) (indices.map (columnKeyWire p)) =
    Circuit.fromList (indices.map fun index =>
      ReversibleGate.cnot (.system index) (columnKeyWire p index) _)
  induction indices with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      have different :
          (Wire.system index : Wire p.ancillaWidth p.systemWidth) ≠
            columnKeyWire p index := by
        intro equal
        cases equal
      simp [ReversibleCircuit.xorCopy, ReversibleCircuit.safeCnot,
        Circuit.fromList, VerifiedCircuitCore.Circuit.fromList,
        different, inductionHypothesis]

/-- COPY参照回路の基底作用は、回路非依存な解析COPY置換に一致する。 -/
theorem xorSystemIntoColumnKeyReversibleCircuit_runBasis_eq_analytic
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
        reversibleGatePermutation input =
      xorSystemIntoColumnKeyAnalyticPermutation p input := by
  rw [xorSystemIntoColumnKeyReversibleCircuit_eq_fromList]
  rw [runBasis_fromList_eq_analyticPermutationSequence]
  unfold xorSystemIntoColumnKeyAnalyticPermutation
  unfold xorSystemIntoColumnKeyAnalyticSteps
  congr 1
  simp [List.map_map, Function.comp_def, reversibleGatePermutation,
    analyticColumnKeyWire, columnKeyWire]

/-- COPY参照回路の実行置換そのものが解析COPY置換に一致する。 -/
theorem xorSystemIntoColumnKeyReversibleCircuit_execution_eq_analytic
    (p : QParameters) :
    (xorSystemIntoColumnKeyReversibleCircuit p).toExecutionPermutation
        reversibleGatePermutation =
      xorSystemIntoColumnKeyAnalyticPermutation p := by
  apply Equiv.ext
  intro input
  exact xorSystemIntoColumnKeyReversibleCircuit_runBasis_eq_analytic p input

/-- column-key整列参照回路の基底作用は、対応する解析Toffoli列に一致する。 -/
theorem controlledXorColumnKeyIntoSystemReversibleCircuit_runBasis_eq_analytic
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledXorColumnKeyIntoSystemReversibleCircuit p).runBasis
        reversibleGatePermutation input =
      analyticPermutationSequence (controlledXorColumnKeyIntoSystemAnalyticSteps p) input := by
  unfold controlledXorColumnKeyIntoSystemReversibleCircuit
  rw [runBasis_fromList_eq_analyticPermutationSequence]
  unfold controlledXorColumnKeyIntoSystemAnalyticSteps
  congr 1
  simp [List.map_map, Function.comp_def, reversibleGatePermutation,
    analyticAmplitudeSignalWire, analyticColumnKeyWire,
    amplitudeSignalWire, columnKeyWire]

/-- row-output整列参照回路の基底作用は、対応する解析Toffoli列に一致する。 -/
theorem controlledXorRowOutputIntoSystemReversibleCircuit_runBasis_eq_analytic
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledXorRowOutputIntoSystemReversibleCircuit p).runBasis
        reversibleGatePermutation input =
      analyticPermutationSequence (controlledXorRowOutputIntoSystemAnalyticSteps p) input := by
  unfold controlledXorRowOutputIntoSystemReversibleCircuit
  rw [runBasis_fromList_eq_analyticPermutationSequence]
  unfold controlledXorRowOutputIntoSystemAnalyticSteps
  congr 1
  simp [List.map_map, Function.comp_def, reversibleGatePermutation,
    analyticAmplitudeSignalWire, analyticRowOutputWire,
    amplitudeSignalWire, rowOutputWire]

/-- selector整列参照回路の基底作用は、対応する解析Toffoli列に一致する。 -/
theorem controlledXorSelectorOutputIntoRowSelectorReversibleCircuit_runBasis_eq_analytic
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledXorSelectorOutputIntoRowSelectorReversibleCircuit p).runBasis
        reversibleGatePermutation input =
      analyticPermutationSequence (controlledXorSelectorOutputIntoRowSelectorAnalyticSteps p) input := by
  unfold controlledXorSelectorOutputIntoRowSelectorReversibleCircuit
  rw [runBasis_fromList_eq_analyticPermutationSequence]
  unfold controlledXorSelectorOutputIntoRowSelectorAnalyticSteps
  congr 1
  simp [List.map_map, Function.comp_def, reversibleGatePermutation,
    analyticAmplitudeSignalWire, analyticSelectorOutputWire,
    analyticRowSelectorWire, amplitudeSignalWire, selectorOutputWire,
    rowSelectorWire]

/-- alignment参照回路全体の基底作用は、回路非依存な解析alignment置換に一致する。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_eq_analytic
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input =
      controlledXorOracleOutputsIntoAlignedRegistersAnalyticPermutation p input := by
  change
    cnotBasisEquiv (amplitudeSignalWire p) (keySignalWire p)
        (amplitudeSignalWire_ne_keySignalWire p)
      ((controlledXorSelectorOutputIntoRowSelectorReversibleCircuit p).runBasis
        reversibleGatePermutation
        ((controlledXorRowOutputIntoSystemReversibleCircuit p).runBasis
          reversibleGatePermutation
          ((controlledXorColumnKeyIntoSystemReversibleCircuit p).runBasis
            reversibleGatePermutation input))) = _
  rw [controlledXorColumnKeyIntoSystemReversibleCircuit_runBasis_eq_analytic]
  rw [controlledXorRowOutputIntoSystemReversibleCircuit_runBasis_eq_analytic]
  rw [controlledXorSelectorOutputIntoRowSelectorReversibleCircuit_runBasis_eq_analytic]
  rfl

/-- alignment参照回路の実行置換そのものが解析alignment置換に一致する。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_execution_eq_analytic (p : QParameters) :
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).toExecutionPermutation reversibleGatePermutation =
      controlledXorOracleOutputsIntoAlignedRegistersAnalyticPermutation p := by
  apply Equiv.ext
  intro input
  exact controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_eq_analytic p input

/-- 終端反転参照回路の基底作用は、回路非依存な解析X置換に一致する。 -/
theorem flipAmplitudeSignalReversibleCircuit_runBasis_eq_analytic
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    (flipAmplitudeSignalReversibleCircuit p).runBasis
        reversibleGatePermutation input =
      flipAmplitudeSignalAnalyticPermutation p input := by
  rfl

/-- 終端反転参照回路の実行置換そのものが解析X置換に一致する。 -/
theorem flipAmplitudeSignalReversibleCircuit_execution_eq_analytic
    (p : QParameters) :
    (flipAmplitudeSignalReversibleCircuit p).toExecutionPermutation
        reversibleGatePermutation =
      flipAmplitudeSignalAnalyticPermutation p := by
  apply Equiv.ext
  intro input
  exact flipAmplitudeSignalReversibleCircuit_runBasis_eq_analytic p input

/-- COPYの回路非依存な解析的基底置換。 -/
def xorSystemIntoColumnKeyPermutation (p : QParameters) :
    Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth) :=
  xorSystemIntoColumnKeyAnalyticPermutation p

/-- COPY参照回路を、その基底作用と逆置換行列へ結び付ける置換部品。 -/
def xorSystemIntoColumnKeyPermutationComponent (p : QParameters) :
    PermutationComponent
      (fun gate : ReversibleGate p.ancillaWidth p.systemWidth =>
        (reversibleGatePermutation gate).permMatrix ℂ)
      reversibleGatePermutation :=
  PermutationComponent.ofInvolutiveCircuit
    (fun gate : ReversibleGate p.ancillaWidth p.systemWidth =>
      (reversibleGatePermutation gate).permMatrix ℂ)
    reversibleGatePermutation
    (by intro gate; cases gate <;> rfl)
    (by intro gate; rfl)
    (xorSystemIntoColumnKeyReversibleCircuit p)
    (xorSystemIntoColumnKeyPermutation p)
    (xorSystemIntoColumnKeyReversibleCircuit_runBasis_eq_analytic p)

/-- COPY参照回路を、全入力上のclean基底変換として再利用する部品。 -/
def xorSystemIntoColumnKeyCleanComponent (p : QParameters) :
    CleanComponent
      (reversibleGatePermutation :
        ReversibleGate p.ancillaWidth p.systemWidth →
          Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth)) :=
  CleanComponent.ofPermutation (xorSystemIntoColumnKeyPermutationComponent p)

/-- 正本COPY回路に対応する、参照置換だけから定義した解析的全作用素。 -/
def XorSystemIntoColumnKeyTargetOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  reindexCanonicalCoreOperatorToJoint
    (VerifiedCircuitCore.registerXorCopyPureOperator
      (systemIntoColumnKeyCoreRegisterXorCopySpec p))

/-- 正本COPY基本ゲート回路が解析的COPY作用素へ厳密一致する全作用素部品。 -/
def xorSystemIntoColumnKeyExactOperatorComponent (p : QParameters) :
    ExactOperatorComponent
      (primitiveGateOperator :
        PrimitiveGate p.ancillaWidth p.systemWidth →
          Operator (JointBasis p.ancillaWidth p.systemWidth)) :=
  xorSystemIntoColumnKeySharedCoreExactOperatorComponent p

/-- 振幅判定回路が表すCZとactive制御CNOTの解析的積作用素。 -/
def ActiveCopyNegativePhaseTargetOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  onTwoWires (negativeWire p) (amplitudeSignalWire p)
      (negativeWire_ne_amplitudeSignalWire p) localControlledZMatrix *
    cnotMatrix (activeWire p) (amplitudeSignalWire p)
      (activeWire_ne_amplitudeSignalWire p)

/-- 振幅判定の正本基本ゲート回路が解析的CZ-CNOT作用素へ一致する全作用素部品。 -/
def activeCopyNegativePhaseExactOperatorComponent (p : QParameters) :
    ExactOperatorComponent
      (primitiveGateOperator :
        PrimitiveGate p.ancillaWidth p.systemWidth →
          Operator (JointBasis p.ancillaWidth p.systemWidth)) where
  circuit := copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p
  target := ActiveCopyNegativePhaseTargetOperator p
  correct := by
    exact copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_operator p

/-- alignmentの回路非依存な解析的基底置換。 -/
def controlledXorOracleOutputsIntoAlignedRegistersPermutation (p : QParameters) :
    Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth) :=
  controlledXorOracleOutputsIntoAlignedRegistersAnalyticPermutation p

/-- 整列参照回路を、その基底作用と逆置換行列へ結び付ける置換部品。 -/
def controlledOracleOutputAlignmentPermutationComponent (p : QParameters) :
    PermutationComponent
      (fun gate : ReversibleGate p.ancillaWidth p.systemWidth =>
        (reversibleGatePermutation gate).permMatrix ℂ)
      reversibleGatePermutation :=
  PermutationComponent.ofInvolutiveCircuit
    (fun gate : ReversibleGate p.ancillaWidth p.systemWidth =>
      (reversibleGatePermutation gate).permMatrix ℂ)
    reversibleGatePermutation
    (by intro gate; cases gate <;> rfl)
    (by intro gate; rfl)
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p)
    (controlledXorOracleOutputsIntoAlignedRegistersPermutation p)
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_eq_analytic p)

/-- 整列参照回路を、全入力上のclean基底変換として再利用する部品。 -/
def controlledOracleOutputAlignmentCleanComponent (p : QParameters) :
    CleanComponent
      (reversibleGatePermutation :
        ReversibleGate p.ancillaWidth p.systemWidth →
          Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth)) :=
  CleanComponent.ofPermutation (controlledOracleOutputAlignmentPermutationComponent p)

/-- 正本整列回路に対応する、参照置換だけから定義した解析的全作用素。 -/
def ControlledOracleOutputAlignmentTargetOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  (controlledXorOracleOutputsIntoAlignedRegistersPermutation p)⁻¹.permMatrix ℂ

/-- 正本整列基本ゲート回路が解析的整列作用素へ厳密一致する全作用素部品。 -/
def controlledOracleOutputAlignmentExactOperatorComponent (p : QParameters) :
    ExactOperatorComponent
      (primitiveGateOperator :
        PrimitiveGate p.ancillaWidth p.systemWidth →
          Operator (JointBasis p.ancillaWidth p.systemWidth)) where
  circuit := controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p
  target := ControlledOracleOutputAlignmentTargetOperator p
  correct := calc
    VerifiedCircuitCore.Circuit.denote primitiveGateOperator
        (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p) =
      ((controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).toBasisPermutation
        reversibleGatePermutation).permMatrix ℂ :=
      controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_operator_eq_permMatrix p
    _ = ControlledOracleOutputAlignmentTargetOperator p := by
      unfold ControlledOracleOutputAlignmentTargetOperator
        controlledXorOracleOutputsIntoAlignedRegistersPermutation
      rw [Circuit.toBasisPermutation_eq_execution_inverse
        reversibleGatePermutation (by intro gate; cases gate <;> rfl)]
      rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_execution_eq_analytic]

/-- 終端反転の回路非依存な解析的基底置換。 -/
def flipAmplitudeSignalPermutation (p : QParameters) :
    Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth) :=
  flipAmplitudeSignalAnalyticPermutation p

/-- 終端反転参照回路を、その基底作用と逆置換行列へ結び付ける置換部品。 -/
def flipAmplitudeSignalPermutationComponent (p : QParameters) :
    PermutationComponent
      (fun gate : ReversibleGate p.ancillaWidth p.systemWidth =>
        (reversibleGatePermutation gate).permMatrix ℂ)
      reversibleGatePermutation :=
  PermutationComponent.ofInvolutiveCircuit
    (fun gate : ReversibleGate p.ancillaWidth p.systemWidth =>
      (reversibleGatePermutation gate).permMatrix ℂ)
    reversibleGatePermutation
    (by intro gate; cases gate <;> rfl)
    (by intro gate; rfl)
    (flipAmplitudeSignalReversibleCircuit p)
    (flipAmplitudeSignalPermutation p)
    (flipAmplitudeSignalReversibleCircuit_runBasis_eq_analytic p)

/-- 終端反転参照回路を、全入力上のclean基底変換として再利用する部品。 -/
def flipAmplitudeSignalCleanComponent (p : QParameters) :
    CleanComponent
      (reversibleGatePermutation :
        ReversibleGate p.ancillaWidth p.systemWidth →
          Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth)) :=
  CleanComponent.ofPermutation (flipAmplitudeSignalPermutationComponent p)

/-- 正本終端反転回路に対応する、参照置換だけから定義した解析的全作用素。 -/
def FlipAmplitudeSignalTargetOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  (flipAmplitudeSignalPermutation p)⁻¹.permMatrix ℂ

/-- 正本終端X回路が解析的反転作用素へ厳密一致する全作用素部品。 -/
def flipAmplitudeSignalExactOperatorComponent (p : QParameters) :
    ExactOperatorComponent
      (primitiveGateOperator :
        PrimitiveGate p.ancillaWidth p.systemWidth →
          Operator (JointBasis p.ancillaWidth p.systemWidth)) where
  circuit := flipAmplitudeSignalPrimitiveCircuit p
  target := FlipAmplitudeSignalTargetOperator p
  correct := calc
    VerifiedCircuitCore.Circuit.denote primitiveGateOperator
        (flipAmplitudeSignalPrimitiveCircuit p) =
      ((flipAmplitudeSignalReversibleCircuit p).toBasisPermutation
        reversibleGatePermutation).permMatrix ℂ := by
      rw [flipAmplitudeSignalPrimitiveCircuit_eq_reversible]
      exact ReversibleCircuit.toPrimitive_operator_eq_permMatrix _
    _ = FlipAmplitudeSignalTargetOperator p := by
      unfold FlipAmplitudeSignalTargetOperator
      unfold flipAmplitudeSignalPermutation
      rw [Circuit.toBasisPermutation_eq_execution_inverse
        reversibleGatePermutation (by intro gate; cases gate <;> rfl)]
      rw [flipAmplitudeSignalReversibleCircuit_execution_eq_analytic]

end

end ProbabilityGeneratorQProof
