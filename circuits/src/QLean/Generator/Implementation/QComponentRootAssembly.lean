import QLean.Generator.Implementation.QVerifiedFullOracleComponents
import QLean.Generator.Implementation.QVerifiedTopComponents
import QLean.Generator.Implementation.QActualPhysicalEventAcceptedCorrectness
import QLean.Generator.Implementation.QActualDiagonalAcceptedCorrectness
import QLean.Generator.Implementation.QActualRejectedPathCorrectness
import QLean.Generator.Implementation.QActualSelectorCasesComplete
import QLean.Generator.Implementation.QEndToEndSelectorAssembly

/-!
# 公開 component から組み立てる Q block encoding root

このファイルは、root 証明を二つの層へ分ける。一般層は直接子から作る
`prefixCircuit`、row状態準備契約、Q専用の位相・clean path契約だけを使い、
selector有限和とblock encodingを導く。正本層のみが既存のwire-level定理を使い、
それらを六つのpath caseと前段振幅の局所componentへ橋渡しする。一般の成功ブロック
定理は固定`uqCircuit`の一体定理を直接適用しない。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

/-- Q 正本の基本ゲート意味論を component 型で再利用するための略記。 -/
abbrev QPrimitiveOperator (p : QParameters) :=
  (primitiveGateOperator :
    PrimitiveGate p.ancillaWidth p.systemWidth →
      Operator (JointBasis p.ancillaWidth p.systemWidth))

/-- Q の可逆参照ゲートを置換行列へ解釈する意味論の略記。 -/
abbrev QReversibleOperator (p : QParameters) :=
  (fun gate : ReversibleGate p.ancillaWidth p.systemWidth =>
    (reversibleGatePermutation gate).permMatrix ℂ)

/-- Q の可逆参照ゲートを計算基底置換へ解釈する意味論の略記。 -/
abbrev QReversiblePermutation (p : QParameters) :=
  (reversibleGatePermutation :
    ReversibleGate p.ancillaWidth p.systemWidth →
      Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth))

/-- 任意のsystem基底を保ったままrow selectorだけを一様化した解析的目標状態。 -/
def UniformRowSelectorTargetState
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ :=
  liftSelectorStateOver p (rowSelectorWire p)
    (zeroAncillaJointBasis p system)
    (idealUniformSelectorState p.selectorWidth p.selectorCount)

/-- 任意のsystem基底を保ったままcolumn selectorだけを一様化した解析的目標状態。 -/
def UniformColumnSelectorTargetState
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ :=
  liftSelectorStateOver p (columnSelectorWire p)
    (zeroAncillaJointBasis p system)
    (idealUniformSelectorState p.selectorWidth p.selectorCount)

/-- 任意の system 基底上で row selector 一様準備を表す状態準備部品。 -/
def uniformRowSelectorStatePreparationComponent
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StatePreparationComponent (QPrimitiveOperator p) where
  circuit := prepareUniformRowSelectorCircuit p
  initialState := basisKet (zeroAncillaJointBasis p system)
  targetState := UniformRowSelectorTargetState p system
  correct := prepareUniformRowSelectorCircuit_systemBasis_correct_sharedCore p system

/-- 任意の system 基底上で column selector 一様準備を表す状態準備部品。 -/
def uniformColumnSelectorStatePreparationComponent
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StatePreparationComponent (QPrimitiveOperator p) where
  circuit := prepareUniformColumnSelectorCircuit p
  initialState := basisKet (zeroAncillaJointBasis p system)
  targetState := UniformColumnSelectorTargetState p system
  correct := prepareUniformColumnSelectorCircuit_systemBasis_correct_sharedCore p system

/-- Q block assembly が直接利用する検証済み子部品群。 -/
structure QRootAssemblyChildren (p : QParameters) where
  columnUniform : ∀ _system : RegisterBasis p.systemWidth,
    StatePreparationComponent (QPrimitiveOperator p)
  rowUniform : ∀ _system : RegisterBasis p.systemWidth,
    StatePreparationComponent (QPrimitiveOperator p)
  xorSystemIntoColumnKeyExactOperator : ExactOperatorComponent (QPrimitiveOperator p)
  xorSystemIntoColumnKeyBasisPermutation :
    PermutationComponent (QReversibleOperator p) (QReversiblePermutation p)
  activeCopyNegativePhaseExactOperator : ExactOperatorComponent (QPrimitiveOperator p)
  controlledOracleOutputAlignmentExactOperator : ExactOperatorComponent (QPrimitiveOperator p)
  controlledOracleOutputAlignmentBasisPermutation :
    PermutationComponent (QReversibleOperator p) (QReversiblePermutation p)
  flipAmplitudeSignalExactOperator : ExactOperatorComponent (QPrimitiveOperator p)
  columnOracle : ∀ _configuration : QConfiguration p, ∀ _selector : QSelector p,
    CleanComponent (QReversiblePermutation p)
  rowOracle : ∀ _configuration : QConfiguration p, ∀ _selector : QSelector p,
    CleanComponent (QReversiblePermutation p)

/--
子 component が正本の各段階と同じ回路・解析 target・clean 契約を持つことを表す。
一様準備では circuit だけでなく initial/target state も比較し、単なる構文一致で
状態準備仕様がすり替わらないようにする。
-/
structure HierarchicalRootToCanonicalUqCircuitIdentification
    (p : QParameters) (children : QRootAssemblyChildren p) : Prop where
  columnUniformCircuit : ∀ system,
    (children.columnUniform system).circuit = prepareUniformColumnSelectorCircuit p
  columnUniformInitialState : ∀ system,
    (children.columnUniform system).initialState =
      basisKet (zeroAncillaJointBasis p system)
  columnUniformTargetState : ∀ system,
    (children.columnUniform system).targetState =
      UniformColumnSelectorTargetState p system
  rowUniformCircuit : ∀ system,
    (children.rowUniform system).circuit = prepareUniformRowSelectorCircuit p
  rowUniformInitialState : ∀ system,
    (children.rowUniform system).initialState =
      basisKet (zeroAncillaJointBasis p system)
  rowUniformTargetState : ∀ system,
    (children.rowUniform system).targetState =
      UniformRowSelectorTargetState p system
  xorSystemIntoColumnKeyPrimitiveCircuit_eq : children.xorSystemIntoColumnKeyExactOperator.circuit = xorSystemIntoColumnKeyPrimitiveCircuit p
  xorSystemIntoColumnKeyTarget_eq : children.xorSystemIntoColumnKeyExactOperator.target = XorSystemIntoColumnKeyTargetOperator p
  xorSystemIntoColumnKeyReversibleCircuit_eq :
    children.xorSystemIntoColumnKeyBasisPermutation.circuit = xorSystemIntoColumnKeyReversibleCircuit p
  xorSystemIntoColumnKeyPermutation_eq :
    children.xorSystemIntoColumnKeyBasisPermutation.reference = xorSystemIntoColumnKeyPermutation p
  activeCopyNegativePhaseCircuit_eq :
    children.activeCopyNegativePhaseExactOperator.circuit = copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p
  activeCopyNegativePhaseTarget_eq :
    children.activeCopyNegativePhaseExactOperator.target = ActiveCopyNegativePhaseTargetOperator p
  controlledOracleOutputAlignmentPrimitiveCircuit_eq : children.controlledOracleOutputAlignmentExactOperator.circuit = controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p
  controlledOracleOutputAlignmentTarget_eq : children.controlledOracleOutputAlignmentExactOperator.target = ControlledOracleOutputAlignmentTargetOperator p
  controlledOracleOutputAlignmentReversibleCircuit_eq :
    children.controlledOracleOutputAlignmentBasisPermutation.circuit = controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p
  controlledOracleOutputAlignmentPermutation_eq :
    children.controlledOracleOutputAlignmentBasisPermutation.reference = controlledXorOracleOutputsIntoAlignedRegistersPermutation p
  flipAmplitudeSignalPrimitiveCircuit_eq : children.flipAmplitudeSignalExactOperator.circuit = flipAmplitudeSignalPrimitiveCircuit p
  flipAmplitudeSignalTarget_eq : children.flipAmplitudeSignalExactOperator.target = FlipAmplitudeSignalTargetOperator p
  applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit : ∀ configuration selector,
    (children.columnOracle configuration selector).circuit =
      applyColumnOracleReferenceAndRestoreWorkCircuit p
  columnOracleReference : ∀ configuration selector,
    (children.columnOracle configuration selector).reference =
      uniqueAnalyticReference
        (ReversibleCircuit.ColumnOracleRestoredReferenceSpec p
          configuration selector)
  columnOracleInputCondition : ∀ configuration selector,
    (children.columnOracle configuration selector).inputCondition =
      ReversibleCircuit.ColumnOracleInputSpec p configuration selector
  columnOracleOutputCondition : ∀ configuration selector,
    (children.columnOracle configuration selector).outputCondition =
      ReversibleCircuit.ColumnOracleInputSpec p configuration selector
  columnOracleRestoration : ∀ configuration selector,
    (children.columnOracle configuration selector).restoration =
      ReversibleCircuit.ColumnOracleRestoredReferenceSpec p
        configuration selector
  applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit : ∀ configuration selector,
    (children.rowOracle configuration selector).circuit =
      applyRowOracleReferenceAndRestoreWorkCircuit p
  rowOracleReference : ∀ configuration selector,
    (children.rowOracle configuration selector).reference =
      uniqueAnalyticReference
        (ReversibleCircuit.RowOracleRestoredReferenceSpec p
          configuration selector)
  rowOracleInputCondition : ∀ configuration selector,
    (children.rowOracle configuration selector).inputCondition =
      ReversibleCircuit.RowOracleInputSpec p configuration selector
  rowOracleOutputCondition : ∀ configuration selector,
    (children.rowOracle configuration selector).outputCondition =
      ReversibleCircuit.RowOracleInputSpec p configuration selector
  rowOracleRestoration : ∀ configuration selector,
    (children.rowOracle configuration selector).restoration =
      ReversibleCircuit.RowOracleRestoredReferenceSpec p
        configuration selector

/--
一様準備と oracle は入力依存 component 族なので、root circuit が使う共通回路を明示し、
各 component の circuit がその共通回路へ一致することを契約に含める。
-/
structure QRootCircuitAssembly
    (p : QParameters) (children : QRootAssemblyChildren p) where
  columnUniformCircuit : Circuit (PrimitiveGate p.ancillaWidth p.systemWidth)
  rowUniformCircuit : Circuit (PrimitiveGate p.ancillaWidth p.systemWidth)
  applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit : Circuit (PrimitiveGate p.ancillaWidth p.systemWidth)
  applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit : Circuit (PrimitiveGate p.ancillaWidth p.systemWidth)
  columnUniform_from_child : ∀ system,
    (children.columnUniform system).circuit = columnUniformCircuit
  rowUniform_from_child : ∀ system,
    (children.rowUniform system).circuit = rowUniformCircuit
  columnOracle_from_child : ∀ configuration selector,
    ReversibleCircuit.toPrimitive
        (children.columnOracle configuration selector).circuit = applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit
  rowOracle_from_child : ∀ configuration selector,
    ReversibleCircuit.toPrimitive
        (children.rowOracle configuration selector).circuit = applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit

/--
column・row oracle component族の回路がroot assemblyの共通oracle回路へ一致するという、
回路配置だけを表す構造契約。解析的oracle仕様やclean契約とは区別する。
-/
structure ColumnRowOracleToRootAssemblyIdentification
    (p : QParameters) (children : QRootAssemblyChildren p)
    (assembly : QRootCircuitAssembly p children) : Prop where
  columnCircuit : ∀ configuration selector,
    ReversibleCircuit.toPrimitive
        (children.columnOracle configuration selector).circuit =
      assembly.applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit
  rowCircuit : ∀ configuration selector,
    ReversibleCircuit.toPrimitive
        (children.rowOracle configuration selector).circuit =
      assembly.applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit

/-- 子部品の circuit だけを自然な二項 `seq` で組み立てた root 回路。 -/
def QRootCircuitAssembly.fullCircuit
    {p : QParameters} {children : QRootAssemblyChildren p}
    (assembly : QRootCircuitAssembly p children) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  .seq assembly.columnUniformCircuit <|
  .seq children.xorSystemIntoColumnKeyExactOperator.circuit <|
  .seq assembly.applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit <|
  .seq children.activeCopyNegativePhaseExactOperator.circuit <|
  .seq children.controlledOracleOutputAlignmentExactOperator.circuit <|
  .seq (assembly.applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit.reverse PrimitiveGate.inverse) <|
  .seq assembly.applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit <|
  .seq children.flipAmplitudeSignalExactOperator.circuit <|
  assembly.rowUniformCircuit.reverse PrimitiveGate.inverse

/-- 最後のrow一様準備逆実行を除いた、直接子だけからなるselector path前段回路。 -/
def QRootCircuitAssembly.prefixCircuit
    {p : QParameters} {children : QRootAssemblyChildren p}
    (assembly : QRootCircuitAssembly p children) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  .seq assembly.columnUniformCircuit <|
  .seq children.xorSystemIntoColumnKeyExactOperator.circuit <|
  .seq assembly.applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit <|
  .seq children.activeCopyNegativePhaseExactOperator.circuit <|
  .seq children.controlledOracleOutputAlignmentExactOperator.circuit <|
  .seq (assembly.applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit.reverse PrimitiveGate.inverse) <|
  .seq assembly.applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit <|
  children.flipAmplitudeSignalExactOperator.circuit

/--
root回路の状態作用は、直接子からなる前段回路を作用させた後にrow準備を逆実行する。
これは回路の二項`seq`だけを使う構造合成則であり、各子のゲート列を展開しない。
-/
theorem QRootCircuitAssembly.applyOperator_eq_rowReverse_prefix
    {p : QParameters} {children : QRootAssemblyChildren p}
    (assembly : QRootCircuitAssembly p children)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    applyOperator (assembly.fullCircuit.toIdealOperator primitiveGateOperator) state =
      applyOperator
        ((assembly.rowUniformCircuit.reverse PrimitiveGate.inverse).toIdealOperator
          primitiveGateOperator)
        (applyOperator
          (assembly.prefixCircuit.toIdealOperator primitiveGateOperator) state) := by
  unfold QRootCircuitAssembly.fullCircuit QRootCircuitAssembly.prefixCircuit
  repeat' rw [applyOperator_toIdealOperator_seq]

/--
row一様準備子の公開`correct`契約だけを使い、root成功ブロックを前段状態との解析的
一様内積へ変換する。固定`uqCircuit`の成功ブロック定理には依存しない。
-/
theorem QRootCircuitAssembly.successBlock_eq_rowUniformOverlap
    {p : QParameters} {children : QRootAssemblyChildren p}
    (assembly : QRootCircuitAssembly p children)
    (canonical : HierarchicalRootToCanonicalUqCircuitIdentification p children)
    (output input : RegisterBasis p.systemWidth) :
    qubitSuccessBlock (allZeroAncilla p.ancillaWidth)
        (assembly.fullCircuit.toIdealOperator primitiveGateOperator) output input =
      qRowUniformOverlap p output
        (applyOperator (assembly.prefixCircuit.toIdealOperator primitiveGateOperator)
          (basisKet (zeroAncillaJointBasis p input))) := by
  let prefixState :=
    applyOperator (assembly.prefixCircuit.toIdealOperator primitiveGateOperator)
      (basisKet (zeroAncillaJointBasis p input))
  change assembly.fullCircuit.toIdealOperator primitiveGateOperator
      (zeroAncillaJointBasis p output) (zeroAncillaJointBasis p input) = _
  calc
    assembly.fullCircuit.toIdealOperator primitiveGateOperator
        (zeroAncillaJointBasis p output) (zeroAncillaJointBasis p input) =
      applyOperator (assembly.fullCircuit.toIdealOperator primitiveGateOperator)
        (basisKet (zeroAncillaJointBasis p input))
        (zeroAncillaJointBasis p output) :=
      (applyOperator_basisKet _ _ _).symm
    _ = applyOperator
        ((assembly.rowUniformCircuit.reverse PrimitiveGate.inverse).toIdealOperator
          primitiveGateOperator)
        prefixState (zeroAncillaJointBasis p output) := by
      exact congrFun (assembly.applyOperator_eq_rowReverse_prefix
        (basisKet (zeroAncillaJointBasis p input)))
        (zeroAncillaJointBasis p output)
    _ = ∑ basis,
        star ((children.rowUniform output).targetState basis) * prefixState basis := by
      rw [← assembly.rowUniform_from_child output]
      exact StatePreparationComponent.reverse_applyOperator_at_basis
        primitiveGateOperator PrimitiveGate.inverse primitiveGateOperator_inverse
        (children.rowUniform output) (zeroAncillaJointBasis p output)
        (canonical.rowUniformInitialState output) prefixState
    _ = qRowUniformOverlap p output prefixState := by
      unfold qRowUniformOverlap
      apply Finset.sum_congr rfl
      intro basis _
      rw [canonical.rowUniformTargetState output]
      rfl

/-- selector 一本の観測振幅が持つ型の略記。 -/
abbrev QSelectorAmplitude (p : QParameters) :=
  RegisterBasis p.systemWidth → RegisterBasis p.systemWidth → QSelector p → ℂ

/--
任意の観測振幅に対する六つの排反 path case。固定回路の名前を含まないため、同じ有限
場合分けを別実装の selector pipeline にも再利用できる。
-/
structure PrefixAmplitudeReferenceCaseComponents
    (p : QParameters) (amplitude : QSelectorAmplitude p) : Prop where
  illegalOutput : ∀ output input rowSelector,
    decodeDelimiter output = none → amplitude output input rowSelector = 0
  illegalInput : ∀ (output : QConfiguration p) input rowSelector,
    decodeDelimiter input = none →
      amplitude (delimiterEncoding output) input rowSelector = 0
  rowRejected : ∀ (output input : QConfiguration p) rowSelector,
    rowReference output rowSelector = none →
      amplitude (delimiterEncoding output) (delimiterEncoding input) rowSelector = 0
  columnRejected : ∀ (output input : QConfiguration p) rowSelector rowResult,
    rowReference output rowSelector = some rowResult →
    columnReference input rowResult.columnSelector = none →
      amplitude (delimiterEncoding output) (delimiterEncoding input) rowSelector = 0
  inconsistent : ∀ (output input : QConfiguration p) rowSelector rowResult
      columnResult,
    rowReference output rowSelector = some rowResult →
    columnReference input rowResult.columnSelector = some columnResult →
    ¬(columnResult.rowSelector = rowSelector ∧
      columnResult.output = output ∧ rowResult.input = input) →
      amplitude (delimiterEncoding output) (delimiterEncoding input) rowSelector = 0
  accepted : ∀ (output input : QConfiguration p) rowSelector rowResult
      columnResult,
    rowReference output rowSelector = some rowResult →
    columnReference input rowResult.columnSelector = some columnResult →
    columnResult.rowSelector = rowSelector →
    columnResult.output = output → rowResult.input = input →
      amplitude (delimiterEncoding output) (delimiterEncoding input) rowSelector =
        ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
          (if columnResult.negative then -1 else 1)

/-- 六つの path case だけから、任意の観測振幅を解析的 selector 仕様へ一致させる。 -/
theorem PrefixAmplitudeReferenceCaseComponents.selectorValues
    {p : QParameters} {amplitude : QSelectorAmplitude p}
    (cases : PrefixAmplitudeReferenceCaseComponents p amplitude) :
    ∀ output input rowSelector,
      amplitude output input rowSelector =
        PrefixAmplitudeReferenceCaseSpec p output input rowSelector := by
  intro output input rowSelector
  cases outputDecoded : decodeDelimiter output with
  | none =>
      rw [cases.illegalOutput output input rowSelector outputDecoded]
      simp [PrefixAmplitudeReferenceCaseSpec, outputDecoded]
  | some outputConfiguration =>
      have outputEncoding : delimiterEncoding outputConfiguration = output :=
        decodeDelimiter_eq_some_iff.mp outputDecoded
      subst output
      cases inputDecoded : decodeDelimiter input with
      | none =>
          rw [cases.illegalInput outputConfiguration input rowSelector inputDecoded]
          simp [PrefixAmplitudeReferenceCaseSpec, inputDecoded]
      | some inputConfiguration =>
          have inputEncoding : delimiterEncoding inputConfiguration = input :=
            decodeDelimiter_eq_some_iff.mp inputDecoded
          subst input
          cases rowAccepted : rowReference outputConfiguration rowSelector with
          | none =>
              rw [cases.rowRejected outputConfiguration inputConfiguration rowSelector
                rowAccepted]
              simp [PrefixAmplitudeReferenceCaseSpec,
                reverseReferenceAcceptedRowSelectorWeight, rowAccepted]
          | some rowResult =>
              cases columnAccepted :
                  columnReference inputConfiguration rowResult.columnSelector with
              | none =>
                  rw [cases.columnRejected outputConfiguration inputConfiguration
                    rowSelector rowResult rowAccepted columnAccepted]
                  simp [PrefixAmplitudeReferenceCaseSpec,
                    reverseReferenceAcceptedRowSelectorWeight, rowAccepted,
                    columnAccepted]
              | some columnResult =>
                  by_cases lands : columnResult.rowSelector = rowSelector ∧
                      columnResult.output = outputConfiguration ∧
                        rowResult.input = inputConfiguration
                  · rcases lands with ⟨rowSelectorEq, outputEq, inputEq⟩
                    rw [cases.accepted outputConfiguration inputConfiguration rowSelector
                      rowResult columnResult rowAccepted columnAccepted rowSelectorEq
                      outputEq inputEq]
                    symm
                    exact PrefixAmplitudeReferenceCaseSpec_of_accepted
                      outputConfiguration inputConfiguration rowSelector rowResult
                      columnResult rowAccepted columnAccepted rowSelectorEq outputEq
                      inputEq
                  · rw [cases.inconsistent outputConfiguration inputConfiguration
                      rowSelector rowResult columnResult rowAccepted columnAccepted lands]
                    simp [PrefixAmplitudeReferenceCaseSpec,
                      reverseReferenceAcceptedRowSelectorWeight, rowAccepted,
                      columnAccepted, lands]

/--
Q固有の位相・clean path部品。既存の五契約だけでは表せない、直接子から作った前段回路の
selector一本の実振幅と六つの回路非依存な解析caseとの一致を公開契約として保持する。
-/
structure PrefixPathAmplitudeAndSignComponent
    (p : QParameters) (children : QRootAssemblyChildren p)
    (assembly : QRootCircuitAssembly p children) where
  observedAmplitude : QSelectorAmplitude p
  prefixAmplitude_correct : ∀ output input selector,
    applyOperator (assembly.prefixCircuit.toIdealOperator primitiveGateOperator)
        (children.columnUniform input).initialState
        (qFinalRowSelectorBasis p output selector) =
      observedAmplitude output input selector
  cases : PrefixAmplitudeReferenceCaseComponents p observedAmplitude

/-- 前段回路がselector一本ごとに与える0または符号付き一様振幅の解析仕様。 -/
def PrefixPathAmplitudeAndSignSpec
    {p : QParameters} {children : QRootAssemblyChildren p}
    {assembly : QRootCircuitAssembly p children}
    (component : PrefixPathAmplitudeAndSignComponent p children assembly) :
    QSelectorAmplitude p :=
  component.observedAmplitude

/--
自然な子回路assembly、正本解析仕様との照合、位相・clean path部品を束ねるpipeline。
成功ブロック合成はfieldとして仮定せず、row状態準備契約から後続定理で導く。
-/
structure PrefixPathsWithRowProjectionComponent
    (p : QParameters) (children : QRootAssemblyChildren p) where
  assembly : QRootCircuitAssembly p children
  canonical : HierarchicalRootToCanonicalUqCircuitIdentification p children
  path : PrefixPathAmplitudeAndSignComponent p children assembly

/-- pipelineが外部へ公開するselector一本の観測振幅。 -/
def PrefixPathsWithRowProjectionComponent.observedAmplitude
    {p : QParameters} {children : QRootAssemblyChildren p}
    (pipeline : PrefixPathsWithRowProjectionComponent p children) : QSelectorAmplitude p :=
  pipeline.path.observedAmplitude

/-- 前段path振幅へrow一様射影を合成する部品が公開する解析的振幅仕様。 -/
def PrefixPathAmplitudeWithRowProjectionSpec
    {p : QParameters} {children : QRootAssemblyChildren p}
    (pipeline : PrefixPathsWithRowProjectionComponent p children) : QSelectorAmplitude p :=
  pipeline.observedAmplitude

/--
直接子のrow状態準備`correct`、前段path契約、selector有限和だけから成功ブロックを得る。
固定`uqCircuit`や固定actual振幅の一体定理は参照しない。
-/
theorem PrefixPathsWithRowProjectionComponent.successBlock_of_selector_values
    {p : QParameters} {children : QRootAssemblyChildren p}
    (pipeline : PrefixPathsWithRowProjectionComponent p children)
    (selectorValues : ∀ output input selector,
      pipeline.observedAmplitude output input selector =
        expectedQSelectorAmplitude p output input selector) :
    qubitSuccessBlock (allZeroAncilla p.ancillaWidth)
        (pipeline.assembly.fullCircuit.toIdealOperator primitiveGateOperator) =
      embeddedReferenceSelectorOverlap p := by
  apply funext
  intro output
  apply funext
  intro input
  rw [pipeline.assembly.successBlock_eq_rowUniformOverlap pipeline.canonical]
  let prefixState :=
    applyOperator
      (pipeline.assembly.prefixCircuit.toIdealOperator primitiveGateOperator)
      (basisKet (zeroAncillaJointBasis p input))
  have prefixValues : ∀ selector,
      prefixState (qFinalRowSelectorBasis p output selector) =
        expectedQSelectorAmplitude p output input selector := by
    intro selector
    unfold prefixState
    rw [← pipeline.canonical.columnUniformInitialState input]
    exact (pipeline.path.prefixAmplitude_correct output input selector).trans
      (selectorValues output input selector)
  have overlapExpected :
      qRowUniformOverlap p output prefixState =
        ∑ selector : QSelector p,
          ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
            expectedQSelectorAmplitude p output input selector := by
    rw [qRowUniformOverlap_eq_qSelector_sum]
    apply Fintype.sum_congr
    intro selector
    simpa [qFinalRowSelectorBasis] using congrArg
      (fun value => ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) * value)
      (prefixValues selector)
  cases outputDecoded : decodeDelimiter output with
  | none =>
      rw [overlapExpected]
      simp [expectedQSelectorAmplitude, outputDecoded,
        embeddedReferenceSelectorOverlap]
  | some outputConfiguration =>
      cases inputDecoded : decodeDelimiter input with
      | none =>
          rw [overlapExpected]
          simp [expectedQSelectorAmplitude, outputDecoded, inputDecoded,
            embeddedReferenceSelectorOverlap]
      | some inputConfiguration =>
          rw [qRowUniformOverlap_eq_configurationReferenceNormalizedOverlap_of_row_selector_values
            p output prefixState outputConfiguration inputConfiguration]
          · simp [embeddedReferenceSelectorOverlap, outputDecoded, inputDecoded]
          · intro selector
            simpa [qFinalRowSelectorBasis, expectedQSelectorAmplitude,
              outputDecoded, inputDecoded] using prefixValues selector

/-- selector path pipeline と六場合の有限和合成を束ねた公開 component。 -/
structure RowSelectorPathFiniteSumComponent
    (p : QParameters) (children : QRootAssemblyChildren p) where
  pipeline : PrefixPathsWithRowProjectionComponent p children
  selectorValues : ∀ output input rowSelector,
    pipeline.observedAmplitude output input rowSelector =
      PrefixAmplitudeReferenceCaseSpec p output input rowSelector

/-- 六つの path case から pipeline の有限和 component を構成する。 -/
def RowSelectorPathFiniteSumComponent.ofReferenceCases
    (p : QParameters) (children : QRootAssemblyChildren p)
    (pipeline : PrefixPathsWithRowProjectionComponent p children)
    (cases : PrefixAmplitudeReferenceCaseComponents p pipeline.observedAmplitude) :
    RowSelectorPathFiniteSumComponent p children where
  pipeline := pipeline
  selectorValues := cases.selectorValues

/-- pipeline自身が直接子として持つ位相・clean path契約から有限和部品を構成する。 -/
def RowSelectorPathFiniteSumComponent.ofPathContract
    (p : QParameters) (children : QRootAssemblyChildren p)
    (pipeline : PrefixPathsWithRowProjectionComponent p children) :
    RowSelectorPathFiniteSumComponent p children where
  pipeline := pipeline
  selectorValues := pipeline.path.cases.selectorValues

/-- pipeline 契約だけを使い、success block を解析的 selector overlap へ一致させる。 -/
theorem RowSelectorPathFiniteSumComponent.successBlock_correct
    {p : QParameters} {children : QRootAssemblyChildren p}
    (component : RowSelectorPathFiniteSumComponent p children) :
    qubitSuccessBlock (allZeroAncilla p.ancillaWidth)
        (component.pipeline.assembly.fullCircuit.toIdealOperator primitiveGateOperator) =
      RowSelectorPathFiniteSumSuccessBlockSpec p := by
  have forwardValues : ∀ output input rowSelector,
      component.pipeline.observedAmplitude output input rowSelector =
        expectedQSelectorAmplitude p output input rowSelector := by
    intro output input rowSelector
    exact (component.selectorValues output input rowSelector).trans
      (PrefixAmplitudeReferenceCaseSpec_eq p output input rowSelector)
  calc
    qubitSuccessBlock (allZeroAncilla p.ancillaWidth)
        (component.pipeline.assembly.fullCircuit.toIdealOperator primitiveGateOperator) =
        embeddedReferenceSelectorOverlap p :=
      component.pipeline.successBlock_of_selector_values forwardValues
    _ = RowSelectorPathFiniteSumSuccessBlockSpec p :=
      embeddedReferenceSelectorOverlap_eq_RowSelectorPathFiniteSumSuccessBlockSpec p

/-- selector 有限和部品の基本ゲート回路は、子部品の具体表現に依存せずユニタリである。 -/
theorem RowSelectorPathFiniteSumComponent.circuit_unitary
    {p : QParameters} {children : QRootAssemblyChildren p}
    (component : RowSelectorPathFiniteSumComponent p children) :
    component.pipeline.assembly.fullCircuit.toIdealOperator primitiveGateOperator ∈
      Matrix.unitaryGroup (JointBasis p.ancillaWidth p.systemWidth) ℂ := by
  exact primitiveCircuit_mem_unitaryGroup _

/-- selector-path pipeline と有限 selector 和から正規化 `3K`・誤差0の root 部品を作る。 -/
def BlockEncodingComponent.ofRowSelectorPathFiniteSum
    (p : QParameters) (children : QRootAssemblyChildren p)
    (selectorSum : RowSelectorPathFiniteSumComponent p children) :
    BlockEncodingComponent (QPrimitiveOperator p) :=
  BlockEncodingComponent.ofProof
    selectorSum.pipeline.assembly.fullCircuit
    (allZeroAncilla p.ancillaWidth)
    (embeddedProbabilityGenerator p)
    (3 * p.K)
    0
    (by
      apply isApproxQubitBlockEncoding_zero_of_exact
      · exact selectorSum.circuit_unitary
      · exact three_mul_K_positive p
      · rw [selectorSum.successBlock_correct,
          RowSelectorPathFiniteSumSuccessBlockSpec_eq_scaled_generator]
        have nonzero : (3 * (p.K : ℂ)) ≠ 0 := by
          norm_num
          exact_mod_cast (Nat.ne_of_gt p.K_pos)
        rw [smul_smul]
        push_cast
        change embeddedProbabilityGenerator p =
          ((3 * (p.K : ℂ)) * (1 / (3 * (p.K : ℂ)))) •
            embeddedProbabilityGenerator p
        rw [one_div, mul_inv_cancel₀ nonzero, one_smul])

/-- 解析的確率生成行列を正規化`3K`、誤差`0`で符号化する最終仕様。 -/
def EmbeddedProbabilityGeneratorScale3KErrorZeroSpec
    (p : QParameters)
    (circuit : Circuit (PrimitiveGate p.ancillaWidth p.systemWidth)) : Prop :=
  IsApproxQubitBlockEncoding
    (allZeroAncilla p.ancillaWidth)
    (circuit.toIdealOperator primitiveGateOperator)
    (embeddedProbabilityGenerator p)
    (3 * p.K)
    0

/-- Q 正本について既証明の公開 component を集めた root assembly の直接子群。 -/
def probabilityGeneratorRootAssemblyChildren (p : QParameters) : QRootAssemblyChildren p where
  columnUniform := uniformColumnSelectorStatePreparationComponent p
  rowUniform := uniformRowSelectorStatePreparationComponent p
  xorSystemIntoColumnKeyExactOperator := xorSystemIntoColumnKeyExactOperatorComponent p
  xorSystemIntoColumnKeyBasisPermutation := xorSystemIntoColumnKeyPermutationComponent p
  activeCopyNegativePhaseExactOperator := activeCopyNegativePhaseExactOperatorComponent p
  controlledOracleOutputAlignmentExactOperator := controlledOracleOutputAlignmentExactOperatorComponent p
  controlledOracleOutputAlignmentBasisPermutation := controlledOracleOutputAlignmentPermutationComponent p
  flipAmplitudeSignalExactOperator := flipAmplitudeSignalExactOperatorComponent p
  columnOracle :=
    ReversibleCircuit.verifiedApplyColumnOracleReferenceAndRestoreWorkCleanComponent p
  rowOracle :=
    ReversibleCircuit.verifiedApplyRowOracleReferenceAndRestoreWorkCleanComponent p

/-- 正本子部品群は circuit・解析 target・clean/restoration 仕様まで正本と一致する。 -/
theorem probabilityGeneratorRootAssemblyChildren_matchesCanonical (p : QParameters) :
    HierarchicalRootToCanonicalUqCircuitIdentification p (probabilityGeneratorRootAssemblyChildren p) := by
  constructor <;> intros <;> rfl

/-- 正本子部品の circuit を二項 `seq` へ配置する root circuit assembly。 -/
def probabilityGeneratorRootCircuitAssembly (p : QParameters) :
    QRootCircuitAssembly p (probabilityGeneratorRootAssemblyChildren p) where
  columnUniformCircuit := prepareUniformColumnSelectorCircuit p
  rowUniformCircuit := prepareUniformRowSelectorCircuit p
  applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit := applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p
  applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit := applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit p
  columnUniform_from_child := by intro system; rfl
  rowUniform_from_child := by intro system; rfl
  columnOracle_from_child := by intro configuration selector; rfl
  rowOracle_from_child := by intro configuration selector; rfl

/-- 正本column・row oracle component族とroot assembly共通回路の配置対応。 -/
theorem columnRowOracleRootAssemblyStructureDescriptor (p : QParameters) :
    ColumnRowOracleToRootAssemblyIdentification p
      (probabilityGeneratorRootAssemblyChildren p)
      (probabilityGeneratorRootCircuitAssembly p) where
  columnCircuit := (probabilityGeneratorRootCircuitAssembly p).columnOracle_from_child
  rowCircuit := (probabilityGeneratorRootCircuitAssembly p).rowOracle_from_child

/-- 正本 root assembly の回路は、唯一の正本 `uqCircuit` と定義的に同じである。 -/
theorem probabilityGeneratorRootCircuitAssembly_fullCircuit (p : QParameters) :
    (probabilityGeneratorRootCircuitAssembly p).fullCircuit = uqCircuit p := by
  rfl

/-- 正本の構造回路一致と全直接子の解析契約照合を一つに束ねる実装対応定理。 -/
theorem hierarchicalRootToUqCircuitStructureDescriptor (p : QParameters) :
    (probabilityGeneratorRootCircuitAssembly p).fullCircuit = uqCircuit p ∧
      HierarchicalRootToCanonicalUqCircuitIdentification p (probabilityGeneratorRootAssemblyChildren p) :=
  ⟨probabilityGeneratorRootCircuitAssembly_fullCircuit p,
    probabilityGeneratorRootAssemblyChildren_matchesCanonical p⟩

/--
正本の直接子回路から作る前段回路の状態は、従来の疎な前段状態に一致する。
固定実装名を使うのはQ専用path部品のcanonical instanceを作るこの末端bridgeだけである。
-/
theorem probabilityGeneratorPrefixCircuit_applyOperator_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    applyOperator
        ((probabilityGeneratorRootCircuitAssembly p).prefixCircuit.toIdealOperator
          primitiveGateOperator)
        (basisKet (zeroAncillaJointBasis p system)) =
      qBeforeRowUniformInverseState p system := by
  unfold QRootCircuitAssembly.prefixCircuit
  rw [show (probabilityGeneratorRootCircuitAssembly p).columnUniformCircuit =
      prepareUniformColumnSelectorCircuit p from rfl]
  rw [(probabilityGeneratorRootAssemblyChildren_matchesCanonical p).xorSystemIntoColumnKeyPrimitiveCircuit_eq]
  rw [show (probabilityGeneratorRootCircuitAssembly p).applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit =
      applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p from rfl]
  rw [(probabilityGeneratorRootAssemblyChildren_matchesCanonical p).activeCopyNegativePhaseCircuit_eq]
  rw [(probabilityGeneratorRootAssemblyChildren_matchesCanonical p).controlledOracleOutputAlignmentPrimitiveCircuit_eq]
  rw [show (probabilityGeneratorRootCircuitAssembly p).applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit =
      applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit p from rfl]
  rw [(probabilityGeneratorRootAssemblyChildren_matchesCanonical p).flipAmplitudeSignalPrimitiveCircuit_eq]
  repeat' rw [applyOperator_toIdealOperator_seq]
  rw [prepareUniformColumnSelectorCircuit_systemBasis_correct_sharedCore]
  rw [xorSystemIntoColumnKeyPrimitiveCircuit_applyOperator]
  rw [applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit_applyOperator]
  rw [copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_applyOperator_eq]
  rw [controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_applyOperator]
  rw [columnOracleReverse_applyOperator]
  rw [applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit_applyOperator]
  rw [flipAmplitudeSignalPrimitiveCircuit_applyOperator]
  rfl

/-- 正本回路の六つの path handler を、回路非依存な局所case契約へまとめる。 -/
theorem verifiedPrefixAmplitudeReferenceCaseComponents (p : QParameters) :
    PrefixAmplitudeReferenceCaseComponents p (qActualSelectorAmplitude p) where
  illegalOutput := qActualSelectorAmplitude_eq_zero_of_illegal_output p
  illegalInput := qActualSelectorAmplitude_eq_zero_of_illegal_input_final p
  rowRejected := fun output input rowSelector rejected =>
    qActualSelectorAmplitude_eq_zero_of_rowReference_none p output
      (delimiterEncoding input) rowSelector rejected
  columnRejected := qActualSelectorAmplitude_eq_zero_of_columnReference_none_final p
  inconsistent := qActualSelectorAmplitude_eq_zero_of_inconsistent_final p
  accepted := by
    intro output input rowSelector rowResult columnResult rowAccepted
      columnAccepted rowSelectorEqual outputEqual inputEqual
    subst input
    exact qActualSelectorAmplitude_of_reference_some output rowSelector rowResult
      columnResult rowAccepted columnAccepted

/--
正本前段回路の実振幅、六つの解析case、直接子bundleへの接続を持つ
Q専用の位相・clean path部品。
-/
def verifiedPrefixPathAmplitudeAndSignComponent (p : QParameters) :
    PrefixPathAmplitudeAndSignComponent p (probabilityGeneratorRootAssemblyChildren p)
      (probabilityGeneratorRootCircuitAssembly p) where
  observedAmplitude := qActualSelectorAmplitude p
  prefixAmplitude_correct := by
    intro output input selector
    exact congrFun (probabilityGeneratorPrefixCircuit_applyOperator_zeroAncilla p input)
      (qFinalRowSelectorBasis p output selector)
  cases := verifiedPrefixAmplitudeReferenceCaseComponents p

/--
正本pipelineは自然な子回路assembly、解析仕様照合、Q専用path部品だけを持つ。
成功ブロック等式はこの定義で仮定しない。
-/
def verifiedPrefixPathsWithRowProjectionComponent (p : QParameters) :
    PrefixPathsWithRowProjectionComponent p (probabilityGeneratorRootAssemblyChildren p) where
  assembly := probabilityGeneratorRootCircuitAssembly p
  canonical := (hierarchicalRootToUqCircuitStructureDescriptor p).2
  path := verifiedPrefixPathAmplitudeAndSignComponent p

/-- 正本 pipeline の局所 path 定理から selector 有限和 component を得る。 -/
def verifiedRowSelectorPathFiniteSumComponent (p : QParameters) :
    RowSelectorPathFiniteSumComponent p (probabilityGeneratorRootAssemblyChildren p) :=
  RowSelectorPathFiniteSumComponent.ofPathContract p
    (probabilityGeneratorRootAssemblyChildren p)
    (verifiedPrefixPathsWithRowProjectionComponent p)

/-- 直接子assembly・path・row準備から合成した有限和契約で得るroot block encoding部品。 -/
def probabilityGeneratorScale3KErrorZeroBlockEncodingComponent (p : QParameters) :
    BlockEncodingComponent (QPrimitiveOperator p) :=
  BlockEncodingComponent.ofRowSelectorPathFiniteSum p
    (probabilityGeneratorRootAssemblyChildren p)
    (verifiedRowSelectorPathFiniteSumComponent p)

/-- component root assembly から取り出した任意の正値 `q,K` に対する最終定理。 -/
theorem probabilityGeneratorScale3KErrorZeroBlockEncoding_correct (p : QParameters) :
    EmbeddedProbabilityGeneratorScale3KErrorZeroSpec p (uqCircuit p) := by
  unfold EmbeddedProbabilityGeneratorScale3KErrorZeroSpec
  have assembled := (probabilityGeneratorScale3KErrorZeroBlockEncodingComponent p).correct
  change IsApproxQubitBlockEncoding
    (allZeroAncilla p.ancillaWidth)
    ((probabilityGeneratorRootCircuitAssembly p).fullCircuit.toIdealOperator
      primitiveGateOperator)
    (embeddedProbabilityGenerator p) (3 * p.K) 0 at assembled
  rw [probabilityGeneratorRootCircuitAssembly_fullCircuit] at assembled
  exact assembled

end

end ProbabilityGeneratorQProof
