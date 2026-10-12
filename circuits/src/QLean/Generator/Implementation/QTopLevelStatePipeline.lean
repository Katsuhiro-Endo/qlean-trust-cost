import QLean.Generator.Implementation.QClassicalStateSemantics
import QLean.Generator.Implementation.UniformPreparationSharedCoreTargetBridge

/-!
# 一般Q正本回路の疎な状態パイプライン

最初のcolumn一様準備から最後のrow逆一様準備直前までを、状態関数と計算基底置換だけで
記述する。oracle内部の巨大行列や全計算基底は展開しない。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- column selector一様準備直後の状態関数。 -/
def qColumnPreparedState (p : QParameters)
    (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ :=
  liftSelectorStateOver p (columnSelectorWire p)
    (zeroAncillaJointBasis p system)
    (idealUniformSelectorState p.selectorWidth p.selectorCount)

/-- COPY直後の状態関数。 -/
def qAfterCopyState (p : QParameters)
    (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ :=
  qColumnPreparedState p system ∘
    (xorSystemIntoColumnKeyReversibleCircuit p).toBasisPermutation
      reversibleGatePermutation

/-- column oracle直後の状態関数。 -/
def qAfterColumnOracleState (p : QParameters)
    (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ :=
  qAfterCopyState p system ∘
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).toBasisPermutation reversibleGatePermutation

/-- 位相付き振幅判定直後の状態関数。 -/
def qAfterDiscriminatorState (p : QParameters)
    (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ :=
  fun output =>
    (if output (negativeWire p) && output (amplitudeSignalWire p) then -1 else 1) *
      qAfterColumnOracleState p system
        (cnotBasisAction (activeWire p) (amplitudeSignalWire p) output)

/-- `C_align`直後の状態関数。 -/
def qAfterAlignState (p : QParameters)
    (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ :=
  qAfterDiscriminatorState p system ∘
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).toBasisPermutation reversibleGatePermutation

/-- column oracle逆実行直後の状態関数。 -/
def qAfterColumnUncomputeState (p : QParameters)
    (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ :=
  qAfterAlignState p system ∘
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).toExecutionPermutation reversibleGatePermutation

/-- row oracle直後の状態関数。 -/
def qAfterRowOracleState (p : QParameters)
    (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ :=
  qAfterColumnUncomputeState p system ∘
    (applyRowOracleReferenceAndRestoreWorkCircuit p).toBasisPermutation reversibleGatePermutation

/-- 終端X直後、row一様準備逆実行の直前にある状態関数。 -/
def qBeforeRowUniformInverseState (p : QParameters)
    (system : RegisterBasis p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth → ℂ :=
  qAfterRowOracleState p system ∘
    (flipAmplitudeSignalReversibleCircuit p).toBasisPermutation
      reversibleGatePermutation

/--
最終基底から逆に追ったとき、振幅判定回路の出力側に現れる基底。
可逆回路部分だけを関数合成し、行列要素は展開しない。
-/
def qDiscriminatorOutputPreimage (p : QParameters)
    (output : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).toBasisPermutation reversibleGatePermutation <|
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).toExecutionPermutation
      reversibleGatePermutation <|
      (applyRowOracleReferenceAndRestoreWorkCircuit p).toBasisPermutation
        reversibleGatePermutation <|
        (flipAmplitudeSignalReversibleCircuit p).toBasisPermutation
          reversibleGatePermutation output

/--
最終基底から全可逆部分を逆に追い、最初のcolumn一様状態上の基底へ戻す。
-/
def qColumnPreparedPreimage (p : QParameters)
    (output : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (xorSystemIntoColumnKeyReversibleCircuit p).toBasisPermutation
      reversibleGatePermutation <|
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).toBasisPermutation
      reversibleGatePermutation <|
      cnotBasisAction (activeWire p) (amplitudeSignalWire p)
        (qDiscriminatorOutputPreimage p output)

/--
最終基底に対する中間振幅は、一意な列側逆像の一様振幅と位相符号の積である。
-/
theorem qBeforeRowUniformInverseState_apply
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (output : JointBasis p.ancillaWidth p.systemWidth) :
    qBeforeRowUniformInverseState p system output =
      (if (qDiscriminatorOutputPreimage p output) (negativeWire p) &&
          (qDiscriminatorOutputPreimage p output) (amplitudeSignalWire p)
        then -1 else 1) *
        qColumnPreparedState p system (qColumnPreparedPreimage p output) := by
  rfl

/-- row一様準備状態と任意の疎な状態との有限内積。 -/
def qRowUniformOverlap (p : QParameters)
    (system : RegisterBasis p.systemWidth)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) : ℂ :=
  ∑ basis,
    star (liftSelectorStateOver p (rowSelectorWire p)
      (zeroAncillaJointBasis p system)
      (idealUniformSelectorState p.selectorWidth p.selectorCount) basis) *
      state basis

/-- row一様状態が非零振幅を持つ基底であることを表す疎な受理条件。 -/
def QRowUniformBasisAccepted (p : QParameters)
    (system : RegisterBasis p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  OutsideSelectorMatches p (rowSelectorWire p)
      (zeroAncillaJointBasis p system) basis ∧
    selectorValue p.selectorWidth
      (projectSelectorBasis p (rowSelectorWire p) basis) < p.selectorCount

/-- row一様内積の受理条件を、有限和のフィルタで利用可能にする。 -/
noncomputable instance qRowUniformBasisAcceptedDecidable
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth) :
    Decidable (QRowUniformBasisAccepted p system basis) :=
  Classical.propDecidable _

/-- row一様内積は、疎な受理条件を満たす基底だけの一般有限和に一致する。 -/
theorem qRowUniformOverlap_eq_accepted_sum
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    qRowUniformOverlap p system state =
      ∑ basis,
        if QRowUniformBasisAccepted p system basis then
          ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) * state basis
        else 0 := by
  classical
  unfold qRowUniformOverlap QRowUniformBasisAccepted liftSelectorStateOver
  apply Finset.sum_congr rfl
  intro basis _
  by_cases outside : OutsideSelectorMatches p (rowSelectorWire p)
      (zeroAncillaJointBasis p system) basis
  · by_cases active : selectorValue p.selectorWidth
        (projectSelectorBasis p (rowSelectorWire p) basis) < p.selectorCount
    · simp [outside, active, idealUniformSelectorState,
        VerifiedCircuitCore.idealUniformSelectorState]
    · simp [outside, active, idealUniformSelectorState,
        VerifiedCircuitCore.idealUniformSelectorState]
  · simp [outside]

/-- 振幅判定回路の状態作用を関数等式として書いた形。 -/
theorem copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_applyOperator_eq
    (p : QParameters)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    applyOperator
        ((copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).toIdealOperator primitiveGateOperator)
        state =
      fun output =>
        (if output (negativeWire p) && output (amplitudeSignalWire p)
          then -1 else 1) *
          state (cnotBasisAction (activeWire p) (amplitudeSignalWire p) output) := by
  funext output
  exact copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_applyOperator p state output

/--
一般Q正本を全0ancillaの任意system基底へ作用させると、最後のrow逆一様準備だけを残した
疎な状態パイプラインへ厳密に一致する。
-/
theorem uqCircuit_applyOperator_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    applyOperator ((uqCircuit p).toIdealOperator primitiveGateOperator)
        (basisKet (zeroAncillaJointBasis p system)) =
      applyOperator
        (((prepareUniformRowSelectorCircuit p).reverse PrimitiveGate.inverse).toIdealOperator
          primitiveGateOperator)
        (qBeforeRowUniformInverseState p system) := by
  unfold uqCircuit
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

/-- row一様準備の逆回路を成功基底で評価すると、一般有限内積に一致する。 -/
theorem rowUniformReverse_applyOperator_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ) :
    applyOperator
        (((prepareUniformRowSelectorCircuit p).reverse PrimitiveGate.inverse).toIdealOperator
          primitiveGateOperator)
        state (zeroAncillaJointBasis p system) =
      qRowUniformOverlap p system state := by
  rw [reverseUniformRowSelectorPreparationIdealOperator_eq_adjoint]
  unfold applyOperator VerifiedCircuitCore.applyOperator Matrix.mulVec dotProduct
    qRowUniformOverlap
  apply Finset.sum_congr rfl
  intro basis _
  change
    star ((prepareUniformRowSelectorCircuit p).toIdealOperator primitiveGateOperator
      basis (zeroAncillaJointBasis p system)) * state basis = _
  have prepared := congrFun
    (prepareUniformSelectorOnWiresCircuit_correct_over_sharedCore p (rowSelectorWire p)
      (sharedRowSelectorWire_injective p)
      (sharedRowSelector_uniformScratch_disjoint p)
      (zeroAncillaJointBasis p system) (by intro index; rfl) (by
        intro wire member
        rcases List.mem_map.mp member with ⟨index, _, rfl⟩
        rfl)) basis
  rw [liftSelectorStateOver_zeroSelectorKet p (rowSelectorWire p)
    (zeroAncillaJointBasis p system) (by intro index; rfl)] at prepared
  change applyOperator
      ((prepareUniformRowSelectorCircuit p).toIdealOperator primitiveGateOperator)
      (basisKet (zeroAncillaJointBasis p system)) basis = _ at prepared
  rw [applyOperator_basisKet] at prepared
  rw [prepared]

/-- 成功ブロックの行列要素は疎な状態パイプラインを成功基底で評価した値である。 -/
theorem uqCircuit_successBlock_apply
    (p : QParameters)
    (output input : RegisterBasis p.systemWidth) :
    qubitSuccessBlock (allZeroAncilla p.ancillaWidth)
        ((uqCircuit p).toIdealOperator primitiveGateOperator) output input =
      applyOperator
        (((prepareUniformRowSelectorCircuit p).reverse PrimitiveGate.inverse).toIdealOperator
          primitiveGateOperator)
        (qBeforeRowUniformInverseState p input)
        (zeroAncillaJointBasis p output) := by
  change (uqCircuit p).toIdealOperator primitiveGateOperator
      (zeroAncillaJointBasis p output) (zeroAncillaJointBasis p input) = _
  calc
    (uqCircuit p).toIdealOperator primitiveGateOperator
        (zeroAncillaJointBasis p output) (zeroAncillaJointBasis p input) =
      applyOperator ((uqCircuit p).toIdealOperator primitiveGateOperator)
        (basisKet (zeroAncillaJointBasis p input))
        (zeroAncillaJointBasis p output) :=
      (applyOperator_basisKet
        ((uqCircuit p).toIdealOperator primitiveGateOperator)
        (zeroAncillaJointBasis p input) (zeroAncillaJointBasis p output)).symm
    _ = _ := congrFun (uqCircuit_applyOperator_zeroAncilla p input)
      (zeroAncillaJointBasis p output)

/-- 成功ブロックの任意要素は、row一様状態と疎な前段状態との有限内積である。 -/
theorem uqCircuit_successBlock_eq_rowUniformOverlap
    (p : QParameters)
    (output input : RegisterBasis p.systemWidth) :
    qubitSuccessBlock (allZeroAncilla p.ancillaWidth)
        ((uqCircuit p).toIdealOperator primitiveGateOperator) output input =
      qRowUniformOverlap p output (qBeforeRowUniformInverseState p input) := by
  rw [uqCircuit_successBlock_apply]
  exact rowUniformReverse_applyOperator_zeroAncilla p output _

/--
成功基底一個が寄与する振幅。row受理条件、振幅判定の位相、column一様準備の
逆像振幅だけからなり、全幅行列は使用しない。
-/
noncomputable def qAcceptedPathContribution
    (p : QParameters)
    (output input : RegisterBasis p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : ℂ :=
  if QRowUniformBasisAccepted p output basis then
    ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
      (if (qDiscriminatorOutputPreimage p basis) (negativeWire p) &&
          (qDiscriminatorOutputPreimage p basis) (amplitudeSignalWire p)
        then -1 else 1) *
      qColumnPreparedState p input (qColumnPreparedPreimage p basis)
  else 0

/--
実際の基本ゲート列から得る成功ブロックは、受理基底の疎な有限和に一般`q,K`で一致する。
-/
theorem uqCircuit_successBlock_eq_acceptedPathSum
    (p : QParameters)
    (output input : RegisterBasis p.systemWidth) :
    qubitSuccessBlock (allZeroAncilla p.ancillaWidth)
        ((uqCircuit p).toIdealOperator primitiveGateOperator) output input =
      ∑ basis, qAcceptedPathContribution p output input basis := by
  rw [uqCircuit_successBlock_eq_rowUniformOverlap]
  rw [qRowUniformOverlap_eq_accepted_sum]
  apply Finset.sum_congr rfl
  intro basis _
  unfold qAcceptedPathContribution
  split
  · rw [qBeforeRowUniformInverseState_apply]
    ring
  · rfl

end

end ProbabilityGeneratorQProof
