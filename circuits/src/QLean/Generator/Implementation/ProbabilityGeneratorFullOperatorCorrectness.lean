import QLean.Generator.Analysis.ProbabilityGeneratorFullOperator
import QLean.Generator.Implementation.OracleCanonicalFullStageCompiler
import QLean.Generator.Implementation.QVerifiedTopComponents
import QLean.Generator.Implementation.UniformPreparationFullOperatorCorrectness
import QLean.Generator.Implementation.QComponentRootAssembly

/-!
# 九段 Q 回路の全空間 Exact contract

九個の公開子 component を `ExactOperatorComponent.seq/reverse` だけで合成し、
正本 `uqCircuit` を独立な `ProbabilityGeneratorFullAnalyticOperator` へ結ぶ。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- pure Hadamard 行列は既存 primitive 意味論の Hadamard と一致する。 -/
theorem analyticHadamardMatrix_eq_hMatrix : analyticHadamardMatrix = hMatrix := by
  unfold analyticHadamardMatrix hMatrix hadamardCoefficient
  rfl

/-- COPY の既存公開 target は pure full-space target と一致する。 -/
theorem XorSystemIntoColumnKeyTargetOperator_eq_fullAnalytic (p : QParameters) :
    XorSystemIntoColumnKeyTargetOperator p =
      xorSystemIntoColumnKeyFullAnalyticOperator p := by
  exact reindexCanonicalCoreOperatorToJoint_eq_analytic _

/-- alignment の既存公開 target は pure full-space target と一致する。 -/
theorem ControlledOracleOutputAlignmentTargetOperator_eq_fullAnalytic
    (p : QParameters) :
    ControlledOracleOutputAlignmentTargetOperator p =
      outputAlignmentFullAnalyticOperator p := by
  rfl

/-- 最終反転の既存公開 target は pure full-space target と一致する。 -/
theorem FlipAmplitudeSignalTargetOperator_eq_fullAnalytic (p : QParameters) :
    FlipAmplitudeSignalTargetOperator p =
      amplitudeSignalFlipFullAnalyticOperator p := by
  rfl

/-- 振幅符号子の既存公開 target は四段の pure full-space target と一致する。 -/
theorem ActiveCopyNegativePhaseTargetOperator_eq_fullAnalytic (p : QParameters) :
    ActiveCopyNegativePhaseTargetOperator p = amplitudeSignFullAnalyticOperator p := by
  unfold ActiveCopyNegativePhaseTargetOperator amplitudeSignFullAnalyticOperator
  rw [analyticHadamardMatrix_eq_hMatrix]
  change onTwoWires (negativeWire p) (amplitudeSignalWire p)
      (negativeWire_ne_amplitudeSignalWire p) localControlledZMatrix *
        cnotMatrix (activeWire p) (amplitudeSignalWire p)
          (activeWire_ne_amplitudeSignalWire p) =
    onWire (amplitudeSignalWire p) hMatrix *
      (cnotMatrix (negativeWire p) (amplitudeSignalWire p)
        (negativeWire_ne_amplitudeSignalWire p) *
        (onWire (amplitudeSignalWire p) hMatrix *
          cnotMatrix (activeWire p) (amplitudeSignalWire p)
            (activeWire_ne_amplitudeSignalWire p)))
  symm
  rw [← Matrix.mul_assoc
    (cnotMatrix (negativeWire p) (amplitudeSignalWire p)
      (negativeWire_ne_amplitudeSignalWire p))
    (onWire (amplitudeSignalWire p) hMatrix)
    (cnotMatrix (activeWire p) (amplitudeSignalWire p)
      (activeWire_ne_amplitudeSignalWire p))]
  rw [← Matrix.mul_assoc
    (onWire (amplitudeSignalWire p) hMatrix)
    (cnotMatrix (negativeWire p) (amplitudeSignalWire p)
      (negativeWire_ne_amplitudeSignalWire p) *
      onWire (amplitudeSignalWire p) hMatrix)
    (cnotMatrix (activeWire p) (amplitudeSignalWire p)
      (activeWire_ne_amplitudeSignalWire p))]
  rw [embedded_h_cnot_h]

/-- 九段の子 component を実行順に二項 seq/reverse だけで合成する。 -/
def probabilityGeneratorFullExactOperatorComponent (p : QParameters) :
    ExactOperatorComponent (primitiveGateOperator
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  let columnUniform := prepareUniformColumnSelectorFullExactOperatorComponent p
  let copy := xorSystemIntoColumnKeyExactOperatorComponent p
  let columnOracle := OracleCanonicalTotalProgram.columnExactOperatorComponent p
  let amplitudeSign := activeCopyNegativePhaseExactOperatorComponent p
  let alignment := controlledOracleOutputAlignmentExactOperatorComponent p
  let columnOracleInverse := ExactOperatorComponent.reverse PrimitiveGate.inverse
    primitiveGateOperator_inverse columnOracle
  let rowOracle := OracleCanonicalTotalProgram.rowExactOperatorComponent p
  let amplitudeFlip := flipAmplitudeSignalExactOperatorComponent p
  let rowUniformInverse := ExactOperatorComponent.reverse PrimitiveGate.inverse
    primitiveGateOperator_inverse
    (prepareUniformRowSelectorFullExactOperatorComponent p)
  ExactOperatorComponent.seq columnUniform <|
    ExactOperatorComponent.seq copy <|
      ExactOperatorComponent.seq columnOracle <|
        ExactOperatorComponent.seq amplitudeSign <|
          ExactOperatorComponent.seq alignment <|
            ExactOperatorComponent.seq columnOracleInverse <|
              ExactOperatorComponent.seq rowOracle <|
                ExactOperatorComponent.seq amplitudeFlip rowUniformInverse

/-- root component の回路 field は九段正本 `uqCircuit` と定義的に同じASTである。 -/
theorem probabilityGeneratorFullExactOperatorComponent_circuit (p : QParameters) :
    (probabilityGeneratorFullExactOperatorComponent p).circuit = uqCircuit p := by
  change Circuit.seq
      (prepareUniformColumnSelectorFullExactOperatorComponent p).circuit
      (Circuit.seq (xorSystemIntoColumnKeyPrimitiveCircuit p)
        (Circuit.seq
          (OracleCanonicalTotalProgram.columnExactOperatorComponent p).circuit
          (Circuit.seq (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p)
            (Circuit.seq
              (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p)
              (Circuit.seq
                (Circuit.reverse PrimitiveGate.inverse
                  (OracleCanonicalTotalProgram.columnExactOperatorComponent p).circuit)
                (Circuit.seq
                  (OracleCanonicalTotalProgram.rowExactOperatorComponent p).circuit
                  (Circuit.seq (flipAmplitudeSignalPrimitiveCircuit p)
                    (Circuit.reverse PrimitiveGate.inverse
                      (prepareUniformRowSelectorFullExactOperatorComponent p).circuit)))))))) =
    uqCircuit p
  rw [prepareUniformColumnSelectorFullExactOperatorComponent_circuit,
    prepareUniformRowSelectorFullExactOperatorComponent_circuit,
    OracleCanonicalTotalProgram.columnExactOperatorComponent_circuit,
    OracleCanonicalTotalProgram.rowExactOperatorComponent_circuit]
  rfl

/-- root component の target は回路非依存な九段解析作用素である。 -/
theorem probabilityGeneratorFullExactOperatorComponent_target (p : QParameters) :
    (probabilityGeneratorFullExactOperatorComponent p).target =
      ProbabilityGeneratorFullAnalyticOperator p := by
  calc
    (probabilityGeneratorFullExactOperatorComponent p).target =
        (((((((Matrix.conjTranspose
              (prepareUniformRowSelectorFullExactOperatorComponent p).target *
            FlipAmplitudeSignalTargetOperator p) *
          (OracleCanonicalTotalProgram.rowExactOperatorComponent p).target) *
        Matrix.conjTranspose
          (OracleCanonicalTotalProgram.columnExactOperatorComponent p).target) *
      ControlledOracleOutputAlignmentTargetOperator p) *
    ActiveCopyNegativePhaseTargetOperator p) *
  (OracleCanonicalTotalProgram.columnExactOperatorComponent p).target) *
      XorSystemIntoColumnKeyTargetOperator p) *
        (prepareUniformColumnSelectorFullExactOperatorComponent p).target := by
      rfl
    _ = ProbabilityGeneratorFullAnalyticOperator p := by
      simp only [OracleCanonicalTotalProgram.columnExactOperatorComponent,
        OracleCanonicalTotalProgram.rowExactOperatorComponent]
      rw [prepareUniformColumnSelectorFullExactOperatorComponent_target,
        prepareUniformRowSelectorFullExactOperatorComponent_target,
        TotalOracleStageChildren.fullExactOperatorComponent_target,
        TotalOracleStageChildren.fullExactOperatorComponent_target,
        XorSystemIntoColumnKeyTargetOperator_eq_fullAnalytic,
        ActiveCopyNegativePhaseTargetOperator_eq_fullAnalytic,
        ControlledOracleOutputAlignmentTargetOperator_eq_fullAnalytic,
        FlipAmplitudeSignalTargetOperator_eq_fullAnalytic]
      rfl

/-- 正本 `uqCircuit` の全空間作用素は独立な九段 target と厳密一致する。 -/
theorem uqCircuit_denote_eq_ProbabilityGeneratorFullAnalyticOperator (p : QParameters) :
    (uqCircuit p).denote primitiveGateOperator =
      ProbabilityGeneratorFullAnalyticOperator p := by
  rw [← probabilityGeneratorFullExactOperatorComponent_circuit]
  rw [(probabilityGeneratorFullExactOperatorComponent p).correct]
  exact probabilityGeneratorFullExactOperatorComponent_target p

/-- full-space Exact 定理から同じ成功 block の `3K, ε=0` 系を得る。 -/
theorem ProbabilityGeneratorFullAnalyticOperator_blockEncoding_correct (p : QParameters) :
    IsApproxQubitBlockEncoding
      (allZeroAncilla p.ancillaWidth)
      (ProbabilityGeneratorFullAnalyticOperator p)
      (embeddedProbabilityGenerator p)
      (3 * p.K)
      0 := by
  rw [← uqCircuit_denote_eq_ProbabilityGeneratorFullAnalyticOperator]
  exact probabilityGeneratorScale3KErrorZeroBlockEncoding_correct p

/-- full-space Exact定理を成功block系として包装した再利用可能component。 -/
def probabilityGeneratorFullAnalyticBlockEncodingComponent (p : QParameters) :
    BlockEncodingComponent (primitiveGateOperator
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  BlockEncodingComponent.ofProof
    (uqCircuit p)
    (allZeroAncilla p.ancillaWidth)
    (embeddedProbabilityGenerator p)
    (3 * p.K)
    0
    (by
      change IsApproxQubitBlockEncoding
        (allZeroAncilla p.ancillaWidth)
        ((uqCircuit p).denote primitiveGateOperator)
        (embeddedProbabilityGenerator p) (3 * p.K) 0
      have selectorBlock :=
        probabilityGeneratorScale3KErrorZeroBlockEncoding_correct p
      unfold EmbeddedProbabilityGeneratorScale3KErrorZeroSpec at selectorBlock
      change IsApproxQubitBlockEncoding
        (allZeroAncilla p.ancillaWidth)
        ((uqCircuit p).denote primitiveGateOperator)
        (embeddedProbabilityGenerator p) (3 * p.K) 0 at selectorBlock
      rw [uqCircuit_denote_eq_ProbabilityGeneratorFullAnalyticOperator]
        at selectorBlock
      rw [uqCircuit_denote_eq_ProbabilityGeneratorFullAnalyticOperator]
      exact selectorBlock)

/-- 包装componentから公開block-encoding命題を取り出す。 -/
theorem probabilityGeneratorFullAnalyticBlockEncodingComponent_correct
    (p : QParameters) :
    IsApproxQubitBlockEncoding
      (allZeroAncilla p.ancillaWidth)
      ((uqCircuit p).denote primitiveGateOperator)
      (embeddedProbabilityGenerator p)
      (3 * p.K)
      0 :=
  (probabilityGeneratorFullAnalyticBlockEncodingComponent p).correct

end

end ProbabilityGeneratorQProof
