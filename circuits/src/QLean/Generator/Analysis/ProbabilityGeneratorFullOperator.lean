import QLean.Generator.Analysis.OracleCanonicalFullStage
import QLean.Generator.Analysis.QTopLevelAnalyticSpecs
import QLean.Generator.Analysis.SharedUniformPreparationFullOperator
import QLean.Generator.Analysis.PrimitiveOperators
import QLean.Circuits.Foundation.ReversibleLogicAnalytic

/-!
# Q 回路九段全体の回路非依存な全空間作用素

各段の解析作用素を実行順の逆向きに積み、dirty ancilla を含む全空間での
`U_Q` target を定義する。特定の回路実装moduleは参照しない。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- Hadamard の回路非依存な局所行列。 -/
def analyticHadamardMatrix : Operator Bool :=
  Matrix.of fun output input =>
    match output, input with
    | true, true => -((Real.sqrt 2 / 2 : ℝ) : ℂ)
    | _, _ => ((Real.sqrt 2 / 2 : ℝ) : ℂ)

/-- system から column key への XOR COPY の全空間解析作用素。 -/
def systemIntoColumnKeyCoreRegisterXorCopySpec (p : QParameters) :
    VerifiedCircuitCore.RegisterXorCopySpec
      (p.ancillaWidth + p.systemWidth) p.systemWidth where
  source := {
    wire := fun index => analyticCanonicalWireEquiv
      p.ancillaWidth p.systemWidth (.system index)
    injective := by
      intro left right equal
      exact Wire.system.inj
        ((analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective equal)
  }
  target := {
    wire := fun index => analyticCanonicalWireEquiv
      p.ancillaWidth p.systemWidth (analyticColumnKeyWire p index)
    injective := by
      intro left right equal
      apply (QLayout.canonical p).columnKey.index_injective
      exact Wire.ancilla.inj
        ((analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective equal)
  }
  disjoint := by
    intro sourceIndex targetIndex equal
    have wireEqual :=
      (analyticCanonicalWireEquiv p.ancillaWidth p.systemWidth).injective equal
    cases wireEqual

/-- systemからcolumn keyへのCOPYを共有pure register actionからQ基底へ移した作用素。 -/
def xorSystemIntoColumnKeyFullAnalyticOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  analyticReindexCoreOperatorToJoint
    (VerifiedCircuitCore.registerXorCopyPureOperator
      (systemIntoColumnKeyCoreRegisterXorCopySpec p))

/-- active と negative から amplitude signal を作る四段の全空間解析作用素。 -/
def amplitudeSignFullAnalyticOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  onWire (analyticAmplitudeSignalWire p) analyticHadamardMatrix *
    (cnotMatrix (OracleDiagonalTotalProgram.negativeWire p)
      (analyticAmplitudeSignalWire p)
      (by
        intro equal
        have values := congrArg analyticWireNumber equal
        simp [OracleDiagonalTotalProgram.negativeWire,
          analyticAmplitudeSignalWire, QLayout.canonical,
          RegisterSlice.ancillaWire, RegisterSlice.index,
          analyticWireNumber] at values
        omega) *
      (onWire (analyticAmplitudeSignalWire p) analyticHadamardMatrix *
        cnotMatrix (OracleDiagonalTotalProgram.activeWire p)
          (analyticAmplitudeSignalWire p)
          (by
            intro equal
            have values := congrArg analyticWireNumber equal
            simp [OracleDiagonalTotalProgram.activeWire,
              analyticAmplitudeSignalWire, QLayout.canonical,
              RegisterSlice.ancillaWire, RegisterSlice.index,
              analyticWireNumber] at values
            omega)))

/-- oracle 出力 alignment の全空間解析作用素。 -/
def outputAlignmentFullAnalyticOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  (controlledXorOracleOutputsIntoAlignedRegistersAnalyticPermutation p)⁻¹.permMatrix ℂ

/-- 最終 amplitude signal 反転の全空間解析作用素。 -/
def amplitudeSignalFlipFullAnalyticOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  (flipAmplitudeSignalAnalyticPermutation p)⁻¹.permMatrix ℂ

/--
一様 column 準備、COPY、column oracle、振幅符号、alignment、column oracle 逆、
row oracle、最終反転、row 一様準備逆の九段を表す独立な全空間作用素。
-/
def ProbabilityGeneratorFullAnalyticOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  (((((((Matrix.conjTranspose (sharedCoreRowUniformPreparationFullAnalyticOperator p) *
      amplitudeSignalFlipFullAnalyticOperator p) *
      OracleCanonicalTotalProgram.rowAnalyticOperator p) *
      Matrix.conjTranspose (OracleCanonicalTotalProgram.columnAnalyticOperator p)) *
      outputAlignmentFullAnalyticOperator p) *
      amplitudeSignFullAnalyticOperator p) *
      OracleCanonicalTotalProgram.columnAnalyticOperator p) *
      xorSystemIntoColumnKeyFullAnalyticOperator p) *
      sharedCoreColumnUniformPreparationFullAnalyticOperator p

end

end ProbabilityGeneratorQProof
