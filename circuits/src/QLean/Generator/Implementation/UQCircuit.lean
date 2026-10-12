import QLean.Generator.Implementation.QOracleCircuit

/-!
# 一般QブロックエンコーディングのLean正本回路

技術レポートの9段構成を、これまでに定義した基本ゲート回路だけで連結する。この定義が
JSON exporterと最終ブロックエンコーディング定理の唯一の回路正本である。
-/

namespace ProbabilityGeneratorQProof

open Matrix

/--
`R_{6K}`、COPY、column oracle、`D_amp`、`C_align`、column逆、row oracle、
最終X、row側`R_{6K}^{-1}`を実行順に連結した一般Q回路。
-/
def uqCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  .seq (prepareUniformColumnSelectorCircuit p) <|
  .seq (xorSystemIntoColumnKeyPrimitiveCircuit p) <|
  .seq (applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p) <|
  .seq (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p) <|
  .seq (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p) <|
  .seq ((applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p).reverse PrimitiveGate.inverse) <|
  .seq (applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit p) <|
  .seq (flipAmplitudeSignalPrimitiveCircuit p) <|
  (prepareUniformRowSelectorCircuit p).reverse PrimitiveGate.inverse

/-- `uqCircuit`の全葉が許可した`X/H/Ry/CNOT/Toffoli`のいずれかである。 -/
theorem uqCircuit_allLeavesAllowed (p : QParameters) :
    ∀ gate ∈ (uqCircuit p).flatten, IsAllowedPrimitiveGate gate :=
  primitiveCircuit_allLeavesAllowed _

/-- `uqCircuit`は任意の正値`q,K`について理想意味論でユニタリである。 -/
theorem uqCircuit_unitary (p : QParameters) :
    (uqCircuit p).toIdealOperator primitiveGateOperator ∈
      Matrix.unitaryGroup (JointBasis p.ancillaWidth p.systemWidth) ℂ :=
  primitiveCircuit_mem_unitaryGroup _

/-- column oracleの構文的逆は理想行列の共役転置に一致する。 -/
theorem reverseColumnOracleIdealOperator_eq_adjoint (p : QParameters) :
    ((applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p).reverse PrimitiveGate.inverse).toIdealOperator
        primitiveGateOperator =
      ((applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p).toIdealOperator primitiveGateOperator)ᴴ :=
  primitiveCircuit_reverse_correct _

/-- row一様準備の構文的逆は理想行列の共役転置に一致する。 -/
theorem reverseUniformRowSelectorPreparationIdealOperator_eq_adjoint (p : QParameters) :
    ((prepareUniformRowSelectorCircuit p).reverse PrimitiveGate.inverse).toIdealOperator
        primitiveGateOperator =
      ((prepareUniformRowSelectorCircuit p).toIdealOperator primitiveGateOperator)ᴴ :=
  primitiveCircuit_reverse_correct _

end ProbabilityGeneratorQProof
