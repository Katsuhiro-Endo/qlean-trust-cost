import QLean.Generator.Implementation.PrimitiveCoreSemanticsAdapter
import QLean.Generator.Implementation.ProbabilityGeneratorFullOperatorCorrectness
import QLean.Circuits.Foundation.WireEmbedding

/-!
# 全空間Q作用素の共有core wire-lift adapter

Q固有の所属付き基底を標準Qubit基底へ付け替えた後、共有coreのinjective
wire-lift合成則で任意の大registerへ持ち上げる。公開targetは独立な九段解析作用素の
reindexとwire-liftであり、compile後回路の意味論から定義しない。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 九段Q回路を標準Qubit基底上の独立targetへ結ぶExact component。 -/
def probabilityGeneratorCanonicalCoreExactOperatorComponent (p : QParameters) :
    VerifiedCircuitCore.ExactOperatorComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := p.ancillaWidth + p.systemWidth) internalZeroSymbolEnvironment) where
  circuit := (uqCircuit p).mapGates PrimitiveGate.toCanonicalCore
  target := reindexJointOperatorToCanonicalCore
    (ProbabilityGeneratorFullAnalyticOperator p)
  correct := by
    rw [compileCircuitToCanonicalCore_denote]
    exact congrArg reindexJointOperatorToCanonicalCore
      (uqCircuit_denote_eq_ProbabilityGeneratorFullAnalyticOperator p)

/-- 九段Q回路を任意の大registerへ配置した共有core Exact component。 -/
def compileProbabilityGeneratorFullExactOperatorComponentToCore
    {totalQubits : Nat} (p : QParameters)
    (embedding : QWireEmbedding p.ancillaWidth p.systemWidth totalQubits) :
    VerifiedCircuitCore.ExactOperatorComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := totalQubits) internalZeroSymbolEnvironment) :=
  VerifiedCircuitCore.ExactOperatorComponent.mapPrimitiveWires
    internalZeroSymbolEnvironment embedding.placement
    (probabilityGeneratorCanonicalCoreExactOperatorComponent p)

/-- 大register版componentの回路fieldは公開compile入口と一致する。 -/
theorem compileProbabilityGeneratorFullExactOperatorComponentToCore_circuit
    {totalQubits : Nat} (p : QParameters)
    (embedding : QWireEmbedding p.ancillaWidth p.systemWidth totalQubits) :
    (compileProbabilityGeneratorFullExactOperatorComponentToCore p embedding).circuit =
      compileUQCircuitToCore p embedding := by
  unfold compileProbabilityGeneratorFullExactOperatorComponentToCore
    compileUQCircuitToCore compileCircuitToCore
    probabilityGeneratorCanonicalCoreExactOperatorComponent
    VerifiedCircuitCore.ExactOperatorComponent.mapPrimitiveWires
    PrimitiveGate.toEmbeddedCore
  exact circuit_mapGates_mapGates
    (VerifiedCircuitCore.PrimitiveGate.mapWires embedding.placement)
    PrimitiveGate.toCanonicalCore (uqCircuit p)

/-- 大register版targetは独立な九段作用素のreindexとwire-liftである。 -/
theorem compileProbabilityGeneratorFullExactOperatorComponentToCore_target
    {totalQubits : Nat} (p : QParameters)
    (embedding : QWireEmbedding p.ancillaWidth p.systemWidth totalQubits) :
    (compileProbabilityGeneratorFullExactOperatorComponentToCore p embedding).target =
      VerifiedCircuitCore.wireLiftOperator embedding.placement
        (reindexJointOperatorToCanonicalCore
          (ProbabilityGeneratorFullAnalyticOperator p)) := by
  rfl

/-- 大register版の正本回路はwire-liftした独立targetを厳密に実装する。 -/
theorem compileUQCircuitToCore_denote_eq_wireLiftFullAnalyticOperator
    {totalQubits : Nat} (p : QParameters)
    (embedding : QWireEmbedding p.ancillaWidth p.systemWidth totalQubits) :
    VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)
        (compileUQCircuitToCore p embedding) =
      VerifiedCircuitCore.wireLiftOperator embedding.placement
        (reindexJointOperatorToCanonicalCore
          (ProbabilityGeneratorFullAnalyticOperator p)) := by
  rw [← compileProbabilityGeneratorFullExactOperatorComponentToCore_circuit]
  exact (compileProbabilityGeneratorFullExactOperatorComponentToCore p embedding).correct

/-- 固定した外部bitのcoherent部分空間上で使うP17向けcomponent。 -/
def compileProbabilityGeneratorToFixedOutsideSubspace
    {totalQubits : Nat} (p : QParameters)
    (embedding : QWireEmbedding p.ancillaWidth p.systemWidth totalQubits)
    (outside : VerifiedCircuitCore.OutsideWire embedding.placement → Bool) :
    VerifiedCircuitCore.SubspaceOperatorComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := totalQubits) internalZeroSymbolEnvironment) :=
  VerifiedCircuitCore.ExactOperatorComponent.mapPrimitiveWiresToFixedOutsideSubspace
    internalZeroSymbolEnvironment embedding.placement outside
    (probabilityGeneratorCanonicalCoreExactOperatorComponent p)

end

end ProbabilityGeneratorQProof
