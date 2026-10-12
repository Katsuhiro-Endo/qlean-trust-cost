import QLean.Generator.Implementation.UniformPreparationSharedCoreFullExactAdapter

/-!
# 一様selector準備の共有core由来full-space Exact契約

公開名を保った薄いQ adapter。汎用一様準備の証明本体は共有coreにあり、ここでは
Q wire配置・restricted compiler・JointBasis付け替え・凍結AST transportだけを公開する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- column selector一様準備の共有core由来full-space Exact component。 -/
def prepareUniformColumnSelectorFullExactOperatorComponent (p : QParameters) :
    ExactOperatorComponent (primitiveGateOperator
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  prepareUniformColumnSelectorFullExactOperatorComponentSharedCore p

/-- row selector一様準備の共有core由来full-space Exact component。 -/
def prepareUniformRowSelectorFullExactOperatorComponent (p : QParameters) :
    ExactOperatorComponent (primitiveGateOperator
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  prepareUniformRowSelectorFullExactOperatorComponentSharedCore p

/-- column selector一様準備回路は共有coreの独立full-space targetに一致する。 -/
theorem prepareUniformColumnSelectorCircuit_denote_eq_fullAnalyticOperator
    (p : QParameters) :
    VerifiedCircuitCore.Circuit.denote primitiveGateOperator
        (prepareUniformColumnSelectorCircuit p) =
      sharedCoreColumnUniformPreparationFullAnalyticOperator p :=
  (prepareUniformColumnSelectorFullExactOperatorComponent p).correct

/-- row selector一様準備回路は共有coreの独立full-space targetに一致する。 -/
theorem prepareUniformRowSelectorCircuit_denote_eq_fullAnalyticOperator
    (p : QParameters) :
    VerifiedCircuitCore.Circuit.denote primitiveGateOperator
        (prepareUniformRowSelectorCircuit p) =
      sharedCoreRowUniformPreparationFullAnalyticOperator p :=
  (prepareUniformRowSelectorFullExactOperatorComponent p).correct

/-- column componentの回路fieldは凍結Q正本ASTである。 -/
theorem prepareUniformColumnSelectorFullExactOperatorComponent_circuit
    (p : QParameters) :
    (prepareUniformColumnSelectorFullExactOperatorComponent p).circuit =
      prepareUniformColumnSelectorCircuit p := by
  rfl

/-- column componentのtargetは回路非依存な共有core作用素である。 -/
theorem prepareUniformColumnSelectorFullExactOperatorComponent_target
    (p : QParameters) :
    (prepareUniformColumnSelectorFullExactOperatorComponent p).target =
      sharedCoreColumnUniformPreparationFullAnalyticOperator p := by
  rfl

/-- row componentの回路fieldは凍結Q正本ASTである。 -/
theorem prepareUniformRowSelectorFullExactOperatorComponent_circuit
    (p : QParameters) :
    (prepareUniformRowSelectorFullExactOperatorComponent p).circuit =
      prepareUniformRowSelectorCircuit p := by
  rfl

/-- row componentのtargetは回路非依存な共有core作用素である。 -/
theorem prepareUniformRowSelectorFullExactOperatorComponent_target
    (p : QParameters) :
    (prepareUniformRowSelectorFullExactOperatorComponent p).target =
      sharedCoreRowUniformPreparationFullAnalyticOperator p := by
  rfl

end

end ProbabilityGeneratorQProof
