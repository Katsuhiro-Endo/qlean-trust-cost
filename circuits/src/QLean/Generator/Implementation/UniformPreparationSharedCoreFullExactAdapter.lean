import QLean.Generator.Implementation.UniformPreparationSharedCoreAdapter
import QLean.Generator.Analysis.SharedUniformPreparationFullOperator
import QLean.Generator.Implementation.ComponentSemantics
import QLean.Circuits.Foundation.UniformPreparationFullOperatorCorrectness

/-!
# 共有一様準備full-space ExactのQ adapter

共有coreのfull-space Exact componentをQ wireへ配置し、restricted compilerで凍結
Q primitive ASTへ移し、最後に標準基底から所属付き`JointBasis`へ戻す。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 実装側と解析側の標準wire符号化は同一である。 -/
theorem wireToCanonicalFin_eq_analyticWireToCanonicalFin
    {ancillaQubits systemQubits : Nat}
    (wire : Wire ancillaQubits systemQubits) :
    wireToCanonicalFin wire = analyticWireToCanonicalFin wire := by
  cases wire <;> rfl

/-- 実装側と解析側の局所一様準備wire配置は一致する。 -/
theorem sharedUniformLocalWire_eq_analytic
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (index : Fin (2 * p.selectorWidth)) :
    sharedUniformLocalWire p selectorWire index =
      analyticSharedUniformLocalWire p selectorWire index := by
  unfold sharedUniformLocalWire analyticSharedUniformLocalWire
  split <;> rfl

/-- 実装側と解析側のinjective placementは外延的に一致する。 -/
theorem sharedUniformCorePlacement_eq_analytic
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (implementationDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (analyticDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (analyticUniformPreparationScratchWires p)) :
    sharedUniformCorePlacement p selectorWire selectorInjective
        implementationDisjoint =
      analyticSharedUniformCorePlacement p selectorWire selectorInjective
        analyticDisjoint := by
  apply Function.Embedding.ext
  intro index
  apply Fin.ext
  change (wireToCanonicalFin
      (sharedUniformLocalWire p selectorWire index)).val =
    (analyticWireToCanonicalFin
      (analyticSharedUniformLocalWire p selectorWire index)).val
  rw [wireToCanonicalFin_eq_analyticWireToCanonicalFin]
  rw [sharedUniformLocalWire_eq_analytic]

/-- 実装側と解析側の標準wire復号も一致する。 -/
theorem canonicalFinToWire_eq_analyticCanonicalFinToWire
    {ancillaQubits systemQubits : Nat}
    (index : Fin (ancillaQubits + systemQubits)) :
    canonicalFinToWire index = analyticCanonicalFinToWire index := by
  unfold canonicalFinToWire analyticCanonicalFinToWire
  split <;> rfl

/-- 二つの基底同値から作ったQへの作用素付け替えは同じ写像である。 -/
theorem reindexCanonicalCoreOperatorToJoint_eq_analytic
    {ancillaQubits systemQubits : Nat}
    (operator : VerifiedCircuitCore.Operator
      (VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits))) :
    reindexCanonicalCoreOperatorToJoint operator =
      analyticReindexCoreOperatorToJoint operator := by
  ext output input
  unfold reindexCanonicalCoreOperatorToJoint
    analyticReindexCoreOperatorToJoint
  change operator (jointBasisToCore output) (jointBasisToCore input) =
    operator
      (fun index => output (analyticCanonicalFinToWire index))
      (fun index => input (analyticCanonicalFinToWire index))
  apply congrArg₂ operator
  · funext index
    exact congrArg output
      (canonicalFinToWire_eq_analyticCanonicalFinToWire index)
  · funext index
    exact congrArg input
      (canonicalFinToWire_eq_analyticCanonicalFinToWire index)

/-- 共有full-space ExactをQの標準数値wire配置へ持ち上げる。 -/
def sharedUniformFullExactAtQLayout
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p)) :
    VerifiedCircuitCore.ExactOperatorComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := p.ancillaWidth + p.systemWidth) (fun _ => 0)) :=
  VerifiedCircuitCore.ExactOperatorComponent.mapPrimitiveWires
    (fun _ => 0)
    (sharedUniformCorePlacement p selectorWire selectorInjective
      selectorScratchDisjoint)
    (VerifiedCircuitCore.uniformPreparationFullExactOperatorComponent
      (sharedUniformPreparationParameters p))

/-- wire-lift後の共有full-space回路に現れる全leafはrestricted compiler可能である。 -/
theorem sharedUniformFullExactAtQLayout_leaf_compilable
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p))
    (gate : VerifiedCircuitCore.PrimitiveGate
      (p.ancillaWidth + p.systemWidth))
    (member : gate ∈
      (sharedUniformFullExactAtQLayout p selectorWire selectorInjective
        selectorScratchDisjoint).circuit.flatten) :
    SharedUniformGateCompilable gate := by
  unfold sharedUniformFullExactAtQLayout at member
  change gate ∈
    ((VerifiedCircuitCore.uniformPreparationCircuit
      (sharedUniformPreparationParameters p)).mapGates
        (VerifiedCircuitCore.PrimitiveGate.mapWires
          (sharedUniformCorePlacement p selectorWire selectorInjective
            selectorScratchDisjoint))).flatten at member
  rw [VerifiedCircuitCore.Circuit.flatten_mapGates] at member
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  apply primitiveGate_mapWires_sharedUniformGateCompilable
  exact uniformPreparationCircuit_sharedUniformCircuitCompilable
    (sharedUniformPreparationParameters p) source sourceMember

/-- restricted compilerで共有full-space ExactをQ primitive標準基底へ移す。 -/
def compiledSharedUniformFullExactOnCanonicalCore
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p)) :
    VerifiedCircuitCore.ExactOperatorComponent
      (qPrimitiveGateOperatorOnCanonicalCore
        (ancillaQubits := p.ancillaWidth)
        (systemQubits := p.systemWidth)) where
  circuit :=
    (sharedUniformFullExactAtQLayout p selectorWire selectorInjective
      selectorScratchDisjoint).circuit.compileGates compileSharedUniformCoreGate
  target :=
    (sharedUniformFullExactAtQLayout p selectorWire selectorInjective
      selectorScratchDisjoint).target
  correct := by
    let child := sharedUniformFullExactAtQLayout p selectorWire
      selectorInjective selectorScratchDisjoint
    rw [VerifiedCircuitCore.Circuit.denote_compileGates_monoidHom_of_mem
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := p.ancillaWidth + p.systemWidth) (fun _ => 0))
      qPrimitiveGateOperatorOnCanonicalCore compileSharedUniformCoreGate
      (MonoidHom.id (VerifiedCircuitCore.Operator
        (VerifiedCircuitCore.QubitBasis
          (p.ancillaWidth + p.systemWidth)))) child.circuit]
    · exact child.correct
    · intro gate member
      exact compileSharedUniformCoreGate_correct gate
        (sharedUniformFullExactAtQLayout_leaf_compilable p selectorWire
          selectorInjective selectorScratchDisjoint gate member)

/-- restricted compiler結果を所属付き`JointBasis`へ戻すfull-space Exact。 -/
def compiledSharedUniformFullExactOnJointBasis
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p)) :
    ExactOperatorComponent (primitiveGateOperator
      (ancillaQubits := p.ancillaWidth)
      (systemQubits := p.systemWidth)) :=
  VerifiedCircuitCore.ExactOperatorComponent.liftByCompiler
    (qPrimitiveGateOperatorOnCanonicalCore
      (ancillaQubits := p.ancillaWidth)
      (systemQubits := p.systemWidth))
    primitiveGateOperator id
    (reindexCanonicalCoreOperatorToJoint
      (ancillaQubits := p.ancillaWidth)
      (systemQubits := p.systemWidth))
    (fun gate => by
      change primitiveGateOperator gate =
        reindexCanonicalCoreOperatorToJoint
          (reindexJointOperatorToCanonicalCore (primitiveGateOperator gate))
      symm
      exact reindexCanonicalCoreOperatorToJoint_joint _)
    (compiledSharedUniformFullExactOnCanonicalCore p selectorWire
      selectorInjective selectorScratchDisjoint)

/-- JointBasisへ戻したcomponent targetの明示形。 -/
theorem compiledSharedUniformFullExactOnJointBasis_target
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p)) :
    (compiledSharedUniformFullExactOnJointBasis p selectorWire
      selectorInjective selectorScratchDisjoint).target =
      reindexCanonicalCoreOperatorToJoint
        (VerifiedCircuitCore.wireLiftOperator
          (sharedUniformCorePlacement p selectorWire selectorInjective
            selectorScratchDisjoint)
          (VerifiedCircuitCore.uniformPreparationFullAnalyticOperator
            (sharedUniformPreparationParameters p))) := by
  rfl

/-- full-space Exactのcompiled回路は凍結Q一様準備ASTに一致する。 -/
theorem compiledSharedUniformFullExactOnJointBasis_circuit_eq_frozen
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (selectorInjective : Function.Injective selectorWire)
    (selectorScratchDisjoint :
      ((List.finRange p.selectorWidth).map selectorWire).Disjoint
        (uniformScratchWires p)) :
    (compiledSharedUniformFullExactOnJointBasis p selectorWire
      selectorInjective selectorScratchDisjoint).circuit =
      prepareUniformSelectorOnWiresCircuit p selectorWire := by
  change
    (compileSharedUniformCircuitAtQLayout p selectorWire selectorInjective
      selectorScratchDisjoint
      (VerifiedCircuitCore.uniformPreparationCircuit
        (sharedUniformPreparationParameters p))).mapGates id = _
  rw [VerifiedCircuitCore.Circuit.mapGates_id]
  exact compileSharedUniformPreparationCircuit_eq_frozenOnWires p selectorWire
    selectorInjective selectorScratchDisjoint

/-- column側のimplementation/analytic placementは同一である。 -/
theorem sharedColumnUniformCorePlacement_eq_analytic (p : QParameters) :
    sharedUniformCorePlacement p (columnSelectorWire p)
        (sharedColumnSelectorWire_injective p)
        (sharedColumnSelector_uniformScratch_disjoint p) =
      analyticSharedUniformCorePlacement p (sharedUniformAnalyticColumnSelectorWire p)
        (sharedUniformAnalyticColumnSelectorWire_injective p)
        (sharedUniformAnalyticColumnSelector_scratch_disjoint p) := by
  change sharedUniformCorePlacement p (sharedUniformAnalyticColumnSelectorWire p)
      (sharedUniformAnalyticColumnSelectorWire_injective p)
      (sharedColumnSelector_uniformScratch_disjoint p) = _
  exact sharedUniformCorePlacement_eq_analytic p (sharedUniformAnalyticColumnSelectorWire p)
    (sharedUniformAnalyticColumnSelectorWire_injective p)
    (sharedColumnSelector_uniformScratch_disjoint p)
    (sharedUniformAnalyticColumnSelector_scratch_disjoint p)

/-- row側のimplementation/analytic placementは同一である。 -/
theorem sharedRowUniformCorePlacement_eq_analytic (p : QParameters) :
    sharedUniformCorePlacement p (rowSelectorWire p)
        (sharedRowSelectorWire_injective p)
        (sharedRowSelector_uniformScratch_disjoint p) =
      analyticSharedUniformCorePlacement p (sharedUniformAnalyticRowSelectorWire p)
        (sharedUniformAnalyticRowSelectorWire_injective p)
        (sharedUniformAnalyticRowSelector_scratch_disjoint p) := by
  change sharedUniformCorePlacement p (sharedUniformAnalyticRowSelectorWire p)
      (sharedUniformAnalyticRowSelectorWire_injective p)
      (sharedRowSelector_uniformScratch_disjoint p) = _
  exact sharedUniformCorePlacement_eq_analytic p (sharedUniformAnalyticRowSelectorWire p)
    (sharedUniformAnalyticRowSelectorWire_injective p)
    (sharedRowSelector_uniformScratch_disjoint p)
    (sharedUniformAnalyticRowSelector_scratch_disjoint p)

/-- 凍結column ASTを回路fieldに持つ共有core由来full-space Exact component。 -/
def prepareUniformColumnSelectorFullExactOperatorComponentSharedCore
    (p : QParameters) : ExactOperatorComponent (primitiveGateOperator
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) := by
  let child := compiledSharedUniformFullExactOnJointBasis p
    (columnSelectorWire p) (sharedColumnSelectorWire_injective p)
    (sharedColumnSelector_uniformScratch_disjoint p)
  exact
    { circuit := prepareUniformColumnSelectorCircuit p
      target := sharedCoreColumnUniformPreparationFullAnalyticOperator p
      correct := by
        change VerifiedCircuitCore.Circuit.denote primitiveGateOperator
            (prepareUniformSelectorOnWiresCircuit p (columnSelectorWire p)) = _
        rw [← compiledSharedUniformFullExactOnJointBasis_circuit_eq_frozen p
          (columnSelectorWire p) (sharedColumnSelectorWire_injective p)
          (sharedColumnSelector_uniformScratch_disjoint p)]
        rw [child.correct]
        rw [compiledSharedUniformFullExactOnJointBasis_target]
        rw [reindexCanonicalCoreOperatorToJoint_eq_analytic]
        rw [sharedColumnUniformCorePlacement_eq_analytic]
        rfl }

/-- 凍結row ASTを回路fieldに持つ共有core由来full-space Exact component。 -/
def prepareUniformRowSelectorFullExactOperatorComponentSharedCore
    (p : QParameters) : ExactOperatorComponent (primitiveGateOperator
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) := by
  let child := compiledSharedUniformFullExactOnJointBasis p
    (rowSelectorWire p) (sharedRowSelectorWire_injective p)
    (sharedRowSelector_uniformScratch_disjoint p)
  exact
    { circuit := prepareUniformRowSelectorCircuit p
      target := sharedCoreRowUniformPreparationFullAnalyticOperator p
      correct := by
        change VerifiedCircuitCore.Circuit.denote primitiveGateOperator
            (prepareUniformSelectorOnWiresCircuit p (rowSelectorWire p)) = _
        rw [← compiledSharedUniformFullExactOnJointBasis_circuit_eq_frozen p
          (rowSelectorWire p) (sharedRowSelectorWire_injective p)
          (sharedRowSelector_uniformScratch_disjoint p)]
        rw [child.correct]
        rw [compiledSharedUniformFullExactOnJointBasis_target]
        rw [reindexCanonicalCoreOperatorToJoint_eq_analytic]
        rw [sharedRowUniformCorePlacement_eq_analytic]
        rfl }

end

end ProbabilityGeneratorQProof
