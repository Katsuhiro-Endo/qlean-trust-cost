import QLean.Generator.Analysis.ClassicalReversibleStageAdapter
import QLean.Generator.Implementation.CompositionalSemantics
import QLean.Generator.Implementation.ComponentSemantics
import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.ClassicalReversibleStage

/-!
# 全dirty可逆stageの基本ゲートcompiler
-/

namespace ProbabilityGeneratorQProof

noncomputable section

namespace TotalReversibleInstruction

/-- 独立命令をQ証明の可逆基本ゲートへ変換する。 -/
def toReversibleGate {ancillaQubits systemQubits : Nat} :
    TotalReversibleInstruction ancillaQubits systemQubits →
      ReversibleGate ancillaQubits systemQubits
  | .xorOne target => .x target
  | .xorControlled control target different => .cnot control target different
  | .xorDoublyControlled control₁ control₂ target controlsDifferent
      firstDifferent secondDifferent =>
      .toffoli control₁ control₂ target controlsDifferent
        firstDifferent secondDifferent

/-- compiler後の一命令は同じ解析置換を持つ。 -/
theorem toReversibleGate_reference {ancillaQubits systemQubits : Nat}
    (instruction : TotalReversibleInstruction ancillaQubits systemQubits) :
    reversibleGatePermutation instruction.toReversibleGate = instruction.reference := by
  cases instruction <;> rfl

end TotalReversibleInstruction

namespace TotalReversibleStage

/-- 独立stageをQ証明の可逆基本ゲート構文木へ変換する。 -/
def compile {ancillaQubits systemQubits : Nat} :
    TotalReversibleStage ancillaQubits systemQubits →
      Circuit (ReversibleGate ancillaQubits systemQubits)
  | .identity => .identity
  | .instruction value => .gate value.toReversibleGate
  | .seq first second => .seq first.compile second.compile
  | .repeat count body => .repeat count body.compile

/-- 共有core命令をQ所属付きwireの可逆gateへ戻す。 -/
def coreInstructionToReversibleGate {ancillaQubits systemQubits : Nat}
    (instruction : VerifiedCircuitCore.ClassicalReversibleInstruction
      (ancillaQubits + systemQubits)) :
    ReversibleGate ancillaQubits systemQubits :=
  (TotalReversibleInstruction.ofCore instruction).toReversibleGate

/-- 共有core stageを凍結Q可逆gate構文木へ読み替えるQ固有compiler。 -/
def compileCoreStageToReversibleGate {ancillaQubits systemQubits : Nat}
    (stage : VerifiedCircuitCore.ClassicalReversibleStage
      (ancillaQubits + systemQubits)) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  stage.toCircuit.mapGates
    (coreInstructionToReversibleGate
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits))

@[simp] theorem compileCoreStageToReversibleGate_identity
    {ancillaQubits systemQubits : Nat} :
    compileCoreStageToReversibleGate
      (VerifiedCircuitCore.ClassicalReversibleStage.identity :
        VerifiedCircuitCore.ClassicalReversibleStage
          (ancillaQubits + systemQubits)) = .identity := rfl

@[simp] theorem compileCoreStageToReversibleGate_instruction
    {ancillaQubits systemQubits : Nat}
    (instruction : VerifiedCircuitCore.ClassicalReversibleInstruction
      (ancillaQubits + systemQubits)) :
    compileCoreStageToReversibleGate
      (.instruction instruction) =
        .gate (coreInstructionToReversibleGate instruction) := rfl

@[simp] theorem compileCoreStageToReversibleGate_seq
    {ancillaQubits systemQubits : Nat}
    (first second : VerifiedCircuitCore.ClassicalReversibleStage
      (ancillaQubits + systemQubits)) :
    compileCoreStageToReversibleGate (.seq first second) =
      .seq (compileCoreStageToReversibleGate first)
        (compileCoreStageToReversibleGate second) := rfl

@[simp] theorem compileCoreStageToReversibleGate_repeat
    {ancillaQubits systemQubits : Nat} (count : Nat)
    (body : VerifiedCircuitCore.ClassicalReversibleStage
      (ancillaQubits + systemQubits)) :
    compileCoreStageToReversibleGate (.repeat count body) =
      .repeat count (compileCoreStageToReversibleGate body) := rfl

/-- 共有core stage列のcompilerは各stage compilerの有限sequenceである。 -/
theorem compileCoreStageToReversibleGate_sequence
    {ancillaQubits systemQubits : Nat}
    (stages : List (VerifiedCircuitCore.ClassicalReversibleStage
      (ancillaQubits + systemQubits))) :
    compileCoreStageToReversibleGate
        (VerifiedCircuitCore.ClassicalReversibleStage.sequence stages) =
      VerifiedCircuitCore.Circuit.sequence
        (stages.map compileCoreStageToReversibleGate) := by
  induction stages with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [VerifiedCircuitCore.ClassicalReversibleStage.sequence,
        compileCoreStageToReversibleGate_seq, List.map_cons,
        VerifiedCircuitCore.Circuit.sequence, inductionHypothesis]

/-- 共有core stageの逆実行はQ compiler後の逆回路になる。 -/
theorem compileCoreStageToReversibleGate_reverse
    {ancillaQubits systemQubits : Nat}
    (stage : VerifiedCircuitCore.ClassicalReversibleStage
      (ancillaQubits + systemQubits)) :
    compileCoreStageToReversibleGate stage.reverse =
      (compileCoreStageToReversibleGate stage).reverse id := by
  induction stage with
  | identity => rfl
  | instruction value => rfl
  | seq first second firstInduction secondInduction =>
      simp only [VerifiedCircuitCore.ClassicalReversibleStage.reverse,
        compileCoreStageToReversibleGate_seq,
        VerifiedCircuitCore.Circuit.reverse, firstInduction, secondInduction]
  | «repeat» count body inductionHypothesis =>
      simp only [VerifiedCircuitCore.ClassicalReversibleStage.reverse,
        compileCoreStageToReversibleGate_repeat,
        VerifiedCircuitCore.Circuit.reverse, inductionHypothesis]

/--
共有core stageをQへ戻してcompileすることは、core構文木の各命令をQ gateへ写すことに等しい。
-/
theorem compile_ofCore {ancillaQubits systemQubits : Nat}
    (stage : VerifiedCircuitCore.ClassicalReversibleStage
      (ancillaQubits + systemQubits)) :
    (ofCore stage).compile = compileCoreStageToReversibleGate stage := by
  induction stage with
  | identity => rfl
  | instruction value => rfl
  | seq first second firstInduction secondInduction =>
      simp [ofCore, compile, compileCoreStageToReversibleGate,
        VerifiedCircuitCore.ClassicalReversibleStage.toCircuit,
        VerifiedCircuitCore.Circuit.mapGates, firstInduction, secondInduction]
  | «repeat» count body inductionHypothesis =>
      simp [ofCore, compile, compileCoreStageToReversibleGate,
        VerifiedCircuitCore.ClassicalReversibleStage.toCircuit,
        VerifiedCircuitCore.Circuit.mapGates, inductionHypothesis]

/-- 独立stageの逆転をcompileすると、可逆回路の逆実行になる。 -/
theorem compile_reverse {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    stage.reverse.compile = stage.compile.reverse id := by
  induction stage with
  | identity => rfl
  | instruction value => rfl
  | seq first second firstInduction secondInduction =>
      simp only [reverse, compile, VerifiedCircuitCore.Circuit.reverse,
        firstInduction, secondInduction]
  | «repeat» count body inductionHypothesis =>
      simp only [reverse, compile, VerifiedCircuitCore.Circuit.reverse,
        inductionHypothesis]

/-- 独立stage列をcompileすると、各子回路の有限sequenceになる。 -/
theorem compile_sequence {ancillaQubits systemQubits : Nat}
    (stages : List (TotalReversibleStage ancillaQubits systemQubits)) :
    (sequence stages).compile =
      VerifiedCircuitCore.Circuit.sequence (stages.map compile) := by
  induction stages with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [sequence, compile, List.map_cons,
        VerifiedCircuitCore.Circuit.sequence, inductionHypothesis]

/-- 同じ添字列から作るpure stage列と実装回路列は、各要素のcompiler一致から合成できる。 -/
theorem compile_sequence_map
    {Index : Type*} {ancillaQubits systemQubits : Nat}
    (indices : List Index)
    (makeStage : Index → TotalReversibleStage ancillaQubits systemQubits)
    (makeCircuit : Index → Circuit (ReversibleGate ancillaQubits systemQubits))
    (eachCorrect : ∀ index, (makeStage index).compile = makeCircuit index) :
    (sequence (indices.map makeStage)).compile =
      VerifiedCircuitCore.Circuit.sequence (indices.map makeCircuit) := by
  rw [compile_sequence]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  rw [List.map_map]
  apply List.map_congr_left
  intro index _
  exact eachCorrect index

/-- pure compute--use--uncomputeをcompileすると、同じ三段構造の実装回路になる。 -/
theorem compile_computeUseUncompute {ancillaQubits systemQubits : Nat}
    (compute use : TotalReversibleStage ancillaQubits systemQubits) :
    (computeUseUncompute compute use).compile =
      VerifiedCircuitCore.Circuit.computeUseUncompute id
        compute.compile use.compile := by
  simp [computeUseUncompute, compile, compile_reverse,
    VerifiedCircuitCore.Circuit.computeUseUncompute]

/-- 可逆基本ゲートの置換行列意味論。 -/
def reversibleBasisOperator {ancillaQubits systemQubits : Nat} :
    ReversibleGate ancillaQubits systemQubits →
      Operator (JointBasis ancillaQubits systemQubits) :=
  fun gate => (reversibleGatePermutation gate).permMatrix ℂ

/-- 独立stageのcompilerと解析置換を結ぶtotal Permutation component。 -/
def permutationComponent {ancillaQubits systemQubits : Nat} :
    (stage : TotalReversibleStage ancillaQubits systemQubits) →
      PermutationComponent
        (reversibleBasisOperator
          (ancillaQubits := ancillaQubits) (systemQubits := systemQubits))
        (reversibleGatePermutation
          (ancillaQubits := ancillaQubits) (systemQubits := systemQubits))
  | .identity =>
      VerifiedCircuitCore.PermutationComponent.identity
        reversibleBasisOperator reversibleGatePermutation
  | .instruction value =>
      { circuit := .gate value.toReversibleGate
        reference := value.reference
        runBasis_correct := by
          intro input
          change reversibleGatePermutation value.toReversibleGate input =
            value.reference input
          rw [value.toReversibleGate_reference]
        operator_correct := by
          change (reversibleGatePermutation value.toReversibleGate).permMatrix ℂ =
            value.reference⁻¹.permMatrix ℂ
          rw [value.toReversibleGate_reference]
          simpa [TotalReversibleInstruction.reverse] using congrArg
            (fun permutation => permutation.permMatrix ℂ)
            value.reference_reverse }
  | .seq first second =>
      VerifiedCircuitCore.PermutationComponent.seq
        (permutationComponent first) (permutationComponent second)
  | .repeat count body =>
      VerifiedCircuitCore.PermutationComponent.«repeat» count
        (permutationComponent body)

/-- total componentの回路fieldはstage compilerそのものである。 -/
theorem permutationComponent_circuit {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    stage.permutationComponent.circuit = stage.compile := by
  induction stage with
  | identity => rfl
  | instruction value => rfl
  | seq first second firstInduction secondInduction =>
      simp [permutationComponent, compile, firstInduction, secondInduction,
        VerifiedCircuitCore.PermutationComponent.seq]
  | «repeat» count body inductionHypothesis =>
      simp [permutationComponent, compile, inductionHypothesis,
        VerifiedCircuitCore.PermutationComponent.«repeat»]

/-- total componentのreference fieldは独立stage referenceそのものである。 -/
theorem permutationComponent_reference {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    stage.permutationComponent.reference = stage.reference := by
  induction stage with
  | identity => rfl
  | instruction value => rfl
  | seq first second firstInduction secondInduction =>
      simp [permutationComponent, reference, firstInduction, secondInduction,
        VerifiedCircuitCore.PermutationComponent.seq]
  | «repeat» count body inductionHypothesis =>
      simp [permutationComponent, reference, inductionHypothesis,
        VerifiedCircuitCore.PermutationComponent.«repeat»]

/-- stage compiler の全基底作用は、回路非依存な純粋 reference に一致する。 -/
theorem compiledStage_runBasis_eq_reference
    {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    VerifiedCircuitCore.Circuit.runBasis reversibleGatePermutation
        stage.compile input =
      stage.reference input := by
  rw [← stage.permutationComponent_circuit]
  rw [stage.permutationComponent.runBasis_correct]
  rw [stage.permutationComponent_reference]

/-- 独立stageを許可されたPrimitiveGate構文木へ直接compileしたExact component。 -/
def primitiveExactOperatorComponent {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    ExactOperatorComponent
      (primitiveGateOperator : PrimitiveGate ancillaQubits systemQubits →
        Operator (JointBasis ancillaQubits systemQubits)) :=
  VerifiedCircuitCore.ExactOperatorComponent.mapGates
    ReversibleGate.toPrimitive
    (fun gate => (reversibleGate_operator_eq_primitive gate).symm)
    stage.permutationComponent.toExactOperatorComponent

/-- Primitive Exact componentのtargetは独立stage解析作用素である。 -/
theorem primitiveExactOperatorComponent_target
    {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    stage.primitiveExactOperatorComponent.target = stage.analyticOperator := by
  change stage.permutationComponent.reference⁻¹.permMatrix ℂ =
    stage.reference⁻¹.permMatrix ℂ
  rw [stage.permutationComponent_reference]

/-- PrimitiveGate へ写した stage 回路は、独立な解析作用素へ厳密に一致する。 -/
theorem primitiveCircuit_denote_eq_analyticOperator
    {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    VerifiedCircuitCore.Circuit.denote primitiveGateOperator
        stage.primitiveExactOperatorComponent.circuit =
      stage.analyticOperator := by
  rw [stage.primitiveExactOperatorComponent.correct]
  exact stage.primitiveExactOperatorComponent_target

end TotalReversibleStage

end

end ProbabilityGeneratorQProof
