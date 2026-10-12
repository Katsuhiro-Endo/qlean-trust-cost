import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic
import QLean.Circuits.Foundation.ReversibleLogic

/-!
# Fin-wire古典可逆stageの基本gate compiler

解析stageを型安全なX・CNOT・Toffoli ASTへcompileし、同じstageから
Permutation componentとPrimitive Exact componentを構成する。
-/

namespace VerifiedCircuitCore

noncomputable section

namespace ClassicalReversibleInstruction

/-- 古典可逆命令を対応する型安全なPrimitive gateへcompileする。 -/
def toPrimitiveGate {qubits : Nat} :
    ClassicalReversibleInstruction qubits → PrimitiveGate qubits
  | .xorOne target => .x target
  | .xorControlled control target different => .cnot control target different
  | .xorDoublyControlled control₁ control₂ target controlsDifferent
      firstDifferent secondDifferent =>
      .toffoli control₁ control₂ target controlsDifferent firstDifferent
        secondDifferent

theorem toPrimitiveGate_isSymbolFree {qubits : Nat}
    (instruction : ClassicalReversibleInstruction qubits) :
    PrimitiveGate.IsSymbolFree instruction.toPrimitiveGate := by
  cases instruction <;>
    simp [toPrimitiveGate, PrimitiveGate.IsSymbolFree]

/-- 古典命令をPrimitive gate意味論経由で作用素へ読む。 -/
def operator {qubits : Nat} (symbolValue : String → ℝ) :
    ClassicalReversibleInstruction qubits → Operator (QubitBasis qubits) :=
  fun instruction => primitiveGateOperatorWithSymbols symbolValue instruction.toPrimitiveGate

/-- 各古典命令のPrimitive作用素は直接基底作用の決定的作用素である。 -/
theorem operator_eq_deterministic {qubits : Nat} (symbolValue : String → ℝ)
    (instruction : ClassicalReversibleInstruction qubits) :
    instruction.operator symbolValue =
      deterministicOperator instruction.basisAction := by
  cases instruction with
  | xorOne target =>
      simp [operator, toPrimitiveGate, basisAction,
        primitiveXOperator_eq_deterministicOperator]
  | xorControlled control target different =>
      simp [operator, toPrimitiveGate, basisAction,
        reversibleAnalyticCnotOperator]
  | xorDoublyControlled control₁ control₂ target controlsDifferent
      firstDifferent secondDifferent =>
      simp [operator, toPrimitiveGate, basisAction, analyticToffoliOperator]

/-- 各古典命令のPrimitive作用素は解析置換行列に一致する。 -/
theorem operator_eq_reference_permMatrix {qubits : Nat}
    (symbolValue : String → ℝ)
    (instruction : ClassicalReversibleInstruction qubits) :
    instruction.operator symbolValue = instruction.reference⁻¹.permMatrix ℂ := by
  rw [operator_eq_deterministic]
  rw [deterministicOperator_eq_permMatrix_of_involutive
    instruction.basisAction instruction.basisAction_involutive]
  congr 1

/-- 一命令をPermutation componentとして包装する。 -/
def permutationComponent {qubits : Nat} (symbolValue : String → ℝ)
    (instruction : ClassicalReversibleInstruction qubits) :
    PermutationComponent
      (ClassicalReversibleInstruction.operator (qubits := qubits) symbolValue)
      (ClassicalReversibleInstruction.reference (qubits := qubits)) where
  circuit := .gate instruction
  reference := instruction.reference
  runBasis_correct := by intro input; rfl
  operator_correct := instruction.operator_eq_reference_permMatrix symbolValue

end ClassicalReversibleInstruction

namespace ClassicalReversibleStage

/-- 解析stageを同じ階層を持つ古典命令回路へ読む。 -/
def toCircuit {qubits : Nat} :
    ClassicalReversibleStage qubits →
      Circuit (ClassicalReversibleInstruction qubits)
  | .identity => .identity
  | .instruction value => .gate value
  | .seq first second => .seq first.toCircuit second.toCircuit
  | .repeat count body => .repeat count body.toCircuit

/-- 解析stageをPrimitive X・CNOT・Toffoli回路へcompileする。 -/
def compile {qubits : Nat} (stage : ClassicalReversibleStage qubits) :
    Circuit (PrimitiveGate qubits) :=
  stage.toCircuit.mapGates ClassicalReversibleInstruction.toPrimitiveGate

theorem compile_isSymbolFree {qubits : Nat}
    (stage : ClassicalReversibleStage qubits) :
    (stage.compile).IsSymbolFree := by
  unfold compile
  exact Circuit.isSymbolFree_mapGates
    ClassicalReversibleInstruction.toPrimitiveGate
    ClassicalReversibleInstruction.toPrimitiveGate_isSymbolFree
    stage.toCircuit

/-- stageの解析置換を子componentの公開契約から構成する。 -/
def permutationComponent {qubits : Nat} (symbolValue : String → ℝ) :
    (stage : ClassicalReversibleStage qubits) →
    PermutationComponent
      (ClassicalReversibleInstruction.operator (qubits := qubits) symbolValue)
      (ClassicalReversibleInstruction.reference (qubits := qubits))
  | .identity => PermutationComponent.identity
      (ClassicalReversibleInstruction.operator (qubits := qubits) symbolValue)
      (ClassicalReversibleInstruction.reference (qubits := qubits))
  | .instruction value => value.permutationComponent symbolValue
  | .seq first second =>
      PermutationComponent.seq (permutationComponent symbolValue first)
        (permutationComponent symbolValue second)
  | .repeat count body =>
      PermutationComponent.repeat count (permutationComponent symbolValue body)

/-- stage componentの回路fieldは解析stageの構文変換と一致する。 -/
theorem permutationComponent_circuit {qubits : Nat}
    (symbolValue : String → ℝ) (stage : ClassicalReversibleStage qubits) :
    (stage.permutationComponent symbolValue).circuit = stage.toCircuit := by
  induction stage with
  | identity => rfl
  | instruction value => rfl
  | seq first second firstInduction secondInduction =>
      simp [permutationComponent, PermutationComponent.seq,
        toCircuit, firstInduction, secondInduction]
  | «repeat» count body inductionHypothesis =>
      simp [permutationComponent, PermutationComponent.repeat,
        toCircuit, inductionHypothesis]

/-- stage componentの解析置換fieldは独立なstage referenceと一致する。 -/
theorem permutationComponent_reference {qubits : Nat}
    (symbolValue : String → ℝ) (stage : ClassicalReversibleStage qubits) :
    (stage.permutationComponent symbolValue).reference = stage.reference := by
  induction stage with
  | identity => rfl
  | instruction value => rfl
  | seq first second firstInduction secondInduction =>
      simp [permutationComponent, PermutationComponent.seq,
        reference, firstInduction, secondInduction]
  | «repeat» count body inductionHypothesis =>
      simp [permutationComponent, PermutationComponent.repeat,
        reference, inductionHypothesis]

/-- stageをPrimitive Exact componentへcompileする。 -/
def primitiveExactOperatorComponent {qubits : Nat}
    (symbolValue : String → ℝ) (stage : ClassicalReversibleStage qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  let permutation := stage.permutationComponent symbolValue
  let exact : ExactOperatorComponent
      (ClassicalReversibleInstruction.operator (qubits := qubits) symbolValue) :=
    { circuit := permutation.circuit
      target := permutation.reference⁻¹.permMatrix ℂ
      correct := permutation.operator_correct }
  ExactOperatorComponent.mapGates
    ClassicalReversibleInstruction.toPrimitiveGate (by intro instruction; rfl) exact

/-- Primitive Exact componentの回路はstage compiler ASTと一致する。 -/
theorem primitiveExactOperatorComponent_circuit {qubits : Nat}
    (symbolValue : String → ℝ) (stage : ClassicalReversibleStage qubits) :
    (stage.primitiveExactOperatorComponent symbolValue).circuit = stage.compile := by
  simp [primitiveExactOperatorComponent, compile,
    ExactOperatorComponent.mapGates, permutationComponent_circuit]

/-- Primitive Exact componentのtargetは独立なstage解析作用素である。 -/
theorem primitiveExactOperatorComponent_target {qubits : Nat}
    (symbolValue : String → ℝ) (stage : ClassicalReversibleStage qubits) :
    (stage.primitiveExactOperatorComponent symbolValue).target =
      stage.analyticOperator := by
  simp [primitiveExactOperatorComponent, analyticOperator,
    ExactOperatorComponent.mapGates, permutationComponent_reference]

/-- The primitive Exact component target preserves every wire outside the
stage support. -/
theorem primitiveExactOperatorComponent_target_preservesOutside {qubits : Nat}
    (symbolValue : String → ℝ) (stage : ClassicalReversibleStage qubits) :
    OperatorPreservesOutside stage.supportWires
      (stage.primitiveExactOperatorComponent symbolValue).target := by
  rw [primitiveExactOperatorComponent_target]
  exact analyticOperator_preservesOutside stage

/-- Exact primitive-gate component for XORing a natural-number constant into a
little-endian register. -/
def xorConstantExactComponent {qubits : Nat}
    (symbolValue : String → ℝ)
    (register : List (Fin qubits)) (constant : Nat) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  primitiveExactOperatorComponent symbolValue (xorConstant register constant)

/-- Exact primitive-gate component for XORing a register-to-constant equality
test into a target, with the multi-control work chain uncomputed. -/
def xorEqualityToConstantExactComponent {qubits : Nat}
    (symbolValue : String → ℝ)
    (register scratch : List (Fin qubits)) (constant : Nat)
    (target : Fin qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  primitiveExactOperatorComponent symbolValue
    (xorEqualityToConstantIntoTarget register scratch constant target)

/-- Exact component for the source-faithful minimum-work equality-to-constant
stage.  Its clean semantic contract is stated separately in the analytic
correctness layer. -/
def xorEqualityToConstantMinimumWorkExactComponent {qubits : Nat}
    (symbolValue : String → ℝ)
    (register scratch : List (Fin qubits)) (constant : Nat)
    (target : Fin qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  primitiveExactOperatorComponent symbolValue
    (xorEqualityToConstantIntoTargetMinimumWork
      register scratch constant target)

/-- Exact primitive-gate component for conjunction-controlled target XOR with
control preservation and AND-scratch uncomputation. -/
def xorConjunctionExactComponent {qubits : Nat}
    (symbolValue : String → ℝ)
    (controls scratch : List (Fin qubits)) (target : Fin qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  primitiveExactOperatorComponent symbolValue
    (xorConjunctionIntoTarget controls scratch target)

/-- Exact component for the source-faithful minimum-work conjunction stage.
For two controls and no scratch its circuit is the direct Toffoli. -/
def xorConjunctionMinimumWorkExactComponent {qubits : Nat}
    (symbolValue : String → ℝ)
    (controls scratch : List (Fin qubits)) (target : Fin qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  primitiveExactOperatorComponent symbolValue
    (xorConjunctionIntoTargetMinimumWork controls scratch target)

/-- Exact primitive-gate component for controlled modular increment of a
little-endian word, with every carry-control scratch chain uncomputed. -/
def controlledIncrementMod2PowExactComponent {qubits : Nat}
    (symbolValue : String → ℝ)
    (control : Fin qubits) (word scratch : List (Fin qubits)) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  primitiveExactOperatorComponent symbolValue
    (controlledIncrementWordMod2PowInPlace control word scratch)

end ClassicalReversibleStage

end

end VerifiedCircuitCore
