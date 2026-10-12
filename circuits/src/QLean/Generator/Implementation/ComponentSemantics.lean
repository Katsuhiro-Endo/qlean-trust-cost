import QLean.Generator.Implementation.CompositionalSemantics
import QLean.Generator.Implementation.QuantumSemanticsCorrectness
import QLean.Generator.Implementation.QubitBlockEncoding
import QLean.Circuits.Foundation.Contracts

/-!
# Q 証明で用いる component contract の薄い型層

一般の Exact / Permutation / Clean / StatePreparation contract は
`VerifiedCircuitCore.Contracts` を唯一の正本とする。この module はそれらを Q namespace
へ再公開し、Qubit block encoding に固有の contract だけを定義する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 回路全体の作用素が独立な解析作用素に厳密一致する共有 contract。 -/
abbrev ExactOperatorComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) :=
  VerifiedCircuitCore.ExactOperatorComponent gateOperator

/-- 可逆回路を独立な全域置換へ対応付ける共有 contract。 -/
abbrev PermutationComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (gatePermutation : Gate → Equiv.Perm basis) :=
  VerifiedCircuitCore.PermutationComponent gateOperator gatePermutation

/-- clean 入力条件、出力条件、work 復元を記録する共有 contract。 -/
abbrev CleanComponent
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis) :=
  VerifiedCircuitCore.CleanComponent gatePermutation

/-- 特定の初期状態から独立な解析目標状態を準備する共有 contract。 -/
abbrev StatePreparationComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) :=
  VerifiedCircuitCore.StatePreparationComponent gateOperator

/--
Qubit success block が解析 target を近似することを記録する Q 固有 contract。
`target` は回路の作用素意味論から定義してはならない。
-/
structure BlockEncodingComponent
    {Gate : Type*} {ancillaQubits systemQubits : Nat}
    (gateOperator : Gate → Operator (JointBasis ancillaQubits systemQubits)) where
  circuit : Circuit Gate
  success : RegisterBasis ancillaQubits
  target : Operator (RegisterBasis systemQubits)
  alpha : ℝ
  epsilon : ℝ
  correct :
    IsApproxQubitBlockEncoding success
      (circuit.toIdealOperator gateOperator) target alpha epsilon

/-- Q block-encoding contract から既存の述語形式を取り出す。 -/
theorem BlockEncodingComponent.isApproxQubitBlockEncoding
    {Gate : Type*} {ancillaQubits systemQubits : Nat}
    {gateOperator : Gate → Operator (JointBasis ancillaQubits systemQubits)}
    (component : BlockEncodingComponent gateOperator) :
    IsApproxQubitBlockEncoding component.success
      (component.circuit.toIdealOperator gateOperator)
      component.target component.alpha component.epsilon :=
  component.correct

end

end ProbabilityGeneratorQProof
