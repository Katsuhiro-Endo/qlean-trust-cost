import QLean.Circuits.Foundation.Foundations
import QLean.Circuits.Foundation.Circuit
import QLean.Circuits.Foundation.Gates
import QLean.Circuits.Foundation.PermutationSemantics
import QLean.Circuits.Foundation.Contracts
import QLean.Circuits.Foundation.Metrics
import QLean.Generator.Analysis.LinearAlgebra

/-!
# Q証明から共有coreを読むための狭いadapter

凍結Q sourceで使っていた基礎名を、`VerifiedCircuitCore`の実体へ接続する。
Q固有moduleは共有namespaceを直接開かず、このmoduleだけをimportする。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- gate型をparameterに取る回路AST。実体は共有coreの`Circuit`である。 -/
abbrev Circuit (Gate : Type*) := VerifiedCircuitCore.Circuit Gate

namespace Circuit

/-- 旧Q sourceが明示参照する二項逐次constructorを共有coreへ接続する。 -/
abbrev seq := @VerifiedCircuitCore.Circuit.seq

/-- Q側の既存公開語`toIdealOperator`を共有coreの`denote`へ接続する。 -/
abbrev toIdealOperator {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) : Circuit Gate → Operator basis :=
  VerifiedCircuitCore.Circuit.denote gateOperator

/-- 全gate葉がunitaryなら、Q側の理想作用素もunitaryである。証明は共有coreへ委譲する。 -/
theorem toIdealOperator_mem_unitaryGroup
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (gateUnitary : ∀ gate, gateOperator gate ∈ Matrix.unitaryGroup basis ℂ) :
    ∀ circuit : Circuit Gate,
      circuit.toIdealOperator gateOperator ∈ Matrix.unitaryGroup basis ℂ := by
  intro circuit
  exact VerifiedCircuitCore.Circuit.denote_mem_unitaryGroup
    gateOperator gateUnitary circuit

end Circuit

end

end ProbabilityGeneratorQProof

namespace VerifiedCircuitCore.Circuit

/-- Q互換field notationを共有core回路型のnamespaceにも公開する。 -/
abbrev toIdealOperator := @VerifiedCircuitCore.Circuit.denote

end VerifiedCircuitCore.Circuit
