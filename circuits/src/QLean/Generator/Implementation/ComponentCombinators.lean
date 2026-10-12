import QLean.Generator.Implementation.ComponentSemantics
import QLean.Circuits.Foundation.Combinators

/-!
# 検証済み component 合成則への Q 用薄層

一般の回路・置換・clean・状態準備 component の合成則は
`VerifiedCircuitCore.Combinators` を唯一の正本とする。この module は、既存の
Q 証明で用いる名前を共有 API へ結ぶ薄い abbreviation と、Q 固有の
block-encoding constructor だけを提供する。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

namespace ExactOperatorComponent

/-- 共有 core の恒等 component。 -/
abbrev identity := @VerifiedCircuitCore.ExactOperatorComponent.identity

/-- 共有 core の実行順二項合成。 -/
abbrev seq := @VerifiedCircuitCore.ExactOperatorComponent.seq

/--
共有 core の gate 写像。Q v2 の明示的な二つの gate 意味論引数を保ち、
証明本体は core constructor へそのまま委譲する。
-/
abbrev mapGates
    {SourceGate TargetGate basis : Type*}
    [Fintype basis] [DecidableEq basis]
    (sourceOperator : SourceGate → Operator basis)
    (targetOperator : TargetGate → Operator basis)
    (mapGate : SourceGate → TargetGate)
    (mapCorrect : ∀ gate, targetOperator (mapGate gate) = sourceOperator gate)
    (component : ExactOperatorComponent sourceOperator) :
    ExactOperatorComponent targetOperator :=
  VerifiedCircuitCore.ExactOperatorComponent.mapGates
    mapGate mapCorrect component

/-- 共有 core の monoid-hom compiler lift。 -/
abbrev liftByCompiler := @VerifiedCircuitCore.ExactOperatorComponent.liftByCompiler

/-- 共有 core の反復合成。 -/
abbrev repeatComponent := @VerifiedCircuitCore.ExactOperatorComponent.repeatComponent

/-- 共有 core の有限列合成。 -/
abbrev sequenceComponents := @VerifiedCircuitCore.ExactOperatorComponent.sequenceComponents

/-- 共有 core の逆回路合成。 -/
abbrev reverse := @VerifiedCircuitCore.ExactOperatorComponent.reverse

end ExactOperatorComponent

namespace PermutationComponent

/-- 共有 core の恒等置換 component。 -/
abbrev identity := @VerifiedCircuitCore.PermutationComponent.identity

/-- 共有 core の involution compiler constructor。 -/
abbrev ofInvolutiveCircuit :=
  @VerifiedCircuitCore.PermutationComponent.ofInvolutiveCircuit

/-- 共有 core の置換 component 二項合成。 -/
abbrev seq := @VerifiedCircuitCore.PermutationComponent.seq

/-- 共有 core の置換 component 反復。 -/
abbrev repeatComponent := @VerifiedCircuitCore.PermutationComponent.repeatComponent

/-- 共有 core の置換 component 有限列合成。 -/
abbrev sequenceComponents := @VerifiedCircuitCore.PermutationComponent.sequenceComponents

/-- 共有 core の置換 component 逆実行。 -/
abbrev reverse := @VerifiedCircuitCore.PermutationComponent.reverse

end PermutationComponent

namespace CleanComponent

/-- 共有 core の恒等 clean component。 -/
abbrev identity := @VerifiedCircuitCore.CleanComponent.identity

/--
中間条件を明示的に保持する共有 core の合成則。
従来の Q 側 `seq` と同じ contract なので、この名前だけを薄く維持する。
-/
abbrev seq := @VerifiedCircuitCore.CleanComponent.seqWithConditions

/-- 共有 core の clean component 反復。 -/
abbrev repeatComponent := @VerifiedCircuitCore.CleanComponent.repeatComponent

/-- 共有 core の clean component 有限列合成。 -/
abbrev sequenceComponents := @VerifiedCircuitCore.CleanComponent.sequenceComponents

/-- 全入力置換 component を clean contract として読む共有則。 -/
abbrev ofPermutation := @VerifiedCircuitCore.CleanComponent.ofPermutation

/-- 共有 core の compute--use--uncompute 合成則。 -/
abbrev computeUseUncompute := @VerifiedCircuitCore.CleanComponent.computeUseUncompute

/-- 実装 reference を独立な解析 reference へ同定する共有則。 -/
abbrev refineReference := @VerifiedCircuitCore.CleanComponent.refineReference

end CleanComponent

namespace StatePreparationComponent

/-- 共有 core の逆状態準備に対する基底振幅公式。 -/
abbrev reverse_applyOperator_at_basis :=
  @VerifiedCircuitCore.StatePreparationComponent.reverse_applyOperator_at_basis

/-- 状態準備の後へ Exact component を接続する共有則。 -/
abbrev thenExact := @VerifiedCircuitCore.StatePreparationComponent.thenExact

end StatePreparationComponent

namespace BlockEncodingComponent

/-- 既証明の Q block-encoding 命題を Q 固有 contract に包装する。 -/
def ofProof
    {Gate : Type*} {ancillaQubits systemQubits : Nat}
    {gateOperator : Gate → Operator (JointBasis ancillaQubits systemQubits)}
    (circuit : Circuit Gate)
    (success : RegisterBasis ancillaQubits)
    (target : Operator (RegisterBasis systemQubits))
    (alpha epsilon : ℝ)
    (correct : IsApproxQubitBlockEncoding success
      (circuit.toIdealOperator gateOperator) target alpha epsilon) :
    BlockEncodingComponent gateOperator where
  circuit := circuit
  success := success
  target := target
  alpha := alpha
  epsilon := epsilon
  correct := correct

/-- Exact success block と回路の unitary 性から誤差 0 の Q contract を作る。 -/
def ofExactBlock
    {Gate : Type*} {ancillaQubits systemQubits : Nat}
    {gateOperator : Gate → Operator (JointBasis ancillaQubits systemQubits)}
    (gateUnitary : ∀ gate,
      gateOperator gate ∈
        Matrix.unitaryGroup (JointBasis ancillaQubits systemQubits) ℂ)
    (circuit : Circuit Gate)
    (success : RegisterBasis ancillaQubits)
    (target : Operator (RegisterBasis systemQubits))
    (alpha : ℝ)
    (alphaPositive : 0 < alpha)
    (exactBlock : target =
      (alpha : ℂ) • qubitSuccessBlock success
        (circuit.toIdealOperator gateOperator)) :
    BlockEncodingComponent gateOperator where
  circuit := circuit
  success := success
  target := target
  alpha := alpha
  epsilon := 0
  correct := isApproxQubitBlockEncoding_zero_of_exact success
    (circuit.toIdealOperator gateOperator) target alpha
    (Circuit.toIdealOperator_mem_unitaryGroup gateOperator gateUnitary circuit)
    alphaPositive exactBlock

end BlockEncodingComponent

end

end ProbabilityGeneratorQProof
