import QLean.Generator.Implementation.BlockEncoding
import QLean.Generator.Analysis.Registers

/-!
# Q固有の任意幅register block encoding

型安全な結合基底上の作用素から、アンシラ成功基底でsystem blockを切り出す。
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace ProbabilityGeneratorQProof

/-- Q結合基底の作用素からアンシラ成功基底で選ぶsystem行列block。 -/
def qubitSuccessBlock {ancillaQubits systemQubits : Nat}
    (success : RegisterBasis ancillaQubits)
    (operator : Operator (JointBasis ancillaQubits systemQubits)) :
    Operator (RegisterBasis systemQubits) :=
  Matrix.of fun output input =>
    operator (combineBasis success output) (combineBasis success input)

/-- 凍結Q定理と同一のL2作用素ノルム近似block encoding述語。 -/
def IsApproxQubitBlockEncoding
    {ancillaQubits systemQubits : Nat}
    (success : RegisterBasis ancillaQubits)
    (operator : Operator (JointBasis ancillaQubits systemQubits))
    (target : Operator (RegisterBasis systemQubits))
    (alpha epsilon : ℝ) : Prop :=
  operator ∈ Matrix.unitaryGroup (JointBasis ancillaQubits systemQubits) ℂ ∧
  0 < alpha ∧
  0 ≤ epsilon ∧
  ‖target - (alpha : ℂ) • qubitSuccessBlock success operator‖ ≤ epsilon

/-- 成功blockの厳密等式から誤差0のQ block encodingを得る。 -/
theorem isApproxQubitBlockEncoding_zero_of_exact
    {ancillaQubits systemQubits : Nat}
    (success : RegisterBasis ancillaQubits)
    (operator : Operator (JointBasis ancillaQubits systemQubits))
    (target : Operator (RegisterBasis systemQubits))
    (alpha : ℝ)
    (unitary : operator ∈ Matrix.unitaryGroup
      (JointBasis ancillaQubits systemQubits) ℂ)
    (alphaPositive : 0 < alpha)
    (exactBlock : target = (alpha : ℂ) • qubitSuccessBlock success operator) :
    IsApproxQubitBlockEncoding success operator target alpha 0 := by
  refine ⟨unitary, alphaPositive, le_rfl, ?_⟩
  rw [exactBlock, sub_self, norm_zero]

/-- Q結合基底blockは直積基底blockを同値で添字替えしたものに等しい。 -/
theorem qubitSuccessBlock_eq_reindexed_successBlock
    {ancillaQubits systemQubits : Nat}
    (success : RegisterBasis ancillaQubits)
    (operator : Operator (JointBasis ancillaQubits systemQubits)) :
    qubitSuccessBlock success operator =
      successBlock success
        (Matrix.reindex (productBasisEquiv ancillaQubits systemQubits).symm
          (productBasisEquiv ancillaQubits systemQubits).symm operator) := by
  rfl

end ProbabilityGeneratorQProof

