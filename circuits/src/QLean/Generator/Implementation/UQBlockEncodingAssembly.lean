import QLean.Generator.Implementation.QTopLevelStatePipeline

/-!
# 疎な成功ブロック等式から最終ブロックエンコーディングを組み立てる補題

oracleの基底作用から成功ブロック等式が得られた後に、ユニタリ性・正規化係数・誤差0を
機械的に合成する。最終無条件定理では、この等式を内部定理として適用する。
-/

namespace ProbabilityGeneratorQProof

open Matrix

noncomputable section

/-- 正規化係数`3K`は任意の正値`K`について正である。 -/
theorem three_mul_K_positive (p : QParameters) : (0 : ℝ) < 3 * p.K := by
  exact_mod_cast Nat.mul_pos (by decide : 0 < 3) p.K_pos

/--
実回路の成功ブロックが証明済みselector内積に一致すれば、実回路は直ちに誤差0の
`embeddedProbabilityGenerator`ブロックエンコーディングになる。
-/
theorem uqCircuit_correct_from_successBlock_eq
    (p : QParameters)
    (successEquality :
      qubitSuccessBlock (allZeroAncilla p.ancillaWidth)
          ((uqCircuit p).toIdealOperator primitiveGateOperator) =
        RowSelectorPathFiniteSumSuccessBlockSpec p) :
    IsApproxQubitBlockEncoding
      (allZeroAncilla p.ancillaWidth)
      ((uqCircuit p).toIdealOperator primitiveGateOperator)
      (embeddedProbabilityGenerator p)
      (3 * p.K)
      0 := by
  apply isApproxQubitBlockEncoding_zero_of_exact
  · exact uqCircuit_unitary p
  · exact three_mul_K_positive p
  · rw [successEquality, RowSelectorPathFiniteSumSuccessBlockSpec_eq_scaled_generator]
    have nonzero : (3 * (p.K : ℂ)) ≠ 0 := by
      norm_num
      exact_mod_cast (Nat.ne_of_gt p.K_pos)
    rw [smul_smul]
    push_cast
    change embeddedProbabilityGenerator p =
      ((3 * (p.K : ℂ)) * (1 / (3 * (p.K : ℂ)))) •
        embeddedProbabilityGenerator p
    rw [one_div, mul_inv_cancel₀ nonzero, one_smul]

end

end ProbabilityGeneratorQProof
