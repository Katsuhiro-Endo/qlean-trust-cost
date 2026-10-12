import QLean.Generator.Implementation.ReversibleArithmetic

/-!
# 全基底を列挙しない疎な状態・振幅意味論

行列の列を計算基底ketへの作用として読み、可逆回路については行列積を展開せず
`runBasis`の一意な出力だけで振幅を記述する。量子ビット数に依存する状態列挙は行わない。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 任意の有限基底上で一個の計算基底状態だけに振幅1を持つket。 -/
abbrev basisKet {basis : Type*} [DecidableEq basis] : basis → basis → ℂ :=
  VerifiedCircuitCore.basisKet

/-- 作用素を状態ベクトルへ左から作用させる。 -/
abbrev applyOperator {basis : Type*} [Fintype basis] :
    Operator basis → (basis → ℂ) → basis → ℂ :=
  VerifiedCircuitCore.applyOperator

/-- 行列を計算基底ketへ作用させた出力振幅は、その行列の一要素に等しい。 -/
@[simp] theorem applyOperator_basisKet
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : Operator basis) (input output : basis) :
    applyOperator operator (basisKet input) output = operator output input := by
  exact VerifiedCircuitCore.applyOperator_basisKet operator input output

/-- 置換行列は状態関数の入力を置換するだけであり、有限和を展開する必要がない。 -/
theorem applyOperator_permMatrix
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (permutation : Equiv.Perm basis) (state : basis → ℂ) :
    applyOperator (permutation.permMatrix ℂ) state = state ∘ permutation := by
  exact VerifiedCircuitCore.applyOperator_permMatrix permutation state

/-- 可逆回路の行列作用は、合成済み基底置換による状態関数の合成に等しい。 -/
theorem reversibleCircuit_applyOperator
    {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (ReversibleGate ancillaQubits systemQubits))
    (state : JointBasis ancillaQubits systemQubits → ℂ) :
    applyOperator
        ((ReversibleCircuit.toPrimitive circuit).toIdealOperator
          primitiveGateOperator) state =
      state ∘ circuit.toBasisPermutation reversibleGatePermutation := by
  rw [ReversibleCircuit.toPrimitive_operator_eq_permMatrix]
  exact applyOperator_permMatrix _ _

/-- 可逆回路の行列要素は、`runBasis`が作る一個の出力でだけ1になる。 -/
theorem reversibleCircuit_basisAmplitude
    {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (ReversibleGate ancillaQubits systemQubits))
    (input output : JointBasis ancillaQubits systemQubits) :
    ((ReversibleCircuit.toPrimitive circuit).toIdealOperator
        primitiveGateOperator) output input =
      if output = circuit.runBasis reversibleGatePermutation input then 1 else 0 := by
  let operator := (ReversibleCircuit.toPrimitive circuit).toIdealOperator
    primitiveGateOperator
  calc
    operator output input = applyOperator operator (basisKet input) output :=
      (applyOperator_basisKet operator input output).symm
    _ = if output = circuit.runBasis reversibleGatePermutation input then 1 else 0 := by
      rw [reversibleCircuit_applyOperator]
      rw [Circuit.toBasisPermutation_eq_execution_inverse]
      · simp only [Function.comp_apply, basisKet,
          VerifiedCircuitCore.basisKet, VerifiedMath.Basis.vector]
        have equivalence :
            ((circuit.toExecutionPermutation reversibleGatePermutation)⁻¹ output = input) ↔
              output = circuit.runBasis reversibleGatePermutation input := by
          change
            ((circuit.toExecutionPermutation reversibleGatePermutation)⁻¹ output = input) ↔
              output = circuit.toExecutionPermutation reversibleGatePermutation input
          simpa only [Equiv.Perm.inv_def] using
            (Equiv.symm_apply_eq
              (circuit.toExecutionPermutation reversibleGatePermutation))
        simp only [equivalence]
      · intro gate
        cases gate <;> rfl

end

end ProbabilityGeneratorQProof
