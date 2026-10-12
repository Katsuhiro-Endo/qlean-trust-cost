import QLean.Generator.Implementation.PrimitiveCircuit

/-!
# 全基底を展開しない合成的回路意味論

古典可逆部分を計算基底上の置換として評価し、その置換行列が既存の理想行列意味論と
一致することを回路構文に関する帰納法だけで証明する。量子ビット数に依存する全状態の
列挙は行わない。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

namespace Circuit

/-- 回路構造を保ったまま各葉のゲート型を写像する。 -/
abbrev map {Gate₁ Gate₂ : Type*} (translate : Gate₁ → Gate₂) :
    Circuit Gate₁ → Circuit Gate₂ :=
  VerifiedCircuitCore.Circuit.mapGates translate

/-- ゲート翻訳後の理想行列は、翻訳をゲート意味論へ合成した理想行列に等しい。 -/
theorem toIdealOperator_map
    {Gate₁ Gate₂ basis : Type*}
    [Fintype basis] [DecidableEq basis]
    (translate : Gate₁ → Gate₂)
    (gateOperator : Gate₂ → Operator basis) :
    ∀ circuit : Circuit Gate₁,
      (map translate circuit).toIdealOperator gateOperator =
        circuit.toIdealOperator (gateOperator ∘ translate) := by
  intro circuit
  exact VerifiedCircuitCore.Circuit.denote_mapGates gateOperator translate circuit

/-- 各ゲートの逆を与えて、実行順も反転した逆回路構文木を作る。 -/
abbrev reverse {Gate : Type*} (inverseGate : Gate → Gate) :
    Circuit Gate → Circuit Gate :=
  VerifiedCircuitCore.Circuit.reverse inverseGate

/-- 葉の逆が共役転置を表すなら、逆回路全体も元の回路の共役転置を表す。 -/
theorem toIdealOperator_reverse
    {Gate basis : Type*}
    [Fintype basis] [DecidableEq basis]
    (inverseGate : Gate → Gate)
    (gateOperator : Gate → Operator basis)
    (inverseCorrect : ∀ gate,
      gateOperator (inverseGate gate) = (gateOperator gate)ᴴ) :
    ∀ circuit : Circuit Gate,
      (reverse inverseGate circuit).toIdealOperator gateOperator =
        (circuit.toIdealOperator gateOperator)ᴴ := by
  intro circuit
  exact VerifiedCircuitCore.Circuit.denote_reverse inverseGate gateOperator
    inverseCorrect circuit

end Circuit

/-- Q回路の構文的逆回路は、理想行列の共役転置を正確に表す。 -/
theorem primitiveCircuit_reverse_correct
    {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (PrimitiveGate ancillaQubits systemQubits)) :
    (circuit.reverse PrimitiveGate.inverse).toIdealOperator primitiveGateOperator =
      (circuit.toIdealOperator primitiveGateOperator)ᴴ := by
  exact Circuit.toIdealOperator_reverse PrimitiveGate.inverse primitiveGateOperator
    primitiveGateOperator_inverse circuit

/-- 計算基底を決定的に置換する三種類の可逆基本ゲート。 -/
inductive ReversibleGate (ancillaQubits systemQubits : Nat) where
  | x (target : Wire ancillaQubits systemQubits)
  | cnot
      (control target : Wire ancillaQubits systemQubits)
      (different : control ≠ target)
  | toffoli
      (control₁ control₂ target : Wire ancillaQubits systemQubits)
      (controlsDifferent : control₁ ≠ control₂)
      (firstDifferent : control₁ ≠ target)
      (secondDifferent : control₂ ≠ target)

/-- 可逆基本ゲートを計算基底上の置換として解釈する。 -/
def reversibleGatePermutation {ancillaQubits systemQubits : Nat} :
    ReversibleGate ancillaQubits systemQubits →
      Equiv.Perm (JointBasis ancillaQubits systemQubits)
  | .x target => xBasisEquiv target
  | .cnot control target different => cnotBasisEquiv control target different
  | .toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      toffoliBasisEquiv control₁ control₂ target controlsDifferent
        firstDifferent secondDifferent

/-- 可逆基本ゲートをQ回路正本の基本ゲートへ埋め込む。 -/
def ReversibleGate.toPrimitive {ancillaQubits systemQubits : Nat} :
    ReversibleGate ancillaQubits systemQubits →
      PrimitiveGate ancillaQubits systemQubits
  | .x target => .x target
  | .cnot control target different => .cnot control target different
  | .toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      .toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent

/-- 可逆ゲート回路全体が計算基底へ及ぼす置換を、構文的に合成する。 -/
abbrev Circuit.toBasisPermutation
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis) :
    Circuit Gate → Equiv.Perm basis :=
  VerifiedCircuitCore.Circuit.toCompositionPermutation gatePermutation

/-- 可逆回路の実行順どおりに計算基底へ作用する置換を合成する。 -/
abbrev Circuit.toExecutionPermutation
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis) :
    Circuit Gate → Equiv.Perm basis :=
  VerifiedCircuitCore.Circuit.toExecutionPermutation gatePermutation

/-- 可逆回路を、実行順に合成済みの置換によって計算基底へ一回作用させる。 -/
abbrev Circuit.runBasis
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (circuit : Circuit Gate)
    (basisState : basis) : basis :=
  VerifiedCircuitCore.Circuit.runBasis gatePermutation circuit basisState

/-- compute、use、computeの逆実行を一つの回路構文へまとめる。 -/
abbrev Circuit.computeUseUncompute
    {Gate : Type*} (inverseGate : Gate → Gate)
    (compute use : Circuit Gate) : Circuit Gate :=
  VerifiedCircuitCore.Circuit.computeUseUncompute inverseGate compute use

/-- 葉の置換が正しい逆なら、構文的逆回路の基底置換は元の置換の逆である。 -/
theorem Circuit.toExecutionPermutation_reverse
    {Gate basis : Type*}
    (inverseGate : Gate → Gate)
    (gatePermutation : Gate → Equiv.Perm basis)
    (inverseCorrect : ∀ gate,
      gatePermutation (inverseGate gate) = (gatePermutation gate)⁻¹) :
    ∀ circuit : Circuit Gate,
      (circuit.reverse inverseGate).toExecutionPermutation gatePermutation =
        (circuit.toExecutionPermutation gatePermutation)⁻¹ := by
  intro circuit
  exact VerifiedCircuitCore.Circuit.toExecutionPermutation_reverse
    inverseGate gatePermutation inverseCorrect circuit

/-- compute--use--uncomputeの基底作用を、三つの置換の合成として展開する。 -/
theorem Circuit.runBasis_computeUseUncompute
    {Gate basis : Type*}
    (inverseGate : Gate → Gate)
    (gatePermutation : Gate → Equiv.Perm basis)
    (inverseCorrect : ∀ gate,
      gatePermutation (inverseGate gate) = (gatePermutation gate)⁻¹)
    (compute use : Circuit Gate) (input : basis) :
    (computeUseUncompute inverseGate compute use).runBasis gatePermutation input =
      (compute.toExecutionPermutation gatePermutation)⁻¹
        (use.toExecutionPermutation gatePermutation
          (compute.toExecutionPermutation gatePermutation input)) := by
  exact VerifiedCircuitCore.Circuit.runBasis_computeUseUncompute
    inverseGate gatePermutation inverseCorrect compute use input

/-- use後の状態が別入力のcompute像なら、uncompute後はその別入力へ厳密に戻る。 -/
theorem Circuit.computeUseUncompute_clean
    {Gate basis : Type*}
    (inverseGate : Gate → Gate)
    (gatePermutation : Gate → Equiv.Perm basis)
    (inverseCorrect : ∀ gate,
      gatePermutation (inverseGate gate) = (gatePermutation gate)⁻¹)
    (compute use : Circuit Gate) (input output : basis)
    (useResult :
      use.toExecutionPermutation gatePermutation
          (compute.toExecutionPermutation gatePermutation input) =
        compute.toExecutionPermutation gatePermutation output) :
    (computeUseUncompute inverseGate compute use).runBasis gatePermutation input = output :=
  VerifiedCircuitCore.Circuit.computeUseUncompute_clean inverseGate gatePermutation
    inverseCorrect compute use input output useResult

/-- 置換行列意味論による回路評価は、合成済み基底置換の置換行列に等しい。 -/
theorem Circuit.toIdealOperator_permMatrix_eq
    {Gate basis : Type*}
    [Fintype basis] [DecidableEq basis]
    (gatePermutation : Gate → Equiv.Perm basis) :
    ∀ circuit : Circuit Gate,
      circuit.toIdealOperator (fun gate => (gatePermutation gate).permMatrix ℂ) =
        (circuit.toBasisPermutation gatePermutation).permMatrix ℂ :=
  VerifiedCircuitCore.Circuit.denote_permMatrix_eq_toCompositionPermutation
    gatePermutation

/-- 各葉が自己逆なら、行列用置換は実行順置換の逆に等しい。 -/
theorem Circuit.toBasisPermutation_eq_execution_inverse
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (gateInvolutive : ∀ gate, gatePermutation gate = (gatePermutation gate)⁻¹) :
    ∀ circuit : Circuit Gate,
      circuit.toBasisPermutation gatePermutation =
        (circuit.toExecutionPermutation gatePermutation)⁻¹ :=
  VerifiedCircuitCore.Circuit.toCompositionPermutation_eq_execution_inverse
    gatePermutation gateInvolutive

/-- Xの全体作用素は、Xの計算基底置換行列と一致する。 -/
theorem x_onWire_eq_permMatrix
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits) :
    onWire target xMatrix = (xBasisEquiv target).permMatrix ℂ := by
  ext output input
  rw [onWire_apply]
  by_cases sameOutside : SameOutside target output input
  · have outputEq :
        output = xBasisAction target input ↔ output target = !(input target) := by
      constructor
      · intro equal
        simpa [xBasisAction] using congrFun equal target
      · intro targetEqual
        funext wire
        by_cases isTarget : wire = target
        · subst wire
          simpa [xBasisAction] using targetEqual
        · simp [xBasisAction, isTarget, sameOutside wire isTarget]
    simp [sameOutside, xMatrix, xBasisEquiv, Equiv.Perm.permMatrix,
      PEquiv.toMatrix, xBasisAction_eq_iff, outputEq]
  · have outputNe : output ≠ xBasisAction target input := by
      intro equal
      apply sameOutside
      intro wire different
      rw [equal]
      simp [xBasisAction, different]
    simp [sameOutside, xBasisEquiv, Equiv.Perm.permMatrix,
      PEquiv.toMatrix, xBasisAction_eq_iff, outputNe]

/-- 可逆基本ゲートの置換行列は、対応するQ回路基本ゲートの理想行列に一致する。 -/
theorem reversibleGate_operator_eq_primitive
    {ancillaQubits systemQubits : Nat}
    (gate : ReversibleGate ancillaQubits systemQubits) :
    (reversibleGatePermutation gate).permMatrix ℂ =
      primitiveGateOperator gate.toPrimitive := by
  cases gate with
  | x target =>
      exact (x_onWire_eq_permMatrix target).symm
  | cnot control target different =>
      rfl
  | toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      rfl

/-- 可逆回路を基本ゲート回路へ翻訳しても、合成済み置換行列の意味は保存される。 -/
theorem reversibleCircuit_operator_eq_permMatrix
    {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (ReversibleGate ancillaQubits systemQubits)) :
    (circuit.map ReversibleGate.toPrimitive).toIdealOperator primitiveGateOperator =
      (circuit.toBasisPermutation reversibleGatePermutation).permMatrix ℂ := by
  rw [Circuit.toIdealOperator_map]
  trans circuit.toIdealOperator
      (fun gate => (reversibleGatePermutation gate).permMatrix ℂ)
  · apply congrArg (Circuit.toIdealOperator · circuit)
    funext gate
    exact (reversibleGate_operator_eq_primitive gate).symm
  · exact Circuit.toIdealOperator_permMatrix_eq reversibleGatePermutation circuit

end

end ProbabilityGeneratorQProof
