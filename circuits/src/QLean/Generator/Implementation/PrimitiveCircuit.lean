import QLean.Generator.Implementation.Gates
import QLean.Generator.Analysis.AngleExpr
import Mathlib.Tactic

/-!
# 記号角度とQ回路用の基本ゲート

大規模回路を全行列展開せずに扱うため、回路の葉を実行可能な記号角度付きの
`X`、`H`、`Ry`、`CNOT`、`Toffoli`へ固定する。このファイルでは各基本ゲートの
理想行列とユニタリ性だけを局所的に証明する。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

/-- Hadamard行列で共通に使う係数`1 / √2`。 -/
def hadamardCoefficient : ℝ := Real.sqrt 2 / 2

/-- Hadamardゲートの複素行列表現。 -/
def hMatrix : Operator Bool :=
  Matrix.of fun output input =>
    match output, input with
    | true, true => -(hadamardCoefficient : ℂ)
    | _, _ => (hadamardCoefficient : ℂ)

/-- Hadamard係数の二乗は`1/2`である。 -/
theorem hadamardCoefficient_sq : hadamardCoefficient ^ 2 = (1 : ℝ) / 2 := by
  rw [hadamardCoefficient]
  have sqrtSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    norm_num
  rw [div_pow, sqrtSq]
  norm_num

/-- The frozen Q coefficient is the shared core Hadamard scale. -/
theorem hadamardCoefficient_eq_invSqrtTwo :
    hadamardCoefficient = 1 / Real.sqrt 2 := by
  rw [hadamardCoefficient]
  have square : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  have nonzero : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The frozen Q Hadamard matrix is the shared core local Hadamard. -/
theorem hMatrix_eq_coreLocalH : hMatrix = VerifiedCircuitCore.localH := by
  ext output input
  cases output <;> cases input <;>
    simp [hMatrix, VerifiedCircuitCore.localH,
      hadamardCoefficient_eq_invSqrtTwo]

/-- Hadamard行列がユニタリであることを示す。 -/
theorem hMatrix_mem_unitaryGroup :
    hMatrix ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [hMatrix_eq_coreLocalH]
  exact VerifiedCircuitCore.localH_mem_unitaryGroup

-- 定義本体は回路非依存な`Analytic.PrimitiveOperators`に置く。

/-- 型安全なToffoli行列がユニタリであることを示す。 -/
theorem toffoliMatrix_mem_unitaryGroup
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (controlsDifferent : control₁ ≠ control₂)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target) :
    toffoliMatrix control₁ control₂ target controlsDifferent firstDifferent secondDifferent ∈
      Matrix.unitaryGroup (JointBasis ancillaQubits systemQubits) ℂ := by
  exact permMatrix_mem_unitaryGroup
    (toffoliBasisEquiv control₁ control₂ target controlsDifferent
      firstDifferent secondDifferent)

/-- Q回路の正本構文木で許可する五種類の基本ゲート。 -/
inductive PrimitiveGate (ancillaQubits systemQubits : Nat) where
  | x (target : Wire ancillaQubits systemQubits)
  | h (target : Wire ancillaQubits systemQubits)
  | ry (target : Wire ancillaQubits systemQubits) (angle : AngleExpr)
  | cnot
      (control target : Wire ancillaQubits systemQubits)
      (different : control ≠ target)
  | toffoli
      (control₁ control₂ target : Wire ancillaQubits systemQubits)
      (controlsDifferent : control₁ ≠ control₂)
      (firstDifferent : control₁ ≠ target)
      (secondDifferent : control₂ ≠ target)

/-- Q回路用の各基本ゲートに全ヒルベルト空間上の理想行列を与える。 -/
def primitiveGateOperator {ancillaQubits systemQubits : Nat} :
    PrimitiveGate ancillaQubits systemQubits →
      Operator (JointBasis ancillaQubits systemQubits)
  | .x target => onWire target xMatrix
  | .h target => onWire target hMatrix
  | .ry target angle => onWire target (ryMatrix angle.toReal)
  | .cnot control target different => cnotMatrix control target different
  | .toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      toffoliMatrix control₁ control₂ target controlsDifferent firstDifferent secondDifferent

/-- 五種類の基本ゲートはすべてユニタリな理想行列を持つ。 -/
theorem primitiveGateOperator_mem_unitaryGroup
    {ancillaQubits systemQubits : Nat}
    (gate : PrimitiveGate ancillaQubits systemQubits) :
    primitiveGateOperator gate ∈
      Matrix.unitaryGroup (JointBasis ancillaQubits systemQubits) ℂ := by
  cases gate with
  | x target =>
      exact onWire_mem_unitaryGroup target xMatrix xMatrix_mem_unitaryGroup
  | h target =>
      exact onWire_mem_unitaryGroup target hMatrix hMatrix_mem_unitaryGroup
  | ry target angle =>
      exact onWire_mem_unitaryGroup target (ryMatrix angle.toReal)
        (ryMatrix_mem_unitaryGroup angle.toReal)
  | cnot control target different =>
      exact cnotMatrix_mem_unitaryGroup control target different
  | toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      exact toffoliMatrix_mem_unitaryGroup control₁ control₂ target
        controlsDifferent firstDifferent secondDifferent

/-- 任意ワイヤへの埋込みは共役転置と可換である。 -/
theorem onWire_conjTranspose
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (operator : Operator Bool) :
    (onWire target operator)ᴴ = onWire target operatorᴴ := by
  simp [onWire, Matrix.conjTranspose_kronecker]

/-- X行列は自己共役である。 -/
theorem xMatrix_conjTranspose : xMatrixᴴ = xMatrix := by
  change star VerifiedCircuitCore.localX = VerifiedCircuitCore.localX
  exact VerifiedCircuitCore.star_localX

/-- Hadamard行列は自己共役である。 -/
theorem hMatrix_conjTranspose : hMatrixᴴ = hMatrix := by
  rw [hMatrix_eq_coreLocalH]
  exact VerifiedCircuitCore.star_localH

/-- `Ry`の逆角度の行列は元の`Ry`行列の共役転置である。 -/
theorem ryMatrix_neg_eq_conjTranspose (angle : ℝ) :
    ryMatrix (-angle) = (ryMatrix angle)ᴴ := by
  change VerifiedCircuitCore.localRy (-angle) =
    star (VerifiedCircuitCore.localRy angle)
  exact (VerifiedCircuitCore.star_localRy angle).symm

namespace PrimitiveGate

/-- 基本ゲートの実行順反転に用いる、各葉の逆ゲート。 -/
def inverse {ancillaQubits systemQubits : Nat} :
    PrimitiveGate ancillaQubits systemQubits →
      PrimitiveGate ancillaQubits systemQubits
  | .x target => .x target
  | .h target => .h target
  | .ry target angle => .ry target (.neg angle)
  | .cnot control target different => .cnot control target different
  | .toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      .toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent

end PrimitiveGate

/-- 各基本ゲートの逆ゲート意味論は、元の意味論の共役転置に一致する。 -/
theorem primitiveGateOperator_inverse
    {ancillaQubits systemQubits : Nat}
    (gate : PrimitiveGate ancillaQubits systemQubits) :
    primitiveGateOperator gate.inverse = (primitiveGateOperator gate)ᴴ := by
  cases gate with
  | x target =>
      simp only [PrimitiveGate.inverse, primitiveGateOperator]
      rw [onWire_conjTranspose, xMatrix_conjTranspose]
  | h target =>
      simp only [PrimitiveGate.inverse, primitiveGateOperator]
      rw [onWire_conjTranspose, hMatrix_conjTranspose]
  | ry target angle =>
      simp only [PrimitiveGate.inverse, primitiveGateOperator, AngleExpr.toReal_neg]
      rw [onWire_conjTranspose]
      exact congrArg (onWire target) (ryMatrix_neg_eq_conjTranspose angle.toReal)
  | cnot control target different =>
      simp only [PrimitiveGate.inverse, primitiveGateOperator, cnotMatrix]
      rw [Matrix.conjTranspose_permMatrix]
      congr 1
  | toffoli control₁ control₂ target controlsDifferent firstDifferent secondDifferent =>
      simp only [PrimitiveGate.inverse, primitiveGateOperator, toffoliMatrix]
      rw [Matrix.conjTranspose_permMatrix]
      congr 1

/-- 五種類の基本ゲートだけからなる任意の回路はユニタリである。 -/
theorem primitiveCircuit_mem_unitaryGroup
    {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (PrimitiveGate ancillaQubits systemQubits)) :
    circuit.toIdealOperator primitiveGateOperator ∈
      Matrix.unitaryGroup (JointBasis ancillaQubits systemQubits) ℂ :=
  Circuit.toIdealOperator_mem_unitaryGroup
    primitiveGateOperator primitiveGateOperator_mem_unitaryGroup circuit

end

end ProbabilityGeneratorQProof
