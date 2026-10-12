import QLean.Generator.Implementation.CircuitUtilities

/-!
# 記号回転と制御回転の基本ゲート分解

非2冪一様準備で使う制御`Ry`を、新しい不透明ゲートを導入せず、二個の`Ry`と二個の
`CNOT`へ厳密に分解する。zero-controlも前後の`X`だけで構成する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 二つの`Ry`行列の積は角度和の`Ry`行列になる。 -/
theorem ryMatrix_mul (left right : ℝ) :
    ryMatrix left * ryMatrix right = ryMatrix (left + right) := by
  have halfAdd : (left + right) / 2 = left / 2 + right / 2 := by ring
  ext output input
  cases output <;> cases input <;>
    simp [Matrix.mul_apply, ryMatrix, halfAdd, Real.cos_add, Real.sin_add] <;>
    ring

/-- 角度0の`Ry`行列は恒等行列である。 -/
@[simp] theorem ryMatrix_zero : ryMatrix 0 = 1 := by
  ext output input
  cases output <;> cases input <;> simp [ryMatrix]

/-- Xで挟んだ`Ry(-θ)`は`Ry(θ)`に等しい。 -/
theorem x_ry_neg_x (angle : ℝ) :
    xMatrix * ryMatrix (-angle) * xMatrix = ryMatrix angle := by
  have cosNeg : Real.cos ((-angle) / 2) = Real.cos (angle / 2) := by
    rw [show (-angle) / 2 = -(angle / 2) by ring, Real.cos_neg]
  have sinNeg : Real.sin ((-angle) / 2) = -Real.sin (angle / 2) := by
    rw [show (-angle) / 2 = -(angle / 2) by ring, Real.sin_neg]
  ext output input
  cases output <;> cases input <;>
    simp [Matrix.mul_apply, xMatrix, ryMatrix, cosNeg, sinNeg]

/-- 固定二量子ビットで第一bitをcontrol、第二bitをtargetとするCNOT行列。 -/
def localCnotMatrix : Operator (Bool × Bool) :=
  Matrix.of fun output input =>
    if output.1 = input.1 ∧ output.2 = (if input.1 then !input.2 else input.2)
    then 1 else 0

/-- 固定二量子ビットのtarget側だけへ一量子ビット行列を作用させる。 -/
def localTargetMatrix (operator : Operator Bool) : Operator (Bool × Bool) :=
  Matrix.of fun output input =>
    if output.1 = input.1 then operator output.2 input.2 else 0

/-- controlが0なら恒等、1ならtargetへ`Ry(angle)`を作用させる固定二量子ビット行列。 -/
def localControlledRyMatrix (angle : ℝ) : Operator (Bool × Bool) :=
  Matrix.of fun output input =>
    if output.1 = input.1 then
      if input.1 then ryMatrix angle output.2 input.2
      else if output.2 = input.2 then 1 else 0
    else 0

/-- 二CNOT・二半角回転の局所4×4行列は理想controlled-`Ry`に厳密一致する。 -/
theorem local_controlledRy_decomposition (angle : ℝ) :
    localCnotMatrix * localTargetMatrix (ryMatrix (-angle / 2)) *
        localCnotMatrix * localTargetMatrix (ryMatrix (angle / 2)) =
      localControlledRyMatrix angle := by
  let quarter : ℂ := (angle : ℂ) / 2 / 2
  have negQuarter : -(angle : ℂ) / 2 / 2 = -quarter := by
    dsimp [quarter]
    ring
  have positiveQuarter : (angle : ℂ) / 2 / 2 = quarter := rfl
  have halfAngle : (angle : ℂ) / 2 = 2 * quarter := by
    simp [quarter]
    ring
  have cosHalf : Complex.cos ((angle : ℂ) / 2) =
      Complex.cos quarter ^ 2 - Complex.sin quarter ^ 2 := by
    rw [halfAngle, Complex.cos_two_mul']
  have sinHalf : Complex.sin ((angle : ℂ) / 2) =
      2 * Complex.sin quarter * Complex.cos quarter := by
    rw [halfAngle, Complex.sin_two_mul]
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases outputTarget <;>
    cases inputControl <;> cases inputTarget <;>
    simp only [Matrix.mul_apply] <;>
    simp_rw [Fintype.sum_prod_type] <;>
    simp [localCnotMatrix, localTargetMatrix,
      localControlledRyMatrix, ryMatrix]
  all_goals
    rw [negQuarter, positiveQuarter]
    simp only [Complex.cos_neg, Complex.sin_neg]
    try rw [cosHalf]
    try rw [sinHalf]
    ring_nf
  all_goals
    first
    | exact Complex.sin_sq_add_cos_sq quarter
    | exact Complex.cos_sq_add_sin_sq quarter

/-- 1-control `Ry(angle)`を二個の半角回転と二個のCNOTへ分解する。 -/
def controlledRyCircuit
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target) (angle : AngleExpr) :
    Circuit (PrimitiveGate ancillaQubits systemQubits) :=
  Circuit.fromList
    [.ry target angle.half,
      .cnot control target different,
      .ry target (.neg angle.half),
      .cnot control target different]

/-- 0-control `Ry`を、制御wireの前後Xと1-control回路だけで作る。 -/
def zeroControlledRyCircuit
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target) (angle : AngleExpr) :
    Circuit (PrimitiveGate ancillaQubits systemQubits) :=
  .seq (.gate (.x control)) <|
  .seq (controlledRyCircuit control target different angle) <|
  .gate (.x control)

/-- 制御値Boolに応じて1-controlまたは0-controlの`Ry`回路を選ぶ。 -/
def boolControlledRyCircuit
    {ancillaQubits systemQubits : Nat}
    (controlValue : Bool)
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target) (angle : AngleExpr) :
    Circuit (PrimitiveGate ancillaQubits systemQubits) :=
  if controlValue then
    controlledRyCircuit control target different angle
  else
    zeroControlledRyCircuit control target different angle

/-- すべての制御`Ry`分解は基本ゲートのユニタリ性だけからユニタリである。 -/
theorem boolControlledRyCircuit_unitary
    {ancillaQubits systemQubits : Nat}
    (controlValue : Bool)
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target) (angle : AngleExpr) :
    (boolControlledRyCircuit controlValue control target different angle).toIdealOperator
        primitiveGateOperator ∈
      Matrix.unitaryGroup (JointBasis ancillaQubits systemQubits) ℂ := by
  exact primitiveCircuit_mem_unitaryGroup _

/-- 制御`Ry`分解の葉は許可された5種類の基本ゲートだけである。 -/
theorem boolControlledRyCircuit_leaves
    {ancillaQubits systemQubits : Nat}
    (controlValue : Bool)
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target) (angle : AngleExpr) :
    ∀ gate ∈ (boolControlledRyCircuit controlValue control target different angle).flatten,
      IsAllowedPrimitiveGate gate :=
  primitiveCircuit_allLeavesAllowed _

end

end ProbabilityGeneratorQProof
