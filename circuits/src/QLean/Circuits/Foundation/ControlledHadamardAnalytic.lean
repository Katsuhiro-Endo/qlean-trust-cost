import QLean.Circuits.Foundation.QuantumFourierAnalytic

/-!
# 7 gate controlled-H compilerの回路非依存解析仕様

記録角`h`を持つ分解のstrict作用素積と、controlが一のときだけ
`Ry(2h) * Z`を作用させる直接的semantic targetを分離する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 7 gate controlled-H分解の型安全な解析入力。 -/
structure ControlledHadamardSevenGateSpec (qubits : Nat) where
  /-- 制御wire。 -/
  control : Fin qubits
  /-- 標的wire。 -/
  target : Fin qubits
  /-- 制御wireと標的wireの相異性。 -/
  different : control ≠ target
  /-- 記録された四分角。semantic targetのRy角はその二倍である。 -/
  quarterAngle : AngleExpr

/-- 7局所作用を実行順の積として記録したstrict二wire target。 -/
def controlledHadamardSevenGateLocalProduct (quarterAngle : ℝ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (localCnotOperator * localOnTarget (localRy (-quarterAngle)) *
      localCnotOperator * localOnTarget (localRy quarterAngle)) *
    (localOnTarget localH * localCnotOperator * localOnTarget localH)

/-- 7 gate分解の各局所作用を任意wireへ埋めたstrict解析作用素。 -/
def controlledHadamardSevenGateStrictOperator {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledHadamardSevenGateSpec qubits) :
    Operator (QubitBasis qubits) :=
  embedTwoQubitOperator spec.control spec.target spec.different
    (controlledHadamardSevenGateLocalProduct
      (spec.quarterAngle.eval symbolValue))

/-- controlが一のときだけ`Ry(2h) * Z`を作用させる直接的semantic target。 -/
def controlledHadamardSemanticOperator {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledHadamardSevenGateSpec qubits) :
    Operator (QubitBasis qubits) :=
  embedControlledSingleQubitOperator spec.control spec.target spec.different
    (localRy (2 * spec.quarterAngle.eval symbolValue) * localZ)

/-- 任意四分角`h`に対しcontrolled-`(Ry(2h)·Z)`を表す7-gate族の正規名。 -/
abbrev ControlledRyZSevenGateSpec := ControlledHadamardSevenGateSpec

/-- 任意角7-gate族のstrict局所作用素積。 -/
def controlledRyZSevenGateStrictOperator {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRyZSevenGateSpec qubits) :
    Operator (QubitBasis qubits) :=
  controlledHadamardSevenGateStrictOperator symbolValue spec

/-- 任意角7-gate族の直接semantic target。 -/
def controlledRyZSemanticOperator {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRyZSevenGateSpec qubits) :
    Operator (QubitBasis qubits) :=
  embedControlledSingleQubitOperator spec.control spec.target spec.different
    (localRy (2 * spec.quarterAngle.eval symbolValue) * localZ)

/-- Hadamard特殊角componentのlayoutだけを保持する型安全入力。 -/
structure ControlledHadamardSpecialAngleSpec (qubits : Nat) where
  /-- 制御wire。 -/
  control : Fin qubits
  /-- 標的wire。 -/
  target : Fin qubits
  /-- 二wireの相異性。 -/
  different : control ≠ target

/-- Hadamard特殊化で使う厳密四分角`π/4`。 -/
def controlledHadamardQuarterAngle : AngleExpr :=
  .div .pi (.rational 4 1 (by decide))

/-- Hadamard特殊角layoutを任意角RyZ compiler入力へ埋め込む。 -/
def ControlledHadamardSpecialAngleSpec.toRyZ {qubits : Nat}
    (spec : ControlledHadamardSpecialAngleSpec qubits) :
    ControlledRyZSevenGateSpec qubits where
  control := spec.control
  target := spec.target
  different := spec.different
  quarterAngle := controlledHadamardQuarterAngle

/-- controlが一のときだけ局所Hadamardを作用させる独立semantic target。 -/
def controlledHadamardSpecialAngleOperator {qubits : Nat}
    (spec : ControlledHadamardSpecialAngleSpec qubits) :
    Operator (QubitBasis qubits) :=
  embedControlledSingleQubitOperator spec.control spec.target spec.different localH

end

end VerifiedCircuitCore
