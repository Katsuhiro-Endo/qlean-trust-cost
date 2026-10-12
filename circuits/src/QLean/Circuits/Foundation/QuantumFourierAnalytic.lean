import QLean.Circuits.Foundation.PrimitiveOperatorSemantics

/-! Local CNOT, tensor-factor, and controlled-phase operators. -/

namespace VerifiedCircuitCore

noncomputable section

/-- CNOT の回路非依存な基底置換作用素。 -/
def analyticCnotOperator {qubits : Nat} (control target : Fin qubits) :
    Operator (QubitBasis qubits) :=
  deterministicOperator fun input => xorWire target (input control) input

/-- control-target 順の二 bit 上で CNOT を表す局所置換行列。 -/
def localCnotOperator : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun output input =>
    if output = (input.1, input.2 != input.1) then 1 else 0

/-- 一 bit 行列を control 側へ作用させる二 bit 局所行列。 -/
def localOnControl (operator : Matrix Bool Bool ℂ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.kronecker operator (1 : Matrix Bool Bool ℂ)

/-- 一 bit 行列を target 側へ作用させる二 bit 局所行列。 -/
def localOnTarget (operator : Matrix Bool Bool ℂ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.kronecker (1 : Matrix Bool Bool ℂ) operator

/-- `|11⟩` 成分だけへ `exp(i angle)` を掛ける理想 controlled-phase 局所行列。 -/
def localControlledPhaseOperator (angle : ℝ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun output input =>
    if output ≠ input then 0
    else if input.1 && input.2 then
      Complex.exp (Complex.I * (angle : ℂ))
    else 1

/-- 任意の相異なる二 wire へ理想 controlled-phase を埋め込む。 -/
def analyticControlledPhaseOperator {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (angle : ℝ) : Operator (QubitBasis qubits) :=
  embedTwoQubitOperator control target different
    (localControlledPhaseOperator angle)

end

end VerifiedCircuitCore
