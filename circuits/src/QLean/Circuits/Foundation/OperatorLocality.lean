import QLean.Circuits.Foundation.OperatorLocalityAnalytic
import QLean.Circuits.Foundation.PrimitiveGateProofs

/-!
# Embedded-gate support locality

The independent locality contract lives in `OperatorLocalityAnalytic`; this
module supplies its one- and two-wire primitive embedding instances.
-/

namespace VerifiedCircuitCore

noncomputable section

namespace OperatorPreservesOutside

/-- A one-wire embedding preserves every other basis wire. -/
theorem embedSingleQubitOperator {qubits : Nat}
    (target : Fin qubits) (localOperator : Matrix Bool Bool ℂ) :
    OperatorPreservesOutside {target}
      (embedSingleQubitOperator target localOperator) := by
  intro output input nonzero wire outside
  rw [VerifiedCircuitCore.embedSingleQubitOperator_apply] at nonzero
  by_cases agrees : agreesExcept target output input
  · apply agrees wire
    simpa using outside
  · simp [agrees] at nonzero

/-- A two-wire embedding preserves every basis wire outside its two operands. -/
theorem embedTwoQubitOperator {qubits : Nat}
    (first second : Fin qubits) (different : first ≠ second)
    (localOperator : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    OperatorPreservesOutside {first, second}
      (embedTwoQubitOperator first second different localOperator) := by
  intro output input nonzero wire outside
  rw [VerifiedCircuitCore.embedTwoQubitOperator_apply] at nonzero
  by_cases agrees : agreesExceptTwo first second output input
  · apply agrees wire
    · intro equal
      subst wire
      exact outside (by simp)
    · intro equal
      subst wire
      exact outside (by simp)
  · simp [agrees] at nonzero

end OperatorPreservesOutside

end

end VerifiedCircuitCore
