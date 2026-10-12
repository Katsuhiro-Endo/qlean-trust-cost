import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.QuantumFourierAnalytic
import QLean.Circuits.Foundation.PhaseShiftMacros

/-! Local one- and two-qubit operator embedding identities. -/

namespace VerifiedCircuitCore

noncomputable section

/-- 同じ二 wire への局所作用素埋込みは作用素積を保存する。 -/
theorem embedTwoQubitOperator_mul {qubits : Nat}
    (first second : Fin qubits) (different : first ≠ second)
    (left right : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    embedTwoQubitOperator first second different (left * right) =
      embedTwoQubitOperator first second different left *
        embedTwoQubitOperator first second different right := by
  unfold embedTwoQubitOperator
  exact reindexKroneckerOne_mul
    (splitTwoWiresEquiv first second different) left right

/-- 二 wire 局所作用素で target 側だけへ作用することは一 wire 埋込みと一致する。 -/
theorem embedTwoQubitOperator_localOnTarget {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ) :
    embedTwoQubitOperator control target different (localOnTarget localOperator) =
      embedSingleQubitOperator target localOperator := by
  ext output input
  rw [embedTwoQubitOperator_apply, embedSingleQubitOperator_apply]
  by_cases outsideTwo : agreesExceptTwo control target output input
  · by_cases controlEqual : output control = input control
    · have outsideOne : agreesExcept target output input := by
        intro wire wireTargetDifferent
        by_cases wireControl : wire = control
        · simpa [wireControl] using controlEqual
        · exact outsideTwo wire wireControl wireTargetDifferent
      simp [outsideTwo, outsideOne, localOnTarget, controlEqual]
    · have outsideOne : ¬ agreesExcept target output input := by
        intro outsideOne
        exact controlEqual (outsideOne control different)
      simp [outsideTwo, outsideOne, localOnTarget, controlEqual]
  · have outsideOne : ¬ agreesExcept target output input := by
      intro outsideOne
      apply outsideTwo
      intro wire wireControlDifferent wireTargetDifferent
      exact outsideOne wire wireTargetDifferent
    simp [outsideTwo, outsideOne]

/-- 二 wire 局所作用素で control 側だけへ作用することは一 wire埋込みと一致する。 -/
theorem embedTwoQubitOperator_localOnControl {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ) :
    embedTwoQubitOperator control target different (localOnControl localOperator) =
      embedSingleQubitOperator control localOperator := by
  ext output input
  rw [embedTwoQubitOperator_apply, embedSingleQubitOperator_apply]
  by_cases outsideTwo : agreesExceptTwo control target output input
  · by_cases targetEqual : output target = input target
    · have outsideOne : agreesExcept control output input := by
        intro wire wireControlDifferent
        by_cases wireTarget : wire = target
        · simpa [wireTarget] using targetEqual
        · exact outsideTwo wire wireControlDifferent wireTarget
      simp [outsideTwo, outsideOne, localOnControl, targetEqual]
    · have outsideOne : ¬ agreesExcept control output input := by
        intro outsideOne
        exact targetEqual (outsideOne target (Ne.symm different))
      simp [outsideTwo, outsideOne, localOnControl, targetEqual]
  · have outsideOne : ¬ agreesExcept control output input := by
      intro outsideOne
      apply outsideTwo
      intro wire wireControlDifferent wireTargetDifferent
      exact outsideOne wire wireControlDifferent
    simp [outsideTwo, outsideOne]

/-- CNOT の基底作用仕様は二 wire 局所 CNOT の埋込みと一致する。 -/
theorem analyticCnotOperator_eq_embedTwo_localCnot {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target) :
    analyticCnotOperator control target =
      embedTwoQubitOperator control target different localCnotOperator := by
  ext output input
  rw [embedTwoQubitOperator_apply]
  simp only [analyticCnotOperator, deterministicOperator_apply]
  by_cases outside : agreesExceptTwo control target output input
  · have actionIff :
        output = xorWire target (input control) input ↔
          (output control, output target) =
            (input control, input target != input control) := by
      constructor
      · intro equal
        subst output
        simp [xorWire, different]
      · intro localEqual
        funext wire
        by_cases wireControl : wire = control
        · subst wire
          simpa [xorWire, different] using congrArg Prod.fst localEqual
        · by_cases wireTarget : wire = target
          · subst wire
            simpa [xorWire] using congrArg Prod.snd localEqual
          · simpa [xorWire, wireTarget] using
              outside wire wireControl wireTarget
    simp [outside, localCnotOperator, actionIff]
  · have actionDifferent : output ≠ xorWire target (input control) input := by
      intro equal
      apply outside
      intro wire wireControlDifferent wireTargetDifferent
      rw [equal]
      simp [xorWire, wireTargetDifferent]
    simp [outside, actionDifferent]

end

end VerifiedCircuitCore
