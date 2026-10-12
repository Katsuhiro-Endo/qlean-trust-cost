import QLean.History.Implementation.HistoryPipelineH2PostFacts
import QLean.History.Implementation.HistoryPipelineSelectorAction

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic
open ExecutableHistorySelectorAction

noncomputable section

/-- A predicate-controlled one-qubit operator has exactly the ordinary
one-qubit action on every input column on which its predicate is true. -/
theorem applyOperator_predicateControlledSingleQubitOperator_basisKet_of_true119
    {qubits : Nat}
    (predicate : QubitBasis qubits → Bool)
    (target : Fin qubits)
    (localOperator : Matrix Bool Bool ℂ)
    (input : QubitBasis qubits)
    (predicateTrue : predicate input = true) :
    applyOperator
        (predicateControlledSingleQubitOperator predicate target localOperator)
        (basisKet input) =
      applyOperator (embedSingleQubitOperator target localOperator)
        (basisKet input) := by
  funext output
  rw [applyOperator_basisKet, applyOperator_basisKet,
    predicateControlledSingleQubitOperator_apply,
    embedSingleQubitOperator_apply]
  simp only [predicateTrue, ↓reduceIte]

/-- A predicate-controlled one-qubit operator fixes every basis ket on which
its predicate is false.  This is the complementary column lemma needed to
remove all non-selected iterations from the Taylor coefficient loop. -/
theorem applyOperator_predicateControlledSingleQubitOperator_basisKet_column_false119
    {qubits : Nat}
    (predicate : QubitBasis qubits → Bool)
    (target : Fin qubits)
    (localOperator : Matrix Bool Bool ℂ)
    (input : QubitBasis qubits)
    (predicateFalse : predicate input = false) :
    applyOperator
        (predicateControlledSingleQubitOperator predicate target localOperator)
        (basisKet input) =
      basisKet input := by
  funext output
  rw [applyOperator_basisKet,
    predicateControlledSingleQubitOperator_apply]
  simp only [predicateFalse, Bool.false_eq_true, ↓reduceIte, basisKet]
  by_cases agrees : agreesExcept target output input
  · by_cases targetEqual : output target = input target
    · have equal : output = input := by
        funext wire
        by_cases isTarget : wire = target
        · simpa [isTarget] using targetEqual
        · exact agrees wire isTarget
      subst output
      simp [agreesExcept]
    · have different : output ≠ input := by
        intro equal
        exact targetEqual (congrFun equal target)
      simp [agrees, targetEqual, different]
  · have different : output ≠ input := by
      intro equal
      apply agrees
      subst output
      exact fun _ _ => rfl
    simp [agrees, different]

/-- Exact two-term action of a predicate-controlled `Ry` on a selected
zero target.  No predicate-stability premise is needed: the matrix definition
tests the input column before changing the target wire. -/
theorem applyOperator_predicateControlledRy_basisKet_of_true_false119
    {qubits : Nat}
    (predicate : QubitBasis qubits → Bool)
    (target : Fin qubits)
    (angle : Real)
    (input : QubitBasis qubits)
    (predicateTrue : predicate input = true)
    (targetFalse : input target = false) :
    applyOperator
        (predicateControlledSingleQubitOperator predicate target
          (localRy angle))
        (basisKet input) =
      ((Real.cos (angle / 2) : Real) : Complex) • basisKet input +
        ((Real.sin (angle / 2) : Real) : Complex) •
          basisKet (replaceQubitWire input target true) := by
  rw [applyOperator_predicateControlledSingleQubitOperator_basisKet_of_true119
    predicate target (localRy angle) input predicateTrue]
  exact applyOperator_embedRy_basisKet_false target angle input targetFalse

end
end ExecutableHistoryExecutableHistory
