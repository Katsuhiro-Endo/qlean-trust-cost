import QLean.History.Implementation.HistoryPipelineHistoryCleanInput

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistorySelectorAction

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

theorem replace_false_eq_of_true
    {qubits : Nat} (input output : QubitBasis qubits) (target : Fin qubits)
    (outputTrue : output target = true)
    (replaced : replaceQubitWire output target false = input) :
    output = replaceQubitWire input target true := by
  funext wire
  by_cases equal : wire = target
  · subst wire
    simp [outputTrue]
  · have atWire := congrFun replaced wire
    rw [replaceQubitWire_outside output target wire false equal] at atWire
    rw [replaceQubitWire_outside input target wire true equal]
    exact atWire

theorem replace_true_ne_of_input_false
    {qubits : Nat} (input output : QubitBasis qubits) (target : Fin qubits)
    (inputFalse : input target = false) :
    replaceQubitWire output target true ≠ input := by
  intro equal
  have atTarget := congrFun equal target
  simp [inputFalse] at atTarget

/-- Exact two-term action of an embedded Ry on a zero input wire. -/
theorem applyOperator_embedRy_basisKet_false
    {qubits : Nat} (target : Fin qubits) (angle : Real)
    (input : QubitBasis qubits) (inputFalse : input target = false) :
    applyOperator (embedSingleQubitOperator target (localRy angle))
        (basisKet input) =
      ((Real.cos (angle / 2) : Real) : Complex) • basisKet input +
        ((Real.sin (angle / 2) : Real) : Complex) •
          basisKet (replaceQubitWire input target true) := by
  funext output
  rw [applyOperator_embedSingleQubitOperator_state, Fintype.sum_bool]
  by_cases outputTrue : output target = true
  · have replaceTrueNe := replace_true_ne_of_input_false
      input output target inputFalse
    have outputEq :
        replaceQubitWire output target false = input ↔
          output = replaceQubitWire input target true := by
      constructor
      · exact replace_false_eq_of_true input output target outputTrue
      · intro equal
        subst output
        funext wire
        by_cases wireEq : wire = target
        · subst wire
          simp [inputFalse]
        · simp [replaceQubitWire_outside, wireEq]
    have outputNe : output ≠ input := by
      intro equal
      have atTarget := congrArg (fun basis : QubitBasis qubits => basis target) equal
      simp [outputTrue, inputFalse] at atTarget
    simp [localRy, basisKet, outputTrue, replaceTrueNe, outputEq,
      outputNe]
  · have outputFalse : output target = false :=
      Bool.eq_false_of_not_eq_true outputTrue
    have replaceFalse : replaceQubitWire output target false = output := by
      simpa [outputFalse] using replaceQubitWire_self output target
    have replaceTrueNe := replace_true_ne_of_input_false
      input output target inputFalse
    have flippedNe : output ≠ replaceQubitWire input target true := by
      intro equal
      have atTarget := congrArg (fun basis : QubitBasis qubits => basis target) equal
      simp [outputFalse] at atTarget
    simp [localRy, basisKet, outputFalse, replaceFalse, replaceTrueNe,
      flippedNe]

end
end ExecutableHistorySelectorAction
