import QLean.Circuits.Foundation.EqualityBranchLessThanAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.Circuits.Foundation.PhaseShiftMacros

/-!
# Exact phase on a finite Boolean basis program

This is the primitive compute--phase--uncompute building block needed to
realize a phase on the image of a finite logical basis embedding.  The phase
is an arbitrary real witness stored exactly in `AngleExpr.const`; no numerical
phase synthesis is involved.
-/

namespace VerifiedCircuitCore

noncomputable section

namespace NativeExactBasisPhase

open ClassicalReversibleStage

/-- Source-order primitive circuit: compute the Boolean program parity into a
clean flag, apply an arbitrary exact phase to the flag, then uncompute. -/
def booleanProgramPhaseCircuit {qubits : Nat}
    (program : List (List (Fin qubits × Bool)))
    (scratches : List (Fin qubits)) (flag : Fin qubits) (angle : ℝ) :
    Circuit (PrimitiveGate qubits) :=
  let compute := (boolControlledXProgram program scratches flag).compile
  compute.seq ((Circuit.gate (.phaseShift (.const angle) flag)).seq compute)

/-- The same finite Boolean phase compiler, retaining the caller's exact
angle syntax rather than first evaluating it to a real number. -/
def booleanProgramPhaseCircuitExpr {qubits : Nat}
    (program : List (List (Fin qubits × Bool)))
    (scratches : List (Fin qubits)) (flag : Fin qubits) (angle : AngleExpr) :
    Circuit (PrimitiveGate qubits) :=
  let compute := (boolControlledXProgram program scratches flag).compile
  compute.seq ((Circuit.gate (.phaseShift angle flag)).seq compute)

theorem booleanProgramPhaseCircuitExpr_denote {qubits : Nat}
    (symbolValue : String → ℝ)
    (program : List (List (Fin qubits × Bool)))
    (scratches : List (Fin qubits)) (flag : Fin qubits) (angle : AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (booleanProgramPhaseCircuitExpr program scratches flag angle) =
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (booleanProgramPhaseCircuit program scratches flag (angle.eval symbolValue)) := by
  rfl

/-- The compiled Boolean program stage has exactly its independent analytic
permutation semantics. -/
theorem boolControlledXProgram_compile_denote {qubits : Nat}
    (symbolValue : String → ℝ)
    (program : List (List (Fin qubits × Bool)))
    (scratches : List (Fin qubits)) (flag : Fin qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (boolControlledXProgram program scratches flag).compile =
      (boolControlledXProgram program scratches flag).analyticOperator := by
  let stage := boolControlledXProgram program scratches flag
  rw [← stage.primitiveExactOperatorComponent_circuit symbolValue]
  rw [(stage.primitiveExactOperatorComponent symbolValue).correct]
  exact stage.primitiveExactOperatorComponent_target symbolValue

/-- Exact clean-basis action.  The flag and all scratch wires are restored,
and the requested phase is applied iff the Boolean program has odd parity. -/
theorem booleanProgramPhaseCircuit_apply_basisKet {qubits : Nat}
    (symbolValue : String → ℝ)
    (program : List (List (Fin qubits × Bool)))
    (scratches : List (Fin qubits)) (flag : Fin qubits) (angle : ℝ)
    (input : QubitBasis qubits)
    (enoughScratch : ∀ controls ∈ program,
      controls.length ≤ scratches.length + 1)
    (layoutNodup : ∀ controls ∈ program,
      (controls.map Prod.fst ++ scratches ++ [flag]).Nodup)
    (flagOutsideScratch : flag ∉ scratches)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (flagZero : input flag = false) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (booleanProgramPhaseCircuit program scratches flag angle))
        (basisKet input) =
      (if boolControlProgramParity program input then
          Complex.exp (Complex.I * (angle : ℂ)) else 1) • basisKet input := by
  let stage := boolControlledXProgram program scratches flag
  let enabled := boolControlProgramParity program input
  have stageDenote :
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) stage.compile =
        stage.analyticOperator :=
    boolControlledXProgram_compile_denote symbolValue program scratches flag
  have firstAction :
      applyOperator stage.analyticOperator (basisKet input) =
        basisKet (xorWire flag enabled input) := by
    rw [analyticOperator_eq_deterministicReference,
      applyOperator_deterministicOperator_basisKet]
    exact congrArg basisKet
      (boolControlledXProgram_reference_apply_of_cleanWork program scratches
        flag input enoughScratch layoutNodup scratchZero)
  have scratchZeroAfter : ∀ wire ∈ scratches,
      xorWire flag enabled input wire = false := by
    intro wire member
    rw [xorWire_apply_other flag wire (by
      intro equal
      apply flagOutsideScratch
      simpa [equal] using member)]
    exact scratchZero wire member
  have flagOutsideRows : ∀ controls ∈ program,
      flag ∉ controls.map Prod.fst := by
    intro controls member flagMember
    have separated := (List.nodup_append.mp (layoutNodup controls member)).2.2
    exact separated flag (List.mem_append_left _ flagMember)
      flag (by simp) rfl
  have parityAfter :
      boolControlProgramParity program (xorWire flag enabled input) = enabled := by
    exact boolControlProgramParity_xorWire_outside program flag enabled input
      flagOutsideRows
  have secondAction :
      applyOperator stage.analyticOperator
          (basisKet (xorWire flag enabled input)) = basisKet input := by
    rw [analyticOperator_eq_deterministicReference,
      applyOperator_deterministicOperator_basisKet]
    rw [boolControlledXProgram_reference_apply_of_cleanWork program scratches
      flag (xorWire flag enabled input) enoughScratch layoutNodup scratchZeroAfter]
    rw [parityAfter]
    exact congrArg basisKet (xorWire_involutive flag enabled input)
  simp only [booleanProgramPhaseCircuit, Circuit.denote_seq,
    Circuit.denote, applyOperator_mul]
  rw [stageDenote, firstAction]
  change applyOperator stage.analyticOperator
      (applyOperator (phaseShiftOneWireOperator angle flag)
        (basisKet (xorWire flag enabled input))) = _
  rw [phaseShiftOneWireOperator_apply_basisKet]
  rw [applyOperator_smul, secondAction]
  simp [xorWire_apply_same, flagZero, enabled]

end NativeExactBasisPhase

end

end VerifiedCircuitCore
