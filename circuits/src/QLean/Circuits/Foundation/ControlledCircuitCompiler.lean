import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.Circuits.Foundation.ControlledHadamard
import QLean.Circuits.Foundation.ControlledCircuitCompilerAnalytic
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.OperatorLocality
import QLean.Circuits.Foundation.WireEmbedding

/-!
# Leaf-wise externally controlled circuit compiler

This module records the source-faithful compiler shape used to add one external
control to a placed primitive circuit.  Unsupported primitive constructors are
totalized to the identity, while public component constructors require a proof
that every source leaf actually occurring in the input AST belongs to the
supported X/Z/CNOT/Toffoli/H/Ry/Rz family.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Primitive source leaves accepted by the legacy compatibility boundary.

The executable primitive language is already normalized.  PhaseShift is handled
by the V2 facade below; the analytic plan deliberately retains the external Z/Rz
source vocabulary without reintroducing those constructors into `PrimitiveGate`.
-/
def IsExternallyControllablePrimitive {qubits : Nat} :
    PrimitiveGate qubits → Prop
  | .x _ | .h _ | .ry _ _ | .phaseShift _ _ | .cnot _ _ _ |
      .toffoli _ _ _ _ _ _ => True

/-- Source-order normalized expansion of an analytic plan leaf.  The Rz source
word is lowered through the typed PhaseShift macro; no legacy primitive node is
constructed. -/
def ExternallyControlledPrimitivePlan.sourceNormalizedCircuit {qubits : Nat} :
    ExternallyControlledPrimitivePlan qubits → Circuit (PrimitiveGate qubits)
  | .x target => .gate (.x target)
  | .z target => .gate (.phaseShift .pi target)
  | .h target => .gate (.h target)
  | .ry angle target => .gate (.ry angle target)
  | .phaseShift angle target => .gate (.phaseShift angle target)
  | .rz angle target => phaseShiftRzCircuit {
      angle := angle
      target := target }
  | .cnot control target different =>
      .gate (.cnot control target different)
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      .gate (.toffoli control₀ control₁ target controlsDifferent firstDifferent
        secondDifferent)

private theorem sourceNormalizedCircuit_z_correct {qubits : Nat}
    (symbolValue : String → ℝ) (target : Fin qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (ExternallyControlledPrimitivePlan.sourceNormalizedCircuit (.z target)) =
      embedSingleQubitOperator target localZ := by
  rw [ExternallyControlledPrimitivePlan.sourceNormalizedCircuit]
  change embedSingleQubitOperator target
      (localPhaseShift Real.pi) =
    embedSingleQubitOperator target localZ
  have expPi : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  have localEqual : localPhaseShift Real.pi = localZ := by
    ext output input
    cases output <;> cases input <;>
      simp [localPhaseShift, localPhase, localZ, expPi]
  rw [localEqual]

theorem ExternallyControlledPrimitivePlan.sourceNormalizedCircuit_correct
    {qubits : Nat} (symbolValue : String → ℝ)
    (plan : ExternallyControlledPrimitivePlan qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        plan.sourceNormalizedCircuit = plan.sourceOperator symbolValue := by
  cases plan with
  | x target => rfl
  | z target =>
      exact sourceNormalizedCircuit_z_correct symbolValue target
  | h target => rfl
  | ry angle target => rfl
  | phaseShift angle target => rfl
  | rz angle target =>
      simpa [ExternallyControlledPrimitivePlan.sourceNormalizedCircuit,
        ExternallyControlledPrimitivePlan.sourceOperator,
        phaseShiftRzOperator] using
        (phaseShiftRzCircuit_denote_eq symbolValue {
          angle := angle
          target := target })
  | cnot control target different => rfl
  | toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent => rfl

/-- The typed source decoder for the normalized core language. -/
def ExternallyControlledPrimitivePlan.ofPrimitive? {qubits : Nat} :
    PrimitiveGate qubits → Option (ExternallyControlledPrimitivePlan qubits)
  | .x target => some (.x target)
  | .h target => some (.h target)
  | .ry angle target => some (.ry angle target)
  | .phaseShift angle target => some (.phaseShift angle target)
  | .cnot control target different => some (.cnot control target different)
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      some (.toffoli control₀ control₁ target controlsDifferent firstDifferent
        secondDifferent)

def ExternallyControlledPrimitivePlan.ofPrimitive {qubits : Nat}
    (gate : PrimitiveGate qubits)
    (supported : IsExternallyControllablePrimitive gate) :
    ExternallyControlledPrimitivePlan qubits := by
  cases gate with
  | x target => exact .x target
  | h target => exact .h target
  | ry angle target => exact .ry angle target
  | phaseShift angle target => exact .phaseShift angle target
  | cnot control target different => exact .cnot control target different
  | toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      exact .toffoli control₀ control₁ target controlsDifferent firstDifferent
        secondDifferent

@[simp] theorem ExternallyControlledPrimitivePlan.ofPrimitive?_ofPrimitive
    {qubits : Nat} (gate : PrimitiveGate qubits)
    (supported : IsExternallyControllablePrimitive gate) :
    ExternallyControlledPrimitivePlan.ofPrimitive? gate =
      some (ExternallyControlledPrimitivePlan.ofPrimitive gate supported) := by
  cases gate <;>
    simp [ExternallyControlledPrimitivePlan.ofPrimitive?,
      ExternallyControlledPrimitivePlan.ofPrimitive,
      IsExternallyControllablePrimitive] at supported ⊢

/-- Decode a supported primitive list without changing source order. -/
def decodeSupportedPrimitiveStream {qubits : Nat} :
    (gates : List (PrimitiveGate qubits)) →
    (∀ gate, gate ∈ gates → IsExternallyControllablePrimitive gate) →
    List (ExternallyControlledPrimitivePlan qubits)
  | [], _ => []
  | first :: rest, supported =>
      ExternallyControlledPrimitivePlan.ofPrimitive first
          (supported first (by simp)) ::
        decodeSupportedPrimitiveStream rest (fun gate member =>
          supported gate (by simp [member]))

def decodeSupportedPrimitiveCircuit {qubits : Nat}
    (circuit : Circuit (PrimitiveGate qubits))
    (supported : ∀ gate, gate ∈ circuit.flatten →
      IsExternallyControllablePrimitive gate) :
    List (ExternallyControlledPrimitivePlan qubits) :=
  decodeSupportedPrimitiveStream circuit.flatten supported

theorem decodeSupportedPrimitiveStream_sourceNormalized_flatten
    {qubits : Nat} (gates : List (PrimitiveGate qubits))
    (supported : ∀ gate, gate ∈ gates →
      IsExternallyControllablePrimitive gate) :
    (Circuit.sequence
      ((decodeSupportedPrimitiveStream gates supported).map
        ExternallyControlledPrimitivePlan.sourceNormalizedCircuit)).flatten =
      gates := by
  rw [Circuit.flatten_sequence]
  induction gates with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      have firstSupported := supported first (by simp)
      have restSupported : ∀ gate, gate ∈ rest →
          IsExternallyControllablePrimitive gate := by
        intro gate member
        exact supported gate (by simp [member])
      simp only [decodeSupportedPrimitiveStream, List.map_cons,
        List.flatMap_cons]
      cases first <;>
        simp [ExternallyControlledPrimitivePlan.ofPrimitive,
          ExternallyControlledPrimitivePlan.sourceNormalizedCircuit,
          IsExternallyControllablePrimitive, Circuit.flatten] at firstSupported ⊢ <;>
        exact inductionHypothesis restSupported

theorem decodeSupportedPrimitiveCircuit_sourceNormalized_flatten
    {qubits : Nat} (circuit : Circuit (PrimitiveGate qubits))
    (supported : ∀ gate, gate ∈ circuit.flatten →
      IsExternallyControllablePrimitive gate) :
    (Circuit.sequence
      ((decodeSupportedPrimitiveCircuit circuit supported).map
        ExternallyControlledPrimitivePlan.sourceNormalizedCircuit)).flatten =
      circuit.flatten :=
  decodeSupportedPrimitiveStream_sourceNormalized_flatten
    circuit.flatten supported

/-!
## Normalized controlled facade

The public V2 compiler is the only typed normalized control entry point.  The
compatibility definitions below are retained for source-order contracts, but
every productive branch emits only the six normalized constructors.
-/

private def externallyControlledPhaseShiftFiveGateCircuit
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (angle : AngleExpr) (target : Fin sourceQubits) :
    Circuit (PrimitiveGate targetQubits) :=
  Circuit.fromList [
    .phaseShift (ControlledCircuitCompilerV2.phaseShiftHalfAngle angle) layout.control,
    .phaseShift (ControlledCircuitCompilerV2.phaseShiftHalfAngle angle) (layout.placement target),
    .cnot layout.control (layout.placement target)
      (layout.control_ne_placed target),
    .phaseShift (.neg (ControlledCircuitCompilerV2.phaseShiftHalfAngle angle))
      (layout.placement target),
    .cnot layout.control (layout.placement target)
      (layout.control_ne_placed target)]

def compileExternallyControlledPrimitive
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    PrimitiveGate sourceQubits → Circuit (PrimitiveGate targetQubits)
  | .x target =>
      .gate (.cnot layout.control (layout.placement target)
        (layout.control_ne_placed target))
  | .h target =>
      controlledHadamardSpecialAngleCircuit {
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }
  | .ry angle target =>
      controlledRyMacroCircuit {
        angle := angle
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }
  | .phaseShift angle target =>
      externallyControlledPhaseShiftFiveGateCircuit layout angle target
  | .cnot sourceControl target different =>
      .gate (.toffoli layout.control (layout.placement sourceControl)
        (layout.placement target)
        (layout.control_ne_placed sourceControl)
        (layout.control_ne_placed target)
        (fun equal => different (layout.placement.injective equal)))
  | .toffoli control₀ control₁ target _ _ _ =>
      (ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement control₀, layout.placement control₁]
        layout.controlWork (layout.placement target)).compile

def externallyControlledPhaseShiftTarget
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (angle : AngleExpr) (target : Fin sourceQubits) :
    Operator (QubitBasis targetQubits) :=
  analyticControlledPhaseOperator layout.control
    (layout.placement target) (layout.control_ne_placed target)
    (angle.eval symbolValue)

theorem externallyControlledPhaseShiftFiveGateCircuit_correct
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (angle : AngleExpr) (target : Fin sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (externallyControlledPhaseShiftFiveGateCircuit layout angle target) =
      externallyControlledPhaseShiftTarget symbolValue layout angle target := by
  simp only [externallyControlledPhaseShiftFiveGateCircuit, Circuit.fromList,
    Circuit.denote, primitiveGateOperatorWithSymbols, AngleExpr.eval_neg,
    ControlledCircuitCompilerV2.phaseShiftHalfAngle_eval, Matrix.one_mul]
  rw [show deterministicOperator
      (fun input => xorWire (layout.placement target)
        (input layout.control) input) =
        analyticCnotOperator layout.control (layout.placement target) by rfl]
  rw [analyticCnotOperator_eq_embedTwo_localCnot
    layout.control (layout.placement target)
      (layout.control_ne_placed target)]
  rw [← embedTwoQubitOperator_localOnTarget layout.control
      (layout.placement target) (layout.control_ne_placed target),
    ← embedTwoQubitOperator_localOnTarget layout.control
      (layout.placement target) (layout.control_ne_placed target),
    ← embedTwoQubitOperator_localOnControl layout.control
      (layout.placement target) (layout.control_ne_placed target)]
  rw [← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul,
    ← embedTwoQubitOperator_mul, ← embedTwoQubitOperator_mul]
  unfold externallyControlledPhaseShiftTarget analyticControlledPhaseOperator
  rw [ControlledCircuitCompilerV2.local_controlledPhaseShift_decomposition]

theorem analyticControlledPhaseOperator_eq_embedControlledPhaseShift
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (angle : ℝ) :
    analyticControlledPhaseOperator control target different angle =
      embedControlledSingleQubitOperator control target different
        (localPhaseShift angle) := by
  unfold analyticControlledPhaseOperator embedControlledSingleQubitOperator
  congr 1
  ext output input
  rcases output with ⟨outputControl, outputTarget⟩
  rcases input with ⟨inputControl, inputTarget⟩
  cases outputControl <;> cases outputTarget <;>
    cases inputControl <;> cases inputTarget <;>
    simp [localControlledOperator, localControlledPhaseOperator,
      localPhaseShift, localPhase]

def ExternallyControlledPrimitivePlan.compile
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    ExternallyControlledPrimitivePlan sourceQubits →
      Circuit (PrimitiveGate targetQubits)
  | .x target =>
      .gate (.cnot layout.control (layout.placement target)
        (layout.control_ne_placed target))
  | .z target =>
      Circuit.fromList [
        .h (layout.placement target),
        .cnot layout.control (layout.placement target)
          (layout.control_ne_placed target),
        .h (layout.placement target)]
  | .h target =>
      controlledHadamardSpecialAngleCircuit {
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }
  | .ry angle target =>
      controlledRyMacroCircuit {
        angle := angle
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }
  | .phaseShift angle target =>
      externallyControlledPhaseShiftFiveGateCircuit layout angle target
  | .rz angle target =>
      controlledRzMacroCircuit {
        angle := angle
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }
  | .cnot sourceControl target different =>
      .gate (.toffoli layout.control (layout.placement sourceControl)
        (layout.placement target)
        (layout.control_ne_placed sourceControl)
        (layout.control_ne_placed target)
        (fun equal => different (layout.placement.injective equal)))
  | .toffoli control₀ control₁ target _ _ _ =>
      (ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement control₀, layout.placement control₁]
        layout.controlWork (layout.placement target)).compile

theorem ExternallyControlledPrimitivePlan.compile_ofPrimitive
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (gate : PrimitiveGate sourceQubits)
    (supported : IsExternallyControllablePrimitive gate) :
    (ExternallyControlledPrimitivePlan.ofPrimitive gate supported).compile
        layout = compileExternallyControlledPrimitive layout gate := by
  cases gate <;>
    simp [ExternallyControlledPrimitivePlan.ofPrimitive,
      ExternallyControlledPrimitivePlan.compile,
      compileExternallyControlledPrimitive,
      IsExternallyControllablePrimitive] at supported ⊢

/-- The H-CNOT-H expansion of an externally controlled Z is its direct
controlled-Z semantic operator. -/
theorem externallyControlledZThreeGateOperator_eq_semantic
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (target : Fin sourceQubits) :
    operatorSequence [
        embedSingleQubitOperator (layout.placement target) localH,
        reversibleAnalyticCnotOperator layout.control (layout.placement target),
        embedSingleQubitOperator (layout.placement target) localH] =
      embedControlledSingleQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target) localZ := by
  rw [show reversibleAnalyticCnotOperator layout.control
      (layout.placement target) =
        analyticCnotOperator layout.control (layout.placement target) by rfl]
  rw [analyticCnotOperator_eq_embedTwo_localCnot layout.control
    (layout.placement target) (layout.control_ne_placed target)]
  rw [← embedTwoQubitOperator_localOnTarget layout.control
      (layout.placement target) (layout.control_ne_placed target) localH]
  change operatorSequence
      (([localOnTarget localH, localCnotOperator, localOnTarget localH] :
        List (Matrix (Bool × Bool) (Bool × Bool) ℂ)).map
          (embedTwoQubitOperator layout.control (layout.placement target)
            (layout.control_ne_placed target))) =
    embedTwoQubitOperator layout.control (layout.placement target)
      (layout.control_ne_placed target) (localControlledOperator localZ)
  rw [embedTwoQubitOperator_operatorSequence]
  apply congrArg
    (embedTwoQubitOperator layout.control (layout.placement target)
      (layout.control_ne_placed target))
  simpa [operatorSequence, mul_assoc] using local_h_cnot_h_eq_controlledZ

/-- Controlling a wire-lifted one-qubit source operator is exactly the usual
two-wire controlled embedding at the placed target. -/
theorem externallyControlledWireLiftOperator_embedSingleQubitOperator
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (target : Fin sourceQubits) (localOperator : Matrix Bool Bool ℂ) :
    externallyControlledWireLiftOperator layout
        (embedSingleQubitOperator target localOperator) =
      embedControlledSingleQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        localOperator := by
  classical
  have liftEq :
      wireLiftOperator layout.placement
          (embedSingleQubitOperator target localOperator) =
        embedSingleQubitOperator (layout.placement target) localOperator := by
    ext output input
    rw [wireLiftOperator_apply, embedSingleQubitOperator_apply,
      embedSingleQubitOperator_apply]
    have agreesIff :
        agreesExcept (layout.placement target) output input ↔
          agreesExcept target
              (restrictToPlacedWires layout.placement output)
              (restrictToPlacedWires layout.placement input) ∧
            restrictToOutsideWires layout.placement output =
              restrictToOutsideWires layout.placement input := by
      constructor
      · intro agrees
        constructor
        · intro wire different
          exact agrees (layout.placement wire) (fun equal =>
            different (layout.placement.injective equal))
        · funext wire
          exact agrees wire.1 (fun equal => wire.2 target equal.symm)
      · rintro ⟨internalAgrees, outsideAgrees⟩ wire different
        by_cases inside : ∃ source, layout.placement source = wire
        · let source := Classical.choose inside
          have sourceAt : layout.placement source = wire :=
            Classical.choose_spec inside
          have sourceDifferent : source ≠ target := by
            intro equal
            apply different
            exact sourceAt.symm.trans (congrArg layout.placement equal)
          simpa [restrictToPlacedWires, sourceAt] using
            internalAgrees source sourceDifferent
        · let outside : OutsideWire layout.placement :=
            ⟨wire, fun source equal => inside ⟨source, equal⟩⟩
          exact congrFun outsideAgrees outside
    by_cases internalAgrees : agreesExcept target
        (restrictToPlacedWires layout.placement output)
        (restrictToPlacedWires layout.placement input)
    · by_cases outsideAgrees :
          restrictToOutsideWires layout.placement output =
            restrictToOutsideWires layout.placement input
      · have mappedAgrees := agreesIff.2 ⟨internalAgrees, outsideAgrees⟩
        simp [internalAgrees, outsideAgrees, mappedAgrees,
          restrictToPlacedWires]
      · have mappedDifferent :
            ¬ agreesExcept (layout.placement target) output input := by
          intro mappedAgrees
          exact outsideAgrees (agreesIff.1 mappedAgrees).2
        simp [internalAgrees, outsideAgrees, mappedDifferent]
    · have mappedDifferent :
          ¬ agreesExcept (layout.placement target) output input := by
        intro mappedAgrees
        exact internalAgrees (agreesIff.1 mappedAgrees).1
      simp [internalAgrees, mappedDifferent]
  ext output input
  rw [externallyControlledWireLiftOperator_apply, liftEq,
    embedControlledSingleQubitOperator_apply_sparse,
    embedSingleQubitOperator_apply]
  by_cases control : input layout.control
  · simp [control]
  · by_cases outside : agreesExcept (layout.placement target) output input
    · by_cases targetEqual :
          output (layout.placement target) = input (layout.placement target)
      · have equal : output = input :=
          (eq_iff_agreesExcept_and_target_eq
            (layout.placement target) output input).2
            ⟨outside, targetEqual⟩
        subst output
        simp [control, agreesExcept]
      · have different : output ≠ input := by
          intro equal
          exact targetEqual (congrFun equal (layout.placement target))
        simp [control, outside, targetEqual, different]
    · have different : output ≠ input := by
        intro equal
        subst output
        exact outside (by simp [agreesExcept])
      simp [control, outside, different]

private theorem xorWire_false_eq {qubits : Nat}
    (target : Fin qubits) (input : QubitBasis qubits) :
    xorWire target false input = input := by
  cases value : input target <;>
    funext wire <;>
    by_cases equal : wire = target <;>
    simp [xorWire, value, equal]

/-- One semantic compiler leaf is the abstract external positive-control lift
of its independent source-register operator. -/
/-
theorem ExternallyControlledPrimitivePlan.semanticOperator_eq_controlledWireLift
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : ExternallyControlledPrimitivePlan sourceQubits) :
    plan.semanticOperator symbolValue layout =
      externallyControlledWireLiftOperator layout
        (plan.sourceOperator symbolValue) := by
  cases plan with
  | x target =>
      have sourceX : embedSingleQubitOperator target localX =
          deterministicOperator (xorWire target true) := by
        simpa [primitiveGateOperatorWithSymbols] using
          primitiveXOperator_eq_deterministicOperator symbolValue target
      rw [ExternallyControlledPrimitivePlan.semanticOperator,
        ExternallyControlledPrimitivePlan.sourceOperator, sourceX,
        externallyControlledWireLiftOperator_deterministic]
      apply congrArg deterministicOperator
      funext input
      rw [liftBasisAction_xorWire]
      generalize input layout.control = controlValue
      cases controlValue <;>
        simp [xorWire_false_eq, restrictToPlacedWires]
  | z target =>
      exact (externallyControlledWireLiftOperator_embedSingleQubitOperator
        layout target localZ).symm
  | h target =>
      exact (externallyControlledWireLiftOperator_embedSingleQubitOperator
        layout target localH).symm
  | ry angle target =>
      exact (externallyControlledWireLiftOperator_embedSingleQubitOperator
        layout target (localRy (angle.eval symbolValue))).symm
  | phaseShift angle target =>
      rw [ExternallyControlledPrimitivePlan.semanticOperator,
        ExternallyControlledPrimitivePlan.sourceOperator,
        analyticControlledPhaseOperator_eq_embedControlledPhaseShift]
      exact (externallyControlledWireLiftOperator_embedSingleQubitOperator
        layout target (localPhaseShift (angle.eval symbolValue))).symm
  | rz angle target =>
      exact (externallyControlledWireLiftOperator_embedSingleQubitOperator
        layout target (localRz (angle.eval symbolValue))).symm
  | cnot control target different =>
      rw [ExternallyControlledPrimitivePlan.semanticOperator,
        ExternallyControlledPrimitivePlan.sourceOperator,
        reversibleAnalyticCnotOperator,
        externallyControlledWireLiftOperator_deterministic]
      apply congrArg deterministicOperator
      funext input
      rw [liftBasisAction_xorWire]
      change ExternallyControlledPrimitivePlan.tripleControlledXBasisAction
          layout.control (layout.placement control竄)
            (layout.placement control竄・ (layout.placement target) input =
        xorWire (layout.placement target)
          (input layout.control &&
            (restrictToPlacedWires layout.placement input control竄 &&
              restrictToPlacedWires layout.placement input control竄・) input
      rfl
  | toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      rw [ExternallyControlledPrimitivePlan.semanticOperator,
        ExternallyControlledPrimitivePlan.sourceOperator,
        analyticToffoliOperator,
        externallyControlledWireLiftOperator_deterministic]
      apply congrArg deterministicOperator
      funext input
      rw [liftBasisAction_xorWire]
      cases controlValue : input layout.control <;>
        simp [controlValue, xorWire]

-/

theorem ExternallyControlledPrimitivePlan.semanticOperator_eq_controlledWireLift
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : ExternallyControlledPrimitivePlan sourceQubits) :
    plan.semanticOperator symbolValue layout =
      externallyControlledWireLiftOperator layout
        (plan.sourceOperator symbolValue) := by
  cases plan with
  | x target =>
      have sourceX : embedSingleQubitOperator target localX =
          deterministicOperator (xorWire target true) := by
        simpa [primitiveGateOperatorWithSymbols] using
          primitiveXOperator_eq_deterministicOperator symbolValue target
      rw [ExternallyControlledPrimitivePlan.semanticOperator,
        ExternallyControlledPrimitivePlan.sourceOperator, sourceX,
        externallyControlledWireLiftOperator_deterministic]
      apply congrArg deterministicOperator
      funext input
      rw [liftBasisAction_xorWire]
      cases controlValue : input layout.control <;>
        simp [xorWire_false_eq]
  | z target =>
      exact (externallyControlledWireLiftOperator_embedSingleQubitOperator
        layout target localZ).symm
  | h target =>
      exact (externallyControlledWireLiftOperator_embedSingleQubitOperator
        layout target localH).symm
  | ry angle target =>
      exact (externallyControlledWireLiftOperator_embedSingleQubitOperator
        layout target (localRy (angle.eval symbolValue))).symm
  | phaseShift angle target =>
      rw [ExternallyControlledPrimitivePlan.semanticOperator,
        ExternallyControlledPrimitivePlan.sourceOperator,
        analyticControlledPhaseOperator_eq_embedControlledPhaseShift]
      exact (externallyControlledWireLiftOperator_embedSingleQubitOperator
        layout target (localPhaseShift (angle.eval symbolValue))).symm
  | rz angle target =>
      exact (externallyControlledWireLiftOperator_embedSingleQubitOperator
        layout target (localRz (angle.eval symbolValue))).symm
  | cnot control target different =>
      rw [ExternallyControlledPrimitivePlan.semanticOperator,
        ExternallyControlledPrimitivePlan.sourceOperator,
        reversibleAnalyticCnotOperator,
        externallyControlledWireLiftOperator_deterministic]
      apply congrArg deterministicOperator
      funext input
      rw [liftBasisAction_xorWire]
      generalize input layout.control = controlValue
      cases controlValue <;>
        simp [xorWire_false_eq, restrictToPlacedWires]
  | toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      rw [ExternallyControlledPrimitivePlan.semanticOperator,
        ExternallyControlledPrimitivePlan.sourceOperator,
        analyticToffoliOperator,
        externallyControlledWireLiftOperator_deterministic]
      apply congrArg deterministicOperator
      funext input
      rw [liftBasisAction_xorWire]
      unfold ExternallyControlledPrimitivePlan.tripleControlledXBasisAction
      generalize input layout.control = controlValue
      cases controlValue <;>
        simp [xorWire_false_eq, restrictToPlacedWires]

/-- The complete semantic controlled plan is the abstract controlled lift of
the complete source plan, not merely a leaf-wise approximation. -/
theorem ExternallyControlledPrimitivePlan.semanticPlanOperator_eq_controlledWireLift
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    ∀ plan : List (ExternallyControlledPrimitivePlan sourceQubits),
      ExternallyControlledPrimitivePlan.semanticPlanOperator
          symbolValue layout plan =
        externallyControlledWireLiftOperator layout
          (ExternallyControlledPrimitivePlan.sourcePlanOperator
            symbolValue plan)
  | [] => by
      simp [ExternallyControlledPrimitivePlan.semanticPlanOperator,
        ExternallyControlledPrimitivePlan.sourcePlanOperator,
        operatorSequence]
  | first :: rest => by
      rw [show ExternallyControlledPrimitivePlan.semanticPlanOperator
          symbolValue layout (first :: rest) =
        ExternallyControlledPrimitivePlan.semanticPlanOperator
            symbolValue layout rest *
          first.semanticOperator symbolValue layout by
        rfl]
      rw [ExternallyControlledPrimitivePlan.semanticPlanOperator_eq_controlledWireLift
        symbolValue layout rest,
        first.semanticOperator_eq_controlledWireLift symbolValue layout,
        ← externallyControlledWireLiftOperator_mul]
      rfl

/-- Updating a placed target wire preserves the two clean work bits. -/
theorem externallyControlledCleanWorkPredicate_xorPlaced
    {sourceQubits targetQubits : Nat}
    {layout : ExternallyControlledCircuitLayout sourceQubits targetQubits}
    (valid : layout.CleanWorkValid) (target : Fin sourceQubits)
    (flag : Bool) (input : QubitBasis targetQubits)
    (clean : externallyControlledCleanWorkPredicate valid input) :
    externallyControlledCleanWorkPredicate valid
      (xorWire (layout.placement target) flag input) := by
  rcases clean with ⟨work₀Zero, work₁Zero⟩
  constructor
  · simp [xorWire, valid.work₀_ne_placed target, work₀Zero]
  · simp [xorWire, valid.work₁_ne_placed target, work₁Zero]

/-- A controlled one-wire operator on a placed target maps a clean work basis
ket into the coherent clean-work span. -/
theorem embedControlledSingleQubitOperator_maps_cleanBasis
    {sourceQubits targetQubits : Nat}
    {layout : ExternallyControlledCircuitLayout sourceQubits targetQubits}
    (valid : layout.CleanWorkValid) (target : Fin sourceQubits)
    (localOperator : Matrix Bool Bool ℂ)
    (input : QubitBasis targetQubits)
    (clean : externallyControlledCleanWorkPredicate valid input) :
    applyOperator
        (embedControlledSingleQubitOperator layout.control
          (layout.placement target) (layout.control_ne_placed target)
          localOperator)
        (basisKet input) ∈
      SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate valid) := by
  apply SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_entry_support
  intro output outside
  rw [embedControlledSingleQubitOperator_apply_sparse]
  by_cases agreement : agreesExcept (layout.placement target) output input
  · have outputClean : externallyControlledCleanWorkPredicate valid output := by
      constructor
      · exact (agreement valid.work₀ (valid.work₀_ne_placed target)).trans clean.1
      · exact (agreement valid.work₁ (valid.work₁_ne_placed target)).trans clean.2
    exact (outside outputClean).elim
  · simp [agreement]

/-- A deterministic XOR of a placed target maps a clean work basis ket to a
clean work basis ket. -/
theorem deterministicXorPlaced_maps_cleanBasis
    {sourceQubits targetQubits : Nat}
    {layout : ExternallyControlledCircuitLayout sourceQubits targetQubits}
    (valid : layout.CleanWorkValid) (target : Fin sourceQubits)
    (flag : QubitBasis targetQubits → Bool) (input : QubitBasis targetQubits)
    (clean : externallyControlledCleanWorkPredicate valid input) :
    applyOperator
        (deterministicOperator
          (fun basis => xorWire (layout.placement target) (flag basis) basis))
        (basisKet input) ∈
      SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate valid) := by
  rw [applyOperator_deterministicOperator_basisKet]
  apply SubspaceMapComponent.basisKet_mem_basisSpan
  exact externallyControlledCleanWorkPredicate_xorPlaced valid target
    (flag input) input clean

/-- On the clean-work basis block, each full-dirty compiler target agrees with
the direct work-preserving semantic target. -/
theorem ExternallyControlledPrimitivePlan.strictOperator_apply_eq_semanticOperator_of_clean
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (plan : ExternallyControlledPrimitivePlan sourceQubits)
    (input : QubitBasis targetQubits)
    (clean : externallyControlledCleanWorkPredicate valid input) :
    applyOperator (plan.strictOperator symbolValue layout) (basisKet input) =
      applyOperator (plan.semanticOperator symbolValue layout) (basisKet input) := by
  cases plan with
  | x target => rfl
  | z target =>
      rw [ExternallyControlledPrimitivePlan.strictOperator,
        ExternallyControlledPrimitivePlan.semanticOperator,
        externallyControlledZThreeGateOperator_eq_semantic layout target]
  | h target => rfl
  | ry angle target => rfl
  | phaseShift angle target => rfl
  | rz angle target => rfl
  | cnot control target different => rfl
  | toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      rw [ExternallyControlledPrimitivePlan.strictOperator,
        ExternallyControlledPrimitivePlan.semanticOperator,
        ClassicalReversibleStage.analyticOperator_eq_deterministicReference,
        applyOperator_deterministicOperator_basisKet,
        ExternallyControlledPrimitivePlan.positiveMultiControlledX_three_reference_apply_of_cleanWork
          layout valid control₀ control₁ target controlsDifferent firstDifferent
          secondDifferent input clean]
      exact (applyOperator_deterministicOperator_basisKet _ _).symm

/-- Every direct semantic leaf preserves the coherent clean-work span on basis
inputs. -/
theorem ExternallyControlledPrimitivePlan.semanticOperator_maps_cleanBasis
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (plan : ExternallyControlledPrimitivePlan sourceQubits)
    (input : QubitBasis targetQubits)
    (clean : externallyControlledCleanWorkPredicate valid input) :
    applyOperator (plan.semanticOperator symbolValue layout) (basisKet input) ∈
      SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate valid) := by
  cases plan with
  | x target =>
      exact deterministicXorPlaced_maps_cleanBasis valid target
        (fun basis => basis layout.control) input clean
  | z target =>
      exact embedControlledSingleQubitOperator_maps_cleanBasis valid target
        localZ input clean
  | h target =>
      exact embedControlledSingleQubitOperator_maps_cleanBasis valid target
        localH input clean
  | ry angle target =>
      exact embedControlledSingleQubitOperator_maps_cleanBasis valid target
        (localRy (angle.eval symbolValue)) input clean
  | phaseShift angle target =>
      rw [ExternallyControlledPrimitivePlan.semanticOperator,
        analyticControlledPhaseOperator_eq_embedControlledPhaseShift]
      exact embedControlledSingleQubitOperator_maps_cleanBasis valid target
        (localPhaseShift (angle.eval symbolValue)) input clean
  | rz angle target =>
      exact embedControlledSingleQubitOperator_maps_cleanBasis valid target
        (localRz (angle.eval symbolValue)) input clean
  | cnot control target different =>
      exact deterministicXorPlaced_maps_cleanBasis valid target
        (fun basis => basis layout.control && basis (layout.placement control))
        input clean
  | toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      exact deterministicXorPlaced_maps_cleanBasis valid target
        (fun basis => basis layout.control && basis (layout.placement control₀) &&
          basis (layout.placement control₁)) input clean

/-- One pure plan leaf compiles exactly to its independent full-dirty target. -/
theorem ExternallyControlledPrimitivePlan.compile_correct
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    ∀ plan : ExternallyControlledPrimitivePlan sourceQubits,
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) (plan.compile layout) =
        plan.strictOperator symbolValue layout
  | .x target => by
      rfl
  | .z target => by
      rw [ExternallyControlledPrimitivePlan.compile,
        Circuit.denote_fromList_eq_operatorSequence]
      rfl
  | .phaseShift angle target => by
      simpa [ExternallyControlledPrimitivePlan.compile,
        ExternallyControlledPrimitivePlan.strictOperator,
        externallyControlledPhaseShiftTarget] using
        (externallyControlledPhaseShiftFiveGateCircuit_correct
          symbolValue layout angle target)
  | .h target => by
      exact (controlledHadamardSpecialAngleExactOperatorComponent symbolValue {
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }).correct
  | .ry angle target => by
      simpa [ExternallyControlledPrimitivePlan.compile,
        ExternallyControlledPrimitivePlan.strictOperator,
        controlledRyMacroOperator] using
        (controlledRyMacroCircuit_denote_eq symbolValue {
          angle := angle
          control := layout.control
          target := layout.placement target
          different := layout.control_ne_placed target })
  | .rz angle target => by
      simpa [ExternallyControlledPrimitivePlan.compile,
        ExternallyControlledPrimitivePlan.strictOperator,
        controlledRzMacroOperator] using
        (controlledRzMacroCircuit_denote_eq symbolValue {
          angle := angle
          control := layout.control
          target := layout.placement target
          different := layout.control_ne_placed target })
  | .cnot sourceControl target different => by
      rfl
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent => by
      let stage := ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement control₀, layout.placement control₁]
        layout.controlWork (layout.placement target)
      change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) stage.compile =
        stage.analyticOperator
      rw [← ClassicalReversibleStage.primitiveExactOperatorComponent_circuit
        symbolValue stage]
      rw [(stage.primitiveExactOperatorComponent symbolValue).correct]
      exact ClassicalReversibleStage.primitiveExactOperatorComponent_target
        symbolValue stage

/-- Full-dirty Exact leaf component. -/
def ExternallyControlledPrimitivePlan.strictExactOperatorComponent
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : ExternallyControlledPrimitivePlan sourceQubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) where
  circuit := plan.compile layout
  target := plan.strictOperator symbolValue layout
  correct := plan.compile_correct symbolValue layout

/-- Full-dirty Unitary Exact leaf component. -/
def ExternallyControlledPrimitivePlan.strictUnitaryExactOperatorComponent
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : ExternallyControlledPrimitivePlan sourceQubits) :
    UnitaryExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) :=
  ExactOperatorComponent.toUnitary
    (primitiveGateOperatorWithSymbols_mem_unitaryGroup symbolValue)
    (plan.strictExactOperatorComponent symbolValue layout)

/-- Clean-work coherent component of one externally controlled plan leaf.

The circuit remains the full-dirty unitary compiler.  Only its refinement to
the desired work-preserving semantic target is restricted to the coherent
span generated by basis states with both decomposition work bits zero.
-/
def ExternallyControlledPrimitivePlan.cleanSubspaceMapComponent
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (plan : ExternallyControlledPrimitivePlan sourceQubits) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) :=
  SubspaceMapComponent.ofBasisSpan
    (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue)
    (plan.compile layout) (plan.semanticOperator symbolValue layout)
    (externallyControlledCleanWorkPredicate valid)
    (externallyControlledCleanWorkPredicate valid)
    (by
      intro input clean
      rw [plan.compile_correct symbolValue layout]
      exact plan.strictOperator_apply_eq_semanticOperator_of_clean
        symbolValue layout valid input clean)
    (by
      intro input clean
      exact plan.semanticOperator_maps_cleanBasis
        symbolValue layout valid input clean)

/-- The one-leaf dirty and semantic targets agree on the entire coherent
clean-work span, not only on its generating basis kets. -/
theorem ExternallyControlledPrimitivePlan.strictOperator_apply_eq_semanticOperator_of_mem
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (plan : ExternallyControlledPrimitivePlan sourceQubits)
    (state : State (QubitBasis targetQubits))
    (inside : state ∈ SubspaceMapComponent.basisSpan
      (externallyControlledCleanWorkPredicate valid)) :
    applyOperator (plan.strictOperator symbolValue layout) state =
      applyOperator (plan.semanticOperator symbolValue layout) state := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ inside
  · intro generator member
    rcases member with ⟨input, rfl⟩
    exact plan.strictOperator_apply_eq_semanticOperator_of_clean
      symbolValue layout valid input.1 input.2
  · simp
  · intro left right _leftInside _rightInside leftEq rightEq
    rw [applyOperator_add, applyOperator_add, leftEq, rightEq]
  · intro scalar basisState _stateInside stateEq
    rw [applyOperator_smul, applyOperator_smul, stateEq]

/-- A semantic leaf preserves the full coherent clean-work span. -/
theorem ExternallyControlledPrimitivePlan.semanticOperator_maps_cleanSpan
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (plan : ExternallyControlledPrimitivePlan sourceQubits)
    (state : State (QubitBasis targetQubits))
    (inside : state ∈ SubspaceMapComponent.basisSpan
      (externallyControlledCleanWorkPredicate valid)) :
    applyOperator (plan.semanticOperator symbolValue layout) state ∈
      SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate valid) := by
  exact (plan.cleanSubspaceMapComponent symbolValue layout valid).target_maps
    state inside

/-- The source-order dirty and semantic plan products agree on every state in
the common clean-work span.  This theorem is independent of any caller AST. -/
theorem ExternallyControlledPrimitivePlan.strictPlanOperator_apply_eq_semanticPlanOperator_of_mem
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid) :
    ∀ (plan : List (ExternallyControlledPrimitivePlan sourceQubits))
      (state : State (QubitBasis targetQubits)),
      state ∈ SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate valid) →
      applyOperator
          (ExternallyControlledPrimitivePlan.strictPlanOperator
            symbolValue layout plan) state =
        applyOperator
          (ExternallyControlledPrimitivePlan.semanticPlanOperator
            symbolValue layout plan) state
  | [], state, _inside => by
      simp [ExternallyControlledPrimitivePlan.strictPlanOperator,
        ExternallyControlledPrimitivePlan.semanticPlanOperator,
        operatorSequence]
  | first :: rest, state, inside => by
      have firstEq := first.strictOperator_apply_eq_semanticOperator_of_mem
        symbolValue layout valid state inside
      have firstInside := first.semanticOperator_maps_cleanSpan
        symbolValue layout valid state inside
      calc
        applyOperator
            (ExternallyControlledPrimitivePlan.strictPlanOperator
              symbolValue layout (first :: rest)) state =
          applyOperator
            (ExternallyControlledPrimitivePlan.strictPlanOperator
              symbolValue layout rest)
            (applyOperator (first.strictOperator symbolValue layout) state) := by
              simp [ExternallyControlledPrimitivePlan.strictPlanOperator,
                operatorSequence, applyOperator_mul]
        _ = applyOperator
            (ExternallyControlledPrimitivePlan.strictPlanOperator
              symbolValue layout rest)
            (applyOperator (first.semanticOperator symbolValue layout) state) := by
              rw [firstEq]
        _ = applyOperator
            (ExternallyControlledPrimitivePlan.semanticPlanOperator
              symbolValue layout rest)
            (applyOperator (first.semanticOperator symbolValue layout) state) :=
              ExternallyControlledPrimitivePlan.strictPlanOperator_apply_eq_semanticPlanOperator_of_mem
                symbolValue layout valid rest _ firstInside
        _ = applyOperator
            (ExternallyControlledPrimitivePlan.semanticPlanOperator
              symbolValue layout (first :: rest)) state := by
              simp [ExternallyControlledPrimitivePlan.semanticPlanOperator,
                operatorSequence, applyOperator_mul]

/-- Semantic support of an externally controlled placed plan.  Compiler work
wires are deliberately absent. -/
def externallyControlledSemanticSupport
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    Finset (Fin targetQubits) :=
  insert layout.control (Finset.univ.image layout.placement)

@[simp] theorem externallyControlledSemanticSupport_control
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    layout.control ∈ externallyControlledSemanticSupport layout := by
  simp [externallyControlledSemanticSupport]

@[simp] theorem externallyControlledSemanticSupport_placement
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (source : Fin sourceQubits) :
    layout.placement source ∈ externallyControlledSemanticSupport layout := by
  simp [externallyControlledSemanticSupport]

/-- Each clean semantic leaf is local to the external control and placed
source register, independently of compiler work wires. -/
theorem ExternallyControlledPrimitivePlan.semanticOperator_preservesOutside
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : ExternallyControlledPrimitivePlan sourceQubits) :
    OperatorPreservesOutside (externallyControlledSemanticSupport layout)
      (plan.semanticOperator symbolValue layout) := by
  have pairSubset (source : Fin sourceQubits) :
      ({layout.control, layout.placement source} : Finset (Fin targetQubits)) ⊆
        externallyControlledSemanticSupport layout := by
    intro wire member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact externallyControlledSemanticSupport_control layout
    · exact externallyControlledSemanticSupport_placement layout source
  have targetSubset (source : Fin sourceQubits) :
      ({layout.placement source} : Finset (Fin targetQubits)) ⊆
        externallyControlledSemanticSupport layout := by
    intro wire member
    have equal : wire = layout.placement source := by simpa using member
    subst wire
    exact externallyControlledSemanticSupport_placement layout source
  cases plan with
  | x target =>
      unfold ExternallyControlledPrimitivePlan.semanticOperator
      unfold reversibleAnalyticCnotOperator
      exact (OperatorPreservesOutside.deterministicXorWire
        (layout.placement target) (fun input => input layout.control)).mono
          (targetSubset target)
  | z target =>
      unfold ExternallyControlledPrimitivePlan.semanticOperator
      unfold embedControlledSingleQubitOperator
      exact (OperatorPreservesOutside.embedTwoQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (localControlledOperator localZ)).mono (pairSubset target)
  | h target =>
      unfold ExternallyControlledPrimitivePlan.semanticOperator
      unfold controlledHadamardSpecialAngleOperator
      unfold embedControlledSingleQubitOperator
      exact (OperatorPreservesOutside.embedTwoQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (localControlledOperator localH)).mono (pairSubset target)
  | ry angle target =>
      unfold ExternallyControlledPrimitivePlan.semanticOperator
      unfold embedControlledSingleQubitOperator
      exact (OperatorPreservesOutside.embedTwoQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (localControlledOperator (localRy (angle.eval symbolValue)))).mono
          (pairSubset target)
  | phaseShift angle target =>
      rw [ExternallyControlledPrimitivePlan.semanticOperator,
        analyticControlledPhaseOperator_eq_embedControlledPhaseShift]
      unfold embedControlledSingleQubitOperator
      exact (OperatorPreservesOutside.embedTwoQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (localControlledOperator (localPhaseShift (angle.eval symbolValue)))).mono
          (pairSubset target)
  | rz angle target =>
      unfold ExternallyControlledPrimitivePlan.semanticOperator
      unfold embedControlledSingleQubitOperator
      exact (OperatorPreservesOutside.embedTwoQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (localControlledOperator (localRz (angle.eval symbolValue)))).mono
          (pairSubset target)
  | cnot sourceControl target different =>
      unfold ExternallyControlledPrimitivePlan.semanticOperator
      unfold analyticToffoliOperator
      exact (OperatorPreservesOutside.deterministicXorWire
        (layout.placement target) (fun input =>
          input layout.control && input (layout.placement sourceControl))).mono
            (targetSubset target)
  | toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      unfold ExternallyControlledPrimitivePlan.semanticOperator
      unfold ExternallyControlledPrimitivePlan.tripleControlledXOperator
      unfold ExternallyControlledPrimitivePlan.tripleControlledXBasisAction
      exact (OperatorPreservesOutside.deterministicXorWire
        (layout.placement target) (fun input =>
          input layout.control && input (layout.placement control₀) &&
            input (layout.placement control₁))).mono (targetSubset target)

/-- The source-order semantic plan product is local to the same work-free
support because every leaf has that common locality. -/
theorem ExternallyControlledPrimitivePlan.semanticPlanOperator_preservesOutside
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    OperatorPreservesOutside (externallyControlledSemanticSupport layout)
      (ExternallyControlledPrimitivePlan.semanticPlanOperator
        symbolValue layout plan) := by
  unfold ExternallyControlledPrimitivePlan.semanticPlanOperator
  apply OperatorPreservesOutside.operatorSequence_of_forall
  intro operator member
  rcases List.mem_map.mp member with ⟨leaf, leafMember, rfl⟩
  exact leaf.semanticOperator_preservesOutside symbolValue layout

/-- The complete semantic plan writes only placed source wires.  In
particular, the external control is preserved even though it is read by every
controlled leaf. -/
theorem ExternallyControlledPrimitivePlan.semanticPlanOperator_preservesOutsidePlacement
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    OperatorPreservesOutside (Finset.univ.image layout.placement)
      (ExternallyControlledPrimitivePlan.semanticPlanOperator
        symbolValue layout plan) := by
  rw [ExternallyControlledPrimitivePlan.semanticPlanOperator_eq_controlledWireLift]
  exact externallyControlledWireLiftOperator_preservesOutsidePlacement layout _

/-- Typed composition certificate for a clean-work plan.  Besides the
component value, it records the exact coherent spaces and the independently
assembled target/circuit transports used by the recursive composition. -/
private structure ExternallyControlledCleanPlanBundle
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) where
  component : SubspaceMapComponent
    (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue)
  inputSubspace_eq : component.inputSubspace =
    SubspaceMapComponent.basisSpan
      (externallyControlledCleanWorkPredicate valid)
  outputSubspace_eq : component.outputSubspace =
    SubspaceMapComponent.basisSpan
      (externallyControlledCleanWorkPredicate valid)
  target_eq : component.target =
    ExternallyControlledPrimitivePlan.semanticPlanOperator
      symbolValue layout plan
  circuit_eq : component.circuit =
    Circuit.sequence (plan.map fun leaf => leaf.compile layout)

/-- Recursively compose clean leaf contracts while retaining typed evidence
for every direct-child edge and every transport equality. -/
private def externallyControlledCleanPlanBundle
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid) :
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) →
      ExternallyControlledCleanPlanBundle symbolValue layout valid plan
  | [] => by
      let component := SubspaceMapComponent.ofBasisSpan
        (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue)
        .identity 1
        (externallyControlledCleanWorkPredicate valid)
        (externallyControlledCleanWorkPredicate valid)
        (by intro input clean; simp [Circuit.denote, applyOperator])
        (by
          intro input clean
          simpa [applyOperator] using
            (SubspaceMapComponent.basisKet_mem_basisSpan clean))
      exact {
        component := component
        inputSubspace_eq := by
          rfl
        outputSubspace_eq := by
          rfl
        target_eq := by
          rfl
        circuit_eq := by
          rfl }
  | first :: rest => by
      let firstComponent :=
        first.cleanSubspaceMapComponent symbolValue layout valid
      let restBundle := externallyControlledCleanPlanBundle
        symbolValue layout valid rest
      have firstInput : firstComponent.inputSubspace =
          SubspaceMapComponent.basisSpan
            (externallyControlledCleanWorkPredicate valid) := by
        rfl
      have firstOutput : firstComponent.outputSubspace =
          SubspaceMapComponent.basisSpan
            (externallyControlledCleanWorkPredicate valid) := by
        rfl
      have middle : restBundle.component.inputSubspace =
          firstComponent.outputSubspace := by
        rw [restBundle.inputSubspace_eq, firstOutput]
      let component := SubspaceMapComponent.seq
        firstComponent restBundle.component middle
      exact {
        component := component
        inputSubspace_eq := by
          exact firstInput
        outputSubspace_eq := by
          exact restBundle.outputSubspace_eq
        target_eq := by
          change restBundle.component.target * firstComponent.target = _
          rw [restBundle.target_eq]
          change
            ExternallyControlledPrimitivePlan.semanticPlanOperator
                symbolValue layout rest *
              first.semanticOperator symbolValue layout = _
          simp [ExternallyControlledPrimitivePlan.semanticPlanOperator,
            operatorSequence]
        circuit_eq := by
          change Circuit.seq firstComponent.circuit restBundle.component.circuit = _
          rw [restBundle.circuit_eq]
          change Circuit.seq (first.compile layout)
              (Circuit.sequence (rest.map fun leaf => leaf.compile layout)) = _
          rfl }

/-- Full source-order clean-work semantic component, composed directly from
the public leaf `SubspaceMapComponent` contracts. -/
def externallyControlledCleanSubspaceMapComponent
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) :=
  (externallyControlledCleanPlanBundle symbolValue layout valid plan).component

/-- The clean component target is exactly the independent semantic plan
product in execution order. -/
theorem externallyControlledCleanSubspaceMapComponent_target
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    (externallyControlledCleanSubspaceMapComponent
        symbolValue layout valid plan).target =
      ExternallyControlledPrimitivePlan.semanticPlanOperator
        symbolValue layout plan :=
  (externallyControlledCleanPlanBundle
    symbolValue layout valid plan).target_eq

/-- The clean component circuit is the source-order sequence of the same
compiled leaf circuits used by the full-dirty component. -/
theorem externallyControlledCleanSubspaceMapComponent_circuit
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    (externallyControlledCleanSubspaceMapComponent
        symbolValue layout valid plan).circuit =
      Circuit.sequence (plan.map fun leaf => leaf.compile layout) :=
  (externallyControlledCleanPlanBundle
    symbolValue layout valid plan).circuit_eq

/-- Full source-order plan compiled from public Unitary Exact leaf contracts. -/
def externallyControlledStrictUnitaryExactOperatorComponent
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    UnitaryExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) :=
  UnitaryExactOperatorComponent.sequence <|
    plan.map fun leaf => leaf.strictUnitaryExactOperatorComponent symbolValue layout

/-- The full dirty compiler target is the independent strict plan product. -/
theorem externallyControlledStrictUnitaryExactOperatorComponent_target
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    (externallyControlledStrictUnitaryExactOperatorComponent
        symbolValue layout plan).target =
      ExternallyControlledPrimitivePlan.strictPlanOperator
        symbolValue layout plan := by
  rw [externallyControlledStrictUnitaryExactOperatorComponent,
    UnitaryExactOperatorComponent.sequence_target_eq_operatorSequence]
  unfold ExternallyControlledPrimitivePlan.strictPlanOperator
  simp only [List.map_map]
  rfl

/-- Compile every source leaf in its original source order. -/
def compileExternallyControlledCircuit
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (circuit : Circuit (PrimitiveGate sourceQubits)) :
    Circuit (PrimitiveGate targetQubits) :=
  circuit.compileGates (compileExternallyControlledPrimitive layout)

/-- The compiled flat stream is the source-order concatenation of leaf
expansions. -/
theorem flatten_compileExternallyControlledCircuit
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (circuit : Circuit (PrimitiveGate sourceQubits)) :
    (compileExternallyControlledCircuit layout circuit).flatten =
      circuit.flatten.flatMap fun gate =>
        (compileExternallyControlledPrimitive layout gate).flatten := by
  exact Circuit.flatten_compileGates
    (compileExternallyControlledPrimitive layout) circuit

/-- Decoding and compiling a supported source stream preserves exact order. -/
theorem decodeSupportedPrimitiveStream_compile_flatMap
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (gates : List (PrimitiveGate sourceQubits))
    (supported : ∀ gate, gate ∈ gates →
      IsExternallyControllablePrimitive gate) :
    List.flatMap (fun leaf => (leaf.compile layout).flatten)
      (decodeSupportedPrimitiveStream gates supported) =
      List.flatMap (fun gate =>
        (compileExternallyControlledPrimitive layout gate).flatten) gates := by
  induction gates with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      have firstSupported := supported first (by simp)
      have restSupported : ∀ gate, gate ∈ rest →
          IsExternallyControllablePrimitive gate := by
        intro gate member
        exact supported gate (by simp [member])
      simp only [decodeSupportedPrimitiveStream, List.flatMap_cons]
      rw [ExternallyControlledPrimitivePlan.compile_ofPrimitive
        layout first firstSupported]
      exact congrArg (fun value =>
        (compileExternallyControlledPrimitive layout first).flatten ++ value)
        (inductionHypothesis restSupported)

theorem flatten_sequence_decodeSupportedPrimitiveCircuit_compile
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (circuit : Circuit (PrimitiveGate sourceQubits))
    (supported : ∀ gate, gate ∈ circuit.flatten →
      IsExternallyControllablePrimitive gate) :
    (Circuit.sequence
      ((decodeSupportedPrimitiveCircuit circuit supported).map fun leaf =>
        leaf.compile layout)).flatten =
      (compileExternallyControlledCircuit layout circuit).flatten := by
  rw [Circuit.flatten_sequence, flatten_compileExternallyControlledCircuit]
  simpa [decodeSupportedPrimitiveCircuit, List.flatMap_map] using
    (decodeSupportedPrimitiveStream_compile_flatMap
      layout circuit.flatten supported)

/-- Exact contract transport through the source-faithful leaf compiler.
The operator lift is supplied independently as a monoid homomorphism; the
caller proves leaf semantics only for source leaves present in the AST. -/
def externallyControlledExactOperatorComponent
    {sourceQubits targetQubits : Nat}
    (sourceSymbolValue targetSymbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (operatorLift : Operator (QubitBasis sourceQubits) →*
      Operator (QubitBasis targetQubits))
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) sourceSymbolValue))
    (leavesSupported : ∀ gate, gate ∈ component.circuit.flatten →
      IsExternallyControllablePrimitive gate)
    (leafCorrect : ∀ gate, IsExternallyControllablePrimitive gate →
      Circuit.denote
          (primitiveGateOperatorWithSymbols (qubits := targetQubits) targetSymbolValue)
          (compileExternallyControlledPrimitive layout gate) =
        operatorLift (primitiveGateOperatorWithSymbols sourceSymbolValue gate)) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) targetSymbolValue) :=
  ExactOperatorComponent.liftByCircuitCompiler
    (primitiveGateOperatorWithSymbols (qubits := sourceQubits) sourceSymbolValue)
    (primitiveGateOperatorWithSymbols (qubits := targetQubits) targetSymbolValue)
    (compileExternallyControlledPrimitive layout) operatorLift component
    (fun gate member => leafCorrect gate (leavesSupported gate member))

/-- Unitary Exact transport through the same source-faithful compiler. -/
def externallyControlledUnitaryExactOperatorComponent
    {sourceQubits targetQubits : Nat}
    (sourceSymbolValue targetSymbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (operatorLift : Operator (QubitBasis sourceQubits) →*
      Operator (QubitBasis targetQubits))
    (unitaryPreserved : ∀ {operator : Operator (QubitBasis sourceQubits)},
      operator ∈ Matrix.unitaryGroup (QubitBasis sourceQubits) ℂ →
        operatorLift operator ∈ Matrix.unitaryGroup (QubitBasis targetQubits) ℂ)
    (component : UnitaryExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) sourceSymbolValue))
    (leavesSupported : ∀ gate, gate ∈ component.circuit.flatten →
      IsExternallyControllablePrimitive gate)
    (leafCorrect : ∀ gate, IsExternallyControllablePrimitive gate →
      Circuit.denote
          (primitiveGateOperatorWithSymbols (qubits := targetQubits) targetSymbolValue)
          (compileExternallyControlledPrimitive layout gate) =
        operatorLift (primitiveGateOperatorWithSymbols sourceSymbolValue gate)) :
    UnitaryExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) targetSymbolValue) :=
  UnitaryExactOperatorComponent.liftByCircuitCompiler
    (primitiveGateOperatorWithSymbols (qubits := sourceQubits) sourceSymbolValue)
    (primitiveGateOperatorWithSymbols (qubits := targetQubits) targetSymbolValue)
    (compileExternallyControlledPrimitive layout) operatorLift unitaryPreserved
    component
    (fun gate member => leafCorrect gate (leavesSupported gate member))

/-!
## Exact-child decoder boundary

The older generic compiler transport above deliberately exposes a
`leafCorrect` premise.  That premise is useful for genuinely new compiler
semantics, but is too low-level for consumers of the verified primitive
external-control compiler in this file.  The API below instead accepts only a
typed supported-leaf certificate.  All leaf correctness is discharged by the
public strict and clean plan components above.
-/

/-- Evidence that every primitive leaf in a circuit can be decoded by the
verified external-control compiler.  This certificate contains syntax
classification only; it contains no operator-equality proof supplied by an
application. -/
structure ExternallyControlledPrimitiveCircuitCertificate
    {sourceQubits : Nat}
    (circuit : Circuit (PrimitiveGate sourceQubits)) : Prop where
  leavesSupported : ∀ gate, gate ∈ circuit.flatten →
    IsExternallyControllablePrimitive gate

namespace ExternallyControlledPrimitiveCircuitCertificate

/-- The canonical source-order typed plan decoded from a certified circuit. -/
def plan {sourceQubits : Nat}
    {circuit : Circuit (PrimitiveGate sourceQubits)}
    (certificate : ExternallyControlledPrimitiveCircuitCertificate circuit) :
    List (ExternallyControlledPrimitivePlan sourceQubits) :=
  decodeSupportedPrimitiveCircuit circuit certificate.leavesSupported

/-- Re-encoding the canonical typed plan returns the exact flattened
source stream after normalized source expansion. -/
theorem plan_sourceNormalized_flatten {sourceQubits : Nat}
    {circuit : Circuit (PrimitiveGate sourceQubits)}
    (certificate : ExternallyControlledPrimitiveCircuitCertificate circuit) :
    (Circuit.sequence
      (certificate.plan.map
        ExternallyControlledPrimitivePlan.sourceNormalizedCircuit)).flatten =
      circuit.flatten :=
  decodeSupportedPrimitiveCircuit_sourceNormalized_flatten
    circuit certificate.leavesSupported

end ExternallyControlledPrimitiveCircuitCertificate

/-- Every leaf produced by the classical reversible-stage compiler belongs to
the source-faithful external-control inventory.  This is the reusable B7
certificate boundary for X/CNOT/Toffoli stages; applications need not inspect
the compiled primitive AST again. -/
theorem ClassicalReversibleStage.compile_leavesExternallyControllable
    {qubits : Nat} (stage : ClassicalReversibleStage qubits) :
    ∀ gate, gate ∈ stage.compile.flatten →
      IsExternallyControllablePrimitive gate := by
  intro gate member
  rw [ClassicalReversibleStage.compile, Circuit.flatten_mapGates] at member
  rcases List.mem_map.mp member with ⟨instruction, _instructionMember, rfl⟩
  cases instruction <;>
    simp [ClassicalReversibleInstruction.toPrimitiveGate,
      IsExternallyControllablePrimitive]

/-- Proof-bearing controlled-subcircuit certificate for any compiled
classical reversible stage. -/
theorem ClassicalReversibleStage.externallyControlledPrimitiveCircuitCertificate
    {qubits : Nat} (stage : ClassicalReversibleStage qubits) :
    ExternallyControlledPrimitiveCircuitCertificate stage.compile where
  leavesSupported := stage.compile_leavesExternallyControllable

/-- The analytic source operator of a plan leaf is exactly the denotation
of its normalized source expansion. -/
@[simp] theorem ExternallyControlledPrimitivePlan.sourceOperator_eq_sourceNormalizedCircuit
    {qubits : Nat} (symbolValue : String → ℝ)
    (plan : ExternallyControlledPrimitivePlan qubits) :
    plan.sourceOperator symbolValue =
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        plan.sourceNormalizedCircuit :=
  (plan.sourceNormalizedCircuit_correct symbolValue).symm

@[simp] theorem ExternallyControlledPrimitivePlan.sourceOperator_ofPrimitive
    {qubits : Nat} (symbolValue : String → ℝ)
    (gate : PrimitiveGate qubits)
    (supported : IsExternallyControllablePrimitive gate) :
    ExternallyControlledPrimitivePlan.sourceOperator symbolValue
        (ExternallyControlledPrimitivePlan.ofPrimitive gate supported) =
      primitiveGateOperatorWithSymbols symbolValue gate := by
  cases gate with
  | x target =>
      simp [ExternallyControlledPrimitivePlan.ofPrimitive,
        ExternallyControlledPrimitivePlan.sourceOperator,
        primitiveGateOperatorWithSymbols]
  | h target => rfl
  | ry angle target => rfl
  | phaseShift angle target => rfl
  | cnot control target different => rfl
  | toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent => rfl

theorem decodeSupportedPrimitiveStream_sourcePlanOperator_eq_operatorSequence
    {qubits : Nat} (symbolValue : String → ℝ)
    (gates : List (PrimitiveGate qubits))
    (supported : ∀ gate, gate ∈ gates →
      IsExternallyControllablePrimitive gate) :
    operatorSequence
        ((decodeSupportedPrimitiveStream gates supported).map
          (ExternallyControlledPrimitivePlan.sourceOperator symbolValue)) =
      operatorSequence (gates.map (primitiveGateOperatorWithSymbols symbolValue)) := by
  induction gates with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      have firstSupported := supported first (by simp)
      have restSupported : ∀ gate, gate ∈ rest →
          IsExternallyControllablePrimitive gate := by
        intro gate member
        exact supported gate (by simp [member])
      have firstEq :=
        ExternallyControlledPrimitivePlan.sourceOperator_ofPrimitive
          symbolValue first firstSupported
      simp only [decodeSupportedPrimitiveStream, List.map_cons]
      rw [firstEq]
      simp only [operatorSequence]
      rw [inductionHypothesis restSupported]

theorem decodeSupportedPrimitiveCircuit_sourcePlanOperator_eq_circuit_denote
    {qubits : Nat} (symbolValue : String → ℝ)
    (circuit : Circuit (PrimitiveGate qubits))
    (supported : ∀ gate, gate ∈ circuit.flatten →
      IsExternallyControllablePrimitive gate) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator symbolValue
        (decodeSupportedPrimitiveCircuit circuit supported) =
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) circuit := by
  rw [Circuit.denote_eq_operatorSequence_flatten]
  simpa [decodeSupportedPrimitiveCircuit,
    ExternallyControlledPrimitivePlan.sourcePlanOperator] using
    (decodeSupportedPrimitiveStream_sourcePlanOperator_eq_operatorSequence
      symbolValue circuit.flatten supported)

/-- The decoded source-plan target of an Exact child is its public target.
This is the semantic link between the child contract and both externally
controlled compiler layers below. -/
theorem ExternallyControlledPrimitiveCircuitCertificate.sourcePlanOperator_eq_component_target
    {sourceQubits : Nat} (symbolValue : String → ℝ)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator
        symbolValue certificate.plan = component.target := by
  calc
    ExternallyControlledPrimitivePlan.sourcePlanOperator
        symbolValue certificate.plan =
        Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          component.circuit :=
      decodeSupportedPrimitiveCircuit_sourcePlanOperator_eq_circuit_denote
        symbolValue component.circuit certificate.leavesSupported
    _ = component.target := component.correct

/-- Full-space Exact external-control compiler for a certified public Exact
child.  Its target is the dirty-work compiler product; no clean-work semantic
claim is made by this component. -/
def externallyControlledStrictExactOperatorComponentOfExact
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) :=
  ExactOperatorComponent.sequenceComponents
    (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue)
    (certificate.plan.map fun leaf =>
      leaf.strictExactOperatorComponent symbolValue layout)

/-- The strict Exact target is the independent dirty-work compiler product. -/
theorem externallyControlledStrictExactOperatorComponentOfExact_target
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    (externallyControlledStrictExactOperatorComponentOfExact
      symbolValue layout component certificate).target =
        ExternallyControlledPrimitivePlan.strictPlanOperator
          symbolValue layout certificate.plan := by
  rw [externallyControlledStrictExactOperatorComponentOfExact,
    ExactOperatorComponent.sequence_target_eq_operatorSequence]
  simp [ExternallyControlledPrimitivePlan.strictPlanOperator,
    ExternallyControlledPrimitivePlan.strictExactOperatorComponent,
    List.map_map, Function.comp_def]

/-- The strict implementation AST is the source-order sequence of verified
compiled leaf circuits. -/
theorem externallyControlledStrictExactOperatorComponentOfExact_circuit
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    (externallyControlledStrictExactOperatorComponentOfExact
      symbolValue layout component certificate).circuit =
        Circuit.sequence
          (certificate.plan.map fun leaf => leaf.compile layout) := by
  simpa [externallyControlledStrictExactOperatorComponentOfExact,
    ExternallyControlledPrimitivePlan.strictExactOperatorComponent,
    List.map_map, Function.comp_def] using
    ExactOperatorComponent.sequenceComponents_circuit
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue)
      (certificate.plan.map fun leaf =>
        leaf.strictExactOperatorComponent symbolValue layout)

/-- Flattening the strict implementation gives the direct source-faithful
leaf compiler applied to the Exact child's original circuit. -/
theorem externallyControlledStrictExactOperatorComponentOfExact_flatten
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    (externallyControlledStrictExactOperatorComponentOfExact
      symbolValue layout component certificate).circuit.flatten =
        (compileExternallyControlledCircuit
          layout component.circuit).flatten := by
  rw [externallyControlledStrictExactOperatorComponentOfExact_circuit]
  exact flatten_sequence_decodeSupportedPrimitiveCircuit_compile
    layout component.circuit certificate.leavesSupported

/-- Coherent clean-work refinement of the same certified Exact child.  The
circuit remains the strict compiler AST, while the target is the independent
work-preserving semantic plan and both spaces are the clean-work basis span. -/
def externallyControlledCleanSubspaceMapComponentOfExact
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) :=
  externallyControlledCleanSubspaceMapComponent
    symbolValue layout valid certificate.plan

/-- Circuit projection for the clean Exact-child lift. -/
theorem externallyControlledCleanSubspaceMapComponentOfExact_circuit
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    (externallyControlledCleanSubspaceMapComponentOfExact
      symbolValue layout valid component certificate).circuit =
        Circuit.sequence
          (certificate.plan.map fun leaf => leaf.compile layout) := by
  exact externallyControlledCleanSubspaceMapComponent_circuit
    symbolValue layout valid certificate.plan

/-- Target projection for the clean Exact-child lift. -/
theorem externallyControlledCleanSubspaceMapComponentOfExact_target
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    (externallyControlledCleanSubspaceMapComponentOfExact
      symbolValue layout valid component certificate).target =
        ExternallyControlledPrimitivePlan.semanticPlanOperator
          symbolValue layout certificate.plan := by
  exact externallyControlledCleanSubspaceMapComponent_target
    symbolValue layout valid certificate.plan

/-- Input-space projection for the clean Exact-child lift. -/
theorem externallyControlledCleanSubspaceMapComponentOfExact_inputSubspace
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    (externallyControlledCleanSubspaceMapComponentOfExact
      symbolValue layout valid component certificate).inputSubspace =
        SubspaceMapComponent.basisSpan
          (externallyControlledCleanWorkPredicate valid) := by
  exact (externallyControlledCleanPlanBundle
    symbolValue layout valid certificate.plan).inputSubspace_eq

/-- Output-space projection for the clean Exact-child lift. -/
theorem externallyControlledCleanSubspaceMapComponentOfExact_outputSubspace
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    (externallyControlledCleanSubspaceMapComponentOfExact
      symbolValue layout valid component certificate).outputSubspace =
        SubspaceMapComponent.basisSpan
          (externallyControlledCleanWorkPredicate valid) := by
  exact (externallyControlledCleanPlanBundle
    symbolValue layout valid certificate.plan).outputSubspace_eq

/-- The strict and clean layers use definitionally the same source-order
compiler AST. -/
theorem externallyControlledCleanSubspaceMapComponentOfExact_circuit_eq_strict
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit) :
    (externallyControlledCleanSubspaceMapComponentOfExact
      symbolValue layout valid component certificate).circuit =
      (externallyControlledStrictExactOperatorComponentOfExact
        symbolValue layout component certificate).circuit := by
  rw [externallyControlledCleanSubspaceMapComponentOfExact_circuit,
    externallyControlledStrictExactOperatorComponentOfExact_circuit]

/-- The actual compiled circuit preserves the coherent clean-work span.

This is the public work-restoration theorem for the external-control compiler:
the full circuit may use the two compiler-work wires on dirty basis states, but
every coherent input supported on `work₀ = work₁ = false` is mapped back into
the same coherent span.  Together with
`externallyControlledCleanWorkPredicate_iff_controlWork_zero`, this states the
two-work-register restoration condition without replacing the full-dirty
Exact target by its clean refinement. -/
theorem externallyControlledCleanSubspaceMapComponentOfExact_actual_maps_cleanWork
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit)
    (state : State (QubitBasis targetQubits))
    (inside : state ∈ SubspaceMapComponent.basisSpan
      (externallyControlledCleanWorkPredicate valid)) :
    applyOperator
        ((externallyControlledCleanSubspaceMapComponentOfExact
          symbolValue layout valid component certificate).circuit.denote
            (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue))
        state ∈
      SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate valid) := by
  let cleanComponent :=
    externallyControlledCleanSubspaceMapComponentOfExact
      symbolValue layout valid component certificate
  have inputSpace : cleanComponent.inputSubspace =
      SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate valid) := by
    dsimp [cleanComponent]
    exact externallyControlledCleanSubspaceMapComponentOfExact_inputSubspace
      symbolValue layout valid component certificate
  have outputSpace : cleanComponent.outputSubspace =
      SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate valid) := by
    dsimp [cleanComponent]
    exact externallyControlledCleanSubspaceMapComponentOfExact_outputSubspace
      symbolValue layout valid component certificate
  have mapped := cleanComponent.actual_maps state (by
    rw [inputSpace]
    exact inside)
  rw [outputSpace] at mapped
  exact mapped

private theorem controlledCompiler_basisSpan_apply_eq_zero
    {basis : Type*} [DecidableEq basis]
    {predicate : basis → Prop} {state : State basis}
    (inside : state ∈ SubspaceMapComponent.basisSpan predicate)
    (output : basis) (outside : ¬ predicate output) :
    state output = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ inside
  · intro generator member
    rcases member with ⟨input, rfl⟩
    by_cases equal : output = input.1
    · subst output
      exact False.elim (outside input.2)
    · simp [basisKet, equal]
  · rfl
  · intro left right _ _ leftZero rightZero
    simp [leftZero, rightZero]
  · intro scalar value _ valueZero
    simp [valueZero]

/-- Lift an asymmetric source basis contract through the actual leaf-wise
external-control compiler.  This is the reusable bridge for block encodings:
source signal ancillas may be zero only at input, while source work ancillas
are restored at output. -/
def externallyControlledAsymmetricSubspaceMapComponentOfExact
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit)
    (inputPredicate outputPredicate : QubitBasis sourceQubits → Prop)
    (sourceMaps : ∀ input output,
      inputPredicate input → ¬ outputPredicate output →
        ExternallyControlledPrimitivePlan.sourcePlanOperator
          symbolValue certificate.plan output input = 0)
    (inputImpliesOutput : ∀ input,
      inputPredicate input → outputPredicate input) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) :=
  let strict := externallyControlledStrictExactOperatorComponentOfExact
    symbolValue layout component certificate
  SubspaceMapComponent.ofBasisSpan
    (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue)
    strict.circuit
    (ExternallyControlledPrimitivePlan.semanticPlanOperator
      symbolValue layout certificate.plan)
    (externallyControlledPlacedInputPredicate valid inputPredicate)
    (externallyControlledPlacedOutputPredicate valid outputPredicate)
    (by
      intro input inside
      calc
        applyOperator
            (strict.circuit.denote
              (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue))
            (basisKet input) =
            applyOperator strict.target (basisKet input) :=
          congrArg (fun operator => applyOperator operator (basisKet input))
            strict.correct
        _ = applyOperator
            (ExternallyControlledPrimitivePlan.semanticPlanOperator
              symbolValue layout certificate.plan) (basisKet input) := by
          rw [show strict.target =
              ExternallyControlledPrimitivePlan.strictPlanOperator
                symbolValue layout certificate.plan from
            externallyControlledStrictExactOperatorComponentOfExact_target
              symbolValue layout component certificate]
          apply ExternallyControlledPrimitivePlan.strictPlanOperator_apply_eq_semanticPlanOperator_of_mem
          exact SubspaceMapComponent.basisKet_mem_basisSpan inside.1)
    (by
      intro input inside
      apply SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_entry_support
      intro output outside
      by_cases compilerClean :
          externallyControlledCleanWorkPredicate valid output
      · have sourceOutside : ¬ outputPredicate
            (restrictToPlacedWires layout.placement output) := by
          intro sourceClean
          exact outside ⟨compilerClean, sourceClean⟩
        rw [ExternallyControlledPrimitivePlan.semanticPlanOperator_eq_controlledWireLift]
        exact externallyControlledWireLiftOperator_basisTransition
          layout
          (ExternallyControlledPrimitivePlan.sourcePlanOperator
            symbolValue certificate.plan)
          inputPredicate outputPredicate sourceMaps inputImpliesOutput
          input output inside.2 sourceOutside
      · let cleanComponent :=
          externallyControlledCleanSubspaceMapComponentOfExact
            symbolValue layout valid component certificate
        have inputSpace : cleanComponent.inputSubspace =
            SubspaceMapComponent.basisSpan
              (externallyControlledCleanWorkPredicate valid) := by
          dsimp [cleanComponent]
          exact externallyControlledCleanSubspaceMapComponentOfExact_inputSubspace
            symbolValue layout valid component certificate
        have outputSpace : cleanComponent.outputSubspace =
            SubspaceMapComponent.basisSpan
              (externallyControlledCleanWorkPredicate valid) := by
          dsimp [cleanComponent]
          exact externallyControlledCleanSubspaceMapComponentOfExact_outputSubspace
            symbolValue layout valid component certificate
        have targetEq : cleanComponent.target =
            ExternallyControlledPrimitivePlan.semanticPlanOperator
              symbolValue layout certificate.plan := by
          dsimp [cleanComponent]
          exact externallyControlledCleanSubspaceMapComponentOfExact_target
            symbolValue layout valid component certificate
        have compilerMapped := cleanComponent.target_maps
          (basisKet input) (by
            rw [inputSpace]
            exact SubspaceMapComponent.basisKet_mem_basisSpan inside.1)
        rw [targetEq, outputSpace] at compilerMapped
        simpa only [applyOperator_basisKet] using
          controlledCompiler_basisSpan_apply_eq_zero
            compilerMapped output compilerClean)

@[simp] theorem
    externallyControlledAsymmetricSubspaceMapComponentOfExact_circuit
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit)
    (inputPredicate outputPredicate : QubitBasis sourceQubits → Prop)
    (sourceMaps : ∀ input output,
      inputPredicate input → ¬ outputPredicate output →
        ExternallyControlledPrimitivePlan.sourcePlanOperator
          symbolValue certificate.plan output input = 0)
    (inputImpliesOutput : ∀ input,
      inputPredicate input → outputPredicate input) :
    (externallyControlledAsymmetricSubspaceMapComponentOfExact
      symbolValue layout valid component certificate inputPredicate
      outputPredicate sourceMaps inputImpliesOutput).circuit =
      (externallyControlledStrictExactOperatorComponentOfExact
        symbolValue layout component certificate).circuit := by
  rfl

@[simp] theorem
    externallyControlledAsymmetricSubspaceMapComponentOfExact_target
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit)
    (inputPredicate outputPredicate : QubitBasis sourceQubits → Prop)
    (sourceMaps : ∀ input output,
      inputPredicate input → ¬ outputPredicate output →
        ExternallyControlledPrimitivePlan.sourcePlanOperator
          symbolValue certificate.plan output input = 0)
    (inputImpliesOutput : ∀ input,
      inputPredicate input → outputPredicate input) :
    (externallyControlledAsymmetricSubspaceMapComponentOfExact
      symbolValue layout valid component certificate inputPredicate
      outputPredicate sourceMaps inputImpliesOutput).target =
      ExternallyControlledPrimitivePlan.semanticPlanOperator
        symbolValue layout certificate.plan := by
  rfl

theorem externallyControlledAsymmetricSubspaceMapComponentOfExact_spaces
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      component.circuit)
    (inputPredicate outputPredicate : QubitBasis sourceQubits → Prop)
    (sourceMaps : ∀ input output,
      inputPredicate input → ¬ outputPredicate output →
        ExternallyControlledPrimitivePlan.sourcePlanOperator
          symbolValue certificate.plan output input = 0)
    (inputImpliesOutput : ∀ input,
      inputPredicate input → outputPredicate input) :
    (externallyControlledAsymmetricSubspaceMapComponentOfExact
        symbolValue layout valid component certificate inputPredicate
        outputPredicate sourceMaps inputImpliesOutput).inputSubspace =
        SubspaceMapComponent.basisSpan
          (externallyControlledPlacedInputPredicate valid inputPredicate) ∧
      (externallyControlledAsymmetricSubspaceMapComponentOfExact
        symbolValue layout valid component certificate inputPredicate
        outputPredicate sourceMaps inputImpliesOutput).outputSubspace =
        SubspaceMapComponent.basisSpan
          (externallyControlledPlacedOutputPredicate valid outputPredicate) := by
  constructor <;> rfl

end

end VerifiedCircuitCore

namespace VerifiedCircuitCore

noncomputable section

section NormalizedMacro

/-- Parallel entry point for certified normalized source circuits.  The
legacy compiler above remains the compatibility surface; this bridge delegates
the new path to the V2 compiler and retains its independent target contract. -/
def externallyControlledNormalizedMacroCircuit
    {sourceQubits targetQubits : Nat}
    (layout : ControlledCircuitCompilerV2.ControlLayout
      sourceQubits targetQubits)
    (source : ControlledCircuitCompilerV2.NormalizedCircuit sourceQubits) :
    ControlledCircuitCompilerV2.NormalizedCircuit targetQubits :=
  ControlledCircuitCompilerV2.controlCircuit layout source

theorem externallyControlledNormalizedMacroCircuit_normalized
    {sourceQubits targetQubits : Nat}
    (layout : ControlledCircuitCompilerV2.ControlLayout
      sourceQubits targetQubits)
    (source : ControlledCircuitCompilerV2.NormalizedCircuit sourceQubits) :
    ControlledCircuitCompilerV2.IsNormalizedCircuit
      (externallyControlledNormalizedMacroCircuit layout source).circuit :=
  (externallyControlledNormalizedMacroCircuit layout source).normalized

/-- Sequencing is exposed explicitly so the consumer cannot reorder source
leaves while moving from the legacy compiler to the normalized surface. -/
theorem externallyControlledNormalizedMacroCircuit_sequence
    {sourceQubits targetQubits : Nat}
    (layout : ControlledCircuitCompilerV2.ControlLayout
      sourceQubits targetQubits)
    (first second : ControlledCircuitCompilerV2.NormalizedCircuit sourceQubits) :
    (externallyControlledNormalizedMacroCircuit layout
      (ControlledCircuitCompilerV2.NormalizedCircuit.seq first second)).circuit =
      .seq (externallyControlledNormalizedMacroCircuit layout first).circuit
        (externallyControlledNormalizedMacroCircuit layout second).circuit := rfl

/-- Exact normalized PhaseShift lowering for a source Rz occurrence. -/
def externallyControlledPhaseShiftRzNormalizedMacroCircuit
    {qubits : Nat} (spec : PhaseShiftRzSpec qubits) :
    ControlledCircuitCompilerV2.NormalizedCircuit qubits :=
  phaseShiftRzNormalizedCircuit spec

theorem externallyControlledPhaseShiftRzNormalizedMacroCircuit_source_order
    {qubits : Nat} (spec : PhaseShiftRzSpec qubits) :
    (externallyControlledPhaseShiftRzNormalizedMacroCircuit spec).circuit =
      phaseShiftRzCircuit spec := rfl

theorem externallyControlledPhaseShiftRzNormalizedMacroCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : PhaseShiftRzSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (externallyControlledPhaseShiftRzNormalizedMacroCircuit spec).circuit =
      phaseShiftRzOperator symbolValue spec := by
  exact phaseShiftRzNormalizedCircuit_denote_eq symbolValue spec

/-- Exact normalized controlled-Ry lowering retained as one macro occurrence. -/
def externallyControlledControlledRyNormalizedMacroCircuit
    {qubits : Nat} (spec : ControlledRySpec qubits) :
    ControlledCircuitCompilerV2.NormalizedCircuit qubits :=
  controlledRyMacroNormalizedCircuit spec

theorem externallyControlledControlledRyNormalizedMacroCircuit_source_order
    {qubits : Nat} (spec : ControlledRySpec qubits) :
    (externallyControlledControlledRyNormalizedMacroCircuit spec).circuit =
      controlledRyMacroCircuit spec := rfl

theorem externallyControlledControlledRyNormalizedMacroCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : ControlledRySpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (externallyControlledControlledRyNormalizedMacroCircuit spec).circuit =
      controlledRyMacroOperator symbolValue spec := by
  exact controlledRyMacroNormalizedCircuit_denote_eq symbolValue spec

/-- Exact normalized controlled-Rz lowering retained as one macro occurrence. -/
def externallyControlledControlledRzNormalizedMacroCircuit
    {qubits : Nat} (spec : ControlledRzSpec qubits) :
    ControlledCircuitCompilerV2.NormalizedCircuit qubits :=
  controlledRzMacroNormalizedCircuit spec

theorem externallyControlledControlledRzNormalizedMacroCircuit_source_order
    {qubits : Nat} (spec : ControlledRzSpec qubits) :
    (externallyControlledControlledRzNormalizedMacroCircuit spec).circuit =
      controlledRzMacroCircuit spec := rfl

theorem externallyControlledControlledRzNormalizedMacroCircuit_denote_eq
    {qubits : Nat} (symbolValue : String → ℝ)
    (spec : ControlledRzSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (externallyControlledControlledRzNormalizedMacroCircuit spec).circuit =
      controlledRzMacroOperator symbolValue spec := by
  exact controlledRzMacroNormalizedCircuit_denote_eq symbolValue spec

end NormalizedMacro

end

end VerifiedCircuitCore

namespace VerifiedCircuitCore

noncomputable section

section NormalizedMacroEstablishedBridge

/-- Primitive-level normalized entry point paired with the V2 correctness API. -/
def externallyControlledNormalizedMacroPrimitiveCircuit
    {sourceQubits targetQubits : Nat}
    (layout : ControlledCircuitCompilerV2.ControlLayout
      sourceQubits targetQubits)
    (source : ControlledCircuitCompilerV2.NormalizedPrimitiveGate sourceQubits) :
    ControlledCircuitCompilerV2.NormalizedCircuit targetQubits :=
  ControlledCircuitCompilerV2.controlPrimitive layout source

theorem externallyControlledNormalizedMacroPrimitiveCircuit_normalized
    {sourceQubits targetQubits : Nat}
    (layout : ControlledCircuitCompilerV2.ControlLayout
      sourceQubits targetQubits)
    (source : ControlledCircuitCompilerV2.NormalizedPrimitiveGate sourceQubits) :
    ControlledCircuitCompilerV2.IsNormalizedCircuit
      (externallyControlledNormalizedMacroPrimitiveCircuit layout source).circuit :=
  (externallyControlledNormalizedMacroPrimitiveCircuit layout source).normalized

/-- Strict primitive correctness is the public V2 theorem, not a denotation
of the candidate circuit used as its own target. -/
theorem externallyControlledNormalizedMacroPrimitiveCircuit_denote_eq_v2
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlledCircuitCompilerV2.ControlLayout
      sourceQubits targetQubits)
    (source : ControlledCircuitCompilerV2.NormalizedPrimitiveGate sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (externallyControlledNormalizedMacroPrimitiveCircuit layout source).circuit =
      ControlledCircuitCompilerV2.controlPrimitiveTarget symbolValue layout source := by
  exact ControlledCircuitCompilerV2.controlPrimitive_normalized_correct
    symbolValue layout source

/-- The whole-circuit strict target is supplied by the V2 theorem.  The
existential presentation keeps the V2 private typed source core encapsulated
without defining a target by self-denotation. -/
theorem externallyControlledNormalizedMacroCircuit_strict_correct
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlledCircuitCompilerV2.ControlLayout
      sourceQubits targetQubits)
    (source : ControlledCircuitCompilerV2.NormalizedCircuit sourceQubits) :
    ∃ target : Operator (QubitBasis targetQubits),
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (externallyControlledNormalizedMacroCircuit layout source).circuit = target := by
  exact ⟨_, ControlledCircuitCompilerV2.controlCircuit_normalized_correct
    symbolValue layout source⟩

def externallyControlledNormalizedMacroCircuitOutputInverse
    {sourceQubits targetQubits : Nat}
    (layout : ControlledCircuitCompilerV2.ControlLayout
      sourceQubits targetQubits)
    (source : ControlledCircuitCompilerV2.NormalizedCircuit sourceQubits) :
    ControlledCircuitCompilerV2.NormalizedCircuit targetQubits :=
  ControlledCircuitCompilerV2.controlCircuitOutputInverse layout source

theorem externallyControlledNormalizedMacroCircuit_inverse_denote
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlledCircuitCompilerV2.ControlLayout
      sourceQubits targetQubits)
    (source : ControlledCircuitCompilerV2.NormalizedCircuit sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (externallyControlledNormalizedMacroCircuitOutputInverse layout source).circuit =
      star (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (externallyControlledNormalizedMacroCircuit layout source).circuit) := by
  exact ControlledCircuitCompilerV2.controlCircuit_reverse_denote
    symbolValue layout source

end NormalizedMacroEstablishedBridge

end

end VerifiedCircuitCore
