import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic
import QLean.Circuits.Foundation.ControlledHadamardAnalytic
import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.WireEmbeddingAnalytic
import QLean.Circuits.Foundation.ControlledRotationMacros

/-!
# Analytic plan for an externally controlled primitive stream

The plan and all targets in this module are independent of the implementation
AST.  A clean-work semantic refinement is deliberately separate from the
full-dirty strict compiler target.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Wire placement, external control, and work register for leaf-wise control. -/
structure ExternallyControlledCircuitLayout
    (sourceQubits targetQubits : Nat) where
  placement : Fin sourceQubits ↪ Fin targetQubits
  control : Fin targetQubits
  control_ne_placed : ∀ source, control ≠ placement source
  controlWork : List (Fin targetQubits)

/-- Two-work layout conditions required by the three-control decomposition. -/
structure ExternallyControlledCircuitLayout.CleanWorkValid
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) where
  work₀ : Fin targetQubits
  work₁ : Fin targetQubits
  controlWork_eq : layout.controlWork = [work₀, work₁]
  work₀_ne_control : work₀ ≠ layout.control
  work₁_ne_control : work₁ ≠ layout.control
  work₀_ne_work₁ : work₀ ≠ work₁
  work₀_ne_placed : ∀ source, work₀ ≠ layout.placement source
  work₁_ne_placed : ∀ source, work₁ ≠ layout.placement source

/-- Computational-basis predicate for the clean two-work input/output block. -/
def externallyControlledCleanWorkPredicate
    {sourceQubits targetQubits : Nat}
    {layout : ExternallyControlledCircuitLayout sourceQubits targetQubits}
    (valid : layout.CleanWorkValid) (basis : QubitBasis targetQubits) : Prop :=
  basis valid.work₀ = false ∧ basis valid.work₁ = false

/-- An XOR away from both compiler-work wires preserves their clean boundary.
Unlike `externallyControlledCleanWorkPredicate_xorPlaced`, this theorem does
not assume that the target belongs to the embedded source placement. -/
theorem externallyControlledCleanWorkPredicate_xorWire_of_ne
    {sourceQubits targetQubits : Nat}
    {layout : ExternallyControlledCircuitLayout sourceQubits targetQubits}
    (valid : layout.CleanWorkValid) (target : Fin targetQubits)
    (value : Bool) (input : QubitBasis targetQubits)
    (clean : externallyControlledCleanWorkPredicate valid input)
    (target_ne_work₀ : target ≠ valid.work₀)
    (target_ne_work₁ : target ≠ valid.work₁) :
    externallyControlledCleanWorkPredicate valid
      (xorWire target value input) := by
  constructor
  · simpa [xorWire, Ne.symm target_ne_work₀] using clean.1
  · simpa [xorWire, Ne.symm target_ne_work₁] using clean.2

/-- Mathematical positive-control lift of an arbitrary source operator.
When the external control is false it is the identity; when the control is
true it applies the source operator through `layout.placement` and preserves
every outside wire.  This definition is independent of the leaf compiler. -/
def externallyControlledWireLiftOperator
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (operator : Operator (QubitBasis sourceQubits)) :
    Operator (QubitBasis targetQubits) :=
  fun output input =>
    if input layout.control then
      wireLiftOperator layout.placement operator output input
    else if output = input then 1 else 0

theorem externallyControlledWireLiftOperator_apply
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (operator : Operator (QubitBasis sourceQubits))
    (output input : QubitBasis targetQubits) :
    externallyControlledWireLiftOperator layout operator output input =
      if input layout.control then
        wireLiftOperator layout.placement operator output input
      else if output = input then 1 else 0 := rfl

/-- The external control is read-only.  Consequently the mathematical
controlled lift can write only placed source wires; the control itself need
not be included in the write support. -/
theorem externallyControlledWireLiftOperator_preservesOutsidePlacement
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (operator : Operator (QubitBasis sourceQubits)) :
    OperatorPreservesOutside (Finset.univ.image layout.placement)
      (externallyControlledWireLiftOperator layout operator) := by
  intro output input nonzero wire outside
  by_cases control : input layout.control
  · rw [externallyControlledWireLiftOperator_apply, if_pos control] at nonzero
    exact wireLiftOperator_preservesOutsidePlacement
      layout.placement operator output input nonzero wire outside
  · rw [externallyControlledWireLiftOperator_apply, if_neg control] at nonzero
    split at nonzero
    · rename_i equal
      exact congrFun equal wire
    · exact False.elim (nonzero rfl)

/-- A wire lift has zero matrix entry between basis labels with different
external-control values, because that control lies outside the placement. -/
theorem wireLiftOperator_apply_eq_zero_of_control_ne
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (operator : Operator (QubitBasis sourceQubits))
    (output input : QubitBasis targetQubits)
    (different : output layout.control ≠ input layout.control) :
    wireLiftOperator layout.placement operator output input = 0 := by
  rw [wireLiftOperator_apply, if_neg, mul_zero]
  intro outsideEqual
  let controlOutside : OutsideWire layout.placement :=
    ⟨layout.control, fun source equal =>
      layout.control_ne_placed source equal.symm⟩
  exact different (congrFun outsideEqual controlOutside)

/-- The abstract controlled lift of the identity is the identity. -/
@[simp] theorem externallyControlledWireLiftOperator_one
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    externallyControlledWireLiftOperator layout
        (1 : Operator (QubitBasis sourceQubits)) =
      (1 : Operator (QubitBasis targetQubits)) := by
  ext output input
  by_cases control : input layout.control
  · simp [externallyControlledWireLiftOperator, control,
      wireLiftOperator_one]
  · rw [externallyControlledWireLiftOperator_apply, if_neg control]
    change (if output = input then 1 else 0) =
      (if output = input then 1 else 0)
    rfl

/-- Positive-control lifting preserves multiplication in source execution
order.  This is the structural bridge that permits a whole child component,
rather than each compiler leaf, to carry an asymmetric clean boundary. -/
theorem externallyControlledWireLiftOperator_mul
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (second first : Operator (QubitBasis sourceQubits)) :
    externallyControlledWireLiftOperator layout (second * first) =
      externallyControlledWireLiftOperator layout second *
        externallyControlledWireLiftOperator layout first := by
  classical
  ext output input
  by_cases inputControl : input layout.control
  · rw [externallyControlledWireLiftOperator_apply, if_pos inputControl,
      wireLiftOperator_mul, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro middle _
    by_cases middleControl : middle layout.control
    · simp [externallyControlledWireLiftOperator, inputControl, middleControl]
    · have controlDifferent : middle layout.control ≠ input layout.control := by
        simp [middleControl, inputControl]
      have zero := wireLiftOperator_apply_eq_zero_of_control_ne
        layout first middle input controlDifferent
      simp [externallyControlledWireLiftOperator, inputControl, middleControl,
        zero]
  · rw [externallyControlledWireLiftOperator_apply, if_neg inputControl,
      Matrix.mul_apply]
    rw [Finset.sum_eq_single input]
    · simp [externallyControlledWireLiftOperator, inputControl]
    · intro middle _ different
      simp [externallyControlledWireLiftOperator, inputControl, different]
    · simp

/-- Generic asymmetric basis-boundary transport through an external positive
control.  A false control uses `inputImpliesOutput`; a true control uses the
source matrix transition. -/
theorem externallyControlledWireLiftOperator_basisTransition
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (operator : Operator (QubitBasis sourceQubits))
    (inputPredicate outputPredicate : QubitBasis sourceQubits → Prop)
    (sourceMaps : ∀ input output,
      inputPredicate input → ¬ outputPredicate output →
        operator output input = 0)
    (inputImpliesOutput : ∀ input,
      inputPredicate input → outputPredicate input)
    (input output : QubitBasis targetQubits)
    (inputInside : inputPredicate
      (restrictToPlacedWires layout.placement input))
    (outputOutside : ¬ outputPredicate
      (restrictToPlacedWires layout.placement output)) :
    externallyControlledWireLiftOperator layout operator output input = 0 := by
  by_cases control : input layout.control
  · rw [externallyControlledWireLiftOperator_apply, if_pos control,
      wireLiftOperator_apply]
    rw [sourceMaps _ _ inputInside outputOutside, zero_mul]
  · rw [externallyControlledWireLiftOperator_apply, if_neg control]
    split
    · rename_i equal
      subst output
      exact False.elim (outputOutside (inputImpliesOutput _ inputInside))
    · rfl

/-- Deterministic source actions remain deterministic after external positive
control; the false branch is the identity basis action. -/
theorem externallyControlledWireLiftOperator_deterministic
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (action : QubitBasis sourceQubits → QubitBasis sourceQubits) :
    externallyControlledWireLiftOperator layout
        (deterministicOperator action) =
      deterministicOperator (fun input =>
        if input layout.control then
          liftBasisAction layout.placement action input
        else input) := by
  ext output input
  by_cases control : input layout.control <;>
    simp [externallyControlledWireLiftOperator, control,
      wireLiftOperator_deterministic, deterministicOperator]

/-- Input boundary for an externally controlled asymmetric source contract:
compiler work is clean and the placed source basis satisfies its input
predicate. -/
def externallyControlledPlacedInputPredicate
    {sourceQubits targetQubits : Nat}
    {layout : ExternallyControlledCircuitLayout sourceQubits targetQubits}
    (valid : layout.CleanWorkValid)
    (sourcePredicate : QubitBasis sourceQubits → Prop)
    (basis : QubitBasis targetQubits) : Prop :=
  externallyControlledCleanWorkPredicate valid basis ∧
    sourcePredicate (restrictToPlacedWires layout.placement basis)

/-- Output boundary paired with `externallyControlledPlacedInputPredicate`.
The source output predicate may be weaker than its input predicate. -/
def externallyControlledPlacedOutputPredicate
    {sourceQubits targetQubits : Nat}
    {layout : ExternallyControlledCircuitLayout sourceQubits targetQubits}
    (valid : layout.CleanWorkValid)
    (sourcePredicate : QubitBasis sourceQubits → Prop)
    (basis : QubitBasis targetQubits) : Prop :=
  externallyControlledCleanWorkPredicate valid basis ∧
    sourcePredicate (restrictToPlacedWires layout.placement basis)

/-- List-form characterization of the two clean compiler-work wires. -/
theorem externallyControlledCleanWorkPredicate_iff_controlWork_zero
    {sourceQubits targetQubits : Nat}
    {layout : ExternallyControlledCircuitLayout sourceQubits targetQubits}
    (valid : layout.CleanWorkValid) (basis : QubitBasis targetQubits) :
    externallyControlledCleanWorkPredicate valid basis ↔
      ∀ wire, wire ∈ layout.controlWork → basis wire = false := by
  rw [valid.controlWork_eq]
  simp [externallyControlledCleanWorkPredicate]

/-- Pure supported-leaf plan.  It intentionally excludes unsupported phase and
already-controlled constructors. -/
inductive ExternallyControlledPrimitivePlan (qubits : Nat) where
  | x (target : Fin qubits)
  | z (target : Fin qubits)
  | h (target : Fin qubits)
  | ry (angle : AngleExpr) (target : Fin qubits)
  | phaseShift (angle : AngleExpr) (target : Fin qubits)
  | rz (angle : AngleExpr) (target : Fin qubits)
  | cnot (control target : Fin qubits) (different : control ≠ target)
  | toffoli (control₀ control₁ target : Fin qubits)
      (controlsDifferent : control₀ ≠ control₁)
      (firstDifferent : control₀ ≠ target)
      (secondDifferent : control₁ ≠ target)

namespace ExternallyControlledPrimitivePlan

/-- Syntactic inverse of a supported source leaf.  Self-inverse classical and
Hadamard/Pauli leaves are unchanged; rotation angles are negated. -/
def inverse {qubits : Nat} :
    ExternallyControlledPrimitivePlan qubits →
      ExternallyControlledPrimitivePlan qubits
  | .x target => .x target
  | .z target => .z target
  | .h target => .h target
  | .ry angle target => .ry (.neg angle) target
  | .phaseShift angle target => .phaseShift (.neg angle) target
  | .rz angle target => .rz (.neg angle) target
  | .cnot control target different => .cnot control target different
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      .toffoli control₀ control₁ target controlsDifferent firstDifferent
        secondDifferent

/-- Inverse source order: reverse the stream and invert every leaf. -/
def inversePlan {qubits : Nat}
    (plan : List (ExternallyControlledPrimitivePlan qubits)) :
    List (ExternallyControlledPrimitivePlan qubits) :=
  plan.reverse.map inverse

/-- Direct three-positive-control XOR action, with no work-register change. -/
def tripleControlledXBasisAction {qubits : Nat}
    (control₀ control₁ control₂ target : Fin qubits)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire target
    (input control₀ && input control₁ && input control₂) input

/-- Direct independent operator of a three-positive-control XOR. -/
def tripleControlledXOperator {qubits : Nat}
    (control₀ control₁ control₂ target : Fin qubits) :
    Operator (QubitBasis qubits) :=
  deterministicOperator
    (tripleControlledXBasisAction control₀ control₁ control₂ target)

/-- With both work bits initially zero, the three-control decomposition
implements the direct triple-controlled XOR and restores both work bits. -/
theorem positiveMultiControlledX_three_reference_apply_of_cleanWork
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (valid : layout.CleanWorkValid)
    (control₀ control₁ target : Fin sourceQubits)
    (controlsDifferent : control₀ ≠ control₁)
    (firstDifferent : control₀ ≠ target)
    (secondDifferent : control₁ ≠ target)
    (input : QubitBasis targetQubits)
    (clean : externallyControlledCleanWorkPredicate valid input) :
    (ClassicalReversibleStage.positiveMultiControlledX
      [layout.control, layout.placement control₀, layout.placement control₁]
      layout.controlWork (layout.placement target)).reference input =
    tripleControlledXBasisAction layout.control (layout.placement control₀)
      (layout.placement control₁) (layout.placement target) input := by
  rcases clean with ⟨work₀Zero, work₁Zero⟩
  have control_ne_control₀ := layout.control_ne_placed control₀
  have control_ne_control₁ := layout.control_ne_placed control₁
  have control_ne_target := layout.control_ne_placed target
  have control₀_ne_control₁ :
      layout.placement control₀ ≠ layout.placement control₁ :=
    fun equal => controlsDifferent (layout.placement.injective equal)
  have control₀_ne_target :
      layout.placement control₀ ≠ layout.placement target :=
    fun equal => firstDifferent (layout.placement.injective equal)
  have control₁_ne_target :
      layout.placement control₁ ≠ layout.placement target :=
    fun equal => secondDifferent (layout.placement.injective equal)
  have control_ne_work₀ : layout.control ≠ valid.work₀ :=
    valid.work₀_ne_control.symm
  have control₀_ne_work₀ : layout.placement control₀ ≠ valid.work₀ :=
    (valid.work₀_ne_placed control₀).symm
  have control₁_ne_work₁ : layout.placement control₁ ≠ valid.work₁ :=
    (valid.work₁_ne_placed control₁).symm
  have control_ne_work₁ : layout.control ≠ valid.work₁ :=
    valid.work₁_ne_control.symm
  have control₀_ne_work₁ : layout.placement control₀ ≠ valid.work₁ :=
    (valid.work₁_ne_placed control₀).symm
  have control₁_ne_work₀ : layout.placement control₁ ≠ valid.work₀ :=
    (valid.work₀_ne_placed control₁).symm
  have target_ne_work₀ : layout.placement target ≠ valid.work₀ :=
    (valid.work₀_ne_placed target).symm
  have target_ne_work₁ : layout.placement target ≠ valid.work₁ :=
    (valid.work₁_ne_placed target).symm
  have work₁_ne_work₀ : valid.work₁ ≠ valid.work₀ :=
    valid.work₀_ne_work₁.symm
  rw [valid.controlWork_eq]
  simp [ClassicalReversibleStage.positiveMultiControlledX,
    ClassicalReversibleStage.andChainUse,
    ClassicalReversibleStage.safeXorControlled,
    ClassicalReversibleStage.safeXorDoublyControlled,
    ClassicalReversibleStage.reference,
    ClassicalReversibleInstruction.reference,
    ClassicalReversibleInstruction.basisAction,
    tripleControlledXBasisAction, work₀Zero, work₁Zero,
    control_ne_control₀, control_ne_target,
    control_ne_work₀, control_ne_work₁,
    control₀_ne_work₀, control₀_ne_work₁,
    control₁_ne_work₀, control₁_ne_work₁,
    target_ne_work₀, target_ne_work₁, work₁_ne_work₀,
    control₀_ne_target, control₁_ne_target,
    valid.work₀_ne_work₁, valid.work₀_ne_placed,
    valid.work₁_ne_placed, xorWire]
  funext wire
  by_cases wireTarget : wire = layout.placement target
  · subst wire
    simp [Function.update, target_ne_work₀, target_ne_work₁,
      Bool.and_assoc]
  · by_cases wireWork₀ : wire = valid.work₀
    · subst wire
      simp [Function.update, work₀Zero, wireTarget]
    · by_cases wireWork₁ : wire = valid.work₁
      · subst wire
        simp [Function.update, work₁Zero, wireTarget, wireWork₀]
      · simp [Function.update, wireTarget, wireWork₀, wireWork₁]

/-- Independent source-register operator of one plan leaf. -/
def sourceOperator {qubits : Nat} (symbolValue : String → ℝ) :
    ExternallyControlledPrimitivePlan qubits → Operator (QubitBasis qubits)
  | .x target => embedSingleQubitOperator target localX
  | .z target => embedSingleQubitOperator target localZ
  | .h target => embedSingleQubitOperator target localH
  | .ry angle target =>
      embedSingleQubitOperator target (localRy (angle.eval symbolValue))
  | .phaseShift angle target =>
      embedSingleQubitOperator target
        (localPhaseShift (angle.eval symbolValue))
  | .rz angle target =>
      embedSingleQubitOperator target (localRz (angle.eval symbolValue))
  | .cnot control target _ => reversibleAnalyticCnotOperator control target
  | .toffoli control₀ control₁ target _ _ _ =>
      analyticToffoliOperator control₀ control₁ target

/-- Full-dirty independent target of one compiled leaf.

For source Toffoli the target is the entire clean-compute/use/uncompute compiler
action on arbitrary work input; no clean-work refinement is claimed here.
-/
def strictOperator {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    ExternallyControlledPrimitivePlan sourceQubits →
      Operator (QubitBasis targetQubits)
  | .x target =>
      reversibleAnalyticCnotOperator layout.control (layout.placement target)
  | .z target => operatorSequence [
      embedSingleQubitOperator (layout.placement target) localH,
      reversibleAnalyticCnotOperator layout.control (layout.placement target),
      embedSingleQubitOperator (layout.placement target) localH]
  | .h target => controlledHadamardSpecialAngleOperator {
      control := layout.control
      target := layout.placement target
      different := layout.control_ne_placed target }
  | .ry angle target =>
      embedControlledSingleQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (localRy (angle.eval symbolValue))
  | .phaseShift angle target =>
      analyticControlledPhaseOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (angle.eval symbolValue)
  | .rz angle target =>
      embedControlledSingleQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (localRz (angle.eval symbolValue))
  | .cnot sourceControl target _ =>
      analyticToffoliOperator layout.control (layout.placement sourceControl)
        (layout.placement target)
  | .toffoli control₀ control₁ target _ _ _ =>
      (ClassicalReversibleStage.positiveMultiControlledX
        [layout.control, layout.placement control₀, layout.placement control₁]
        layout.controlWork (layout.placement target)).analyticOperator

/-- Desired work-preserving controlled semantic target of one plan leaf. -/
def semanticOperator {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    ExternallyControlledPrimitivePlan sourceQubits →
      Operator (QubitBasis targetQubits)
  | .x target =>
      reversibleAnalyticCnotOperator layout.control (layout.placement target)
  | .z target =>
      embedControlledSingleQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target) localZ
  | .h target => controlledHadamardSpecialAngleOperator {
      control := layout.control
      target := layout.placement target
      different := layout.control_ne_placed target }
  | .ry angle target =>
      embedControlledSingleQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (localRy (angle.eval symbolValue))
  | .phaseShift angle target =>
      analyticControlledPhaseOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (angle.eval symbolValue)
  | .rz angle target =>
      embedControlledSingleQubitOperator layout.control
        (layout.placement target) (layout.control_ne_placed target)
        (localRz (angle.eval symbolValue))
  | .cnot sourceControl target _ =>
      analyticToffoliOperator layout.control (layout.placement sourceControl)
        (layout.placement target)
  | .toffoli control₀ control₁ target _ _ _ =>
      tripleControlledXOperator layout.control (layout.placement control₀)
        (layout.placement control₁) (layout.placement target)

/-- Source plan operator in execution order. -/
def sourcePlanOperator {qubits : Nat} (symbolValue : String → ℝ)
    (plan : List (ExternallyControlledPrimitivePlan qubits)) :
    Operator (QubitBasis qubits) :=
  operatorSequence (plan.map (sourceOperator symbolValue))

/-- Full-dirty compiled plan target in execution order. -/
def strictPlanOperator {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    Operator (QubitBasis targetQubits) :=
  operatorSequence (plan.map (strictOperator symbolValue layout))

/-- Desired work-preserving controlled plan target in execution order. -/
def semanticPlanOperator {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    Operator (QubitBasis targetQubits) :=
  operatorSequence (plan.map (semanticOperator symbolValue layout))

end ExternallyControlledPrimitivePlan

end

end VerifiedCircuitCore

namespace VerifiedCircuitCore

noncomputable section

section NormalizedMacro

/-- Independent target for a normalized macro consumer.  Rotation branches are
spelled with the completed macro operators; all other branches retain the
existing independent semantic target. -/
def externallyControlledNormalizedMacroOperator
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    ExternallyControlledPrimitivePlan sourceQubits →
      Operator (QubitBasis targetQubits)
  | .ry angle target =>
      controlledRyMacroOperator symbolValue {
        angle := angle
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }
  | .rz angle target =>
      controlledRzMacroOperator symbolValue {
        angle := angle
        control := layout.control
        target := layout.placement target
        different := layout.control_ne_placed target }
  | plan => ExternallyControlledPrimitivePlan.semanticOperator
      symbolValue layout plan

theorem externallyControlledNormalizedMacroOperator_eq_semanticOperator
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : ExternallyControlledPrimitivePlan sourceQubits) :
    externallyControlledNormalizedMacroOperator symbolValue layout plan =
      ExternallyControlledPrimitivePlan.semanticOperator
        symbolValue layout plan := by
  cases plan <;> rfl

/-- Source-order composition of the normalized independent leaf targets. -/
def externallyControlledNormalizedMacroPlanOperator
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    Operator (QubitBasis targetQubits) :=
  operatorSequence (plan.map
    (externallyControlledNormalizedMacroOperator symbolValue layout))

theorem externallyControlledNormalizedMacroPlanOperator_eq_semanticPlanOperator
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    externallyControlledNormalizedMacroPlanOperator symbolValue layout plan =
      ExternallyControlledPrimitivePlan.semanticPlanOperator
        symbolValue layout plan := by
  induction plan with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      change operatorSequence (rest.map
          (externallyControlledNormalizedMacroOperator symbolValue layout)) *
          externallyControlledNormalizedMacroOperator symbolValue layout first =
        operatorSequence (rest.map
          (ExternallyControlledPrimitivePlan.semanticOperator symbolValue layout)) *
          ExternallyControlledPrimitivePlan.semanticOperator symbolValue layout first
      change operatorSequence (rest.map
          (externallyControlledNormalizedMacroOperator symbolValue layout)) =
        operatorSequence (rest.map
          (ExternallyControlledPrimitivePlan.semanticOperator symbolValue layout))
        at inductionHypothesis
      rw [inductionHypothesis]
      rw [externallyControlledNormalizedMacroOperator_eq_semanticOperator]

end NormalizedMacro

end

end VerifiedCircuitCore
