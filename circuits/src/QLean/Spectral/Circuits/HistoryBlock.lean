import QLean.Spectral.Analysis.HistoryBlock
import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.ControlledCircuitCompiler
import QLean.Circuits.Foundation.ControlledConstantAdder
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.ReversibleLogic
import QLean.Circuits.Foundation.ConstructionMultiControlledRotationCorrectness
import QLean.Circuits.Foundation.ShuklaVedulaUniformCorrectness
import QLean.Circuits.Foundation.ControlledRotationMacros
import QLean.Circuits.Foundation.NormalizedControlProofBridge

/-!
# P05 history block のcontract合成境界

P14/P15/P16の公開Exact contractと各pure targetとの同定だけを受け取り、
一般`ExactOperatorComponent.sequence`一則でP05 parentを構成する。
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

/-- P14のsymbolic five-gate source順。recorded角度値はparameter側から受け取る。 -/
def historySelectorPreparationGates {qubits : Nat}
    (parameters : HistorySelectorPreparationParameters qubits) :
    List (PrimitiveGate qubits) := [
  .ry parameters.firstHighAngle parameters.high,
  .ry parameters.firstLowAngle parameters.low,
  .cnot parameters.high parameters.low parameters.different,
  .ry parameters.secondLowAngle parameters.low,
  .cnot parameters.high parameters.low parameters.different]

/-- P14のLean-owned symbolic AST。外部gate streamとの一致は別certificate境界とする。 -/
def historySelectorPreparationCircuit {qubits : Nat}
    (parameters : HistorySelectorPreparationParameters qubits) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence ((historySelectorPreparationGates parameters).map Circuit.gate)

/-- P14 symbolic ASTは回路非依存な5段作用素積に一致する。 -/
theorem historySelectorPreparationCircuit_correct {qubits : Nat}
    (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (historySelectorPreparationCircuit parameters) =
      historySelectorPreparationOperator symbolValue parameters := by
  rw [historySelectorPreparationCircuit, denote_gate_sequence_eq_operatorSequence]
  rfl

/-- H1 changes only the two selector wires. -/
theorem historySelectorPreparationOperator_preservesOutside {qubits : Nat}
    (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    OperatorPreservesOutside (historySelectorPreparationSupport parameters)
      (historySelectorPreparationOperator symbolValue parameters) := by
  unfold historySelectorPreparationOperator
  apply OperatorPreservesOutside.operatorSequence_of_forall
  intro operator member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h
  · subst operator
    exact OperatorPreservesOutside.mono
      (OperatorPreservesOutside.embedSingleQubitOperator parameters.high _)
      (by simp [historySelectorPreparationSupport])
  · subst operator
    exact OperatorPreservesOutside.mono
      (OperatorPreservesOutside.embedSingleQubitOperator parameters.low _)
      (by simp [historySelectorPreparationSupport])
  · subst operator
    exact OperatorPreservesOutside.mono
      (OperatorPreservesOutside.deterministicXorWire parameters.low
        (fun input => input parameters.high))
      (by simp [historySelectorPreparationSupport])
  · subst operator
    exact OperatorPreservesOutside.mono
      (OperatorPreservesOutside.embedSingleQubitOperator parameters.low _)
      (by simp [historySelectorPreparationSupport])
  · subst operator
    exact OperatorPreservesOutside.mono
      (OperatorPreservesOutside.deterministicXorWire parameters.low
        (fun input => input parameters.high))
      (by simp [historySelectorPreparationSupport])

/-- One verified P50 rotation-emitter occurrence used by P14.  The concrete
P50 adapters will instantiate this interface from shared primitive Exact
components; P14 itself only consumes their public `.correct` contracts. -/
structure VerifiedHistorySelectorRotationChild
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) where
  analyticTarget : Operator basis
  component : ExactOperatorComponent gateOperator
  target_eq : component.target = analyticTarget

/-- The two actual P50 occurrences in the frozen two-wire selector emitter:
one zero-control Ry and one one-control source decomposition. -/
structure VerifiedHistorySelectorPreparationP50Children
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) where
  highRotation : VerifiedHistorySelectorRotationChild
    (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue)
  lowControlledRotation : VerifiedHistorySelectorRotationChild
    (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue)
  highTarget_eq : highRotation.analyticTarget =
    historySelectorHighRotationOperator symbolValue parameters
  lowTarget_eq : lowControlledRotation.analyticTarget =
    historySelectorLowControlledRotationRecordedOperator symbolValue parameters

private noncomputable def historyPrimitiveGateExactComponent
    {qubits : Nat} (symbolValue : String → ℝ) (gate : PrimitiveGate qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := .gate gate
  target := primitiveGateOperatorWithSymbols symbolValue gate
  correct := rfl

@[simp] private theorem historyPrimitiveGateExactComponent_circuit
    {qubits : Nat} (symbolValue : String → ℝ) (gate : PrimitiveGate qubits) :
    (historyPrimitiveGateExactComponent symbolValue gate).circuit = .gate gate :=
  rfl

/-- First concrete P50 occurrence: a zero-control Ry represented by the shared
single-gate Exact constructor and refined to the independent selector target. -/
noncomputable def historySelectorHighRotationP50ExactComponent
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  ExactOperatorComponent.refineTarget
    (historyPrimitiveGateExactComponent symbolValue
      (.ry parameters.firstHighAngle parameters.high))
    (historySelectorHighRotationOperator symbolValue parameters)
    (by rfl)

@[simp] theorem historySelectorHighRotationP50ExactComponent_circuit
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    (historySelectorHighRotationP50ExactComponent
      symbolValue parameters).circuit =
      .gate (.ry parameters.firstHighAngle parameters.high) := by
  exact (ExactOperatorComponent.refineTarget_circuit _ _ _).trans
    (historyPrimitiveGateExactComponent_circuit _ _)

/-- Strict source-order implementation of the one-control P50 occurrence.
The two CNOTs remain actual primitive children; the recorded half angles are
not silently replaced by an ideal exact-angle relation. -/
noncomputable def compiledHistorySelectorLowControlledRotationP50ExactComponent
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :=
  ExactOperatorComponent.sequence [
    historyPrimitiveGateExactComponent symbolValue
      (.ry parameters.firstLowAngle parameters.low),
    historyPrimitiveGateExactComponent symbolValue
      (.cnot parameters.high parameters.low parameters.different),
    historyPrimitiveGateExactComponent symbolValue
      (.ry parameters.secondLowAngle parameters.low),
    historyPrimitiveGateExactComponent symbolValue
      (.cnot parameters.high parameters.low parameters.different)]

theorem compiledHistorySelectorLowControlledRotationP50Target_eq
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    (compiledHistorySelectorLowControlledRotationP50ExactComponent
      symbolValue parameters).target =
      historySelectorLowControlledRotationRecordedOperator
        symbolValue parameters := by
  rw [compiledHistorySelectorLowControlledRotationP50ExactComponent,
    ExactOperatorComponent.sequence_target_eq_operatorSequence]
  rfl

noncomputable def historySelectorLowControlledRotationP50ExactComponent
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  ExactOperatorComponent.refineTarget
    (compiledHistorySelectorLowControlledRotationP50ExactComponent
      symbolValue parameters)
    (historySelectorLowControlledRotationRecordedOperator
      symbolValue parameters)
    (compiledHistorySelectorLowControlledRotationP50Target_eq
      symbolValue parameters)

@[simp] theorem historySelectorLowControlledRotationP50ExactComponent_circuit
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    (historySelectorLowControlledRotationP50ExactComponent
      symbolValue parameters).circuit =
      (compiledHistorySelectorLowControlledRotationP50ExactComponent
        symbolValue parameters).circuit :=
  ExactOperatorComponent.refineTarget_circuit _ _ _

/-- Concrete P50 children at the frozen P14 placement. -/
noncomputable def historySelectorPreparationConcreteP50Children
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    VerifiedHistorySelectorPreparationP50Children symbolValue parameters where
  highRotation := {
    analyticTarget := historySelectorHighRotationOperator symbolValue parameters
    component := historySelectorHighRotationP50ExactComponent
      symbolValue parameters
    target_eq := ExactOperatorComponent.refineTarget_target _ _ _ }
  lowControlledRotation := {
    analyticTarget := historySelectorLowControlledRotationRecordedOperator
      symbolValue parameters
    component := historySelectorLowControlledRotationP50ExactComponent
      symbolValue parameters
    target_eq := ExactOperatorComponent.refineTarget_target _ _ _ }
  highTarget_eq := rfl
  lowTarget_eq := rfl

/-- The P14 source-order compiler expressed only through its two P50 child
components. -/
noncomputable def compiledHistorySelectorPreparationFromP50ExactComponent
    {qubits : Nat} {symbolValue : String → ℝ}
    {parameters : HistorySelectorPreparationParameters qubits}
    (children : VerifiedHistorySelectorPreparationP50Children
      symbolValue parameters) :=
  ExactOperatorComponent.sequence [
    children.highRotation.component,
    children.lowControlledRotation.component]

theorem compiledHistorySelectorPreparationFromP50Target_eq
    {qubits : Nat} {symbolValue : String → ℝ}
    {parameters : HistorySelectorPreparationParameters qubits}
    (children : VerifiedHistorySelectorPreparationP50Children
      symbolValue parameters) :
    (compiledHistorySelectorPreparationFromP50ExactComponent children).target =
      historySelectorPreparationOperator symbolValue parameters := by
  rw [compiledHistorySelectorPreparationFromP50ExactComponent,
    ExactOperatorComponent.sequence_target_eq_operatorSequence]
  simp only [List.map_cons, List.map_nil]
  rw [children.highRotation.target_eq, children.lowControlledRotation.target_eq,
    children.highTarget_eq, children.lowTarget_eq]
  exact (historySelectorPreparationOperator_eq_rotationChildren
    symbolValue parameters).symm

/-- P14 parent whose correctness uses the two P50 children and one generic
target-refinement rule.  This is intentionally not catalogued until the
shared primitive P50 adapters instantiate `children`. -/
noncomputable def historySelectorPreparationFromP50ExactComponent
    {qubits : Nat} {symbolValue : String → ℝ}
    {parameters : HistorySelectorPreparationParameters qubits}
    (children : VerifiedHistorySelectorPreparationP50Children
      symbolValue parameters) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  ExactOperatorComponent.refineTarget
    (compiledHistorySelectorPreparationFromP50ExactComponent children)
    (historySelectorPreparationOperator symbolValue parameters)
    (compiledHistorySelectorPreparationFromP50Target_eq children)

@[simp] theorem historySelectorPreparationFromP50ExactComponent_circuit
    {qubits : Nat} {symbolValue : String → ℝ}
    {parameters : HistorySelectorPreparationParameters qubits}
    (children : VerifiedHistorySelectorPreparationP50Children
      symbolValue parameters) :
    (historySelectorPreparationFromP50ExactComponent children).circuit =
      (compiledHistorySelectorPreparationFromP50ExactComponent children).circuit :=
  ExactOperatorComponent.refineTarget_circuit _ _ _

/-- Concrete P14 implementation assembled from the two public P50 instances. -/
noncomputable def historySelectorPreparationP50ComposedExactComponent
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  historySelectorPreparationFromP50ExactComponent
    (historySelectorPreparationConcreteP50Children symbolValue parameters)

noncomputable def historySelectorPreparationFromP50InverseExactComponent
    {qubits : Nat} {symbolValue : String → ℝ}
    {parameters : HistorySelectorPreparationParameters qubits}
    (children : VerifiedHistorySelectorPreparationP50Children
      symbolValue parameters) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  ExactOperatorComponent.reverse
    (gateOperator := primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue)
    PrimitiveGate.inverse
    (primitiveGateOperator_inverse (qubits := qubits) symbolValue)
    (historySelectorPreparationFromP50ExactComponent children)

@[simp] theorem historySelectorPreparationFromP50InverseExactComponent_target
    {qubits : Nat} {symbolValue : String → ℝ}
    {parameters : HistorySelectorPreparationParameters qubits}
    (children : VerifiedHistorySelectorPreparationP50Children
      symbolValue parameters) :
    (historySelectorPreparationFromP50InverseExactComponent children).target =
      historySelectorPreparationInverseOperator symbolValue parameters := rfl

/-- P16 固有 constant comparison の3子 full-dirty Exact implementation。 -/
noncomputable def historyLessThanConstantExactComponent {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat) :=
  ExactOperatorComponent.sequence [
    ClassicalReversibleStage.xorConstantExactComponent symbolValue
      (List.ofFn spec.rhs.wire) constant,
    unsignedLessThanXorExactComponent symbolValue spec,
    ClassicalReversibleStage.xorConstantExactComponent symbolValue
      (List.ofFn spec.rhs.wire) constant]

/-- P16 constant comparison compiler target は独立 dirty target と一致する。 -/
theorem historyLessThanConstantExactComponent_target {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat) :
    (historyLessThanConstantExactComponent symbolValue spec constant).target =
      historyLessThanConstantOperator spec constant := by
  have xorTarget :
      (ClassicalReversibleStage.xorConstantExactComponent symbolValue
        (List.ofFn spec.rhs.wire) constant).target =
      (ClassicalReversibleStage.xorConstant
        (List.ofFn spec.rhs.wire) constant).analyticOperator :=
    ClassicalReversibleStage.primitiveExactOperatorComponent_target
      symbolValue
      (ClassicalReversibleStage.xorConstant
        (List.ofFn spec.rhs.wire) constant)
  have lessTarget :
      (unsignedLessThanXorExactComponent symbolValue spec).target =
        unsignedLessThanXorDirtyOperator spec := by
    rfl
  unfold historyLessThanConstantExactComponent
  rw [ExactOperatorComponent.sequence_target_eq_operatorSequence]
  simp only [List.map_cons, List.map_nil]
  rw [xorTarget, lessTarget]
  rfl

set_option maxHeartbeats 800000 in

/-- Frozen four-gate controlled-Ry leaf used for the P16 idle coefficient. -/
noncomputable def historyClockCoefficientRotationExactComponent
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) (fun _ => 0)) where
  circuit := Circuit.controlledRyMacroExpansion control target different angle
  target := embedControlledSingleQubitOperator control target different
    (localRy angle.uniformValue)
  correct := Circuit.controlledRyMacroExpansion_operator
    control target different angle

/-- Active P50 consumer component routed through the normalized macro surface. -/
noncomputable def historyClockCoefficientRotationNormalizedStageComponent
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) (fun _ => 0)) where
  circuit := controlledRyMacroCircuit {
    angle := angle, control := control, target := target, different := different }
  target := embedControlledSingleQubitOperator control target different
    (localRy angle.uniformValue)
  correct := NormalizedControlProofBridge.controlledRyMacro_zero_strict_target
    control target different angle

set_option maxHeartbeats 800000 in

/-- One primitive CNOT exposed as an Exact semantic child. -/
noncomputable def historyCnotExactComponent {qubits : Nat}
    (symbolValue : String → ℝ) (control target : Fin qubits)
    (different : control ≠ target) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := .gate (.cnot control target different)
  target := reversibleAnalyticCnotOperator control target
  correct := rfl

/-- Wire inequalities required by the source-faithful I03 primitive stream. -/
structure HistoryIdleTransformEvidence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  idleEnd_ne_idle :
    historyLessThanIdleEndWire layout ≠ historyIdleFlag layout
  time_ne_idle :
    historyLessThanTimeWire layout ≠ historyIdleFlag layout
  active_ne_order : ∀ target ∈ historyRegisterWires layout.order,
    historyActiveWire layout ≠ target
  active_ne_coefficient :
    historyActiveWire layout ≠ layout.coefficientSignal

/-- Wire inequalities required by the two projector-target CNOTs in I06. -/
structure HistoryProjectorControlEvidence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  branch_ne_projector : historyBranchWire layout ≠ layout.projectorSignal
  coefficientControl_ne_projector :
    historyCoefficientControl layout ≠ layout.projectorSignal

/-- I06 full-dirty compute/use/uncompute implementation in frozen source order. -/
noncomputable def historyProjectorControlExactComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryProjectorControlEvidence layout) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  let branchToggle := historyCnotExactComponent symbolValue
    (historyBranchWire layout) layout.projectorSignal
    evidence.branch_ne_projector
  let degreeZeroEquality :=
    ClassicalReversibleStage.xorEqualityToConstantMinimumWorkExactComponent
      symbolValue
      (historyRegisterWires layout.order)
      (historyRegisterWires (historyEqualityWork layout)) 0
      (historyEqualityFlag layout)
  let projectorConjunction :=
    ClassicalReversibleStage.xorConjunctionMinimumWorkExactComponent symbolValue
      [historyBranchWire layout, historyEqualityFlag layout] []
      (historyCoefficientControl layout)
  let projectorToggle := historyCnotExactComponent symbolValue
    (historyCoefficientControl layout) layout.projectorSignal
    evidence.coefficientControl_ne_projector
  ExactOperatorComponent.sequence [branchToggle, degreeZeroEquality,
    projectorConjunction, projectorToggle, projectorConjunction,
    degreeZeroEquality]

theorem historyProjectorControlExactComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryProjectorControlEvidence layout) :
    (historyProjectorControlExactComponent symbolValue layout evidence).target =
      historyProjectorControlOperator layout := by
  let equalityStage :=
    ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
      (historyRegisterWires layout.order)
      (historyRegisterWires (historyEqualityWork layout)) 0
      (historyEqualityFlag layout)
  let conjunctionStage :=
    ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
    [historyBranchWire layout, historyEqualityFlag layout] []
    (historyCoefficientControl layout)
  have equalityTarget :
      (ClassicalReversibleStage.xorEqualityToConstantMinimumWorkExactComponent
        symbolValue
        (historyRegisterWires layout.order)
        (historyRegisterWires (historyEqualityWork layout)) 0
        (historyEqualityFlag layout)).target = equalityStage.analyticOperator :=
    ClassicalReversibleStage.primitiveExactOperatorComponent_target
      symbolValue equalityStage
  have conjunctionTarget :
      (ClassicalReversibleStage.xorConjunctionMinimumWorkExactComponent symbolValue
        [historyBranchWire layout, historyEqualityFlag layout] []
        (historyCoefficientControl layout)).target =
          conjunctionStage.analyticOperator :=
    ClassicalReversibleStage.primitiveExactOperatorComponent_target
      symbolValue conjunctionStage
  unfold historyProjectorControlExactComponent
  rw [ExactOperatorComponent.sequence_target_eq_operatorSequence]
  simp only [List.map_cons, List.map_nil]
  rw [equalityTarget, conjunctionTarget]
  unfold historyProjectorControlOperator
  rfl

/-- Disjointness evidence needed to place the frozen P24 order-register
subcircuit under the P16 `active` control.  The two compiler work wires are
the source-allocated `uniform_control_work` pair; they are not hidden in the
source circuit. -/
structure HistoryOrderUniformExternalControlEvidence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  active_ne_order : ∀ source,
    historyActiveWire layout ≠ layout.order.wire source
  work₀_ne_active :
    (historyUniformControlWork layout).wire 0 ≠ historyActiveWire layout
  work₁_ne_active :
    (historyUniformControlWork layout).wire 1 ≠ historyActiveWire layout
  work₀_ne_order : ∀ source,
    (historyUniformControlWork layout).wire 0 ≠ layout.order.wire source
  work₁_ne_order : ∀ source,
    (historyUniformControlWork layout).wire 1 ≠ layout.order.wire source

/-- Frozen P24 call parameters: Python invokes the width-only uniform
preparation with `validCount = taylor_order + 1` on the existing order width. -/
def historyOrderUniformPreparationParameters
    (parameters : HistoryBlockParameters) : UniformPreparationParameters where
  width := historyOrderWidth parameters.taylorOrder
  validCount := parameters.taylorOrder + 1
  validCountPositive := by omega
  validCountLeCapacity := by
    unfold historyOrderWidth
    have strict : parameters.taylorOrder <
        2 ^ (Nat.log2 parameters.taylorOrder + 1) := by
      rw [← Nat.log2_lt (Nat.ne_of_gt parameters.taylorOrderPositive)]
      omega
    have exponentLe : Nat.log2 parameters.taylorOrder + 1 ≤
        max 1 (Nat.log2 parameters.taylorOrder + 1) :=
      Nat.le_max_right _ _
    exact Nat.le_trans strict
      (Nat.pow_le_pow_right (by omega) exponentLe)

/-- Frozen P16 placement of the P24 source register, external control, and
the two clean decomposition-work wires. -/
def historyOrderUniformExternalControlLayout
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout) :
    ExternallyControlledCircuitLayout
      (historyOrderWidth parameters.taylorOrder) qubits where
  placement := ⟨layout.order.wire, layout.order.injective⟩
  control := historyActiveWire layout
  control_ne_placed := evidence.active_ne_order
  controlWork := historyRegisterWires (historyUniformControlWork layout)

/-- The P16 allocation supplies exactly two clean work wires for the generic
external-control compiler. -/
def historyOrderUniformExternalControlCleanWorkValid
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout) :
    (historyOrderUniformExternalControlLayout layout evidence).CleanWorkValid where
  work₀ := (historyUniformControlWork layout).wire 0
  work₁ := (historyUniformControlWork layout).wire 1
  controlWork_eq := by
    simp [historyOrderUniformExternalControlLayout, historyRegisterWires]
  work₀_ne_control := evidence.work₀_ne_active
  work₁_ne_control := evidence.work₁_ne_active
  work₀_ne_work₁ := by
    intro equal
    have indexEqual := (historyUniformControlWork layout).injective equal
    exact Fin.zero_ne_one indexEqual
  work₀_ne_placed := evidence.work₀_ne_order
  work₁_ne_placed := evidence.work₁_ne_order

/-- P24 inverse after source-order decoding.  The input list is explicitly the
already reversed-and-inverted frozen primitive plan; no Python stream is
inferred from a manifest label. -/
noncomputable def historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout)
    (inversePlan : List (ExternallyControlledPrimitivePlan
      (historyOrderWidth parameters.taylorOrder))) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  externallyControlledCleanSubspaceMapComponent symbolValue
    (historyOrderUniformExternalControlLayout layout evidence)
    (historyOrderUniformExternalControlCleanWorkValid layout evidence)
    inversePlan

/-- P24 clean input and output are the same coherent span generated by basis
states with both decomposition-work bits zero. -/
theorem historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout)
    (inversePlan : List (ExternallyControlledPrimitivePlan
      (historyOrderWidth parameters.taylorOrder))) :
    (historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent
        symbolValue layout evidence inversePlan).inputSubspace =
        SubspaceMapComponent.basisSpan (externallyControlledCleanWorkPredicate
          (historyOrderUniformExternalControlCleanWorkValid layout evidence)) ∧
      (historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent
          symbolValue layout evidence inversePlan).outputSubspace =
        SubspaceMapComponent.basisSpan (externallyControlledCleanWorkPredicate
          (historyOrderUniformExternalControlCleanWorkValid layout evidence)) := by
  constructor
  · cases inversePlan <;> rfl
  · induction inversePlan with
    | nil => rfl
    | cons first rest inductionHypothesis =>
        change
          (historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent
            symbolValue layout evidence rest).outputSubspace = _
        exact inductionHypothesis

/-- P24 clean target is the independent semantic source-order product. -/
theorem historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout)
    (inversePlan : List (ExternallyControlledPrimitivePlan
      (historyOrderWidth parameters.taylorOrder))) :
    (historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent
        symbolValue layout evidence inversePlan).target =
      ExternallyControlledPrimitivePlan.semanticPlanOperator symbolValue
        (historyOrderUniformExternalControlLayout layout evidence) inversePlan := by
  exact externallyControlledCleanSubspaceMapComponent_target
    symbolValue (historyOrderUniformExternalControlLayout layout evidence)
    (historyOrderUniformExternalControlCleanWorkValid layout evidence) inversePlan

/-- P24 clean component preserves the frozen reverse source order in its AST. -/
theorem historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout)
    (inversePlan : List (ExternallyControlledPrimitivePlan
      (historyOrderWidth parameters.taylorOrder))) :
    (historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent
        symbolValue layout evidence inversePlan).circuit =
      Circuit.sequence (inversePlan.map fun leaf =>
        leaf.compile (historyOrderUniformExternalControlLayout layout evidence)) := by
  exact externallyControlledCleanSubspaceMapComponent_circuit
    symbolValue (historyOrderUniformExternalControlLayout layout evidence)
    (historyOrderUniformExternalControlCleanWorkValid layout evidence) inversePlan

/-- Concrete P24 child obtained by decoding the frozen width-only Shukla--Vedula
AST and using its reverse/inverted primitive plan. -/
noncomputable def historyOrderUniformPreparationInverseCleanSubspaceMapComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  shuklaVedulaWidthOnlyUniformInverseExternallyControlledCleanSubspaceMapComponent
    symbolValue (historyOrderUniformPreparationParameters parameters)
      (historyOrderUniformExternalControlLayout layout evidence)
      (historyOrderUniformExternalControlCleanWorkValid layout evidence)

/-- Concrete P24 input/output spaces are the clean external-control work span. -/
theorem historyOrderUniformPreparationInverseCleanSubspaceMapComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout) :
    (historyOrderUniformPreparationInverseCleanSubspaceMapComponent
        symbolValue layout evidence).inputSubspace =
        SubspaceMapComponent.basisSpan (externallyControlledCleanWorkPredicate
          (historyOrderUniformExternalControlCleanWorkValid layout evidence)) ∧
      (historyOrderUniformPreparationInverseCleanSubspaceMapComponent
          symbolValue layout evidence).outputSubspace =
        SubspaceMapComponent.basisSpan (externallyControlledCleanWorkPredicate
          (historyOrderUniformExternalControlCleanWorkValid layout evidence)) := by
  unfold historyOrderUniformPreparationInverseCleanSubspaceMapComponent
    shuklaVedulaWidthOnlyUniformInverseExternallyControlledCleanSubspaceMapComponent
  exact historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent_spaces
    symbolValue layout evidence
      (shuklaVedulaWidthOnlyUniformInversePlan
        (historyOrderUniformPreparationParameters parameters))

/-- Concrete P24 target is the independent semantic product of the decoded
reverse source plan. -/
theorem historyOrderUniformPreparationInverseCleanSubspaceMapComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout) :
    (historyOrderUniformPreparationInverseCleanSubspaceMapComponent
        symbolValue layout evidence).target =
      ExternallyControlledPrimitivePlan.semanticPlanOperator symbolValue
        (historyOrderUniformExternalControlLayout layout evidence)
        (shuklaVedulaWidthOnlyUniformInversePlan
          (historyOrderUniformPreparationParameters parameters)) := by
  unfold historyOrderUniformPreparationInverseCleanSubspaceMapComponent
    shuklaVedulaWidthOnlyUniformInverseExternallyControlledCleanSubspaceMapComponent
  exact historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent_target
    symbolValue layout evidence
      (shuklaVedulaWidthOnlyUniformInversePlan
        (historyOrderUniformPreparationParameters parameters))

/-- Concrete P24 circuit preserves the decoded frozen reverse source order. -/
theorem historyOrderUniformPreparationInverseCleanSubspaceMapComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout) :
    (historyOrderUniformPreparationInverseCleanSubspaceMapComponent
        symbolValue layout evidence).circuit =
      Circuit.sequence
        ((shuklaVedulaWidthOnlyUniformInversePlan
          (historyOrderUniformPreparationParameters parameters)).map fun leaf =>
            leaf.compile
              (historyOrderUniformExternalControlLayout layout evidence)) := by
  unfold historyOrderUniformPreparationInverseCleanSubspaceMapComponent
    shuklaVedulaWidthOnlyUniformInverseExternallyControlledCleanSubspaceMapComponent
  exact historyOrderUniformPreparationInversePlanCleanSubspaceMapComponent_circuit
    symbolValue layout evidence
      (shuklaVedulaWidthOnlyUniformInversePlan
        (historyOrderUniformPreparationParameters parameters))

/-- Full-dirty I02 compiler contract.  This is kept separate from the desired
clean inverse semantics below: its independent target is the strict product of
the externally-controlled primitive compiler targets. -/
noncomputable def historyOrderUniformPreparationInverseExactComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) (fun _ => 0)) :=
  (externallyControlledStrictUnitaryExactOperatorComponent
    (fun _ => 0)
    (historyOrderUniformExternalControlLayout layout evidence)
    (shuklaVedulaWidthOnlyUniformInversePlan
      (historyOrderUniformPreparationParameters parameters))).toExact

theorem historyOrderUniformPreparationInverseExactComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout) :
    (historyOrderUniformPreparationInverseExactComponent
      layout evidence).target =
      ExternallyControlledPrimitivePlan.strictPlanOperator (fun _ => 0)
        (historyOrderUniformExternalControlLayout layout evidence)
        (shuklaVedulaWidthOnlyUniformInversePlan
          (historyOrderUniformPreparationParameters parameters)) := by
  exact externallyControlledStrictUnitaryExactOperatorComponent_target
    (fun _ => 0) (historyOrderUniformExternalControlLayout layout evidence)
    (shuklaVedulaWidthOnlyUniformInversePlan
      (historyOrderUniformPreparationParameters parameters))

/-- Pairwise-disjointness certificate for the frozen P42 call.  The registers
are fixed by `HistoryBlockLayout`; this structure only exposes the proof data
needed by the shared Cuccaro component. -/
structure HistoryControlledClockIncrementEvidence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  masked_clock_disjoint : ∀ left right,
    (historyClockMaskedConstantRegister layout).wire left ≠
      (historyClockAccumulatorRegister layout).wire right
  carry_ne_masked : ∀ index,
    historyClockIncrementCarry layout ≠
      (historyClockMaskedConstantRegister layout).wire index
  carry_ne_clock : ∀ index,
    historyClockIncrementCarry layout ≠
      (historyClockAccumulatorRegister layout).wire index
  branch_ne_masked : ∀ index,
    historyBranchWire layout ≠
      (historyClockMaskedConstantRegister layout).wire index
  branch_ne_clock : ∀ index,
    historyBranchWire layout ≠
      (historyClockAccumulatorRegister layout).wire index
  branch_ne_carry :
    historyBranchWire layout ≠ historyClockIncrementCarry layout

/-- Frozen P42 layout: branch-controlled addition of one to the clock, using
the masked-constant prefix and first increment-work wire from the source. -/
def historyControlledClockIncrementSpec
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryControlledClockIncrementEvidence layout) :
    ControlledAddConstantMod2PowSpec qubits (historyClockTailWidth parameters) where
  addend := historyClockMaskedConstantRegister layout
  accumulator := historyClockAccumulatorRegister layout
  carry := historyClockIncrementCarry layout
  addend_accumulator_disjoint := evidence.masked_clock_disjoint
  carry_ne_addend := evidence.carry_ne_masked
  carry_ne_accumulator := evidence.carry_ne_clock
  control := historyBranchWire layout
  constant := 1
  control_ne_addend := evidence.branch_ne_masked
  control_ne_accumulator := evidence.branch_ne_clock
  control_ne_carry := evidence.branch_ne_carry

/-- Full-dirty source-faithful P42 implementation child.  Its target remains
the recorded mask/Cuccaro/unmask action and is not the clean modular-add target. -/
noncomputable def historyControlledClockIncrementExactComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryControlledClockIncrementEvidence layout) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  controlledAddConstantMod2PowExactOperatorComponent symbolValue
    (historyControlledClockIncrementSpec layout evidence)

theorem historyControlledClockIncrementExactComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (symbolValue : String → ℝ)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryControlledClockIncrementEvidence layout) :
    (historyControlledClockIncrementExactComponent
        symbolValue layout evidence).target =
      controlledAddConstantMod2PowDirtyOperator
        (historyControlledClockIncrementSpec layout evidence) := by
  exact controlledAddConstantMod2PowExactOperatorComponent_target _ _

/-- All layout proof data and recorded angles needed to instantiate I01--I07.
The seven child components themselves are not parameters of the parent. -/
structure HistoryClockConcreteSourceOrderEvidence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  uniformExternalControl : HistoryOrderUniformExternalControlEvidence layout
  idleTransform : HistoryIdleTransformEvidence layout
  coefficientControl_ne_signal :
    historyActiveWire layout ≠ layout.coefficientSignal
  projectorControl : HistoryProjectorControlEvidence layout
  controlledIncrement : HistoryControlledClockIncrementEvidence layout
  idleCoefficientAngle : AngleExpr
  coefficientAngle : AngleExpr

/-- Wires required to be zero at every clean P16 stage boundary.  This is the
intersection of the P24 external-control compiler work and the P42 masked
addend/carry work; it does not constrain the live clock accumulator. -/
def historyClockCleanProtectedWires
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    List (Fin qubits) :=
  [(historyUniformControlWork layout).wire 0,
    (historyUniformControlWork layout).wire 1] ++
    historyRegisterWires (historyClockMaskedConstantRegister layout) ++
    [historyClockIncrementCarry layout]

/-- Every P16 clean-protected wire belongs to the frozen workspace region. -/
theorem historyClockCleanProtectedWire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (wire : Fin qubits)
    (member : wire ∈ historyClockCleanProtectedWires layout) :
    wire ∈ historyRegisterWires layout.workspace := by
  unfold historyClockCleanProtectedWires at member
  rcases List.mem_append.mp member with prefixMember | carryMember
  · rcases List.mem_append.mp prefixMember with uniformMember | maskedMember
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at uniformMember
      rcases uniformMember with rfl | rfl
      · exact historyUniformControlWork_wire_mem_workspace layout 0
      · exact historyUniformControlWork_wire_mem_workspace layout 1
    · simp only [historyRegisterWires, List.mem_ofFn] at maskedMember
      rcases maskedMember with ⟨index, rfl⟩
      exact historyClockMaskedConstantRegister_wire_mem_workspace layout index
  · simp only [List.mem_singleton] at carryMember
    subst wire
    exact historyClockIncrementCarry_mem_workspace layout

/-- Every P15 external-control compiler-work wire belongs to the workspace. -/
theorem historyControlledWorkWire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (wire : Fin qubits)
    (member : wire ∈ historyRegisterWires (historyControlledWork layout)) :
    wire ∈ historyRegisterWires layout.workspace := by
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  exact historyControlledWork_wire_mem_workspace layout index

/-- Computational-basis generator predicate for the common clean P16 middle
space. -/
def historyClockCleanPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  ∀ wire, wire ∈ historyClockCleanProtectedWires layout → basis wire = false

end SpectralSamplingProof.Components

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore

section NormalizedMacro

end NormalizedMacro

end SpectralSamplingProof.Components
