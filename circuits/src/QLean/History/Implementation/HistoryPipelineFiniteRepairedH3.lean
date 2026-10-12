import QLean.History.Implementation.HistoryPipelineRepairedH3

/-!
# Finite compiler for the repaired H3 word

The semantic H3 component is intentionally `noncomputable`, because it also
stores operators and correctness proofs.  Its emitted circuit, however, is a
finite program.  This file spells out that program from layout data, finite
integers and closed angle syntax only.  The compiler is an ordinary `def`;
the noncomputable scientific wrapper appears only in the bridge theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components

/-- Direct finite implementation of a comparison against a natural constant.
It is the circuit projection of `historyLessThanConstantExactComponent`. -/
def finiteLessThanConstantCircuit119 {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat) :
    VerifiedCircuitCore.Circuit (VerifiedCircuitCore.PrimitiveGate qubits) :=
  VerifiedCircuitCore.Circuit.sequence [
    (ClassicalReversibleStage.xorConstant
      (List.ofFn spec.rhs.wire) constant).compile,
    unsignedLessThanXorCircuit spec,
    (ClassicalReversibleStage.xorConstant
      (List.ofFn spec.rhs.wire) constant).compile]

/-- Direct finite source word for the repaired idle transformation. -/
def finiteRepairedH3IdleTransform119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryIdleTransformEvidence layout)
    (binaryLabels : Nat) (angle : VerifiedCircuitCore.AngleExpr) :
    VerifiedCircuitCore.Circuit (VerifiedCircuitCore.PrimitiveGate qubits) :=
  let idleConjunction :=
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyIdleFlag layout] []
      (historyActiveWire layout)).compile
  let orderFinalLabelXor := VerifiedCircuitCore.Circuit.sequence
    ((repairedH3IdleOrderTargets119 layout binaryLabels).attach.map fun target =>
      VerifiedCircuitCore.Circuit.gate
        (VerifiedCircuitCore.PrimitiveGate.cnot
          (historyActiveWire layout) target.1
        (evidence.active_ne_order target.1
          (repairedH3IdleOrderTargets119_mem_order layout binaryLabels
            target.1 target.2))))
  let coefficientRotation := controlledRyMacroCircuit {
    angle := angle
    control := historyActiveWire layout
    target := layout.coefficientSignal
    different := evidence.active_ne_coefficient }
  VerifiedCircuitCore.Circuit.sequence [
    .gate (VerifiedCircuitCore.PrimitiveGate.cnot
      (historyLessThanIdleEndWire layout)
      (historyIdleFlag layout) evidence.idleEnd_ne_idle),
    .gate (VerifiedCircuitCore.PrimitiveGate.cnot
      (historyLessThanTimeWire layout)
      (historyIdleFlag layout) evidence.time_ne_idle),
    idleConjunction, orderFinalLabelXor, coefficientRotation,
    idleConjunction,
    .gate (VerifiedCircuitCore.PrimitiveGate.cnot
      (historyLessThanTimeWire layout)
      (historyIdleFlag layout) evidence.time_ne_idle),
    .gate (VerifiedCircuitCore.PrimitiveGate.cnot
      (historyLessThanIdleEndWire layout)
      (historyIdleFlag layout) evidence.idleEnd_ne_idle)]

/-- Direct finite source word for the projector-control child. -/
def finiteRepairedH3ProjectorControl119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryProjectorControlEvidence layout) :
    VerifiedCircuitCore.Circuit (VerifiedCircuitCore.PrimitiveGate qubits) :=
  let degreeZeroEquality :=
    (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
      (historyRegisterWires layout.order)
      (historyRegisterWires (historyEqualityWork layout)) 0
      (historyEqualityFlag layout)).compile
  let projectorConjunction :=
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyEqualityFlag layout] []
      (historyCoefficientControl layout)).compile
  VerifiedCircuitCore.Circuit.sequence [
    .gate (VerifiedCircuitCore.PrimitiveGate.cnot
      (historyBranchWire layout) layout.projectorSignal
      evidence.branch_ne_projector),
    degreeZeroEquality, projectorConjunction,
    .gate (VerifiedCircuitCore.PrimitiveGate.cnot
      (historyCoefficientControl layout) layout.projectorSignal
      evidence.coefficientControl_ne_projector),
    projectorConjunction, degreeZeroEquality]

/-- The complete repaired H3 source order as a computable finite circuit. -/
def finiteRepairedH3Circuit119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (clock : HistoryClockConcreteSourceOrderEvidence layout)
    (timeComparisonSpec idleEndComparisonSpec :
      UnsignedLessThanXorSpec qubits (historyClockWidth
        parameters.timeSteps parameters.taylorOrder parameters.idlingSteps))
    (physicalClocks idleClockEnd binaryLabels : Nat)
    (idleAngle coefficientAngle : VerifiedCircuitCore.AngleExpr) :
    VerifiedCircuitCore.Circuit (VerifiedCircuitCore.PrimitiveGate qubits) :=
  let selectorEquality :=
    (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
      (historyRegisterWires layout.selector) [] 2
      (historyBranchWire layout)).compile
  let timeComparison := finiteLessThanConstantCircuit119
    timeComparisonSpec physicalClocks
  let idleEndComparison := finiteLessThanConstantCircuit119
    idleEndComparisonSpec idleClockEnd
  let activeConjunction :=
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyActiveWire layout)).compile
  let uniformInverse := VerifiedCircuitCore.Circuit.sequence
    ((shuklaVedulaWidthOnlyUniformInversePlan
      (historyOrderUniformPreparationParameters parameters)).map fun leaf =>
        leaf.compile
          (historyOrderUniformExternalControlLayout layout
            clock.uniformExternalControl))
  let idleTransform := finiteRepairedH3IdleTransform119 layout
    clock.idleTransform binaryLabels idleAngle
  let coefficientRotation := Circuit.controlledRyMacroExpansion
    (historyActiveWire layout) layout.coefficientSignal
    clock.coefficientControl_ne_signal coefficientAngle
  let projector := finiteRepairedH3ProjectorControl119 layout
    clock.projectorControl
  let increment :=
    (controlledAddConstantMod2PowStage
      (historyControlledClockIncrementSpec layout
        clock.controlledIncrement)).compile
  VerifiedCircuitCore.Circuit.sequence [
    selectorEquality, timeComparison, idleEndComparison, activeConjunction,
    uniformInverse, activeConjunction, idleTransform, activeConjunction,
    coefficientRotation, activeConjunction, idleEndComparison, timeComparison,
    projector, increment, selectorEquality]

noncomputable section

/-- Forgetting the proof fields of an exact component sequence leaves the
same source-order circuit sequence.  Keeping this lemma local to the finite
compiler prevents the executable definitions above from depending on proof
objects. -/
theorem finiteExactSequenceCircuit119
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → VerifiedCircuitCore.Operator basis}
    (components : List
      (VerifiedCircuitCore.ExactOperatorComponent gateOperator)) :
    (VerifiedCircuitCore.ExactOperatorComponent.sequence components).circuit =
      VerifiedCircuitCore.Circuit.sequence
        (components.map
          VerifiedCircuitCore.ExactOperatorComponent.circuit) := by
  induction components with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      change VerifiedCircuitCore.Circuit.seq first.circuit
          (VerifiedCircuitCore.ExactOperatorComponent.sequence rest).circuit =
        VerifiedCircuitCore.Circuit.seq first.circuit
          (VerifiedCircuitCore.Circuit.sequence
            (rest.map
              VerifiedCircuitCore.ExactOperatorComponent.circuit))
      rw [inductionHypothesis]

theorem finiteLessThanConstantCircuit119_eq_component
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (constant : Nat) :
    finiteLessThanConstantCircuit119 spec constant =
      (historyLessThanConstantExactComponent
        internalZeroSymbolEnvironment spec constant).circuit := by
  unfold finiteLessThanConstantCircuit119
    historyLessThanConstantExactComponent
  rw [finiteExactSequenceCircuit119]
  simp only [List.map_cons, List.map_nil]
  unfold ClassicalReversibleStage.xorConstantExactComponent
  rw [ClassicalReversibleStage.primitiveExactOperatorComponent_circuit]
  unfold unsignedLessThanXorExactComponent
  rfl

theorem finiteUnitaryExactSequenceCircuit119
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → VerifiedCircuitCore.Operator basis}
    (components : List
      (VerifiedCircuitCore.UnitaryExactOperatorComponent gateOperator)) :
    (VerifiedCircuitCore.UnitaryExactOperatorComponent.sequence
        components).circuit =
      VerifiedCircuitCore.Circuit.sequence
        (components.map fun component => component.circuit) := by
  induction components with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [VerifiedCircuitCore.UnitaryExactOperatorComponent.sequence,
        VerifiedCircuitCore.UnitaryExactOperatorComponent.seq,
        VerifiedCircuitCore.ExactOperatorComponent.seq,
        VerifiedCircuitCore.Circuit.sequence, List.map_cons]
      exact congrArg
        (VerifiedCircuitCore.Circuit.seq first.circuit)
        inductionHypothesis

theorem finiteOrderUniformPreparationInverse119_eq_component
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout) :
    VerifiedCircuitCore.Circuit.sequence
        ((shuklaVedulaWidthOnlyUniformInversePlan
          (historyOrderUniformPreparationParameters parameters)).map fun leaf =>
          leaf.compile
            (historyOrderUniformExternalControlLayout layout evidence)) =
      (historyOrderUniformPreparationInverseExactComponent
        layout evidence).circuit := by
  unfold historyOrderUniformPreparationInverseExactComponent
    externallyControlledStrictUnitaryExactOperatorComponent
  change
    VerifiedCircuitCore.Circuit.sequence
        ((shuklaVedulaWidthOnlyUniformInversePlan
          (historyOrderUniformPreparationParameters parameters)).map fun leaf =>
          leaf.compile
            (historyOrderUniformExternalControlLayout layout evidence)) =
      (VerifiedCircuitCore.UnitaryExactOperatorComponent.sequence
        ((shuklaVedulaWidthOnlyUniformInversePlan
          (historyOrderUniformPreparationParameters parameters)).map fun leaf =>
          leaf.strictUnitaryExactOperatorComponent (fun _ => 0)
            (historyOrderUniformExternalControlLayout layout evidence))).circuit
  rw [finiteUnitaryExactSequenceCircuit119]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  rw [List.map_map]
  apply List.map_congr_left
  intro leaf _member
  unfold ExternallyControlledPrimitivePlan.strictUnitaryExactOperatorComponent
    ExternallyControlledPrimitivePlan.strictExactOperatorComponent
    VerifiedCircuitCore.ExactOperatorComponent.toUnitary
  rfl

theorem finiteRepairedH3IdleTransform119_eq_component
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryIdleTransformEvidence layout)
    (binaryLabels : Nat) (angle : VerifiedCircuitCore.AngleExpr) :
    finiteRepairedH3IdleTransform119 layout evidence binaryLabels angle =
      (let idleEndToggle := historyCnotExactComponent (fun _ => 0)
          (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
          evidence.idleEnd_ne_idle
       let timeToggle := historyCnotExactComponent (fun _ => 0)
          (historyLessThanTimeWire layout) (historyIdleFlag layout)
          evidence.time_ne_idle
       let idleConjunction :=
          ClassicalReversibleStage.xorConjunctionMinimumWorkExactComponent
            (fun _ => 0) [historyBranchWire layout, historyIdleFlag layout] []
            (historyActiveWire layout)
       let orderFinalLabelXor := ExactOperatorComponent.sequence
          ((repairedH3IdleOrderTargets119 layout binaryLabels).attach.map fun target =>
            historyCnotExactComponent (fun _ => 0) (historyActiveWire layout)
              target.1 (evidence.active_ne_order target.1
                (repairedH3IdleOrderTargets119_mem_order layout binaryLabels
                  target.1 target.2)))
       let coefficientRotation :=
          historyClockCoefficientRotationNormalizedStageComponent
            (historyActiveWire layout) layout.coefficientSignal
            evidence.active_ne_coefficient angle
       ExactOperatorComponent.sequence [idleEndToggle, timeToggle,
         idleConjunction, orderFinalLabelXor, coefficientRotation,
         idleConjunction, timeToggle, idleEndToggle]).circuit := by
  unfold finiteRepairedH3IdleTransform119
    ClassicalReversibleStage.xorConjunctionMinimumWorkExactComponent
  simp only [finiteExactSequenceCircuit119, List.map_cons, List.map_nil]
  rw [ClassicalReversibleStage.primitiveExactOperatorComponent_circuit]
  simp only [List.map_map]
  unfold historyCnotExactComponent
    historyClockCoefficientRotationNormalizedStageComponent
  rfl

theorem finiteRepairedH3ProjectorControl119_eq_component
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryProjectorControlEvidence layout) :
    finiteRepairedH3ProjectorControl119 layout evidence =
      (historyProjectorControlExactComponent
        internalZeroSymbolEnvironment layout evidence).circuit := by
  unfold finiteRepairedH3ProjectorControl119
    historyProjectorControlExactComponent
    ClassicalReversibleStage.xorEqualityToConstantMinimumWorkExactComponent
    ClassicalReversibleStage.xorConjunctionMinimumWorkExactComponent
  simp only [finiteExactSequenceCircuit119, List.map_cons, List.map_nil]
  rw [ClassicalReversibleStage.primitiveExactOperatorComponent_circuit]
  rw [ClassicalReversibleStage.primitiveExactOperatorComponent_circuit]
  rfl

/-- Projecting the certified scientific H3 component to its circuit yields
exactly the ordinary finite compiler above. -/
theorem finiteRepairedH3Circuit119_eq_certified
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    finiteRepairedH3Circuit119
        (ExecutableLayout119 source domain)
        (ExecutableClockEvidence119 source domain)
        (((ScientificWidthGenericContract.correctedCleanEvidence259
          (ExecutableRaw119 source)
          (ExecutableAdmissible119 source domain)).clock
            ).clockTimeLessThan.toSpec)
        (((ScientificWidthGenericContract.correctedCleanEvidence259
          (ExecutableRaw119 source)
          (ExecutableAdmissible119 source domain)).clock
            ).clockIdleEndLessThan.toSpec)
        source.historyParameters.physicalClocks
        (historyIdleClockEnd source.historyParameters.physicalClocks
          source.historyParameters.taylorOrder
          (ExecutableRaw119 source).history.idlingSteps)
        source.historyParameters.binaryLabels
        (repairedH3IdleAngle119 source)
        compiledIdleCoefficientAngle119 =
      (repairedH3Component119 source domain).circuit := by
  rw [repairedH3Component119_source_order]
  unfold finiteRepairedH3Circuit119 repairedH3Components119
  simp only [List.map_cons, List.map_nil]
  rw [finiteLessThanConstantCircuit119_eq_component]
  rw [finiteLessThanConstantCircuit119_eq_component]
  rw [finiteOrderUniformPreparationInverse119_eq_component]
  rw [finiteRepairedH3IdleTransform119_eq_component]
  rw [finiteRepairedH3ProjectorControl119_eq_component]
  unfold historyControlledClockIncrementExactComponent
  rw [controlledAddConstantMod2PowExactOperatorComponent_circuit]
  unfold repairedH3SelectorEquality119 repairedH3TimeComparison119
    repairedH3IdleEndComparison119 repairedH3ActiveConjunction119
    repairedH3IdleTransform119 repairedH3CoefficientRotation119
    historyOrderUniformPreparationInverseExactComponent
    ClassicalReversibleStage.xorEqualityToConstantMinimumWorkExactComponent
    ClassicalReversibleStage.xorConjunctionMinimumWorkExactComponent
  rw [ClassicalReversibleStage.primitiveExactOperatorComponent_circuit]
  rw [ClassicalReversibleStage.primitiveExactOperatorComponent_circuit]
  rfl

end

end ExecutableHistoryExecutableHistory
