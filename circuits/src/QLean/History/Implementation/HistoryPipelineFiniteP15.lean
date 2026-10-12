import QLean.History.Implementation.HistoryPipelineFiniteRepairedH3
import QLean.History.HistoryP15GeneratedProviderInternalBinding226

/-!
# Finite compiler for the padded P15 history block

The legacy raw compiler required the history carrier width to be exactly the
probability-generator target width.  The scientific construction deliberately
uses a larger history carrier.  This module therefore emits the P15 word
directly from the accepted padded layout instead of casting an equal-width
generator word.

All definitions before the bridge section are ordinary `def`s.  In
particular, no operator, semantic equality, or classical choice is needed to
obtain the finite primitive-gate word.
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
open ExecutableHistoryData

/-- Source-faithful equality compiler.  Unlike the legacy unrestricted
compiler, this uses the proved minimum-work implementation, so two controls
with no scratch compile to the required Toffoli rather than to identity. -/
def finiteMinimumWorkEquality119 {qubits : Nat}
    (register scratch : List (Fin qubits)) (constant : Nat)
    (target : Fin qubits) :
    VerifiedCircuitCore.Circuit (PrimitiveGate qubits) :=
  (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
    register scratch constant target).compile

/-- Source-faithful conjunction compiler using the same minimum-work word as
the clean P15 component. -/
def finiteMinimumWorkConjunction119 {qubits : Nat}
    (controls scratch : List (Fin qubits)) (target : Fin qubits) :
    VerifiedCircuitCore.Circuit (PrimitiveGate qubits) :=
  (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
    controls scratch target).compile

/-- The four finite P15 calls before the controlled probability generator. -/
def finiteHistoryTaylorBefore119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryTaylorL2Evidence layout) :
    List (VerifiedCircuitCore.Circuit (PrimitiveGate qubits)) :=
  [ finiteMinimumWorkEquality119 (historyRegisterWires layout.selector) [] 1
      (historyBranchWire layout),
    finiteLessThanConstantCircuit119 evidence.clockTimeLessThan.toSpec
      parameters.timeSteps,
    finiteLessThanConstantCircuit119 evidence.clockIdleEndLessThan.toSpec
      (historyIdleClockEnd parameters.timeSteps parameters.taylorOrder
        parameters.idlingSteps),
    finiteMinimumWorkConjunction119
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyActiveWire layout) ]

/-- One finite coefficient-angle iteration, in the frozen P15 source order. -/
def finiteHistoryTaylorCoefficientIteration119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryTaylorL2Evidence layout)
    (angle : VerifiedCircuitCore.AngleExpr)
    (index : Fin parameters.taylorOrder) :
    List (VerifiedCircuitCore.Circuit (PrimitiveGate qubits)) :=
  let equality := finiteMinimumWorkEquality119
    (historyRegisterWires layout.order)
    (historyRegisterWires (historyEqualityWork layout)) (index.val + 1)
    (historyEqualityFlag layout)
  let active := finiteMinimumWorkConjunction119
    [historyCoefficientControl layout, historyEqualityFlag layout] []
    (historyActiveWire layout)
  let rotation := actualRotation225
    (historyActiveWire layout) layout.coefficientSignal
    evidence.active_ne_coefficientSignal angle
  [equality, active, rotation, active, equality]

/-- All finite coefficient-angle iterations. -/
def finiteHistoryTaylorCoefficientLoop119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryTaylorL2Evidence layout)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr) :
    List (VerifiedCircuitCore.Circuit (PrimitiveGate qubits)) :=
  (List.finRange parameters.taylorOrder).flatMap
    (fun index => finiteHistoryTaylorCoefficientIteration119
      layout evidence (angles index) index)

/-- The complete finite P15 suffix after the controlled generator. -/
def finiteHistoryTaylorAfter119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryTaylorL2Evidence layout)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr) :
    List (VerifiedCircuitCore.Circuit (PrimitiveGate qubits)) :=
  let clockTime := finiteLessThanConstantCircuit119
    evidence.clockTimeLessThan.toSpec parameters.timeSteps
  let clockIdleEnd := finiteLessThanConstantCircuit119
    evidence.clockIdleEndLessThan.toSpec
    (historyIdleClockEnd parameters.timeSteps parameters.taylorOrder
      parameters.idlingSteps)
  let generatorActive := finiteMinimumWorkConjunction119
    [historyBranchWire layout, historyLessThanTimeWire layout] []
    (historyActiveWire layout)
  let idleEndX := actualX225 (historyLessThanIdleEndWire layout)
  let invalidClock := actualToffoli225
    (historyBranchWire layout) (historyLessThanIdleEndWire layout)
    layout.coefficientSignal evidence.branch_ne_ltIdleEnd
    evidence.branch_ne_coefficientSignal
    evidence.ltIdleEnd_ne_coefficientSignal
  let degreeLess := finiteLessThanConstantCircuit119
    evidence.degreeOrderLessThan.toSpec parameters.taylorOrder
  let equalityX := actualX225 (historyEqualityFlag layout)
  let orderBoundaryActive := finiteMinimumWorkConjunction119
    [historyBranchWire layout, historyLessThanTimeWire layout] []
    (historyActiveWire layout)
  let orderBoundary := actualToffoli225
    (historyActiveWire layout) (historyEqualityFlag layout)
    layout.orderBoundarySignal evidence.active_ne_equality
    evidence.active_ne_orderBoundary evidence.equality_ne_orderBoundary
  let idleEndToggle := actualCnot225
    (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
    evidence.ltIdleEnd_ne_idle
  let timeToggle := actualCnot225
    (historyLessThanTimeWire layout) (historyIdleFlag layout)
    evidence.ltTime_ne_idle
  let idleActive := finiteMinimumWorkConjunction119
    [historyBranchWire layout, historyIdleFlag layout] []
    (historyActiveWire layout)
  let idleLastEquality := finiteMinimumWorkEquality119
    (historyRegisterWires layout.order)
    (historyRegisterWires (historyEqualityWork layout))
    (historyIdleBlockSize parameters.taylorOrder - 1)
    (historyEqualityFlag layout)
  let incrementActive := finiteMinimumWorkConjunction119
    [historyBranchWire layout, historyLessThanIdleEndWire layout] []
    (historyActiveWire layout)
  let degreeIncrement := actualIncrement225
    (historyTaylorDegreeIncrementSpec layout evidence.degreeIncrement)
  let coefficientActive := finiteMinimumWorkConjunction119
    [historyBranchWire layout, historyLessThanTimeWire layout] []
    (historyCoefficientControl layout)
  let idleCoefficientActive := finiteMinimumWorkConjunction119
    [historyBranchWire layout, historyIdleFlag layout] []
    (historyCoefficientControl layout)
  let idleRotation := actualRotation225
    (historyCoefficientControl layout) layout.coefficientSignal
    evidence.coefficientControl_ne_coefficientSignal
    idleAngle
  [generatorActive,
    idleEndX, invalidClock, idleEndX,
    degreeLess, equalityX, orderBoundaryActive, orderBoundary,
      orderBoundaryActive, equalityX, degreeLess,
    idleEndToggle, timeToggle, idleActive, idleLastEquality, orderBoundary,
      idleLastEquality, idleActive, timeToggle, idleEndToggle,
    incrementActive, degreeIncrement, incrementActive,
    coefficientActive] ++
    finiteHistoryTaylorCoefficientLoop119 layout evidence angles ++
  [coefficientActive,
    idleEndToggle, timeToggle, idleCoefficientActive, idleRotation,
      idleCoefficientActive, timeToggle, idleEndToggle,
    clockIdleEnd, clockTime,
    finiteMinimumWorkEquality119 (historyRegisterWires layout.selector) [] 1
      (historyBranchWire layout)]

/-- The central controlled-Q10 word compiled into the padded history layout. -/
def finiteHistoryTaylorControlledGenerator119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    (p : QParameters)
    (control : HistoryTaylorQ10ControlEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p) :
    VerifiedCircuitCore.Circuit (PrimitiveGate qubits) :=
  compileExternallyControlledCircuit control.placement.externalLayout
    ((ProbabilityGeneratorQProof.uqCircuit p).mapGates
      ProbabilityGeneratorQProof.PrimitiveGate.toCanonicalCore)

/-- Complete computable P15 circuit on a padded history carrier. -/
def finiteHistoryTaylorPaddedCircuit119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (p : QParameters)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryTaylorL2Evidence layout)
    (control : HistoryTaylorQ10ControlEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr) :
    VerifiedCircuitCore.Circuit (PrimitiveGate qubits) :=
    VerifiedCircuitCore.Circuit.sequence
    (finiteHistoryTaylorBefore119 layout evidence ++
      [finiteHistoryTaylorControlledGenerator119 p control] ++
      finiteHistoryTaylorAfter119 layout evidence angles idleAngle)

noncomputable section

/-- The ordinary central compiler flattens to the already certified strict
external-control component. -/
theorem finiteHistoryTaylorControlledGenerator119_flatten_eq
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    (p : QParameters)
    (control : HistoryTaylorQ10ControlEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p) :
    (finiteHistoryTaylorControlledGenerator119 p control).flatten =
      (historyTaylorControlledProbabilityGeneratorStrictExactComponent
        p control).circuit.flatten := by
  unfold finiteHistoryTaylorControlledGenerator119
    historyTaylorControlledProbabilityGeneratorStrictExactComponent
    r12ControlledSubcircuitStrictExactComponent
  rw [externallyControlledStrictExactOperatorComponentOfExact_flatten]
  unfold probabilityGeneratorCanonicalCoreExactOperatorComponent
  rfl

end

end ExecutableHistoryExecutableHistory
