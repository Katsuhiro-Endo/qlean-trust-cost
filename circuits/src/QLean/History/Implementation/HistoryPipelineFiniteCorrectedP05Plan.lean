import QLean.History.Implementation.HistoryPipelineFiniteScientificAngles

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option warningAsError true

/-!
# Data-driven finite corrected-P05 plan

The execution record below contains exactly the finite layout, comparison and
control data consumed by the P15 and repaired-H3 compilers. Its `compile`
definition is an ordinary `def`; no real-number comparison, phase choice or
operator semantics is evaluated while producing the primitive word.

The proof-only scientific wrapper at the end projects the already certified
history construction into this same record. Consequently the numerical and
theoretical paths share one circuit-building function.
-/

namespace ExecutableHistoryFiniteCorrectedP05

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryExecutableHistory
open ExecutableHistoryData
open ExecutableHistoryFiniteScientificAngles

structure Plan (qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat)
    (p : QParameters) (parameters : HistoryBlockParameters) where
  layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
    (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters
  selector : HistorySelectorPreparationParameters qubits
  p15Evidence : HistoryTaylorL2Evidence layout
  p15Control : HistoryTaylorQ10ControlEvidence
    (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
    (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p
  coefficientAngles : Fin parameters.taylorOrder →
    VerifiedCircuitCore.AngleExpr
  idleCoefficientAngle : VerifiedCircuitCore.AngleExpr
  clockEvidence : HistoryClockConcreteSourceOrderEvidence layout
  timeComparison : UnsignedLessThanXorSpec qubits
    (historyClockWidth parameters.timeSteps parameters.taylorOrder
      parameters.idlingSteps)
  idleEndComparison : UnsignedLessThanXorSpec qubits
    (historyClockWidth parameters.timeSteps parameters.taylorOrder
      parameters.idlingSteps)
  physicalClocks : Nat
  idleClockEnd : Nat
  binaryLabels : Nat
  repairedIdleAngle : VerifiedCircuitCore.AngleExpr
  repairedCoefficientAngle : VerifiedCircuitCore.AngleExpr

/-- The unique finite corrected-P05 construction body. -/
def Plan.compile
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {p : QParameters} {parameters : HistoryBlockParameters}
    (plan : Plan qubits dataWidth generatorSignalWidth generatorWorkWidth
      p parameters) :
    VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate qubits) :=
  finiteCorrectedP05Circuit119 plan.selector
    (finiteHistoryTaylorPaddedCircuit119 p plan.layout plan.p15Evidence
      plan.p15Control plan.coefficientAngles plan.idleCoefficientAngle)
    (finiteRepairedH3Circuit119 plan.layout plan.clockEvidence
      plan.timeComparison plan.idleEndComparison plan.physicalClocks
      plan.idleClockEnd plan.binaryLabels plan.repairedIdleAngle
      plan.repairedCoefficientAngle)

noncomputable section

/-- Proof-only projection of a valid scientific input into the finite plan.
All circuit data are fed to `Plan.compile`; the wrapper performs no alternative
gate construction. -/
def certifiedPlan
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    Plan
      (ExecutableRaw119 source).history.qubits
      (ExecutableRaw119 source).history.dataWidth
      (ExecutableRaw119 source).history.generatorSignalWidth
      (ExecutableRaw119 source).history.generatorWorkWidth
      (ScientificWidthGenericContract.correctedGeneratorParameters259
        (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
      (HistoryRawSchema.parameters203
        (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic) :=
  let layout := ExecutableLayout119 source domain
  let clean := ScientificWidthGenericContract.correctedCleanEvidence259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let l2 := HistoryIndexCast.history_taylor_l2_evidence207
    (ExecutableRaw119 source).history
    (ExecutableAdmissible119 source domain).analytic
  let control := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  { layout := layout
    selector := historySelectorPreparationParametersAtLayout layout
      (correctedSelectorHigh source) correctedSelectorLow correctedSelectorLow
    p15Evidence := l2
    p15Control := control
    coefficientAngles := fun index => correctedCoefficient source index.val
    idleCoefficientAngle := compiledIdleCoefficientAngle119
    clockEvidence := ExecutableClockEvidence119 source domain
    timeComparison := clean.clock.clockTimeLessThan.toSpec
    idleEndComparison := clean.clock.clockIdleEndLessThan.toSpec
    physicalClocks := source.historyParameters.physicalClocks
    idleClockEnd := historyIdleClockEnd
      source.historyParameters.physicalClocks
      source.historyParameters.taylorOrder
      (ExecutableRaw119 source).history.idlingSteps
    binaryLabels := source.historyParameters.binaryLabels
    repairedIdleAngle := repairedIdle source
    repairedCoefficientAngle := compiledIdleCoefficientAngle119 }

theorem certifiedPlan_compile_eq
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (certifiedPlan source domain).compile =
      finiteCorrectedP05CertifiedProjection119 source domain := by
  rfl

end
end ExecutableHistoryFiniteCorrectedP05
