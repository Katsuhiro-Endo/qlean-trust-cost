import QLean.History.Implementation.HistoryPipelineFiniteP15
import QLean.History.Implementation.HistoryPipelineCorrectedP05Circuit

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

/-- Computable H1 source word. -/
def finiteHistorySelectorForward119 {qubits : Nat}
    (parameters : HistorySelectorPreparationParameters qubits) :
    VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate qubits) :=
  historySelectorPreparationCircuit parameters

/-- Computable H1 inverse word, obtained from the same five-gate H1 word. -/
def finiteHistorySelectorInverse119 {qubits : Nat}
    (parameters : HistorySelectorPreparationParameters qubits) :
    VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate qubits) :=
  (historySelectorPreparationCircuit parameters).reverse
    VerifiedCircuitCore.PrimitiveGate.inverse

/-- Finite corrected-P05 assembler.  The P15 and repaired-H3 words are data;
the H1/H1-inverse pair is generated from one common selector parameter
record, so a numerical caller cannot accidentally use two unrelated words. -/
def finiteCorrectedP05Circuit119 {qubits : Nat}
    (parameters : HistorySelectorPreparationParameters qubits)
    (p15 repairedH3 : VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate qubits)) :
    VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate qubits) :=
  VerifiedCircuitCore.Circuit.sequence [
    finiteHistorySelectorForward119 parameters,
    p15,
    repairedH3,
    finiteHistorySelectorInverse119 parameters]

/-- The P50-composed selector implementation used by corrected P05 has the
same literal finite source word as the direct H1 compiler. -/
theorem finiteHistorySelectorForward119_eq_p50
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    (finiteHistorySelectorForward119 parameters).flatten =
      (historySelectorPreparationP50ComposedExactComponent
        symbolValue parameters).circuit.flatten := by
  unfold finiteHistorySelectorForward119
    historySelectorPreparationP50ComposedExactComponent
  rw [historySelectorPreparationFromP50ExactComponent_circuit]
  unfold compiledHistorySelectorPreparationFromP50ExactComponent
  rw [finiteExactSequenceCircuit119]
  simp only [List.map_cons, List.map_nil]
  unfold historySelectorPreparationConcreteP50Children
  rw [historySelectorHighRotationP50ExactComponent_circuit,
    historySelectorLowControlledRotationP50ExactComponent_circuit]
  unfold compiledHistorySelectorLowControlledRotationP50ExactComponent
  rw [finiteExactSequenceCircuit119]
  simp only [List.map_cons, List.map_nil]
  unfold historySelectorPreparationCircuit historySelectorPreparationGates
  simp [VerifiedCircuitCore.Circuit.flatten]

private theorem list_replicate_flatten_reverse119 {α : Type*}
    (items : List α) :
    ∀ count, (List.replicate count items.reverse).flatten =
      (List.replicate count items).flatten.reverse := by
  intro count
  simpa [List.reverse_replicate] using
    (List.flatten_reverse (L := List.replicate count items.reverse))

private theorem flatten_reverse119 {Gate : Type*} (inverseGate : Gate → Gate) :
    ∀ circuit : VerifiedCircuitCore.Circuit Gate,
      (circuit.reverse inverseGate).flatten =
        circuit.flatten.reverse.map inverseGate
  | .identity => rfl
  | .gate _ => rfl
  | .seq first second => by
      simp [VerifiedCircuitCore.Circuit.reverse,
        VerifiedCircuitCore.Circuit.flatten,
        flatten_reverse119 inverseGate first,
        flatten_reverse119 inverseGate second,
        List.map_append]
  | .repeat count body => by
      simp [VerifiedCircuitCore.Circuit.reverse,
        VerifiedCircuitCore.Circuit.flatten,
        flatten_reverse119 inverseGate body,
        List.map_flatten,
        list_replicate_flatten_reverse119]

theorem finiteHistorySelectorInverse119_eq_p50
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    (finiteHistorySelectorInverse119 parameters).flatten =
      (historySelectorPreparationFromP50InverseExactComponent
        (historySelectorPreparationConcreteP50Children
          symbolValue parameters)).circuit.flatten := by
  change
    ((finiteHistorySelectorForward119 parameters).reverse
        VerifiedCircuitCore.PrimitiveGate.inverse).flatten =
      (((historySelectorPreparationP50ComposedExactComponent
          symbolValue parameters).circuit).reverse
        VerifiedCircuitCore.PrimitiveGate.inverse).flatten
  rw [flatten_reverse119, flatten_reverse119]
  exact congrArg
    (fun gates => gates.reverse.map VerifiedCircuitCore.PrimitiveGate.inverse)
    (finiteHistorySelectorForward119_eq_p50 symbolValue parameters)

noncomputable section

/-- The finite corrected-P05 assembler instantiated with the already certified
P15 child and the new ordinary finite repaired-H3 compiler.  The wrapper is
noncomputable only because the scientific source packages real-valued proof
data; the assembler and H3 program generator above remain ordinary `def`s. -/
def finiteCorrectedP05CertifiedProjection119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate
        (ExecutableRaw119 source).history.qubits) :=
  let layout := ExecutableLayout119 source domain
  let clean := ScientificWidthGenericContract.correctedCleanEvidence259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let p := ScientificWidthGenericContract.correctedGeneratorParameters259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)
  let l2 := HistoryIndexCast.history_taylor_l2_evidence207
    (ExecutableRaw119 source).history
    (ExecutableAdmissible119 source domain).analytic
  let control := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  finiteCorrectedP05Circuit119
    (correctedSelectorParameters119 source domain)
    (finiteHistoryTaylorPaddedCircuit119 p layout l2 control
      (fun index => correctedTaylorCoefficientAngle119
        source.toCommonSource119 index.val)
      compiledIdleCoefficientAngle119)
    (finiteRepairedH3Circuit119 layout
      (ExecutableClockEvidence119 source domain)
      (clean.clock.clockTimeLessThan.toSpec)
      (clean.clock.clockIdleEndLessThan.toSpec)
      source.historyParameters.physicalClocks
      (historyIdleClockEnd source.historyParameters.physicalClocks
        source.historyParameters.taylorOrder
        (ExecutableRaw119 source).history.idlingSteps)
      source.historyParameters.binaryLabels
      (repairedH3IdleAngle119 source)
      compiledIdleCoefficientAngle119)

private theorem historyP15SelectorEqualityWithQ10Component_circuit_finite119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths : QParameters.ProbabilityGeneratorCanonicalPlacementWidths
      p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15SelectorEqualityWithQ10Component layout widths).circuit =
      finiteMinimumWorkEquality119 (historyRegisterWires layout.selector) [] 1
        (historyBranchWire layout) := by
  unfold historyP15SelectorEqualityWithQ10Component
    finiteMinimumWorkEquality119
    ClassicalReversibleStage.xorEqualityToConstantMinimumWorkCleanSubspaceMapComponentBetween
  simp only [SubspaceMapComponent.ofBasisSpan]
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

private theorem historyP15LessThanConstantCleanStageBetween_circuit_finite119
    {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (inputClean : ∀ input, inputPredicate input →
      historyLessThanConstantCleanInputPredicate spec input)
    (directMaps : ∀ input, inputPredicate input →
      outputPredicate
        (historyLessThanConstantDirectBasisAction spec constant input)) :
    (historyP15LessThanConstantCleanStageBetween spec constant
      inputPredicate outputPredicate inputClean directMaps).circuit =
      finiteLessThanConstantCircuit119 spec constant := by
  unfold historyP15LessThanConstantCleanStageBetween
  rw [ExactOperatorComponent.toSubspaceMapOfBasisAgreementBetween_circuit]
  exact (finiteLessThanConstantCircuit119_eq_component spec constant).symm

private theorem historyP15ActiveConjunctionWithQ10Component_circuit_finite119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths : QParameters.ProbabilityGeneratorCanonicalPlacementWidths
      p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15ActiveConjunctionWithQ10Component layout widths).circuit =
      finiteMinimumWorkConjunction119
        [historyBranchWire layout, historyLessThanTimeWire layout] []
        (historyActiveWire layout) := by
  unfold historyP15ActiveConjunctionWithQ10Component
    finiteMinimumWorkConjunction119
    ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
  simp only [SubspaceMapComponent.ofBasisSpan]
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

private theorem historyP15Q10LiveBoundary_circuit_finite119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths : QParameters.ProbabilityGeneratorCanonicalPlacementWidths
      p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15Q10LiveBoundarySubspaceMapComponent layout widths).circuit.flatten =
      (finiteHistoryTaylorControlledGenerator119 p
        (historyP15Q10ControlEvidence_ofFrozenLayout
          (layout := layout) widths)).flatten := by
  unfold historyP15Q10LiveBoundarySubspaceMapComponent
  simp only [SubspaceMapComponent.restrictBasisSpanWithInvariant_circuit,
    historyTaylorControlledProbabilityGeneratorQ10CleanBoundary_circuit]
  exact (finiteHistoryTaylorControlledGenerator119_flatten_eq p
    (historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths)).symm

private theorem finiteHistoryTaylorCoefficientIteration119_eq_sourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryTaylorL2Evidence layout)
    (angle : VerifiedCircuitCore.AngleExpr)
    (index : Fin parameters.taylorOrder) :
    finiteHistoryTaylorCoefficientIteration119 layout evidence angle index =
      historyP15CoefficientIterationSourceStages layout angle index := by
  unfold finiteHistoryTaylorCoefficientIteration119
    historyP15CoefficientIterationSourceStages
  simp [finiteMinimumWorkEquality119, finiteMinimumWorkConjunction119,
    providerIntegration_coefficientEqualityCompute_circuit,
    providerIntegration_coefficientEqualityUncompute_circuit,
    providerIntegration_coefficientActiveCompute_circuit,
    providerIntegration_coefficientActiveUncompute_circuit,
    providerIntegration_coefficientUse_circuit,
    historyClockCoefficientRotationExactComponent,
    actualRotation225]

private theorem finiteHistoryTaylorCoefficientLoop119_eq_sourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryTaylorL2Evidence layout)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr) :
    finiteHistoryTaylorCoefficientLoop119 layout evidence angles =
      (List.finRange parameters.taylorOrder).flatMap
        (fun index => historyP15CoefficientIterationSourceStages layout
          (angles index) index) := by
  unfold finiteHistoryTaylorCoefficientLoop119
  apply List.flatMap_congr
  intro index _member
  exact finiteHistoryTaylorCoefficientIteration119_eq_sourceStages
    layout evidence (angles index) index

set_option linter.unusedSimpArgs false in
private theorem scientificFiniteP15_flatten_eq_clean119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    let raw := ExecutableRaw119 source
    let admissible := ExecutableAdmissible119 source domain
    let layout := ExecutableLayout119 source domain
    let clean := ScientificWidthGenericContract.correctedCleanEvidence259
      raw admissible
    let widths := admissible.placementWidths
    let p := ScientificWidthGenericContract.correctedGeneratorParameters259
      raw admissible
    let l2 := HistoryIndexCast.history_taylor_l2_evidence207
      raw.history admissible.analytic
    let control := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    (finiteHistoryTaylorPaddedCircuit119 p layout l2 control
      (fun index => correctedTaylorCoefficientAngle119
        source.toCommonSource119 index.val)
      compiledIdleCoefficientAngle119).flatten =
      (historyP15FullCleanH2Component layout clean widths
        (fun index => correctedTaylorCoefficientAngle119
          source.toCommonSource119 index.val)
        compiledIdleCoefficientAngle119).circuit.flatten := by
  dsimp only
  have degreeLessSpecEq :
      providerIntegration_orderBoundaryLessThanSpec
          (ExecutableLayout119 source domain) =
        (HistoryIndexCast.history_taylor_l2_evidence207
          (ExecutableRaw119 source).history
          (ExecutableAdmissible119 source domain).analytic).degreeOrderLessThan.toSpec := by
    rfl
  have degreeIncrementSpecEq :
      providerIntegration_degreeIncrementSpec
          (ExecutableLayout119 source domain) =
        historyTaylorDegreeIncrementSpec
          (ExecutableLayout119 source domain)
          (HistoryIndexCast.history_taylor_l2_evidence207
            (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic).degreeIncrement := by
    rfl
  dsimp only [providerIntegration_degreeIncrementSpec] at degreeIncrementSpecEq
  rw [historyP15FullCleanH2Component_flatten_eq_p15]
  rw [historyP15FullCleanComponent_flatten_eq_source]
  unfold finiteHistoryTaylorPaddedCircuit119
    historyP15FullCleanSourceCircuit historyP15FullCleanSourceStages
  simp only [VerifiedCircuitCore.Circuit.flatten_sequence,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  unfold finiteHistoryTaylorBefore119
    historyP15FullCleanPrefixSourceStages historyP15ThroughQ10Components
    historyP15PreQ10WithInvariantComponents
  simp only [List.map_append, List.map_cons, List.map_nil,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [historyP15SelectorEqualityWithQ10Component_circuit_finite119]
  unfold historyP15TimeComparisonWithQ10Component
    historyP15IdleEndComparisonWithQ10Component
  rw [historyP15LessThanConstantCleanStageBetween_circuit_finite119,
    historyP15LessThanConstantCleanStageBetween_circuit_finite119]
  rw [historyP15ActiveConjunctionWithQ10Component_circuit_finite119]
  rw [historyP15Q10LiveBoundary_circuit_finite119]
  simp only [ScientificWidthGenericContract.correctedGeneratorParameters259]
  unfold finiteHistoryTaylorAfter119
    historyP15PostQ10SourceCircuit historyP15PostQ10SourceStages
    historyP15RestoreGeneratorActiveSourceCircuit
    historyP15InvalidClockSourceCircuit
    historyP15OrderBoundarySourceCircuit historyP15OrderBoundarySourceStages
    historyP15IdleBoundarySourceCircuit historyP15IdleBoundarySourceStages
    historyP15DegreeIncrementSourceCircuit historyP15DegreeIncrementSourceStages
    historyP15TaylorCoefficientSourceCircuit
    historyP15TaylorCoefficientSourceStages
    historyP15CoefficientLoopSourceCircuit
    historyP15IdleCoefficientSourceCircuit historyP15IdleCoefficientSourceStages
    historyP15RestoreEntryFlagsSourceCircuit
    historyP15RestoreEntryFlagsSourceStages
  rw [finiteHistoryTaylorCoefficientLoop119_eq_sourceStages]
  rw [providerIntegration_orderDegreeLessCompute_circuit,
    providerIntegration_orderDegreeLessUncompute_circuit]
  rw [degreeLessSpecEq, degreeIncrementSpecEq]
  simp only [VerifiedCircuitCore.Circuit.flatten_sequence,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  simp [finiteMinimumWorkEquality119, finiteMinimumWorkConjunction119,
    providerIntegration_invalidClockStages_circuit_list,
    providerIntegration_orderEqualityXCompute_circuit,
    providerIntegration_orderEqualityXUncompute_circuit,
    providerIntegration_orderActiveCompute_circuit,
    providerIntegration_orderActiveUncompute_circuit,
    providerIntegration_orderToffoli_circuit,
    providerIntegration_idleBoundaryIdleEndToggle_circuit,
    providerIntegration_idleBoundaryTimeToggle_circuit,
    providerIntegration_idleBoundaryActiveCompute_circuit,
    providerIntegration_idleBoundaryEqualityCompute_circuit,
    providerIntegration_idleBoundaryToffoli_circuit,
    providerIntegration_idleBoundaryEqualityUncompute_circuit,
    providerIntegration_idleBoundaryActiveUncompute_circuit,
    providerIntegration_idleBoundaryTimeToggleUncompute_circuit,
    providerIntegration_idleBoundaryIdleEndToggleUncompute_circuit,
    providerIntegration_coefficientEqualityCompute_circuit,
    providerIntegration_coefficientEqualityUncompute_circuit,
    providerIntegration_coefficientActiveCompute_circuit,
    providerIntegration_coefficientActiveUncompute_circuit,
    providerIntegration_coefficientUse_circuit,
    providerIntegration_idleCoefficientIdleEndToggle_circuit,
    providerIntegration_idleCoefficientTimeToggle_circuit,
    providerIntegration_idleCoefficientControlCompute_circuit,
    providerIntegration_idleCoefficientUse_circuit,
    providerIntegration_idleCoefficientControlUncompute_circuit,
    providerIntegration_idleCoefficientTimeToggleUncompute_circuit,
    providerIntegration_idleCoefficientIdleEndToggleUncompute_circuit,
    providerIntegration_restoreIdleEnd_circuit,
    providerIntegration_restoreTime_circuit,
    providerIntegration_restoreSelector_circuit,
    ClassicalReversibleStage.primitiveExactOperatorComponent_circuit,
    ClassicalReversibleStage.compile, ClassicalReversibleStage.toCircuit,
    ClassicalReversibleInstruction.toPrimitiveGate,
    VerifiedCircuitCore.Circuit.mapGates,
    VerifiedCircuitCore.Circuit.flatten,
    historyClockCoefficientRotationExactComponent,
    actualX225, actualCnot225, actualToffoli225, actualRotation225,
    actualIncrement225_eq_history226,
    controlledAddConstantMod2PowExactOperatorComponent_circuit,
    List.append_assoc,
    finiteLessThanConstantCircuit119_eq_component]
  rfl

/-- The finite projection emits exactly the same flattened primitive word as
the certified corrected-P05 component. -/
theorem finiteCorrectedP05CertifiedProjection119_flatten_eq
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (finiteCorrectedP05CertifiedProjection119 source domain).flatten =
      (correctedP05Component119 source domain).circuit.flatten := by
  rw [correctedP05Component119_source_order]
  unfold finiteCorrectedP05CertifiedProjection119
    finiteCorrectedP05Circuit119 correctedP05Components119
  simp only [VerifiedCircuitCore.Circuit.flatten_sequence,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [finiteHistorySelectorForward119_eq_p50 internalZeroSymbolEnvironment]
  rw [scientificFiniteP15_flatten_eq_clean119]
  rw [finiteRepairedH3Circuit119_eq_certified]
  rw [finiteHistorySelectorInverse119_eq_p50 internalZeroSymbolEnvironment]
  rfl

end

end ExecutableHistoryExecutableHistory
