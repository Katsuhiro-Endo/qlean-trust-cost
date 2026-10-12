import QLean.Spectral.Analysis.HistoryH4CorrectedCleanSpecifications
import QLean.Spectral.Circuits.HistoryBlock
import QLean.Spectral.Circuits.HistoryP15FullClean
import QLean.Spectral.Circuits.HistoryP15H2CleanBridge
import QLean.Spectral.Circuits.HistoryClockCleanRestoredStrong

/-!
# Corrected clean H4 composition

This leaf is deliberately independent of the historical H4 dirty composition
and of the historical monolithic implementation wrapper.  Its H3 bridge names the literal repaired source
word supplied by `HistoryClockCleanRestoredStrong` and connects it to the pure
corrected-H4 specification.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

/-- The pure corrected-H3 specification instantiated by the actual repaired
H3 source.  I05 remains internal to I06 and is not a top-level source child.
-/
noncomputable def historyH3CorrectedCleanSpecification
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryClockConcreteSourceOrderEvidence layout) :
    H3CorrectedCleanSpecification qubits where
  i01SelectorEquality :=
    (historySelectorEqualityClassicalStage layout).analyticOperator
  i02OrderUniformPreparationInverse :=
    ExternallyControlledPrimitivePlan.semanticPlanOperator (fun _ => 0)
      (historyOrderUniformExternalControlLayout layout
        evidence.uniformExternalControl)
      (shuklaVedulaWidthOnlyUniformInversePlan
        (historyOrderUniformPreparationParameters parameters))
  i03IdleTransform :=
    historyIdleTransformOperator layout
      evidence.idleTransform.active_ne_coefficient
      evidence.idleCoefficientAngle.uniformValue
  i04CoefficientRotation :=
    embedControlledSingleQubitOperator (historyActiveWire layout)
      layout.coefficientSignal evidence.coefficientControl_ne_signal
      (localRy evidence.coefficientAngle.uniformValue)
  i06ProjectorControl := historyProjectorControlOperator layout
  i07ControlledClockIncrement :=
    controlledAddConstantMod2PowSemanticOperator
      (historyControlledClockIncrementSpec layout evidence.controlledIncrement)
  cleanPredicate := historyClockBranchUncomputedStrongOutputPredicate layout

/-- Assemble the pure corrected H4 specification from independently supplied
H1/H2 human specifications and the repaired concrete H3 specification.  The
P15-to-H2 bridge is intentionally supplied in a later component theorem;
this definition does not turn a component target into a specification field.
-/
noncomputable def historyH4CorrectedCleanSpecificationOf
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (selector : H1SelectorUnderstandingSpecification qubits)
    (taylor : H2TaylorUnderstandingSpecification qubits)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (clockEvidence : HistoryClockConcreteSourceOrderEvidence layout) :
    H4CorrectedCleanSpecification qubits where
  selector := selector
  taylor := taylor
  correctedClock := historyH3CorrectedCleanSpecification layout clockEvidence

/-- The H1 mathematical object used by the corrected H4 composition.  It is
defined locally so this leaf remains independent of the historical monolithic
H4 implementation link. -/
noncomputable def historyH4CorrectedSelectorSpecification
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    H1SelectorUnderstandingSpecification qubits where
  symbolValue := symbolValue
  parameters := parameters

/-- Coherent H1 preparation between arbitrary basis predicates whose values
outside the two selector wires have the stated forward stability.  This is
the superposition-safe wrapper used for the corrected H4 first child. -/
noncomputable def historyH4CorrectedSelectorForwardOutsideSupportComponent
    {qubits : Nat}
    (spec : H1SelectorUnderstandingSpecification qubits)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (predicateStable : ∀ input output,
      inputPredicate input →
      (∀ wire, wire ∉ historySelectorPreparationSupport spec.parameters →
        output wire = input wire) →
      outputPredicate output) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) spec.symbolValue) :=
  let child := historySelectorPreparationP50ComposedExactComponent
    spec.symbolValue spec.parameters
  let refined := child.refineTarget (h1SelectorRecordedOperator spec) (by
    rfl)
  refined.toSubspaceMapOfOutsideSupport
    (historySelectorPreparationSupport spec.parameters)
    (by
      change OperatorPreservesOutside
        (historySelectorPreparationSupport spec.parameters)
        (h1SelectorRecordedOperator spec)
      exact historySelectorPreparationOperator_preservesOutside
        spec.symbolValue spec.parameters)
    inputPredicate outputPredicate predicateStable

/-- A data, generator-signal, or workspace wire is outside the two frozen H1
selector wires.  The proof uses the single layout `Nodup` certificate rather
than a basis-state argument, so it can be used to protect coherent spans. -/
theorem historyH4Corrected_nonselectorWire_not_mem_selectorSupport
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (firstHighAngle firstLowAngle secondLowAngle : AngleExpr)
    (wire : Fin qubits)
    (outside : wire ∈ historyRegisterWires layout.data ∨
      wire ∈ historyRegisterWires layout.generatorSignal ∨
      wire ∈ historyRegisterWires layout.workspace) :
    wire ∉ historySelectorPreparationSupport
      (historySelectorPreparationParametersAtLayout layout firstHighAngle
        firstLowAngle secondLowAngle) := by
  rw [historySelectorPreparationParametersAtLayout_support]
  let selectorWires := historyRegisterWires layout.selector
  let dataWires := historyRegisterWires layout.data
  let clockWires := historyRegisterWires layout.clock
  let orderWires := historyRegisterWires layout.order
  let generatorWires := historyRegisterWires layout.generatorSignal
  let reservedWires := [layout.coefficientSignal, layout.orderBoundarySignal,
    layout.projectorSignal, layout.clockBoundarySignal]
  let workspaceWires := historyRegisterWires layout.workspace
  have normalized :
      (selectorWires ++ (dataWires ++ (clockWires ++ (orderWires ++
        (generatorWires ++ (reservedWires ++ workspaceWires)))))).Nodup := by
    simpa [selectorWires, dataWires, clockWires, orderWires, generatorWires,
      reservedWires, workspaceWires, List.append_assoc] using
      layout.allWiresNodup
  have selectorSplit := List.nodup_append.mp normalized
  have tailMember : wire ∈ dataWires ++ (clockWires ++ (orderWires ++
      (generatorWires ++ (reservedWires ++ workspaceWires)))) := by
    rcases outside with dataMember | generatorMember | workspaceMember
    · exact List.mem_append_left _ (by simpa [dataWires] using dataMember)
    · exact List.mem_append_right dataWires
        (List.mem_append_right clockWires
          (List.mem_append_right orderWires
            (List.mem_append_left _ (by
              simpa [generatorWires] using generatorMember))))
    · exact List.mem_append_right dataWires
        (List.mem_append_right clockWires
          (List.mem_append_right orderWires
            (List.mem_append_right generatorWires
              (List.mem_append_right reservedWires (by
                simpa [workspaceWires] using workspaceMember)))))
  have selectorMember (index : Fin 2) :
      layout.selector.wire index ∈ selectorWires := by
    simpa [selectorWires, historyRegisterWires] using
      (List.mem_ofFn.mpr ⟨index, rfl⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · intro equal
    exact selectorSplit.2.2 _ (selectorMember 0) _ tailMember equal.symm
  · intro equal
    exact selectorSplit.2.2 _ (selectorMember 1) _ tailMember equal.symm

/-- Every physical wire selected by the frozen P15 Q10 placement is outside
H1's support.  This is the exact non-overlap needed for the H1 preparation to
preserve the all-zero Q10 input predicate on arbitrary superpositions. -/
theorem historyH4Corrected_p15Placement_not_mem_selectorSupport
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (firstHighAngle firstLowAngle secondLowAngle : AngleExpr)
    (source : Fin (p.ancillaWidth + p.systemWidth)) :
    (historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths).placement.embedding.placement source ∉
      historySelectorPreparationSupport
        (historySelectorPreparationParametersAtLayout layout firstHighAngle
          firstLowAngle secondLowAngle) := by
  have placedMember :
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := layout) widths).placement.embedding.placement source ∈
        List.ofFn (historyP15Q10ControlEvidence_ofFrozenLayout
          (layout := layout) widths).placement.embedding.placement := by
    exact List.mem_ofFn.mpr ⟨source, rfl⟩
  rw [historyP15Q10Placement_sourceOrder (layout := layout) widths] at placedMember
  rcases List.mem_append.mp placedMember with initialMember | dataMember
  · rcases List.mem_append.mp initialMember with signalMember | workMember
    · exact historyH4Corrected_nonselectorWire_not_mem_selectorSupport layout
        firstHighAngle firstLowAngle secondLowAngle _ (Or.inr (Or.inl signalMember))
    · refine historyH4Corrected_nonselectorWire_not_mem_selectorSupport layout
        firstHighAngle firstLowAngle secondLowAngle _ (Or.inr (Or.inr ?_))
      rcases List.mem_ofFn.mp workMember with ⟨index, equal⟩
      rw [← equal]
      exact historyGeneratorWorkRegister_wire_mem_workspace layout index
  · exact historyH4Corrected_nonselectorWire_not_mem_selectorSupport layout
      firstHighAngle firstLowAngle secondLowAngle _ (Or.inl dataMember)

/-- Concrete H1 specification at the frozen history layout. -/
noncomputable def historyH4CorrectedConcreteSelectorSpecification
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (firstHighAngle firstLowAngle secondLowAngle : AngleExpr) :
    H1SelectorUnderstandingSpecification qubits :=
  historyH4CorrectedSelectorSpecification ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (historySelectorPreparationParametersAtLayout layout firstHighAngle
      firstLowAngle secondLowAngle)

/-- Concrete pure H2 specification reconstructed directly from P15. -/
noncomputable def historyH4CorrectedConcreteTaylorSpecification
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr) :
    H2TaylorUnderstandingSpecification qubits :=
  historyP15H2CleanUnderstandingSpecification layout evidence widths angles idleAngle

/-- Fully concrete corrected-H4 pure specification.  Its source is the
independent H1/H2/corrected-H3 product, not an implementation component
target. -/
noncomputable def historyH4CorrectedConcreteSpecification
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (p15Evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (firstHighAngle firstLowAngle secondLowAngle : AngleExpr)
    (clockEvidence : HistoryClockConcreteSourceOrderEvidence layout) :
    H4CorrectedCleanSpecification qubits :=
  historyH4CorrectedCleanSpecificationOf
    (historyH4CorrectedConcreteSelectorSpecification layout firstHighAngle
      firstLowAngle secondLowAngle)
    (historyH4CorrectedConcreteTaylorSpecification layout p15Evidence widths
      angles idleAngle)
    layout clockEvidence

/-- The initial pure H4 predicate can be retyped to the P15 full-clean input
boundary.  H1 changes only the selector, and P15's actual Q10 input wires are
all outside that support. -/
theorem historyH4CorrectedIdealInput_stable_to_historyP15FullCleanInput
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (p15Evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (firstHighAngle firstLowAngle secondLowAngle : AngleExpr)
    (clockEvidence : HistoryClockConcreteSourceOrderEvidence layout)
    (input output : QubitBasis qubits)
    (inside : h4CorrectedIdealInputPredicate
      (historyH4CorrectedConcreteSpecification layout p15Evidence widths
        angles idleAngle firstHighAngle firstLowAngle secondLowAngle clockEvidence)
      input)
    (unchanged : ∀ wire,
      wire ∉ historySelectorPreparationSupport
        (historySelectorPreparationParametersAtLayout layout firstHighAngle
          firstLowAngle secondLowAngle) → output wire = input wire) :
    historyP15FullCleanInputPredicate (layout := layout) widths output := by
  have h2Input : h2TaylorIdealInputPredicate
      (historyH4CorrectedConcreteTaylorSpecification layout p15Evidence widths
        angles idleAngle) input := by
    simpa [h4CorrectedIdealInputPredicate,
      historyH4CorrectedConcreteSpecification,
      historyH4CorrectedCleanSpecificationOf] using inside.1
  have p15Input : historyP15FullCleanInputPredicate (layout := layout) widths input := by
    rw [← h2TaylorIdealInputPredicate_eq_historyP15FullCleanInputPredicate
      layout p15Evidence widths angles idleAngle]
    exact h2Input
  unfold historyP15FullCleanInputPredicate historyP15WithQ10Input at p15Input ⊢
  constructor
  · intro workspaceIndex
    rw [unchanged (layout.workspace.wire workspaceIndex)]
    · exact p15Input.1 workspaceIndex
    · rw [historySelectorPreparationParametersAtLayout_support]
      exact layout.workspace_wire_not_mem_selector_support _
        (List.mem_ofFn.mpr ⟨workspaceIndex, rfl⟩)
  · unfold historyP15Q10PlacedInputPredicate
      externallyControlledPlacedInputPredicate at p15Input ⊢
    constructor
    · rw [externallyControlledCleanWorkPredicate_iff_controlWork_zero] at p15Input ⊢
      intro wire member
      rw [unchanged wire]
      · exact p15Input.2.1 wire member
      · rw [historyP15Q10Placement_compilerWork] at member
        rw [historySelectorPreparationParametersAtLayout_support]
        exact layout.workspace_wire_not_mem_selector_support _
          (historyControlledWorkWire_mem_workspace layout wire member)
    · have restrictedEq :
          restrictToPlacedWires
              (historyP15Q10ControlEvidence_ofFrozenLayout
                (layout := layout) widths).placement.externalLayout.placement output =
            restrictToPlacedWires
              (historyP15Q10ControlEvidence_ofFrozenLayout
                (layout := layout) widths).placement.externalLayout.placement input := by
        funext source
        apply unchanged
        change (historyP15Q10ControlEvidence_ofFrozenLayout
          (layout := layout) widths).placement.embedding.placement source ∉
            historySelectorPreparationSupport
              (historySelectorPreparationParametersAtLayout layout firstHighAngle
                firstLowAngle secondLowAngle)
        exact historyH4Corrected_p15Placement_not_mem_selectorSupport
          layout widths firstHighAngle firstLowAngle secondLowAngle source
      rw [restrictedEq]
      exact p15Input.2.2

/-- The actual H1 preparation, viewed coherently from the independent H4
ideal boundary to the concrete P15 full-clean entrance. -/
noncomputable def historyH4CorrectedSelectorForwardComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (p15Evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (firstHighAngle firstLowAngle secondLowAngle : AngleExpr)
    (clockEvidence : HistoryClockConcreteSourceOrderEvidence layout) :=
  historyH4CorrectedSelectorForwardOutsideSupportComponent
    (historyH4CorrectedConcreteSelectorSpecification layout firstHighAngle
      firstLowAngle secondLowAngle)
    (h4CorrectedIdealInputPredicate
      (historyH4CorrectedConcreteSpecification layout p15Evidence widths angles
        idleAngle firstHighAngle firstLowAngle secondLowAngle clockEvidence))
    (historyP15FullCleanInputPredicate (layout := layout) widths)
    (historyH4CorrectedIdealInput_stable_to_historyP15FullCleanInput layout
      p15Evidence widths angles idleAngle firstHighAngle firstLowAngle
      secondLowAngle clockEvidence)

@[simp] theorem historyH4CorrectedSelectorForwardComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (p15Evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (firstHighAngle firstLowAngle secondLowAngle : AngleExpr)
    (clockEvidence : HistoryClockConcreteSourceOrderEvidence layout) :
    (historyH4CorrectedSelectorForwardComponent layout p15Evidence widths angles
      idleAngle firstHighAngle firstLowAngle secondLowAngle clockEvidence).target =
      h1SelectorRecordedOperator
        (historyH4CorrectedConcreteSelectorSpecification layout firstHighAngle
          firstLowAngle secondLowAngle) := rfl

/-! ## Fully concrete corrected H4 -/

end

end SpectralSamplingProof.Components
