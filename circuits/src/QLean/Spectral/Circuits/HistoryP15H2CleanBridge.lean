import QLean.Spectral.Analysis.HistoryUnderstandingSpecifications
import QLean.Spectral.Circuits.HistoryP15FullClean
import QLean.Spectral.Circuits.HistoryP15CoefficientPureBridge

/-!
# P15 full-clean / H2 mathematical specification bridge

This is a deliberately narrow bridge.  It constructs the human-facing H2
specification directly from the concrete P15 layout evidence, placement widths,
and coefficient angles.  In particular, it does not import the historical
`HistoryTaylorBlock` implementation wrapper or its H2 specification link.

The H2 clean word is kept as thirteen independently named source groups:
the four pre-Q10 groups, the unique controlled-Q10 meaning, and the eight
post-Q10 groups.  The final theorem identifies that flat H2 word with the
actual nested P15 clean target.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

/-- The controlled-Q10 mathematical contract obtained solely from the frozen
P15 placement.  This is the P15 specialization of the generic H2 contract;
its plan and its clean-work boundary come from the public Q10 component, not
from an additional semantic-existence assumption. -/
noncomputable def historyP15ControlledQ10UnderstandingSpecification
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (p : ProbabilityGeneratorQProof.QParameters)
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    H2ControlledQ10UnderstandingSpecification qubits := by
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  refine {
    p := p
    symbolValue := ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    layout := evidence.placement.externalLayout
    cleanWorkValid := evidence.cleanWorkValid
    plan := (historyTaylorQ10ExternallyControlledCertificate p).plan
    sourceReindex := ProbabilityGeneratorQProof.reindexJointOperatorToCanonicalCore
    sourcePlan_eq_q10 := ?_
    sourceInputPredicate :=
      ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate p
    sourceOutputPredicate :=
      ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p
    sourceInputImpliesOutput :=
      ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate_implies_workClean p
    sourceBoundary := ?_
    signalWires := historyRegisterWires layout.generatorSignal
    generatorWorkWires :=
      historyRegisterWires (historyGeneratorWorkRegister layout)
    dataWires := historyRegisterWires layout.data
    signalWires_length := by
      simpa [historyRegisterWires] using evidence.placement.widths.signal_eq
    generatorWorkWires_length := by
      simpa [historyRegisterWires] using evidence.placement.widths.work_eq
    dataWires_length := by
      simpa [historyRegisterWires] using evidence.placement.widths.data_eq
    placementSourceOrder := evidence.placement.placement_sourceOrder }
  · calc
      r12ControlledSubcircuitSourceOperator
          ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
          (historyTaylorQ10ExternallyControlledCertificate p).plan =
          Circuit.denote
            (primitiveGateOperatorWithSymbols (qubits := p.ancillaWidth + p.systemWidth)
              ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
            (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent
              p).circuit :=
        by
          simpa [r12ControlledSubcircuitSourceOperator] using
            (historyTaylorProbabilityGeneratorSourcePlan_eq_qCircuitDenote p)
      _ = (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent
              p).target :=
        (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent
          p).correct
      _ = ProbabilityGeneratorQProof.reindexJointOperatorToCanonicalCore
          (ProbabilityGeneratorQProof.ProbabilityGeneratorFullAnalyticOperator p) := rfl
      _ = ProbabilityGeneratorQProof.reindexJointOperatorToCanonicalCore
          (ProbabilityGeneratorQProof.q10ProbabilityGeneratorRecordedOperator p) :=
        congrArg ProbabilityGeneratorQProof.reindexJointOperatorToCanonicalCore
          (ProbabilityGeneratorQProof.q10ProbabilityGeneratorRecordedOperator_eq_established
            p).symm
  · intro input output inputZero outputDirty
    simpa [r12ControlledSubcircuitSourceOperator] using
      (historyTaylorProbabilityGeneratorSourcePlan_maps_of_q10CleanChild p
        (q10CanonicalCleanChild p).correct
        (q10CanonicalCleanChild p).target_maps
        input output inputZero outputDirty)

/-- The P15-specialized H2 human-facing specification.  Every clean group is
the target of the corresponding P15 source group, so the construction retains
the literal source order even though P15 packages its eight post-Q10 groups
inside one child component. -/
noncomputable def historyP15H2CleanUnderstandingSpecification
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (_evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr) :
    H2TaylorUnderstandingSpecification qubits where
  beforeControlledQ10 :=
    [{ family := .selectorEquality
       leafContract := .equality
       target := historyTaylorSelectorEqualityOperator layout
       cleanTarget := historyTaylorSelectorEqualityOperator layout },
     { family := .clockPredicate
       leafContract := .lessThan
       target := historyTaylorTimeComparisonOperator layout
       cleanTarget := historyTaylorTimeComparisonOperator layout },
     { family := .clockPredicate
       leafContract := .lessThan
       target := historyTaylorIdleEndComparisonOperator layout
       cleanTarget := historyTaylorIdleEndComparisonOperator layout },
     { family := .controlledLogic
       leafContract := .conjunction
       target := historyTaylorActiveConjunctionOperator layout
       cleanTarget := historyTaylorActiveConjunctionOperator layout }]
  controlledQ10 :=
    historyP15ControlledQ10UnderstandingSpecification p layout widths
  postGenerator :=
    { restoreGeneratorActive :=
        [{ family := .controlledLogic
           leafContract := .conjunction
           target := historyTaylorActiveConjunctionOperator layout
           cleanTarget := historyTaylorActiveConjunctionOperator layout }]
      invalidClockSignal :=
        [{ family := .clockPredicate
           leafContract := .lessThan
           target := historyTaylorInvalidClockOperator layout
           cleanTarget := historyTaylorInvalidClockOperator layout }]
      orderBoundarySignal :=
        [{ family := .orderBoundaryPredicate
           leafContract := .equality
           target := historyTaylorOrderBoundaryOperator layout
           cleanTarget := historyTaylorOrderBoundaryOperator layout }]
      idleBoundarySignal :=
        [{ family := .orderBoundaryPredicate
           leafContract := .equality
           target := historyTaylorIdleBoundaryOperator layout
           cleanTarget := historyTaylorIdleBoundaryOperator layout }]
      degreeIncrement :=
        [{ family := .orderIncrement
           leafContract := .controlledIncrement
           target := historyTaylorDegreeIncrementOperator layout
           cleanTarget := historyTaylorDegreeIncrementOperator layout }]
      taylorCoefficientRotations :=
        [{ family := .coefficientRotation
           leafContract := .controlledRotation
           target := historyTaylorCoefficientLoopOperator layout angles
           cleanTarget := historyTaylorCoefficientLoopOperator layout angles }]
      idleCoefficientRotation :=
        [{ family := .idlingCoefficientRotation
           leafContract := .controlledRotation
           target := historyTaylorIdleCoefficientOperator layout idleAngle
           cleanTarget := historyTaylorIdleCoefficientOperator layout idleAngle }]
      restoreEntryFlags :=
        [{ family := .controlledLogic
           leafContract := .equality
           target := operatorSequence
             [historyTaylorIdleEndComparisonOperator layout,
              historyTaylorTimeComparisonOperator layout,
              historyTaylorSelectorEqualityOperator layout]
           cleanTarget := operatorSequence
             [historyTaylorIdleEndComparisonOperator layout,
              historyTaylorTimeComparisonOperator layout,
              historyTaylorSelectorEqualityOperator layout] }]
      restoreGeneratorActiveClean := historyTaylorActiveConjunctionOperator layout
      invalidClockSignalClean := historyTaylorInvalidClockOperator layout
      orderBoundarySignalClean := historyTaylorOrderBoundaryOperator layout
      idleBoundarySignalClean := historyTaylorIdleBoundaryOperator layout
      degreeIncrementClean := historyTaylorDegreeIncrementOperator layout
      taylorCoefficientRotationsClean :=
        historyTaylorCoefficientLoopOperator layout angles
      idleCoefficientRotationClean :=
        historyTaylorIdleCoefficientOperator layout idleAngle
      restoreEntryFlagsClean := operatorSequence
        [historyTaylorIdleEndComparisonOperator layout,
         historyTaylorTimeComparisonOperator layout,
         historyTaylorSelectorEqualityOperator layout] }
  auxiliaryBoundaryPredicate := historyTaylorAuxiliaryBoundaryPredicate layout
  afterSelectorPredicate := historyTaylorAfterSelectorPredicate layout
  afterTimeComparisonPredicate := historyTaylorAfterTimeComparisonPredicate layout
  afterIdleEndComparisonPredicate :=
    historyTaylorAfterIdleEndComparisonPredicate layout
  centralAuxiliaryPredicate := historyTaylorBeforeGeneratorBoundaryPredicate layout
  postGeneratorStablePredicate := historyTaylorPostGeneratorStablePredicate layout

/-- The unique controlled-Q10 target in the P15 source is definitionally the
clean controlled meaning installed in the concrete H2 specification. -/
theorem historyP15Q10LiveBoundary_target_eq_h2ControlledClean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15Q10LiveBoundarySubspaceMapComponent layout widths).target =
      h2ControlledQ10CleanOperator
        (historyP15ControlledQ10UnderstandingSpecification p layout widths) := by
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  change (historyP15Q10LiveBoundarySubspaceMapComponent layout widths).target =
    ExternallyControlledPrimitivePlan.semanticPlanOperator
      ProbabilityGeneratorQProof.internalZeroSymbolEnvironment evidence.placement.externalLayout
      (historyTaylorQ10ExternallyControlledCertificate p).plan
  unfold historyP15Q10LiveBoundarySubspaceMapComponent
  rw [SubspaceMapComponent.restrictBasisSpanWithInvariant_target]
  exact historyTaylorControlledProbabilityGeneratorQ10CleanBoundary_target
    p evidence

/-- The H2 ideal input boundary reconstructed from P15 is exactly the public
P15 full-clean entrance.  The two definitions merely order the independent
auxiliary and Q10 conjuncts differently. -/
theorem h2TaylorIdealInputPredicate_eq_historyP15FullCleanInputPredicate
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
    h2TaylorIdealInputPredicate
        (historyP15H2CleanUnderstandingSpecification layout evidence widths
          angles idleAngle) =
      historyP15FullCleanInputPredicate (layout := layout) widths := by
  funext basis
  unfold h2TaylorIdealInputPredicate h2ControlledQ10IdealInputPredicate
    h2ControlledQ10CleanPredicate
    h2ControlledQ10BlockEncodingInputPredicate
    historyP15FullCleanInputPredicate historyP15WithQ10Input
    historyP15Q10PlacedInputPredicate
    historyP15H2CleanUnderstandingSpecification
    historyP15ControlledQ10UnderstandingSpecification
    externallyControlledPlacedInputPredicate
  simp only [and_comm]

/-- The P15-specialized H2 clean source list, made explicit so later circuit
composition never needs to unfold the human-facing record. -/
theorem h2TaylorCleanSourceOperators_historyP15_eq
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
    h2TaylorCleanSourceOperators
        (historyP15H2CleanUnderstandingSpecification layout evidence widths
          angles idleAngle) =
      [historyTaylorSelectorEqualityOperator layout,
       historyTaylorTimeComparisonOperator layout,
       historyTaylorIdleEndComparisonOperator layout,
       historyTaylorActiveConjunctionOperator layout,
       h2ControlledQ10CleanOperator
         (historyP15ControlledQ10UnderstandingSpecification p layout widths),
       historyTaylorActiveConjunctionOperator layout,
       historyTaylorInvalidClockOperator layout,
       historyTaylorOrderBoundaryOperator layout,
       historyTaylorIdleBoundaryOperator layout,
       historyTaylorDegreeIncrementOperator layout,
       historyTaylorCoefficientLoopOperator layout angles,
       historyTaylorIdleCoefficientOperator layout idleAngle,
       operatorSequence [historyTaylorIdleEndComparisonOperator layout,
         historyTaylorTimeComparisonOperator layout,
         historyTaylorSelectorEqualityOperator layout]] := by
  rfl

/-! ## Non-coefficient target bridges -/

/-- The first P15 pre-Q10 source group already has the pure H2 meaning. -/
theorem historyP15SelectorEqualityWithQ10_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15SelectorEqualityWithQ10Component layout widths).target =
      historyTaylorSelectorEqualityOperator layout := rfl

theorem historyP15TimeComparisonWithQ10_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15TimeComparisonWithQ10Component layout evidence.clock widths).target =
      historyTaylorTimeComparisonOperator layout := rfl

theorem historyP15IdleEndComparisonWithQ10_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15IdleEndComparisonWithQ10Component layout evidence.clock widths).target =
      historyTaylorIdleEndComparisonOperator layout := rfl

theorem historyP15ActiveConjunctionWithQ10_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15ActiveConjunctionWithQ10Component layout widths).target =
      historyTaylorActiveConjunctionOperator layout := rfl

theorem historyP15RestoreGeneratorActive_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreGeneratorActiveComponent layout widths).target =
      historyTaylorActiveConjunctionOperator layout := rfl

theorem historyP15InvalidClock_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15InvalidClockComponent layout evidence widths).target =
      historyTaylorInvalidClockOperator layout := rfl

theorem historyP15OrderBoundary_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15OrderBoundaryComponent layout widths).target =
      historyTaylorOrderBoundaryOperator layout := rfl

theorem historyP15IdleBoundary_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15IdleBoundaryComponent layout widths).target =
      historyTaylorIdleBoundaryOperator layout := rfl

theorem historyP15DegreeIncrement_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15DegreeIncrementComponent layout widths).target =
      historyTaylorDegreeIncrementOperator layout := rfl

theorem historyP15IdleCoefficient_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (idleAngle : AngleExpr) :
    (historyP15IdleCoefficientComponent layout widths idleAngle).target =
      historyTaylorIdleCoefficientOperator layout idleAngle := rfl

theorem historyP15RestoreEntryFlags_target_eq_pure
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsComponent layout evidence widths).target =
      operatorSequence [historyTaylorIdleEndComparisonOperator layout,
        historyTaylorTimeComparisonOperator layout,
        historyTaylorSelectorEqualityOperator layout] := by
  rw [historyP15RestoreEntryFlagsComponent_target,
    historyP15RestoreEntryFlagsOperator_eq_analyticSequence]

/-- The four pure pre-Q10 targets and the unique clean-Q10 target are already
an equality of operators, not merely an equality on a clean sector. -/
theorem historyP15ThroughQ10_target_eq_h2CleanPrefix
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15ThroughQ10SubspaceMapComponent layout evidence.clock widths).target =
      operatorSequence
        [historyTaylorSelectorEqualityOperator layout,
         historyTaylorTimeComparisonOperator layout,
         historyTaylorIdleEndComparisonOperator layout,
         historyTaylorActiveConjunctionOperator layout,
         h2ControlledQ10CleanOperator
           (historyP15ControlledQ10UnderstandingSpecification p layout widths)] := by
  unfold historyP15ThroughQ10SubspaceMapComponent
  rw [SubspaceMapComponent.sequenceAlong_target]
  simp only [historyP15ThroughQ10Components,
    historyP15PreQ10WithInvariantComponents, List.map_append,
    List.map_cons, List.map_nil]
  rw [historyP15SelectorEqualityWithQ10_target_eq_pure layout widths,
    historyP15TimeComparisonWithQ10_target_eq_pure layout evidence widths,
    historyP15IdleEndComparisonWithQ10_target_eq_pure layout evidence widths,
    historyP15ActiveConjunctionWithQ10_target_eq_pure layout widths,
    historyP15Q10LiveBoundary_target_eq_h2ControlledClean layout widths]
  rfl

noncomputable def historyP15ThroughQ10ComponentRefinedToH2
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits)
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment) :=
  (historyP15ThroughQ10SubspaceMapComponent layout evidence.clock widths).refineTarget
    (operatorSequence
      [historyTaylorSelectorEqualityOperator layout,
       historyTaylorTimeComparisonOperator layout,
       historyTaylorIdleEndComparisonOperator layout,
       historyTaylorActiveConjunctionOperator layout,
       h2ControlledQ10CleanOperator
         (historyP15ControlledQ10UnderstandingSpecification p layout widths)])
    (historyP15ThroughQ10_target_eq_h2CleanPrefix layout evidence widths)

@[simp] theorem historyP15ThroughQ10ComponentRefinedToH2_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15ThroughQ10ComponentRefinedToH2 layout evidence widths).target =
      operatorSequence
        [historyTaylorSelectorEqualityOperator layout,
         historyTaylorTimeComparisonOperator layout,
         historyTaylorIdleEndComparisonOperator layout,
         historyTaylorActiveConjunctionOperator layout,
         h2ControlledQ10CleanOperator
           (historyP15ControlledQ10UnderstandingSpecification p layout widths)] := rfl

/-- The only non-definitional group bridge required to assemble full H2. -/
def historyP15TaylorCoefficientBasisAgreement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) : Prop :=
  ∀ input,
    historyP15PostQ10StablePredicate (layout := layout) widths input ->
      applyOperator
          (historyP15TaylorCoefficientComponent layout widths angles).target
          (basisKet input) =
        applyOperator (historyTaylorCoefficientLoopOperator layout angles)
          (basisKet input)

/-- Lift the one non-definitional coefficient comparison from stable basis
kets to a coherent component, preserving the literal P15 circuit and stable
P0/P1 boundary. -/
noncomputable def historyP15TaylorCoefficientComponentRefinedToH2OfBasisAgreement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr)
    (basisAgreement : ∀ input,
      historyP15PostQ10StablePredicate (layout := layout) widths input ->
        applyOperator
            (historyP15TaylorCoefficientComponent layout widths angles).target
            (basisKet input) =
          applyOperator (historyTaylorCoefficientLoopOperator layout angles)
            (basisKet input)) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits)
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment) :=
  SubspaceMapComponent.ofBasisSpan
    (primitiveGateOperatorWithSymbols (qubits := qubits)
      ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
    (historyP15TaylorCoefficientComponent layout widths angles).circuit
    (historyTaylorCoefficientLoopOperator layout angles)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (by
      intro input inside
      calc
        applyOperator
            (Circuit.denote
              (primitiveGateOperatorWithSymbols (qubits := qubits)
                ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
              (historyP15TaylorCoefficientComponent layout widths angles).circuit)
            (basisKet input) =
            applyOperator
              (historyP15TaylorCoefficientComponent layout widths angles).target
              (basisKet input) :=
          (historyP15TaylorCoefficientComponent layout widths angles).correct _
            (SubspaceMapComponent.basisKet_mem_basisSpan inside)
        _ = applyOperator (historyTaylorCoefficientLoopOperator layout angles)
              (basisKet input) :=
          basisAgreement input inside)
    (by
      intro input inside
      rw [← basisAgreement input inside]
      exact (historyP15TaylorCoefficientComponent layout widths angles).target_maps _
        (SubspaceMapComponent.basisKet_mem_basisSpan inside))

/-- The eight P15 post-Q10 circuits, with only the coefficient child retargeted
on its stable sector.  All other target replacements are operator equalities. -/
noncomputable def historyP15PostQ10H2CleanComponentsOfCoefficientAgreement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :
    List (SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits)
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)) :=
  [(historyP15RestoreGeneratorActiveComponent layout widths).refineTarget
      (historyTaylorActiveConjunctionOperator layout)
      (historyP15RestoreGeneratorActive_target_eq_pure layout widths),
   (historyP15InvalidClockComponent layout evidence widths).refineTarget
      (historyTaylorInvalidClockOperator layout)
      (historyP15InvalidClock_target_eq_pure layout evidence widths),
   (historyP15OrderBoundaryComponent layout widths).refineTarget
      (historyTaylorOrderBoundaryOperator layout)
      (historyP15OrderBoundary_target_eq_pure layout widths),
   (historyP15IdleBoundaryComponent layout widths).refineTarget
      (historyTaylorIdleBoundaryOperator layout)
      (historyP15IdleBoundary_target_eq_pure layout widths),
   (historyP15DegreeIncrementComponent layout widths).refineTarget
      (historyTaylorDegreeIncrementOperator layout)
      (historyP15DegreeIncrement_target_eq_pure layout widths),
   historyP15TaylorCoefficientComponentRefinedToH2OfBasisAgreement
      layout widths angles coefficientAgreement,
   (historyP15IdleCoefficientComponent layout widths idleAngle).refineTarget
      (historyTaylorIdleCoefficientOperator layout idleAngle)
      (historyP15IdleCoefficient_target_eq_pure layout widths idleAngle),
   (historyP15RestoreEntryFlagsComponent layout evidence widths).refineTarget
      (operatorSequence [historyTaylorIdleEndComparisonOperator layout,
        historyTaylorTimeComparisonOperator layout,
        historyTaylorSelectorEqualityOperator layout])
      (historyP15RestoreEntryFlags_target_eq_pure layout evidence widths)]

theorem historyP15PostQ10H2CleanComponentsOfCoefficientAgreement_chain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :
    SubspaceMapComponent.SpaceChain
      (historyP15PostQ10H2CleanComponentsOfCoefficientAgreement
        layout evidence widths angles idleAngle coefficientAgreement)
      (SubspaceMapComponent.basisSpan
        (historyP15PostQ10CleanInputPredicate (layout := layout) widths))
      (SubspaceMapComponent.basisSpan
        (historyP15PostQ10CleanOutputPredicate (layout := layout) widths)) := by
  exact .cons _ [_, _, _, _, _, _, _] _ _ _ rfl rfl
    (.cons _ [_, _, _, _, _, _] _ _ _ rfl rfl
      (.cons _ [_, _, _, _, _] _ _ _ rfl rfl
        (.cons _ [_, _, _, _] _ _ _ rfl rfl
          (.cons _ [_, _, _] _ _ _ rfl rfl
            (.cons _ [_, _] _ _ _ rfl rfl
              (.cons _ [_] _ _ _ rfl rfl
                (.cons _ [] _ _ _ rfl rfl (.nil _))))))))

noncomputable def historyP15PostQ10CleanComponentRefinedToH2OfCoefficientAgreement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :=
  SubspaceMapComponent.sequenceAlong
    (historyP15PostQ10H2CleanComponentsOfCoefficientAgreement_chain
      layout evidence widths angles idleAngle coefficientAgreement)

@[simp] theorem historyP15PostQ10CleanComponentRefinedToH2OfCoefficientAgreement_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :
    (historyP15PostQ10CleanComponentRefinedToH2OfCoefficientAgreement
      layout evidence widths angles idleAngle coefficientAgreement).target =
      operatorSequence
        [historyTaylorActiveConjunctionOperator layout,
         historyTaylorInvalidClockOperator layout,
         historyTaylorOrderBoundaryOperator layout,
         historyTaylorIdleBoundaryOperator layout,
         historyTaylorDegreeIncrementOperator layout,
         historyTaylorCoefficientLoopOperator layout angles,
         historyTaylorIdleCoefficientOperator layout idleAngle,
         operatorSequence [historyTaylorIdleEndComparisonOperator layout,
           historyTaylorTimeComparisonOperator layout,
           historyTaylorSelectorEqualityOperator layout]] := by
  unfold historyP15PostQ10CleanComponentRefinedToH2OfCoefficientAgreement
  rw [SubspaceMapComponent.sequenceAlong_target]
  rfl

@[simp] theorem historyP15PostQ10CleanComponentRefinedToH2OfCoefficientAgreement_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :
    (historyP15PostQ10CleanComponentRefinedToH2OfCoefficientAgreement
      layout evidence widths angles idleAngle coefficientAgreement).circuit =
      (historyP15PostQ10CleanComponent layout evidence widths angles idleAngle).circuit := by
  rfl

/-- The two maximal P15 source regions, retargeted independently to their
pure H2 meanings.  The coefficient hypothesis is confined to the post child. -/
noncomputable def historyP15FullCleanH2TwoChildComponentsOfCoefficientAgreement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :=
  [historyP15ThroughQ10ComponentRefinedToH2 layout evidence widths,
   historyP15PostQ10CleanComponentRefinedToH2OfCoefficientAgreement
     layout evidence widths angles idleAngle coefficientAgreement]

theorem historyP15FullCleanH2TwoChildComponentsOfCoefficientAgreement_chain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :
    SubspaceMapComponent.SpaceChain
      (historyP15FullCleanH2TwoChildComponentsOfCoefficientAgreement
        layout evidence widths angles idleAngle coefficientAgreement)
      (SubspaceMapComponent.basisSpan
        (historyP15FullCleanInputPredicate (layout := layout) widths))
      (SubspaceMapComponent.basisSpan
        (historyP15FullCleanOutputPredicate (layout := layout) widths)) := by
  exact .cons _ [_] _ _ _ rfl rfl
    (.cons _ [] _ _ _ rfl rfl (.nil _))

noncomputable def historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :=
  (SubspaceMapComponent.sequenceAlong
    (historyP15FullCleanH2TwoChildComponentsOfCoefficientAgreement_chain
      layout evidence widths angles idleAngle coefficientAgreement)).refineTarget
    (h2TaylorCleanOperator
      (historyP15H2CleanUnderstandingSpecification layout evidence widths
        angles idleAngle))
    (by
      rw [SubspaceMapComponent.sequenceAlong_target]
      unfold historyP15FullCleanH2TwoChildComponentsOfCoefficientAgreement
      simp only [List.map_cons, List.map_nil]
      rw [historyP15ThroughQ10ComponentRefinedToH2_target,
        historyP15PostQ10CleanComponentRefinedToH2OfCoefficientAgreement_target]
      unfold h2TaylorCleanOperator
      rw [h2TaylorCleanSourceOperators_historyP15_eq]
      change operatorSequence
          [operatorSequence
            [historyTaylorSelectorEqualityOperator layout,
             historyTaylorTimeComparisonOperator layout,
             historyTaylorIdleEndComparisonOperator layout,
             historyTaylorActiveConjunctionOperator layout,
             h2ControlledQ10CleanOperator
               (historyP15ControlledQ10UnderstandingSpecification p layout widths)],
           operatorSequence
            [historyTaylorActiveConjunctionOperator layout,
             historyTaylorInvalidClockOperator layout,
             historyTaylorOrderBoundaryOperator layout,
             historyTaylorIdleBoundaryOperator layout,
             historyTaylorDegreeIncrementOperator layout,
             historyTaylorCoefficientLoopOperator layout angles,
             historyTaylorIdleCoefficientOperator layout idleAngle,
             operatorSequence [historyTaylorIdleEndComparisonOperator layout,
               historyTaylorTimeComparisonOperator layout,
               historyTaylorSelectorEqualityOperator layout]]] =
        operatorSequence
          ([historyTaylorSelectorEqualityOperator layout,
            historyTaylorTimeComparisonOperator layout,
            historyTaylorIdleEndComparisonOperator layout,
            historyTaylorActiveConjunctionOperator layout,
            h2ControlledQ10CleanOperator
              (historyP15ControlledQ10UnderstandingSpecification p layout widths)] ++
           [historyTaylorActiveConjunctionOperator layout,
            historyTaylorInvalidClockOperator layout,
            historyTaylorOrderBoundaryOperator layout,
            historyTaylorIdleBoundaryOperator layout,
            historyTaylorDegreeIncrementOperator layout,
            historyTaylorCoefficientLoopOperator layout angles,
            historyTaylorIdleCoefficientOperator layout idleAngle,
            operatorSequence [historyTaylorIdleEndComparisonOperator layout,
              historyTaylorTimeComparisonOperator layout,
              historyTaylorSelectorEqualityOperator layout]])
      rw [operatorSequence_append]
      simp [operatorSequence, mul_assoc])

@[simp] theorem historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :
    (historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement
      layout evidence widths angles idleAngle coefficientAgreement).target =
      h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout evidence widths
          angles idleAngle) := rfl

@[simp] theorem historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :
    (historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement
      layout evidence widths angles idleAngle coefficientAgreement).inputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15FullCleanInputPredicate (layout := layout) widths) /\
      (historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement
        layout evidence widths angles idleAngle coefficientAgreement).outputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15FullCleanOutputPredicate (layout := layout) widths) := by
  constructor <;> rfl

/-- Retargeting never changes the literal P15 gate stream: the two aggregate
H2 children flatten to the existing complete P15 clean circuit. -/
theorem historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement_flatten_eq_p15
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr)
    (coefficientAgreement :
      historyP15TaylorCoefficientBasisAgreement layout widths angles) :
    (historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement
      layout evidence widths angles idleAngle coefficientAgreement).circuit.flatten =
      (historyP15FullCleanComponent layout evidence widths angles idleAngle).circuit.flatten := by
  unfold historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement
    historyP15FullCleanH2TwoChildComponentsOfCoefficientAgreement
  simp only [SubspaceMapComponent.refineTarget_circuit,
    SubspaceMapComponent.sequenceAlong_circuit, List.map_cons, List.map_nil,
    Circuit.flatten_sequence, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [historyP15PostQ10CleanComponentRefinedToH2OfCoefficientAgreement_circuit]
  unfold historyP15ThroughQ10ComponentRefinedToH2
    historyP15FullCleanComponent historyP15FullCleanComponents
  simp only [SubspaceMapComponent.refineTarget_circuit,
    SubspaceMapComponent.sequenceAlong_circuit, Circuit.flatten_sequence,
    List.map_append, List.map_cons, List.map_nil, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

/-- The coefficient bridge discharges the sole non-definitional group
comparison required by the full P15-to-H2 construction. -/
theorem historyP15TaylorCoefficientBasisAgreement_of_pureBridge
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) :
    historyP15TaylorCoefficientBasisAgreement layout widths angles := by
  intro input inside
  rw [historyP15TaylorCoefficientComponent_target]
  exact historyP15TaylorCoefficientOperator_eq_historyTaylorCoefficientLoopOperator_basisKet
    layout widths angles input inside

/-- Concrete H2 clean component: the actual two-region P15 circuit with the
independently specified H2 clean operator as target.  No semantic existence
assumption remains. -/
noncomputable def historyP15FullCleanH2Component
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr) (idleAngle : AngleExpr) :=
  historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement
    layout evidence widths angles idleAngle
    (historyP15TaylorCoefficientBasisAgreement_of_pureBridge layout widths angles)

@[simp] theorem historyP15FullCleanH2Component_target
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
    (historyP15FullCleanH2Component layout evidence widths angles idleAngle).target =
      h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout evidence widths
          angles idleAngle) := by
  unfold historyP15FullCleanH2Component
  exact historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement_target
    layout evidence widths angles idleAngle
    (historyP15TaylorCoefficientBasisAgreement_of_pureBridge layout widths angles)

@[simp] theorem historyP15FullCleanH2Component_spaces
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
    (historyP15FullCleanH2Component layout evidence widths angles idleAngle).inputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15FullCleanInputPredicate (layout := layout) widths) /\
      (historyP15FullCleanH2Component layout evidence widths angles idleAngle).outputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15FullCleanOutputPredicate (layout := layout) widths) := by
  unfold historyP15FullCleanH2Component
  exact historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement_spaces
    layout evidence widths angles idleAngle
    (historyP15TaylorCoefficientBasisAgreement_of_pureBridge layout widths angles)

/-- The retargeted component retains the literal P15 source circuit. -/
theorem historyP15FullCleanH2Component_flatten_eq_p15
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
    (historyP15FullCleanH2Component layout evidence widths angles idleAngle).circuit.flatten =
      (historyP15FullCleanComponent layout evidence widths angles idleAngle).circuit.flatten := by
  unfold historyP15FullCleanH2Component
  exact historyP15FullCleanH2TwoChildComponentOfCoefficientAgreement_flatten_eq_p15
    layout evidence widths angles idleAngle
    (historyP15TaylorCoefficientBasisAgreement_of_pureBridge layout widths angles)

end

end SpectralSamplingProof.Components
