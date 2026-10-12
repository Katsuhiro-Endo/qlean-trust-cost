import QLean.Spectral.Circuits.HistoryP15PostQ10Clean

/-!
# Constructive whole-P15 clean composition

This leaf joins the pre-Q10/Q10 prefix exactly once to the already-verified
eight-group post-Q10 clean component.  In particular, it deliberately starts
from `historyP15ThroughQ10Components`, rather than the older
`historyP15ThroughInvalidClockComponents` checkpoint: the latter already
contains the first two post-Q10 groups and would duplicate them here.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

/-- The clean P15 entry additionally records the all-zero Q10 placement
required by the unique Q10 occurrence.  The ordinary P15 auxiliary boundary
alone does not imply that placement invariant. -/
def historyP15FullCleanInputPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    QubitBasis qubits -> Prop :=
  historyP15WithQ10Input (layout := layout) widths
    (historyTaylorAuxiliaryBoundaryPredicate layout)

/-- The whole-P15 clean exit keeps the independently restored Q10 boundary
and restores every P15 auxiliary workspace wire to zero. -/
def historyP15FullCleanOutputPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    QubitBasis qubits -> Prop :=
  historyP15PostQ10CleanOutputPredicate (layout := layout) widths

/-- The actual P15 clean children in source order.  The prefix stops at the
post-Q10 input boundary, so the restore-active and invalid-clock groups occur
only in the final post-Q10 child. -/
noncomputable def historyP15FullCleanComponents
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
  historyP15ThroughQ10Components layout evidence.clock widths ++
    [historyP15PostQ10CleanComponent layout evidence widths angles idleAngle]

/-- The typed source-order chain for the full P15 clean region. -/
theorem historyP15FullCleanComponents_chain
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
    SubspaceMapComponent.SpaceChain
      (historyP15FullCleanComponents layout evidence widths angles idleAngle)
      (SubspaceMapComponent.basisSpan
        (historyP15FullCleanInputPredicate (layout := layout) widths))
      (SubspaceMapComponent.basisSpan
        (historyP15FullCleanOutputPredicate (layout := layout) widths)) := by
  have prefixChain := historyP15ThroughQ10Components_chain
    layout evidence.clock widths
  have postChain := SubspaceMapComponent.SpaceChain.singleton
    (historyP15PostQ10CleanComponent layout evidence widths angles idleAngle)
  have joined := SubspaceMapComponent.SpaceChain.append prefixChain postChain
  simpa [historyP15FullCleanComponents, historyP15FullCleanInputPredicate,
    historyP15FullCleanOutputPredicate] using joined

/-- Independent source-order target for the complete P15 clean word. -/
noncomputable def historyP15FullCleanOperator
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
    Operator (QubitBasis qubits) :=
  operatorSequence
    ((historyP15ThroughQ10Components layout evidence.clock widths).map
      (fun component => component.target) ++
      [historyP15PostQ10CleanOperator layout evidence widths angles idleAngle])

/-- Constructive coherent component for the actual full P15 source word. -/
noncomputable def historyP15FullCleanComponent
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
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits)
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment) :=
  (SubspaceMapComponent.sequenceAlong
    (historyP15FullCleanComponents_chain layout evidence widths angles idleAngle)).refineTarget
      (historyP15FullCleanOperator layout evidence widths angles idleAngle)
      (by
        rw [SubspaceMapComponent.sequenceAlong_target]
        simp only [historyP15FullCleanComponents, List.map_append,
          List.map_cons, List.map_nil]
        rw [historyP15PostQ10CleanComponent_target]
        rfl)

/-- The actual prefix circuit stages, in their already-verified source order.
This list ends immediately before the first post-Q10 group. -/
noncomputable def historyP15FullCleanPrefixSourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    List (Circuit (PrimitiveGate qubits)) :=
  (historyP15ThroughQ10Components layout evidence.clock widths).map
    (fun component => component.circuit)

/-- Full P15 source stages: the non-overlapping prefix followed by the
independently spelled-out post-Q10 source circuit. -/
noncomputable def historyP15FullCleanSourceStages
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
    List (Circuit (PrimitiveGate qubits)) :=
  historyP15FullCleanPrefixSourceStages layout evidence widths ++
    [historyP15PostQ10SourceCircuit layout evidence widths angles idleAngle]

/-- Literal actual source circuit for the entire non-duplicated P15 clean
word. -/
noncomputable def historyP15FullCleanSourceCircuit
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
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence
    (historyP15FullCleanSourceStages layout evidence widths angles idleAngle)

/-- The constructed full component flattens to the literal source circuit in
the same order. -/
theorem historyP15FullCleanComponent_flatten_eq_source
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
    (historyP15FullCleanComponent layout evidence widths angles idleAngle).circuit.flatten =
      (historyP15FullCleanSourceCircuit layout evidence widths angles idleAngle).flatten := by
  change (Circuit.sequence
      ((historyP15FullCleanComponents layout evidence widths angles idleAngle).map
        (fun component => component.circuit))).flatten = _
  unfold historyP15FullCleanComponents
  simp only [List.map_append, List.map_cons, List.map_nil,
    Circuit.flatten_sequence, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rw [historyP15PostQ10CleanComponent_flatten_eq_source]
  unfold historyP15FullCleanSourceCircuit historyP15FullCleanSourceStages
    historyP15FullCleanPrefixSourceStages
  simp only [Circuit.flatten_sequence, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

end

end SpectralSamplingProof.Components
