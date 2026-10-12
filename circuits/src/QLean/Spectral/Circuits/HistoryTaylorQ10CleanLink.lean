import QLean.Generator.Implementation.Q10BorrowingStageRestoration
import QLean.Spectral.Circuits.ControlledSubcircuit

/-!
# H2/P15 direct link to the canonical Q10 clean component

This module is deliberately dependency-minimal.  It does not import or modify
the in-progress history implementation.  Instead it records the exact H2 wire
contract in a small placement record and proves the controlled-Q10 clean
boundary for every placement satisfying that contract.  A later H packet must
construct this record from the concrete history layout.

The proof consumes both public fields of the canonical Q10 clean child:
`.correct` for coherent action and `.target_maps` for work restoration.  The
full-space Q10 Exact component (P17) and the strict controlled compiler (P44)
remain separate direct children.  Q11 is not used.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore

/-- Source-order register enumeration used by the isolated H2 contract. -/
def historyTaylorQ10RegisterWires {qubits width : Nat}
    (register : Register qubits width) : List (Fin qubits) :=
  List.ofFn register.wire

/-- Minimal mathematical placement contract for one P15 controlled-Q10
occurrence.  The source order is exactly
`signal ++ generatorWork ++ data`; the external control and compiler work are
explicit fields, rather than facts hidden in an implementation layout. -/
structure HistoryTaylorQ10PlacementEvidence
    {qubits generatorSignalWidth generatorWorkWidth dataWidth : Nat}
    (p : ProbabilityGeneratorQProof.QParameters) where
  widths :
    ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
      p generatorSignalWidth generatorWorkWidth dataWidth
  signal : Register qubits generatorSignalWidth
  generatorWork : Register qubits generatorWorkWidth
  data : Register qubits dataWidth
  activeWire : Fin qubits
  compilerWork : Register qubits 2
  embedding : ProbabilityGeneratorQProof.QWireEmbedding
    p.ancillaWidth p.systemWidth qubits
  placement_sourceOrder : List.ofFn embedding.placement =
    historyTaylorQ10RegisterWires signal ++
      historyTaylorQ10RegisterWires generatorWork ++
      historyTaylorQ10RegisterWires data
  control_ne_placed : forall source, activeWire ≠ embedding.placement source

/-- Shared-core P44 layout extracted from the explicit H2 placement record. -/
def HistoryTaylorQ10PlacementEvidence.externalLayout
    {qubits generatorSignalWidth generatorWorkWidth dataWidth : Nat}
    {p : ProbabilityGeneratorQProof.QParameters}
    (placement : HistoryTaylorQ10PlacementEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p) :
    ExternallyControlledCircuitLayout
      (p.ancillaWidth + p.systemWidth) qubits where
  placement := placement.embedding.placement
  control := placement.activeWire
  control_ne_placed := placement.control_ne_placed
  controlWork := historyTaylorQ10RegisterWires placement.compilerWork

/-- The only additional semantic assumption is the standard P44 two-clean-work
contract. -/
structure HistoryTaylorQ10ControlEvidence
    {qubits generatorSignalWidth generatorWorkWidth dataWidth : Nat}
    (p : ProbabilityGeneratorQProof.QParameters) where
  placement : HistoryTaylorQ10PlacementEvidence
    (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
    (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p
  cleanWorkValid : placement.externalLayout.CleanWorkValid

/-- A frozen allowed Q leaf compiles through the shared P44 primitive family. -/
private theorem historyTaylorQ10AllowedPrimitive_isExternallyControllable
    {ancillaQubits systemQubits : Nat}
    (gate : ProbabilityGeneratorQProof.PrimitiveGate ancillaQubits systemQubits)
    (allowed : ProbabilityGeneratorQProof.IsAllowedPrimitiveGate gate) :
    IsExternallyControllablePrimitive gate.toCanonicalCore := by
  cases gate <;>
    simp [ProbabilityGeneratorQProof.IsAllowedPrimitiveGate,
      ProbabilityGeneratorQProof.PrimitiveGate.toCanonicalCore,
      IsExternallyControllablePrimitive] at allowed ⊢

/-- Package-local supported-leaf certificate.  This is reconstructed from the
already-green public Q circuit and its allowed-leaf theorem, so the ungreen
local Q adapter source is not a dependency of this packet. -/
theorem historyTaylorQ10ExternallyControlledCertificate
    (p : ProbabilityGeneratorQProof.QParameters) :
    ExternallyControlledPrimitiveCircuitCertificate
      (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent
        p).circuit where
  leavesSupported gate member := by
    change gate ∈
      ((ProbabilityGeneratorQProof.uqCircuit p).mapGates
        ProbabilityGeneratorQProof.PrimitiveGate.toCanonicalCore).flatten at member
    rw [Circuit.flatten_mapGates] at member
    rcases List.mem_map.mp member with ⟨sourceGate, sourceMember, rfl⟩
    exact historyTaylorQ10AllowedPrimitive_isExternallyControllable sourceGate
      (ProbabilityGeneratorQProof.uqCircuit_allLeavesAllowed
        p sourceGate sourceMember)

noncomputable abbrev q10CanonicalCleanChild
    (p : ProbabilityGeneratorQProof.QParameters) :=
  ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
    p

private theorem q10CleanLink_basisSpan_apply_eq_zero
    {basis : Type*} [DecidableEq basis]
    {predicate : basis -> Prop} {state : State basis}
    (inside : state ∈ SubspaceMapComponent.basisSpan predicate)
    (output : basis) (outside : Not (predicate output)) :
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

/-- The decoded source plan is exactly the circuit denotation of the public
full-space P17 child. -/
theorem historyTaylorProbabilityGeneratorSourcePlan_eq_qCircuitDenote
    (p : ProbabilityGeneratorQProof.QParameters) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
        (historyTaylorQ10ExternallyControlledCertificate p).plan =
      Circuit.denote
        (primitiveGateOperatorWithSymbols
          (qubits := p.ancillaWidth + p.systemWidth)
          ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
        (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent
          p).circuit := by
  let component :=
    ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent p
  let certificate := historyTaylorQ10ExternallyControlledCertificate p
  calc
    ExternallyControlledPrimitivePlan.sourcePlanOperator
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment certificate.plan =
        component.target :=
      ExternallyControlledPrimitiveCircuitCertificate.sourcePlanOperator_eq_component_target
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment component certificate
    _ = Circuit.denote
        (primitiveGateOperatorWithSymbols
          (qubits := p.ancillaWidth + p.systemWidth)
          ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
        component.circuit := component.correct.symm

/-- This transition-zero proof explicitly consumes both Q10 clean contracts. -/
theorem historyTaylorProbabilityGeneratorSourcePlan_maps_of_q10CleanChild
    (p : ProbabilityGeneratorQProof.QParameters)
    (qCorrect : forall state,
      state ∈ (q10CanonicalCleanChild p).inputSubspace ->
        applyOperator
            ((q10CanonicalCleanChild p).circuit.denote
              (primitiveGateOperatorWithSymbols ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)) state =
          applyOperator (q10CanonicalCleanChild p).target state)
    (qTargetMaps : forall state,
      state ∈ (q10CanonicalCleanChild p).inputSubspace ->
        applyOperator (q10CanonicalCleanChild p).target state ∈
          (q10CanonicalCleanChild p).outputSubspace) :
    forall input output,
      ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate p input ->
      Not (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p output) ->
      ExternallyControlledPrimitivePlan.sourcePlanOperator
          ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
          (historyTaylorQ10ExternallyControlledCertificate p).plan output input = 0 := by
  intro input output inputZero outputDirty
  have inputInside : basisKet input ∈
      (q10CanonicalCleanChild p).inputSubspace := by
    rw [(ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent_spaces
      p).1]
    exact SubspaceMapComponent.basisKet_mem_basisSpan inputZero
  have targetMapped := qTargetMaps (basisKet input) inputInside
  rw [(ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent_spaces
    p).2] at targetMapped
  have targetZero :
      applyOperator (q10CanonicalCleanChild p).target (basisKet input) output = 0 :=
    q10CleanLink_basisSpan_apply_eq_zero targetMapped output outputDirty
  have sourceApply :
      applyOperator
          (ExternallyControlledPrimitivePlan.sourcePlanOperator
            ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
            (historyTaylorQ10ExternallyControlledCertificate p).plan)
          (basisKet input) =
        applyOperator (q10CanonicalCleanChild p).target (basisKet input) := by
    calc
      _ = applyOperator
          (Circuit.denote
            (primitiveGateOperatorWithSymbols
              (qubits := p.ancillaWidth + p.systemWidth)
              ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
            (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent
              p).circuit)
          (basisKet input) := by
            exact congrArg (fun operator => applyOperator operator (basisKet input))
              (historyTaylorProbabilityGeneratorSourcePlan_eq_qCircuitDenote p)
      _ = applyOperator
          (Circuit.denote
            (primitiveGateOperatorWithSymbols
              (qubits := p.ancillaWidth + p.systemWidth)
              ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
            (q10CanonicalCleanChild p).circuit)
          (basisKet input) := by
            rw [ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent_circuit]
      _ = applyOperator (q10CanonicalCleanChild p).target (basisKet input) :=
        qCorrect (basisKet input) inputInside
  have sourceZero := congrArg (fun state => state output) sourceApply
  rw [targetZero] at sourceZero
  simpa only [applyOperator_basisKet] using sourceZero

/-- Full-dirty P44 child for the isolated H2 placement contract. -/
noncomputable def historyTaylorControlledProbabilityGeneratorStrictExactComponent
    {qubits generatorSignalWidth generatorWorkWidth dataWidth : Nat}
    (p : ProbabilityGeneratorQProof.QParameters)
    (evidence : HistoryTaylorQ10ControlEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p) :=
  r12ControlledSubcircuitStrictExactComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    evidence.placement.externalLayout
    (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent p)
    (historyTaylorQ10ExternallyControlledCertificate p)

/-- Clean H2 boundary: same dirty circuit, semantic controlled-Q10 target, and
all-zero input to work-clean output. -/
noncomputable def
    historyTaylorControlledProbabilityGeneratorQ10CleanBoundarySubspaceMapComponent
    {qubits generatorSignalWidth generatorWorkWidth dataWidth : Nat}
    (p : ProbabilityGeneratorQProof.QParameters)
    (evidence : HistoryTaylorQ10ControlEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p) :=
  externallyControlledAsymmetricSubspaceMapComponentOfExact
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    evidence.placement.externalLayout evidence.cleanWorkValid
    (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent p)
    (historyTaylorQ10ExternallyControlledCertificate p)
    (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate p)
    (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p)
    (historyTaylorProbabilityGeneratorSourcePlan_maps_of_q10CleanChild p
      (q10CanonicalCleanChild p).correct
      (q10CanonicalCleanChild p).target_maps)
    (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate_implies_workClean p)

@[simp] theorem historyTaylorControlledProbabilityGeneratorQ10CleanBoundary_circuit
    {qubits generatorSignalWidth generatorWorkWidth dataWidth : Nat}
    (p : ProbabilityGeneratorQProof.QParameters)
    (evidence : HistoryTaylorQ10ControlEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p) :
    (historyTaylorControlledProbabilityGeneratorQ10CleanBoundarySubspaceMapComponent
      p evidence).circuit =
      (historyTaylorControlledProbabilityGeneratorStrictExactComponent
        p evidence).circuit := by
  change
    (externallyControlledAsymmetricSubspaceMapComponentOfExact
      ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
      evidence.placement.externalLayout evidence.cleanWorkValid
      (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent p)
      (historyTaylorQ10ExternallyControlledCertificate p)
      (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate p)
      (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p)
      (historyTaylorProbabilityGeneratorSourcePlan_maps_of_q10CleanChild p
        (q10CanonicalCleanChild p).correct
        (q10CanonicalCleanChild p).target_maps)
      (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate_implies_workClean p)).circuit =
    (externallyControlledStrictExactOperatorComponentOfExact
      ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
      evidence.placement.externalLayout
      (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent p)
      (historyTaylorQ10ExternallyControlledCertificate p)).circuit
  exact externallyControlledAsymmetricSubspaceMapComponentOfExact_circuit
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    evidence.placement.externalLayout evidence.cleanWorkValid
    (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent p)
    (historyTaylorQ10ExternallyControlledCertificate p)
    (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate p)
    (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p)
    (historyTaylorProbabilityGeneratorSourcePlan_maps_of_q10CleanChild p
      (q10CanonicalCleanChild p).correct
      (q10CanonicalCleanChild p).target_maps)
    (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate_implies_workClean p)

@[simp] theorem historyTaylorControlledProbabilityGeneratorQ10CleanBoundary_target
    {qubits generatorSignalWidth generatorWorkWidth dataWidth : Nat}
    (p : ProbabilityGeneratorQProof.QParameters)
    (evidence : HistoryTaylorQ10ControlEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p) :
    (historyTaylorControlledProbabilityGeneratorQ10CleanBoundarySubspaceMapComponent
      p evidence).target =
      ExternallyControlledPrimitivePlan.semanticPlanOperator
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
        evidence.placement.externalLayout
        (historyTaylorQ10ExternallyControlledCertificate p).plan := by
  exact externallyControlledAsymmetricSubspaceMapComponentOfExact_target
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    evidence.placement.externalLayout evidence.cleanWorkValid
    (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent p)
    (historyTaylorQ10ExternallyControlledCertificate p)
    (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate p)
    (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p)
    (historyTaylorProbabilityGeneratorSourcePlan_maps_of_q10CleanChild p
      (q10CanonicalCleanChild p).correct
      (q10CanonicalCleanChild p).target_maps)
    (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate_implies_workClean p)

theorem historyTaylorControlledProbabilityGeneratorQ10CleanBoundary_spaces
    {qubits generatorSignalWidth generatorWorkWidth dataWidth : Nat}
    (p : ProbabilityGeneratorQProof.QParameters)
    (evidence : HistoryTaylorQ10ControlEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p) :
    let component :=
      historyTaylorControlledProbabilityGeneratorQ10CleanBoundarySubspaceMapComponent
        p evidence
    component.inputSubspace = SubspaceMapComponent.basisSpan
        (externallyControlledPlacedInputPredicate evidence.cleanWorkValid
          (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate p)) ∧
      component.outputSubspace = SubspaceMapComponent.basisSpan
        (externallyControlledPlacedOutputPredicate evidence.cleanWorkValid
          (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p)) := by
  exact externallyControlledAsymmetricSubspaceMapComponentOfExact_spaces
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    evidence.placement.externalLayout evidence.cleanWorkValid
    (ProbabilityGeneratorQProof.probabilityGeneratorCanonicalCoreExactOperatorComponent p)
    (historyTaylorQ10ExternallyControlledCertificate p)
    (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate p)
    (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p)
    (historyTaylorProbabilityGeneratorSourcePlan_maps_of_q10CleanChild p
      (q10CanonicalCleanChild p).correct
      (q10CanonicalCleanChild p).target_maps)
    (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate_implies_workClean p)

end SpectralSamplingProof.Components
