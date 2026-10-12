import QLean.Spectral.Circuits.HistoryP15Q10Invariant
import QLean.Circuits.Foundation.PrimitiveGateProofs

/-!
# Constructive P15 post-Q10 clean checkpoint

This module continues the already-green P15-through-Q10 coherent component.
It uses the concrete frozen placement and the actual post-Q10 source words.
No whole-block agreement hypothesis and no supplied parent component is used.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

private abbrev historyP15PostGate {qubits : Nat} :=
  primitiveGateOperatorWithSymbols (qubits := qubits)
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment

/-! ### Clean compute--use--uncompute algebra

The following lemma deliberately speaks about matrix entries rather than
pretending that the middle operation has a single basis output.  Thus a
controlled one-qubit `use` may create a superposition (and hence entangle its
control with its target): the final XOR is justified because every nonzero
basis entry preserves the compute inputs and the workspace control value is
available on each such entry.
-/

private def historyP15XorComputeAction {qubits : Nat} (control : Fin qubits)
    (condition : QubitBasis qubits -> Bool) (input : QubitBasis qubits) :
    QubitBasis qubits :=
  xorWire control (condition input) input

private theorem historyP15XorComputeAction_agreesExcept_control {qubits : Nat}
    (control : Fin qubits) (condition : QubitBasis qubits -> Bool)
    (input : QubitBasis qubits) :
    agreesExcept control (historyP15XorComputeAction control condition input)
      input := by
  intro wire different
  exact xorWire_apply_other control wire different _ input

private theorem historyP15XorComputeAction_condition_stable {qubits : Nat}
    (control : Fin qubits) (condition : QubitBasis qubits -> Bool)
    (controlIndependent : forall first second,
      agreesExcept control first second -> condition first = condition second)
    (input : QubitBasis qubits) :
    condition (historyP15XorComputeAction control condition input) =
      condition input := by
  apply controlIndependent
  exact historyP15XorComputeAction_agreesExcept_control control condition input

private theorem historyP15XorComputeAction_involutive {qubits : Nat}
    (control : Fin qubits) (condition : QubitBasis qubits -> Bool)
    (controlIndependent : forall first second,
      agreesExcept control first second -> condition first = condition second) :
    Function.Involutive (historyP15XorComputeAction control condition) := by
  intro input
  change xorWire control
    (condition (historyP15XorComputeAction control condition input))
    (historyP15XorComputeAction control condition input) = input
  rw [historyP15XorComputeAction_condition_stable control condition
    controlIndependent input]
  change xorWire control (condition input)
    (xorWire control (condition input) input) = input
  exact xorWire_involutive control (condition input) input

private noncomputable def historyP15XorComputeUseUncomputeOperator
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (condition : QubitBasis qubits -> Bool)
    (localOperator : Matrix Bool Bool ℂ) : Operator (QubitBasis qubits) :=
  (deterministicOperator (historyP15XorComputeAction control condition) *
      embedControlledSingleQubitOperator control target different localOperator) *
    deterministicOperator (historyP15XorComputeAction control condition)

/-- Clean-control matrix-element identity for an XOR compute, an arbitrary
single-qubit use, and the same XOR uncompute.  It is intentionally only a
clean-input statement; no false equality on the whole Hilbert space is used. -/
private theorem historyP15_applyOperator_xorComputeUseUncompute_basisKet
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (condition : QubitBasis qubits -> Bool)
    (localOperator : Matrix Bool Bool ℂ)
    (controlIndependent : forall first second,
      agreesExcept control first second -> condition first = condition second)
    (targetIndependent : forall first second,
      agreesExcept target first second -> condition first = condition second)
    (input : QubitBasis qubits) (controlClean : input control = false) :
    applyOperator
        (historyP15XorComputeUseUncomputeOperator control target different
          condition localOperator)
        (basisKet input) =
      applyOperator
        (predicateControlledSingleQubitOperator condition target localOperator)
        (basisKet input) := by
  have actionInvolutive : Function.Involutive
      (historyP15XorComputeAction control condition) :=
    historyP15XorComputeAction_involutive control condition controlIndependent
  have actionControl (state : QubitBasis qubits)
      (clean : state control = false) :
      historyP15XorComputeAction control condition state control =
        condition state := by
    unfold historyP15XorComputeAction
    rw [xorWire_apply_same, clean]
    cases condition state <;> rfl
  have actionTarget (state : QubitBasis qubits) :
      historyP15XorComputeAction control condition state target = state target := by
    unfold historyP15XorComputeAction
    exact xorWire_apply_other control target different.symm _ state
  funext output
  unfold historyP15XorComputeUseUncomputeOperator
  rw [applyOperator_basisKet, applyOperator_basisKet]
  rw [deterministicOperator_eq_permMatrix_of_involutive
    (historyP15XorComputeAction control condition) actionInvolutive]
  rw [permMatrix_conjugate_operator_apply
    (involutiveBasisEquiv (historyP15XorComputeAction control condition)
      actionInvolutive) (by rfl)]
  change embedControlledSingleQubitOperator control target different localOperator
      (historyP15XorComputeAction control condition output)
      (historyP15XorComputeAction control condition input) =
    predicateControlledSingleQubitOperator condition target localOperator output input
  rw [embedControlledSingleQubitOperator_apply_sparse,
    predicateControlledSingleQubitOperator_apply]
  by_cases originalAgreement : agreesExcept target output input
  · have conditionAgreement : condition output = condition input :=
      targetIndependent output input originalAgreement
    have transformedAgreement : agreesExcept target
        (historyP15XorComputeAction control condition output)
        (historyP15XorComputeAction control condition input) := by
      intro wire wireDifferent
      by_cases wireControl : wire = control
      · subst wire
        rw [actionControl output (by
          have controlEqual := originalAgreement control different
          simpa [controlEqual] using controlClean),
          actionControl input controlClean, conditionAgreement]
      · rw [show historyP15XorComputeAction control condition output wire =
            output wire by
            unfold historyP15XorComputeAction
            exact xorWire_apply_other control wire wireControl _ output,
          show historyP15XorComputeAction control condition input wire =
            input wire by
            unfold historyP15XorComputeAction
            exact xorWire_apply_other control wire wireControl _ input]
        exact originalAgreement wire wireDifferent
    rw [if_pos transformedAgreement, if_pos originalAgreement]
    rw [actionControl input controlClean, actionTarget output, actionTarget input]
  · have transformedDisagreement : ¬ agreesExcept target
        (historyP15XorComputeAction control condition output)
        (historyP15XorComputeAction control condition input) := by
      intro transformedAgreement
      apply originalAgreement
      have conditionOutputCompute :
          condition (historyP15XorComputeAction control condition output) =
            condition output :=
        historyP15XorComputeAction_condition_stable control condition
          controlIndependent output
      have conditionInputCompute :
          condition (historyP15XorComputeAction control condition input) =
            condition input :=
        historyP15XorComputeAction_condition_stable control condition
          controlIndependent input
      have conditionAgreement : condition output = condition input := by
        rw [<- conditionOutputCompute, <- conditionInputCompute]
        exact targetIndependent _ _ transformedAgreement
      intro wire wireDifferent
      by_cases wireControl : wire = control
      · subst wire
        have controlOutputClean : output control = false := by
          have controlEqual := transformedAgreement control different
          unfold historyP15XorComputeAction at controlEqual
          rw [xorWire_apply_same, xorWire_apply_same, controlClean,
            <- conditionAgreement] at controlEqual
          cases hOutput : output control <;>
          cases hCondition : condition input <;>
          simp [hOutput] at controlEqual ⊢
        exact controlOutputClean.trans controlClean.symm
      · have equal := transformedAgreement wire wireDifferent
        rw [show historyP15XorComputeAction control condition output wire =
              output wire by
              unfold historyP15XorComputeAction
              exact xorWire_apply_other control wire wireControl _ output,
            show historyP15XorComputeAction control condition input wire =
              input wire by
              unfold historyP15XorComputeAction
              exact xorWire_apply_other control wire wireControl _ input] at equal
        exact equal
    simp [transformedDisagreement, originalAgreement]

/-- One actual post-Q10 source occurrence with its independently stated
operator target. -/
private structure HistoryP15PostStage (qubits : Nat) where
  analyticTarget : Operator (QubitBasis qubits)
  component : ExactOperatorComponent (historyP15PostGate (qubits := qubits))
  target_eq : component.target = analyticTarget

private noncomputable def historyP15PostInstructionStage {qubits : Nat}
    (instruction : ClassicalReversibleInstruction qubits) :
    HistoryP15PostStage qubits where
  analyticTarget := deterministicOperator instruction.basisAction
  component := ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.instruction instruction)
  target_eq := by
    calc
      _ = (ClassicalReversibleStage.instruction instruction).analyticOperator :=
        ClassicalReversibleStage.primitiveExactOperatorComponent_target
          ProbabilityGeneratorQProof.internalZeroSymbolEnvironment _
      _ = deterministicOperator instruction.basisAction :=
        ClassicalReversibleStage.analyticOperator_eq_deterministicReference _

/-- Typed physical facts and angles used only by the post-Q10 source word.
These are layout certificates, not circuit- or operator-existence assumptions. -/
structure HistoryP15PostQ10Evidence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  clock : HistoryP15PreQ10Evidence layout
  branch_ne_ltIdleEnd :
    historyBranchWire layout ≠ historyLessThanIdleEndWire layout
  branch_ne_coefficientSignal :
    historyBranchWire layout ≠ layout.coefficientSignal
  ltIdleEnd_ne_coefficientSignal :
    historyLessThanIdleEndWire layout ≠ layout.coefficientSignal

/-- The placed Q10 output boundary after its compiler work and Q work have
been restored. -/
def historyP15PostQ10OutputPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    QubitBasis qubits -> Prop :=
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  externallyControlledPlacedOutputPredicate evidence.cleanWorkValid
    (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p)

/-- Common coherent boundary for every post-Q10 group. -/
def historyP15PostQ10StablePredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (basis : QubitBasis qubits) : Prop :=
  historyP15PostQ10OutputPredicate (layout := layout) widths basis /\
    historyTaylorPostGeneratorStablePredicate layout basis

/-- Every live P15 auxiliary XOR preserves the already-restored Q10 output
boundary. -/
theorem historyP15PostQ10OutputPredicate_xorLiveWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (wire : Fin qubits)
    (live : wire ∈ historyTaylorBeforeGeneratorLiveWires layout)
    (value : Bool) (input : QubitBasis qubits)
    (inside : historyP15PostQ10OutputPredicate
      (layout := layout) widths input) :
    historyP15PostQ10OutputPredicate (layout := layout) widths
      (xorWire wire value input) := by
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  have compilerDifferent := historyP15Q10LiveWire_ne_compilerWork
    (layout := layout) widths wire live
  unfold historyP15PostQ10OutputPredicate
    externallyControlledPlacedOutputPredicate at inside ⊢
  constructor
  · exact externallyControlledCleanWorkPredicate_xorWire_of_ne
      evidence.cleanWorkValid wire value input inside.1
      compilerDifferent.1 compilerDifferent.2
  · rw [restrictToPlacedWires_xorWire_outside]
    · exact inside.2
    · exact historyP15Q10LiveWire_ne_placement
        (layout := layout) widths wire live

private theorem historyP15PostSignal_ne_placement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (signal : Fin qubits)
    (signalMember : signal ∈
      [layout.coefficientSignal, layout.orderBoundarySignal])
    (source : Fin (p.ancillaWidth + p.systemWidth)) :
    signal ≠ (historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths).placement.embedding.placement source := by
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
  have dataSplit := List.nodup_append.mp selectorSplit.2.1
  have clockSplit := List.nodup_append.mp dataSplit.2.1
  have orderSplit := List.nodup_append.mp clockSplit.2.1
  have generatorSplit := List.nodup_append.mp orderSplit.2.1
  have reservedSplit := List.nodup_append.mp generatorSplit.2.1
  have reservedMember : signal ∈ reservedWires := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at signalMember
    rcases signalMember with equal | equal
    · simp [reservedWires, equal]
    · simp [reservedWires, equal]
  intro equal
  have placedMember :
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := layout) widths).placement.embedding.placement source ∈
        List.ofFn (historyP15Q10ControlEvidence_ofFrozenLayout
          (layout := layout) widths).placement.embedding.placement := by
    exact List.mem_ofFn.mpr ⟨source, rfl⟩
  rw [historyP15Q10Placement_sourceOrder (layout := layout) widths] at placedMember
  rcases List.mem_append.mp placedMember with initialMember | dataMember
  · rcases List.mem_append.mp initialMember with generatorMember | workMember
    · exact generatorSplit.2.2 _ generatorMember signal
        (List.mem_append_left _ reservedMember) equal.symm
    · have workspaceMember :
          (historyP15Q10ControlEvidence_ofFrozenLayout
            (layout := layout) widths).placement.embedding.placement source ∈
            workspaceWires := by
        simp only [historyRegisterWires, List.mem_ofFn] at workMember ⊢
        rcases workMember with ⟨index, equalWork⟩
        rw [← equalWork]
        simpa [workspaceWires] using
          historyGeneratorWorkRegister_wire_mem_workspace layout index
      exact reservedSplit.2.2 signal reservedMember _
        workspaceMember equal
  · exact dataSplit.2.2 _ dataMember signal
      (by
        exact List.mem_append_right clockWires
          (List.mem_append_right orderWires
            (List.mem_append_right generatorWires
              (List.mem_append_left workspaceWires reservedMember)))) equal.symm

/-- Either reserved post signal may be toggled without changing the Q10 clean
output boundary. -/
theorem historyP15PostQ10OutputPredicate_xorPostSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (signal : Fin qubits)
    (signalMember : signal ∈
      [layout.coefficientSignal, layout.orderBoundarySignal])
    (value : Bool) (input : QubitBasis qubits)
    (inside : historyP15PostQ10OutputPredicate
      (layout := layout) widths input) :
    historyP15PostQ10OutputPredicate (layout := layout) widths
      (xorWire signal value input) := by
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  have separated := layout.postGeneratorSignal_separated signal signalMember
  have compiler0 : signal ≠ evidence.cleanWorkValid.work₀ := by
    change signal ≠ (historyControlledWork layout).wire 0
    intro equal
    have member := historyControlledWork_wire_mem_workspace layout 0
    rcases List.mem_ofFn.mp member with ⟨index, member⟩
    exact (separated.2.2 index) (member.trans equal.symm)
  have compiler1 : signal ≠ evidence.cleanWorkValid.work₁ := by
    change signal ≠ (historyControlledWork layout).wire 1
    intro equal
    have member := historyControlledWork_wire_mem_workspace layout 1
    rcases List.mem_ofFn.mp member with ⟨index, member⟩
    exact (separated.2.2 index) (member.trans equal.symm)
  unfold historyP15PostQ10OutputPredicate
    externallyControlledPlacedOutputPredicate at inside ⊢
  constructor
  · exact externallyControlledCleanWorkPredicate_xorWire_of_ne
      evidence.cleanWorkValid signal value input inside.1 compiler0 compiler1
  · rw [restrictToPlacedWires_xorWire_outside]
    · exact inside.2
    · exact historyP15PostSignal_ne_placement widths signal signalMember

/-- Reapply the genuine P43 occurrence after Q10 to erase the active flag. -/
noncomputable def historyP15RestoreGeneratorActiveComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
      ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyActiveWire layout) (by simp)
      (historyTaylorActiveConjunctionLayout_nodup layout)
      (fun input =>
        historyP15PostQ10OutputPredicate (layout := layout) widths input /\
          historyTaylorBeforeGeneratorBoundaryPredicate layout input)
      (historyP15PostQ10StablePredicate (layout := layout) widths)
      (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
      (by
        intro input inside
        constructor
        · exact historyP15PostQ10OutputPredicate_xorLiveWire
            widths (historyActiveWire layout)
            (by simp [historyTaylorBeforeGeneratorLiveWires]) _ input inside.1
        · exact historyTaylorActiveConjunctionBasisAction_unmaps_phase
            layout input inside.2)

theorem historyP15RestoreGeneratorActiveComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    let component := historyP15RestoreGeneratorActiveComponent layout widths
    component.inputSubspace = SubspaceMapComponent.basisSpan
        (fun input =>
          historyP15PostQ10OutputPredicate (layout := layout) widths input /\
            historyTaylorBeforeGeneratorBoundaryPredicate layout input) /\
      component.outputSubspace = SubspaceMapComponent.basisSpan
        (historyP15PostQ10StablePredicate (layout := layout) widths) := by
  constructor <;> rfl

private noncomputable def historyP15PostXStage {qubits : Nat}
    (target : Fin qubits) :=
  historyP15PostInstructionStage (.xorOne target)

private noncomputable def historyP15PostToffoliStage {qubits : Nat}
    (control0 control1 target : Fin qubits)
    (controlsDifferent : control0 ≠ control1)
    (firstDifferent : control0 ≠ target)
    (secondDifferent : control1 ≠ target) :=
  historyP15PostInstructionStage
    (.xorDoublyControlled control0 control1 target
      controlsDifferent firstDifferent secondDifferent)

private noncomputable def historyP15InvalidClockStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout) :=
  [historyP15PostXStage (historyLessThanIdleEndWire layout),
   historyP15PostToffoliStage
      (historyBranchWire layout) (historyLessThanIdleEndWire layout)
      layout.coefficientSignal evidence.branch_ne_ltIdleEnd
      evidence.branch_ne_coefficientSignal
      evidence.ltIdleEnd_ne_coefficientSignal,
   historyP15PostXStage (historyLessThanIdleEndWire layout)]

private noncomputable def historyP15PostGroupExactComponent
    {qubits : Nat}
    (stages : List (HistoryP15PostStage qubits)) :=
  ExactOperatorComponent.sequence
    (stages.map HistoryP15PostStage.component)

private theorem historyP15PostGroupExactComponent_target
    {qubits : Nat}
    (stages : List (HistoryP15PostStage qubits)) :
    (historyP15PostGroupExactComponent stages).target =
      operatorSequence (stages.map HistoryP15PostStage.analyticTarget) := by
  rw [historyP15PostGroupExactComponent,
    ExactOperatorComponent.sequence_target_eq_operatorSequence]
  apply congrArg operatorSequence
  simp only [List.map_map]
  apply List.map_congr_left
  intro stage _member
  exact stage.target_eq

private noncomputable def historyP15PostGroupSubspaceMap
    {qubits : Nat}
    (stages : List (HistoryP15PostStage qubits))
    (cleanTarget : Operator (QubitBasis qubits))
    (inputPredicate outputPredicate : QubitBasis qubits -> Prop)
    (agreement : forall input, inputPredicate input ->
      applyOperator
          (operatorSequence (stages.map HistoryP15PostStage.analyticTarget))
          (basisKet input) = applyOperator cleanTarget (basisKet input))
    (cleanMaps : forall input, inputPredicate input ->
      applyOperator cleanTarget (basisKet input) ∈
        SubspaceMapComponent.basisSpan outputPredicate) :=
  let exact := historyP15PostGroupExactComponent stages
  SubspaceMapComponent.ofBasisSpan historyP15PostGate exact.circuit cleanTarget
    inputPredicate outputPredicate
    (by
      intro input inside
      calc
        applyOperator (Circuit.denote historyP15PostGate exact.circuit)
            (basisKet input) = applyOperator exact.target (basisKet input) :=
          congrArg (fun operator => applyOperator operator (basisKet input))
            exact.correct
        _ = applyOperator
            (operatorSequence
              (stages.map HistoryP15PostStage.analyticTarget))
            (basisKet input) := by
          rw [historyP15PostGroupExactComponent_target]
        _ = applyOperator cleanTarget (basisKet input) :=
          agreement input inside)
    cleanMaps

private theorem historyP15InvalidClockRecorded_eq
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout) :
    operatorSequence
        ((historyP15InvalidClockStages layout evidence).map
          HistoryP15PostStage.analyticTarget) =
      historyTaylorInvalidClockOperator layout := by
  change operatorSequence
      [deterministicOperator
          (ClassicalReversibleInstruction.xorOne
            (historyLessThanIdleEndWire layout)).basisAction,
       deterministicOperator
          (ClassicalReversibleInstruction.xorDoublyControlled
            (historyBranchWire layout) (historyLessThanIdleEndWire layout)
            layout.coefficientSignal evidence.branch_ne_ltIdleEnd
            evidence.branch_ne_coefficientSignal
            evidence.ltIdleEnd_ne_coefficientSignal).basisAction,
       deterministicOperator
          (ClassicalReversibleInstruction.xorOne
            (historyLessThanIdleEndWire layout)).basisAction] = _
  exact historyTaylorInvalidClockSourceOperator_eq_direct layout
    evidence.branch_ne_ltIdleEnd evidence.branch_ne_coefficientSignal
    evidence.ltIdleEnd_ne_coefficientSignal

/- The actual X--Toffoli--X source word, restricted to the concrete Q10 clean
output and common post-generator invariant. -/
noncomputable def historyP15InvalidClockComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  historyP15PostGroupSubspaceMap
    (historyP15InvalidClockStages layout evidence)
    (historyTaylorInvalidClockOperator layout)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (by intro input _inside; rw [historyP15InvalidClockRecorded_eq])
    (by
      intro input inside
      rw [historyTaylorInvalidClockOperator,
        applyOperator_deterministicOperator_basisKet]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      constructor
      · simpa [historyTaylorInvalidClockBasisAction] using
          historyP15PostQ10OutputPredicate_xorPostSignal widths
            layout.coefficientSignal (by simp)
            (historyTaylorInvalidClockCondition layout input) input inside.1
      · exact historyTaylorInvalidClockBasisAction_maps_stable
          layout input inside.2)

theorem historyP15InvalidClockComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    let component := historyP15InvalidClockComponent layout evidence widths
    component.inputSubspace = SubspaceMapComponent.basisSpan
        (historyP15PostQ10StablePredicate (layout := layout) widths) /\
      component.outputSubspace = SubspaceMapComponent.basisSpan
        (historyP15PostQ10StablePredicate (layout := layout) widths) := by
  constructor <;> rfl

/-! ### One Taylor coefficient compute--use--uncompute occurrence

This is intentionally a one-iteration checkpoint.  The surrounding equality
compute/uncompute pair and the finite loop are separate source-order
obligations; here the middle `[conjunction, Ry, conjunction]` word is proved
on the clean post-Q10 span.
-/

private theorem historyP15PostQ10OutputPredicate_of_agreesOutsideSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (signal : Fin qubits)
    (signalMember : signal ∈
      [layout.coefficientSignal, layout.orderBoundarySignal])
    (input output : QubitBasis qubits)
    (inside : historyP15PostQ10OutputPredicate (layout := layout) widths input)
    (sameOutside : forall wire, wire ≠ signal -> output wire = input wire) :
    historyP15PostQ10OutputPredicate (layout := layout) widths output := by
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  have separated := layout.postGeneratorSignal_separated signal signalMember
  have signal_ne_controlledWork (index : Fin 2) :
      signal ≠ (historyControlledWork layout).wire index := by
    have member := historyControlledWork_wire_mem_workspace layout index
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, equal⟩
    exact fun same => separated.2.2 workspaceIndex (equal.trans same.symm)
  unfold historyP15PostQ10OutputPredicate
    externallyControlledPlacedOutputPredicate at inside ⊢
  constructor
  · constructor
    · rw [sameOutside evidence.cleanWorkValid.work₀ (by
          exact (signal_ne_controlledWork 0).symm)]
      exact inside.1.1
    · rw [sameOutside evidence.cleanWorkValid.work₁ (by
          exact (signal_ne_controlledWork 1).symm)]
      exact inside.1.2
  · change ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p
      (restrictToPlacedWires evidence.placement.embedding.placement output)
    rw [show restrictToPlacedWires evidence.placement.embedding.placement output =
        restrictToPlacedWires evidence.placement.embedding.placement input by
          funext source
          unfold restrictToPlacedWires
          exact sameOutside _
            (historyP15PostSignal_ne_placement widths signal signalMember source).symm]
    exact inside.2

private def historyP15CoefficientIterationCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  ClassicalReversibleStage.allWiresTrue
    [historyCoefficientControl layout, historyEqualityFlag layout] basis

private theorem historyP15CoefficientControl_ne_equalityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ≠ historyEqualityFlag layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

private theorem historyP15Active_ne_coefficientControl
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyActiveWire layout ≠ historyCoefficientControl layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

private theorem historyP15EqualityFlag_ne_coefficientSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyEqualityFlag layout ≠ layout.coefficientSignal := by
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  change layout.workspace.wire _ ≠ layout.coefficientSignal
  exact separated.2.2 _

private theorem historyP15CoefficientIterationCondition_activeInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality : historyActiveWire layout ≠ historyEqualityFlag layout)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyActiveWire layout) first second) :
    historyP15CoefficientIterationCondition layout first =
      historyP15CoefficientIterationCondition layout second := by
  unfold historyP15CoefficientIterationCondition
    ClassicalReversibleStage.allWiresTrue ClassicalReversibleStage.readWires
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true]
  rw [same (historyCoefficientControl layout)
    (historyP15Active_ne_coefficientControl layout).symm,
    same (historyEqualityFlag layout) active_ne_equality.symm]

private theorem historyP15CoefficientIterationCondition_signalInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (coefficientControl_ne_signal :
      historyCoefficientControl layout ≠ layout.coefficientSignal)
    (first second : QubitBasis qubits)
    (same : agreesExcept layout.coefficientSignal first second) :
    historyP15CoefficientIterationCondition layout first =
      historyP15CoefficientIterationCondition layout second := by
  unfold historyP15CoefficientIterationCondition
    ClassicalReversibleStage.allWiresTrue ClassicalReversibleStage.readWires
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true]
  rw [same (historyCoefficientControl layout) coefficientControl_ne_signal,
    same (historyEqualityFlag layout)
      (historyP15EqualityFlag_ne_coefficientSignal layout)]

private def historyP15CoefficientIterationCleanActivePredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyActiveWire layout) = false

private def historyP15CoefficientIterationComputedActivePredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyActiveWire layout) =
    historyP15CoefficientIterationCondition layout basis

private theorem historyP15CoefficientIterationConjunction_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality :
      historyActiveWire layout ≠ historyEqualityFlag layout) :
    ([historyCoefficientControl layout, historyEqualityFlag layout] ++ [] ++
      [historyActiveWire layout]).Nodup := by
  simp [historyP15CoefficientControl_ne_equalityFlag,
    (historyP15Active_ne_coefficientControl layout).symm,
    active_ne_equality.symm]

private noncomputable def historyP15CoefficientIterationComputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality :
      historyActiveWire layout ≠ historyEqualityFlag layout) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyCoefficientControl layout, historyEqualityFlag layout] []
    (historyActiveWire layout) (by simp)
    (historyP15CoefficientIterationConjunction_nodup layout active_ne_equality)
    (historyP15CoefficientIterationCleanActivePredicate layout)
    (historyP15CoefficientIterationComputedActivePredicate layout)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input clean
      let action := ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyCoefficientControl layout, historyEqualityFlag layout]
        (historyActiveWire layout)
      have actionAgrees : agreesExcept (historyActiveWire layout)
          (action input) input := by
        intro wire different
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyCoefficientControl layout, historyEqualityFlag layout]
          (historyActiveWire layout) wire different input
      have conditionStable :
          historyP15CoefficientIterationCondition layout (action input) =
            historyP15CoefficientIterationCondition layout input :=
        historyP15CoefficientIterationCondition_activeInvariant layout
          active_ne_equality _ _ actionAgrees
      unfold historyP15CoefficientIterationComputedActivePredicate
      change input (historyActiveWire layout) = false at clean
      change action input (historyActiveWire layout) =
        historyP15CoefficientIterationCondition layout (action input)
      rw [show action input (historyActiveWire layout) =
          (input (historyActiveWire layout) !=
            historyP15CoefficientIterationCondition layout input) by
          exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target
            _ _ _, clean, conditionStable]
      cases historyP15CoefficientIterationCondition layout input <;> rfl)

private theorem historyP15CoefficientIterationComputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality :
      historyActiveWire layout ≠ historyEqualityFlag layout) :
    (historyP15CoefficientIterationComputeComponent layout active_ne_equality).target =
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyCoefficientControl layout, historyEqualityFlag layout]
        (historyActiveWire layout) := rfl

private noncomputable def historyP15CoefficientIterationUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality :
      historyActiveWire layout ≠ historyEqualityFlag layout) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyCoefficientControl layout, historyEqualityFlag layout] []
    (historyActiveWire layout) (by simp)
    (historyP15CoefficientIterationConjunction_nodup layout active_ne_equality)
    (historyP15CoefficientIterationComputedActivePredicate layout)
    (historyP15CoefficientIterationCleanActivePredicate layout)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input computed
      unfold historyP15CoefficientIterationComputedActivePredicate at computed
      unfold historyP15CoefficientIterationCleanActivePredicate
      let action := ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyCoefficientControl layout, historyEqualityFlag layout]
        (historyActiveWire layout)
      change action input (historyActiveWire layout) = false
      rw [show action input (historyActiveWire layout) =
          (input (historyActiveWire layout) !=
            historyP15CoefficientIterationCondition layout input) by
          exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target
            _ _ _, computed]
      cases historyP15CoefficientIterationCondition layout input <;> rfl)

private theorem historyP15CoefficientIterationUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality :
      historyActiveWire layout ≠ historyEqualityFlag layout) :
    (historyP15CoefficientIterationUncomputeComponent layout active_ne_equality).target =
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyCoefficientControl layout, historyEqualityFlag layout]
        (historyActiveWire layout) := rfl

private noncomputable def historyP15CoefficientIterationUseComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_signal : historyActiveWire layout ≠ layout.coefficientSignal)
    (coefficientControl_ne_signal :
      historyCoefficientControl layout ≠ layout.coefficientSignal)
    (angle : AngleExpr) :=
  let exact := ExactOperatorComponent.refineTarget
    (historyClockCoefficientRotationExactComponent
      (historyActiveWire layout) layout.coefficientSignal active_ne_signal angle)
    (predicateControlledSingleQubitOperator
      (fun basis => basis (historyActiveWire layout)) layout.coefficientSignal
      (localRy angle.uniformValue))
    (embedControlledSingleQubitOperator_eq_predicateControlled
      (historyActiveWire layout) layout.coefficientSignal active_ne_signal
      (localRy angle.uniformValue))
  exact.toSubspaceMapOfOutsideSupport {layout.coefficientSignal}
    (OperatorPreservesOutside.predicateControlledSingleQubitOperator
      (fun basis => basis (historyActiveWire layout)) layout.coefficientSignal
      (localRy angle.uniformValue))
    (historyP15CoefficientIterationComputedActivePredicate layout)
    (historyP15CoefficientIterationComputedActivePredicate layout)
    (by
      intro input output computed sameOutside
      unfold historyP15CoefficientIterationComputedActivePredicate at computed ⊢
      have agrees : agreesExcept layout.coefficientSignal input output := by
        intro wire different
        exact (sameOutside wire (by simpa using different)).symm
      calc
        output (historyActiveWire layout) = input (historyActiveWire layout) :=
          sameOutside _ (by simp [active_ne_signal])
        _ = historyP15CoefficientIterationCondition layout input := computed
        _ = historyP15CoefficientIterationCondition layout output :=
          historyP15CoefficientIterationCondition_signalInvariant layout
            coefficientControl_ne_signal input output agrees)

private theorem historyP15CoefficientIterationUseComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_signal : historyActiveWire layout ≠ layout.coefficientSignal)
    (coefficientControl_ne_signal :
      historyCoefficientControl layout ≠ layout.coefficientSignal)
    (angle : AngleExpr) :
    (historyP15CoefficientIterationUseComponent layout active_ne_signal
      coefficientControl_ne_signal angle).target =
      predicateControlledSingleQubitOperator
        (fun basis => basis (historyActiveWire layout)) layout.coefficientSignal
        (localRy angle.uniformValue) := rfl

private theorem historyP15CoefficientIterationComputeUseUncomputeChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality : historyActiveWire layout ≠ historyEqualityFlag layout)
    (active_ne_signal : historyActiveWire layout ≠ layout.coefficientSignal)
    (coefficientControl_ne_signal :
      historyCoefficientControl layout ≠ layout.coefficientSignal)
    (angle : AngleExpr) :
    SubspaceMapComponent.SpaceChain
      [historyP15CoefficientIterationComputeComponent layout active_ne_equality,
       historyP15CoefficientIterationUseComponent layout active_ne_signal
         coefficientControl_ne_signal angle,
       historyP15CoefficientIterationUncomputeComponent layout active_ne_equality]
      (SubspaceMapComponent.basisSpan
        (historyP15CoefficientIterationCleanActivePredicate layout))
      (SubspaceMapComponent.basisSpan
        (historyP15CoefficientIterationCleanActivePredicate layout)) := by
  exact .cons _ [_, _] _ _ _ rfl rfl
    (.cons _ [_] _ _ _ rfl rfl
      (.cons _ [] _ _ _ rfl rfl (.nil _)))

private theorem historyP15CoefficientIterationConjunctionDirectOperator_eq_xorCompute
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ClassicalReversibleStage.conjunctionDirectOperator
        [historyCoefficientControl layout, historyEqualityFlag layout]
        (historyActiveWire layout) =
      deterministicOperator
        (historyP15XorComputeAction (historyActiveWire layout)
          (historyP15CoefficientIterationCondition layout)) := rfl

set_option maxHeartbeats 400000 in
private theorem historyP15CoefficientIterationComputeUseUncomputeSequence_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality : historyActiveWire layout ≠ historyEqualityFlag layout)
    (active_ne_signal : historyActiveWire layout ≠ layout.coefficientSignal)
    (coefficientControl_ne_signal :
      historyCoefficientControl layout ≠ layout.coefficientSignal)
    (angle : AngleExpr) :
    (SubspaceMapComponent.sequenceAlong
      (historyP15CoefficientIterationComputeUseUncomputeChain layout
        active_ne_equality active_ne_signal coefficientControl_ne_signal angle)).target =
      historyP15XorComputeUseUncomputeOperator (historyActiveWire layout)
        layout.coefficientSignal active_ne_signal
        (historyP15CoefficientIterationCondition layout)
        (localRy angle.uniformValue) := by
  rw [SubspaceMapComponent.sequenceAlong_target]
  simp only [List.map_cons, List.map_nil, operatorSequence]
  rw [historyP15CoefficientIterationComputeComponent_target,
    historyP15CoefficientIterationUseComponent_target,
    historyP15CoefficientIterationUncomputeComponent_target,
    ← embedControlledSingleQubitOperator_eq_predicateControlled
      (historyActiveWire layout) layout.coefficientSignal active_ne_signal
      (localRy angle.uniformValue)]
  simp only [one_mul,
    historyP15CoefficientIterationConjunctionDirectOperator_eq_xorCompute,
    historyP15XorComputeUseUncomputeOperator]

/-- Direct clean-subspace target of the actual coefficient-inner triple.
The condition reads the two preserved controls, not the temporary `active`
workspace wire. -/
noncomputable def historyP15CoefficientIterationInnerOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) : Operator (QubitBasis qubits) :=
  predicateControlledSingleQubitOperator
    (historyP15CoefficientIterationCondition layout) layout.coefficientSignal
    (localRy angle.uniformValue)

private theorem historyP15CoefficientIterationRecordedTarget_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality : historyActiveWire layout ≠ historyEqualityFlag layout)
    (active_ne_signal : historyActiveWire layout ≠ layout.coefficientSignal)
    (coefficientControl_ne_signal :
      historyCoefficientControl layout ≠ layout.coefficientSignal)
    (angle : AngleExpr) (input : QubitBasis qubits)
    (clean : historyP15CoefficientIterationCleanActivePredicate layout input) :
    applyOperator
        (SubspaceMapComponent.sequenceAlong
          (historyP15CoefficientIterationComputeUseUncomputeChain layout
            active_ne_equality active_ne_signal coefficientControl_ne_signal angle)).target
        (basisKet input) =
      applyOperator (historyP15CoefficientIterationInnerOperator layout angle)
        (basisKet input) := by
  rw [historyP15CoefficientIterationComputeUseUncomputeSequence_target]
  change input (historyActiveWire layout) = false at clean
  simpa only [historyP15CoefficientIterationInnerOperator] using
    (historyP15_applyOperator_xorComputeUseUncompute_basisKet
      (historyActiveWire layout) layout.coefficientSignal active_ne_signal
      (historyP15CoefficientIterationCondition layout)
      (localRy angle.uniformValue)
      (historyP15CoefficientIterationCondition_activeInvariant layout
        active_ne_equality)
      (historyP15CoefficientIterationCondition_signalInvariant layout
        coefficientControl_ne_signal)
      input clean)

/-- The actual single coefficient-rotation occurrence, packaged only on the
sector where its temporary `active` workspace enters clean.  The target reads
the preserved coefficient/equality controls directly and returns that
workspace to the same clean sector. -/
noncomputable def historyP15CoefficientIterationComputeUseUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality : historyActiveWire layout ≠ historyEqualityFlag layout)
    (active_ne_signal : historyActiveWire layout ≠ layout.coefficientSignal)
    (coefficientControl_ne_signal :
      historyCoefficientControl layout ≠ layout.coefficientSignal)
    (angle : AngleExpr) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let chain := historyP15CoefficientIterationComputeUseUncomputeChain layout
    active_ne_equality active_ne_signal coefficientControl_ne_signal angle
  let sequence := SubspaceMapComponent.sequenceAlong chain
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits)) sequence.circuit
    (historyP15CoefficientIterationInnerOperator layout angle)
    (historyP15CoefficientIterationCleanActivePredicate layout)
    (historyP15CoefficientIterationCleanActivePredicate layout)
    (by
      intro input clean
      calc
        applyOperator (Circuit.denote (historyP15PostGate (qubits := qubits)) sequence.circuit)
            (basisKet input) =
          applyOperator sequence.target (basisKet input) :=
            sequence.correct _
              (SubspaceMapComponent.basisKet_mem_basisSpan clean)
        _ = applyOperator (historyP15CoefficientIterationInnerOperator layout angle)
            (basisKet input) :=
          historyP15CoefficientIterationRecordedTarget_basisKet layout
            active_ne_equality active_ne_signal coefficientControl_ne_signal
            angle input clean)
    (by
      intro input clean
      apply SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_preservesOutside
        (historyP15CoefficientIterationInnerOperator layout angle)
        {layout.coefficientSignal}
        (OperatorPreservesOutside.predicateControlledSingleQubitOperator
          (historyP15CoefficientIterationCondition layout)
          layout.coefficientSignal (localRy angle.uniformValue))
        (historyP15CoefficientIterationCleanActivePredicate layout)
        (historyP15CoefficientIterationCleanActivePredicate layout)
        (by
          intro before after beforeClean sameOutside
          unfold historyP15CoefficientIterationCleanActivePredicate at beforeClean ⊢
          rw [sameOutside (historyActiveWire layout) (by
            simp [active_ne_signal])]
          exact beforeClean)
        input clean)

/-! ### Full coefficient iteration: equality, active workspace, rotation -/

private theorem historyP15Active_ne_equalityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyActiveWire layout ≠ historyEqualityFlag layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

private theorem historyP15Active_ne_coefficientSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyActiveWire layout ≠ layout.coefficientSignal := by
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  change layout.workspace.wire _ ≠ layout.coefficientSignal
  exact separated.2.2 _

private theorem historyP15CoefficientControl_ne_coefficientSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ≠ layout.coefficientSignal := by
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  change layout.workspace.wire _ ≠ layout.coefficientSignal
  exact separated.2.2 _

private theorem historyP15EqualityWork_wire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyEqualityWorkWidth parameters)) :
    (historyEqualityWork layout).wire index ∈ historyRegisterWires layout.workspace := by
  unfold historyEqualityWork
  apply historyWorkspaceSlice_wire_mem

private theorem historyP15EqualityFlag_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyEqualityFlag layout ∈ historyRegisterWires layout.workspace := by
  unfold historyEqualityFlag
  apply historyWorkspaceSlice_wire_mem

private theorem historyP15EqualityWorkWire_ne_equalityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyEqualityWorkWidth parameters)) :
    (historyEqualityWork layout).wire index ≠ historyEqualityFlag layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

private theorem historyP15EqualityWorkWire_ne_coefficientSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyEqualityWorkWidth parameters)) :
    (historyEqualityWork layout).wire index ≠ layout.coefficientSignal := by
  have member := historyP15EqualityWork_wire_mem_workspace layout index
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, equal⟩
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  intro same
  exact separated.2.2 workspaceIndex (equal.trans same)

private theorem historyP15CoefficientEquality_enoughScratch
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyRegisterWires layout.order).length ≤
      (historyRegisterWires (historyEqualityWork layout)).length + 2 := by
  simp only [historyRegisterWires, List.length_ofFn]
  unfold historyEqualityWorkWidth historyMaximumLabelWidth
  omega

private theorem historyP15CoefficientEqualityLayout_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyRegisterWires layout.order ++
      historyRegisterWires (historyEqualityWork layout) ++
      [historyEqualityFlag layout]).Nodup := by
  rw [List.append_assoc]
  apply List.nodup_append.mpr
  refine ⟨historyRegisterWires_nodup layout.order, ?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨historyRegisterWires_nodup (historyEqualityWork layout), by simp, ?_⟩
    intro workWire workMember flagWire flagMember
    simp only [List.mem_singleton] at flagMember
    subst flagWire
    simp only [historyRegisterWires, List.mem_ofFn] at workMember
    rcases workMember with ⟨workIndex, rfl⟩
    exact historyP15EqualityWorkWire_ne_equalityFlag layout workIndex
  · intro orderWire orderMember trailing trailingMember
    simp only [historyRegisterWires, List.mem_ofFn] at orderMember
    rcases orderMember with ⟨orderIndex, rfl⟩
    rcases List.mem_append.mp trailingMember with workMember | flagMember
    · simp only [historyRegisterWires, List.mem_ofFn] at workMember
      rcases workMember with ⟨workIndex, rfl⟩
      have workspaceMember :=
        historyP15EqualityWork_wire_mem_workspace layout workIndex
      rcases List.mem_ofFn.mp workspaceMember with ⟨workspaceIndex, equal⟩
      intro same
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (same.trans equal.symm)
    · simp only [List.mem_singleton] at flagMember
      subst trailing
      have workspaceMember := historyP15EqualityFlag_mem_workspace layout
      rcases List.mem_ofFn.mp workspaceMember with ⟨workspaceIndex, equal⟩
      intro same
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (same.trans equal.symm)

/-- The clean entrance/exit sector of each complete coefficient iteration.
It records exactly the equality compiler work, equality flag, and temporary
active wire which must all be restored by the five-stage source word. -/
def historyP15CoefficientIterationCleanPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyEqualityFlag layout) = false ∧
    ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) basis ∧
    basis (historyActiveWire layout) = false

/-- Middle boundary after the equality compiler has materialized the current
`order = index + 1` predicate, while its work and the active workspace remain
clean. -/
def historyP15CoefficientIterationEqualityComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) (basis : QubitBasis qubits) : Prop :=
  basis (historyEqualityFlag layout) =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1) basis ∧
    ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) basis ∧
    basis (historyActiveWire layout) = false

/-- Direct clean-subspace target of a complete coefficient iteration. -/
noncomputable def historyP15CoefficientIterationOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    Operator (QubitBasis qubits) :=
  predicateControlledSingleQubitOperator
    (fun basis => basis (historyCoefficientControl layout) &&
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1) basis)
    layout.coefficientSignal (localRy angle.uniformValue)

private noncomputable def historyP15XorComputeGuardedUseUncomputeOperator
    {qubits : Nat} (control target : Fin qubits)
    (condition guard : QubitBasis qubits → Bool)
    (localOperator : Matrix Bool Bool ℂ) : Operator (QubitBasis qubits) :=
  (deterministicOperator (historyP15XorComputeAction control condition) *
      predicateControlledSingleQubitOperator
        (fun basis => guard basis && basis control) target localOperator) *
    deterministicOperator (historyP15XorComputeAction control condition)

/-- Matrix-entry form of an outer XOR compute--use--uncompute in which the
middle controlled operation also has a preserved Boolean guard.  The middle
operation may create a target superposition; this remains a clean-input ket
identity, never a claimed whole-space equality. -/
private theorem historyP15_applyOperator_xorCompute_guardedUseUncompute_basisKet
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (condition guard : QubitBasis qubits → Bool)
    (localOperator : Matrix Bool Bool ℂ)
    (conditionControlIndependent : ∀ first second,
      agreesExcept control first second → condition first = condition second)
    (conditionTargetIndependent : ∀ first second,
      agreesExcept target first second → condition first = condition second)
    (guardControlIndependent : ∀ first second,
      agreesExcept control first second → guard first = guard second)
    (input : QubitBasis qubits) (controlClean : input control = false) :
    applyOperator
        (historyP15XorComputeGuardedUseUncomputeOperator control target
          condition guard localOperator)
        (basisKet input) =
      applyOperator
        (predicateControlledSingleQubitOperator
          (fun basis => guard basis && condition basis) target localOperator)
        (basisKet input) := by
  have actionInvolutive : Function.Involutive
      (historyP15XorComputeAction control condition) :=
    historyP15XorComputeAction_involutive control condition
      conditionControlIndependent
  have actionControl (state : QubitBasis qubits)
      (clean : state control = false) :
      historyP15XorComputeAction control condition state control =
        condition state := by
    unfold historyP15XorComputeAction
    rw [xorWire_apply_same, clean]
    cases condition state <;> rfl
  have actionTarget (state : QubitBasis qubits) :
      historyP15XorComputeAction control condition state target = state target := by
    unfold historyP15XorComputeAction
    exact xorWire_apply_other control target different.symm _ state
  funext output
  unfold historyP15XorComputeGuardedUseUncomputeOperator
  rw [applyOperator_basisKet, applyOperator_basisKet]
  rw [deterministicOperator_eq_permMatrix_of_involutive
    (historyP15XorComputeAction control condition) actionInvolutive]
  rw [permMatrix_conjugate_operator_apply
    (involutiveBasisEquiv (historyP15XorComputeAction control condition)
      actionInvolutive) (by rfl)]
  change predicateControlledSingleQubitOperator
      (fun basis => guard basis && basis control) target localOperator
      (historyP15XorComputeAction control condition output)
      (historyP15XorComputeAction control condition input) =
    predicateControlledSingleQubitOperator
      (fun basis => guard basis && condition basis) target localOperator output input
  rw [predicateControlledSingleQubitOperator_apply,
    predicateControlledSingleQubitOperator_apply]
  by_cases originalAgreement : agreesExcept target output input
  · have conditionAgreement : condition output = condition input :=
      conditionTargetIndependent output input originalAgreement
    have transformedAgreement : agreesExcept target
        (historyP15XorComputeAction control condition output)
        (historyP15XorComputeAction control condition input) := by
      intro wire wireDifferent
      by_cases wireControl : wire = control
      · subst wire
        rw [actionControl output (by
          have controlEqual := originalAgreement control different
          simpa [controlEqual] using controlClean),
          actionControl input controlClean, conditionAgreement]
      · rw [show historyP15XorComputeAction control condition output wire =
            output wire by
            unfold historyP15XorComputeAction
            exact xorWire_apply_other control wire wireControl _ output,
          show historyP15XorComputeAction control condition input wire =
            input wire by
            unfold historyP15XorComputeAction
            exact xorWire_apply_other control wire wireControl _ input]
        exact originalAgreement wire wireDifferent
    have guardCompute :
        guard (historyP15XorComputeAction control condition input) = guard input :=
      guardControlIndependent _ _
        (historyP15XorComputeAction_agreesExcept_control control condition input)
    rw [if_pos transformedAgreement, if_pos originalAgreement,
      guardCompute, actionControl input controlClean,
      actionTarget output, actionTarget input]
  · have transformedDisagreement : ¬ agreesExcept target
        (historyP15XorComputeAction control condition output)
        (historyP15XorComputeAction control condition input) := by
      intro transformedAgreement
      apply originalAgreement
      have conditionOutputCompute :
          condition (historyP15XorComputeAction control condition output) =
            condition output :=
        historyP15XorComputeAction_condition_stable control condition
          conditionControlIndependent output
      have conditionInputCompute :
          condition (historyP15XorComputeAction control condition input) =
            condition input :=
        historyP15XorComputeAction_condition_stable control condition
          conditionControlIndependent input
      have conditionAgreement : condition output = condition input := by
        rw [← conditionOutputCompute, ← conditionInputCompute]
        exact conditionTargetIndependent _ _ transformedAgreement
      intro wire wireDifferent
      by_cases wireControl : wire = control
      · subst wire
        have controlOutputClean : output control = false := by
          have controlEqual := transformedAgreement control different
          unfold historyP15XorComputeAction at controlEqual
          rw [xorWire_apply_same, xorWire_apply_same, controlClean,
            ← conditionAgreement] at controlEqual
          cases hOutput : output control <;>
          cases hCondition : condition input <;>
          simp [hOutput] at controlEqual ⊢
        exact controlOutputClean.trans controlClean.symm
      · have equal := transformedAgreement wire wireDifferent
        rw [show historyP15XorComputeAction control condition output wire =
              output wire by
              unfold historyP15XorComputeAction
              exact xorWire_apply_other control wire wireControl _ output,
            show historyP15XorComputeAction control condition input wire =
              input wire by
              unfold historyP15XorComputeAction
              exact xorWire_apply_other control wire wireControl _ input] at equal
        exact equal
    simp [transformedDisagreement, originalAgreement]

private theorem historyP15OrderWire_ne_equalityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (orderIndex : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire orderIndex ≠ historyEqualityFlag layout := by
  have workspaceMember := historyP15EqualityFlag_mem_workspace layout
  rcases List.mem_ofFn.mp workspaceMember with ⟨workspaceIndex, workspaceEqual⟩
  intro equal
  exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
    (equal.trans workspaceEqual.symm)

private theorem historyP15OrderEqualsIndex_equalityActionInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) (input : QubitBasis qubits) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1)
        (ClassicalReversibleStage.equalityToConstantDirectBasisAction
          (historyRegisterWires layout.order) (index.val + 1)
          (historyEqualityFlag layout) input) =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1) input := by
  apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
  intro wire wireMember
  simp only [historyRegisterWires, List.mem_ofFn] at wireMember
  rcases wireMember with ⟨orderIndex, rfl⟩
  exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
    (historyRegisterWires layout.order) (index.val + 1)
    (historyEqualityFlag layout) (layout.order.wire orderIndex)
    (historyP15OrderWire_ne_equalityFlag layout orderIndex) input

private theorem historyP15OrderEqualsIndex_equalityFlagInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyEqualityFlag layout) first second) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1) first =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1) second := by
  apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
  intro wire wireMember
  simp only [historyRegisterWires, List.mem_ofFn] at wireMember
  rcases wireMember with ⟨orderIndex, rfl⟩
  apply same
  exact historyP15OrderWire_ne_equalityFlag layout orderIndex

private theorem historyP15OrderEqualsIndex_signalInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder)
    (first second : QubitBasis qubits)
    (same : agreesExcept layout.coefficientSignal first second) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1) first =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1) second := by
  apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
  intro wire wireMember
  simp only [historyRegisterWires, List.mem_ofFn] at wireMember
  rcases wireMember with ⟨orderIndex, rfl⟩
  exact same _ ((layout.orderWire_separated orderIndex).2.2.1
    layout.coefficientSignal (by simp))

private theorem historyP15CoefficientControl_equalityFlagInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyEqualityFlag layout) first second) :
    first (historyCoefficientControl layout) =
      second (historyCoefficientControl layout) :=
  same _ (historyP15CoefficientControl_ne_equalityFlag layout)

@[simp] theorem historyP15CoefficientIterationComputeUseUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_equality : historyActiveWire layout ≠ historyEqualityFlag layout)
    (active_ne_signal : historyActiveWire layout ≠ layout.coefficientSignal)
    (coefficientControl_ne_signal :
      historyCoefficientControl layout ≠ layout.coefficientSignal)
    (angle : AngleExpr) :
    (historyP15CoefficientIterationComputeUseUncomputeComponent layout
      active_ne_equality active_ne_signal coefficientControl_ne_signal angle).target =
      historyP15CoefficientIterationInnerOperator layout angle := rfl

private noncomputable def historyP15CoefficientIterationEqualityComputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) :=
  ClassicalReversibleStage.xorEqualityToConstantMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (historyRegisterWires layout.order)
    (historyRegisterWires (historyEqualityWork layout)) (index.val + 1)
    (historyEqualityFlag layout)
    (historyP15CoefficientEquality_enoughScratch layout)
    (historyP15CoefficientEqualityLayout_nodup layout)
    (historyP15CoefficientIterationCleanPredicate layout)
    (historyP15CoefficientIterationEqualityComputedPredicate layout index)
    (by
      intro input inside
      unfold historyP15CoefficientIterationCleanPredicate at inside
      exact inside.2.1)
    (by
      intro input inside
      unfold historyP15CoefficientIterationCleanPredicate at inside
      unfold historyP15CoefficientIterationEqualityComputedPredicate
      have orderStable :=
        historyP15OrderEqualsIndex_equalityActionInvariant layout index input
      refine ⟨?_, ?_, ?_⟩
      · rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
          inside.1, orderStable]
        cases h : ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) input <;> rfl
      · exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_clean
          (historyRegisterWires layout.order)
          (historyRegisterWires (historyEqualityWork layout)) (index.val + 1)
          (historyEqualityFlag layout) input
          (historyP15CoefficientEqualityLayout_nodup layout) inside.2.1
      · rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order) (index.val + 1)
          (historyEqualityFlag layout) (historyActiveWire layout)
          (historyP15Active_ne_equalityFlag layout) input]
        exact inside.2.2)

private theorem historyP15CoefficientIterationEqualityComputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) :
    (historyP15CoefficientIterationEqualityComputeComponent layout index).target =
      ClassicalReversibleStage.equalityToConstantDirectOperator
        (historyRegisterWires layout.order) (index.val + 1)
        (historyEqualityFlag layout) := rfl

private noncomputable def historyP15CoefficientIterationEqualityUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) :=
  ClassicalReversibleStage.xorEqualityToConstantMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (historyRegisterWires layout.order)
    (historyRegisterWires (historyEqualityWork layout)) (index.val + 1)
    (historyEqualityFlag layout)
    (historyP15CoefficientEquality_enoughScratch layout)
    (historyP15CoefficientEqualityLayout_nodup layout)
    (historyP15CoefficientIterationEqualityComputedPredicate layout index)
    (historyP15CoefficientIterationCleanPredicate layout)
    (by
      intro input inside
      unfold historyP15CoefficientIterationEqualityComputedPredicate at inside
      exact inside.2.1)
    (by
      intro input inside
      unfold historyP15CoefficientIterationEqualityComputedPredicate at inside
      unfold historyP15CoefficientIterationCleanPredicate
      refine ⟨?_, ?_, ?_⟩
      · rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
          inside.1]
        cases h : ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) input <;> rfl
      · exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_clean
          (historyRegisterWires layout.order)
          (historyRegisterWires (historyEqualityWork layout)) (index.val + 1)
          (historyEqualityFlag layout) input
          (historyP15CoefficientEqualityLayout_nodup layout) inside.2.1
      · rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order) (index.val + 1)
          (historyEqualityFlag layout) (historyActiveWire layout)
          (historyP15Active_ne_equalityFlag layout) input]
        exact inside.2.2)

private theorem historyP15CoefficientIterationEqualityUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) :
    (historyP15CoefficientIterationEqualityUncomputeComponent layout index).target =
      ClassicalReversibleStage.equalityToConstantDirectOperator
        (historyRegisterWires layout.order) (index.val + 1)
        (historyEqualityFlag layout) := rfl

private theorem historyP15CoefficientIterationCleanPredicate_stableOutsideSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (before after : QubitBasis qubits)
    (inside : historyP15CoefficientIterationCleanPredicate layout before)
    (sameOutside : ∀ wire : Fin qubits,
      wire ∉ ({layout.coefficientSignal} : Finset (Fin qubits)) →
      after wire = before wire) :
    historyP15CoefficientIterationCleanPredicate layout after := by
  unfold historyP15CoefficientIterationCleanPredicate at inside ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [sameOutside (historyEqualityFlag layout) (by
      simp [historyP15EqualityFlag_ne_coefficientSignal])]
    exact inside.1
  · intro wire member
    have wireMember := member
    simp only [historyRegisterWires, List.mem_ofFn] at wireMember
    rcases wireMember with ⟨workIndex, rfl⟩
    rw [sameOutside _ (by
      simp [historyP15EqualityWorkWire_ne_coefficientSignal layout workIndex])]
    exact inside.2.1 _ member
  · rw [sameOutside (historyActiveWire layout) (by
      simp [historyP15Active_ne_coefficientSignal])]
    exact inside.2.2

private theorem historyP15CoefficientIterationEqualityComputedPredicate_stableOutsideSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder)
    (before after : QubitBasis qubits)
    (inside : historyP15CoefficientIterationEqualityComputedPredicate layout index before)
    (sameOutside : ∀ wire : Fin qubits,
      wire ∉ ({layout.coefficientSignal} : Finset (Fin qubits)) →
      after wire = before wire) :
    historyP15CoefficientIterationEqualityComputedPredicate layout index after := by
  unfold historyP15CoefficientIterationEqualityComputedPredicate at inside ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [sameOutside (historyEqualityFlag layout) (by
      simp [historyP15EqualityFlag_ne_coefficientSignal])]
    have orderStable := historyP15OrderEqualsIndex_signalInvariant layout index
      before after (by
        intro wire different
        exact (sameOutside wire (by simpa using different)).symm)
    rw [← orderStable]
    exact inside.1
  · intro wire member
    have wireMember := member
    simp only [historyRegisterWires, List.mem_ofFn] at wireMember
    rcases wireMember with ⟨workIndex, rfl⟩
    rw [sameOutside _ (by
      simp [historyP15EqualityWorkWire_ne_coefficientSignal layout workIndex])]
    exact inside.2.1 _ member
  · rw [sameOutside (historyActiveWire layout) (by
      simp [historyP15Active_ne_coefficientSignal])]
    exact inside.2.2

private noncomputable def historyP15CoefficientIterationActiveOnEqualityComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) (angle : AngleExpr) :=
  let inner := historyP15CoefficientIterationComputeUseUncomputeComponent layout
    (historyP15Active_ne_equalityFlag layout)
    (historyP15Active_ne_coefficientSignal layout)
    (historyP15CoefficientControl_ne_coefficientSignal layout) angle
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    inner.circuit (historyP15CoefficientIterationInnerOperator layout angle)
    (historyP15CoefficientIterationEqualityComputedPredicate layout index)
    (historyP15CoefficientIterationEqualityComputedPredicate layout index)
    (by
      intro input inside
      calc
        applyOperator
            (Circuit.denote (historyP15PostGate (qubits := qubits)) inner.circuit)
            (basisKet input) =
          applyOperator inner.target (basisKet input) :=
            inner.correct _
              (SubspaceMapComponent.basisKet_mem_basisSpan inside.2.2)
        _ = applyOperator (historyP15CoefficientIterationInnerOperator layout angle)
            (basisKet input) :=
          congrArg (fun operator => applyOperator operator (basisKet input))
            (historyP15CoefficientIterationComputeUseUncomputeComponent_target layout
              (historyP15Active_ne_equalityFlag layout)
              (historyP15Active_ne_coefficientSignal layout)
              (historyP15CoefficientControl_ne_coefficientSignal layout) angle))
    (by
      intro input inside
      exact SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_preservesOutside
        (historyP15CoefficientIterationInnerOperator layout angle)
        {layout.coefficientSignal}
        (OperatorPreservesOutside.predicateControlledSingleQubitOperator
          (historyP15CoefficientIterationCondition layout)
          layout.coefficientSignal (localRy angle.uniformValue))
        (historyP15CoefficientIterationEqualityComputedPredicate layout index)
        (historyP15CoefficientIterationEqualityComputedPredicate layout index)
        (historyP15CoefficientIterationEqualityComputedPredicate_stableOutsideSignal
          layout index) input inside)

private theorem historyP15CoefficientIterationActiveOnEqualityComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) (angle : AngleExpr) :
    (historyP15CoefficientIterationActiveOnEqualityComponent layout index angle).target =
      historyP15CoefficientIterationInnerOperator layout angle := rfl

private theorem historyP15CoefficientIterationInnerOperator_eq_guarded
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    historyP15CoefficientIterationInnerOperator layout angle =
      predicateControlledSingleQubitOperator
        (fun basis => basis (historyCoefficientControl layout) &&
          basis (historyEqualityFlag layout))
        layout.coefficientSignal (localRy angle.uniformValue) := by
  apply congrArg (fun predicate : QubitBasis qubits → Bool =>
    predicateControlledSingleQubitOperator predicate layout.coefficientSignal
      (localRy angle.uniformValue))
  funext basis
  unfold historyP15CoefficientIterationCondition
    ClassicalReversibleStage.allWiresTrue ClassicalReversibleStage.readWires
  simp

private theorem historyP15CoefficientIterationEqualityDirectOperator_eq_xorCompute
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) :
    ClassicalReversibleStage.equalityToConstantDirectOperator
        (historyRegisterWires layout.order) (index.val + 1)
        (historyEqualityFlag layout) =
      deterministicOperator
        (historyP15XorComputeAction (historyEqualityFlag layout)
          (fun basis => ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order) (index.val + 1) basis)) := rfl

private theorem historyP15CoefficientIterationFullChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) (angle : AngleExpr) :
    SubspaceMapComponent.SpaceChain
      [historyP15CoefficientIterationEqualityComputeComponent layout index,
       historyP15CoefficientIterationActiveOnEqualityComponent layout index angle,
       historyP15CoefficientIterationEqualityUncomputeComponent layout index]
      (SubspaceMapComponent.basisSpan
        (historyP15CoefficientIterationCleanPredicate layout))
      (SubspaceMapComponent.basisSpan
        (historyP15CoefficientIterationCleanPredicate layout)) := by
  exact .cons _ [_, _] _ _ _ rfl rfl
    (.cons _ [_] _ _ _ rfl rfl
      (.cons _ [] _ _ _ rfl rfl (.nil _)))

private noncomputable def historyP15CoefficientIterationRawComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) (angle : AngleExpr) :=
  SubspaceMapComponent.sequenceAlong
    (historyP15CoefficientIterationFullChain layout index angle)

private theorem historyP15CoefficientIterationRawComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) (angle : AngleExpr) :
    (historyP15CoefficientIterationRawComponent layout index angle).target =
      historyP15XorComputeGuardedUseUncomputeOperator
        (historyEqualityFlag layout) layout.coefficientSignal
        (fun basis => ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) basis)
        (fun basis => basis (historyCoefficientControl layout))
        (localRy angle.uniformValue) := by
  rw [show (historyP15CoefficientIterationRawComponent layout index angle).target =
      (SubspaceMapComponent.sequenceAlong
        (historyP15CoefficientIterationFullChain layout index angle)).target by rfl,
    SubspaceMapComponent.sequenceAlong_target]
  simp only [List.map_cons, List.map_nil, operatorSequence]
  rw [historyP15CoefficientIterationEqualityComputeComponent_target,
    historyP15CoefficientIterationActiveOnEqualityComponent_target,
    historyP15CoefficientIterationEqualityUncomputeComponent_target,
    historyP15CoefficientIterationEqualityDirectOperator_eq_xorCompute,
    historyP15CoefficientIterationInnerOperator_eq_guarded]
  simp only [one_mul, historyP15XorComputeGuardedUseUncomputeOperator]

private theorem historyP15CoefficientIterationRawTarget_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) (angle : AngleExpr)
    (input : QubitBasis qubits)
    (clean : historyP15CoefficientIterationCleanPredicate layout input) :
    applyOperator (historyP15CoefficientIterationRawComponent layout index angle).target
        (basisKet input) =
      applyOperator (historyP15CoefficientIterationOperator layout angle index)
        (basisKet input) := by
  rw [historyP15CoefficientIterationRawComponent_target]
  unfold historyP15CoefficientIterationCleanPredicate at clean
  simpa only [historyP15CoefficientIterationOperator] using
    (historyP15_applyOperator_xorCompute_guardedUseUncompute_basisKet
      (historyEqualityFlag layout) layout.coefficientSignal
      (historyP15EqualityFlag_ne_coefficientSignal layout)
      (fun basis => ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1) basis)
      (fun basis => basis (historyCoefficientControl layout))
      (localRy angle.uniformValue)
      (historyP15OrderEqualsIndex_equalityFlagInvariant layout index)
      (historyP15OrderEqualsIndex_signalInvariant layout index)
      (historyP15CoefficientControl_equalityFlagInvariant layout)
      input clean.1)

/-- The actual five-stage coefficient iteration, with equality and active
ancillas explicitly clean both before and after the source occurrence. -/
noncomputable def historyP15CoefficientIterationComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let raw := historyP15CoefficientIterationRawComponent layout index angle
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    raw.circuit (historyP15CoefficientIterationOperator layout angle index)
    (historyP15CoefficientIterationCleanPredicate layout)
    (historyP15CoefficientIterationCleanPredicate layout)
    (by
      intro input clean
      calc
        applyOperator
            (Circuit.denote (historyP15PostGate (qubits := qubits)) raw.circuit)
            (basisKet input) =
          applyOperator raw.target (basisKet input) :=
            raw.correct _
              (SubspaceMapComponent.basisKet_mem_basisSpan clean)
        _ = applyOperator (historyP15CoefficientIterationOperator layout angle index)
            (basisKet input) :=
          historyP15CoefficientIterationRawTarget_basisKet layout index angle
            input clean)
    (by
      intro input clean
      exact SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_preservesOutside
        (historyP15CoefficientIterationOperator layout angle index)
        {layout.coefficientSignal}
        (OperatorPreservesOutside.predicateControlledSingleQubitOperator
          (fun basis => basis (historyCoefficientControl layout) &&
            ClassicalReversibleStage.littleEndianRegisterEqualsNat
              (historyRegisterWires layout.order) (index.val + 1) basis)
          layout.coefficientSignal (localRy angle.uniformValue))
        (historyP15CoefficientIterationCleanPredicate layout)
        (historyP15CoefficientIterationCleanPredicate layout)
        (historyP15CoefficientIterationCleanPredicate_stableOutsideSignal layout)
        input clean)

@[simp] theorem historyP15CoefficientIterationComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    (historyP15CoefficientIterationComponent layout angle index).target =
      historyP15CoefficientIterationOperator layout angle index := rfl

@[simp] theorem historyP15CoefficientIterationComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    (historyP15CoefficientIterationComponent layout angle index).inputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15CoefficientIterationCleanPredicate layout) ∧
      (historyP15CoefficientIterationComponent layout angle index).outputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15CoefficientIterationCleanPredicate layout) := by
  constructor <;> rfl

/-- The five direct source-order children for one Taylor-coefficient
occurrence: equality compute, active compute, controlled rotation, active
uncompute, and equality uncompute. -/
noncomputable def historyP15CoefficientIterationSourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    List (Circuit (PrimitiveGate qubits)) :=
    [(historyP15CoefficientIterationEqualityComputeComponent layout index).circuit,
     (historyP15CoefficientIterationComputeComponent layout
       (historyP15Active_ne_equalityFlag layout)).circuit,
     (historyP15CoefficientIterationUseComponent layout
       (historyP15Active_ne_coefficientSignal layout)
       (historyP15CoefficientControl_ne_coefficientSignal layout) angle).circuit,
     (historyP15CoefficientIterationUncomputeComponent layout
       (historyP15Active_ne_equalityFlag layout)).circuit,
     (historyP15CoefficientIterationEqualityUncomputeComponent layout index).circuit]

/-- The source-order circuit for one Taylor-coefficient occurrence. -/
noncomputable def historyP15CoefficientIterationSourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence (historyP15CoefficientIterationSourceStages layout angle index)

private theorem historyP15CoefficientIterationInnerComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    (historyP15CoefficientIterationComputeUseUncomputeComponent layout
      (historyP15Active_ne_equalityFlag layout)
      (historyP15Active_ne_coefficientSignal layout)
      (historyP15CoefficientControl_ne_coefficientSignal layout) angle).circuit =
      Circuit.sequence
        [(historyP15CoefficientIterationComputeComponent layout
          (historyP15Active_ne_equalityFlag layout)).circuit,
         (historyP15CoefficientIterationUseComponent layout
          (historyP15Active_ne_coefficientSignal layout)
          (historyP15CoefficientControl_ne_coefficientSignal layout) angle).circuit,
         (historyP15CoefficientIterationUncomputeComponent layout
          (historyP15Active_ne_equalityFlag layout)).circuit] := rfl

private theorem historyP15CoefficientIterationActiveOnEqualityComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) (angle : AngleExpr) :
    (historyP15CoefficientIterationActiveOnEqualityComponent layout index angle).circuit =
      (historyP15CoefficientIterationComputeUseUncomputeComponent layout
        (historyP15Active_ne_equalityFlag layout)
        (historyP15Active_ne_coefficientSignal layout)
        (historyP15CoefficientControl_ne_coefficientSignal layout) angle).circuit := rfl

private theorem historyP15CoefficientIterationRawComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) (angle : AngleExpr) :
    (historyP15CoefficientIterationRawComponent layout index angle).circuit =
      Circuit.sequence
        [(historyP15CoefficientIterationEqualityComputeComponent layout index).circuit,
         (historyP15CoefficientIterationActiveOnEqualityComponent layout index angle).circuit,
         (historyP15CoefficientIterationEqualityUncomputeComponent layout index).circuit] := rfl

@[simp] theorem historyP15CoefficientIterationComponent_circuit_eq_raw
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    (historyP15CoefficientIterationComponent layout angle index).circuit =
      (historyP15CoefficientIterationRawComponent layout index angle).circuit := rfl

/-- The public clean-subspace iteration has the same primitive-gate stream as
the five-stage source construction. -/
theorem historyP15CoefficientIterationComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    (historyP15CoefficientIterationComponent layout angle index).circuit.flatten =
      (historyP15CoefficientIterationSourceCircuit layout angle index).flatten := by
  rw [historyP15CoefficientIterationComponent_circuit_eq_raw,
    historyP15CoefficientIterationRawComponent_circuit,
    historyP15CoefficientIterationActiveOnEqualityComponent_circuit,
    historyP15CoefficientIterationInnerComponent_circuit]
  simp [historyP15CoefficientIterationSourceCircuit,
    historyP15CoefficientIterationSourceStages, Circuit.sequence,
    Circuit.flatten, List.append_assoc]

/-- The source-order product of all clean-subspace Taylor coefficient
iterations.  The supplied angle family remains entirely external. -/
noncomputable def historyP15CoefficientLoopOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    Operator (QubitBasis qubits) :=
  operatorSequence ((List.finRange parameters.taylorOrder).map
    (fun index => historyP15CoefficientIterationOperator layout (angles index) index))

private noncomputable def historyP15CoefficientLoopComponents
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    List (SubspaceMapComponent (historyP15PostGate (qubits := qubits))) :=
  (List.finRange parameters.taylorOrder).map
    (fun index => historyP15CoefficientIterationComponent layout (angles index) index)

private theorem historyP15CoefficientLoopChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    SubspaceMapComponent.SpaceChain
      (historyP15CoefficientLoopComponents layout angles)
      (SubspaceMapComponent.basisSpan
        (historyP15CoefficientIterationCleanPredicate layout))
      (SubspaceMapComponent.basisSpan
        (historyP15CoefficientIterationCleanPredicate layout)) := by
  apply SubspaceMapComponent.SpaceChain.ofCommon
  intro component componentMember
  simp only [historyP15CoefficientLoopComponents, List.mem_map] at componentMember
  rcases componentMember with ⟨index, _, rfl⟩
  exact historyP15CoefficientIterationComponent_spaces layout (angles index) index

/-- The actual coefficient loop, typed on the sector in which every temporary
equality, equality-work, and active ancilla is clean between iterations. -/
noncomputable def historyP15CoefficientLoopComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let chain := historyP15CoefficientLoopChain layout angles
  (SubspaceMapComponent.sequenceAlong chain).refineTarget
    (historyP15CoefficientLoopOperator layout angles)
    (by
      rw [SubspaceMapComponent.sequenceAlong_target]
      unfold historyP15CoefficientLoopComponents
        historyP15CoefficientLoopOperator
      simp only [List.map_map]
      apply congrArg operatorSequence
      apply List.map_congr_left
      intro index _
      exact historyP15CoefficientIterationComponent_target layout (angles index) index)

@[simp] theorem historyP15CoefficientLoopComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    (historyP15CoefficientLoopComponent layout angles).target =
      historyP15CoefficientLoopOperator layout angles := rfl

@[simp] theorem historyP15CoefficientLoopComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    (historyP15CoefficientLoopComponent layout angles).circuit =
      Circuit.sequence
        ((historyP15CoefficientLoopComponents layout angles).map
          (fun component => component.circuit)) := rfl

/-- The flattened source circuit for the whole Taylor coefficient loop: each
index contributes the same five source stages in increasing `finRange` order. -/
noncomputable def historyP15CoefficientLoopSourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence ((List.finRange parameters.taylorOrder).flatMap
    (fun index => historyP15CoefficientIterationSourceStages layout
      (angles index) index))

private theorem historyP15CoefficientIterationComponent_flatten_eq_sourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    (historyP15CoefficientIterationComponent layout angle index).circuit.flatten =
      (historyP15CoefficientIterationSourceStages layout angle index).flatMap
        Circuit.flatten := by
  rw [historyP15CoefficientIterationComponent_flatten_eq_source]
  unfold historyP15CoefficientIterationSourceCircuit
  exact Circuit.flatten_sequence _

private theorem historyP15CoefficientLoopComponents_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr)
    (indices : List (Fin parameters.taylorOrder)) :
    (Circuit.sequence (indices.map (fun index =>
      (historyP15CoefficientIterationComponent layout (angles index) index).circuit))).flatten =
      (Circuit.sequence (indices.flatMap (fun index =>
        historyP15CoefficientIterationSourceStages layout (angles index) index))).flatten := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp only [Circuit.flatten_sequence] at inductionHypothesis ⊢
      simp only [List.map_cons, List.flatMap_cons, List.flatMap_append]
      rw [historyP15CoefficientIterationComponent_flatten_eq_sourceStages,
        inductionHypothesis]

/-- The actual loop component and the literal `finRange.flatMap` source list
have identical primitive-gate streams. -/
theorem historyP15CoefficientLoopComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    (historyP15CoefficientLoopComponent layout angles).circuit.flatten =
      (historyP15CoefficientLoopSourceCircuit layout angles).flatten := by
  rw [historyP15CoefficientLoopComponent_circuit]
  unfold historyP15CoefficientLoopComponents
    historyP15CoefficientLoopSourceCircuit
  simp only [List.map_map]
  exact historyP15CoefficientLoopComponents_flatten_eq_source layout angles
    (List.finRange parameters.taylorOrder)

/-! ### Order-boundary signal: clean comparison, use, and restoration

The frozen seven-stage word first materializes `order < taylorOrder` in the
equality flag, complements that flag, computes the branch/time conjunction,
uses the two flags as a Toffoli control, and then reverses the three computes.
The output signal is deliberately not required to be zero: this group is an
XOR action on an already-live post-generator signal. -/

private theorem historyP15OrderBoundaryBound_wire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    (historyOrderBoundRegister layout).wire index ∈
      historyRegisterWires layout.workspace := by
  unfold historyOrderBoundRegister
  apply historyWorkspaceSlice_wire_mem

private theorem historyP15OrderBoundaryMask_wire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    (historyOrderMaskedConstantRegister layout).wire index ∈
      historyRegisterWires layout.workspace := by
  unfold historyOrderMaskedConstantRegister
  apply historyWorkspaceSlice_wire_mem

private theorem historyP15OrderBoundaryMask_ne_bound
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (boundIndex maskIndex : Fin (historyOrderWidth parameters.taylorOrder)) :
    (historyOrderBoundRegister layout).wire boundIndex ≠
      (historyOrderMaskedConstantRegister layout).wire maskIndex := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have orderLeMaximum : historyOrderWidth parameters.taylorOrder ≤
      historyMaximumLabelWidth parameters := by
    unfold historyMaximumLabelWidth
    exact Nat.le_max_right _ _
  omega

private theorem historyP15EqualityFlag_ne_orderBoundaryBound
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    historyEqualityFlag layout ≠ (historyOrderBoundRegister layout).wire index := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

private theorem historyP15EqualityFlag_ne_orderBoundaryMask
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    historyEqualityFlag layout ≠
      (historyOrderMaskedConstantRegister layout).wire index := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

private theorem historyP15OrderBoundaryLessThanEvidence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    HistoryP15LessThanEvidence layout.order (historyOrderBoundRegister layout)
      (historyOrderMaskedConstantRegister layout) (historyEqualityFlag layout) := by
  refine {
    widthPositive := ?_
    lhsRhsDifferent := ?_
    lhsBorrowDifferent := ?_
    rhsBorrowDifferent := ?_
    targetLhsDifferent := ?_
    targetRhsDifferent := ?_
    targetBorrowDifferent := ?_ }
  · unfold historyOrderWidth
    omega
  · intro left right equal
    have workspaceMember :=
      historyP15OrderBoundaryBound_wire_mem_workspace layout right
    rcases List.mem_ofFn.mp workspaceMember with ⟨workspaceIndex, workspaceEqual⟩
    exact (layout.orderWire_separated left).2.2.2 workspaceIndex
      (equal.trans workspaceEqual.symm)
  · intro left right equal
    have workspaceMember :=
      historyP15OrderBoundaryMask_wire_mem_workspace layout right
    rcases List.mem_ofFn.mp workspaceMember with ⟨workspaceIndex, workspaceEqual⟩
    exact (layout.orderWire_separated left).2.2.2 workspaceIndex
      (equal.trans workspaceEqual.symm)
  · intro left right
    exact historyP15OrderBoundaryMask_ne_bound layout left right
  · intro index equal
    exact historyP15OrderWire_ne_equalityFlag layout index equal.symm
  · intro index
    exact historyP15EqualityFlag_ne_orderBoundaryBound layout index
  · intro index
    exact historyP15EqualityFlag_ne_orderBoundaryMask layout index

private noncomputable def historyP15OrderBoundaryLessThanSpec
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    UnsignedLessThanXorSpec qubits (historyOrderWidth parameters.taylorOrder) :=
  (historyP15OrderBoundaryLessThanEvidence layout).toSpec

/-- Clean entrance and exit sector of the source-faithful order-boundary
word.  The output signal itself is intentionally unrestricted. -/
def historyP15OrderBoundaryCleanPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyEqualityFlag layout) = false ∧
    historyLessThanConstantCleanInputPredicate
      (historyP15OrderBoundaryLessThanSpec layout) basis ∧
    basis (historyActiveWire layout) = false

private def historyP15OrderBoundaryLessComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyEqualityFlag layout) =
      historyTaylorOrderLessThanTaylorOrderValue layout basis ∧
    historyLessThanConstantCleanInputPredicate
      (historyP15OrderBoundaryLessThanSpec layout) basis ∧
    basis (historyActiveWire layout) = false

private def historyP15OrderBoundaryComplementedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyEqualityFlag layout) =
      !historyTaylorOrderLessThanTaylorOrderValue layout basis ∧
    historyLessThanConstantCleanInputPredicate
      (historyP15OrderBoundaryLessThanSpec layout) basis ∧
    basis (historyActiveWire layout) = false

private def historyP15OrderBoundaryActiveComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyEqualityFlag layout) =
      !historyTaylorOrderLessThanTaylorOrderValue layout basis ∧
    historyLessThanConstantCleanInputPredicate
      (historyP15OrderBoundaryLessThanSpec layout) basis ∧
    basis (historyActiveWire layout) =
      (basis (historyBranchWire layout) && basis (historyLessThanTimeWire layout))

private theorem historyP15OrderBoundaryBound_not_mem_live
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    (historyOrderBoundRegister layout).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyOrderBoundRegister
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  have structuralFits := Nat.le_max_right generatorWorkWidth
    (historyStructuralPoolWidth parameters)
  unfold historySharedPoolWidth
  unfold historyStructuralPoolWidth at structuralFits ⊢
  unfold historyMaximumLabelWidth
  omega

private theorem historyP15OrderBoundaryMask_not_mem_live
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    (historyOrderMaskedConstantRegister layout).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyOrderMaskedConstantRegister
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  have structuralFits := Nat.le_max_right generatorWorkWidth
    (historyStructuralPoolWidth parameters)
  unfold historySharedPoolWidth
  unfold historyStructuralPoolWidth at structuralFits ⊢
  unfold historyMaximumLabelWidth
  omega

private theorem historyP15Active_ne_orderBoundaryBound
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    historyActiveWire layout ≠ (historyOrderBoundRegister layout).wire index := by
  intro equal
  apply historyP15OrderBoundaryBound_not_mem_live layout index
  simp [historyTaylorBeforeGeneratorLiveWires, equal]

private theorem historyP15Active_ne_orderBoundaryMask
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    historyActiveWire layout ≠
      (historyOrderMaskedConstantRegister layout).wire index := by
  intro equal
  apply historyP15OrderBoundaryMask_not_mem_live layout index
  simp [historyTaylorBeforeGeneratorLiveWires, equal]

private theorem historyP15OrderBoundaryWorkspaceWire_ne_signal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (wire : Fin qubits)
    (member : wire ∈ historyRegisterWires layout.workspace) :
    wire ≠ layout.orderBoundarySignal := by
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨workspaceIndex, rfl⟩
  exact (layout.postGeneratorSignal_separated layout.orderBoundarySignal
    (by simp)).2.2 workspaceIndex

private theorem historyP15Active_ne_orderBoundarySignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyActiveWire layout ≠ layout.orderBoundarySignal :=
  historyP15OrderBoundaryWorkspaceWire_ne_signal layout (historyActiveWire layout)
    (historyActiveWire_mem_workspace layout)

private theorem historyP15Branch_ne_equalityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyBranchWire layout ≠ historyEqualityFlag layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast : 5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
    calc
      5 ≤ historyStructuralPoolWidth parameters := by
        unfold historyStructuralPoolWidth
        omega
      _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
        Nat.le_max_right _ _
  omega

private theorem historyP15LessThanTime_ne_equalityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyLessThanTimeWire layout ≠ historyEqualityFlag layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast : 5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
    calc
      5 ≤ historyStructuralPoolWidth parameters := by
        unfold historyStructuralPoolWidth
        omega
      _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
        Nat.le_max_right _ _
  omega

private theorem historyP15LessThanIdleEnd_ne_equalityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyLessThanIdleEndWire layout ≠ historyEqualityFlag layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast : 5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
    calc
      5 ≤ historyStructuralPoolWidth parameters := by
        unfold historyStructuralPoolWidth
        omega
      _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
        Nat.le_max_right _ _
  omega

/-- The placed Q10 work-clean boundary restores every physical generator-work
wire, including the prefix which aliases the P15 structural workspace. -/
private theorem historyP15OrderBoundaryGeneratorWorkClean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10OutputPredicate (layout := layout) widths input)
    (index : Fin generatorWorkWidth) :
    input ((historyGeneratorWorkRegister layout).wire index) = false := by
  rcases widths with ⟨rfl, rfl, rfl⟩
  unfold historyP15PostQ10OutputPredicate
    externallyControlledPlacedOutputPredicate at inside
  have coreClean := inside.2
  unfold ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate
    ProbabilityGeneratorQProof.q10GeneratorWorkCleanPredicate at coreClean
  have workMember :
      (ProbabilityGeneratorQProof.QLayout.canonical p).oracleWork.ancillaWire index ∈
        ProbabilityGeneratorQProof.q10RegisterSliceWires
          (systemWidth := p.systemWidth)
          (ProbabilityGeneratorQProof.QLayout.canonical p).oracleWork := by
    unfold ProbabilityGeneratorQProof.q10RegisterSliceWires
    exact List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  have zero := coreClean _ workMember
  change restrictToPlacedWires
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := layout)
        (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical p)).placement.embedding.placement
      input
      (ProbabilityGeneratorQProof.wireToCanonicalFin
        ((ProbabilityGeneratorQProof.QLayout.canonical p).oracleWork.ancillaWire index)) = false at zero
  unfold restrictToPlacedWires at zero
  have canonicalIndex :
      ProbabilityGeneratorQProof.wireToCanonicalFin
        (systemQubits := p.systemWidth)
        ((ProbabilityGeneratorQProof.QLayout.canonical p).oracleWork.ancillaWire
          (systemWidth := p.systemWidth) index) =
        (⟨p.generatorSignalWidth + index.val, by
          have partition := p.generatorSignalWidth_add_generatorWorkWidth_eq_ancillaWidth
          omega⟩ : Fin (p.ancillaWidth + p.systemWidth)) := by
    apply Fin.ext
    rfl
  let source : Fin (p.ancillaWidth + p.systemWidth) :=
    ⟨p.generatorSignalWidth + index.val, by
      have partition := p.generatorSignalWidth_add_generatorWorkWidth_eq_ancillaWidth
      omega⟩
  have sourceOrder := historyP15Q10Placement_sourceOrder
    (layout := layout)
    (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical p)
  have sourceBound : source.val < (List.ofFn
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := layout)
        (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical p)).placement.embedding.placement).length := by
    simp only [List.length_ofFn]
    dsimp [source]
    have partition := p.generatorSignalWidth_add_generatorWorkWidth_eq_ancillaWidth
    omega
  have placementAt : (List.ofFn
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := layout)
        (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical p)).placement.embedding.placement)[source.val] =
      (historyGeneratorWorkRegister layout).wire index := by
    simp [sourceOrder, source, historyRegisterWires]
  have placement :
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := layout)
        (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical p)).placement.embedding.placement source =
      (historyGeneratorWorkRegister layout).wire index := by
    calc
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := layout)
        (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical p)).placement.embedding.placement source =
          (List.ofFn
            (historyP15Q10ControlEvidence_ofFrozenLayout
              (layout := layout)
              (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical p)).placement.embedding.placement)[source.val] := by
            symm
            simp [source]
      _ = (historyGeneratorWorkRegister layout).wire index := placementAt
  rw [canonicalIndex, placement] at zero
  exact zero

/-- The post-Q10 stable boundary supplies zero on any workspace wire which
is not one of the three live clock flags.  Q10-owned aliases are discharged
through its already-restored work-clean contract. -/
private theorem historyP15OrderBoundaryStableWorkspaceZero
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input)
    (workspaceIndex : Fin (historyClockWorkspaceWidth parameters generatorWorkWidth))
    (outsideFlags : layout.workspace.wire workspaceIndex ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout]) :
    input (layout.workspace.wire workspaceIndex) = false := by
  by_cases generatorMember : layout.workspace.wire workspaceIndex ∈
      historyRegisterWires (historyGeneratorWorkRegister layout)
  · rcases List.mem_ofFn.mp generatorMember with ⟨index, equal⟩
    rw [← equal]
    exact historyP15OrderBoundaryGeneratorWorkClean layout widths input inside.1 index
  by_cases controlledMember : layout.workspace.wire workspaceIndex ∈
      historyRegisterWires (historyControlledWork layout)
  · rcases List.mem_ofFn.mp controlledMember with ⟨index, equal⟩
    rw [← equal]
    have output := inside.1
    unfold historyP15PostQ10OutputPredicate
      externallyControlledPlacedOutputPredicate at output
    fin_cases index
    · exact output.1.1
    · exact output.1.2
  · exact inside.2.2.2.2 workspaceIndex (by
      have outsideBase :
          ¬ layout.workspace.wire workspaceIndex = historyBranchWire layout ∧
            ¬ layout.workspace.wire workspaceIndex = historyLessThanTimeWire layout ∧
              ¬ layout.workspace.wire workspaceIndex =
                historyLessThanIdleEndWire layout := by
        constructor
        · intro equal
          apply outsideFlags
          simp [equal]
        constructor
        · intro equal
          apply outsideFlags
          simp [equal]
        · intro equal
          apply outsideFlags
          simp [equal]
      simpa [historyTaylorControlledQ10OwnedWorkspaceWires,
        generatorMember, controlledMember] using outsideBase)

private theorem historyP15OrderBoundaryEqualityFlag_not_mem_stableFlags
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyEqualityFlag layout ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] := by
  intro member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal
  · exact (historyP15Branch_ne_equalityFlag layout) equal.symm
  · exact (historyP15LessThanTime_ne_equalityFlag layout) equal.symm
  · exact (historyP15LessThanIdleEnd_ne_equalityFlag layout) equal.symm

private theorem historyP15OrderBoundaryActive_not_mem_stableFlags
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyActiveWire layout ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] := by
  intro member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal
  · exact (historyBranchWire_ne_activeWire layout) equal.symm
  · exact (historyLessThanTimeWire_ne_activeWire layout) equal.symm
  · exact (historyLessThanIdleEndWire_ne_activeWire layout) equal.symm

private theorem historyP15OrderBoundaryBound_not_mem_stableFlags
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    (historyOrderBoundRegister layout).wire index ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] := by
  intro member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  apply historyP15OrderBoundaryBound_not_mem_live layout index
  simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
    List.not_mem_nil, or_false]
  rcases member with equal | equal | equal
  · exact Or.inl equal
  · exact Or.inr (Or.inl equal)
  · exact Or.inr (Or.inr (Or.inl equal))

private theorem historyP15OrderBoundaryMask_not_mem_stableFlags
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    (historyOrderMaskedConstantRegister layout).wire index ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] := by
  intro member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  apply historyP15OrderBoundaryMask_not_mem_live layout index
  simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
    List.not_mem_nil, or_false]
  rcases member with equal | equal | equal
  · exact Or.inl equal
  · exact Or.inr (Or.inl equal)
  · exact Or.inr (Or.inr (Or.inl equal))

/-- The coherent post-Q10 boundary contains all clean premises used by the
order-boundary comparator and its temporary flags. -/
theorem historyP15PostQ10StablePredicate_implies_orderBoundaryClean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    historyP15OrderBoundaryCleanPredicate layout input := by
  unfold historyP15OrderBoundaryCleanPredicate
  refine ⟨?_, ?_, ?_⟩
  · rcases List.mem_ofFn.mp (historyP15EqualityFlag_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    rw [← equal]
    have outside : layout.workspace.wire workspaceIndex ∉
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout] := by
      simpa [equal] using
        historyP15OrderBoundaryEqualityFlag_not_mem_stableFlags layout
    exact historyP15OrderBoundaryStableWorkspaceZero layout widths input inside
      workspaceIndex outside
  · unfold historyLessThanConstantCleanInputPredicate
    constructor
    · intro index
      rcases List.mem_ofFn.mp
          (historyP15OrderBoundaryMask_wire_mem_workspace layout index) with
        ⟨workspaceIndex, equal⟩
      have outside : layout.workspace.wire workspaceIndex ∉
          [historyBranchWire layout, historyLessThanTimeWire layout,
            historyLessThanIdleEndWire layout] := by
        simpa [equal] using
          historyP15OrderBoundaryMask_not_mem_stableFlags layout index
      have zero := historyP15OrderBoundaryStableWorkspaceZero layout widths input
        inside workspaceIndex outside
      simpa [historyP15OrderBoundaryLessThanSpec,
        HistoryP15LessThanEvidence.toSpec, Register.read, equal] using zero
    · intro index
      rcases List.mem_ofFn.mp
          (historyP15OrderBoundaryBound_wire_mem_workspace layout index) with
        ⟨workspaceIndex, equal⟩
      have outside : layout.workspace.wire workspaceIndex ∉
          [historyBranchWire layout, historyLessThanTimeWire layout,
            historyLessThanIdleEndWire layout] := by
        simpa [equal] using
          historyP15OrderBoundaryBound_not_mem_stableFlags layout index
      have zero := historyP15OrderBoundaryStableWorkspaceZero layout widths input
        inside workspaceIndex outside
      simpa [historyP15OrderBoundaryLessThanSpec,
        HistoryP15LessThanEvidence.toSpec, Register.read, equal] using zero
  · rcases List.mem_ofFn.mp (historyActiveWire_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    rw [← equal]
    have outside : layout.workspace.wire workspaceIndex ∉
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout] := by
      simpa [equal] using
        historyP15OrderBoundaryActive_not_mem_stableFlags layout
    exact historyP15OrderBoundaryStableWorkspaceZero layout widths input inside
      workspaceIndex outside

private theorem historyP15EqualityFlag_ne_orderBoundarySignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyEqualityFlag layout ≠ layout.orderBoundarySignal :=
  historyP15OrderBoundaryWorkspaceWire_ne_signal layout (historyEqualityFlag layout)
    (historyP15EqualityFlag_mem_workspace layout)

private theorem historyP15OrderBoundaryOrderLess_invariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (excluded : Fin qubits)
    (excluded_ne_order : ∀ index, excluded ≠ layout.order.wire index)
    (first second : QubitBasis qubits)
    (same : agreesExcept excluded first second) :
    historyTaylorOrderLessThanTaylorOrderValue layout first =
      historyTaylorOrderLessThanTaylorOrderValue layout second := by
  unfold historyTaylorOrderLessThanTaylorOrderValue
  apply congrArg (fun bits => unsignedLessThanBits bits
    (fun index => parameters.taylorOrder.testBit index.val))
  funext index
  exact same (layout.order.wire index) (excluded_ne_order index).symm

private theorem historyP15OrderBoundaryOrderLess_equalityFlagInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyEqualityFlag layout) first second) :
    historyTaylorOrderLessThanTaylorOrderValue layout first =
      historyTaylorOrderLessThanTaylorOrderValue layout second :=
  historyP15OrderBoundaryOrderLess_invariant layout (historyEqualityFlag layout)
    (fun index => (historyP15OrderWire_ne_equalityFlag layout index).symm)
    first second same

private theorem historyP15OrderBoundaryOrderLess_activeInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyActiveWire layout) first second) :
    historyTaylorOrderLessThanTaylorOrderValue layout first =
      historyTaylorOrderLessThanTaylorOrderValue layout second := by
  apply historyP15OrderBoundaryOrderLess_invariant layout (historyActiveWire layout)
  · intro index
    have member := historyActiveWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, workspaceEqual⟩
    intro equal
    exact (layout.orderWire_separated index).2.2.2 workspaceIndex
      (equal.symm.trans workspaceEqual.symm)
  · exact same

private theorem historyP15OrderBoundaryOrderLess_signalInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept layout.orderBoundarySignal first second) :
    historyTaylorOrderLessThanTaylorOrderValue layout first =
      historyTaylorOrderLessThanTaylorOrderValue layout second :=
  historyP15OrderBoundaryOrderLess_invariant layout layout.orderBoundarySignal
    (fun index => ((layout.orderWire_separated index).2.2.1
      layout.orderBoundarySignal (by simp)).symm)
    first second same

private theorem historyP15OrderBoundaryLessDirectAction_eq
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    historyLessThanConstantDirectBasisAction
        (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder input =
      xorWire (historyEqualityFlag layout)
        (historyTaylorOrderLessThanTaylorOrderValue layout input) input := rfl

private noncomputable def historyP15OrderBoundaryInstructionComponent
    {qubits : Nat} (instruction : ClassicalReversibleInstruction qubits)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (directMaps : ∀ input, inputPredicate input →
      outputPredicate (instruction.basisAction input)) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let exact := ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.instruction instruction)
  exact.toSubspaceMapOfBasisAgreementBetween
    (deterministicOperator instruction.basisAction)
    inputPredicate outputPredicate
    (by
      intro input _inside
      rw [ClassicalReversibleStage.primitiveExactOperatorComponent_target,
        ClassicalReversibleStage.analyticOperator_eq_deterministicReference]
      rfl)
    (by
      intro input inside
      rw [applyOperator_deterministicOperator_basisKet]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      exact directMaps input inside)

private noncomputable def historyP15OrderBoundaryDegreeLessComputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15LessThanConstantCleanStageBetween
    (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder
    (historyP15OrderBoundaryCleanPredicate layout)
    (historyP15OrderBoundaryLessComputedPredicate layout)
    (by
      intro input inside
      exact inside.2.1)
    (by
      intro input inside
      unfold historyP15OrderBoundaryCleanPredicate at inside
      unfold historyP15OrderBoundaryLessComputedPredicate
      rw [historyP15OrderBoundaryLessDirectAction_eq]
      refine ⟨?_, ?_, ?_⟩
      · have orderStable :=
          historyP15OrderBoundaryOrderLess_equalityFlagInvariant layout
            (xorWire (historyEqualityFlag layout)
              (historyTaylorOrderLessThanTaylorOrderValue layout input) input)
            input (by
              intro wire different
              exact xorWire_apply_other (historyEqualityFlag layout) wire
                different _ input)
        rw [xorWire_apply_same, inside.1, orderStable]
        cases historyTaylorOrderLessThanTaylorOrderValue layout input <;> rfl
      · exact historyP15LessThanConstantDirectBasisAction_cleanOutput
          (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder
          input inside.2.1
      · rw [xorWire_apply_other (historyEqualityFlag layout)
          (historyActiveWire layout)
          (historyP15Active_ne_equalityFlag layout)]
        exact inside.2.2)

private theorem historyP15OrderBoundaryDegreeLessComputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryDegreeLessComputeComponent layout).target =
      historyLessThanConstantDirectOperator
        (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder := rfl

private theorem historyP15OrderBoundaryComparatorClean_xorEqualityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Bool) (input : QubitBasis qubits)
    (clean : historyLessThanConstantCleanInputPredicate
      (historyP15OrderBoundaryLessThanSpec layout) input) :
    historyLessThanConstantCleanInputPredicate
      (historyP15OrderBoundaryLessThanSpec layout)
      (xorWire (historyEqualityFlag layout) value input) := by
  unfold historyLessThanConstantCleanInputPredicate at clean ⊢
  constructor
  · intro index
    change xorWire (historyEqualityFlag layout) value input
      ((historyOrderMaskedConstantRegister layout).wire index) = false
    rw [xorWire_apply_other (historyEqualityFlag layout)
      ((historyOrderMaskedConstantRegister layout).wire index)
      (historyP15EqualityFlag_ne_orderBoundaryMask layout index).symm]
    exact clean.1 index
  · intro index
    change xorWire (historyEqualityFlag layout) value input
      ((historyOrderBoundRegister layout).wire index) = false
    rw [xorWire_apply_other (historyEqualityFlag layout)
      ((historyOrderBoundRegister layout).wire index)
      (historyP15EqualityFlag_ne_orderBoundaryBound layout index).symm]
    exact clean.2 index

private noncomputable def historyP15OrderBoundaryEqualityXComputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15OrderBoundaryInstructionComponent
    (.xorOne (historyEqualityFlag layout))
    (historyP15OrderBoundaryLessComputedPredicate layout)
    (historyP15OrderBoundaryComplementedPredicate layout)
    (by
      intro input inside
      unfold historyP15OrderBoundaryLessComputedPredicate at inside
      unfold historyP15OrderBoundaryComplementedPredicate
      have orderStable :=
        historyP15OrderBoundaryOrderLess_equalityFlagInvariant layout
          (xorWire (historyEqualityFlag layout) true input) input (by
            intro wire different
            exact xorWire_apply_other (historyEqualityFlag layout) wire
              different _ input)
      refine ⟨?_, ?_, ?_⟩
      · change xorWire (historyEqualityFlag layout) true input
          (historyEqualityFlag layout) =
            !historyTaylorOrderLessThanTaylorOrderValue layout
              (xorWire (historyEqualityFlag layout) true input)
        rw [xorWire_apply_same, inside.1, orderStable]
        cases historyTaylorOrderLessThanTaylorOrderValue layout input <;> rfl
      · simpa [ClassicalReversibleInstruction.basisAction] using
          historyP15OrderBoundaryComparatorClean_xorEqualityFlag layout true
            input inside.2.1
      · change xorWire (historyEqualityFlag layout) true input
          (historyActiveWire layout) = false
        rw [xorWire_apply_other (historyEqualityFlag layout)
          (historyActiveWire layout) (historyP15Active_ne_equalityFlag layout)]
        exact inside.2.2)

private theorem historyP15OrderBoundaryEqualityXComputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryEqualityXComputeComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorOne (historyEqualityFlag layout)).basisAction := rfl

private noncomputable def historyP15OrderBoundaryEqualityXUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15OrderBoundaryInstructionComponent
    (.xorOne (historyEqualityFlag layout))
    (historyP15OrderBoundaryComplementedPredicate layout)
    (historyP15OrderBoundaryLessComputedPredicate layout)
    (by
      intro input inside
      unfold historyP15OrderBoundaryComplementedPredicate at inside
      unfold historyP15OrderBoundaryLessComputedPredicate
      have orderStable :=
        historyP15OrderBoundaryOrderLess_equalityFlagInvariant layout
          (xorWire (historyEqualityFlag layout) true input) input (by
            intro wire different
            exact xorWire_apply_other (historyEqualityFlag layout) wire
              different _ input)
      refine ⟨?_, ?_, ?_⟩
      · change xorWire (historyEqualityFlag layout) true input
          (historyEqualityFlag layout) =
            historyTaylorOrderLessThanTaylorOrderValue layout
              (xorWire (historyEqualityFlag layout) true input)
        rw [xorWire_apply_same, inside.1, orderStable]
        cases historyTaylorOrderLessThanTaylorOrderValue layout input <;> rfl
      · simpa [ClassicalReversibleInstruction.basisAction] using
          historyP15OrderBoundaryComparatorClean_xorEqualityFlag layout true
            input inside.2.1
      · change xorWire (historyEqualityFlag layout) true input
          (historyActiveWire layout) = false
        rw [xorWire_apply_other (historyEqualityFlag layout)
          (historyActiveWire layout) (historyP15Active_ne_equalityFlag layout)]
        exact inside.2.2)

private theorem historyP15OrderBoundaryEqualityXUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryEqualityXUncomputeComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorOne (historyEqualityFlag layout)).basisAction := rfl

private theorem historyP15OrderBoundaryComparatorClean_activeInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (clean : historyLessThanConstantCleanInputPredicate
      (historyP15OrderBoundaryLessThanSpec layout) input) :
    historyLessThanConstantCleanInputPredicate
      (historyP15OrderBoundaryLessThanSpec layout)
      (ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyActiveWire layout) input) := by
  unfold historyLessThanConstantCleanInputPredicate at clean ⊢
  constructor
  · intro index
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) input
      ((historyOrderMaskedConstantRegister layout).wire index) = false
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout)
      ((historyOrderMaskedConstantRegister layout).wire index)
      (historyP15Active_ne_orderBoundaryMask layout index).symm]
    exact clean.1 index
  · intro index
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) input
      ((historyOrderBoundRegister layout).wire index) = false
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout)
      ((historyOrderBoundRegister layout).wire index)
      (historyP15Active_ne_orderBoundaryBound layout index).symm]
    exact clean.2 index

private theorem historyP15OrderBoundaryConjunctionCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    ClassicalReversibleStage.allWiresTrue
      [historyBranchWire layout, historyLessThanTimeWire layout] input =
        (input (historyBranchWire layout) && input (historyLessThanTimeWire layout)) := by
  simp [ClassicalReversibleStage.allWiresTrue,
    ClassicalReversibleStage.readWires]

private noncomputable def historyP15OrderBoundaryActiveComputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyBranchWire layout, historyLessThanTimeWire layout] []
    (historyActiveWire layout) (by simp)
    (historyTaylorActiveConjunctionLayout_nodup layout)
    (historyP15OrderBoundaryComplementedPredicate layout)
    (historyP15OrderBoundaryActiveComputedPredicate layout)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input inside
      unfold historyP15OrderBoundaryComplementedPredicate at inside
      unfold historyP15OrderBoundaryActiveComputedPredicate
      let action := ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyActiveWire layout)
      have actionAgrees : agreesExcept (historyActiveWire layout)
          (action input) input := by
        intro wire different
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyLessThanTimeWire layout]
          (historyActiveWire layout) wire different input
      have orderStable := historyP15OrderBoundaryOrderLess_activeInvariant layout
        (action input) input actionAgrees
      refine ⟨?_, ?_, ?_⟩
      · rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyLessThanTimeWire layout]
          (historyActiveWire layout) (historyEqualityFlag layout)
          (historyP15Active_ne_equalityFlag layout).symm]
        rw [inside.1, orderStable]
      · exact historyP15OrderBoundaryComparatorClean_activeInvariant layout input
          inside.2.1
      · change action input (historyActiveWire layout) =
          (action input (historyBranchWire layout) &&
            action input (historyLessThanTimeWire layout))
        have conditionStable :
            (action input (historyBranchWire layout) &&
              action input (historyLessThanTimeWire layout)) =
              (input (historyBranchWire layout) &&
                input (historyLessThanTimeWire layout)) := by
          dsimp [action]
          rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
            [historyBranchWire layout, historyLessThanTimeWire layout]
            (historyActiveWire layout) (historyBranchWire layout)
            (historyBranchWire_ne_activeWire layout),
            ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
            [historyBranchWire layout, historyLessThanTimeWire layout]
            (historyActiveWire layout) (historyLessThanTimeWire layout)
            (historyLessThanTimeWire_ne_activeWire layout)]
        rw [show action input (historyActiveWire layout) =
            (input (historyActiveWire layout) !=
              ClassicalReversibleStage.allWiresTrue
                [historyBranchWire layout, historyLessThanTimeWire layout] input) by
              exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target
                _ _ _, historyP15OrderBoundaryConjunctionCondition layout input,
          inside.2.2, conditionStable]
        cases input (historyBranchWire layout) <;>
          cases input (historyLessThanTimeWire layout) <;> rfl)

private theorem historyP15OrderBoundaryActiveComputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryActiveComputeComponent layout).target =
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyActiveWire layout) := rfl

private noncomputable def historyP15OrderBoundaryActiveUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyBranchWire layout, historyLessThanTimeWire layout] []
    (historyActiveWire layout) (by simp)
    (historyTaylorActiveConjunctionLayout_nodup layout)
    (historyP15OrderBoundaryActiveComputedPredicate layout)
    (historyP15OrderBoundaryComplementedPredicate layout)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input inside
      unfold historyP15OrderBoundaryActiveComputedPredicate at inside
      unfold historyP15OrderBoundaryComplementedPredicate
      let action := ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyActiveWire layout)
      have actionAgrees : agreesExcept (historyActiveWire layout)
          (action input) input := by
        intro wire different
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyLessThanTimeWire layout]
          (historyActiveWire layout) wire different input
      have orderStable := historyP15OrderBoundaryOrderLess_activeInvariant layout
        (action input) input actionAgrees
      refine ⟨?_, ?_, ?_⟩
      · rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyLessThanTimeWire layout]
          (historyActiveWire layout) (historyEqualityFlag layout)
          (historyP15Active_ne_equalityFlag layout).symm]
        rw [inside.1, orderStable]
      · exact historyP15OrderBoundaryComparatorClean_activeInvariant layout input
          inside.2.1
      · change action input (historyActiveWire layout) = false
        rw [show action input (historyActiveWire layout) =
            (input (historyActiveWire layout) !=
              ClassicalReversibleStage.allWiresTrue
                [historyBranchWire layout, historyLessThanTimeWire layout] input) by
              exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target
                _ _ _, historyP15OrderBoundaryConjunctionCondition layout input,
          inside.2.2]
        cases input (historyBranchWire layout) <;>
          cases input (historyLessThanTimeWire layout) <;> rfl)

private theorem historyP15OrderBoundaryActiveUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryActiveUncomputeComponent layout).target =
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyActiveWire layout) := rfl

private theorem historyP15OrderBoundaryComparatorClean_xorSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Bool) (input : QubitBasis qubits)
    (clean : historyLessThanConstantCleanInputPredicate
      (historyP15OrderBoundaryLessThanSpec layout) input) :
    historyLessThanConstantCleanInputPredicate
      (historyP15OrderBoundaryLessThanSpec layout)
      (xorWire layout.orderBoundarySignal value input) := by
  unfold historyLessThanConstantCleanInputPredicate at clean ⊢
  constructor
  · intro index
    change xorWire layout.orderBoundarySignal value input
      ((historyOrderMaskedConstantRegister layout).wire index) = false
    rw [xorWire_apply_other layout.orderBoundarySignal
      ((historyOrderMaskedConstantRegister layout).wire index)
      (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
        (historyP15OrderBoundaryMask_wire_mem_workspace layout index))]
    exact clean.1 index
  · intro index
    change xorWire layout.orderBoundarySignal value input
      ((historyOrderBoundRegister layout).wire index) = false
    rw [xorWire_apply_other layout.orderBoundarySignal
      ((historyOrderBoundRegister layout).wire index)
      (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
        (historyP15OrderBoundaryBound_wire_mem_workspace layout index))]
    exact clean.2 index

private noncomputable def historyP15OrderBoundaryToffoliComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15OrderBoundaryInstructionComponent
    (.xorDoublyControlled (historyActiveWire layout) (historyEqualityFlag layout)
      layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
      (historyP15Active_ne_orderBoundarySignal layout)
      (historyP15EqualityFlag_ne_orderBoundarySignal layout))
    (historyP15OrderBoundaryActiveComputedPredicate layout)
    (historyP15OrderBoundaryActiveComputedPredicate layout)
    (by
      intro input inside
      unfold historyP15OrderBoundaryActiveComputedPredicate at inside ⊢
      let action :=
        (ClassicalReversibleInstruction.xorDoublyControlled
          (historyActiveWire layout) (historyEqualityFlag layout)
          layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
          (historyP15Active_ne_orderBoundarySignal layout)
          (historyP15EqualityFlag_ne_orderBoundarySignal layout)).basisAction
      have actionAgrees : agreesExcept layout.orderBoundarySignal
          (action input) input := by
        intro wire different
        dsimp [action, ClassicalReversibleInstruction.basisAction]
        exact xorWire_apply_other layout.orderBoundarySignal wire different _ input
      have orderStable := historyP15OrderBoundaryOrderLess_signalInvariant layout
        (action input) input actionAgrees
      refine ⟨?_, ?_, ?_⟩
      · change action input (historyEqualityFlag layout) =
          !historyTaylorOrderLessThanTaylorOrderValue layout (action input)
        rw [show action input (historyEqualityFlag layout) =
            input (historyEqualityFlag layout) by
              dsimp [action, ClassicalReversibleInstruction.basisAction]
              exact xorWire_apply_other layout.orderBoundarySignal
                (historyEqualityFlag layout)
                (historyP15EqualityFlag_ne_orderBoundarySignal layout) _ input,
          inside.1, orderStable]
      · simpa [action, ClassicalReversibleInstruction.basisAction] using
          historyP15OrderBoundaryComparatorClean_xorSignal layout
            (input (historyActiveWire layout) && input (historyEqualityFlag layout))
            input inside.2.1
      · change action input (historyActiveWire layout) =
          (action input (historyBranchWire layout) &&
            action input (historyLessThanTimeWire layout))
        rw [show action input (historyActiveWire layout) =
            input (historyActiveWire layout) by
              dsimp [action, ClassicalReversibleInstruction.basisAction]
              exact xorWire_apply_other layout.orderBoundarySignal
                (historyActiveWire layout)
                (historyP15Active_ne_orderBoundarySignal layout) _ input,
          show action input (historyBranchWire layout) =
            input (historyBranchWire layout) by
              dsimp [action, ClassicalReversibleInstruction.basisAction]
              exact xorWire_apply_other layout.orderBoundarySignal
                (historyBranchWire layout)
                (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
                  (historyBranchWire_mem_workspace layout)) _ input,
          show action input (historyLessThanTimeWire layout) =
            input (historyLessThanTimeWire layout) by
              dsimp [action, ClassicalReversibleInstruction.basisAction]
              exact xorWire_apply_other layout.orderBoundarySignal
                (historyLessThanTimeWire layout)
                (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
                  (historyLessThanTimeWire_mem_workspace layout)) _ input]
        exact inside.2.2)

private theorem historyP15OrderBoundaryToffoliComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryToffoliComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorDoublyControlled
          (historyActiveWire layout) (historyEqualityFlag layout)
          layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
          (historyP15Active_ne_orderBoundarySignal layout)
          (historyP15EqualityFlag_ne_orderBoundarySignal layout)).basisAction := rfl

private noncomputable def historyP15OrderBoundaryDegreeLessUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15LessThanConstantCleanStageBetween
    (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder
    (historyP15OrderBoundaryLessComputedPredicate layout)
    (historyP15OrderBoundaryCleanPredicate layout)
    (by
      intro input inside
      exact inside.2.1)
    (by
      intro input inside
      unfold historyP15OrderBoundaryLessComputedPredicate at inside
      unfold historyP15OrderBoundaryCleanPredicate
      rw [historyP15OrderBoundaryLessDirectAction_eq]
      refine ⟨?_, ?_, ?_⟩
      · rw [xorWire_apply_same, inside.1]
        cases historyTaylorOrderLessThanTaylorOrderValue layout input <;> rfl
      · exact historyP15LessThanConstantDirectBasisAction_cleanOutput
          (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder
          input inside.2.1
      · rw [xorWire_apply_other (historyEqualityFlag layout)
          (historyActiveWire layout) (historyP15Active_ne_equalityFlag layout)]
        exact inside.2.2)

private theorem historyP15OrderBoundaryDegreeLessUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryDegreeLessUncomputeComponent layout).target =
      historyLessThanConstantDirectOperator
        (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder := rfl

private theorem historyP15OrderBoundarySignalChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    SubspaceMapComponent.SpaceChain
      [historyP15OrderBoundaryDegreeLessComputeComponent layout,
       historyP15OrderBoundaryEqualityXComputeComponent layout,
       historyP15OrderBoundaryActiveComputeComponent layout,
       historyP15OrderBoundaryToffoliComponent layout,
       historyP15OrderBoundaryActiveUncomputeComponent layout,
       historyP15OrderBoundaryEqualityXUncomputeComponent layout,
       historyP15OrderBoundaryDegreeLessUncomputeComponent layout]
      (SubspaceMapComponent.basisSpan
        (historyP15OrderBoundaryCleanPredicate layout))
      (SubspaceMapComponent.basisSpan
        (historyP15OrderBoundaryCleanPredicate layout)) := by
  exact .cons _ [_, _, _, _, _, _] _ _ _ rfl rfl
    (.cons _ [_, _, _, _, _] _ _ _ rfl rfl
      (.cons _ [_, _, _, _] _ _ _ rfl rfl
        (.cons _ [_, _, _] _ _ _ rfl rfl
          (.cons _ [_, _] _ _ _ rfl rfl
            (.cons _ [_] _ _ _ rfl rfl
              (.cons _ [] _ _ _ rfl rfl (.nil _)))))))

private noncomputable def historyP15OrderBoundaryRawComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  SubspaceMapComponent.sequenceAlong (historyP15OrderBoundarySignalChain layout)

private theorem historyP15OrderBoundaryRawComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryRawComponent layout).target =
      operatorSequence
        [historyLessThanConstantDirectOperator
          (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder,
         deterministicOperator
           (ClassicalReversibleInstruction.xorOne (historyEqualityFlag layout)).basisAction,
         ClassicalReversibleStage.conjunctionDirectOperator
           [historyBranchWire layout, historyLessThanTimeWire layout]
           (historyActiveWire layout),
         deterministicOperator
           (ClassicalReversibleInstruction.xorDoublyControlled
             (historyActiveWire layout) (historyEqualityFlag layout)
             layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
             (historyP15Active_ne_orderBoundarySignal layout)
             (historyP15EqualityFlag_ne_orderBoundarySignal layout)).basisAction,
         ClassicalReversibleStage.conjunctionDirectOperator
           [historyBranchWire layout, historyLessThanTimeWire layout]
           (historyActiveWire layout),
         deterministicOperator
           (ClassicalReversibleInstruction.xorOne (historyEqualityFlag layout)).basisAction,
         historyLessThanConstantDirectOperator
           (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder] := by
  rw [show (historyP15OrderBoundaryRawComponent layout).target =
      (SubspaceMapComponent.sequenceAlong
        (historyP15OrderBoundarySignalChain layout)).target by rfl,
    SubspaceMapComponent.sequenceAlong_target]
  simp only [List.map_cons, List.map_nil]
  rw [historyP15OrderBoundaryDegreeLessComputeComponent_target,
    historyP15OrderBoundaryEqualityXComputeComponent_target,
    historyP15OrderBoundaryActiveComputeComponent_target,
    historyP15OrderBoundaryToffoliComponent_target,
    historyP15OrderBoundaryActiveUncomputeComponent_target,
    historyP15OrderBoundaryEqualityXUncomputeComponent_target,
    historyP15OrderBoundaryDegreeLessUncomputeComponent_target]

private def historyP15OrderBoundarySourceAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  let less := historyLessThanConstantDirectBasisAction
    (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder input
  let complemented := xorWire (historyEqualityFlag layout) true less
  let active := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyLessThanTimeWire layout]
    (historyActiveWire layout) complemented
  let used := xorWire layout.orderBoundarySignal
    (active (historyActiveWire layout) && active (historyEqualityFlag layout)) active
  let unactive := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyLessThanTimeWire layout]
    (historyActiveWire layout) used
  let uncomplemented := xorWire (historyEqualityFlag layout) true unactive
  historyLessThanConstantDirectBasisAction
    (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder
    uncomplemented

private theorem historyP15OrderBoundaryRawTarget_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    applyOperator (historyP15OrderBoundaryRawComponent layout).target
        (basisKet input) =
      basisKet (historyP15OrderBoundarySourceAction layout input) := by
  rw [historyP15OrderBoundaryRawComponent_target,
    historyLessThanConstantDirectOperator,
    ClassicalReversibleStage.conjunctionDirectOperator]
  change applyOperator
      (operatorSequence
        ([historyLessThanConstantDirectBasisAction
            (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder,
          (ClassicalReversibleInstruction.xorOne
            (historyEqualityFlag layout)).basisAction,
          ClassicalReversibleStage.conjunctionDirectBasisAction
            [historyBranchWire layout, historyLessThanTimeWire layout]
            (historyActiveWire layout),
          (ClassicalReversibleInstruction.xorDoublyControlled
            (historyActiveWire layout) (historyEqualityFlag layout)
            layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
            (historyP15Active_ne_orderBoundarySignal layout)
            (historyP15EqualityFlag_ne_orderBoundarySignal layout)).basisAction,
          ClassicalReversibleStage.conjunctionDirectBasisAction
            [historyBranchWire layout, historyLessThanTimeWire layout]
            (historyActiveWire layout),
          (ClassicalReversibleInstruction.xorOne
            (historyEqualityFlag layout)).basisAction,
          historyLessThanConstantDirectBasisAction
            (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder].map
          deterministicOperator))
      (basisKet input) =
    basisKet (historyP15OrderBoundarySourceAction layout input)
  rw [operatorSequence_deterministicOperator,
    applyOperator_deterministicOperator_basisKet]
  simp only [List.foldl]
  rfl

private theorem historyP15OrderBoundarySourceAction_eq_direct
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (clean : historyP15OrderBoundaryCleanPredicate layout input)
    (stable : historyTaylorPostGeneratorStablePredicate layout input) :
    historyP15OrderBoundarySourceAction layout input =
      historyTaylorOrderBoundaryBasisAction layout input := by
  let lessValue := historyTaylorOrderLessThanTaylorOrderValue layout input
  let conjunctionValue :=
    (input (historyBranchWire layout) && input (historyLessThanTimeWire layout))
  let first := historyLessThanConstantDirectBasisAction
    (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder input
  let complemented := xorWire (historyEqualityFlag layout) true first
  let active := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyLessThanTimeWire layout]
    (historyActiveWire layout) complemented
  let used := xorWire layout.orderBoundarySignal
    (active (historyActiveWire layout) && active (historyEqualityFlag layout)) active
  let unactive := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyLessThanTimeWire layout]
    (historyActiveWire layout) used
  let uncomplemented := xorWire (historyEqualityFlag layout) true unactive
  let final := historyLessThanConstantDirectBasisAction
    (historyP15OrderBoundaryLessThanSpec layout) parameters.taylorOrder
    uncomplemented
  have source_eq : historyP15OrderBoundarySourceAction layout input = final := by
    rfl
  rw [source_eq]
  unfold historyTaylorOrderBoundaryBasisAction historyTaylorOrderBoundaryCondition
  rw [← stable.2.1]
  change final = xorWire layout.orderBoundarySignal
    (conjunctionValue && !lessValue) input
  have first_eq : first = xorWire (historyEqualityFlag layout) lessValue input := by
    dsimp [first, lessValue]
    exact historyP15OrderBoundaryLessDirectAction_eq layout input
  have first_agrees : agreesExcept (historyEqualityFlag layout) first input := by
    intro wire different
    rw [first_eq]
    exact xorWire_apply_other (historyEqualityFlag layout) wire different _ input
  have first_flag : first (historyEqualityFlag layout) = lessValue := by
    rw [first_eq, xorWire_apply_same, clean.1]
    cases lessValue <;> rfl
  have first_active : first (historyActiveWire layout) = false := by
    rw [first_eq, xorWire_apply_other (historyEqualityFlag layout)
      (historyActiveWire layout) (historyP15Active_ne_equalityFlag layout)]
    exact clean.2.2
  have first_branch : first (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    rw [first_eq, xorWire_apply_other (historyEqualityFlag layout)
      (historyBranchWire layout) (historyP15Branch_ne_equalityFlag layout)]
  have first_time : first (historyLessThanTimeWire layout) =
      input (historyLessThanTimeWire layout) := by
    rw [first_eq, xorWire_apply_other (historyEqualityFlag layout)
      (historyLessThanTimeWire layout)
      (historyP15LessThanTime_ne_equalityFlag layout)]
  have complemented_agrees : agreesExcept (historyEqualityFlag layout)
      complemented first := by
    intro wire different
    exact xorWire_apply_other (historyEqualityFlag layout) wire different _ first
  have complemented_flag : complemented (historyEqualityFlag layout) =
      !lessValue := by
    change xorWire (historyEqualityFlag layout) true first
      (historyEqualityFlag layout) = !lessValue
    rw [xorWire_apply_same, first_flag]
    cases lessValue <;> rfl
  have complemented_active : complemented (historyActiveWire layout) = false := by
    change xorWire (historyEqualityFlag layout) true first
      (historyActiveWire layout) = false
    rw [xorWire_apply_other (historyEqualityFlag layout)
      (historyActiveWire layout) (historyP15Active_ne_equalityFlag layout)]
    exact first_active
  have complemented_branch : complemented (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    change xorWire (historyEqualityFlag layout) true first
      (historyBranchWire layout) = input (historyBranchWire layout)
    rw [xorWire_apply_other (historyEqualityFlag layout)
      (historyBranchWire layout) (historyP15Branch_ne_equalityFlag layout),
      first_branch]
  have complemented_time : complemented (historyLessThanTimeWire layout) =
      input (historyLessThanTimeWire layout) := by
    change xorWire (historyEqualityFlag layout) true first
      (historyLessThanTimeWire layout) = input (historyLessThanTimeWire layout)
    rw [xorWire_apply_other (historyEqualityFlag layout)
      (historyLessThanTimeWire layout)
      (historyP15LessThanTime_ne_equalityFlag layout), first_time]
  have complemented_condition : ClassicalReversibleStage.allWiresTrue
      [historyBranchWire layout, historyLessThanTimeWire layout] complemented =
        conjunctionValue := by
    rw [historyP15OrderBoundaryConjunctionCondition layout complemented,
      complemented_branch, complemented_time]
  have active_agrees : agreesExcept (historyActiveWire layout) active complemented := by
    intro wire different
    exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) wire different complemented
  have active_flag : active (historyEqualityFlag layout) = !lessValue := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) complemented (historyEqualityFlag layout) =
        !lessValue
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) (historyEqualityFlag layout)
      (historyP15Active_ne_equalityFlag layout).symm,
      complemented_flag]
  have active_value : active (historyActiveWire layout) = conjunctionValue := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) complemented (historyActiveWire layout) =
        conjunctionValue
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target,
      complemented_active, complemented_condition]
    cases conjunctionValue <;> rfl
  have active_branch : active (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) complemented (historyBranchWire layout) =
        input (historyBranchWire layout)
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) (historyBranchWire layout)
      (historyBranchWire_ne_activeWire layout), complemented_branch]
  have active_time : active (historyLessThanTimeWire layout) =
      input (historyLessThanTimeWire layout) := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) complemented (historyLessThanTimeWire layout) =
        input (historyLessThanTimeWire layout)
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_ne_activeWire layout), complemented_time]
  have used_control :
      (active (historyActiveWire layout) && active (historyEqualityFlag layout)) =
        (conjunctionValue && !lessValue) := by
    rw [active_value, active_flag]
  have used_agrees : agreesExcept layout.orderBoundarySignal used active := by
    intro wire different
    exact xorWire_apply_other layout.orderBoundarySignal wire different _ active
  have used_active : used (historyActiveWire layout) = conjunctionValue := by
    change xorWire layout.orderBoundarySignal
      (active (historyActiveWire layout) && active (historyEqualityFlag layout)) active
      (historyActiveWire layout) = conjunctionValue
    rw [xorWire_apply_other layout.orderBoundarySignal
      (historyActiveWire layout) (historyP15Active_ne_orderBoundarySignal layout),
      active_value]
  have used_flag : used (historyEqualityFlag layout) = !lessValue := by
    change xorWire layout.orderBoundarySignal
      (active (historyActiveWire layout) && active (historyEqualityFlag layout)) active
      (historyEqualityFlag layout) = !lessValue
    rw [xorWire_apply_other layout.orderBoundarySignal
      (historyEqualityFlag layout)
      (historyP15EqualityFlag_ne_orderBoundarySignal layout), active_flag]
  have used_branch : used (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    change xorWire layout.orderBoundarySignal
      (active (historyActiveWire layout) && active (historyEqualityFlag layout)) active
      (historyBranchWire layout) = input (historyBranchWire layout)
    rw [xorWire_apply_other layout.orderBoundarySignal
      (historyBranchWire layout)
      (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
        (historyBranchWire_mem_workspace layout)), active_branch]
  have used_time : used (historyLessThanTimeWire layout) =
      input (historyLessThanTimeWire layout) := by
    change xorWire layout.orderBoundarySignal
      (active (historyActiveWire layout) && active (historyEqualityFlag layout)) active
      (historyLessThanTimeWire layout) = input (historyLessThanTimeWire layout)
    rw [xorWire_apply_other layout.orderBoundarySignal
      (historyLessThanTimeWire layout)
      (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
        (historyLessThanTimeWire_mem_workspace layout)), active_time]
  have used_condition : ClassicalReversibleStage.allWiresTrue
      [historyBranchWire layout, historyLessThanTimeWire layout] used =
        conjunctionValue := by
    rw [historyP15OrderBoundaryConjunctionCondition layout used,
      used_branch, used_time]
  have unactive_agrees : agreesExcept (historyActiveWire layout) unactive used := by
    intro wire different
    exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) wire different used
  have unactive_flag : unactive (historyEqualityFlag layout) = !lessValue := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) used (historyEqualityFlag layout) =
        !lessValue
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) (historyEqualityFlag layout)
      (historyP15Active_ne_equalityFlag layout).symm, used_flag]
  have unactive_value : unactive (historyActiveWire layout) = false := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyActiveWire layout) used (historyActiveWire layout) = false
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target,
      used_active, used_condition]
    cases conjunctionValue <;> rfl
  have uncomplemented_agrees : agreesExcept (historyEqualityFlag layout)
      uncomplemented unactive := by
    intro wire different
    exact xorWire_apply_other (historyEqualityFlag layout) wire different _ unactive
  have uncomplemented_flag : uncomplemented (historyEqualityFlag layout) =
      lessValue := by
    change xorWire (historyEqualityFlag layout) true unactive
      (historyEqualityFlag layout) = lessValue
    rw [xorWire_apply_same, unactive_flag]
    cases lessValue <;> rfl
  have uncomplemented_active : uncomplemented (historyActiveWire layout) = false := by
    change xorWire (historyEqualityFlag layout) true unactive
      (historyActiveWire layout) = false
    rw [xorWire_apply_other (historyEqualityFlag layout)
      (historyActiveWire layout) (historyP15Active_ne_equalityFlag layout),
      unactive_value]
  have first_less : historyTaylorOrderLessThanTaylorOrderValue layout first =
      lessValue := by
    dsimp [lessValue]
    exact historyP15OrderBoundaryOrderLess_equalityFlagInvariant layout
      first input first_agrees
  have complemented_less :
      historyTaylorOrderLessThanTaylorOrderValue layout complemented = lessValue := by
    calc
      historyTaylorOrderLessThanTaylorOrderValue layout complemented =
          historyTaylorOrderLessThanTaylorOrderValue layout first :=
        historyP15OrderBoundaryOrderLess_equalityFlagInvariant layout
          complemented first complemented_agrees
      _ = lessValue := first_less
  have active_less : historyTaylorOrderLessThanTaylorOrderValue layout active =
      lessValue := by
    calc
      historyTaylorOrderLessThanTaylorOrderValue layout active =
          historyTaylorOrderLessThanTaylorOrderValue layout complemented :=
        historyP15OrderBoundaryOrderLess_activeInvariant layout
          active complemented active_agrees
      _ = lessValue := complemented_less
  have used_less : historyTaylorOrderLessThanTaylorOrderValue layout used =
      lessValue := by
    calc
      historyTaylorOrderLessThanTaylorOrderValue layout used =
          historyTaylorOrderLessThanTaylorOrderValue layout active :=
        (historyP15OrderBoundaryOrderLess_signalInvariant layout active used
          (fun wire different => (used_agrees wire different).symm)).symm
      _ = lessValue := active_less
  have unactive_less : historyTaylorOrderLessThanTaylorOrderValue layout unactive =
      lessValue := by
    calc
      historyTaylorOrderLessThanTaylorOrderValue layout unactive =
          historyTaylorOrderLessThanTaylorOrderValue layout used :=
        historyP15OrderBoundaryOrderLess_activeInvariant layout unactive used
          unactive_agrees
      _ = lessValue := used_less
  have uncomplemented_less :
      historyTaylorOrderLessThanTaylorOrderValue layout uncomplemented =
        lessValue := by
    calc
      historyTaylorOrderLessThanTaylorOrderValue layout uncomplemented =
          historyTaylorOrderLessThanTaylorOrderValue layout unactive :=
        historyP15OrderBoundaryOrderLess_equalityFlagInvariant layout
          uncomplemented unactive uncomplemented_agrees
      _ = lessValue := unactive_less
  have final_eq : final = xorWire (historyEqualityFlag layout)
      (historyTaylorOrderLessThanTaylorOrderValue layout uncomplemented)
      uncomplemented := by
    dsimp [final]
    exact historyP15OrderBoundaryLessDirectAction_eq layout uncomplemented
  have final_flag : final (historyEqualityFlag layout) = false := by
    rw [final_eq, xorWire_apply_same, uncomplemented_flag,
      uncomplemented_less]
    cases lessValue <;> rfl
  have final_active : final (historyActiveWire layout) = false := by
    rw [final_eq, xorWire_apply_other (historyEqualityFlag layout)
      (historyActiveWire layout) (historyP15Active_ne_equalityFlag layout),
      uncomplemented_active]
  have final_agrees : agreesExcept layout.orderBoundarySignal final input := by
    intro wire different
    by_cases isFlag : wire = historyEqualityFlag layout
    · subst wire
      exact final_flag.trans clean.1.symm
    by_cases isActive : wire = historyActiveWire layout
    · subst wire
      exact final_active.trans clean.2.2.symm
    calc
      final wire = uncomplemented wire := by
        rw [final_eq, xorWire_apply_other (historyEqualityFlag layout) wire isFlag]
      _ = unactive wire := by
        change xorWire (historyEqualityFlag layout) true unactive wire = _
        rw [xorWire_apply_other (historyEqualityFlag layout) wire isFlag]
      _ = used wire := by
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyLessThanTimeWire layout]
          (historyActiveWire layout) wire isActive used
      _ = active wire := by
        change xorWire layout.orderBoundarySignal
          (active (historyActiveWire layout) && active (historyEqualityFlag layout))
          active wire = _
        rw [xorWire_apply_other layout.orderBoundarySignal wire different]
      _ = complemented wire := by
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyLessThanTimeWire layout]
          (historyActiveWire layout) wire isActive complemented
      _ = first wire := by
        change xorWire (historyEqualityFlag layout) true first wire = _
        rw [xorWire_apply_other (historyEqualityFlag layout) wire isFlag]
      _ = input wire := by
        rw [first_eq, xorWire_apply_other (historyEqualityFlag layout) wire isFlag]
  have active_signal : active layout.orderBoundarySignal =
      input layout.orderBoundarySignal := by
    calc
      active layout.orderBoundarySignal =
          complemented layout.orderBoundarySignal :=
        active_agrees layout.orderBoundarySignal
          (historyP15Active_ne_orderBoundarySignal layout).symm
      _ = first layout.orderBoundarySignal :=
        complemented_agrees layout.orderBoundarySignal
          (historyP15EqualityFlag_ne_orderBoundarySignal layout).symm
      _ = input layout.orderBoundarySignal := by
        rw [first_eq, xorWire_apply_other (historyEqualityFlag layout)
          layout.orderBoundarySignal
          (historyP15EqualityFlag_ne_orderBoundarySignal layout).symm]
  have final_signal : final layout.orderBoundarySignal =
      xorWire layout.orderBoundarySignal (conjunctionValue && !lessValue) input
        layout.orderBoundarySignal := by
    calc
      final layout.orderBoundarySignal = uncomplemented layout.orderBoundarySignal := by
        rw [final_eq, xorWire_apply_other (historyEqualityFlag layout)
          layout.orderBoundarySignal
          (historyP15EqualityFlag_ne_orderBoundarySignal layout).symm]
      _ = unactive layout.orderBoundarySignal := by
        change xorWire (historyEqualityFlag layout) true unactive
          layout.orderBoundarySignal = _
        rw [xorWire_apply_other (historyEqualityFlag layout)
          layout.orderBoundarySignal
          (historyP15EqualityFlag_ne_orderBoundarySignal layout).symm]
      _ = used layout.orderBoundarySignal := by
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyLessThanTimeWire layout]
          (historyActiveWire layout) layout.orderBoundarySignal
          (historyP15Active_ne_orderBoundarySignal layout).symm used
      _ = xorWire layout.orderBoundarySignal
          (active (historyActiveWire layout) && active (historyEqualityFlag layout)) active
          layout.orderBoundarySignal := rfl
      _ = xorWire layout.orderBoundarySignal
          (conjunctionValue && !lessValue) input layout.orderBoundarySignal := by
        simp only [xorWire_apply_same]
        rw [used_control]
        rw [active_signal]
  funext wire
  by_cases isSignal : wire = layout.orderBoundarySignal
  · subst wire
    exact final_signal
  rw [xorWire_apply_other layout.orderBoundarySignal wire isSignal]
  exact final_agrees wire isSignal

/-- The seven genuine post-Q10 source stages, restricted to the stable
boundary which supplies their clean comparator and flag ancillas.  The target
is the direct order-boundary signal action; no full-space circuit equality is
claimed. -/
noncomputable def historyP15OrderBoundaryComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let raw := historyP15OrderBoundaryRawComponent layout
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    raw.circuit (historyTaylorOrderBoundaryOperator layout)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (by
      intro input inside
      have clean := historyP15PostQ10StablePredicate_implies_orderBoundaryClean
        layout widths input inside
      calc
        applyOperator
            (Circuit.denote (historyP15PostGate (qubits := qubits)) raw.circuit)
            (basisKet input) =
          applyOperator raw.target (basisKet input) :=
            raw.correct _
              (SubspaceMapComponent.basisKet_mem_basisSpan clean)
        _ = basisKet (historyP15OrderBoundarySourceAction layout input) :=
          historyP15OrderBoundaryRawTarget_basisKet layout input
        _ = basisKet (historyTaylorOrderBoundaryBasisAction layout input) := by
          rw [historyP15OrderBoundarySourceAction_eq_direct layout input clean
            inside.2]
        _ = applyOperator (historyTaylorOrderBoundaryOperator layout)
            (basisKet input) := by
          rw [historyTaylorOrderBoundaryOperator,
            applyOperator_deterministicOperator_basisKet])
    (by
      intro input inside
      rw [historyTaylorOrderBoundaryOperator,
        applyOperator_deterministicOperator_basisKet]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      constructor
      · simpa [historyTaylorOrderBoundaryBasisAction] using
          historyP15PostQ10OutputPredicate_xorPostSignal widths
            layout.orderBoundarySignal (by simp)
            (historyTaylorOrderBoundaryCondition layout input) input inside.1
      · exact historyTaylorOrderBoundaryBasisAction_maps_stable
          layout input inside.2)

/-- Both interfaces are exactly the post-Q10 stable basis span. -/
@[simp] theorem historyP15OrderBoundaryComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15OrderBoundaryComponent layout widths).inputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) ∧
      (historyP15OrderBoundaryComponent layout widths).outputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) := by
  constructor <;> rfl

/-- Literal source order for the P15 `orderBoundarySignal` word: comparator
compute, X, active compute, Toffoli use, then the three reverse stages. -/
noncomputable def historyP15OrderBoundarySourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    List (Circuit (PrimitiveGate qubits)) :=
  [(historyP15OrderBoundaryDegreeLessComputeComponent layout).circuit,
   (historyP15OrderBoundaryEqualityXComputeComponent layout).circuit,
   (historyP15OrderBoundaryActiveComputeComponent layout).circuit,
   (historyP15OrderBoundaryToffoliComponent layout).circuit,
   (historyP15OrderBoundaryActiveUncomputeComponent layout).circuit,
   (historyP15OrderBoundaryEqualityXUncomputeComponent layout).circuit,
   (historyP15OrderBoundaryDegreeLessUncomputeComponent layout).circuit]

/-- The literal circuit assembled from the seven source-order stages. -/
noncomputable def historyP15OrderBoundarySourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence (historyP15OrderBoundarySourceStages layout)

private theorem historyP15OrderBoundaryRawComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryRawComponent layout).circuit =
      Circuit.sequence
        [(historyP15OrderBoundaryDegreeLessComputeComponent layout).circuit,
         (historyP15OrderBoundaryEqualityXComputeComponent layout).circuit,
         (historyP15OrderBoundaryActiveComputeComponent layout).circuit,
         (historyP15OrderBoundaryToffoliComponent layout).circuit,
         (historyP15OrderBoundaryActiveUncomputeComponent layout).circuit,
         (historyP15OrderBoundaryEqualityXUncomputeComponent layout).circuit,
         (historyP15OrderBoundaryDegreeLessUncomputeComponent layout).circuit] := rfl

/-- The public component retains the raw source circuit; only its typing and
target contract are refined to the stable boundary. -/
@[simp] theorem historyP15OrderBoundaryComponent_circuit_eq_raw
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15OrderBoundaryComponent layout widths).circuit =
      (historyP15OrderBoundaryRawComponent layout).circuit := rfl

/-- The actual public circuit has exactly the primitive-gate flattening of
the literal seven-stage source word, in source order. -/
theorem historyP15OrderBoundaryComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15OrderBoundaryComponent layout widths).circuit.flatten =
      (historyP15OrderBoundarySourceCircuit layout).flatten := by
  rw [historyP15OrderBoundaryComponent_circuit_eq_raw,
    historyP15OrderBoundaryRawComponent_circuit]
  simp [historyP15OrderBoundarySourceCircuit,
    historyP15OrderBoundarySourceStages, Circuit.sequence,
    Circuit.flatten]

/-! ### Idle-boundary signal: two clock CNOTs, equality, use, restoration

The frozen post-Q10 word first XORs the two already-recorded clock predicates
into the idle flag.  It then computes the branch/idle conjunction and the
last-order equality, uses those two controls on the order-boundary signal,
and reverses every temporary computation.  As with the preceding group, all
claims below are restricted to the clean post-Q10 stable sector.
-/

private theorem historyP15SharedPool_ge_five
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (_layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
  calc
    5 ≤ historyStructuralPoolWidth parameters := by
      unfold historyStructuralPoolWidth
      omega
    _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
      Nat.le_max_right _ _

private theorem historyP15IdleFlag_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ∈ historyRegisterWires layout.workspace := by
  unfold historyIdleFlag
  apply historyWorkspaceSlice_wire_mem

private theorem historyP15IdleFlag_ne_branch
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ≠ historyBranchWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast := historyP15SharedPool_ge_five layout
  omega

private theorem historyP15IdleFlag_ne_lessThanTime
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ≠ historyLessThanTimeWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast := historyP15SharedPool_ge_five layout
  omega

private theorem historyP15IdleFlag_ne_lessThanIdleEnd
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ≠ historyLessThanIdleEndWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast := historyP15SharedPool_ge_five layout
  omega

private theorem historyP15IdleFlag_ne_active
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ≠ historyActiveWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast := historyP15SharedPool_ge_five layout
  omega

private theorem historyP15IdleFlag_ne_equalityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ≠ historyEqualityFlag layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

private theorem historyP15EqualityWorkWire_ne_idleFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyEqualityWorkWidth parameters)) :
    (historyEqualityWork layout).wire index ≠ historyIdleFlag layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast := historyP15SharedPool_ge_five layout
  omega

private theorem historyP15EqualityWorkWire_ne_active
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyEqualityWorkWidth parameters)) :
    (historyEqualityWork layout).wire index ≠ historyActiveWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have structuralFits : historyStructuralPoolWidth parameters ≤
      historySharedPoolWidth parameters generatorWorkWidth :=
    Nat.le_max_right _ _
  unfold historyStructuralPoolWidth historyMaximumLabelWidth at structuralFits
  omega

private theorem historyP15OrderWire_ne_idleFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (orderIndex : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire orderIndex ≠ historyIdleFlag layout := by
  have workspaceMember := historyP15IdleFlag_mem_workspace layout
  rcases List.mem_ofFn.mp workspaceMember with ⟨workspaceIndex, workspaceEqual⟩
  intro equal
  exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
    (equal.trans workspaceEqual.symm)

private theorem historyP15IdleFlag_ne_orderBoundarySignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ≠ layout.orderBoundarySignal :=
  historyP15OrderBoundaryWorkspaceWire_ne_signal layout (historyIdleFlag layout)
    (historyP15IdleFlag_mem_workspace layout)

private theorem historyP15IdleBoundaryIdleFlag_not_mem_stableFlags
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] := by
  intro member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal
  · exact (historyP15IdleFlag_ne_branch layout) equal
  · exact (historyP15IdleFlag_ne_lessThanTime layout) equal
  · exact (historyP15IdleFlag_ne_lessThanIdleEnd layout) equal

private theorem historyP15IdleBoundaryEqualityWork_not_mem_stableFlags
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyEqualityWorkWidth parameters)) :
    (historyEqualityWork layout).wire index ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] := by
  intro member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal
  all_goals
    change layout.workspace.wire _ = layout.workspace.wire _ at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    dsimp at valuesEqual
    have sharedAtLeast := historyP15SharedPool_ge_five layout
    have structuralFits : historyStructuralPoolWidth parameters ≤
        historySharedPoolWidth parameters generatorWorkWidth :=
      Nat.le_max_right _ _
    unfold historyStructuralPoolWidth historyMaximumLabelWidth at structuralFits
    omega

/-- Internal clean sector for the source-faithful idle-boundary word.  It
records each temporary target explicitly: idle parity, conjunction target,
equality flag, and equality compiler work. -/
def historyP15IdleBoundaryCleanPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyIdleFlag layout) = false ∧
    basis (historyActiveWire layout) = false ∧
    basis (historyEqualityFlag layout) = false ∧
    ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) basis

private def historyP15IdleBoundaryIdleEndComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyIdleFlag layout) = basis (historyLessThanIdleEndWire layout) ∧
    basis (historyActiveWire layout) = false ∧
    basis (historyEqualityFlag layout) = false ∧
    ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) basis

private def historyP15IdleBoundaryIdleComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyIdleFlag layout) =
      (basis (historyLessThanIdleEndWire layout) !=
        basis (historyLessThanTimeWire layout)) ∧
    basis (historyActiveWire layout) = false ∧
    basis (historyEqualityFlag layout) = false ∧
    ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) basis

private def historyP15IdleBoundaryActiveComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyIdleFlag layout) =
      (basis (historyLessThanIdleEndWire layout) !=
        basis (historyLessThanTimeWire layout)) ∧
    basis (historyActiveWire layout) =
      (basis (historyBranchWire layout) && basis (historyIdleFlag layout)) ∧
    basis (historyEqualityFlag layout) = false ∧
    ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) basis

private def historyP15IdleBoundaryEqualityComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyIdleFlag layout) =
      (basis (historyLessThanIdleEndWire layout) !=
        basis (historyLessThanTimeWire layout)) ∧
    basis (historyActiveWire layout) =
      (basis (historyBranchWire layout) && basis (historyIdleFlag layout)) ∧
    basis (historyEqualityFlag layout) =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) basis ∧
    ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) basis

/-- The post-Q10 stable boundary supplies all idle-boundary work-clean
premises.  Stored clock flags remain live; all four temporary targets here
are outside that live set. -/
theorem historyP15PostQ10StablePredicate_implies_idleBoundaryClean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    historyP15IdleBoundaryCleanPredicate layout input := by
  have orderClean := historyP15PostQ10StablePredicate_implies_orderBoundaryClean
    layout widths input inside
  unfold historyP15IdleBoundaryCleanPredicate
  refine ⟨?_, orderClean.2.2, orderClean.1, ?_⟩
  · rcases List.mem_ofFn.mp (historyP15IdleFlag_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    rw [← equal]
    have outside : layout.workspace.wire workspaceIndex ∉
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout] := by
      simpa [equal] using historyP15IdleBoundaryIdleFlag_not_mem_stableFlags
        layout
    exact historyP15OrderBoundaryStableWorkspaceZero layout widths input inside
      workspaceIndex outside
  · intro wire workMember
    simp only [historyRegisterWires, List.mem_ofFn] at workMember
    rcases workMember with ⟨index, rfl⟩
    rcases List.mem_ofFn.mp
        (historyP15EqualityWork_wire_mem_workspace layout index) with
      ⟨workspaceIndex, equal⟩
    have outside : layout.workspace.wire workspaceIndex ∉
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout] := by
      simpa [equal] using
        historyP15IdleBoundaryEqualityWork_not_mem_stableFlags layout index
    have zero := historyP15OrderBoundaryStableWorkspaceZero layout widths input
      inside workspaceIndex outside
    simpa [ClassicalReversibleStage.minimumWorkCleanPredicate,
      historyRegisterWires, equal] using zero

private noncomputable def historyP15IdleBoundaryCnotComponent
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (directMaps : ∀ input, inputPredicate input → outputPredicate
      ((ClassicalReversibleInstruction.xorControlled control target different).basisAction
        input)) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  historyP15OrderBoundaryInstructionComponent
    (.xorControlled control target different)
    inputPredicate outputPredicate directMaps

private noncomputable def historyP15IdleBoundaryIdleEndToggleComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15IdleBoundaryCnotComponent
    (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
    (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm
    (historyP15IdleBoundaryCleanPredicate layout)
    (historyP15IdleBoundaryIdleEndComputedPredicate layout)
    (by
      intro input inside
      unfold historyP15IdleBoundaryCleanPredicate at inside
      unfold historyP15IdleBoundaryIdleEndComputedPredicate
      change historyP15IdleBoundaryIdleEndComputedPredicate layout
        (xorWire (historyIdleFlag layout)
          (input (historyLessThanIdleEndWire layout)) input)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [xorWire_apply_same, inside.1,
          xorWire_apply_other (historyIdleFlag layout)
            (historyLessThanIdleEndWire layout)
            (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm]
        cases input (historyLessThanIdleEndWire layout) <;> rfl
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyActiveWire layout) (historyP15IdleFlag_ne_active layout).symm]
        exact inside.2.1
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyEqualityFlag layout)
          (historyP15IdleFlag_ne_equalityFlag layout).symm]
        exact inside.2.2.1
      · intro wire workMember
        simp only [historyRegisterWires, List.mem_ofFn] at workMember
        rcases workMember with ⟨index, rfl⟩
        rw [xorWire_apply_other (historyIdleFlag layout)
          ((historyEqualityWork layout).wire index)
          (historyP15EqualityWorkWire_ne_idleFlag layout index)]
        exact inside.2.2.2 _ (by
          simp [historyRegisterWires]))

private theorem historyP15IdleBoundaryIdleEndToggleComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryIdleEndToggleComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorControlled
          (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm).basisAction := rfl

private noncomputable def historyP15IdleBoundaryTimeToggleComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15IdleBoundaryCnotComponent
    (historyLessThanTimeWire layout) (historyIdleFlag layout)
    (historyP15IdleFlag_ne_lessThanTime layout).symm
    (historyP15IdleBoundaryIdleEndComputedPredicate layout)
    (historyP15IdleBoundaryIdleComputedPredicate layout)
    (by
      intro input inside
      unfold historyP15IdleBoundaryIdleEndComputedPredicate at inside
      unfold historyP15IdleBoundaryIdleComputedPredicate
      change historyP15IdleBoundaryIdleComputedPredicate layout
        (xorWire (historyIdleFlag layout)
          (input (historyLessThanTimeWire layout)) input)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [xorWire_apply_same, inside.1,
          xorWire_apply_other (historyIdleFlag layout)
            (historyLessThanIdleEndWire layout)
            (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm,
          xorWire_apply_other (historyIdleFlag layout)
            (historyLessThanTimeWire layout)
            (historyP15IdleFlag_ne_lessThanTime layout).symm]
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyActiveWire layout) (historyP15IdleFlag_ne_active layout).symm]
        exact inside.2.1
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyEqualityFlag layout)
          (historyP15IdleFlag_ne_equalityFlag layout).symm]
        exact inside.2.2.1
      · intro wire workMember
        simp only [historyRegisterWires, List.mem_ofFn] at workMember
        rcases workMember with ⟨index, rfl⟩
        rw [xorWire_apply_other (historyIdleFlag layout)
          ((historyEqualityWork layout).wire index)
          (historyP15EqualityWorkWire_ne_idleFlag layout index)]
        exact inside.2.2.2 _ (by
          simp [historyRegisterWires]))

private theorem historyP15IdleBoundaryTimeToggleComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryTimeToggleComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorControlled
          (historyLessThanTimeWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanTime layout).symm).basisAction := rfl

private theorem historyP15IdleBoundaryConjunctionLayout_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ([historyBranchWire layout, historyIdleFlag layout] ++ [] ++
      [historyActiveWire layout]).Nodup := by
  simp [(historyP15IdleFlag_ne_branch layout).symm,
    historyP15IdleFlag_ne_active,
    historyBranchWire_ne_activeWire]

private theorem historyP15IdleBoundaryConjunctionCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    ClassicalReversibleStage.allWiresTrue
      [historyBranchWire layout, historyIdleFlag layout] input =
        (input (historyBranchWire layout) && input (historyIdleFlag layout)) := by
  simp [ClassicalReversibleStage.allWiresTrue,
    ClassicalReversibleStage.readWires]

private noncomputable def historyP15IdleBoundaryActiveComputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyBranchWire layout, historyIdleFlag layout] []
    (historyActiveWire layout) (by simp)
    (historyP15IdleBoundaryConjunctionLayout_nodup layout)
    (historyP15IdleBoundaryIdleComputedPredicate layout)
    (historyP15IdleBoundaryActiveComputedPredicate layout)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input inside
      unfold historyP15IdleBoundaryIdleComputedPredicate at inside
      unfold historyP15IdleBoundaryActiveComputedPredicate
      let action := ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyIdleFlag layout]
        (historyActiveWire layout)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_active layout)]
        rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) (historyLessThanIdleEndWire layout)
          (historyLessThanIdleEndWire_ne_activeWire layout),
          ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) (historyLessThanTimeWire layout)
          (historyLessThanTimeWire_ne_activeWire layout)]
        exact inside.1
      · change action input (historyActiveWire layout) =
          (action input (historyBranchWire layout) &&
            action input (historyIdleFlag layout))
        have conditionStable :
            (action input (historyBranchWire layout) &&
              action input (historyIdleFlag layout)) =
              (input (historyBranchWire layout) && input (historyIdleFlag layout)) := by
          dsimp [action]
          rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
            [historyBranchWire layout, historyIdleFlag layout]
            (historyActiveWire layout) (historyBranchWire layout)
            (historyBranchWire_ne_activeWire layout),
            ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
            [historyBranchWire layout, historyIdleFlag layout]
            (historyActiveWire layout) (historyIdleFlag layout)
            (historyP15IdleFlag_ne_active layout)]
        rw [show action input (historyActiveWire layout) =
            (input (historyActiveWire layout) !=
              ClassicalReversibleStage.allWiresTrue
                [historyBranchWire layout, historyIdleFlag layout] input) by
              exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target
                _ _ _, historyP15IdleBoundaryConjunctionCondition layout input,
          inside.2.1, conditionStable]
        cases input (historyBranchWire layout) <;>
          cases input (historyIdleFlag layout) <;> rfl
      · rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) (historyEqualityFlag layout)
          (historyP15Active_ne_equalityFlag layout).symm]
        exact inside.2.2.1
      · intro wire workMember
        simp only [historyRegisterWires, List.mem_ofFn] at workMember
        rcases workMember with ⟨index, rfl⟩
        rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) ((historyEqualityWork layout).wire index)
          (historyP15EqualityWorkWire_ne_active layout index)]
        exact inside.2.2.2 _ (by
          simp [historyRegisterWires]))

private theorem historyP15IdleBoundaryActiveComputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryActiveComputeComponent layout).target =
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyIdleFlag layout]
        (historyActiveWire layout) := rfl

private theorem historyP15IdleBoundaryOrderEqualsLast_equalityActionInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1)
        (ClassicalReversibleStage.equalityToConstantDirectBasisAction
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) input) =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) input := by
  apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
  intro wire wireMember
  simp only [historyRegisterWires, List.mem_ofFn] at wireMember
  rcases wireMember with ⟨orderIndex, rfl⟩
  exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
    (historyRegisterWires layout.order)
    (historyIdleBlockSize parameters.taylorOrder - 1)
    (historyEqualityFlag layout) (layout.order.wire orderIndex)
    (historyP15OrderWire_ne_equalityFlag layout orderIndex) input

private noncomputable def historyP15IdleBoundaryEqualityComputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  ClassicalReversibleStage.xorEqualityToConstantMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (historyRegisterWires layout.order)
    (historyRegisterWires (historyEqualityWork layout))
    (historyIdleBlockSize parameters.taylorOrder - 1)
    (historyEqualityFlag layout)
    (historyP15CoefficientEquality_enoughScratch layout)
    (historyP15CoefficientEqualityLayout_nodup layout)
    (historyP15IdleBoundaryActiveComputedPredicate layout)
    (historyP15IdleBoundaryEqualityComputedPredicate layout)
    (by
      intro input inside
      unfold historyP15IdleBoundaryActiveComputedPredicate at inside
      exact inside.2.2.2)
    (by
      intro input inside
      unfold historyP15IdleBoundaryActiveComputedPredicate at inside
      unfold historyP15IdleBoundaryEqualityComputedPredicate
      have orderStable :=
        historyP15IdleBoundaryOrderEqualsLast_equalityActionInvariant layout input
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_equalityFlag layout),
          ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyLessThanIdleEndWire layout)
          (historyP15LessThanIdleEnd_ne_equalityFlag layout),
          ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyLessThanTimeWire layout)
          (historyP15LessThanTime_ne_equalityFlag layout)]
        exact inside.1
      · rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyActiveWire layout)
          (historyP15Active_ne_equalityFlag layout),
          ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyBranchWire layout)
          (historyP15Branch_ne_equalityFlag layout),
          ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_equalityFlag layout)]
        exact inside.2.1
      · rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
          inside.2.2.1, orderStable]
        cases h : ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1) input <;> rfl
      · exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_clean
          (historyRegisterWires layout.order)
          (historyRegisterWires (historyEqualityWork layout))
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) input
          (historyP15CoefficientEqualityLayout_nodup layout) inside.2.2.2)

private theorem historyP15IdleBoundaryEqualityComputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryEqualityComputeComponent layout).target =
      ClassicalReversibleStage.equalityToConstantDirectOperator
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1)
        (historyEqualityFlag layout) := rfl

private noncomputable def historyP15IdleBoundaryEqualityUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  ClassicalReversibleStage.xorEqualityToConstantMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (historyRegisterWires layout.order)
    (historyRegisterWires (historyEqualityWork layout))
    (historyIdleBlockSize parameters.taylorOrder - 1)
    (historyEqualityFlag layout)
    (historyP15CoefficientEquality_enoughScratch layout)
    (historyP15CoefficientEqualityLayout_nodup layout)
    (historyP15IdleBoundaryEqualityComputedPredicate layout)
    (historyP15IdleBoundaryActiveComputedPredicate layout)
    (by
      intro input inside
      unfold historyP15IdleBoundaryEqualityComputedPredicate at inside
      exact inside.2.2.2)
    (by
      intro input inside
      unfold historyP15IdleBoundaryEqualityComputedPredicate at inside
      unfold historyP15IdleBoundaryActiveComputedPredicate
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_equalityFlag layout),
          ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyLessThanIdleEndWire layout)
          (historyP15LessThanIdleEnd_ne_equalityFlag layout),
          ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyLessThanTimeWire layout)
          (historyP15LessThanTime_ne_equalityFlag layout)]
        exact inside.1
      · rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyActiveWire layout)
          (historyP15Active_ne_equalityFlag layout),
          ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyBranchWire layout)
          (historyP15Branch_ne_equalityFlag layout),
          ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_equalityFlag layout)]
        exact inside.2.1
      · rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
          inside.2.2.1]
        cases h : ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1) input <;> rfl
      · exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_clean
          (historyRegisterWires layout.order)
          (historyRegisterWires (historyEqualityWork layout))
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) input
          (historyP15CoefficientEqualityLayout_nodup layout) inside.2.2.2)

private theorem historyP15IdleBoundaryEqualityUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryEqualityUncomputeComponent layout).target =
      ClassicalReversibleStage.equalityToConstantDirectOperator
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1)
        (historyEqualityFlag layout) := rfl

private theorem historyP15IdleBoundaryOrderEqualsLast_signalInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept layout.orderBoundarySignal first second) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) first =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) second := by
  apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
  intro wire wireMember
  simp only [historyRegisterWires, List.mem_ofFn] at wireMember
  rcases wireMember with ⟨orderIndex, rfl⟩
  exact same _ ((layout.orderWire_separated orderIndex).2.2.1
    layout.orderBoundarySignal (by simp))

private theorem historyP15IdleBoundaryEqualityComputedPredicate_stableOutsideSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (before after : QubitBasis qubits)
    (inside : historyP15IdleBoundaryEqualityComputedPredicate layout before)
    (sameOutside : ∀ wire : Fin qubits, wire ≠ layout.orderBoundarySignal →
      after wire = before wire) :
    historyP15IdleBoundaryEqualityComputedPredicate layout after := by
  unfold historyP15IdleBoundaryEqualityComputedPredicate at inside ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sameOutside (historyIdleFlag layout)
        (historyP15IdleFlag_ne_orderBoundarySignal layout),
        sameOutside (historyLessThanIdleEndWire layout)
        (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
          (historyLessThanIdleEndWire_mem_workspace layout)),
        sameOutside (historyLessThanTimeWire layout)
        (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
          (historyLessThanTimeWire_mem_workspace layout))]
    exact inside.1
  · rw [sameOutside (historyActiveWire layout)
        (historyP15Active_ne_orderBoundarySignal layout),
        sameOutside (historyBranchWire layout)
        (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
          (historyBranchWire_mem_workspace layout)),
        sameOutside (historyIdleFlag layout)
        (historyP15IdleFlag_ne_orderBoundarySignal layout)]
    exact inside.2.1
  · rw [sameOutside (historyEqualityFlag layout)
        (historyP15EqualityFlag_ne_orderBoundarySignal layout)]
    have orderStable := historyP15IdleBoundaryOrderEqualsLast_signalInvariant
      layout after before (by
        intro wire different
        exact sameOutside wire different)
    rw [orderStable]
    exact inside.2.2.1
  · intro wire workMember
    have workspaceMember : wire ∈ historyRegisterWires layout.workspace := by
      simp only [historyRegisterWires, List.mem_ofFn] at workMember
      rcases workMember with ⟨index, rfl⟩
      exact historyP15EqualityWork_wire_mem_workspace layout index
    rw [sameOutside wire
      (historyP15OrderBoundaryWorkspaceWire_ne_signal layout wire workspaceMember)]
    exact inside.2.2.2 wire workMember

private noncomputable def historyP15IdleBoundaryToffoliComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15OrderBoundaryInstructionComponent
    (.xorDoublyControlled (historyActiveWire layout) (historyEqualityFlag layout)
      layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
      (historyP15Active_ne_orderBoundarySignal layout)
      (historyP15EqualityFlag_ne_orderBoundarySignal layout))
    (historyP15IdleBoundaryEqualityComputedPredicate layout)
    (historyP15IdleBoundaryEqualityComputedPredicate layout)
    (by
      intro input inside
      let action :=
        (ClassicalReversibleInstruction.xorDoublyControlled
          (historyActiveWire layout) (historyEqualityFlag layout)
          layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
          (historyP15Active_ne_orderBoundarySignal layout)
          (historyP15EqualityFlag_ne_orderBoundarySignal layout)).basisAction
      apply historyP15IdleBoundaryEqualityComputedPredicate_stableOutsideSignal
        layout input (action input) inside
      intro wire different
      dsimp [action, ClassicalReversibleInstruction.basisAction]
      exact xorWire_apply_other layout.orderBoundarySignal wire different _ input)

private theorem historyP15IdleBoundaryToffoliComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryToffoliComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorDoublyControlled
          (historyActiveWire layout) (historyEqualityFlag layout)
          layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
          (historyP15Active_ne_orderBoundarySignal layout)
          (historyP15EqualityFlag_ne_orderBoundarySignal layout)).basisAction := rfl

private noncomputable def historyP15IdleBoundaryActiveUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyBranchWire layout, historyIdleFlag layout] []
    (historyActiveWire layout) (by simp)
    (historyP15IdleBoundaryConjunctionLayout_nodup layout)
    (historyP15IdleBoundaryActiveComputedPredicate layout)
    (historyP15IdleBoundaryIdleComputedPredicate layout)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input inside
      unfold historyP15IdleBoundaryActiveComputedPredicate at inside
      unfold historyP15IdleBoundaryIdleComputedPredicate
      let action := ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyIdleFlag layout]
        (historyActiveWire layout)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_active layout)]
        rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) (historyLessThanIdleEndWire layout)
          (historyLessThanIdleEndWire_ne_activeWire layout),
          ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) (historyLessThanTimeWire layout)
          (historyLessThanTimeWire_ne_activeWire layout)]
        exact inside.1
      · change action input (historyActiveWire layout) = false
        rw [show action input (historyActiveWire layout) =
            (input (historyActiveWire layout) !=
              ClassicalReversibleStage.allWiresTrue
                [historyBranchWire layout, historyIdleFlag layout] input) by
              exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target
                _ _ _, historyP15IdleBoundaryConjunctionCondition layout input,
          inside.2.1]
        cases input (historyBranchWire layout) <;>
          cases input (historyIdleFlag layout) <;> rfl
      · rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) (historyEqualityFlag layout)
          (historyP15Active_ne_equalityFlag layout).symm]
        exact inside.2.2.1
      · intro wire workMember
        simp only [historyRegisterWires, List.mem_ofFn] at workMember
        rcases workMember with ⟨index, rfl⟩
        rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) ((historyEqualityWork layout).wire index)
          (historyP15EqualityWorkWire_ne_active layout index)]
        exact inside.2.2.2 _ (by
          simp [historyRegisterWires]))

private theorem historyP15IdleBoundaryActiveUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryActiveUncomputeComponent layout).target =
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyIdleFlag layout]
        (historyActiveWire layout) := rfl

private noncomputable def historyP15IdleBoundaryTimeToggleUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15IdleBoundaryCnotComponent
    (historyLessThanTimeWire layout) (historyIdleFlag layout)
    (historyP15IdleFlag_ne_lessThanTime layout).symm
    (historyP15IdleBoundaryIdleComputedPredicate layout)
    (historyP15IdleBoundaryIdleEndComputedPredicate layout)
    (by
      intro input inside
      unfold historyP15IdleBoundaryIdleComputedPredicate at inside
      unfold historyP15IdleBoundaryIdleEndComputedPredicate
      change historyP15IdleBoundaryIdleEndComputedPredicate layout
        (xorWire (historyIdleFlag layout)
          (input (historyLessThanTimeWire layout)) input)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [xorWire_apply_same, inside.1,
          xorWire_apply_other (historyIdleFlag layout)
            (historyLessThanIdleEndWire layout)
            (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm]
        cases input (historyLessThanIdleEndWire layout) <;>
          cases input (historyLessThanTimeWire layout) <;> rfl
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyActiveWire layout) (historyP15IdleFlag_ne_active layout).symm]
        exact inside.2.1
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyEqualityFlag layout)
          (historyP15IdleFlag_ne_equalityFlag layout).symm]
        exact inside.2.2.1
      · intro wire workMember
        simp only [historyRegisterWires, List.mem_ofFn] at workMember
        rcases workMember with ⟨index, rfl⟩
        rw [xorWire_apply_other (historyIdleFlag layout)
          ((historyEqualityWork layout).wire index)
          (historyP15EqualityWorkWire_ne_idleFlag layout index)]
        exact inside.2.2.2 _ (by
          simp [historyRegisterWires]))

private theorem historyP15IdleBoundaryTimeToggleUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryTimeToggleUncomputeComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorControlled
          (historyLessThanTimeWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanTime layout).symm).basisAction := rfl

private noncomputable def historyP15IdleBoundaryIdleEndToggleUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15IdleBoundaryCnotComponent
    (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
    (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm
    (historyP15IdleBoundaryIdleEndComputedPredicate layout)
    (historyP15IdleBoundaryCleanPredicate layout)
    (by
      intro input inside
      unfold historyP15IdleBoundaryIdleEndComputedPredicate at inside
      unfold historyP15IdleBoundaryCleanPredicate
      change historyP15IdleBoundaryCleanPredicate layout
        (xorWire (historyIdleFlag layout)
          (input (historyLessThanIdleEndWire layout)) input)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [xorWire_apply_same, inside.1]
        cases input (historyLessThanIdleEndWire layout) <;> rfl
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyActiveWire layout) (historyP15IdleFlag_ne_active layout).symm]
        exact inside.2.1
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyEqualityFlag layout)
          (historyP15IdleFlag_ne_equalityFlag layout).symm]
        exact inside.2.2.1
      · intro wire workMember
        simp only [historyRegisterWires, List.mem_ofFn] at workMember
        rcases workMember with ⟨index, rfl⟩
        rw [xorWire_apply_other (historyIdleFlag layout)
          ((historyEqualityWork layout).wire index)
          (historyP15EqualityWorkWire_ne_idleFlag layout index)]
        exact inside.2.2.2 _ (by
          simp [historyRegisterWires]))

private theorem historyP15IdleBoundaryIdleEndToggleUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryIdleEndToggleUncomputeComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorControlled
          (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm).basisAction := rfl

private theorem historyP15IdleBoundarySignalChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    SubspaceMapComponent.SpaceChain
      [historyP15IdleBoundaryIdleEndToggleComponent layout,
       historyP15IdleBoundaryTimeToggleComponent layout,
       historyP15IdleBoundaryActiveComputeComponent layout,
       historyP15IdleBoundaryEqualityComputeComponent layout,
       historyP15IdleBoundaryToffoliComponent layout,
       historyP15IdleBoundaryEqualityUncomputeComponent layout,
       historyP15IdleBoundaryActiveUncomputeComponent layout,
       historyP15IdleBoundaryTimeToggleUncomputeComponent layout,
       historyP15IdleBoundaryIdleEndToggleUncomputeComponent layout]
      (SubspaceMapComponent.basisSpan
        (historyP15IdleBoundaryCleanPredicate layout))
      (SubspaceMapComponent.basisSpan
        (historyP15IdleBoundaryCleanPredicate layout)) := by
  exact .cons _ [_, _, _, _, _, _, _, _] _ _ _ rfl rfl
    (.cons _ [_, _, _, _, _, _, _] _ _ _ rfl rfl
      (.cons _ [_, _, _, _, _, _] _ _ _ rfl rfl
        (.cons _ [_, _, _, _, _] _ _ _ rfl rfl
          (.cons _ [_, _, _, _] _ _ _ rfl rfl
            (.cons _ [_, _, _] _ _ _ rfl rfl
              (.cons _ [_, _] _ _ _ rfl rfl
                (.cons _ [_] _ _ _ rfl rfl
                  (.cons _ [] _ _ _ rfl rfl (.nil _)))))))))

private noncomputable def historyP15IdleBoundaryRawComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  SubspaceMapComponent.sequenceAlong (historyP15IdleBoundarySignalChain layout)

private theorem historyP15IdleBoundaryRawComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryRawComponent layout).target =
      operatorSequence
        [deterministicOperator
           (ClassicalReversibleInstruction.xorControlled
             (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
             (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm).basisAction,
         deterministicOperator
           (ClassicalReversibleInstruction.xorControlled
             (historyLessThanTimeWire layout) (historyIdleFlag layout)
             (historyP15IdleFlag_ne_lessThanTime layout).symm).basisAction,
         ClassicalReversibleStage.conjunctionDirectOperator
           [historyBranchWire layout, historyIdleFlag layout]
           (historyActiveWire layout),
         ClassicalReversibleStage.equalityToConstantDirectOperator
           (historyRegisterWires layout.order)
           (historyIdleBlockSize parameters.taylorOrder - 1)
           (historyEqualityFlag layout),
         deterministicOperator
           (ClassicalReversibleInstruction.xorDoublyControlled
             (historyActiveWire layout) (historyEqualityFlag layout)
             layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
             (historyP15Active_ne_orderBoundarySignal layout)
             (historyP15EqualityFlag_ne_orderBoundarySignal layout)).basisAction,
         ClassicalReversibleStage.equalityToConstantDirectOperator
           (historyRegisterWires layout.order)
           (historyIdleBlockSize parameters.taylorOrder - 1)
           (historyEqualityFlag layout),
         ClassicalReversibleStage.conjunctionDirectOperator
           [historyBranchWire layout, historyIdleFlag layout]
           (historyActiveWire layout),
         deterministicOperator
           (ClassicalReversibleInstruction.xorControlled
             (historyLessThanTimeWire layout) (historyIdleFlag layout)
             (historyP15IdleFlag_ne_lessThanTime layout).symm).basisAction,
         deterministicOperator
           (ClassicalReversibleInstruction.xorControlled
             (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
             (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm).basisAction] := by
  rw [show (historyP15IdleBoundaryRawComponent layout).target =
      (SubspaceMapComponent.sequenceAlong
        (historyP15IdleBoundarySignalChain layout)).target by rfl,
    SubspaceMapComponent.sequenceAlong_target]
  simp only [List.map_cons, List.map_nil]
  rw [historyP15IdleBoundaryIdleEndToggleComponent_target,
    historyP15IdleBoundaryTimeToggleComponent_target,
    historyP15IdleBoundaryActiveComputeComponent_target,
    historyP15IdleBoundaryEqualityComputeComponent_target,
    historyP15IdleBoundaryToffoliComponent_target,
    historyP15IdleBoundaryEqualityUncomputeComponent_target,
    historyP15IdleBoundaryActiveUncomputeComponent_target,
    historyP15IdleBoundaryTimeToggleUncomputeComponent_target,
    historyP15IdleBoundaryIdleEndToggleUncomputeComponent_target]

private def historyP15IdleBoundarySourceAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  let idleEnd := xorWire (historyIdleFlag layout)
    (input (historyLessThanIdleEndWire layout)) input
  let idle := xorWire (historyIdleFlag layout)
    (idleEnd (historyLessThanTimeWire layout)) idleEnd
  let active := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyIdleFlag layout]
    (historyActiveWire layout) idle
  let equality := ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.order)
    (historyIdleBlockSize parameters.taylorOrder - 1)
    (historyEqualityFlag layout) active
  let used := xorWire layout.orderBoundarySignal
    (equality (historyActiveWire layout) && equality (historyEqualityFlag layout))
    equality
  let unequality := ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.order)
    (historyIdleBlockSize parameters.taylorOrder - 1)
    (historyEqualityFlag layout) used
  let unactive := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyIdleFlag layout]
    (historyActiveWire layout) unequality
  let untime := xorWire (historyIdleFlag layout)
    (unactive (historyLessThanTimeWire layout)) unactive
  xorWire (historyIdleFlag layout)
    (untime (historyLessThanIdleEndWire layout)) untime

private theorem historyP15IdleBoundaryRawTarget_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    applyOperator (historyP15IdleBoundaryRawComponent layout).target
        (basisKet input) =
      basisKet (historyP15IdleBoundarySourceAction layout input) := by
  rw [historyP15IdleBoundaryRawComponent_target,
    ClassicalReversibleStage.conjunctionDirectOperator,
    ClassicalReversibleStage.equalityToConstantDirectOperator]
  change applyOperator
      (operatorSequence
        ([((ClassicalReversibleInstruction.xorControlled
            (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
            (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm).basisAction),
          ((ClassicalReversibleInstruction.xorControlled
            (historyLessThanTimeWire layout) (historyIdleFlag layout)
            (historyP15IdleFlag_ne_lessThanTime layout).symm).basisAction),
          ClassicalReversibleStage.conjunctionDirectBasisAction
            [historyBranchWire layout, historyIdleFlag layout]
            (historyActiveWire layout),
          ClassicalReversibleStage.equalityToConstantDirectBasisAction
            (historyRegisterWires layout.order)
            (historyIdleBlockSize parameters.taylorOrder - 1)
            (historyEqualityFlag layout),
          (ClassicalReversibleInstruction.xorDoublyControlled
            (historyActiveWire layout) (historyEqualityFlag layout)
            layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
            (historyP15Active_ne_orderBoundarySignal layout)
            (historyP15EqualityFlag_ne_orderBoundarySignal layout)).basisAction,
          ClassicalReversibleStage.equalityToConstantDirectBasisAction
            (historyRegisterWires layout.order)
            (historyIdleBlockSize parameters.taylorOrder - 1)
            (historyEqualityFlag layout),
          ClassicalReversibleStage.conjunctionDirectBasisAction
            [historyBranchWire layout, historyIdleFlag layout]
            (historyActiveWire layout),
          (ClassicalReversibleInstruction.xorControlled
            (historyLessThanTimeWire layout) (historyIdleFlag layout)
            (historyP15IdleFlag_ne_lessThanTime layout).symm).basisAction,
          (ClassicalReversibleInstruction.xorControlled
            (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
            (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm).basisAction].map
          deterministicOperator))
      (basisKet input) =
    basisKet (historyP15IdleBoundarySourceAction layout input)
  rw [operatorSequence_deterministicOperator,
    applyOperator_deterministicOperator_basisKet]
  simp only [List.foldl]
  rfl

private theorem historyP15OrderWire_ne_active
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (orderIndex : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire orderIndex ≠ historyActiveWire layout := by
  have workspaceMember := historyActiveWire_mem_workspace layout
  rcases List.mem_ofFn.mp workspaceMember with ⟨workspaceIndex, workspaceEqual⟩
  intro equal
  exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
    (equal.trans workspaceEqual.symm)

private theorem historyP15IdleBoundaryOrderEqualsLast_invariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (excluded : Fin qubits)
    (excluded_ne_order : ∀ index, excluded ≠ layout.order.wire index)
    (first second : QubitBasis qubits)
    (same : agreesExcept excluded first second) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) first =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) second := by
  apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
  intro wire wireMember
  simp only [historyRegisterWires, List.mem_ofFn] at wireMember
  rcases wireMember with ⟨orderIndex, rfl⟩
  exact same (layout.order.wire orderIndex)
    (excluded_ne_order orderIndex).symm

private theorem historyP15IdleBoundaryOrderEqualsLast_idleInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyIdleFlag layout) first second) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) first =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) second :=
  historyP15IdleBoundaryOrderEqualsLast_invariant layout (historyIdleFlag layout)
    (fun index => (historyP15OrderWire_ne_idleFlag layout index).symm)
    first second same

private theorem historyP15IdleBoundaryOrderEqualsLast_activeInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyActiveWire layout) first second) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) first =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) second :=
  historyP15IdleBoundaryOrderEqualsLast_invariant layout (historyActiveWire layout)
    (fun index => (historyP15OrderWire_ne_active layout index).symm)
    first second same

private theorem historyP15IdleBoundaryOrderEqualsLast_equalityFlagInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyEqualityFlag layout) first second) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) first =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order)
        (historyIdleBlockSize parameters.taylorOrder - 1) second :=
  historyP15IdleBoundaryOrderEqualsLast_invariant layout (historyEqualityFlag layout)
    (fun index => (historyP15OrderWire_ne_equalityFlag layout index).symm)
    first second same

private theorem historyP15IdleBoundarySourceAction_eq_direct
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (clean : historyP15IdleBoundaryCleanPredicate layout input)
    (stable : historyTaylorPostGeneratorStablePredicate layout input) :
    historyP15IdleBoundarySourceAction layout input =
      historyTaylorIdleBoundaryBasisAction layout input := by
  unfold historyP15IdleBoundaryCleanPredicate at clean
  unfold historyTaylorPostGeneratorStablePredicate at stable
  let idleEndValue := input (historyLessThanIdleEndWire layout)
  let timeValue := input (historyLessThanTimeWire layout)
  let idleValue := idleEndValue != timeValue
  let lastValue := ClassicalReversibleStage.littleEndianRegisterEqualsNat
    (historyRegisterWires layout.order)
    (historyIdleBlockSize parameters.taylorOrder - 1) input
  let activeValue := input (historyBranchWire layout) && idleValue
  let first := xorWire (historyIdleFlag layout) idleEndValue input
  let second := xorWire (historyIdleFlag layout)
    (first (historyLessThanTimeWire layout)) first
  let active := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyIdleFlag layout]
    (historyActiveWire layout) second
  let equality := ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.order)
    (historyIdleBlockSize parameters.taylorOrder - 1)
    (historyEqualityFlag layout) active
  let used := xorWire layout.orderBoundarySignal
    (equality (historyActiveWire layout) && equality (historyEqualityFlag layout))
    equality
  let unequality := ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.order)
    (historyIdleBlockSize parameters.taylorOrder - 1)
    (historyEqualityFlag layout) used
  let unactive := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyIdleFlag layout]
    (historyActiveWire layout) unequality
  let untime := xorWire (historyIdleFlag layout)
    (unactive (historyLessThanTimeWire layout)) unactive
  let final := xorWire (historyIdleFlag layout)
    (untime (historyLessThanIdleEndWire layout)) untime
  have source_eq : historyP15IdleBoundarySourceAction layout input = final := by
    rfl
  rw [source_eq]
  unfold historyTaylorIdleBoundaryBasisAction historyTaylorIdleBoundaryCondition
    historyTaylorIdleIntervalCondition
  rw [← stable.2.2.1, ← stable.2.1]
  change final = xorWire layout.orderBoundarySignal
    (activeValue && lastValue) input
  have first_eq : first = xorWire (historyIdleFlag layout) idleEndValue input := rfl
  have first_agrees : agreesExcept (historyIdleFlag layout) first input := by
    intro wire different
    rw [first_eq]
    exact xorWire_apply_other (historyIdleFlag layout) wire different _ input
  have first_idle : first (historyIdleFlag layout) = idleEndValue := by
    rw [first_eq, xorWire_apply_same, clean.1]
    cases idleEndValue <;> rfl
  have first_end : first (historyLessThanIdleEndWire layout) = idleEndValue := by
    rw [first_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyLessThanIdleEndWire layout)
      (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm]
  have first_time : first (historyLessThanTimeWire layout) = timeValue := by
    rw [first_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyLessThanTimeWire layout)
      (historyP15IdleFlag_ne_lessThanTime layout).symm]
  have first_branch : first (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    rw [first_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyBranchWire layout) (historyP15IdleFlag_ne_branch layout).symm]
  have first_active : first (historyActiveWire layout) = false := by
    rw [first_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyActiveWire layout) (historyP15IdleFlag_ne_active layout).symm]
    exact clean.2.1
  have first_flag : first (historyEqualityFlag layout) = false := by
    rw [first_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyEqualityFlag layout)
      (historyP15IdleFlag_ne_equalityFlag layout).symm]
    exact clean.2.2.1
  have first_last : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1) first = lastValue := by
    calc
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1) first =
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order)
            (historyIdleBlockSize parameters.taylorOrder - 1) input :=
        historyP15IdleBoundaryOrderEqualsLast_idleInvariant layout first input
          first_agrees
      _ = lastValue := rfl
  have second_eq : second = xorWire (historyIdleFlag layout) timeValue first := by
    dsimp [second]
    rw [first_time]
  have second_agrees : agreesExcept (historyIdleFlag layout) second first := by
    intro wire different
    rw [second_eq]
    exact xorWire_apply_other (historyIdleFlag layout) wire different _ first
  have second_idle : second (historyIdleFlag layout) = idleValue := by
    rw [second_eq, xorWire_apply_same, first_idle]
  have second_end : second (historyLessThanIdleEndWire layout) = idleEndValue := by
    rw [second_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyLessThanIdleEndWire layout)
      (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm, first_end]
  have second_time : second (historyLessThanTimeWire layout) = timeValue := by
    rw [second_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyLessThanTimeWire layout)
      (historyP15IdleFlag_ne_lessThanTime layout).symm, first_time]
  have second_branch : second (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    rw [second_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyBranchWire layout) (historyP15IdleFlag_ne_branch layout).symm,
      first_branch]
  have second_active : second (historyActiveWire layout) = false := by
    rw [second_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyActiveWire layout) (historyP15IdleFlag_ne_active layout).symm,
      first_active]
  have second_flag : second (historyEqualityFlag layout) = false := by
    rw [second_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyEqualityFlag layout)
      (historyP15IdleFlag_ne_equalityFlag layout).symm, first_flag]
  have second_last : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1) second = lastValue := by
    calc
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1) second =
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order)
            (historyIdleBlockSize parameters.taylorOrder - 1) first :=
        historyP15IdleBoundaryOrderEqualsLast_idleInvariant layout second first
          second_agrees
      _ = lastValue := first_last
  have active_agrees : agreesExcept (historyActiveWire layout) active second := by
    intro wire different
    exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) wire different second
  have active_idle : active (historyIdleFlag layout) = idleValue := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) second (historyIdleFlag layout) = idleValue
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) (historyIdleFlag layout)
      (historyP15IdleFlag_ne_active layout), second_idle]
  have active_end : active (historyLessThanIdleEndWire layout) = idleEndValue := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) second (historyLessThanIdleEndWire layout) =
        idleEndValue
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) (historyLessThanIdleEndWire layout)
      (historyLessThanIdleEndWire_ne_activeWire layout), second_end]
  have active_time : active (historyLessThanTimeWire layout) = timeValue := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) second (historyLessThanTimeWire layout) = timeValue
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_ne_activeWire layout), second_time]
  have active_branch : active (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) second (historyBranchWire layout) =
        input (historyBranchWire layout)
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) (historyBranchWire layout)
      (historyBranchWire_ne_activeWire layout), second_branch]
  have active_flag : active (historyEqualityFlag layout) = false := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) second (historyEqualityFlag layout) = false
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) (historyEqualityFlag layout)
      (historyP15Active_ne_equalityFlag layout).symm, second_flag]
  have active_value : active (historyActiveWire layout) = activeValue := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) second (historyActiveWire layout) = activeValue
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target,
      second_active, historyP15IdleBoundaryConjunctionCondition layout second,
      second_branch, second_idle]
    dsimp [activeValue]
    cases input (historyBranchWire layout) <;> cases idleValue <;> rfl
  have active_last : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1) active = lastValue := by
    calc
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1) active =
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order)
            (historyIdleBlockSize parameters.taylorOrder - 1) second :=
        historyP15IdleBoundaryOrderEqualsLast_activeInvariant layout active second
          active_agrees
      _ = lastValue := second_last
  have equality_agrees : agreesExcept (historyEqualityFlag layout)
      equality active := by
    intro wire different
    exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) wire different active
  have equality_idle : equality (historyIdleFlag layout) = idleValue := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) active (historyIdleFlag layout) = idleValue
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) (historyIdleFlag layout)
      (historyP15IdleFlag_ne_equalityFlag layout), active_idle]
  have equality_end : equality (historyLessThanIdleEndWire layout) = idleEndValue := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) active (historyLessThanIdleEndWire layout) =
        idleEndValue
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) (historyLessThanIdleEndWire layout)
      (historyP15LessThanIdleEnd_ne_equalityFlag layout), active_end]
  have equality_time : equality (historyLessThanTimeWire layout) = timeValue := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) active (historyLessThanTimeWire layout) =
        timeValue
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) (historyLessThanTimeWire layout)
      (historyP15LessThanTime_ne_equalityFlag layout), active_time]
  have equality_branch : equality (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) active (historyBranchWire layout) =
        input (historyBranchWire layout)
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) (historyBranchWire layout)
      (historyP15Branch_ne_equalityFlag layout), active_branch]
  have equality_active : equality (historyActiveWire layout) = activeValue := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) active (historyActiveWire layout) = activeValue
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) (historyActiveWire layout)
      (historyP15Active_ne_equalityFlag layout), active_value]
  have equality_flag : equality (historyEqualityFlag layout) = lastValue := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) active (historyEqualityFlag layout) = lastValue
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
      active_flag, active_last]
    cases lastValue <;> rfl
  have used_agrees : agreesExcept layout.orderBoundarySignal used equality := by
    intro wire different
    exact xorWire_apply_other layout.orderBoundarySignal wire different _ equality
  have used_control :
      (equality (historyActiveWire layout) && equality (historyEqualityFlag layout)) =
        (activeValue && lastValue) := by
    rw [equality_active, equality_flag]
  have used_idle : used (historyIdleFlag layout) = idleValue := by
    change xorWire layout.orderBoundarySignal
      (equality (historyActiveWire layout) && equality (historyEqualityFlag layout))
      equality (historyIdleFlag layout) = idleValue
    rw [xorWire_apply_other layout.orderBoundarySignal (historyIdleFlag layout)
      (historyP15IdleFlag_ne_orderBoundarySignal layout), equality_idle]
  have used_end : used (historyLessThanIdleEndWire layout) = idleEndValue := by
    change xorWire layout.orderBoundarySignal
      (equality (historyActiveWire layout) && equality (historyEqualityFlag layout))
      equality (historyLessThanIdleEndWire layout) = idleEndValue
    rw [xorWire_apply_other layout.orderBoundarySignal
      (historyLessThanIdleEndWire layout)
      (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
        (historyLessThanIdleEndWire_mem_workspace layout)), equality_end]
  have used_time : used (historyLessThanTimeWire layout) = timeValue := by
    change xorWire layout.orderBoundarySignal
      (equality (historyActiveWire layout) && equality (historyEqualityFlag layout))
      equality (historyLessThanTimeWire layout) = timeValue
    rw [xorWire_apply_other layout.orderBoundarySignal
      (historyLessThanTimeWire layout)
      (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
        (historyLessThanTimeWire_mem_workspace layout)), equality_time]
  have used_branch : used (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    change xorWire layout.orderBoundarySignal
      (equality (historyActiveWire layout) && equality (historyEqualityFlag layout))
      equality (historyBranchWire layout) = input (historyBranchWire layout)
    rw [xorWire_apply_other layout.orderBoundarySignal (historyBranchWire layout)
      (historyP15OrderBoundaryWorkspaceWire_ne_signal layout _
        (historyBranchWire_mem_workspace layout)), equality_branch]
  have used_active : used (historyActiveWire layout) = activeValue := by
    change xorWire layout.orderBoundarySignal
      (equality (historyActiveWire layout) && equality (historyEqualityFlag layout))
      equality (historyActiveWire layout) = activeValue
    rw [xorWire_apply_other layout.orderBoundarySignal (historyActiveWire layout)
      (historyP15Active_ne_orderBoundarySignal layout), equality_active]
  have used_flag : used (historyEqualityFlag layout) = lastValue := by
    change xorWire layout.orderBoundarySignal
      (equality (historyActiveWire layout) && equality (historyEqualityFlag layout))
      equality (historyEqualityFlag layout) = lastValue
    rw [xorWire_apply_other layout.orderBoundarySignal (historyEqualityFlag layout)
      (historyP15EqualityFlag_ne_orderBoundarySignal layout), equality_flag]
  have used_last : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1) used = lastValue := by
    calc
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1) used =
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order)
            (historyIdleBlockSize parameters.taylorOrder - 1) equality :=
        historyP15IdleBoundaryOrderEqualsLast_signalInvariant layout used equality
          used_agrees
      _ = lastValue := by
        exact historyP15IdleBoundaryOrderEqualsLast_equalityFlagInvariant
          layout equality active equality_agrees |>.trans active_last
  have unequality_agrees : agreesExcept (historyEqualityFlag layout)
      unequality used := by
    intro wire different
    exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) wire different used
  have unequality_idle : unequality (historyIdleFlag layout) = idleValue := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) used (historyIdleFlag layout) = idleValue
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) (historyIdleFlag layout)
      (historyP15IdleFlag_ne_equalityFlag layout), used_idle]
  have unequality_end : unequality (historyLessThanIdleEndWire layout) =
      idleEndValue := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) used (historyLessThanIdleEndWire layout) =
        idleEndValue
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) (historyLessThanIdleEndWire layout)
      (historyP15LessThanIdleEnd_ne_equalityFlag layout), used_end]
  have unequality_time : unequality (historyLessThanTimeWire layout) = timeValue := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) used (historyLessThanTimeWire layout) = timeValue
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) (historyLessThanTimeWire layout)
      (historyP15LessThanTime_ne_equalityFlag layout), used_time]
  have unequality_branch : unequality (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) used (historyBranchWire layout) =
        input (historyBranchWire layout)
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) (historyBranchWire layout)
      (historyP15Branch_ne_equalityFlag layout), used_branch]
  have unequality_active : unequality (historyActiveWire layout) = activeValue := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) used (historyActiveWire layout) = activeValue
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) (historyActiveWire layout)
      (historyP15Active_ne_equalityFlag layout), used_active]
  have unequality_flag : unequality (historyEqualityFlag layout) = false := by
    change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) used (historyEqualityFlag layout) = false
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
      used_flag, used_last]
    cases lastValue <;> rfl
  have unactive_agrees : agreesExcept (historyActiveWire layout)
      unactive unequality := by
    intro wire different
    exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) wire different unequality
  have unactive_idle : unactive (historyIdleFlag layout) = idleValue := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) unequality (historyIdleFlag layout) = idleValue
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) (historyIdleFlag layout)
      (historyP15IdleFlag_ne_active layout), unequality_idle]
  have unactive_end : unactive (historyLessThanIdleEndWire layout) = idleEndValue := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) unequality (historyLessThanIdleEndWire layout) =
        idleEndValue
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) (historyLessThanIdleEndWire layout)
      (historyLessThanIdleEndWire_ne_activeWire layout), unequality_end]
  have unactive_time : unactive (historyLessThanTimeWire layout) = timeValue := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) unequality (historyLessThanTimeWire layout) = timeValue
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_ne_activeWire layout), unequality_time]
  have unactive_branch : unactive (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) unequality (historyBranchWire layout) =
        input (historyBranchWire layout)
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) (historyBranchWire layout)
      (historyBranchWire_ne_activeWire layout), unequality_branch]
  have unactive_flag : unactive (historyEqualityFlag layout) = false := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) unequality (historyEqualityFlag layout) = false
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) (historyEqualityFlag layout)
      (historyP15Active_ne_equalityFlag layout).symm, unequality_flag]
  have unactive_active : unactive (historyActiveWire layout) = false := by
    change ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) unequality (historyActiveWire layout) = false
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target,
      unequality_active,
      historyP15IdleBoundaryConjunctionCondition layout unequality,
      unequality_branch, unequality_idle]
    dsimp [activeValue]
    cases input (historyBranchWire layout) <;> cases idleValue <;> rfl
  have untime_eq : untime = xorWire (historyIdleFlag layout) timeValue unactive := by
    dsimp [untime]
    rw [unactive_time]
  have untime_agrees : agreesExcept (historyIdleFlag layout) untime unactive := by
    intro wire different
    rw [untime_eq]
    exact xorWire_apply_other (historyIdleFlag layout) wire different _ unactive
  have untime_idle : untime (historyIdleFlag layout) = idleEndValue := by
    rw [untime_eq, xorWire_apply_same, unactive_idle]
    dsimp [idleValue]
    cases idleEndValue <;> cases timeValue <;> rfl
  have untime_end : untime (historyLessThanIdleEndWire layout) = idleEndValue := by
    rw [untime_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyLessThanIdleEndWire layout)
      (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm, unactive_end]
  have untime_active : untime (historyActiveWire layout) = false := by
    rw [untime_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyActiveWire layout) (historyP15IdleFlag_ne_active layout).symm,
      unactive_active]
  have untime_flag : untime (historyEqualityFlag layout) = false := by
    rw [untime_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyEqualityFlag layout)
      (historyP15IdleFlag_ne_equalityFlag layout).symm, unactive_flag]
  have final_eq : final = xorWire (historyIdleFlag layout) idleEndValue untime := by
    dsimp [final]
    rw [untime_end]
  have final_idle : final (historyIdleFlag layout) = false := by
    rw [final_eq, xorWire_apply_same, untime_idle]
    cases idleEndValue <;> rfl
  have final_active : final (historyActiveWire layout) = false := by
    rw [final_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyActiveWire layout) (historyP15IdleFlag_ne_active layout).symm,
      untime_active]
  have final_flag : final (historyEqualityFlag layout) = false := by
    rw [final_eq, xorWire_apply_other (historyIdleFlag layout)
      (historyEqualityFlag layout)
      (historyP15IdleFlag_ne_equalityFlag layout).symm, untime_flag]
  have final_agrees : agreesExcept layout.orderBoundarySignal final input := by
    intro wire different
    by_cases isIdle : wire = historyIdleFlag layout
    · subst wire
      exact final_idle.trans clean.1.symm
    by_cases isActive : wire = historyActiveWire layout
    · subst wire
      exact final_active.trans clean.2.1.symm
    by_cases isEquality : wire = historyEqualityFlag layout
    · subst wire
      exact final_flag.trans clean.2.2.1.symm
    calc
      final wire = untime wire := by
        rw [final_eq, xorWire_apply_other (historyIdleFlag layout) wire isIdle]
      _ = unactive wire := by
        rw [untime_eq, xorWire_apply_other (historyIdleFlag layout) wire isIdle]
      _ = unequality wire := by
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) wire isActive unequality
      _ = used wire := by
        exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) wire isEquality used
      _ = equality wire := by
        change xorWire layout.orderBoundarySignal
          (equality (historyActiveWire layout) && equality (historyEqualityFlag layout))
          equality wire = _
        rw [xorWire_apply_other layout.orderBoundarySignal wire different]
      _ = active wire := by
        exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) wire isEquality active
      _ = second wire := by
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) wire isActive second
      _ = first wire := by
        rw [second_eq, xorWire_apply_other (historyIdleFlag layout) wire isIdle]
      _ = input wire := by
        rw [first_eq, xorWire_apply_other (historyIdleFlag layout) wire isIdle]
  have active_signal : active layout.orderBoundarySignal =
      input layout.orderBoundarySignal := by
    calc
      active layout.orderBoundarySignal = second layout.orderBoundarySignal :=
        active_agrees layout.orderBoundarySignal
          (historyP15Active_ne_orderBoundarySignal layout).symm
      _ = first layout.orderBoundarySignal :=
        second_agrees layout.orderBoundarySignal
          (historyP15IdleFlag_ne_orderBoundarySignal layout).symm
      _ = input layout.orderBoundarySignal :=
        first_agrees layout.orderBoundarySignal
          (historyP15IdleFlag_ne_orderBoundarySignal layout).symm
  have equality_signal : equality layout.orderBoundarySignal =
      active layout.orderBoundarySignal := by
    exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout) layout.orderBoundarySignal
      (historyP15EqualityFlag_ne_orderBoundarySignal layout).symm active
  have final_signal : final layout.orderBoundarySignal =
      xorWire layout.orderBoundarySignal (activeValue && lastValue) input
        layout.orderBoundarySignal := by
    calc
      final layout.orderBoundarySignal = untime layout.orderBoundarySignal := by
        rw [final_eq, xorWire_apply_other (historyIdleFlag layout)
          layout.orderBoundarySignal
          (historyP15IdleFlag_ne_orderBoundarySignal layout).symm]
      _ = unactive layout.orderBoundarySignal := by
        rw [untime_eq, xorWire_apply_other (historyIdleFlag layout)
          layout.orderBoundarySignal
          (historyP15IdleFlag_ne_orderBoundarySignal layout).symm]
      _ = unequality layout.orderBoundarySignal := by
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyIdleFlag layout]
          (historyActiveWire layout) layout.orderBoundarySignal
          (historyP15Active_ne_orderBoundarySignal layout).symm unequality
      _ = used layout.orderBoundarySignal := by
        exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order)
          (historyIdleBlockSize parameters.taylorOrder - 1)
          (historyEqualityFlag layout) layout.orderBoundarySignal
          (historyP15EqualityFlag_ne_orderBoundarySignal layout).symm used
      _ = xorWire layout.orderBoundarySignal
          (equality (historyActiveWire layout) && equality (historyEqualityFlag layout))
          equality layout.orderBoundarySignal := rfl
      _ = xorWire layout.orderBoundarySignal (activeValue && lastValue) input
          layout.orderBoundarySignal := by
        rw [used_control]
        have signalValue : equality layout.orderBoundarySignal =
            input layout.orderBoundarySignal :=
          equality_signal.trans active_signal
        simpa only [xorWire_apply_same] using
          congrArg (fun bit => bit != (activeValue && lastValue)) signalValue
  funext wire
  by_cases isSignal : wire = layout.orderBoundarySignal
  · subst wire
    exact final_signal
  rw [xorWire_apply_other layout.orderBoundarySignal wire isSignal]
  exact final_agrees wire isSignal

/-- The genuine nine post-Q10 source stages for the idle-boundary signal,
restricted to the stable boundary that supplies their clean temporary wires.
The target is the existing mathematical idle-boundary action; no whole-space
circuit equality is asserted. -/
noncomputable def historyP15IdleBoundaryComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let raw := historyP15IdleBoundaryRawComponent layout
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    raw.circuit (historyTaylorIdleBoundaryOperator layout)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (by
      intro input inside
      have clean := historyP15PostQ10StablePredicate_implies_idleBoundaryClean
        layout widths input inside
      calc
        applyOperator
            (Circuit.denote (historyP15PostGate (qubits := qubits)) raw.circuit)
            (basisKet input) =
          applyOperator raw.target (basisKet input) :=
            raw.correct _
              (SubspaceMapComponent.basisKet_mem_basisSpan clean)
        _ = basisKet (historyP15IdleBoundarySourceAction layout input) :=
          historyP15IdleBoundaryRawTarget_basisKet layout input
        _ = basisKet (historyTaylorIdleBoundaryBasisAction layout input) := by
          rw [historyP15IdleBoundarySourceAction_eq_direct layout input clean
            inside.2]
        _ = applyOperator (historyTaylorIdleBoundaryOperator layout)
            (basisKet input) := by
          rw [historyTaylorIdleBoundaryOperator,
            applyOperator_deterministicOperator_basisKet])
    (by
      intro input inside
      rw [historyTaylorIdleBoundaryOperator,
        applyOperator_deterministicOperator_basisKet]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      constructor
      · simpa [historyTaylorIdleBoundaryBasisAction] using
          historyP15PostQ10OutputPredicate_xorPostSignal widths
            layout.orderBoundarySignal (by simp)
            (historyTaylorIdleBoundaryCondition layout input) input inside.1
      · exact historyTaylorIdleBoundaryBasisAction_maps_stable
          layout input inside.2)

@[simp] theorem historyP15IdleBoundaryComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15IdleBoundaryComponent layout widths).inputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) ∧
      (historyP15IdleBoundaryComponent layout widths).outputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) := by
  constructor <;> rfl

/-- Literal source-order circuit stages for the frozen idle-boundary word:
idle-end CNOT, time CNOT, active conjunction, equality, Toffoli, and their
four inverse computations. -/
noncomputable def historyP15IdleBoundarySourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    List (Circuit (PrimitiveGate qubits)) :=
  [(historyP15IdleBoundaryIdleEndToggleComponent layout).circuit,
   (historyP15IdleBoundaryTimeToggleComponent layout).circuit,
   (historyP15IdleBoundaryActiveComputeComponent layout).circuit,
   (historyP15IdleBoundaryEqualityComputeComponent layout).circuit,
   (historyP15IdleBoundaryToffoliComponent layout).circuit,
   (historyP15IdleBoundaryEqualityUncomputeComponent layout).circuit,
   (historyP15IdleBoundaryActiveUncomputeComponent layout).circuit,
   (historyP15IdleBoundaryTimeToggleUncomputeComponent layout).circuit,
   (historyP15IdleBoundaryIdleEndToggleUncomputeComponent layout).circuit]

noncomputable def historyP15IdleBoundarySourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence (historyP15IdleBoundarySourceStages layout)

private theorem historyP15IdleBoundaryRawComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryRawComponent layout).circuit =
      Circuit.sequence
        [(historyP15IdleBoundaryIdleEndToggleComponent layout).circuit,
         (historyP15IdleBoundaryTimeToggleComponent layout).circuit,
         (historyP15IdleBoundaryActiveComputeComponent layout).circuit,
         (historyP15IdleBoundaryEqualityComputeComponent layout).circuit,
         (historyP15IdleBoundaryToffoliComponent layout).circuit,
         (historyP15IdleBoundaryEqualityUncomputeComponent layout).circuit,
         (historyP15IdleBoundaryActiveUncomputeComponent layout).circuit,
         (historyP15IdleBoundaryTimeToggleUncomputeComponent layout).circuit,
         (historyP15IdleBoundaryIdleEndToggleUncomputeComponent layout).circuit] := rfl

@[simp] theorem historyP15IdleBoundaryComponent_circuit_eq_raw
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15IdleBoundaryComponent layout widths).circuit =
      (historyP15IdleBoundaryRawComponent layout).circuit := rfl

/-- The actual public circuit has exactly the primitive-gate flattening of
the literal nine-stage source word, in source order. -/
theorem historyP15IdleBoundaryComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15IdleBoundaryComponent layout widths).circuit.flatten =
      (historyP15IdleBoundarySourceCircuit layout).flatten := by
  rw [historyP15IdleBoundaryComponent_circuit_eq_raw,
    historyP15IdleBoundaryRawComponent_circuit]
  simp [historyP15IdleBoundarySourceCircuit,
    historyP15IdleBoundarySourceStages, Circuit.sequence,
    Circuit.flatten]

/-! ### Controlled Taylor-degree increment

The source word has three stages: materialize the branch-and-idle-end
predicate in `historyActiveWire`, run the frozen masked-constant/Cuccaro
increment, and apply the same conjunction again.  The source-level
`HistoryTaylorDegreeIncrementEvidence` record lives in the monolithic P15
file, so the small physical facts needed by the public arithmetic component
are reconstructed directly from the frozen layout here.
-/

private theorem historyP15DegreeIncrementAddend_wire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderTailWidth parameters + 1)) :
    (historyOrderIncrementAddendRegister layout).wire index ∈
      historyRegisterWires layout.workspace := by
  unfold historyOrderIncrementAddendRegister
  exact historyP15OrderBoundaryMask_wire_mem_workspace layout _

private theorem historyP15DegreeIncrementCarry_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyOrderIncrementCarry layout ∈ historyRegisterWires layout.workspace := by
  unfold historyOrderIncrementCarry
  apply historyWorkspaceSlice_wire_mem

private theorem historyP15DegreeIncrementAddend_not_mem_stableFlags
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderTailWidth parameters + 1)) :
    (historyOrderIncrementAddendRegister layout).wire index ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] := by
  unfold historyOrderIncrementAddendRegister
  exact historyP15OrderBoundaryMask_not_mem_stableFlags layout _

private theorem historyP15DegreeIncrementCarry_not_mem_stableFlags
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyOrderIncrementCarry layout ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] := by
  have notLive : historyOrderIncrementCarry layout ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
    unfold historyOrderIncrementCarry
    apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
    have carryFitsStructural :
        5 + 2 * historyClockWidth parameters.timeSteps parameters.taylorOrder
          parameters.idlingSteps + historyEqualityWorkWidth parameters + 1 ≤
          historyStructuralPoolWidth parameters := by
      have orderWidthPositive : 1 ≤ historyOrderWidth parameters.taylorOrder := by
        unfold historyOrderWidth
        omega
      have maximumWidthPositive : 1 ≤ historyMaximumLabelWidth parameters :=
        orderWidthPositive.trans (Nat.le_max_right _ _)
      unfold historyStructuralPoolWidth
      omega
    exact carryFitsStructural.trans (Nat.le_max_right _ _)
  intro member
  apply notLive
  simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
    List.not_mem_nil, or_false] at member ⊢
  rcases member with first | second | third
  · exact Or.inl first
  · exact Or.inr (Or.inl second)
  · exact Or.inr (Or.inr (Or.inl third))

private theorem historyP15DegreeIncrementAddend_ne_accumulator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (addendIndex : Fin (historyOrderTailWidth parameters + 1))
    (accumulatorIndex : Fin (historyOrderTailWidth parameters + 1)) :
    (historyOrderIncrementAddendRegister layout).wire addendIndex ≠
      (historyOrderAccumulatorRegister layout).wire accumulatorIndex := by
  have member := historyP15DegreeIncrementAddend_wire_mem_workspace
    layout addendIndex
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, workspaceEqual⟩
  intro equal
  change (historyOrderIncrementAddendRegister layout).wire addendIndex =
      layout.order.wire accumulatorIndex at equal
  exact (layout.orderWire_separated accumulatorIndex).2.2.2 workspaceIndex
    (equal.symm.trans workspaceEqual.symm)

private theorem historyP15DegreeIncrementCarry_ne_addend
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderTailWidth parameters + 1)) :
    historyOrderIncrementCarry layout ≠
      (historyOrderIncrementAddendRegister layout).wire index := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp [historyOrderIncrementCarry, historyOrderIncrementAddendRegister,
    historyOrderMaskedConstantRegister] at valuesEqual
  have orderLeMaximum : historyOrderWidth parameters.taylorOrder ≤
      historyMaximumLabelWidth parameters := by
    unfold historyMaximumLabelWidth
    exact Nat.le_max_right _ _
  omega

private theorem historyP15DegreeIncrementCarry_ne_accumulator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (accumulatorIndex : Fin (historyOrderTailWidth parameters + 1)) :
    historyOrderIncrementCarry layout ≠
      (historyOrderAccumulatorRegister layout).wire accumulatorIndex := by
  have member := historyP15DegreeIncrementCarry_mem_workspace layout
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, workspaceEqual⟩
  intro equal
  change historyOrderIncrementCarry layout =
      layout.order.wire accumulatorIndex at equal
  exact (layout.orderWire_separated accumulatorIndex).2.2.2 workspaceIndex
    (equal.symm.trans workspaceEqual.symm)

private theorem historyP15DegreeIncrementActive_ne_addend
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderTailWidth parameters + 1)) :
    historyActiveWire layout ≠
      (historyOrderIncrementAddendRegister layout).wire index := by
  change historyActiveWire layout ≠
    (historyOrderMaskedConstantRegister layout).wire _
  exact historyP15Active_ne_orderBoundaryMask layout _

private theorem historyP15DegreeIncrementActive_ne_accumulator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderTailWidth parameters + 1)) :
    historyActiveWire layout ≠
      (historyOrderAccumulatorRegister layout).wire index := by
  change historyActiveWire layout ≠ layout.order.wire index
  exact (historyP15OrderWire_ne_active layout index).symm

private theorem historyP15DegreeIncrementActive_ne_carry
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyActiveWire layout ≠ historyOrderIncrementCarry layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp [historyActiveWire, historyOrderIncrementCarry] at valuesEqual
  have structuralFits : historyStructuralPoolWidth parameters ≤
      historySharedPoolWidth parameters generatorWorkWidth :=
    Nat.le_max_right _ _
  unfold historyStructuralPoolWidth historyMaximumLabelWidth at structuralFits
  omega

/-- The frozen P15 degree-increment layout, reconstructed without the
monolithic source evidence record. -/
private noncomputable def historyP15DegreeIncrementSpec
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ControlledAddConstantMod2PowSpec qubits (historyOrderTailWidth parameters) where
  addend := historyOrderIncrementAddendRegister layout
  accumulator := historyOrderAccumulatorRegister layout
  carry := historyOrderIncrementCarry layout
  addend_accumulator_disjoint :=
    historyP15DegreeIncrementAddend_ne_accumulator layout
  carry_ne_addend := historyP15DegreeIncrementCarry_ne_addend layout
  carry_ne_accumulator := historyP15DegreeIncrementCarry_ne_accumulator layout
  control := historyActiveWire layout
  constant := 1
  control_ne_addend := historyP15DegreeIncrementActive_ne_addend layout
  control_ne_accumulator :=
    historyP15DegreeIncrementActive_ne_accumulator layout
  control_ne_carry := historyP15DegreeIncrementActive_ne_carry layout

private theorem historyP15PostQ10StablePredicate_implies_degreeIncrementClean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    controlledAddConstantMod2PowCleanPredicate
      (historyP15DegreeIncrementSpec layout) input := by
  constructor
  · intro index
    change input ((historyOrderIncrementAddendRegister layout).wire index) = false
    rcases List.mem_ofFn.mp
        (historyP15DegreeIncrementAddend_wire_mem_workspace layout index) with
      ⟨workspaceIndex, equal⟩
    rw [← equal]
    have outside : layout.workspace.wire workspaceIndex ∉
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout] := by
      simpa [equal] using
        historyP15DegreeIncrementAddend_not_mem_stableFlags layout index
    exact historyP15OrderBoundaryStableWorkspaceZero layout widths input inside
      workspaceIndex outside
  · change input (historyOrderIncrementCarry layout) = false
    rcases List.mem_ofFn.mp
        (historyP15DegreeIncrementCarry_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    rw [← equal]
    have outside : layout.workspace.wire workspaceIndex ∉
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout] := by
      simpa [equal] using
        historyP15DegreeIncrementCarry_not_mem_stableFlags layout
    exact historyP15OrderBoundaryStableWorkspaceZero layout widths input inside
      workspaceIndex outside

private theorem historyP15DegreeIncrementConjunctionLayout_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ([historyBranchWire layout, historyLessThanIdleEndWire layout] ++ [] ++
      [historyActiveWire layout]).Nodup := by
  simp [historyBranchWire_ne_lessThanIdleEndWire,
    historyBranchWire_ne_activeWire,
    historyLessThanIdleEndWire_ne_activeWire]

private theorem historyP15DegreeIncrementConjunction_maps_clean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (clean : controlledAddConstantMod2PowCleanPredicate
      (historyP15DegreeIncrementSpec layout) input) :
    controlledAddConstantMod2PowCleanPredicate
      (historyP15DegreeIncrementSpec layout)
      (ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyLessThanIdleEndWire layout]
        (historyActiveWire layout) input) := by
  constructor
  · intro index
    change ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyLessThanIdleEndWire layout]
        (historyActiveWire layout) input
        ((historyOrderIncrementAddendRegister layout).wire index) = false
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyLessThanIdleEndWire layout]
      (historyActiveWire layout)
      ((historyOrderIncrementAddendRegister layout).wire index)
      (historyP15DegreeIncrementActive_ne_addend layout index).symm]
    exact clean.1 index
  · change ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyLessThanIdleEndWire layout]
        (historyActiveWire layout) input (historyOrderIncrementCarry layout) = false
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyLessThanIdleEndWire layout]
      (historyActiveWire layout) (historyOrderIncrementCarry layout)
      (historyP15DegreeIncrementActive_ne_carry layout).symm]
    exact clean.2

/-- One of the two literal source conjunction occurrences, viewed on the
common addend/carry-clean boundary needed by the intervening Cuccaro child. -/
private noncomputable def historyP15DegreeIncrementActiveToggleComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyBranchWire layout, historyLessThanIdleEndWire layout] []
    (historyActiveWire layout) (by simp)
    (historyP15DegreeIncrementConjunctionLayout_nodup layout)
    (controlledAddConstantMod2PowCleanPredicate
      (historyP15DegreeIncrementSpec layout))
    (controlledAddConstantMod2PowCleanPredicate
      (historyP15DegreeIncrementSpec layout))
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (historyP15DegreeIncrementConjunction_maps_clean layout)

private theorem historyP15DegreeIncrementActiveToggleComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15DegreeIncrementActiveToggleComponent layout).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyLessThanIdleEndWire layout] []
        (historyActiveWire layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanIdleEndWire layout] []
      (historyActiveWire layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

private noncomputable def historyP15DegreeIncrementArithmeticComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  controlledAddConstantMod2PowSubspaceMapComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (historyP15DegreeIncrementSpec layout)

private theorem historyP15DegreeIncrementArithmeticComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15DegreeIncrementArithmeticComponent layout).circuit =
      (controlledAddConstantMod2PowStage
        (historyP15DegreeIncrementSpec layout)).compile := by
  exact controlledAddConstantMod2PowExactOperatorComponent_circuit _ _

private theorem historyP15DegreeIncrementChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    SubspaceMapComponent.SpaceChain
      [historyP15DegreeIncrementActiveToggleComponent layout,
       historyP15DegreeIncrementArithmeticComponent layout,
       historyP15DegreeIncrementActiveToggleComponent layout]
      (SubspaceMapComponent.basisSpan
        (controlledAddConstantMod2PowCleanPredicate
          (historyP15DegreeIncrementSpec layout)))
      (SubspaceMapComponent.basisSpan
        (controlledAddConstantMod2PowCleanPredicate
          (historyP15DegreeIncrementSpec layout))) := by
  refine .cons _ [_, _] _ _ _ rfl rfl ?_
  refine .cons _ [_] _ _ _ rfl rfl ?_
  exact .cons _ [] _ _ _ rfl rfl (.nil _)

private noncomputable def historyP15DegreeIncrementRawComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  SubspaceMapComponent.sequenceAlong (historyP15DegreeIncrementChain layout)

private theorem historyP15DegreeIncrementRawComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15DegreeIncrementRawComponent layout).target =
      operatorSequence
        [ClassicalReversibleStage.conjunctionDirectOperator
           [historyBranchWire layout, historyLessThanIdleEndWire layout]
           (historyActiveWire layout),
         controlledAddConstantMod2PowSemanticOperator
           (historyP15DegreeIncrementSpec layout),
         ClassicalReversibleStage.conjunctionDirectOperator
           [historyBranchWire layout, historyLessThanIdleEndWire layout]
           (historyActiveWire layout)] := rfl

private theorem historyP15DegreeIncrementSpec_accumulator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15DegreeIncrementSpec layout).accumulator = layout.order := rfl

private theorem historyP15DegreeIncrementSpec_control
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15DegreeIncrementSpec layout).control = historyActiveWire layout := rfl

private theorem historyP15DegreeIncrementAccumulator_value_eq_order
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    registerValue (historyOrderAccumulatorRegister layout) input =
      registerValue layout.order input := by
  rfl

private theorem historyP15DegreeIncrementAccumulator_write_eq_order
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    writeRegisterValue (historyOrderAccumulatorRegister layout) value input =
      writeRegisterValue layout.order value input := by
  rfl

private theorem historyP15DegreeIncrementBranch_ne_accumulator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderTailWidth parameters + 1)) :
    historyBranchWire layout ≠
      (historyP15DegreeIncrementSpec layout).accumulator.wire index := by
  rw [historyP15DegreeIncrementSpec_accumulator]
  have member := historyBranchWire_mem_workspace layout
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, workspaceEqual⟩
  intro equal
  exact (layout.orderWire_separated index).2.2.2 workspaceIndex
    (equal.symm.trans workspaceEqual.symm)

private theorem historyP15DegreeIncrementIdleEnd_ne_accumulator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderTailWidth parameters + 1)) :
    historyLessThanIdleEndWire layout ≠
      (historyP15DegreeIncrementSpec layout).accumulator.wire index := by
  rw [historyP15DegreeIncrementSpec_accumulator]
  have member := historyLessThanIdleEndWire_mem_workspace layout
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, workspaceEqual⟩
  intro equal
  exact (layout.orderWire_separated index).2.2.2 workspaceIndex
    (equal.symm.trans workspaceEqual.symm)

private theorem historyP15DegreeIncrementOrderRead_after_activeXor
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Bool) (input : QubitBasis qubits) :
    layout.order.read (xorWire (historyActiveWire layout) value input) =
      layout.order.read input := by
  funext index
  unfold Register.read
  exact xorWire_apply_other (historyActiveWire layout) (layout.order.wire index)
    (historyP15OrderWire_ne_active layout index) value input

private theorem historyP15DegreeIncrementWrite_commutes_activeXor
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    writeRegisterValue layout.order value
        (xorWire (historyActiveWire layout) true input) =
      xorWire (historyActiveWire layout) true
        (writeRegisterValue layout.order value input) := by
  funext wire
  by_cases inOrder : ∃ index, layout.order.wire index = wire
  · rcases inOrder with ⟨index, rfl⟩
    rw [writeRegisterValue_apply_wire,
      xorWire_apply_other (historyActiveWire layout) (layout.order.wire index)
        (historyP15OrderWire_ne_active layout index) true,
      writeRegisterValue_apply_wire]
  · have outsideOrder : ∀ index, layout.order.wire index ≠ wire := by
      intro index equal
      exact inOrder ⟨index, equal⟩
    by_cases isActive : wire = historyActiveWire layout
    · subst wire
      rw [writeRegisterValue_apply_outside layout.order value
          (xorWire (historyActiveWire layout) true input)
          (historyActiveWire layout)
          (fun index => historyP15OrderWire_ne_active layout index),
        xorWire_apply_same, xorWire_apply_same,
        writeRegisterValue_apply_outside layout.order value input
          (historyActiveWire layout)
          (fun index => historyP15OrderWire_ne_active layout index)]
    · rw [writeRegisterValue_apply_outside layout.order value
          (xorWire (historyActiveWire layout) true input) wire outsideOrder,
        xorWire_apply_other (historyActiveWire layout) wire isActive true input,
        xorWire_apply_other (historyActiveWire layout) wire isActive true
          (writeRegisterValue layout.order value input),
        writeRegisterValue_apply_outside layout.order value input wire outsideOrder]

private def historyP15DegreeIncrementSourceAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  let computed := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyLessThanIdleEndWire layout]
    (historyActiveWire layout) input
  let incremented := controlledAddConstantMod2PowBasisAction
    (historyP15DegreeIncrementSpec layout) computed
  ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyLessThanIdleEndWire layout]
    (historyActiveWire layout) incremented

private theorem historyP15DegreeIncrementRawComponent_target_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    applyOperator (historyP15DegreeIncrementRawComponent layout).target
        (basisKet input) =
      basisKet (historyP15DegreeIncrementSourceAction layout input) := by
  rw [historyP15DegreeIncrementRawComponent_target]
  change applyOperator
      (operatorSequence
        ([ClassicalReversibleStage.conjunctionDirectBasisAction
            [historyBranchWire layout, historyLessThanIdleEndWire layout]
            (historyActiveWire layout),
          controlledAddConstantMod2PowBasisAction
            (historyP15DegreeIncrementSpec layout),
          ClassicalReversibleStage.conjunctionDirectBasisAction
            [historyBranchWire layout, historyLessThanIdleEndWire layout]
            (historyActiveWire layout)].map deterministicOperator))
      (basisKet input) =
        basisKet (historyP15DegreeIncrementSourceAction layout input)
  rw [
    operatorSequence_deterministicOperator,
    applyOperator_deterministicOperator_basisKet]
  simp only [List.foldl]
  rfl

private theorem historyP15DegreeIncrementSourceAction_eq_direct
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    historyP15DegreeIncrementSourceAction layout input =
      historyTaylorDegreeIncrementBasisAction layout input := by
  let condition := historyTaylorDegreeIncrementCondition layout input
  let computed := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyLessThanIdleEndWire layout]
    (historyActiveWire layout) input
  let incremented := controlledAddConstantMod2PowBasisAction
    (historyP15DegreeIncrementSpec layout) computed
  let final := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyLessThanIdleEndWire layout]
    (historyActiveWire layout) incremented
  change final = historyTaylorDegreeIncrementBasisAction layout input
  have stable := inside.2
  have activeClean : input (historyActiveWire layout) = false :=
    (historyP15PostQ10StablePredicate_implies_orderBoundaryClean
      layout widths input inside).2.2
  have controlsInput : ClassicalReversibleStage.allWiresTrue
      [historyBranchWire layout, historyLessThanIdleEndWire layout] input =
      condition := by
    dsimp [condition]
    simp [ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires,
      historyTaylorDegreeIncrementCondition, stable.2.2.1]
  by_cases conditionTrue : condition
  · have computed_eq : computed = xorWire (historyActiveWire layout) true input := by
      dsimp [computed]
      change xorWire (historyActiveWire layout)
        (ClassicalReversibleStage.allWiresTrue
          [historyBranchWire layout, historyLessThanIdleEndWire layout] input)
        input = _
      rw [controlsInput, conditionTrue]
    have computedActive : computed (historyActiveWire layout) = true := by
      rw [computed_eq, xorWire_apply_same, activeClean]
      simp
    have computedOrderRead : layout.order.read computed = layout.order.read input := by
      rw [computed_eq]
      exact historyP15DegreeIncrementOrderRead_after_activeXor layout true input
    have computedOrderValue : registerValue layout.order computed =
        registerValue layout.order input :=
      congrArg (qubitBasisLittleEndianIndex
        (historyOrderWidth parameters.taylorOrder)) computedOrderRead
    have computedAccumulatorValue :
        registerValue (historyOrderAccumulatorRegister layout) computed =
          registerValue (historyOrderAccumulatorRegister layout) input := by
      calc
        registerValue (historyOrderAccumulatorRegister layout) computed =
            registerValue layout.order computed :=
          historyP15DegreeIncrementAccumulator_value_eq_order layout computed
        _ = registerValue layout.order input := computedOrderValue
        _ = registerValue (historyOrderAccumulatorRegister layout) input :=
          (historyP15DegreeIncrementAccumulator_value_eq_order layout input).symm
    have incremented_eq_accumulator : incremented =
        writeRegisterValue (historyOrderAccumulatorRegister layout)
          ((registerValue (historyOrderAccumulatorRegister layout) input + 1) %
            2 ^ (historyOrderTailWidth parameters + 1)) computed := by
      dsimp [incremented]
      rw [controlledAddConstantMod2PowBasisAction,
        if_pos (by
          simpa [historyP15DegreeIncrementSpec_control] using computedActive)]
      change writeRegisterValue (historyOrderAccumulatorRegister layout)
          ((registerValue (historyOrderAccumulatorRegister layout) computed + 1) %
            2 ^ (historyOrderTailWidth parameters + 1)) computed = _
      rw [computedAccumulatorValue]
    have incremented_eq : incremented = writeRegisterValue layout.order
        ((registerValue layout.order input + 1) %
          2 ^ historyOrderWidth parameters.taylorOrder) computed := by
      calc
        incremented = writeRegisterValue (historyOrderAccumulatorRegister layout)
            ((registerValue (historyOrderAccumulatorRegister layout) input + 1) %
              2 ^ (historyOrderTailWidth parameters + 1)) computed :=
          incremented_eq_accumulator
        _ = writeRegisterValue layout.order
            ((registerValue layout.order input + 1) %
              2 ^ historyOrderWidth parameters.taylorOrder) computed := by
          simpa [historyOrderTailWidth_succ,
            historyP15DegreeIncrementAccumulator_value_eq_order] using
            historyP15DegreeIncrementAccumulator_write_eq_order layout
              ((registerValue (historyOrderAccumulatorRegister layout) input + 1) %
                2 ^ (historyOrderTailWidth parameters + 1)) computed
    have incrementedBranch : incremented (historyBranchWire layout) =
        input (historyBranchWire layout) := by
      calc
        incremented (historyBranchWire layout) =
            computed (historyBranchWire layout) := by
          dsimp [incremented]
          exact controlledAddConstantMod2PowBasisAction_apply_outside
            (historyP15DegreeIncrementSpec layout) computed
            (historyBranchWire layout)
            (historyP15DegreeIncrementBranch_ne_accumulator layout)
        _ = input (historyBranchWire layout) := by
          rw [computed_eq,
            xorWire_apply_other (historyActiveWire layout)
              (historyBranchWire layout)
              (historyBranchWire_ne_activeWire layout) true]
    have incrementedIdleEnd : incremented (historyLessThanIdleEndWire layout) =
        input (historyLessThanIdleEndWire layout) := by
      calc
        incremented (historyLessThanIdleEndWire layout) =
            computed (historyLessThanIdleEndWire layout) := by
          dsimp [incremented]
          exact controlledAddConstantMod2PowBasisAction_apply_outside
            (historyP15DegreeIncrementSpec layout) computed
            (historyLessThanIdleEndWire layout)
            (historyP15DegreeIncrementIdleEnd_ne_accumulator layout)
        _ = input (historyLessThanIdleEndWire layout) := by
          rw [computed_eq,
            xorWire_apply_other (historyActiveWire layout)
              (historyLessThanIdleEndWire layout)
              (historyLessThanIdleEndWire_ne_activeWire layout) true]
    have final_eq : final = xorWire (historyActiveWire layout) true incremented := by
      dsimp [final]
      change xorWire (historyActiveWire layout)
        (ClassicalReversibleStage.allWiresTrue
          [historyBranchWire layout, historyLessThanIdleEndWire layout]
          incremented) incremented = _
      have conditionBits : input (historyBranchWire layout) = true ∧
          historyTaylorClockLessThanIdleEndValue layout input = true := by
        have conditionValue := conditionTrue
        dsimp [condition, historyTaylorDegreeIncrementCondition] at conditionValue
        cases branchValue : input (historyBranchWire layout) <;>
          cases idleEndValue : historyTaylorClockLessThanIdleEndValue layout input <;>
          simp [branchValue, idleEndValue] at conditionValue ⊢
      have controlsIncremented : ClassicalReversibleStage.allWiresTrue
          [historyBranchWire layout, historyLessThanIdleEndWire layout]
          incremented = true := by
        simp [ClassicalReversibleStage.allWiresTrue,
          ClassicalReversibleStage.readWires, incrementedBranch,
          incrementedIdleEnd, stable.2.2.1, conditionBits.1, conditionBits.2]
      rw [controlsIncremented]
    have direct_eq : historyTaylorDegreeIncrementBasisAction layout input =
        writeRegisterValue layout.order
          ((registerValue layout.order input + 1) %
            2 ^ historyOrderWidth parameters.taylorOrder) input := by
      unfold historyTaylorDegreeIncrementBasisAction
        predicateControlledAddMod2PowBasisAction
      change (if condition then
          writeRegisterValue layout.order
            ((registerValue layout.order input + 1) %
              2 ^ historyOrderWidth parameters.taylorOrder) input
        else input) = _
      rw [if_pos conditionTrue]
    calc
      final = xorWire (historyActiveWire layout) true incremented := final_eq
      _ = xorWire (historyActiveWire layout) true
          (writeRegisterValue layout.order
            ((registerValue layout.order input + 1) %
              2 ^ historyOrderWidth parameters.taylorOrder) computed) := by
        rw [incremented_eq]
      _ = xorWire (historyActiveWire layout) true
          (writeRegisterValue layout.order
            ((registerValue layout.order input + 1) %
              2 ^ historyOrderWidth parameters.taylorOrder)
            (xorWire (historyActiveWire layout) true input)) := by
        rw [computed_eq]
      _ = xorWire (historyActiveWire layout) true
          (xorWire (historyActiveWire layout) true
            (writeRegisterValue layout.order
              ((registerValue layout.order input + 1) %
                2 ^ historyOrderWidth parameters.taylorOrder) input)) := by
        rw [historyP15DegreeIncrementWrite_commutes_activeXor]
      _ = writeRegisterValue layout.order
          ((registerValue layout.order input + 1) %
            2 ^ historyOrderWidth parameters.taylorOrder) input :=
        xorWire_involutive (historyActiveWire layout) true _
      _ = historyTaylorDegreeIncrementBasisAction layout input := direct_eq.symm
  · have conditionFalse : condition = false := by
      cases conditionValue : condition <;> simp_all
    have computed_eq : computed = input := by
      dsimp [computed]
      change xorWire (historyActiveWire layout)
        (ClassicalReversibleStage.allWiresTrue
          [historyBranchWire layout, historyLessThanIdleEndWire layout] input)
        input = input
      rw [controlsInput, conditionFalse]
      simp [xorWire]
    have incremented_eq : incremented = input := by
      dsimp [incremented]
      rw [computed_eq, controlledAddConstantMod2PowBasisAction,
        if_neg (by simpa [historyP15DegreeIncrementSpec_control] using activeClean)]
    have direct_eq : historyTaylorDegreeIncrementBasisAction layout input = input := by
      unfold historyTaylorDegreeIncrementBasisAction
        predicateControlledAddMod2PowBasisAction
      change (if condition then
          writeRegisterValue layout.order
            ((registerValue layout.order input + 1) %
              2 ^ historyOrderWidth parameters.taylorOrder) input
        else input) = input
      simp [conditionFalse]
    dsimp [final]
    rw [incremented_eq]
    change xorWire (historyActiveWire layout)
      (ClassicalReversibleStage.allWiresTrue
        [historyBranchWire layout, historyLessThanIdleEndWire layout] input)
      input = _
    rw [controlsInput, conditionFalse]
    simpa [xorWire] using direct_eq.symm

private theorem historyP15OrderWire_ne_placement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (index : Fin (historyOrderTailWidth parameters + 1))
    (source : Fin (p.ancillaWidth + p.systemWidth)) :
    layout.order.wire index ≠
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := layout) widths).placement.embedding.placement source := by
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
  have dataSplit := List.nodup_append.mp selectorSplit.2.1
  have clockSplit := List.nodup_append.mp dataSplit.2.1
  have orderSplit := List.nodup_append.mp clockSplit.2.1
  have orderMember : layout.order.wire index ∈ orderWires := by
    simp only [orderWires, historyRegisterWires, List.mem_ofFn]
    exact ⟨index, rfl⟩
  intro equal
  have placedMember :
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := layout) widths).placement.embedding.placement source ∈
        List.ofFn (historyP15Q10ControlEvidence_ofFrozenLayout
          (layout := layout) widths).placement.embedding.placement := by
    exact List.mem_ofFn.mpr ⟨source, rfl⟩
  rw [historyP15Q10Placement_sourceOrder (layout := layout) widths] at placedMember
  rcases List.mem_append.mp placedMember with initialMember | dataMember
  · rcases List.mem_append.mp initialMember with generatorMember | workMember
    · exact orderSplit.2.2 _ orderMember _
        (by simp [generatorWires, generatorMember]) equal
    · have workspaceMember :
          (historyP15Q10ControlEvidence_ofFrozenLayout
            (layout := layout) widths).placement.embedding.placement source ∈
            workspaceWires := by
        simp only [historyRegisterWires, List.mem_ofFn] at workMember
        rcases workMember with ⟨workspaceIndex, equalWork⟩
        rw [← equalWork]
        simpa [workspaceWires] using
          historyGeneratorWorkRegister_wire_mem_workspace layout workspaceIndex
      exact orderSplit.2.2 _ orderMember _
        (by simp [workspaceMember]) equal
  · exact dataSplit.2.2 _ dataMember _
      (by
        exact List.mem_append_right clockWires
          (List.mem_append_left (generatorWires ++
            (reservedWires ++ workspaceWires)) orderMember)) equal.symm

private theorem historyP15OrderWire_ne_controlledWork
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (orderIndex : Fin (historyOrderTailWidth parameters + 1))
    (workIndex : Fin 2) :
    layout.order.wire orderIndex ≠ (historyControlledWork layout).wire workIndex := by
  have member := historyControlledWork_wire_mem_workspace layout workIndex
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, workspaceEqual⟩
  exact fun equal => (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
    (equal.trans workspaceEqual.symm)

private theorem historyP15PostQ10OutputPredicate_of_agreesOutsideOrder
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input output : QubitBasis qubits)
    (inside : historyP15PostQ10OutputPredicate (layout := layout) widths input)
    (sameOutside : ∀ wire, (∀ index, wire ≠ layout.order.wire index) →
      output wire = input wire) :
    historyP15PostQ10OutputPredicate (layout := layout) widths output := by
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  unfold historyP15PostQ10OutputPredicate
    externallyControlledPlacedOutputPredicate at inside ⊢
  constructor
  · constructor
    · rw [sameOutside evidence.cleanWorkValid.work₀ (by
          intro index
          exact (historyP15OrderWire_ne_controlledWork layout index 0).symm)]
      exact inside.1.1
    · rw [sameOutside evidence.cleanWorkValid.work₁ (by
          intro index
          exact (historyP15OrderWire_ne_controlledWork layout index 1).symm)]
      exact inside.1.2
  · change ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p
      (restrictToPlacedWires evidence.placement.embedding.placement output)
    rw [show restrictToPlacedWires evidence.placement.embedding.placement output =
        restrictToPlacedWires evidence.placement.embedding.placement input by
          funext source
          unfold restrictToPlacedWires
          exact sameOutside _ (fun index =>
            (historyP15OrderWire_ne_placement widths index source).symm)]
    exact inside.2

private theorem historyP15DegreeIncrementBasisAction_apply_outside_order
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : ∀ index, wire ≠ layout.order.wire index) :
    historyTaylorDegreeIncrementBasisAction layout input wire = input wire := by
  exact predicateControlledAddMod2PowBasisAction_apply_outside
    (historyTaylorDegreeIncrementCondition layout) layout.order 1 input wire outside

private theorem historyP15PostQ10OutputPredicate_degreeIncrement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10OutputPredicate (layout := layout) widths input) :
    historyP15PostQ10OutputPredicate (layout := layout) widths
      (historyTaylorDegreeIncrementBasisAction layout input) := by
  exact historyP15PostQ10OutputPredicate_of_agreesOutsideOrder widths input
    (historyTaylorDegreeIncrementBasisAction layout input) inside
    (fun wire outside =>
      historyP15DegreeIncrementBasisAction_apply_outside_order layout input wire outside)

/-- The literal post-Q10 three-stage degree-increment group, certified only on
the stable clean boundary.  Its target is the pre-existing analytic modular
increment on `layout.order`; the final conjunction restores the active flag
and the public arithmetic component restores its Cuccaro work. -/
noncomputable def historyP15DegreeIncrementComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let raw := historyP15DegreeIncrementRawComponent layout
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    raw.circuit (historyTaylorDegreeIncrementOperator layout)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (by
      intro input inside
      have clean := historyP15PostQ10StablePredicate_implies_degreeIncrementClean
        layout widths input inside
      calc
        applyOperator
            (Circuit.denote (historyP15PostGate (qubits := qubits)) raw.circuit)
            (basisKet input) =
          applyOperator raw.target (basisKet input) :=
            raw.correct _ (SubspaceMapComponent.basisKet_mem_basisSpan clean)
        _ = basisKet (historyP15DegreeIncrementSourceAction layout input) :=
          historyP15DegreeIncrementRawComponent_target_basisKet layout input
        _ = basisKet (historyTaylorDegreeIncrementBasisAction layout input) := by
          rw [historyP15DegreeIncrementSourceAction_eq_direct layout widths input
            inside]
        _ = applyOperator (historyTaylorDegreeIncrementOperator layout)
            (basisKet input) := by
          rw [historyTaylorDegreeIncrementOperator,
            predicateControlledAddMod2PowOperator,
            historyTaylorDegreeIncrementBasisAction,
            applyOperator_deterministicOperator_basisKet])
    (by
      intro input inside
      rw [historyTaylorDegreeIncrementOperator,
        predicateControlledAddMod2PowOperator,
        applyOperator_deterministicOperator_basisKet]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      constructor
      · exact historyP15PostQ10OutputPredicate_degreeIncrement widths input
          inside.1
      · exact historyTaylorDegreeIncrementBasisAction_maps_stable
          layout input inside.2)

/-- The degree-increment component has the common clean post-Q10 stable span
as both its input and output space. -/
@[simp] theorem historyP15DegreeIncrementComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15DegreeIncrementComponent layout widths).inputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) ∧
      (historyP15DegreeIncrementComponent layout widths).outputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) := by
  constructor <;> rfl

/-- Literal source-order circuits for the P15 degree increment: active
compute, masked-constant/Cuccaro increment, and active uncompute.  These are
the primitive circuits underlying the three source stages without importing the
monolithic P15 wrapper. -/
noncomputable def historyP15DegreeIncrementSourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    List (Circuit (PrimitiveGate qubits)) :=
  [(ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanIdleEndWire layout] []
      (historyActiveWire layout)).compile,
   (controlledAddConstantMod2PowStage
      (historyP15DegreeIncrementSpec layout)).compile,
   (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanIdleEndWire layout] []
      (historyActiveWire layout)).compile]

noncomputable def historyP15DegreeIncrementSourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence (historyP15DegreeIncrementSourceStages layout)

private theorem historyP15DegreeIncrementRawComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15DegreeIncrementRawComponent layout).circuit =
      Circuit.sequence
        [(historyP15DegreeIncrementActiveToggleComponent layout).circuit,
         (historyP15DegreeIncrementArithmeticComponent layout).circuit,
         (historyP15DegreeIncrementActiveToggleComponent layout).circuit] := rfl

@[simp] theorem historyP15DegreeIncrementComponent_circuit_eq_raw
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15DegreeIncrementComponent layout widths).circuit =
      (historyP15DegreeIncrementRawComponent layout).circuit := rfl

/-- The public clean component has exactly the primitive flattening of the
literal three-stage P15 source word. -/
theorem historyP15DegreeIncrementComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15DegreeIncrementComponent layout widths).circuit.flatten =
      (historyP15DegreeIncrementSourceCircuit layout).flatten := by
  rw [historyP15DegreeIncrementComponent_circuit_eq_raw,
    historyP15DegreeIncrementRawComponent_circuit,
    historyP15DegreeIncrementActiveToggleComponent_circuit,
    historyP15DegreeIncrementArithmeticComponent_circuit]
  simp [historyP15DegreeIncrementSourceCircuit,
    historyP15DegreeIncrementSourceStages, Circuit.sequence, Circuit.flatten]

/-! ### Idle coefficient rotation

The frozen seven-stage word computes the parity of the two already-recorded
clock predicates into `historyIdleFlag`, materializes the branch-and-idle
control in `historyCoefficientControl`, performs one controlled `Ry`, and
then reverses both temporary computations.  The two nested clean-control
lemmas above deliberately allow the middle rotation to create a coherent
superposition of the coefficient signal. -/

private theorem historyP15IdleCoefficientControl_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ∈ historyRegisterWires layout.workspace := by
  unfold historyCoefficientControl
  apply historyWorkspaceSlice_wire_mem

private theorem historyP15IdleCoefficientControl_ne_branch
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ≠ historyBranchWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast := historyP15SharedPool_ge_five layout
  omega

private theorem historyP15IdleCoefficientControl_ne_lessThanTime
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ≠ historyLessThanTimeWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast := historyP15SharedPool_ge_five layout
  omega

private theorem historyP15IdleCoefficientControl_ne_lessThanIdleEnd
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ≠ historyLessThanIdleEndWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast := historyP15SharedPool_ge_five layout
  omega

private theorem historyP15IdleCoefficientControl_ne_idleFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ≠ historyIdleFlag layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  have sharedAtLeast := historyP15SharedPool_ge_five layout
  omega

private theorem historyP15IdleCoefficientIdleFlag_ne_coefficientSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ≠ layout.coefficientSignal := by
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  change layout.workspace.wire _ ≠ layout.coefficientSignal
  exact separated.2.2 _

private theorem historyP15IdleCoefficientBranch_ne_coefficientSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyBranchWire layout ≠ layout.coefficientSignal := by
  have member := historyBranchWire_mem_workspace layout
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, equal⟩
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  exact fun same => separated.2.2 workspaceIndex (equal.trans same)

private theorem historyP15IdleCoefficientLessThanTime_ne_coefficientSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyLessThanTimeWire layout ≠ layout.coefficientSignal := by
  have member := historyLessThanTimeWire_mem_workspace layout
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, equal⟩
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  exact fun same => separated.2.2 workspaceIndex (equal.trans same)

private theorem historyP15IdleCoefficientLessThanIdleEnd_ne_coefficientSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyLessThanIdleEndWire layout ≠ layout.coefficientSignal := by
  have member := historyLessThanIdleEndWire_mem_workspace layout
  rcases List.mem_ofFn.mp member with ⟨workspaceIndex, equal⟩
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  exact fun same => separated.2.2 workspaceIndex (equal.trans same)

private theorem historyP15IdleCoefficientControl_not_mem_stableFlags
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] := by
  simp [historyP15IdleCoefficientControl_ne_branch,
    historyP15IdleCoefficientControl_ne_lessThanTime,
    historyP15IdleCoefficientControl_ne_lessThanIdleEnd]

private def historyP15IdleCoefficientCleanPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyIdleFlag layout) = false ∧
    basis (historyCoefficientControl layout) = false

private def historyP15IdleCoefficientIdleEndComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyIdleFlag layout) = basis (historyLessThanIdleEndWire layout) ∧
    basis (historyCoefficientControl layout) = false

private def historyP15IdleCoefficientStoredIntervalCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  basis (historyLessThanIdleEndWire layout) !=
    basis (historyLessThanTimeWire layout)

private def historyP15IdleCoefficientIdleComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyIdleFlag layout) =
      historyP15IdleCoefficientStoredIntervalCondition layout basis ∧
    basis (historyCoefficientControl layout) = false

private def historyP15IdleCoefficientControlComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyIdleFlag layout) =
      historyP15IdleCoefficientStoredIntervalCondition layout basis ∧
    basis (historyCoefficientControl layout) =
      (basis (historyBranchWire layout) && basis (historyIdleFlag layout))

private theorem historyP15PostQ10StablePredicate_implies_idleCoefficientClean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    historyP15IdleCoefficientCleanPredicate layout input := by
  constructor
  · exact (historyP15PostQ10StablePredicate_implies_idleBoundaryClean
      layout widths input inside).1
  · rcases List.mem_ofFn.mp
        (historyP15IdleCoefficientControl_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    rw [← equal]
    exact historyP15OrderBoundaryStableWorkspaceZero layout widths input inside
      workspaceIndex (by
        simpa [equal] using
          historyP15IdleCoefficientControl_not_mem_stableFlags layout)

private noncomputable def historyP15IdleCoefficientCnotComponent
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (directMaps : ∀ input, inputPredicate input → outputPredicate
      ((ClassicalReversibleInstruction.xorControlled control target different).basisAction
        input)) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  historyP15IdleBoundaryCnotComponent control target different inputPredicate
    outputPredicate directMaps

private noncomputable def historyP15IdleCoefficientIdleEndToggleComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15IdleCoefficientCnotComponent
    (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
    (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm
    (historyP15IdleCoefficientCleanPredicate layout)
    (historyP15IdleCoefficientIdleEndComputedPredicate layout)
    (by
      intro input clean
      unfold historyP15IdleCoefficientCleanPredicate at clean
      unfold historyP15IdleCoefficientIdleEndComputedPredicate
      change historyP15IdleCoefficientIdleEndComputedPredicate layout
        (xorWire (historyIdleFlag layout)
          (input (historyLessThanIdleEndWire layout)) input)
      constructor
      · rw [xorWire_apply_same, clean.1,
          xorWire_apply_other (historyIdleFlag layout)
            (historyLessThanIdleEndWire layout)
            (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm]
        cases input (historyLessThanIdleEndWire layout) <;> rfl
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyCoefficientControl layout)
          (historyP15IdleCoefficientControl_ne_idleFlag layout)]
        exact clean.2)

private theorem historyP15IdleCoefficientIdleEndToggleComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientIdleEndToggleComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorControlled
          (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm).basisAction := rfl

private noncomputable def historyP15IdleCoefficientTimeToggleComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15IdleCoefficientCnotComponent
    (historyLessThanTimeWire layout) (historyIdleFlag layout)
    (historyP15IdleFlag_ne_lessThanTime layout).symm
    (historyP15IdleCoefficientIdleEndComputedPredicate layout)
    (historyP15IdleCoefficientIdleComputedPredicate layout)
    (by
      intro input inside
      unfold historyP15IdleCoefficientIdleEndComputedPredicate at inside
      unfold historyP15IdleCoefficientIdleComputedPredicate
      change historyP15IdleCoefficientIdleComputedPredicate layout
        (xorWire (historyIdleFlag layout)
          (input (historyLessThanTimeWire layout)) input)
      unfold historyP15IdleCoefficientIdleComputedPredicate
        historyP15IdleCoefficientStoredIntervalCondition
      constructor
      · rw [xorWire_apply_same, inside.1,
          xorWire_apply_other (historyIdleFlag layout)
            (historyLessThanIdleEndWire layout)
            (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm,
          xorWire_apply_other (historyIdleFlag layout)
            (historyLessThanTimeWire layout)
            (historyP15IdleFlag_ne_lessThanTime layout).symm]
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyCoefficientControl layout)
          (historyP15IdleCoefficientControl_ne_idleFlag layout)]
        exact inside.2)

private theorem historyP15IdleCoefficientTimeToggleComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientTimeToggleComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorControlled
          (historyLessThanTimeWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanTime layout).symm).basisAction := rfl

private theorem historyP15IdleCoefficientConjunctionLayout_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ([historyBranchWire layout, historyIdleFlag layout] ++ [] ++
      [historyCoefficientControl layout]).Nodup := by
  simp [(historyP15IdleFlag_ne_branch layout).symm,
    (historyP15IdleCoefficientControl_ne_branch layout).symm,
    (historyP15IdleCoefficientControl_ne_idleFlag layout).symm]

private theorem historyP15IdleCoefficientConjunctionCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    ClassicalReversibleStage.allWiresTrue
      [historyBranchWire layout, historyIdleFlag layout] input =
        (input (historyBranchWire layout) && input (historyIdleFlag layout)) := by
  simp [ClassicalReversibleStage.allWiresTrue,
    ClassicalReversibleStage.readWires]

private noncomputable def historyP15IdleCoefficientControlComputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyBranchWire layout, historyIdleFlag layout] []
    (historyCoefficientControl layout) (by simp)
    (historyP15IdleCoefficientConjunctionLayout_nodup layout)
    (historyP15IdleCoefficientIdleComputedPredicate layout)
    (historyP15IdleCoefficientControlComputedPredicate layout)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input inside
      unfold historyP15IdleCoefficientIdleComputedPredicate at inside
      unfold historyP15IdleCoefficientControlComputedPredicate
      let action := ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyIdleFlag layout]
        (historyCoefficientControl layout)
      constructor
      · calc
          action input (historyIdleFlag layout) =
              input (historyIdleFlag layout) :=
            ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
              [historyBranchWire layout, historyIdleFlag layout]
              (historyCoefficientControl layout) (historyIdleFlag layout)
              (historyP15IdleCoefficientControl_ne_idleFlag layout).symm input
          _ = historyP15IdleCoefficientStoredIntervalCondition layout input :=
            inside.1
          _ = historyP15IdleCoefficientStoredIntervalCondition layout
              (action input) := by
            unfold historyP15IdleCoefficientStoredIntervalCondition
            dsimp [action]
            rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
              [historyBranchWire layout, historyIdleFlag layout]
              (historyCoefficientControl layout)
              (historyLessThanIdleEndWire layout)
              (historyP15IdleCoefficientControl_ne_lessThanIdleEnd layout).symm,
              ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
                [historyBranchWire layout, historyIdleFlag layout]
                (historyCoefficientControl layout)
                (historyLessThanTimeWire layout)
                (historyP15IdleCoefficientControl_ne_lessThanTime layout).symm]
      · change action input (historyCoefficientControl layout) =
          (action input (historyBranchWire layout) &&
            action input (historyIdleFlag layout))
        have conditionStable :
            (action input (historyBranchWire layout) &&
              action input (historyIdleFlag layout)) =
              (input (historyBranchWire layout) && input (historyIdleFlag layout)) := by
          dsimp [action]
          rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
            [historyBranchWire layout, historyIdleFlag layout]
            (historyCoefficientControl layout) (historyBranchWire layout)
            (historyP15IdleCoefficientControl_ne_branch layout).symm,
            ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
            [historyBranchWire layout, historyIdleFlag layout]
            (historyCoefficientControl layout) (historyIdleFlag layout)
            (historyP15IdleCoefficientControl_ne_idleFlag layout).symm]
        rw [show action input (historyCoefficientControl layout) =
            (input (historyCoefficientControl layout) !=
              ClassicalReversibleStage.allWiresTrue
                [historyBranchWire layout, historyIdleFlag layout] input) by
              exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target
                _ _ _, historyP15IdleCoefficientConjunctionCondition layout input,
          inside.2, conditionStable]
        cases input (historyBranchWire layout) <;>
          cases input (historyIdleFlag layout) <;> rfl)

private theorem historyP15IdleCoefficientControlComputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientControlComputeComponent layout).target =
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyIdleFlag layout]
        (historyCoefficientControl layout) := rfl

private noncomputable def historyP15IdleCoefficientUseComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :=
  let exact := ExactOperatorComponent.refineTarget
    (historyClockCoefficientRotationExactComponent
      (historyCoefficientControl layout) layout.coefficientSignal
      (historyP15CoefficientControl_ne_coefficientSignal layout) angle)
    (predicateControlledSingleQubitOperator
      (fun basis => basis (historyCoefficientControl layout))
      layout.coefficientSignal (localRy angle.uniformValue))
    (embedControlledSingleQubitOperator_eq_predicateControlled
      (historyCoefficientControl layout) layout.coefficientSignal
      (historyP15CoefficientControl_ne_coefficientSignal layout)
      (localRy angle.uniformValue))
  exact.toSubspaceMapOfOutsideSupport {layout.coefficientSignal}
    (OperatorPreservesOutside.predicateControlledSingleQubitOperator
      (fun basis => basis (historyCoefficientControl layout))
      layout.coefficientSignal (localRy angle.uniformValue))
    (historyP15IdleCoefficientControlComputedPredicate layout)
    (historyP15IdleCoefficientControlComputedPredicate layout)
    (by
      intro input output computed sameOutside
      unfold historyP15IdleCoefficientControlComputedPredicate at computed ⊢
      have agrees : agreesExcept layout.coefficientSignal input output := by
        intro wire different
        exact (sameOutside wire (by simpa using different)).symm
      constructor
      · calc
          output (historyIdleFlag layout) = input (historyIdleFlag layout) :=
            sameOutside _ (by
              simp [historyP15IdleCoefficientIdleFlag_ne_coefficientSignal])
          _ = historyP15IdleCoefficientStoredIntervalCondition layout input :=
            computed.1
          _ = historyP15IdleCoefficientStoredIntervalCondition layout output :=
            by
              unfold historyP15IdleCoefficientStoredIntervalCondition
              rw [agrees (historyLessThanIdleEndWire layout)
                (historyP15IdleCoefficientLessThanIdleEnd_ne_coefficientSignal
                  layout),
                agrees (historyLessThanTimeWire layout)
                  (historyP15IdleCoefficientLessThanTime_ne_coefficientSignal
                    layout)]
      · calc
          output (historyCoefficientControl layout) =
              input (historyCoefficientControl layout) :=
            sameOutside _ (by
              simp [historyP15CoefficientControl_ne_coefficientSignal])
          _ = (input (historyBranchWire layout) &&
              input (historyIdleFlag layout)) := computed.2
          _ = (output (historyBranchWire layout) &&
              output (historyIdleFlag layout)) :=
            by
              rw [agrees (historyBranchWire layout)
                (historyP15IdleCoefficientBranch_ne_coefficientSignal layout),
                agrees (historyIdleFlag layout)
                  (historyP15IdleCoefficientIdleFlag_ne_coefficientSignal layout)])

private theorem historyP15IdleCoefficientUseComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    (historyP15IdleCoefficientUseComponent layout angle).target =
      predicateControlledSingleQubitOperator
        (fun basis => basis (historyCoefficientControl layout))
        layout.coefficientSignal (localRy angle.uniformValue) := rfl

private noncomputable def historyP15IdleCoefficientControlUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyBranchWire layout, historyIdleFlag layout] []
    (historyCoefficientControl layout) (by simp)
    (historyP15IdleCoefficientConjunctionLayout_nodup layout)
    (historyP15IdleCoefficientControlComputedPredicate layout)
    (historyP15IdleCoefficientIdleComputedPredicate layout)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input inside
      unfold historyP15IdleCoefficientControlComputedPredicate at inside
      unfold historyP15IdleCoefficientIdleComputedPredicate
      let action := ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyIdleFlag layout]
        (historyCoefficientControl layout)
      constructor
      · calc
          action input (historyIdleFlag layout) =
              input (historyIdleFlag layout) :=
            ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
              [historyBranchWire layout, historyIdleFlag layout]
              (historyCoefficientControl layout) (historyIdleFlag layout)
              (historyP15IdleCoefficientControl_ne_idleFlag layout).symm input
          _ = historyP15IdleCoefficientStoredIntervalCondition layout input :=
            inside.1
          _ = historyP15IdleCoefficientStoredIntervalCondition layout
              (action input) := by
            unfold historyP15IdleCoefficientStoredIntervalCondition
            dsimp [action]
            rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
              [historyBranchWire layout, historyIdleFlag layout]
              (historyCoefficientControl layout)
              (historyLessThanIdleEndWire layout)
              (historyP15IdleCoefficientControl_ne_lessThanIdleEnd layout).symm,
              ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
                [historyBranchWire layout, historyIdleFlag layout]
                (historyCoefficientControl layout)
                (historyLessThanTimeWire layout)
                (historyP15IdleCoefficientControl_ne_lessThanTime layout).symm]
      · change action input (historyCoefficientControl layout) = false
        rw [show action input (historyCoefficientControl layout) =
            (input (historyCoefficientControl layout) !=
              ClassicalReversibleStage.allWiresTrue
                [historyBranchWire layout, historyIdleFlag layout] input) by
              exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target
                _ _ _, historyP15IdleCoefficientConjunctionCondition layout input,
          inside.2]
        cases input (historyBranchWire layout) <;>
          cases input (historyIdleFlag layout) <;> rfl)

private theorem historyP15IdleCoefficientControlUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientControlUncomputeComponent layout).target =
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyIdleFlag layout]
        (historyCoefficientControl layout) := rfl

private theorem historyP15IdleCoefficientCondition_controlInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyCoefficientControl layout) first second) :
    (first (historyBranchWire layout) && first (historyIdleFlag layout)) =
      (second (historyBranchWire layout) && second (historyIdleFlag layout)) := by
  rw [same (historyBranchWire layout)
    (historyP15IdleCoefficientControl_ne_branch layout).symm,
    same (historyIdleFlag layout)
      (historyP15IdleCoefficientControl_ne_idleFlag layout).symm]

private theorem historyP15IdleCoefficientCondition_signalInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept layout.coefficientSignal first second) :
    (first (historyBranchWire layout) && first (historyIdleFlag layout)) =
      (second (historyBranchWire layout) && second (historyIdleFlag layout)) := by
  rw [same (historyBranchWire layout)
    (historyP15IdleCoefficientBranch_ne_coefficientSignal layout),
    same (historyIdleFlag layout)
      (historyP15IdleCoefficientIdleFlag_ne_coefficientSignal layout)]

private theorem historyP15IdleCoefficientInnerChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    SubspaceMapComponent.SpaceChain
      [historyP15IdleCoefficientControlComputeComponent layout,
       historyP15IdleCoefficientUseComponent layout angle,
       historyP15IdleCoefficientControlUncomputeComponent layout]
      (SubspaceMapComponent.basisSpan
        (historyP15IdleCoefficientIdleComputedPredicate layout))
      (SubspaceMapComponent.basisSpan
        (historyP15IdleCoefficientIdleComputedPredicate layout)) := by
  exact .cons _ [_, _] _ _ _ rfl rfl
    (.cons _ [_] _ _ _ rfl rfl
      (.cons _ [] _ _ _ rfl rfl (.nil _)))

private theorem historyP15IdleCoefficientConjunctionDirectOperator_eq_xorCompute
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyIdleFlag layout]
        (historyCoefficientControl layout) =
      deterministicOperator
        (historyP15XorComputeAction (historyCoefficientControl layout)
          (fun basis => basis (historyBranchWire layout) &&
            basis (historyIdleFlag layout))) := by
  apply congrArg deterministicOperator
  funext input
  change xorWire (historyCoefficientControl layout)
      (ClassicalReversibleStage.allWiresTrue
        [historyBranchWire layout, historyIdleFlag layout] input) input =
    xorWire (historyCoefficientControl layout)
      (input (historyBranchWire layout) && input (historyIdleFlag layout)) input
  rw [historyP15IdleCoefficientConjunctionCondition]

private noncomputable def historyP15IdleCoefficientInnerOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) : Operator (QubitBasis qubits) :=
  predicateControlledSingleQubitOperator
    (fun basis => basis (historyBranchWire layout) &&
      basis (historyIdleFlag layout))
    layout.coefficientSignal (localRy angle.uniformValue)

private theorem historyP15IdleCoefficientInnerSequence_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    (SubspaceMapComponent.sequenceAlong
      (historyP15IdleCoefficientInnerChain layout angle)).target =
      historyP15XorComputeUseUncomputeOperator
        (historyCoefficientControl layout) layout.coefficientSignal
        (historyP15CoefficientControl_ne_coefficientSignal layout)
        (fun basis => basis (historyBranchWire layout) &&
          basis (historyIdleFlag layout))
        (localRy angle.uniformValue) := by
  rw [SubspaceMapComponent.sequenceAlong_target]
  simp only [List.map_cons, List.map_nil, operatorSequence]
  rw [historyP15IdleCoefficientControlComputeComponent_target,
    historyP15IdleCoefficientUseComponent_target,
    historyP15IdleCoefficientControlUncomputeComponent_target]
  rw [← embedControlledSingleQubitOperator_eq_predicateControlled
    (historyCoefficientControl layout) layout.coefficientSignal
    (historyP15CoefficientControl_ne_coefficientSignal layout)
    (localRy angle.uniformValue)]
  simp only [one_mul,
    historyP15IdleCoefficientConjunctionDirectOperator_eq_xorCompute,
    historyP15XorComputeUseUncomputeOperator]

private theorem historyP15IdleCoefficientInnerSequence_target_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (input : QubitBasis qubits)
    (clean : historyP15IdleCoefficientIdleComputedPredicate layout input) :
    applyOperator
        (SubspaceMapComponent.sequenceAlong
          (historyP15IdleCoefficientInnerChain layout angle)).target
        (basisKet input) =
      applyOperator (historyP15IdleCoefficientInnerOperator layout angle)
        (basisKet input) := by
  rw [historyP15IdleCoefficientInnerSequence_target]
  unfold historyP15IdleCoefficientIdleComputedPredicate at clean
  simpa only [historyP15IdleCoefficientInnerOperator] using
    (historyP15_applyOperator_xorComputeUseUncompute_basisKet
      (historyCoefficientControl layout) layout.coefficientSignal
      (historyP15CoefficientControl_ne_coefficientSignal layout)
      (fun basis => basis (historyBranchWire layout) &&
        basis (historyIdleFlag layout))
      (localRy angle.uniformValue)
      (historyP15IdleCoefficientCondition_controlInvariant layout)
      (historyP15IdleCoefficientCondition_signalInvariant layout)
      input clean.2)

private noncomputable def historyP15IdleCoefficientInnerComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let chain := historyP15IdleCoefficientInnerChain layout angle
  let raw := SubspaceMapComponent.sequenceAlong chain
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    raw.circuit (historyP15IdleCoefficientInnerOperator layout angle)
    (historyP15IdleCoefficientIdleComputedPredicate layout)
    (historyP15IdleCoefficientIdleComputedPredicate layout)
    (by
      intro input clean
      calc
        applyOperator (Circuit.denote (historyP15PostGate (qubits := qubits))
            raw.circuit) (basisKet input) =
          applyOperator raw.target (basisKet input) :=
            raw.correct _
              (SubspaceMapComponent.basisKet_mem_basisSpan clean)
        _ = applyOperator (historyP15IdleCoefficientInnerOperator layout angle)
            (basisKet input) :=
          historyP15IdleCoefficientInnerSequence_target_basisKet layout angle
            input clean)
    (by
      intro input clean
      apply SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_preservesOutside
        (historyP15IdleCoefficientInnerOperator layout angle)
        {layout.coefficientSignal}
        (OperatorPreservesOutside.predicateControlledSingleQubitOperator
          (fun basis => basis (historyBranchWire layout) &&
            basis (historyIdleFlag layout))
          layout.coefficientSignal (localRy angle.uniformValue))
        (historyP15IdleCoefficientIdleComputedPredicate layout)
        (historyP15IdleCoefficientIdleComputedPredicate layout)
        (by
          intro before after beforeClean sameOutside
          unfold historyP15IdleCoefficientIdleComputedPredicate at beforeClean ⊢
          constructor
          · calc
              after (historyIdleFlag layout) = before (historyIdleFlag layout) :=
                sameOutside _ (by
                  simp [historyP15IdleCoefficientIdleFlag_ne_coefficientSignal])
              _ = historyP15IdleCoefficientStoredIntervalCondition layout before :=
                beforeClean.1
              _ = historyP15IdleCoefficientStoredIntervalCondition layout after := by
                unfold historyP15IdleCoefficientStoredIntervalCondition
                rw [sameOutside (historyLessThanIdleEndWire layout) (by
                  simp [historyP15IdleCoefficientLessThanIdleEnd_ne_coefficientSignal]),
                  sameOutside (historyLessThanTimeWire layout) (by
                    simp [historyP15IdleCoefficientLessThanTime_ne_coefficientSignal])]
          · rw [sameOutside (historyCoefficientControl layout) (by
              simp [historyP15CoefficientControl_ne_coefficientSignal])]
            exact beforeClean.2)
        input clean)

private theorem historyP15IdleCoefficientInnerComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    (historyP15IdleCoefficientInnerComponent layout angle).target =
      historyP15IdleCoefficientInnerOperator layout angle := rfl

private theorem historyP15IdleCoefficientInnerComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    (historyP15IdleCoefficientInnerComponent layout angle).circuit =
      Circuit.sequence
        [(historyP15IdleCoefficientControlComputeComponent layout).circuit,
         (historyP15IdleCoefficientUseComponent layout angle).circuit,
         (historyP15IdleCoefficientControlUncomputeComponent layout).circuit] := rfl

private noncomputable def historyP15IdleCoefficientTimeToggleUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15IdleCoefficientCnotComponent
    (historyLessThanTimeWire layout) (historyIdleFlag layout)
    (historyP15IdleFlag_ne_lessThanTime layout).symm
    (historyP15IdleCoefficientIdleComputedPredicate layout)
    (historyP15IdleCoefficientIdleEndComputedPredicate layout)
    (by
      intro input inside
      unfold historyP15IdleCoefficientIdleComputedPredicate at inside
      unfold historyP15IdleCoefficientIdleEndComputedPredicate
      change historyP15IdleCoefficientIdleEndComputedPredicate layout
        (xorWire (historyIdleFlag layout)
          (input (historyLessThanTimeWire layout)) input)
      constructor
      · rw [xorWire_apply_same, inside.1,
          xorWire_apply_other (historyIdleFlag layout)
            (historyLessThanIdleEndWire layout)
            (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm]
        unfold historyP15IdleCoefficientStoredIntervalCondition
        cases input (historyLessThanIdleEndWire layout) <;>
          cases input (historyLessThanTimeWire layout) <;> rfl
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyCoefficientControl layout)
          (historyP15IdleCoefficientControl_ne_idleFlag layout)]
        exact inside.2)

private theorem historyP15IdleCoefficientTimeToggleUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientTimeToggleUncomputeComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorControlled
          (historyLessThanTimeWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanTime layout).symm).basisAction := rfl

private noncomputable def historyP15IdleCoefficientIdleEndToggleUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15IdleCoefficientCnotComponent
    (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
    (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm
    (historyP15IdleCoefficientIdleEndComputedPredicate layout)
    (historyP15IdleCoefficientCleanPredicate layout)
    (by
      intro input inside
      unfold historyP15IdleCoefficientIdleEndComputedPredicate at inside
      unfold historyP15IdleCoefficientCleanPredicate
      change historyP15IdleCoefficientCleanPredicate layout
        (xorWire (historyIdleFlag layout)
          (input (historyLessThanIdleEndWire layout)) input)
      constructor
      · rw [xorWire_apply_same, inside.1]
        cases input (historyLessThanIdleEndWire layout) <;> rfl
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyCoefficientControl layout)
          (historyP15IdleCoefficientControl_ne_idleFlag layout)]
        exact inside.2)

private theorem historyP15IdleCoefficientIdleEndToggleUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientIdleEndToggleUncomputeComponent layout).target =
      deterministicOperator
        (ClassicalReversibleInstruction.xorControlled
          (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm).basisAction := rfl

private theorem historyP15IdleCoefficientIdleComputeChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    SubspaceMapComponent.SpaceChain
      [historyP15IdleCoefficientIdleEndToggleComponent layout,
       historyP15IdleCoefficientTimeToggleComponent layout]
      (SubspaceMapComponent.basisSpan
        (historyP15IdleCoefficientCleanPredicate layout))
      (SubspaceMapComponent.basisSpan
        (historyP15IdleCoefficientIdleComputedPredicate layout)) := by
  exact .cons _ [_] _ _ _ rfl rfl
    (.cons _ [] _ _ _ rfl rfl (.nil _))

private noncomputable def historyP15IdleCoefficientIdleComputeRawComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  SubspaceMapComponent.sequenceAlong
    (historyP15IdleCoefficientIdleComputeChain layout)

private theorem historyP15IdleCoefficientIdleComputeRawComponent_target_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (clean : historyP15IdleCoefficientCleanPredicate layout input) :
    applyOperator (historyP15IdleCoefficientIdleComputeRawComponent layout).target
        (basisKet input) =
      applyOperator
        (deterministicOperator
          (historyP15XorComputeAction (historyIdleFlag layout)
            (historyP15IdleCoefficientStoredIntervalCondition layout)))
        (basisKet input) := by
  rw [show (historyP15IdleCoefficientIdleComputeRawComponent layout).target =
      (SubspaceMapComponent.sequenceAlong
        (historyP15IdleCoefficientIdleComputeChain layout)).target by rfl,
    SubspaceMapComponent.sequenceAlong_target]
  simp only [List.map_cons, List.map_nil]
  rw [historyP15IdleCoefficientIdleEndToggleComponent_target,
    historyP15IdleCoefficientTimeToggleComponent_target]
  let idleEndAction : QubitBasis qubits → QubitBasis qubits :=
    (ClassicalReversibleInstruction.xorControlled
      (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
      (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm).basisAction
  let timeAction : QubitBasis qubits → QubitBasis qubits :=
    (ClassicalReversibleInstruction.xorControlled
      (historyLessThanTimeWire layout) (historyIdleFlag layout)
      (historyP15IdleFlag_ne_lessThanTime layout).symm).basisAction
  change applyOperator
      (operatorSequence
        [deterministicOperator idleEndAction, deterministicOperator timeAction])
      (basisKet input) = _
  have folded :
      operatorSequence
          [deterministicOperator idleEndAction, deterministicOperator timeAction] =
        deterministicOperator (fun state =>
          [idleEndAction, timeAction].foldl (fun current action => action current)
            state) := by
    simpa only [List.map_cons, List.map_nil] using
      (operatorSequence_deterministicOperator [idleEndAction, timeAction])
  rw [folded,
    applyOperator_deterministicOperator_basisKet,
    applyOperator_deterministicOperator_basisKet]
  simp only [List.foldl]
  apply congrArg basisKet
  funext wire
  by_cases isIdle : wire = historyIdleFlag layout
  · subst wire
    simp [idleEndAction, timeAction,
      ClassicalReversibleInstruction.basisAction, xorWire,
      historyP15XorComputeAction,
      historyP15IdleCoefficientStoredIntervalCondition, clean.1,
      (historyP15IdleFlag_ne_lessThanTime layout).symm]
  · simp [idleEndAction, timeAction,
      ClassicalReversibleInstruction.basisAction, xorWire,
      historyP15XorComputeAction, isIdle]

private noncomputable def historyP15IdleCoefficientIdleComputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let raw := historyP15IdleCoefficientIdleComputeRawComponent layout
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    raw.circuit
    (deterministicOperator
      (historyP15XorComputeAction (historyIdleFlag layout)
        (historyP15IdleCoefficientStoredIntervalCondition layout)))
    (historyP15IdleCoefficientCleanPredicate layout)
    (historyP15IdleCoefficientIdleComputedPredicate layout)
    (by
      intro input clean
      calc
        applyOperator (Circuit.denote (historyP15PostGate (qubits := qubits))
            raw.circuit) (basisKet input) =
          applyOperator raw.target (basisKet input) :=
            raw.correct _
              (SubspaceMapComponent.basisKet_mem_basisSpan clean)
        _ = applyOperator
            (deterministicOperator
              (historyP15XorComputeAction (historyIdleFlag layout)
                (historyP15IdleCoefficientStoredIntervalCondition layout)))
            (basisKet input) := by
              exact historyP15IdleCoefficientIdleComputeRawComponent_target_basisKet
                layout input clean)
    (by
      intro input clean
      rw [applyOperator_deterministicOperator_basisKet]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      unfold historyP15IdleCoefficientCleanPredicate at clean
      unfold historyP15IdleCoefficientIdleComputedPredicate
      unfold historyP15XorComputeAction
      unfold historyP15IdleCoefficientStoredIntervalCondition
      constructor
      · rw [xorWire_apply_same, clean.1,
          xorWire_apply_other (historyIdleFlag layout)
            (historyLessThanIdleEndWire layout)
            (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm,
          xorWire_apply_other (historyIdleFlag layout)
            (historyLessThanTimeWire layout)
            (historyP15IdleFlag_ne_lessThanTime layout).symm]
        cases input (historyLessThanIdleEndWire layout) <;>
          cases input (historyLessThanTimeWire layout) <;> rfl
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyCoefficientControl layout)
          (historyP15IdleCoefficientControl_ne_idleFlag layout)]
        exact clean.2)

private theorem historyP15IdleCoefficientIdleComputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientIdleComputeComponent layout).target =
      deterministicOperator
        (historyP15XorComputeAction (historyIdleFlag layout)
          (historyP15IdleCoefficientStoredIntervalCondition layout)) := rfl

private theorem historyP15IdleCoefficientIdleComputeComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientIdleComputeComponent layout).circuit =
      Circuit.sequence
        [(historyP15IdleCoefficientIdleEndToggleComponent layout).circuit,
         (historyP15IdleCoefficientTimeToggleComponent layout).circuit] := rfl

private theorem historyP15IdleCoefficientIdleUncomputeChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    SubspaceMapComponent.SpaceChain
      [historyP15IdleCoefficientTimeToggleUncomputeComponent layout,
       historyP15IdleCoefficientIdleEndToggleUncomputeComponent layout]
      (SubspaceMapComponent.basisSpan
        (historyP15IdleCoefficientIdleComputedPredicate layout))
      (SubspaceMapComponent.basisSpan
        (historyP15IdleCoefficientCleanPredicate layout)) := by
  exact .cons _ [_] _ _ _ rfl rfl
    (.cons _ [] _ _ _ rfl rfl (.nil _))

private noncomputable def historyP15IdleCoefficientIdleUncomputeRawComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  SubspaceMapComponent.sequenceAlong
    (historyP15IdleCoefficientIdleUncomputeChain layout)

private theorem historyP15IdleCoefficientIdleUncomputeRawComponent_target_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (computed : historyP15IdleCoefficientIdleComputedPredicate layout input) :
    applyOperator (historyP15IdleCoefficientIdleUncomputeRawComponent layout).target
        (basisKet input) =
      applyOperator
        (deterministicOperator
          (historyP15XorComputeAction (historyIdleFlag layout)
            (historyP15IdleCoefficientStoredIntervalCondition layout)))
        (basisKet input) := by
  rw [show (historyP15IdleCoefficientIdleUncomputeRawComponent layout).target =
      (SubspaceMapComponent.sequenceAlong
        (historyP15IdleCoefficientIdleUncomputeChain layout)).target by rfl,
    SubspaceMapComponent.sequenceAlong_target]
  simp only [List.map_cons, List.map_nil]
  rw [historyP15IdleCoefficientTimeToggleUncomputeComponent_target,
    historyP15IdleCoefficientIdleEndToggleUncomputeComponent_target]
  let timeAction : QubitBasis qubits → QubitBasis qubits :=
    (ClassicalReversibleInstruction.xorControlled
      (historyLessThanTimeWire layout) (historyIdleFlag layout)
      (historyP15IdleFlag_ne_lessThanTime layout).symm).basisAction
  let idleEndAction : QubitBasis qubits → QubitBasis qubits :=
    (ClassicalReversibleInstruction.xorControlled
      (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
      (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm).basisAction
  change applyOperator
      (operatorSequence
        [deterministicOperator timeAction, deterministicOperator idleEndAction])
      (basisKet input) = _
  have folded :
      operatorSequence
          [deterministicOperator timeAction, deterministicOperator idleEndAction] =
        deterministicOperator (fun state =>
          [timeAction, idleEndAction].foldl (fun current action => action current)
            state) := by
    simpa only [List.map_cons, List.map_nil] using
      (operatorSequence_deterministicOperator [timeAction, idleEndAction])
  rw [folded,
    applyOperator_deterministicOperator_basisKet,
    applyOperator_deterministicOperator_basisKet]
  simp only [List.foldl]
  apply congrArg basisKet
  funext wire
  by_cases isIdle : wire = historyIdleFlag layout
  · subst wire
    simp [timeAction, idleEndAction,
      ClassicalReversibleInstruction.basisAction, xorWire,
      historyP15XorComputeAction,
      historyP15IdleCoefficientStoredIntervalCondition, computed.1,
      (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm]
  · simp [timeAction, idleEndAction,
      ClassicalReversibleInstruction.basisAction, xorWire,
      historyP15XorComputeAction, isIdle]

private noncomputable def historyP15IdleCoefficientIdleUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let raw := historyP15IdleCoefficientIdleUncomputeRawComponent layout
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    raw.circuit
    (deterministicOperator
      (historyP15XorComputeAction (historyIdleFlag layout)
        (historyP15IdleCoefficientStoredIntervalCondition layout)))
    (historyP15IdleCoefficientIdleComputedPredicate layout)
    (historyP15IdleCoefficientCleanPredicate layout)
    (by
      intro input clean
      calc
        applyOperator (Circuit.denote (historyP15PostGate (qubits := qubits))
            raw.circuit) (basisKet input) =
          applyOperator raw.target (basisKet input) :=
            raw.correct _
              (SubspaceMapComponent.basisKet_mem_basisSpan clean)
        _ = applyOperator
            (deterministicOperator
              (historyP15XorComputeAction (historyIdleFlag layout)
                (historyP15IdleCoefficientStoredIntervalCondition layout)))
            (basisKet input) := by
              exact historyP15IdleCoefficientIdleUncomputeRawComponent_target_basisKet
                layout input clean)
    (by
      intro input computed
      rw [applyOperator_deterministicOperator_basisKet]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      unfold historyP15IdleCoefficientIdleComputedPredicate at computed
      unfold historyP15IdleCoefficientCleanPredicate
      unfold historyP15XorComputeAction
      constructor
      · rw [xorWire_apply_same, computed.1]
        cases historyP15IdleCoefficientStoredIntervalCondition layout input <;> rfl
      · rw [xorWire_apply_other (historyIdleFlag layout)
          (historyCoefficientControl layout)
          (historyP15IdleCoefficientControl_ne_idleFlag layout)]
        exact computed.2)

private theorem historyP15IdleCoefficientIdleUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientIdleUncomputeComponent layout).target =
      deterministicOperator
        (historyP15XorComputeAction (historyIdleFlag layout)
          (historyP15IdleCoefficientStoredIntervalCondition layout)) := rfl

private theorem historyP15IdleCoefficientIdleUncomputeComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientIdleUncomputeComponent layout).circuit =
      Circuit.sequence
        [(historyP15IdleCoefficientTimeToggleUncomputeComponent layout).circuit,
         (historyP15IdleCoefficientIdleEndToggleUncomputeComponent layout).circuit] := rfl

private theorem historyP15IdleCoefficientStoredInterval_idleInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyIdleFlag layout) first second) :
    historyP15IdleCoefficientStoredIntervalCondition layout first =
      historyP15IdleCoefficientStoredIntervalCondition layout second := by
  unfold historyP15IdleCoefficientStoredIntervalCondition
  rw [same (historyLessThanIdleEndWire layout)
      (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm,
    same (historyLessThanTimeWire layout)
      (historyP15IdleFlag_ne_lessThanTime layout).symm]

private theorem historyP15IdleCoefficientStoredInterval_signalInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept layout.coefficientSignal first second) :
    historyP15IdleCoefficientStoredIntervalCondition layout first =
      historyP15IdleCoefficientStoredIntervalCondition layout second := by
  unfold historyP15IdleCoefficientStoredIntervalCondition
  rw [same (historyLessThanIdleEndWire layout)
      (historyP15IdleCoefficientLessThanIdleEnd_ne_coefficientSignal layout),
    same (historyLessThanTimeWire layout)
      (historyP15IdleCoefficientLessThanTime_ne_coefficientSignal layout)]

private theorem historyP15IdleCoefficientBranch_idleInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyIdleFlag layout) first second) :
    first (historyBranchWire layout) = second (historyBranchWire layout) :=
  same (historyBranchWire layout) (historyP15IdleFlag_ne_branch layout).symm

private theorem historyP15IdleCoefficientFullChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    SubspaceMapComponent.SpaceChain
      [historyP15IdleCoefficientIdleComputeComponent layout,
       historyP15IdleCoefficientInnerComponent layout angle,
       historyP15IdleCoefficientIdleUncomputeComponent layout]
      (SubspaceMapComponent.basisSpan
        (historyP15IdleCoefficientCleanPredicate layout))
      (SubspaceMapComponent.basisSpan
        (historyP15IdleCoefficientCleanPredicate layout)) := by
  exact .cons _ [_, _] _ _ _ rfl rfl
    (.cons _ [_] _ _ _ rfl rfl
      (.cons _ [] _ _ _ rfl rfl (.nil _)))

private noncomputable def historyP15IdleCoefficientRawComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :=
  SubspaceMapComponent.sequenceAlong
    (historyP15IdleCoefficientFullChain layout angle)

private theorem historyP15IdleCoefficientRawComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    (historyP15IdleCoefficientRawComponent layout angle).target =
      historyP15XorComputeGuardedUseUncomputeOperator
        (historyIdleFlag layout) layout.coefficientSignal
        (historyP15IdleCoefficientStoredIntervalCondition layout)
        (fun basis => basis (historyBranchWire layout))
        (localRy angle.uniformValue) := by
  rw [show (historyP15IdleCoefficientRawComponent layout angle).target =
      (SubspaceMapComponent.sequenceAlong
        (historyP15IdleCoefficientFullChain layout angle)).target by rfl,
    SubspaceMapComponent.sequenceAlong_target]
  simp only [List.map_cons, List.map_nil, operatorSequence]
  rw [historyP15IdleCoefficientIdleComputeComponent_target,
    historyP15IdleCoefficientInnerComponent_target,
    historyP15IdleCoefficientIdleUncomputeComponent_target]
  simp only [one_mul, historyP15IdleCoefficientInnerOperator,
    historyP15XorComputeGuardedUseUncomputeOperator]

private theorem historyP15IdleCoefficientStoredInterval_eq_analytic
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    historyP15IdleCoefficientStoredIntervalCondition layout input =
      historyTaylorIdleIntervalCondition layout input := by
  unfold historyP15IdleCoefficientStoredIntervalCondition
    historyTaylorIdleIntervalCondition
  rw [inside.2.2.2.1, inside.2.2.1]

private theorem historyP15IdleCoefficientRawComponent_target_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angle : AngleExpr) (input : QubitBasis qubits)
    (clean : historyP15IdleCoefficientCleanPredicate layout input)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    applyOperator (historyP15IdleCoefficientRawComponent layout angle).target
        (basisKet input) =
      applyOperator (historyTaylorIdleCoefficientOperator layout angle)
        (basisKet input) := by
  rw [historyP15IdleCoefficientRawComponent_target]
  have intervalEqual := historyP15IdleCoefficientStoredInterval_eq_analytic
    layout widths input inside
  calc
    applyOperator
        (historyP15XorComputeGuardedUseUncomputeOperator
          (historyIdleFlag layout) layout.coefficientSignal
          (historyP15IdleCoefficientStoredIntervalCondition layout)
          (fun basis => basis (historyBranchWire layout))
          (localRy angle.uniformValue))
        (basisKet input) =
      applyOperator
        (predicateControlledSingleQubitOperator
          (fun basis => basis (historyBranchWire layout) &&
            historyP15IdleCoefficientStoredIntervalCondition layout basis)
          layout.coefficientSignal (localRy angle.uniformValue))
        (basisKet input) := by
          simpa using
            (historyP15_applyOperator_xorCompute_guardedUseUncompute_basisKet
              (historyIdleFlag layout) layout.coefficientSignal
              (historyP15IdleCoefficientIdleFlag_ne_coefficientSignal layout)
              (historyP15IdleCoefficientStoredIntervalCondition layout)
              (fun basis => basis (historyBranchWire layout))
              (localRy angle.uniformValue)
              (historyP15IdleCoefficientStoredInterval_idleInvariant layout)
              (historyP15IdleCoefficientStoredInterval_signalInvariant layout)
              (historyP15IdleCoefficientBranch_idleInvariant layout)
              input clean.1)
    _ = applyOperator (historyTaylorIdleCoefficientOperator layout angle)
        (basisKet input) := by
          unfold historyTaylorIdleCoefficientOperator
          funext output
          rw [applyOperator_basisKet, applyOperator_basisKet,
            predicateControlledSingleQubitOperator_apply,
            predicateControlledSingleQubitOperator_apply]
          rw [show (input (historyBranchWire layout) &&
              historyP15IdleCoefficientStoredIntervalCondition layout input) =
              (input (historyBranchWire layout) &&
                historyTaylorIdleIntervalCondition layout input) by
              rw [intervalEqual]]

private theorem historyP15PostQ10StablePredicate_of_agreesOutsideCoefficientSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input output : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input)
    (sameOutside : ∀ wire, wire ≠ layout.coefficientSignal →
      output wire = input wire) :
    historyP15PostQ10StablePredicate (layout := layout) widths output := by
  constructor
  · exact historyP15PostQ10OutputPredicate_of_agreesOutsideSignal widths
      layout.coefficientSignal (by simp) input output inside.1 sameOutside
  · exact historyTaylorPostGeneratorStablePredicate_of_agreesOutsideSignal
      layout layout.coefficientSignal (by simp) input output inside.2 sameOutside

/-- The genuine seven post-Q10 source stages for the idling coefficient
rotation, restricted to the common stable clean boundary.  The declared
target is the existing analytic idling-interval controlled rotation. -/
noncomputable def historyP15IdleCoefficientComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angle : AngleExpr) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let raw := historyP15IdleCoefficientRawComponent layout angle
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    raw.circuit (historyTaylorIdleCoefficientOperator layout angle)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (by
      intro input inside
      have clean := historyP15PostQ10StablePredicate_implies_idleCoefficientClean
        layout widths input inside
      calc
        applyOperator (Circuit.denote (historyP15PostGate (qubits := qubits))
            raw.circuit) (basisKet input) =
          applyOperator raw.target (basisKet input) :=
            raw.correct _
              (SubspaceMapComponent.basisKet_mem_basisSpan clean)
        _ = applyOperator (historyTaylorIdleCoefficientOperator layout angle)
            (basisKet input) :=
          historyP15IdleCoefficientRawComponent_target_basisKet layout widths
            angle input clean inside)
    (by
      intro input inside
      apply SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_preservesOutside
        (historyTaylorIdleCoefficientOperator layout angle)
        {layout.coefficientSignal}
        (OperatorPreservesOutside.predicateControlledSingleQubitOperator
          (fun basis => basis (historyBranchWire layout) &&
            historyTaylorIdleIntervalCondition layout basis)
          layout.coefficientSignal (localRy angle.uniformValue))
        (historyP15PostQ10StablePredicate (layout := layout) widths)
        (historyP15PostQ10StablePredicate (layout := layout) widths)
        (by
          intro before after beforeStable sameOutside
          apply historyP15PostQ10StablePredicate_of_agreesOutsideCoefficientSignal
            layout widths before after beforeStable
          intro wire different
          exact sameOutside wire (by simpa using different))
        input inside)

/-- Both public spaces of the idle-coefficient component are exactly the
common post-Q10 stable basis span. -/
@[simp] theorem historyP15IdleCoefficientComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angle : AngleExpr) :
    (historyP15IdleCoefficientComponent layout widths angle).inputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) ∧
      (historyP15IdleCoefficientComponent layout widths angle).outputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) := by
  constructor <;> rfl

/-- Literal source-order stages for the frozen idling-coefficient word. -/
noncomputable def historyP15IdleCoefficientSourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) : List (Circuit (PrimitiveGate qubits)) :=
  [(historyP15IdleCoefficientIdleEndToggleComponent layout).circuit,
   (historyP15IdleCoefficientTimeToggleComponent layout).circuit,
   (historyP15IdleCoefficientControlComputeComponent layout).circuit,
   (historyP15IdleCoefficientUseComponent layout angle).circuit,
   (historyP15IdleCoefficientControlUncomputeComponent layout).circuit,
   (historyP15IdleCoefficientTimeToggleUncomputeComponent layout).circuit,
   (historyP15IdleCoefficientIdleEndToggleUncomputeComponent layout).circuit]

noncomputable def historyP15IdleCoefficientSourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) : Circuit (PrimitiveGate qubits) :=
  Circuit.sequence (historyP15IdleCoefficientSourceStages layout angle)

private theorem historyP15IdleCoefficientRawComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    (historyP15IdleCoefficientRawComponent layout angle).circuit =
      Circuit.sequence
        [(historyP15IdleCoefficientIdleComputeComponent layout).circuit,
         (historyP15IdleCoefficientInnerComponent layout angle).circuit,
         (historyP15IdleCoefficientIdleUncomputeComponent layout).circuit] := rfl

@[simp] theorem historyP15IdleCoefficientComponent_circuit_eq_raw
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angle : AngleExpr) :
    (historyP15IdleCoefficientComponent layout widths angle).circuit =
      (historyP15IdleCoefficientRawComponent layout angle).circuit := rfl

/-- The public idle-coefficient circuit has exactly the primitive-gate
flattening of the literal seven-stage P15 source word. -/
theorem historyP15IdleCoefficientComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angle : AngleExpr) :
    (historyP15IdleCoefficientComponent layout widths angle).circuit.flatten =
      (historyP15IdleCoefficientSourceCircuit layout angle).flatten := by
  rw [historyP15IdleCoefficientComponent_circuit_eq_raw,
    historyP15IdleCoefficientRawComponent_circuit,
    historyP15IdleCoefficientIdleComputeComponent_circuit,
    historyP15IdleCoefficientInnerComponent_circuit,
    historyP15IdleCoefficientIdleUncomputeComponent_circuit]
  simp [historyP15IdleCoefficientSourceCircuit,
    historyP15IdleCoefficientSourceStages, Circuit.sequence, Circuit.flatten]

/-! ### Restore the three P15 entry flags

The final post-generator word is the literal reverse use of the two clock
comparisons followed by the selector equality.  The three flags are live on
the common post-Q10 boundary, whereas every comparator scratch is clean.  The
following small chain exposes that final clean boundary without importing the
monolithic P15 wrapper.
-/

/-- Final clean P15 boundary after the two clock predicates and the selector
predicate have been erased, while the independently restored Q10 output
boundary remains available to the enclosing H2 composition. -/
def historyP15PostQ10CleanOutputPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (basis : QubitBasis qubits) : Prop :=
  historyP15PostQ10OutputPredicate (layout := layout) widths basis /\
    historyTaylorAuxiliaryBoundaryPredicate layout basis

private def historyP15RestoreEntryFlagsAfterIdleEndPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (basis : QubitBasis qubits) : Prop :=
  historyP15PostQ10OutputPredicate (layout := layout) widths basis /\
    historyTaylorAfterTimeComparisonPredicate layout basis

private def historyP15RestoreEntryFlagsAfterTimePredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (basis : QubitBasis qubits) : Prop :=
  historyP15PostQ10OutputPredicate (layout := layout) widths basis /\
    historyTaylorAfterSelectorPredicate layout basis

/-- The stable post-Q10 boundary gives the ordinary P41 phase predicate once
the Q10-owned aliases have been discharged through their own clean contract. -/
private theorem historyP15PostQ10StablePredicate_implies_afterIdleEndComparison
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    historyTaylorAfterIdleEndComparisonPredicate layout input := by
  refine ⟨inside.2.1, inside.2.2.1, inside.2.2.2.1, ?_⟩
  intro workspaceIndex outside
  exact historyP15OrderBoundaryStableWorkspaceZero layout widths input inside
    workspaceIndex outside

private theorem historyP15RestoreEntryFlags_not_mem_stableFlags_of_not_mem_live
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (wire : Fin qubits)
    (outsideLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
    wire ∉ [historyBranchWire layout, historyLessThanTimeWire layout,
      historyLessThanIdleEndWire layout] := by
  intro member
  apply outsideLive
  simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
    List.not_mem_nil, or_false] at member ⊢
  rcases member with branch | time | idle
  · exact Or.inl branch
  · exact Or.inr (Or.inl time)
  · exact Or.inr (Or.inr (Or.inl idle))

/-- Both constant-comparison work slices are clean at the post-Q10 boundary.
This is stated once for the idle-end comparator; the time comparator shares
the same registers and therefore follows by definitional reduction. -/
private theorem historyP15RestoreEntryFlagsIdleEndComparisonClean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    historyLessThanConstantCleanInputPredicate
      evidence.clock.clockIdleEndLessThan.toSpec input := by
  unfold historyLessThanConstantCleanInputPredicate
  constructor
  · intro index
    rcases List.mem_ofFn.mp
        (historyBorrowRegister_wire_mem_workspace layout index) with
      ⟨workspaceIndex, equal⟩
    have outside : layout.workspace.wire workspaceIndex ∉
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout] := by
      simpa [equal] using
        historyP15RestoreEntryFlags_not_mem_stableFlags_of_not_mem_live
          layout ((historyBorrowRegister layout).wire index)
          (historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires layout index)
    have zero := historyP15OrderBoundaryStableWorkspaceZero layout widths input
      inside workspaceIndex outside
    simpa [HistoryP15LessThanEvidence.toSpec, Register.read, equal] using zero
  · intro index
    rcases List.mem_ofFn.mp
        (historyBoundRegister_wire_mem_workspace layout index) with
      ⟨workspaceIndex, equal⟩
    have outside : layout.workspace.wire workspaceIndex ∉
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout] := by
      simpa [equal] using
        historyP15RestoreEntryFlags_not_mem_stableFlags_of_not_mem_live
          layout ((historyBoundRegister layout).wire index)
          (historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires layout index)
    have zero := historyP15OrderBoundaryStableWorkspaceZero layout widths input
      inside workspaceIndex outside
    simpa [HistoryP15LessThanEvidence.toSpec, Register.read, equal] using zero

/-- The stored idle-end comparison is exactly erased by its repeated direct
XOR action. -/
private theorem historyP15IdleEndComparisonBasisAction_unmaps_phase
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAfterIdleEndComparisonPredicate layout input) :
    historyTaylorAfterTimeComparisonPredicate layout
      (historyTaylorIdleEndComparisonBasisAction layout input) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold historyTaylorIdleEndComparisonBasisAction
    rw [xorWire_apply_other (historyLessThanIdleEndWire layout)
      (historyBranchWire layout)
      (historyBranchWire_ne_lessThanIdleEndWire layout), inside.1]
    symm
    exact layout.selectorEqualsNat_xorWire_workspace
      (historyLessThanIdleEndWire layout)
      (historyLessThanIdleEndWire_mem_workspace layout) _ _ _
  · unfold historyTaylorIdleEndComparisonBasisAction
    rw [xorWire_apply_other (historyLessThanIdleEndWire layout)
      (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_ne_lessThanIdleEndWire layout), inside.2.1]
    unfold historyTaylorClockLessThanTimeValue
    rw [layout.clock_read_xorWire_workspace
      (historyLessThanIdleEndWire layout)
      (historyLessThanIdleEndWire_mem_workspace layout)]
  · intro workspaceIndex outside
    by_cases isIdle : layout.workspace.wire workspaceIndex =
        historyLessThanIdleEndWire layout
    · rw [isIdle]
      unfold historyTaylorIdleEndComparisonBasisAction
      rw [xorWire_apply_same, inside.2.2.1]
      cases historyTaylorClockLessThanIdleEndValue layout input <;> rfl
    · unfold historyTaylorIdleEndComparisonBasisAction
      rw [xorWire_apply_other (historyLessThanIdleEndWire layout)
        (layout.workspace.wire workspaceIndex) (fun equal => isIdle equal)]
      exact inside.2.2.2 workspaceIndex (by
        intro member
        apply outside
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        rcases member with branch | time | idle
        · exact Or.inl branch
        · exact Or.inr time
        · exact False.elim (isIdle idle))

/-- Repeating the time comparison erases its stored predicate. -/
private theorem historyP15TimeComparisonBasisAction_unmaps_phase
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAfterTimeComparisonPredicate layout input) :
    historyTaylorAfterSelectorPredicate layout
      (historyTaylorTimeComparisonBasisAction layout input) := by
  refine ⟨?_, ?_⟩
  · unfold historyTaylorTimeComparisonBasisAction
    rw [xorWire_apply_other (historyLessThanTimeWire layout)
      (historyBranchWire layout)
      (historyBranchWire_ne_lessThanTimeWire layout), inside.1]
    symm
    exact layout.selectorEqualsNat_xorWire_workspace
      (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_mem_workspace layout) _ _ _
  · intro workspaceIndex outside
    by_cases isTime : layout.workspace.wire workspaceIndex =
        historyLessThanTimeWire layout
    · rw [isTime]
      unfold historyTaylorTimeComparisonBasisAction
      rw [xorWire_apply_same, inside.2.1]
      cases historyTaylorClockLessThanTimeValue layout input <;> rfl
    · unfold historyTaylorTimeComparisonBasisAction
      rw [xorWire_apply_other (historyLessThanTimeWire layout)
        (layout.workspace.wire workspaceIndex) (fun equal => isTime equal)]
      exact inside.2.2 workspaceIndex (by
        intro member
        apply outside
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        rcases member with branch | time
        · exact branch
        · exact False.elim (isTime time))

/-- The selector equality stage is self-inverse and therefore restores the
all-zero auxiliary boundary from its recorded branch predicate. -/
private theorem historyP15SelectorEqualityBasisAction_unmaps_phase
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAfterSelectorPredicate layout input) :
    historyTaylorAuxiliaryBoundaryPredicate layout
      (historyTaylorSelectorEqualityBasisAction layout input) := by
  intro workspaceIndex
  by_cases isBranch : layout.workspace.wire workspaceIndex =
      historyBranchWire layout
  · rw [isBranch]
    unfold historyTaylorSelectorEqualityBasisAction
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
      inside.1]
    cases ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.selector) 1 input <;> rfl
  · unfold historyTaylorSelectorEqualityBasisAction
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.selector) 1 (historyBranchWire layout)
      (layout.workspace.wire workspaceIndex) isBranch]
    exact inside.2 workspaceIndex (by
      intro member
      apply isBranch
      simpa using member)

private noncomputable def historyP15RestoreEntryFlagsIdleEndComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  let comparison := evidence.clock.clockIdleEndLessThan.toSpec
  let constant := historyIdleClockEnd parameters.timeSteps
    parameters.taylorOrder parameters.idlingSteps
  historyP15LessThanConstantCleanStageBetween comparison constant
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (historyP15RestoreEntryFlagsAfterIdleEndPredicate (layout := layout) widths)
    (by
      intro input inside
      simpa [comparison, HistoryP15LessThanEvidence.toSpec] using
        historyP15RestoreEntryFlagsIdleEndComparisonClean layout evidence widths
          input inside)
    (by
      intro input inside
      constructor
      · simpa [comparison, constant, HistoryP15LessThanEvidence.toSpec,
          historyLessThanConstantDirectBasisAction] using
          historyP15PostQ10OutputPredicate_xorLiveWire widths
            (historyLessThanIdleEndWire layout)
            (by simp [historyTaylorBeforeGeneratorLiveWires])
            (unsignedLessThanBits (comparison.lhs.read input)
              (fun index => constant.testBit index.val)) input inside.1
      · simpa [comparison, constant, HistoryP15LessThanEvidence.toSpec,
          historyTaylorIdleEndComparisonBasisAction,
          historyTaylorClockLessThanIdleEndValue,
          historyLessThanConstantDirectBasisAction] using
          historyP15IdleEndComparisonBasisAction_unmaps_phase layout input
            (historyP15PostQ10StablePredicate_implies_afterIdleEndComparison
              layout widths input inside))

private theorem historyP15RestoreEntryFlagsIdleEndComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsIdleEndComponent layout evidence widths).target =
      historyTaylorIdleEndComparisonOperator layout := by
  rfl

private noncomputable def historyP15RestoreEntryFlagsTimeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  let comparison := evidence.clock.clockTimeLessThan.toSpec
  historyP15LessThanConstantCleanStageBetween comparison parameters.timeSteps
    (historyP15RestoreEntryFlagsAfterIdleEndPredicate (layout := layout) widths)
    (historyP15RestoreEntryFlagsAfterTimePredicate (layout := layout) widths)
    (by
      intro input inside
      have clean := historyTaylorAfterTimeComparisonPredicate_p41Clean
        layout input inside.2
      exact ⟨clean.2, clean.1⟩)
    (by
      intro input inside
      constructor
      · simpa [comparison, HistoryP15LessThanEvidence.toSpec,
          historyLessThanConstantDirectBasisAction] using
          historyP15PostQ10OutputPredicate_xorLiveWire widths
            (historyLessThanTimeWire layout)
            (by simp [historyTaylorBeforeGeneratorLiveWires])
            (unsignedLessThanBits (comparison.lhs.read input)
              (fun index => parameters.timeSteps.testBit index.val)) input inside.1
      · simpa [comparison, HistoryP15LessThanEvidence.toSpec,
          historyTaylorTimeComparisonBasisAction,
          historyTaylorClockLessThanTimeValue,
          historyLessThanConstantDirectBasisAction] using
          historyP15TimeComparisonBasisAction_unmaps_phase layout input inside.2)

private theorem historyP15RestoreEntryFlagsTimeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsTimeComponent layout evidence widths).target =
      historyTaylorTimeComparisonOperator layout := by
  rfl

private noncomputable def historyP15RestoreEntryFlagsSelectorComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  ClassicalReversibleStage.xorEqualityToConstantMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (historyRegisterWires layout.selector) [] 1
    (historyBranchWire layout) (by simp [historyRegisterWires])
    (historyTaylorSelectorEqualityLayout_nodup layout)
    (historyP15RestoreEntryFlagsAfterTimePredicate (layout := layout) widths)
    (historyP15PostQ10CleanOutputPredicate (layout := layout) widths)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input inside
      constructor
      · simpa [historyTaylorSelectorEqualityBasisAction,
          ClassicalReversibleStage.equalityToConstantDirectBasisAction] using
          historyP15PostQ10OutputPredicate_xorLiveWire widths
            (historyBranchWire layout)
            (by simp [historyTaylorBeforeGeneratorLiveWires])
            (ClassicalReversibleStage.littleEndianRegisterEqualsNat
              (historyRegisterWires layout.selector) 1 input) input inside.1
      · exact historyP15SelectorEqualityBasisAction_unmaps_phase
          layout input inside.2)

private theorem historyP15RestoreEntryFlagsSelectorComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsSelectorComponent layout widths).target =
      historyTaylorSelectorEqualityOperator layout := by
  rfl

private theorem historyP15RestoreEntryFlagsChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    SubspaceMapComponent.SpaceChain
      [historyP15RestoreEntryFlagsIdleEndComponent layout evidence widths,
       historyP15RestoreEntryFlagsTimeComponent layout evidence widths,
       historyP15RestoreEntryFlagsSelectorComponent layout widths]
      (SubspaceMapComponent.basisSpan
        (historyP15PostQ10StablePredicate (layout := layout) widths))
      (SubspaceMapComponent.basisSpan
        (historyP15PostQ10CleanOutputPredicate (layout := layout) widths)) := by
  exact .cons _ [_, _] _ _ _ rfl rfl
    (.cons _ [_] _ _ _ rfl rfl
      (.cons _ [] _ _ _ rfl rfl (.nil _)))

private noncomputable def historyP15RestoreEntryFlagsRawComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  SubspaceMapComponent.sequenceAlong
    (historyP15RestoreEntryFlagsChain layout evidence widths)

/-- The direct three-action basis model for the final source word. -/
def historyP15RestoreEntryFlagsBasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  historyTaylorSelectorEqualityBasisAction layout
    (historyTaylorTimeComparisonBasisAction layout
      (historyTaylorIdleEndComparisonBasisAction layout input))

/-- Analytic clean target for the final P15 entry-flag restoration word. -/
noncomputable def historyP15RestoreEntryFlagsOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (historyP15RestoreEntryFlagsBasisAction layout)

/-- The direct target is the source-order sequence of the existing three
analytic P40/P41 actions. -/
theorem historyP15RestoreEntryFlagsOperator_eq_analyticSequence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyP15RestoreEntryFlagsOperator layout =
      operatorSequence [historyTaylorIdleEndComparisonOperator layout,
        historyTaylorTimeComparisonOperator layout,
        historyTaylorSelectorEqualityOperator layout] := by
  unfold historyP15RestoreEntryFlagsOperator
    historyTaylorIdleEndComparisonOperator
    historyTaylorTimeComparisonOperator
    historyTaylorSelectorEqualityOperator
  change deterministicOperator (historyP15RestoreEntryFlagsBasisAction layout) =
    operatorSequence
      ([historyTaylorIdleEndComparisonBasisAction layout,
        historyTaylorTimeComparisonBasisAction layout,
        historyTaylorSelectorEqualityBasisAction layout].map deterministicOperator)
  rw [operatorSequence_deterministicOperator]
  rfl

private theorem historyP15RestoreEntryFlagsRawComponent_target_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits) :
    applyOperator
        (historyP15RestoreEntryFlagsRawComponent layout evidence widths).target
        (basisKet input) =
      applyOperator (historyP15RestoreEntryFlagsOperator layout)
        (basisKet input) := by
  change applyOperator
      (operatorSequence
        [(historyP15RestoreEntryFlagsIdleEndComponent layout evidence widths).target,
         (historyP15RestoreEntryFlagsTimeComponent layout evidence widths).target,
         (historyP15RestoreEntryFlagsSelectorComponent layout widths).target])
      (basisKet input) =
    applyOperator (historyP15RestoreEntryFlagsOperator layout) (basisKet input)
  rw [
    historyP15RestoreEntryFlagsIdleEndComponent_target,
    historyP15RestoreEntryFlagsTimeComponent_target,
    historyP15RestoreEntryFlagsSelectorComponent_target,
    ← historyP15RestoreEntryFlagsOperator_eq_analyticSequence]

private theorem historyP15RestoreEntryFlagsBasisAction_maps_output
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    historyP15PostQ10CleanOutputPredicate (layout := layout) widths
      (historyP15RestoreEntryFlagsBasisAction layout input) := by
  let afterIdle := historyTaylorIdleEndComparisonBasisAction layout input
  let afterTime := historyTaylorTimeComparisonBasisAction layout afterIdle
  have idlePhase := historyP15IdleEndComparisonBasisAction_unmaps_phase
    layout input
    (historyP15PostQ10StablePredicate_implies_afterIdleEndComparison
      layout widths input inside)
  have timePhase := historyP15TimeComparisonBasisAction_unmaps_phase
    layout afterIdle idlePhase
  have idleQ10 : historyP15PostQ10OutputPredicate (layout := layout) widths
      afterIdle := by
    simpa [afterIdle, historyTaylorIdleEndComparisonBasisAction] using
      historyP15PostQ10OutputPredicate_xorLiveWire widths
        (historyLessThanIdleEndWire layout)
        (by simp [historyTaylorBeforeGeneratorLiveWires])
        (historyTaylorClockLessThanIdleEndValue layout input) input inside.1
  have timeQ10 : historyP15PostQ10OutputPredicate (layout := layout) widths
      afterTime := by
    simpa [afterTime, historyTaylorTimeComparisonBasisAction] using
      historyP15PostQ10OutputPredicate_xorLiveWire widths
        (historyLessThanTimeWire layout)
        (by simp [historyTaylorBeforeGeneratorLiveWires])
        (historyTaylorClockLessThanTimeValue layout afterIdle) afterIdle idleQ10
  have selectorQ10 : historyP15PostQ10OutputPredicate (layout := layout)
      widths (historyTaylorSelectorEqualityBasisAction layout afterTime) := by
    simpa [historyTaylorSelectorEqualityBasisAction,
      ClassicalReversibleStage.equalityToConstantDirectBasisAction] using
      historyP15PostQ10OutputPredicate_xorLiveWire widths
        (historyBranchWire layout)
        (by simp [historyTaylorBeforeGeneratorLiveWires])
        (ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 1 afterTime) afterTime timeQ10
  change historyP15PostQ10CleanOutputPredicate (layout := layout) widths
    (historyTaylorSelectorEqualityBasisAction layout afterTime)
  exact ⟨selectorQ10,
    historyP15SelectorEqualityBasisAction_unmaps_phase layout afterTime timePhase⟩

/-- The literal three-stage P15 source group which erases the stored idle-end
and time comparisons, then the stored selector-equality flag. -/
noncomputable def historyP15RestoreEntryFlagsComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let raw := historyP15RestoreEntryFlagsRawComponent layout evidence widths
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    raw.circuit (historyP15RestoreEntryFlagsOperator layout)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (historyP15PostQ10CleanOutputPredicate (layout := layout) widths)
    (by
      intro input inside
      calc
        applyOperator
            (Circuit.denote (historyP15PostGate (qubits := qubits)) raw.circuit)
            (basisKet input) =
          applyOperator raw.target (basisKet input) :=
            raw.correct _ (SubspaceMapComponent.basisKet_mem_basisSpan inside)
        _ = applyOperator (historyP15RestoreEntryFlagsOperator layout)
            (basisKet input) :=
          historyP15RestoreEntryFlagsRawComponent_target_basisKet
            layout evidence widths input)
    (by
      intro input inside
      rw [historyP15RestoreEntryFlagsOperator,
        applyOperator_deterministicOperator_basisKet]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      exact historyP15RestoreEntryFlagsBasisAction_maps_output
        layout widths input inside)

@[simp] theorem historyP15RestoreEntryFlagsComponent_target
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
      historyP15RestoreEntryFlagsOperator layout := rfl

@[simp] theorem historyP15RestoreEntryFlagsComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsComponent layout evidence widths).inputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) /\
      (historyP15RestoreEntryFlagsComponent layout evidence widths).outputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10CleanOutputPredicate (layout := layout) widths) := by
  constructor <;> rfl

/-- Literal source-order circuit stages for the final P15 entry restoration. -/
noncomputable def historyP15RestoreEntryFlagsSourceStages
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
  [(historyP15RestoreEntryFlagsIdleEndComponent layout evidence widths).circuit,
   (historyP15RestoreEntryFlagsTimeComponent layout evidence widths).circuit,
   (historyP15RestoreEntryFlagsSelectorComponent layout widths).circuit]

noncomputable def historyP15RestoreEntryFlagsSourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence (historyP15RestoreEntryFlagsSourceStages layout evidence widths)

private theorem historyP15RestoreEntryFlagsRawComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsRawComponent layout evidence widths).circuit =
      Circuit.sequence
        [(historyP15RestoreEntryFlagsIdleEndComponent layout evidence widths).circuit,
         (historyP15RestoreEntryFlagsTimeComponent layout evidence widths).circuit,
         (historyP15RestoreEntryFlagsSelectorComponent layout widths).circuit] := rfl

@[simp] theorem historyP15RestoreEntryFlagsComponent_circuit_eq_raw
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsComponent layout evidence widths).circuit =
      (historyP15RestoreEntryFlagsRawComponent layout evidence widths).circuit := rfl

/-- The public entry-restoration circuit has precisely the primitive-gate
flattening of the literal source list `[clockIdleEnd, clockTime, selector]`. -/
theorem historyP15RestoreEntryFlagsComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsComponent layout evidence widths).circuit.flatten =
      (historyP15RestoreEntryFlagsSourceCircuit layout evidence widths).flatten := by
  rw [historyP15RestoreEntryFlagsComponent_circuit_eq_raw,
    historyP15RestoreEntryFlagsRawComponent_circuit]
  simp [historyP15RestoreEntryFlagsSourceCircuit,
    historyP15RestoreEntryFlagsSourceStages, Circuit.sequence, Circuit.flatten]

/-! ### Taylor coefficient group: outer control and finite loop

The finite coefficient loop above intentionally starts after the source has
materialized `branch && clock < time` in `historyCoefficientControl`.  That
workspace wire belongs to the pool aliased with Q10 work, so the intermediate
boundary cannot itself demand the Q10 clean predicate.  Instead it remembers
that undoing the outer conjunction restores the full post-Q10 stable boundary.
This is exactly the source's compute--loop--uncompute interface.
-/

private def historyP15CoefficientOuterCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  basis (historyBranchWire layout) && basis (historyLessThanTimeWire layout)

private theorem historyP15CoefficientOuterCondition_eq_allWiresTrue
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) :
    ClassicalReversibleStage.allWiresTrue
        [historyBranchWire layout, historyLessThanTimeWire layout] basis =
      historyP15CoefficientOuterCondition layout basis := by
  simp [historyP15CoefficientOuterCondition,
    ClassicalReversibleStage.allWiresTrue,
    ClassicalReversibleStage.readWires]

private theorem historyP15CoefficientControl_ne_equalityWork
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyEqualityWorkWidth parameters)) :
    historyCoefficientControl layout ≠ (historyEqualityWork layout).wire index := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

private theorem historyP15CoefficientOuterCondition_controlInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyCoefficientControl layout) first second) :
    historyP15CoefficientOuterCondition layout first =
      historyP15CoefficientOuterCondition layout second := by
  unfold historyP15CoefficientOuterCondition
  rw [same (historyBranchWire layout)
        (historyP15IdleCoefficientControl_ne_branch layout).symm,
    same (historyLessThanTimeWire layout)
      (historyP15IdleCoefficientControl_ne_lessThanTime layout).symm]

private theorem historyP15CoefficientOuterCondition_signalInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept layout.coefficientSignal first second) :
    historyP15CoefficientOuterCondition layout first =
      historyP15CoefficientOuterCondition layout second := by
  unfold historyP15CoefficientOuterCondition
  rw [same (historyBranchWire layout)
        (historyP15IdleCoefficientBranch_ne_coefficientSignal layout),
    same (historyLessThanTimeWire layout)
      (historyP15IdleCoefficientLessThanTime_ne_coefficientSignal layout)]

/-- The outer-control boundary is intentionally stated through its inverse:
XORing the stored conjunction once more returns to the common stable sector.
This retains the Q10 work-clean fact despite the temporary shared-pool bit. -/
private def historyP15CoefficientLoopComputedPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (basis : QubitBasis qubits) : Prop :=
  historyP15PostQ10StablePredicate (layout := layout) widths
    (xorWire (historyCoefficientControl layout)
      (historyP15CoefficientOuterCondition layout basis) basis) /\
    basis (historyCoefficientControl layout) =
      historyP15CoefficientOuterCondition layout basis

private theorem historyP15CoefficientLoopComputedPredicate_implies_iterationClean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (basis : QubitBasis qubits)
    (inside : historyP15CoefficientLoopComputedPredicate
      (layout := layout) widths basis) :
    historyP15CoefficientIterationCleanPredicate layout basis := by
  have restoredClean := historyP15PostQ10StablePredicate_implies_idleBoundaryClean
    layout widths
      (xorWire (historyCoefficientControl layout)
        (historyP15CoefficientOuterCondition layout basis) basis) inside.1
  unfold historyP15CoefficientIterationCleanPredicate
  refine ⟨?_, ?_, ?_⟩
  · calc
      basis (historyEqualityFlag layout) =
          xorWire (historyCoefficientControl layout)
            (historyP15CoefficientOuterCondition layout basis) basis
            (historyEqualityFlag layout) := by
              symm
              exact xorWire_apply_other (historyCoefficientControl layout)
                (historyEqualityFlag layout)
                (historyP15CoefficientControl_ne_equalityFlag layout).symm _ basis
      _ = false := restoredClean.2.2.1
  · intro wire member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨index, rfl⟩
    calc
      basis ((historyEqualityWork layout).wire index) =
          xorWire (historyCoefficientControl layout)
            (historyP15CoefficientOuterCondition layout basis) basis
            ((historyEqualityWork layout).wire index) := by
              symm
              exact xorWire_apply_other (historyCoefficientControl layout)
                ((historyEqualityWork layout).wire index)
                (historyP15CoefficientControl_ne_equalityWork layout index).symm _ basis
      _ = false := restoredClean.2.2.2 _ (by
        simp [historyRegisterWires])
  · calc
      basis (historyActiveWire layout) =
          xorWire (historyCoefficientControl layout)
            (historyP15CoefficientOuterCondition layout basis) basis
            (historyActiveWire layout) := by
              symm
              exact xorWire_apply_other (historyCoefficientControl layout)
                (historyActiveWire layout)
                (historyP15Active_ne_coefficientControl layout) _ basis
      _ = false := restoredClean.2.1

private theorem historyP15CoefficientLoopComputedPredicate_stableOutsideSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (before after : QubitBasis qubits)
    (inside : historyP15CoefficientLoopComputedPredicate
      (layout := layout) widths before)
    (sameOutside : forall wire, wire ≠ layout.coefficientSignal ->
      after wire = before wire) :
    historyP15CoefficientLoopComputedPredicate (layout := layout) widths after := by
  have conditionEqual : historyP15CoefficientOuterCondition layout after =
      historyP15CoefficientOuterCondition layout before :=
    historyP15CoefficientOuterCondition_signalInvariant layout after before
      (by
        intro wire different
        exact sameOutside wire different)
  constructor
  · apply historyP15PostQ10StablePredicate_of_agreesOutsideCoefficientSignal
      layout widths
      (xorWire (historyCoefficientControl layout)
        (historyP15CoefficientOuterCondition layout before) before)
      (xorWire (historyCoefficientControl layout)
        (historyP15CoefficientOuterCondition layout after) after) inside.1
    intro wire different
    by_cases isControl : wire = historyCoefficientControl layout
    · subst wire
      rw [xorWire_apply_same, xorWire_apply_same, conditionEqual,
        sameOutside (historyCoefficientControl layout)
          (historyP15CoefficientControl_ne_coefficientSignal layout)]
    · rw [xorWire_apply_other (historyCoefficientControl layout) wire isControl _ after,
        xorWire_apply_other (historyCoefficientControl layout) wire isControl _ before,
        sameOutside wire different]
  · calc
      after (historyCoefficientControl layout) =
          before (historyCoefficientControl layout) :=
        sameOutside _ (historyP15CoefficientControl_ne_coefficientSignal layout)
      _ = historyP15CoefficientOuterCondition layout before := inside.2
      _ = historyP15CoefficientOuterCondition layout after := conditionEqual.symm

private theorem historyP15CoefficientLoopOperator_preservesOutside
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    OperatorPreservesOutside {layout.coefficientSignal}
      (historyP15CoefficientLoopOperator layout angles) := by
  unfold historyP15CoefficientLoopOperator
  apply OperatorPreservesOutside.operatorSequence_of_forall
    {layout.coefficientSignal}
  intro operator member
  simp only [List.mem_map] at member
  rcases member with ⟨index, _, rfl⟩
  exact OperatorPreservesOutside.predicateControlledSingleQubitOperator _
    layout.coefficientSignal _

private noncomputable def historyP15CoefficientLoopComputedComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  let loop := historyP15CoefficientLoopComponent layout angles
  SubspaceMapComponent.ofBasisSpan (historyP15PostGate (qubits := qubits))
    loop.circuit (historyP15CoefficientLoopOperator layout angles)
    (historyP15CoefficientLoopComputedPredicate (layout := layout) widths)
    (historyP15CoefficientLoopComputedPredicate (layout := layout) widths)
    (by
      intro input inside
      calc
        applyOperator (Circuit.denote (historyP15PostGate (qubits := qubits))
            loop.circuit) (basisKet input) =
            applyOperator loop.target (basisKet input) :=
          loop.correct _ (SubspaceMapComponent.basisKet_mem_basisSpan
            (historyP15CoefficientLoopComputedPredicate_implies_iterationClean
              widths input inside))
        _ = applyOperator (historyP15CoefficientLoopOperator layout angles)
            (basisKet input) := by
          change applyOperator
              (historyP15CoefficientLoopComponent layout angles).target
              (basisKet input) = _
          rw [historyP15CoefficientLoopComponent_target])
    (by
      intro input inside
      apply SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_preservesOutside
        (historyP15CoefficientLoopOperator layout angles)
        {layout.coefficientSignal}
        (historyP15CoefficientLoopOperator_preservesOutside layout angles)
        (historyP15CoefficientLoopComputedPredicate (layout := layout) widths)
        (historyP15CoefficientLoopComputedPredicate (layout := layout) widths)
        (by
          intro before after beforeInside sameOutside
          apply historyP15CoefficientLoopComputedPredicate_stableOutsideSignal
            widths before after beforeInside
          intro wire different
          exact sameOutside wire (by simpa using different)) input inside)

private theorem historyP15CoefficientLoopComputedComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    (historyP15CoefficientLoopComputedComponent layout widths angles).target =
      historyP15CoefficientLoopOperator layout angles := rfl

private theorem historyP15CoefficientLoopComputedComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    (historyP15CoefficientLoopComputedComponent layout widths angles).circuit =
      (historyP15CoefficientLoopComponent layout angles).circuit := rfl

private theorem historyP15CoefficientOuterConjunctionLayout_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ([historyBranchWire layout, historyLessThanTimeWire layout] ++ [] ++
      [historyCoefficientControl layout]).Nodup := by
  simp [historyBranchWire_ne_lessThanTimeWire layout,
    (historyP15IdleCoefficientControl_ne_branch layout).symm,
    (historyP15IdleCoefficientControl_ne_lessThanTime layout).symm]

private noncomputable def historyP15CoefficientOuterComputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyBranchWire layout, historyLessThanTimeWire layout] []
    (historyCoefficientControl layout) (by simp)
    (historyP15CoefficientOuterConjunctionLayout_nodup layout)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (historyP15CoefficientLoopComputedPredicate (layout := layout) widths)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input stable
      let action := ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyCoefficientControl layout)
      have actionEq : action input = xorWire (historyCoefficientControl layout)
          (historyP15CoefficientOuterCondition layout input) input := by
        unfold action ClassicalReversibleStage.conjunctionDirectBasisAction
        rw [historyP15CoefficientOuterCondition_eq_allWiresTrue]
      have conditionAfterCompute : historyP15CoefficientOuterCondition layout
          (xorWire (historyCoefficientControl layout)
            (historyP15CoefficientOuterCondition layout input) input) =
          historyP15CoefficientOuterCondition layout input :=
        historyP15CoefficientOuterCondition_controlInvariant layout _ _
          (historyP15XorComputeAction_agreesExcept_control
            (historyCoefficientControl layout)
            (historyP15CoefficientOuterCondition layout) input)
      constructor
      · rw [show xorWire (historyCoefficientControl layout)
            (historyP15CoefficientOuterCondition layout (action input))
            (action input) = input by
              rw [actionEq, conditionAfterCompute]
              exact xorWire_involutive (historyCoefficientControl layout)
                (historyP15CoefficientOuterCondition layout input) input]
        exact stable
      · have controlClean :=
          (historyP15PostQ10StablePredicate_implies_idleCoefficientClean
            layout widths input stable).2
        have directActionEq :
            ClassicalReversibleStage.conjunctionDirectBasisAction
              [historyBranchWire layout, historyLessThanTimeWire layout]
              (historyCoefficientControl layout) input =
              xorWire (historyCoefficientControl layout)
                (historyP15CoefficientOuterCondition layout input) input := by
          simpa [action] using actionEq
        rw [directActionEq, xorWire_apply_same, controlClean, conditionAfterCompute]
        cases historyP15CoefficientOuterCondition layout input <;> rfl)

private noncomputable def historyP15CoefficientOuterUncomputeComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyBranchWire layout, historyLessThanTimeWire layout] []
    (historyCoefficientControl layout) (by simp)
    (historyP15CoefficientOuterConjunctionLayout_nodup layout)
    (historyP15CoefficientLoopComputedPredicate (layout := layout) widths)
    (historyP15PostQ10StablePredicate (layout := layout) widths)
    (by simp [ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input inside
      change historyP15PostQ10StablePredicate (layout := layout) widths
        (xorWire (historyCoefficientControl layout)
          (ClassicalReversibleStage.allWiresTrue
            [historyBranchWire layout, historyLessThanTimeWire layout] input) input)
      rw [historyP15CoefficientOuterCondition_eq_allWiresTrue]
      exact inside.1)

private theorem historyP15CoefficientOuterComputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15CoefficientOuterComputeComponent layout widths).target =
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyCoefficientControl layout) := rfl

private theorem historyP15CoefficientOuterUncomputeComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15CoefficientOuterUncomputeComponent layout widths).target =
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyCoefficientControl layout) := rfl

private theorem historyP15CoefficientOuterComputeComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15CoefficientOuterComputeComponent layout widths).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyLessThanTimeWire layout] []
        (historyCoefficientControl layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyCoefficientControl layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

private theorem historyP15CoefficientOuterUncomputeComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15CoefficientOuterUncomputeComponent layout widths).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyLessThanTimeWire layout] []
        (historyCoefficientControl layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyCoefficientControl layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

private theorem historyP15TaylorCoefficientChain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    SubspaceMapComponent.SpaceChain
      [historyP15CoefficientOuterComputeComponent layout widths,
       historyP15CoefficientLoopComputedComponent layout widths angles,
       historyP15CoefficientOuterUncomputeComponent layout widths]
      (SubspaceMapComponent.basisSpan
        (historyP15PostQ10StablePredicate (layout := layout) widths))
      (SubspaceMapComponent.basisSpan
        (historyP15PostQ10StablePredicate (layout := layout) widths)) := by
  exact .cons _ [_, _] _ _ _ rfl rfl
    (.cons _ [_] _ _ _ rfl rfl
      (.cons _ [] _ _ _ rfl rfl (.nil _)))

private noncomputable def historyP15TaylorCoefficientRawComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :=
  SubspaceMapComponent.sequenceAlong
    (historyP15TaylorCoefficientChain layout widths angles)

/-- The clean analytic target of the literal outer-control and finite-loop
source word.  It is deliberately a source-order product: equality with the
whole-space loop target is neither claimed nor needed outside the clean span. -/
noncomputable def historyP15TaylorCoefficientOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (_widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    Operator (QubitBasis qubits) :=
  operatorSequence
    [ClassicalReversibleStage.conjunctionDirectOperator
       [historyBranchWire layout, historyLessThanTimeWire layout]
       (historyCoefficientControl layout),
     historyP15CoefficientLoopOperator layout angles,
     ClassicalReversibleStage.conjunctionDirectOperator
       [historyBranchWire layout, historyLessThanTimeWire layout]
       (historyCoefficientControl layout)]

/-- The source-faithful Taylor coefficient group: materialize the outer
control, execute the increasing-index coefficient loop, then restore it. -/
noncomputable def historyP15TaylorCoefficientComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  (historyP15TaylorCoefficientRawComponent layout widths angles).refineTarget
    (historyP15TaylorCoefficientOperator layout widths angles)
    (by
      rw [show (historyP15TaylorCoefficientRawComponent layout widths angles).target =
          (SubspaceMapComponent.sequenceAlong
            (historyP15TaylorCoefficientChain layout widths angles)).target by rfl,
        SubspaceMapComponent.sequenceAlong_target]
      simp only [List.map_cons, List.map_nil]
      rw [historyP15CoefficientOuterComputeComponent_target,
        historyP15CoefficientLoopComputedComponent_target,
        historyP15CoefficientOuterUncomputeComponent_target]
      rfl)

@[simp] theorem historyP15TaylorCoefficientComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    (historyP15TaylorCoefficientComponent layout widths angles).target =
      historyP15TaylorCoefficientOperator layout widths angles := rfl

@[simp] theorem historyP15TaylorCoefficientComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    (historyP15TaylorCoefficientComponent layout widths angles).inputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) /\
      (historyP15TaylorCoefficientComponent layout widths angles).outputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10StablePredicate (layout := layout) widths) := by
  constructor <;> rfl

noncomputable def historyP15TaylorCoefficientSourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (_widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    List (Circuit (PrimitiveGate qubits)) :=
  [(ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyCoefficientControl layout)).compile,
   historyP15CoefficientLoopSourceCircuit layout angles,
   (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyCoefficientControl layout)).compile]

noncomputable def historyP15TaylorCoefficientSourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence (historyP15TaylorCoefficientSourceStages layout widths angles)

private theorem historyP15TaylorCoefficientRawComponent_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    (historyP15TaylorCoefficientRawComponent layout widths angles).circuit =
      Circuit.sequence
        [(historyP15CoefficientOuterComputeComponent layout widths).circuit,
         (historyP15CoefficientLoopComputedComponent layout widths angles).circuit,
         (historyP15CoefficientOuterUncomputeComponent layout widths).circuit] := rfl

@[simp] theorem historyP15TaylorCoefficientComponent_circuit_eq_raw
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    (historyP15TaylorCoefficientComponent layout widths angles).circuit =
      (historyP15TaylorCoefficientRawComponent layout widths angles).circuit := rfl

theorem historyP15TaylorCoefficientComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    (historyP15TaylorCoefficientComponent layout widths angles).circuit.flatten =
      (historyP15TaylorCoefficientSourceCircuit layout widths angles).flatten := by
  rw [historyP15TaylorCoefficientComponent_circuit_eq_raw,
    historyP15TaylorCoefficientRawComponent_circuit,
    historyP15CoefficientOuterComputeComponent_circuit,
    historyP15CoefficientLoopComputedComponent_circuit,
    historyP15CoefficientOuterUncomputeComponent_circuit]
  simp only [Circuit.flatten_sequence, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [historyP15CoefficientLoopComponent_flatten_eq_source]
  simp [historyP15TaylorCoefficientSourceCircuit,
    historyP15TaylorCoefficientSourceStages, Circuit.flatten]

/-! ### Whole P15 post-Q10 sequence

The following eight-child chain is deliberately kept separate from the
through-Q10 checkpoint: its input is the actual post-Q10/before-generator
boundary, not the H2 entrance.  Each child is retained in the frozen source
order, including the outer Taylor-coefficient conjunction pair.
-/

/-- The concrete entry boundary of the eight post-Q10 source groups. -/
def historyP15PostQ10CleanInputPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (basis : QubitBasis qubits) : Prop :=
  historyP15PostQ10OutputPredicate (layout := layout) widths basis /\
    historyTaylorBeforeGeneratorBoundaryPredicate layout basis

/-- Literal source circuit for the single post-Q10 P43 active restoration. -/
noncomputable def historyP15RestoreGeneratorActiveSourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (_widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    Circuit (PrimitiveGate qubits) :=
  (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
    [historyBranchWire layout, historyLessThanTimeWire layout] []
    (historyActiveWire layout)).compile

private theorem historyP15RestoreGeneratorActiveComponent_circuit_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreGeneratorActiveComponent layout widths).circuit =
      historyP15RestoreGeneratorActiveSourceCircuit layout widths := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyActiveWire layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

theorem historyP15RestoreGeneratorActiveComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreGeneratorActiveComponent layout widths).circuit.flatten =
      (historyP15RestoreGeneratorActiveSourceCircuit layout widths).flatten := by
  rw [historyP15RestoreGeneratorActiveComponent_circuit_eq_source]

/-- Literal X--Toffoli--X source circuit for the invalid-clock group. -/
noncomputable def historyP15InvalidClockSourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence ((historyP15InvalidClockStages layout evidence).map
    (fun stage => stage.component.circuit))

private theorem historyP15InvalidClockComponent_circuit_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15InvalidClockComponent layout evidence widths).circuit =
      historyP15InvalidClockSourceCircuit layout evidence := by
  rfl

theorem historyP15InvalidClockComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15InvalidClockComponent layout evidence widths).circuit.flatten =
      (historyP15InvalidClockSourceCircuit layout evidence).flatten := by
  rw [historyP15InvalidClockComponent_circuit_eq_source]

/-- The eight independently reviewed P15 post-Q10 components in literal
source order. -/
noncomputable def historyP15PostQ10Components
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) (idleAngle : AngleExpr) :
    List (SubspaceMapComponent (historyP15PostGate (qubits := qubits))) :=
  [historyP15RestoreGeneratorActiveComponent layout widths,
   historyP15InvalidClockComponent layout evidence widths,
   historyP15OrderBoundaryComponent layout widths,
   historyP15IdleBoundaryComponent layout widths,
   historyP15DegreeIncrementComponent layout widths,
   historyP15TaylorCoefficientComponent layout widths angles,
   historyP15IdleCoefficientComponent layout widths idleAngle,
   historyP15RestoreEntryFlagsComponent layout evidence widths]

theorem historyP15PostQ10Components_chain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) (idleAngle : AngleExpr) :
    SubspaceMapComponent.SpaceChain
      (historyP15PostQ10Components layout evidence widths angles idleAngle)
      (SubspaceMapComponent.basisSpan
        (historyP15PostQ10CleanInputPredicate (layout := layout) widths))
      (SubspaceMapComponent.basisSpan
        (historyP15PostQ10CleanOutputPredicate (layout := layout) widths)) := by
  have restoreSpaces := historyP15RestoreGeneratorActiveComponent_spaces
    layout widths
  have invalidSpaces := historyP15InvalidClockComponent_spaces layout evidence widths
  have orderSpaces := historyP15OrderBoundaryComponent_spaces layout widths
  have idleBoundarySpaces := historyP15IdleBoundaryComponent_spaces layout widths
  have degreeSpaces := historyP15DegreeIncrementComponent_spaces layout widths
  have coefficientSpaces := historyP15TaylorCoefficientComponent_spaces
    layout widths angles
  have idleCoefficientSpaces := historyP15IdleCoefficientComponent_spaces
    layout widths idleAngle
  have restoreEntrySpaces := historyP15RestoreEntryFlagsComponent_spaces
    layout evidence widths
  have chain : SubspaceMapComponent.SpaceChain
      [historyP15RestoreGeneratorActiveComponent layout widths,
       historyP15InvalidClockComponent layout evidence widths,
       historyP15OrderBoundaryComponent layout widths,
       historyP15IdleBoundaryComponent layout widths,
       historyP15DegreeIncrementComponent layout widths,
       historyP15TaylorCoefficientComponent layout widths angles,
       historyP15IdleCoefficientComponent layout widths idleAngle,
       historyP15RestoreEntryFlagsComponent layout evidence widths]
      (SubspaceMapComponent.basisSpan
        (fun basis => historyP15PostQ10OutputPredicate (layout := layout)
          widths basis /\ historyTaylorBeforeGeneratorBoundaryPredicate layout basis))
      (SubspaceMapComponent.basisSpan
        (historyP15PostQ10CleanOutputPredicate (layout := layout) widths)) := by
    exact .cons _ [_, _, _, _, _, _, _] _ _ _ restoreSpaces.1 restoreSpaces.2
      (.cons _ [_, _, _, _, _, _] _ _ _ invalidSpaces.1 invalidSpaces.2
        (.cons _ [_, _, _, _, _] _ _ _ orderSpaces.1 orderSpaces.2
          (.cons _ [_, _, _, _] _ _ _ idleBoundarySpaces.1 idleBoundarySpaces.2
            (.cons _ [_, _, _] _ _ _ degreeSpaces.1 degreeSpaces.2
              (.cons _ [_, _] _ _ _ coefficientSpaces.1 coefficientSpaces.2
                (.cons _ [_] _ _ _ idleCoefficientSpaces.1 idleCoefficientSpaces.2
                  (.cons _ [] _ _ _ restoreEntrySpaces.1 restoreEntrySpaces.2
                    (.nil _))))))))
  change SubspaceMapComponent.SpaceChain
      [historyP15RestoreGeneratorActiveComponent layout widths,
       historyP15InvalidClockComponent layout evidence widths,
       historyP15OrderBoundaryComponent layout widths,
       historyP15IdleBoundaryComponent layout widths,
       historyP15DegreeIncrementComponent layout widths,
       historyP15TaylorCoefficientComponent layout widths angles,
       historyP15IdleCoefficientComponent layout widths idleAngle,
       historyP15RestoreEntryFlagsComponent layout evidence widths]
      (SubspaceMapComponent.basisSpan
        (fun basis => historyP15PostQ10OutputPredicate (layout := layout)
          widths basis /\ historyTaylorBeforeGeneratorBoundaryPredicate layout basis))
      (SubspaceMapComponent.basisSpan
        (historyP15PostQ10CleanOutputPredicate (layout := layout) widths))
  exact chain

/-- Source-order analytic target of all eight post-Q10 groups. -/
noncomputable def historyP15PostQ10CleanOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) (idleAngle : AngleExpr) :
    Operator (QubitBasis qubits) :=
  operatorSequence
    [(historyP15RestoreGeneratorActiveComponent layout widths).target,
     (historyP15InvalidClockComponent layout evidence widths).target,
     (historyP15OrderBoundaryComponent layout widths).target,
     (historyP15IdleBoundaryComponent layout widths).target,
     (historyP15DegreeIncrementComponent layout widths).target,
     (historyP15TaylorCoefficientComponent layout widths angles).target,
     (historyP15IdleCoefficientComponent layout widths idleAngle).target,
     (historyP15RestoreEntryFlagsComponent layout evidence widths).target]

/-- Complete clean component for the source region following Q10. -/
noncomputable def historyP15PostQ10CleanComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) (idleAngle : AngleExpr) :
    SubspaceMapComponent (historyP15PostGate (qubits := qubits)) :=
  (SubspaceMapComponent.sequenceAlong
    (historyP15PostQ10Components_chain layout evidence widths angles idleAngle)).refineTarget
      (historyP15PostQ10CleanOperator layout evidence widths angles idleAngle)
      (by
        rw [SubspaceMapComponent.sequenceAlong_target]
        rfl)

@[simp] theorem historyP15PostQ10CleanComponent_target
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) (idleAngle : AngleExpr) :
    (historyP15PostQ10CleanComponent layout evidence widths angles idleAngle).target =
      historyP15PostQ10CleanOperator layout evidence widths angles idleAngle := rfl

@[simp] theorem historyP15PostQ10CleanComponent_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) (idleAngle : AngleExpr) :
    (historyP15PostQ10CleanComponent layout evidence widths angles idleAngle).inputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10CleanInputPredicate (layout := layout) widths) /\
      (historyP15PostQ10CleanComponent layout evidence widths angles idleAngle).outputSubspace =
        SubspaceMapComponent.basisSpan
          (historyP15PostQ10CleanOutputPredicate (layout := layout) widths) := by
  constructor <;> rfl

/-- The eight literal group circuits, nested in their exact source order. -/
noncomputable def historyP15PostQ10SourceStages
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) (idleAngle : AngleExpr) :
    List (Circuit (PrimitiveGate qubits)) :=
  [historyP15RestoreGeneratorActiveSourceCircuit layout widths,
   historyP15InvalidClockSourceCircuit layout evidence,
   historyP15OrderBoundarySourceCircuit layout,
   historyP15IdleBoundarySourceCircuit layout,
   historyP15DegreeIncrementSourceCircuit layout,
   historyP15TaylorCoefficientSourceCircuit layout widths angles,
   historyP15IdleCoefficientSourceCircuit layout idleAngle,
   historyP15RestoreEntryFlagsSourceCircuit layout evidence widths]

noncomputable def historyP15PostQ10SourceCircuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) (idleAngle : AngleExpr) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence
    (historyP15PostQ10SourceStages layout evidence widths angles idleAngle)

theorem historyP15PostQ10CleanComponent_flatten_eq_source
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → AngleExpr) (idleAngle : AngleExpr) :
    (historyP15PostQ10CleanComponent layout evidence widths angles idleAngle).circuit.flatten =
      (historyP15PostQ10SourceCircuit layout evidence widths angles idleAngle).flatten := by
  change (Circuit.sequence
      ((historyP15PostQ10Components layout evidence widths angles idleAngle).map
        (fun component => component.circuit))).flatten = _
  unfold historyP15PostQ10Components
  simp only [List.map_cons, List.map_nil, Circuit.flatten_sequence,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [historyP15RestoreGeneratorActiveComponent_flatten_eq_source,
    historyP15InvalidClockComponent_flatten_eq_source,
    historyP15OrderBoundaryComponent_flatten_eq_source,
    historyP15IdleBoundaryComponent_flatten_eq_source,
    historyP15DegreeIncrementComponent_flatten_eq_source,
    historyP15TaylorCoefficientComponent_flatten_eq_source,
    historyP15IdleCoefficientComponent_flatten_eq_source,
    historyP15RestoreEntryFlagsComponent_flatten_eq_source]
  simp [historyP15PostQ10SourceCircuit, historyP15PostQ10SourceStages,
    Circuit.flatten]

/-! ProviderIntegration proof-only circuit projections.

These aliases expose already-proved circuit equalities without changing any
component, target, predicate, or source word.  The overlay is SHA-guarded and
can be rolled back by removing this additive block. -/

set_option linter.defProp false

noncomputable def providerIntegration_orderBoundaryLessThanSpec
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15OrderBoundaryLessThanSpec layout

def providerIntegration_orderDegreeLessCompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryDegreeLessComputeComponent layout).circuit =
      (historyLessThanConstantExactComponent
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
        (providerIntegration_orderBoundaryLessThanSpec layout)
        parameters.taylorOrder).circuit := by
  rfl

def providerIntegration_orderDegreeLessUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryDegreeLessUncomputeComponent layout).circuit =
      (historyLessThanConstantExactComponent
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
        (providerIntegration_orderBoundaryLessThanSpec layout)
        parameters.taylorOrder).circuit := by
  rfl

def providerIntegration_orderActiveCompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryActiveComputeComponent layout).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyLessThanTimeWire layout] []
        (historyActiveWire layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyActiveWire layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_orderActiveUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryActiveUncomputeComponent layout).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyLessThanTimeWire layout] []
        (historyActiveWire layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyLessThanTimeWire layout] []
      (historyActiveWire layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_idleBoundaryActiveCompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryActiveComputeComponent layout).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyIdleFlag layout] []
        (historyActiveWire layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyIdleFlag layout] []
      (historyActiveWire layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_idleBoundaryActiveUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryActiveUncomputeComponent layout).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyIdleFlag layout] []
        (historyActiveWire layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyIdleFlag layout] []
      (historyActiveWire layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_idleBoundaryEqualityCompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryEqualityComputeComponent layout).circuit =
      (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
        (historyRegisterWires layout.order)
        (historyRegisterWires (historyEqualityWork layout))
        (historyIdleBlockSize parameters.taylorOrder - 1)
        (historyEqualityFlag layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
      (historyRegisterWires layout.order)
      (historyRegisterWires (historyEqualityWork layout))
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_idleBoundaryEqualityUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryEqualityUncomputeComponent layout).circuit =
      (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
        (historyRegisterWires layout.order)
        (historyRegisterWires (historyEqualityWork layout))
        (historyIdleBlockSize parameters.taylorOrder - 1)
        (historyEqualityFlag layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
      (historyRegisterWires layout.order)
      (historyRegisterWires (historyEqualityWork layout))
      (historyIdleBlockSize parameters.taylorOrder - 1)
      (historyEqualityFlag layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_coefficientEqualityCompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) :
    (historyP15CoefficientIterationEqualityComputeComponent layout index).circuit =
      (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
        (historyRegisterWires layout.order)
        (historyRegisterWires (historyEqualityWork layout))
        (index.val + 1) (historyEqualityFlag layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
      (historyRegisterWires layout.order)
      (historyRegisterWires (historyEqualityWork layout))
      (index.val + 1) (historyEqualityFlag layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_coefficientEqualityUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder) :
    (historyP15CoefficientIterationEqualityUncomputeComponent layout index).circuit =
      (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
        (historyRegisterWires layout.order)
        (historyRegisterWires (historyEqualityWork layout))
        (index.val + 1) (historyEqualityFlag layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
      (historyRegisterWires layout.order)
      (historyRegisterWires (historyEqualityWork layout))
      (index.val + 1) (historyEqualityFlag layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_coefficientActiveCompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (different : historyActiveWire layout ≠ historyEqualityFlag layout) :
    (historyP15CoefficientIterationComputeComponent layout different).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyCoefficientControl layout, historyEqualityFlag layout] []
        (historyActiveWire layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyCoefficientControl layout, historyEqualityFlag layout] []
      (historyActiveWire layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_coefficientActiveUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (different : historyActiveWire layout ≠ historyEqualityFlag layout) :
    (historyP15CoefficientIterationUncomputeComponent layout different).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyCoefficientControl layout, historyEqualityFlag layout] []
        (historyActiveWire layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyCoefficientControl layout, historyEqualityFlag layout] []
      (historyActiveWire layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_coefficientUse_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (activeDifferent : historyActiveWire layout ≠ layout.coefficientSignal)
    (controlDifferent :
      historyCoefficientControl layout ≠ layout.coefficientSignal)
    (angle : AngleExpr) :
    (historyP15CoefficientIterationUseComponent layout activeDifferent
      controlDifferent angle).circuit =
      (historyClockCoefficientRotationExactComponent
        (historyActiveWire layout) layout.coefficientSignal
        activeDifferent angle).circuit := by
  rfl

def providerIntegration_idleCoefficientIdleEndToggle_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientIdleEndToggleComponent layout).circuit =
      (ClassicalReversibleStage.primitiveExactOperatorComponent
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
        (.instruction (.xorControlled
          (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm))).circuit := by
  rfl

def providerIntegration_idleCoefficientTimeToggle_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientTimeToggleComponent layout).circuit =
      (ClassicalReversibleStage.primitiveExactOperatorComponent
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
        (.instruction (.xorControlled
          (historyLessThanTimeWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanTime layout).symm))).circuit := by
  rfl

def providerIntegration_idleCoefficientTimeToggleUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientTimeToggleUncomputeComponent layout).circuit =
      (ClassicalReversibleStage.primitiveExactOperatorComponent
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
        (.instruction (.xorControlled
          (historyLessThanTimeWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanTime layout).symm))).circuit := by
  rfl

def providerIntegration_idleCoefficientIdleEndToggleUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientIdleEndToggleUncomputeComponent layout).circuit =
      (ClassicalReversibleStage.primitiveExactOperatorComponent
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
        (.instruction (.xorControlled
          (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
          (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm))).circuit := by
  rfl

def providerIntegration_idleCoefficientControlCompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientControlComputeComponent layout).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyIdleFlag layout] []
        (historyCoefficientControl layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyIdleFlag layout] []
      (historyCoefficientControl layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_idleCoefficientControlUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleCoefficientControlUncomputeComponent layout).circuit =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyIdleFlag layout] []
        (historyCoefficientControl layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyIdleFlag layout] []
      (historyCoefficientControl layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_idleCoefficientUse_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) :
    (historyP15IdleCoefficientUseComponent layout angle).circuit =
      (historyClockCoefficientRotationExactComponent
        (historyCoefficientControl layout) layout.coefficientSignal
        (historyP15CoefficientControl_ne_coefficientSignal layout) angle).circuit := by
  rfl

def providerIntegration_restoreIdleEnd_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsIdleEndComponent layout evidence widths).circuit =
      (historyLessThanConstantExactComponent
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
        evidence.clock.clockIdleEndLessThan.toSpec
        (historyIdleClockEnd parameters.timeSteps parameters.taylorOrder
          parameters.idlingSteps)).circuit := by
  rfl

def providerIntegration_restoreTime_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsTimeComponent layout evidence widths).circuit =
      (historyLessThanConstantExactComponent
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
        evidence.clock.clockTimeLessThan.toSpec parameters.timeSteps).circuit := by
  rfl

def providerIntegration_restoreSelector_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15RestoreEntryFlagsSelectorComponent layout widths).circuit =
      (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
        (historyRegisterWires layout.selector) [] 1
        (historyBranchWire layout)).compile := by
  change (ClassicalReversibleStage.primitiveExactOperatorComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
      (historyRegisterWires layout.selector) [] 1
      (historyBranchWire layout))).circuit = _
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_circuit _ _

def providerIntegration_invalidClockStages_circuit_list
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout) :
    (historyP15InvalidClockStages layout evidence).map
        (fun stage => stage.component.circuit) =
      [Circuit.gate (.x (historyLessThanIdleEndWire layout)),
       Circuit.gate (.toffoli
         (historyBranchWire layout) (historyLessThanIdleEndWire layout)
         layout.coefficientSignal evidence.branch_ne_ltIdleEnd
         evidence.branch_ne_coefficientSignal
         evidence.ltIdleEnd_ne_coefficientSignal),
       Circuit.gate (.x (historyLessThanIdleEndWire layout))] := by
  rfl

def providerIntegration_orderEqualityXCompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryEqualityXComputeComponent layout).circuit =
      Circuit.gate (.x (historyEqualityFlag layout)) := by
  rfl

def providerIntegration_orderEqualityXUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryEqualityXUncomputeComponent layout).circuit =
      Circuit.gate (.x (historyEqualityFlag layout)) := by
  rfl

def providerIntegration_orderToffoli_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15OrderBoundaryToffoliComponent layout).circuit =
      Circuit.gate (.toffoli
        (historyActiveWire layout) (historyEqualityFlag layout)
        layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
        (historyP15Active_ne_orderBoundarySignal layout)
        (historyP15EqualityFlag_ne_orderBoundarySignal layout)) := by
  rfl

def providerIntegration_idleBoundaryIdleEndToggle_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryIdleEndToggleComponent layout).circuit =
      Circuit.gate (.cnot (historyLessThanIdleEndWire layout)
        (historyIdleFlag layout) (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm) := by
  rfl

def providerIntegration_idleBoundaryTimeToggle_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryTimeToggleComponent layout).circuit =
      Circuit.gate (.cnot (historyLessThanTimeWire layout)
        (historyIdleFlag layout) (historyP15IdleFlag_ne_lessThanTime layout).symm) := by
  rfl

def providerIntegration_idleBoundaryToffoli_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryToffoliComponent layout).circuit =
      Circuit.gate (.toffoli
        (historyActiveWire layout) (historyEqualityFlag layout)
        layout.orderBoundarySignal (historyP15Active_ne_equalityFlag layout)
        (historyP15Active_ne_orderBoundarySignal layout)
        (historyP15EqualityFlag_ne_orderBoundarySignal layout)) := by
  rfl

def providerIntegration_idleBoundaryTimeToggleUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryTimeToggleUncomputeComponent layout).circuit =
      Circuit.gate (.cnot (historyLessThanTimeWire layout)
        (historyIdleFlag layout) (historyP15IdleFlag_ne_lessThanTime layout).symm) := by
  rfl

def providerIntegration_idleBoundaryIdleEndToggleUncompute_circuit
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyP15IdleBoundaryIdleEndToggleUncomputeComponent layout).circuit =
      Circuit.gate (.cnot (historyLessThanIdleEndWire layout)
        (historyIdleFlag layout) (historyP15IdleFlag_ne_lessThanIdleEnd layout).symm) := by
  rfl

noncomputable def providerIntegration_degreeIncrementSpec
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :=
  historyP15DegreeIncrementSpec layout

end

end SpectralSamplingProof.Components
