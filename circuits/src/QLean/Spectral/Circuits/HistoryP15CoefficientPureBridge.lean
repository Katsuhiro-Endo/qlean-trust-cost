import QLean.Spectral.Circuits.HistoryP15PostQ10Clean
import QLean.Circuits.Foundation.PrimitiveGateProofs

/-!
# P15 coefficient-loop / pure semantic bridge

This leaf identifies the source-faithful P15 coefficient group with the
pure branch-and-clock coefficient loop on the stable post-Q10 boundary.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

/-! ### Small clean-control algebra -/

private def historyP15CoefficientBridgeXorAction {qubits : Nat}
    (control : Fin qubits) (condition : QubitBasis qubits -> Bool)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire control (condition input) input

private theorem historyP15CoefficientBridgeXorAction_agreesExcept_control
    {qubits : Nat} (control : Fin qubits) (condition : QubitBasis qubits -> Bool)
    (input : QubitBasis qubits) :
    agreesExcept control
      (historyP15CoefficientBridgeXorAction control condition input) input := by
  intro wire different
  exact xorWire_apply_other control wire different _ input

private theorem historyP15CoefficientBridgeXorAction_condition_stable
    {qubits : Nat} (control : Fin qubits) (condition : QubitBasis qubits -> Bool)
    (controlIndependent : forall first second,
      agreesExcept control first second -> condition first = condition second)
    (input : QubitBasis qubits) :
    condition (historyP15CoefficientBridgeXorAction control condition input) =
      condition input := by
  apply controlIndependent
  exact historyP15CoefficientBridgeXorAction_agreesExcept_control
    control condition input

private theorem historyP15CoefficientBridgeXorAction_involutive
    {qubits : Nat} (control : Fin qubits) (condition : QubitBasis qubits -> Bool)
    (controlIndependent : forall first second,
      agreesExcept control first second -> condition first = condition second) :
    Function.Involutive
      (historyP15CoefficientBridgeXorAction control condition) := by
  intro input
  change xorWire control
    (condition (historyP15CoefficientBridgeXorAction control condition input))
    (historyP15CoefficientBridgeXorAction control condition input) = input
  rw [historyP15CoefficientBridgeXorAction_condition_stable control condition
    controlIndependent input]
  exact xorWire_involutive control (condition input) input

private noncomputable def historyP15CoefficientBridgeXorComputeGuardedUseUncompute
    {qubits : Nat} (control target : Fin qubits)
    (condition guard : QubitBasis qubits -> Bool)
    (localOperator : Matrix Bool Bool ℂ) : Operator (QubitBasis qubits) :=
  (deterministicOperator
      (historyP15CoefficientBridgeXorAction control condition) *
    predicateControlledSingleQubitOperator
      (fun basis => guard basis && basis control) target localOperator) *
    deterministicOperator
      (historyP15CoefficientBridgeXorAction control condition)

/-! This is the matrix-entry clean-control argument needed below.  The middle
gate may make a superposition on `target`; the proof therefore never replaces
it by a basis action. -/
private theorem historyP15CoefficientBridge_apply_xorCompute_guardedUseUncompute_basisKet
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (condition guard : QubitBasis qubits -> Bool)
    (localOperator : Matrix Bool Bool ℂ)
    (conditionControlIndependent : forall first second,
      agreesExcept control first second -> condition first = condition second)
    (conditionTargetIndependent : forall first second,
      agreesExcept target first second -> condition first = condition second)
    (guardControlIndependent : forall first second,
      agreesExcept control first second -> guard first = guard second)
    (input : QubitBasis qubits) (controlClean : input control = false) :
    applyOperator
        (historyP15CoefficientBridgeXorComputeGuardedUseUncompute
          control target condition guard localOperator)
        (basisKet input) =
      applyOperator
        (predicateControlledSingleQubitOperator
          (fun basis => guard basis && condition basis) target localOperator)
        (basisKet input) := by
  have actionInvolutive : Function.Involutive
      (historyP15CoefficientBridgeXorAction control condition) :=
    historyP15CoefficientBridgeXorAction_involutive control condition
      conditionControlIndependent
  have actionControl (state : QubitBasis qubits)
      (clean : state control = false) :
      historyP15CoefficientBridgeXorAction control condition state control =
        condition state := by
    unfold historyP15CoefficientBridgeXorAction
    rw [xorWire_apply_same, clean]
    cases condition state <;> rfl
  have actionTarget (state : QubitBasis qubits) :
      historyP15CoefficientBridgeXorAction control condition state target =
        state target := by
    unfold historyP15CoefficientBridgeXorAction
    exact xorWire_apply_other control target different.symm _ state
  funext output
  unfold historyP15CoefficientBridgeXorComputeGuardedUseUncompute
  rw [applyOperator_basisKet, applyOperator_basisKet]
  rw [deterministicOperator_eq_permMatrix_of_involutive
    (historyP15CoefficientBridgeXorAction control condition) actionInvolutive]
  rw [permMatrix_conjugate_operator_apply
    (involutiveBasisEquiv
      (historyP15CoefficientBridgeXorAction control condition) actionInvolutive)
    (by rfl)]
  change predicateControlledSingleQubitOperator
      (fun basis => guard basis && basis control) target localOperator
      (historyP15CoefficientBridgeXorAction control condition output)
      (historyP15CoefficientBridgeXorAction control condition input) =
    predicateControlledSingleQubitOperator
      (fun basis => guard basis && condition basis) target localOperator output input
  rw [predicateControlledSingleQubitOperator_apply,
    predicateControlledSingleQubitOperator_apply]
  by_cases originalAgreement : agreesExcept target output input
  · have conditionAgreement : condition output = condition input :=
      conditionTargetIndependent output input originalAgreement
    have transformedAgreement : agreesExcept target
        (historyP15CoefficientBridgeXorAction control condition output)
        (historyP15CoefficientBridgeXorAction control condition input) := by
      intro wire wireDifferent
      by_cases wireControl : wire = control
      · subst wire
        rw [actionControl output (by
          have controlEqual := originalAgreement control different
          simpa [controlEqual] using controlClean),
          actionControl input controlClean, conditionAgreement]
      · rw [show historyP15CoefficientBridgeXorAction control condition output wire =
            output wire by
            unfold historyP15CoefficientBridgeXorAction
            exact xorWire_apply_other control wire wireControl _ output,
          show historyP15CoefficientBridgeXorAction control condition input wire =
            input wire by
            unfold historyP15CoefficientBridgeXorAction
            exact xorWire_apply_other control wire wireControl _ input]
        exact originalAgreement wire wireDifferent
    have guardCompute :
        guard (historyP15CoefficientBridgeXorAction control condition input) =
          guard input :=
      guardControlIndependent _ _
        (historyP15CoefficientBridgeXorAction_agreesExcept_control
          control condition input)
    rw [if_pos transformedAgreement, if_pos originalAgreement,
      guardCompute, actionControl input controlClean,
      actionTarget output, actionTarget input]
  · have transformedDisagreement : ¬ agreesExcept target
        (historyP15CoefficientBridgeXorAction control condition output)
        (historyP15CoefficientBridgeXorAction control condition input) := by
      intro transformedAgreement
      apply originalAgreement
      have conditionOutputCompute :
          condition (historyP15CoefficientBridgeXorAction control condition output) =
            condition output :=
        historyP15CoefficientBridgeXorAction_condition_stable control condition
          conditionControlIndependent output
      have conditionInputCompute :
          condition (historyP15CoefficientBridgeXorAction control condition input) =
            condition input :=
        historyP15CoefficientBridgeXorAction_condition_stable control condition
          conditionControlIndependent input
      have conditionAgreement : condition output = condition input := by
        rw [← conditionOutputCompute, ← conditionInputCompute]
        exact conditionTargetIndependent _ _ transformedAgreement
      intro wire wireDifferent
      by_cases wireControl : wire = control
      · subst wire
        have controlOutputClean : output control = false := by
          have controlEqual := transformedAgreement control different
          unfold historyP15CoefficientBridgeXorAction at controlEqual
          rw [xorWire_apply_same, xorWire_apply_same, controlClean,
            ← conditionAgreement] at controlEqual
          cases hOutput : output control <;>
          cases hCondition : condition input <;>
          simp [hOutput] at controlEqual ⊢
        exact controlOutputClean.trans controlClean.symm
      · have equal := transformedAgreement wire wireDifferent
        rw [show historyP15CoefficientBridgeXorAction control condition output wire =
              output wire by
              unfold historyP15CoefficientBridgeXorAction
              exact xorWire_apply_other control wire wireControl _ output,
            show historyP15CoefficientBridgeXorAction control condition input wire =
              input wire by
              unfold historyP15CoefficientBridgeXorAction
              exact xorWire_apply_other control wire wireControl _ input] at equal
        exact equal
    simp [transformedDisagreement, originalAgreement]

/-! ### Stable-boundary observations used by the coefficient bridge -/

private theorem historyP15CoefficientBridge_generatorWork_clean
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

private theorem historyP15CoefficientBridge_stable_workspace_zero
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
    exact historyP15CoefficientBridge_generatorWork_clean layout widths input inside.1 index
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

private theorem historyP15CoefficientBridge_sharedPool_ge_five
    (parameters : HistoryBlockParameters) (generatorWorkWidth : Nat) :
    5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
  unfold historySharedPoolWidth historyStructuralPoolWidth
  omega

private theorem historyP15CoefficientBridge_control_ne_branch
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
  have sharedAtLeast := historyP15CoefficientBridge_sharedPool_ge_five
    parameters generatorWorkWidth
  omega

private theorem historyP15CoefficientBridge_control_ne_time
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
  have sharedAtLeast := historyP15CoefficientBridge_sharedPool_ge_five
    parameters generatorWorkWidth
  omega

private theorem historyP15CoefficientBridge_control_ne_idleEnd
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
  have sharedAtLeast := historyP15CoefficientBridge_sharedPool_ge_five
    parameters generatorWorkWidth
  omega

private theorem historyP15CoefficientBridge_control_not_liveFlags
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ∉
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] := by
  intro member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal
  · exact historyP15CoefficientBridge_control_ne_branch layout equal
  · exact historyP15CoefficientBridge_control_ne_time layout equal
  · exact historyP15CoefficientBridge_control_ne_idleEnd layout equal

theorem historyP15PostQ10StablePredicate_coefficientControl_zero
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
    input (historyCoefficientControl layout) = false := by
  unfold historyCoefficientControl
  apply historyP15CoefficientBridge_stable_workspace_zero layout widths input inside
  exact historyP15CoefficientBridge_control_not_liveFlags layout

private def historyP15CoefficientBridgeOuterCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  ClassicalReversibleStage.allWiresTrue
    [historyBranchWire layout, historyLessThanTimeWire layout] basis

private theorem historyP15CoefficientBridge_control_ne_signal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ≠ layout.coefficientSignal := by
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  change layout.workspace.wire _ ≠ layout.coefficientSignal
  exact separated.2.2 _

private theorem historyP15CoefficientBridge_branch_ne_signal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyBranchWire layout ≠ layout.coefficientSignal := by
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  rcases List.mem_ofFn.mp (historyBranchWire_mem_workspace layout) with
    ⟨index, equal⟩
  exact fun same => separated.2.2 index (equal.trans same)

private theorem historyP15CoefficientBridge_time_ne_signal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyLessThanTimeWire layout ≠ layout.coefficientSignal := by
  have separated := layout.postGeneratorSignal_separated layout.coefficientSignal
    (by simp)
  rcases List.mem_ofFn.mp (historyLessThanTimeWire_mem_workspace layout) with
    ⟨index, equal⟩
  exact fun same => separated.2.2 index (equal.trans same)

private theorem historyP15CoefficientBridge_control_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyCoefficientControl layout ∈ historyRegisterWires layout.workspace := by
  unfold historyCoefficientControl
  apply historyWorkspaceSlice_wire_mem

private theorem historyP15CoefficientBridge_order_ne_control
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire index ≠ historyCoefficientControl layout := by
  rcases List.mem_ofFn.mp
      (historyP15CoefficientBridge_control_mem_workspace layout) with
    ⟨workspaceIndex, equal⟩
  exact fun same => (layout.orderWire_separated index).2.2.2 workspaceIndex
    (same.trans equal.symm)

private theorem historyP15CoefficientBridge_outer_condition_controlInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyCoefficientControl layout) first second) :
    historyP15CoefficientBridgeOuterCondition layout first =
      historyP15CoefficientBridgeOuterCondition layout second := by
  unfold historyP15CoefficientBridgeOuterCondition
    ClassicalReversibleStage.allWiresTrue ClassicalReversibleStage.readWires
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true]
  rw [same (historyBranchWire layout)
    (historyP15CoefficientBridge_control_ne_branch layout).symm,
    same (historyLessThanTimeWire layout)
      (historyP15CoefficientBridge_control_ne_time layout).symm]

private theorem historyP15CoefficientBridge_outer_condition_signalInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (first second : QubitBasis qubits)
    (same : agreesExcept layout.coefficientSignal first second) :
    historyP15CoefficientBridgeOuterCondition layout first =
      historyP15CoefficientBridgeOuterCondition layout second := by
  unfold historyP15CoefficientBridgeOuterCondition
    ClassicalReversibleStage.allWiresTrue ClassicalReversibleStage.readWires
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true]
  rw [same (historyBranchWire layout)
    (historyP15CoefficientBridge_branch_ne_signal layout),
    same (historyLessThanTimeWire layout)
      (historyP15CoefficientBridge_time_ne_signal layout)]

private theorem historyP15CoefficientBridge_order_controlInvariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin parameters.taylorOrder)
    (first second : QubitBasis qubits)
    (same : agreesExcept (historyCoefficientControl layout) first second) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order) (index.val + 1) first =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1) second := by
  apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
  intro wire member
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨orderIndex, rfl⟩
  exact same _ (historyP15CoefficientBridge_order_ne_control layout orderIndex)

private theorem historyP15CoefficientBridge_signalFiber_stable
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input state : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input)
    (same : agreesExcept layout.coefficientSignal state input) :
    historyTaylorPostGeneratorStablePredicate layout state := by
  exact historyTaylorPostGeneratorStablePredicate_of_agreesOutsideSignal
    layout layout.coefficientSignal (by simp) input state inside.2 same

private theorem historyP15CoefficientBridge_signalFiber_control_zero
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input state : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input)
    (same : agreesExcept layout.coefficientSignal state input) :
    state (historyCoefficientControl layout) = false := by
  rw [same (historyCoefficientControl layout)
    (historyP15CoefficientBridge_control_ne_signal layout)]
  exact historyP15PostQ10StablePredicate_coefficientControl_zero
    layout widths input inside

private theorem historyP15CoefficientBridge_iteration_predicate_agrees_on_signalFiber
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input state : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input)
    (same : agreesExcept layout.coefficientSignal state input)
    (index : Fin parameters.taylorOrder) :
    (ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (index.val + 1) state &&
      historyP15CoefficientBridgeOuterCondition layout state) =
      (state (historyBranchWire layout) &&
        historyTaylorClockLessThanTimeValue layout state &&
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) state) := by
  have stable := historyP15CoefficientBridge_signalFiber_stable
    layout widths input state inside same
  unfold historyP15CoefficientBridgeOuterCondition
    ClassicalReversibleStage.allWiresTrue ClassicalReversibleStage.readWires
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true]
  rw [stable.2.1]
  simp [Bool.and_assoc, Bool.and_comm]

/-! ### One coefficient rotation across the outer control -/

private theorem historyP15CoefficientBridge_outerOperator_eq_xor
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyCoefficientControl layout) =
      deterministicOperator
        (historyP15CoefficientBridgeXorAction
          (historyCoefficientControl layout)
          (historyP15CoefficientBridgeOuterCondition layout)) := rfl

private theorem historyP15CoefficientBridge_iteration_conjugated_eq_xorOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    (ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyCoefficientControl layout) *
      historyP15CoefficientIterationOperator layout angle index) *
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyCoefficientControl layout) =
      historyP15CoefficientBridgeXorComputeGuardedUseUncompute
        (historyCoefficientControl layout) layout.coefficientSignal
        (historyP15CoefficientBridgeOuterCondition layout)
        (fun basis => ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) basis)
        (localRy angle.uniformValue) := by
  rw [historyP15CoefficientBridge_outerOperator_eq_xor,
    historyP15CoefficientIterationOperator]
  unfold historyP15CoefficientBridgeXorComputeGuardedUseUncompute
  have predicateEqual :
      (fun basis => basis (historyCoefficientControl layout) &&
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) basis) =
      (fun basis =>
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) basis &&
        basis (historyCoefficientControl layout)) := by
    funext basis
    exact Bool.and_comm _ _
  rw [predicateEqual]

private theorem historyP15CoefficientBridge_iteration_conjugated_eq_pure_on_signalFiber_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder)
    (anchor state : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths anchor)
    (same : agreesExcept layout.coefficientSignal state anchor) :
    applyOperator
        ((ClassicalReversibleStage.conjunctionDirectOperator
            [historyBranchWire layout, historyLessThanTimeWire layout]
            (historyCoefficientControl layout) *
          historyP15CoefficientIterationOperator layout angle index) *
          ClassicalReversibleStage.conjunctionDirectOperator
            [historyBranchWire layout, historyLessThanTimeWire layout]
            (historyCoefficientControl layout))
        (basisKet state) =
      applyOperator (historyTaylorCoefficientIterationOperator layout angle index)
        (basisKet state) := by
  rw [historyP15CoefficientBridge_iteration_conjugated_eq_xorOperator]
  calc
    _ = applyOperator
        (predicateControlledSingleQubitOperator
          (fun basis =>
            ClassicalReversibleStage.littleEndianRegisterEqualsNat
              (historyRegisterWires layout.order) (index.val + 1) basis &&
            historyP15CoefficientBridgeOuterCondition layout basis)
          layout.coefficientSignal (localRy angle.uniformValue))
        (basisKet state) := by
      exact historyP15CoefficientBridge_apply_xorCompute_guardedUseUncompute_basisKet
        (historyCoefficientControl layout) layout.coefficientSignal
        (historyP15CoefficientBridge_control_ne_signal layout)
        (historyP15CoefficientBridgeOuterCondition layout)
        (fun basis => ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) basis)
        (localRy angle.uniformValue)
        (historyP15CoefficientBridge_outer_condition_controlInvariant layout)
        (historyP15CoefficientBridge_outer_condition_signalInvariant layout)
        (historyP15CoefficientBridge_order_controlInvariant layout index)
        state
        (historyP15CoefficientBridge_signalFiber_control_zero
          layout widths anchor state inside same)
    _ = _ := by
      unfold historyTaylorCoefficientIterationOperator
      have predicatesAgree :=
        historyP15CoefficientBridge_iteration_predicate_agrees_on_signalFiber
          layout widths anchor state inside same index
      funext output
      rw [applyOperator_basisKet, applyOperator_basisKet]
      rw [predicateControlledSingleQubitOperator_apply,
        predicateControlledSingleQubitOperator_apply]
      rw [predicatesAgree]

/-! ### Coherent signal-fiber lifting -/

private theorem historyP15CoefficientBridge_pureIteration_preservesOutsideSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    OperatorPreservesOutside {layout.coefficientSignal}
      (historyTaylorCoefficientIterationOperator layout angle index) := by
  unfold historyTaylorCoefficientIterationOperator
  exact OperatorPreservesOutside.predicateControlledSingleQubitOperator _ _ _

private theorem historyP15CoefficientBridge_pureIteration_maps_signalFiber_basisSpan
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder)
    (anchor state : QubitBasis qubits)
    (same : agreesExcept layout.coefficientSignal state anchor) :
    applyOperator (historyTaylorCoefficientIterationOperator layout angle index)
        (basisKet state) ∈
      SubspaceMapComponent.basisSpan
        (fun output => agreesExcept layout.coefficientSignal output anchor) := by
  apply SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_preservesOutside
    (historyTaylorCoefficientIterationOperator layout angle index)
    {layout.coefficientSignal}
    (historyP15CoefficientBridge_pureIteration_preservesOutsideSignal
      layout angle index)
    (fun basis => agreesExcept layout.coefficientSignal basis anchor)
    (fun basis => agreesExcept layout.coefficientSignal basis anchor)
  · intro before after beforeSame sameOutside wire different
    exact (sameOutside wire (by simpa using different)).trans
      (beforeSame wire different)
  · exact same

private theorem historyP15CoefficientBridge_apply_eq_of_basisSpan
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (predicate : basis -> Prop) (actual pure : Operator basis)
    (basisEqual : forall input, predicate input ->
      applyOperator actual (basisKet input) =
        applyOperator pure (basisKet input))
    (state : State basis)
    (inside : state ∈ SubspaceMapComponent.basisSpan predicate) :
    applyOperator actual state = applyOperator pure state := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ inside
  · intro generator member
    rcases member with ⟨input, rfl⟩
    exact basisEqual input.1 input.2
  · simp
  · intro left right _ _ leftEqual rightEqual
    rw [applyOperator_add, applyOperator_add, leftEqual, rightEqual]
  · intro scalar basisState _ stateEqual
    rw [applyOperator_smul, applyOperator_smul, stateEqual]

private theorem historyP15CoefficientBridge_apply_maps_basisSpan
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (predicate : basis -> Prop) (operator : Operator basis)
    (basisMaps : forall input, predicate input ->
      applyOperator operator (basisKet input) ∈
        SubspaceMapComponent.basisSpan predicate)
    (state : State basis)
    (inside : state ∈ SubspaceMapComponent.basisSpan predicate) :
    applyOperator operator state ∈ SubspaceMapComponent.basisSpan predicate := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ inside
  · intro generator member
    rcases member with ⟨input, rfl⟩
    exact basisMaps input.1 input.2
  · rw [applyOperator_zero]
    exact Submodule.zero_mem (SubspaceMapComponent.basisSpan predicate)
  · intro left right _ _ leftInside rightInside
    rw [applyOperator_add]
    exact Submodule.add_mem _ leftInside rightInside
  · intro scalar basisState _ stateInside
    rw [applyOperator_smul]
    exact Submodule.smul_mem _ scalar stateInside

private noncomputable def historyP15CoefficientBridge_conjugatedIteration
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    Operator (QubitBasis qubits) :=
  (ClassicalReversibleStage.conjunctionDirectOperator
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyCoefficientControl layout) *
    historyP15CoefficientIterationOperator layout angle index) *
    ClassicalReversibleStage.conjunctionDirectOperator
      [historyBranchWire layout, historyLessThanTimeWire layout]
      (historyCoefficientControl layout)

private theorem historyP15CoefficientBridge_coefficientLoop_conjugated_eq_pure_on_signalFiber
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr)
    (anchor : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths anchor) :
    ∀ (indices : List (Fin parameters.taylorOrder)) (state : State (QubitBasis qubits)),
      state ∈ SubspaceMapComponent.basisSpan
        (fun basis => agreesExcept layout.coefficientSignal basis anchor) →
      applyOperator
          (operatorSequence (indices.map (fun index =>
            historyP15CoefficientBridge_conjugatedIteration layout
              (angles index) index))) state =
        applyOperator
          (operatorSequence (indices.map (fun index =>
            historyTaylorCoefficientIterationOperator layout (angles index) index))) state := by
  intro indices
  induction indices with
  | nil =>
      intro state _
      simp [operatorSequence]
  | cons index rest inductionHypothesis =>
      intro state stateInside
      simp only [List.map_cons, operatorSequence]
      rw [applyOperator_mul, applyOperator_mul]
      have iterationEqual :
          applyOperator
              (historyP15CoefficientBridge_conjugatedIteration layout
                (angles index) index)
              state =
            applyOperator
              (historyTaylorCoefficientIterationOperator layout (angles index) index)
              state := by
        apply historyP15CoefficientBridge_apply_eq_of_basisSpan
          (fun basis => agreesExcept layout.coefficientSignal basis anchor)
          _ _
        · intro basis basisSame
          change applyOperator
              ((ClassicalReversibleStage.conjunctionDirectOperator
                  [historyBranchWire layout, historyLessThanTimeWire layout]
                  (historyCoefficientControl layout) *
                historyP15CoefficientIterationOperator layout (angles index) index) *
                ClassicalReversibleStage.conjunctionDirectOperator
                  [historyBranchWire layout, historyLessThanTimeWire layout]
                  (historyCoefficientControl layout))
              (basisKet basis) = _
          exact historyP15CoefficientBridge_iteration_conjugated_eq_pure_on_signalFiber_basisKet
            layout widths (angles index) index anchor basis inside basisSame
        · exact stateInside
      rw [iterationEqual]
      apply inductionHypothesis
      apply historyP15CoefficientBridge_apply_maps_basisSpan
        (fun basis => agreesExcept layout.coefficientSignal basis anchor)
        (historyTaylorCoefficientIterationOperator layout (angles index) index)
      · intro basis basisSame
        exact historyP15CoefficientBridge_pureIteration_maps_signalFiber_basisSpan
          layout (angles index) index anchor basis basisSame
      · exact stateInside

/-! ### Cancelling the outer involution through a finite word -/

private theorem historyP15CoefficientBridge_deterministicOperator_square
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (action : basis -> basis) (involutive : Function.Involutive action) :
    deterministicOperator action * deterministicOperator action =
      (1 : Operator basis) := by
  rw [deterministicOperator_eq_permMatrix_of_involutive action involutive]
  rw [<- Matrix.permMatrix_mul]
  have permutationSquare :
      involutiveBasisEquiv action involutive *
          involutiveBasisEquiv action involutive = Equiv.refl basis := by
    ext input
    exact involutive input
  rw [permutationSquare]
  simp

private theorem historyP15CoefficientBridge_conjugated_operatorSequence
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (outer : Operator basis) (outerSquare : outer * outer = 1) :
    forall operators : List (Operator basis),
      operatorSequence (operators.map (fun operator => (outer * operator) * outer)) =
        (outer * operatorSequence operators) * outer := by
  intro operators
  induction operators with
  | nil =>
      simpa [operatorSequence] using outerSquare.symm
  | cons first rest inductionHypothesis =>
      simp only [List.map_cons, operatorSequence]
      rw [inductionHypothesis]
      calc
        ((outer * operatorSequence rest) * outer) * ((outer * first) * outer) =
            (((outer * operatorSequence rest) * (outer * outer)) * first) * outer := by
              simp only [Matrix.mul_assoc]
        _ = (outer * (operatorSequence rest * first)) * outer := by
              rw [outerSquare]
              simp only [Matrix.mul_one, Matrix.mul_assoc]

private theorem historyP15CoefficientBridge_outerOperator_square
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyCoefficientControl layout) *
      ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyCoefficientControl layout) = (1 : Operator (QubitBasis qubits)) := by
  rw [historyP15CoefficientBridge_outerOperator_eq_xor]
  apply historyP15CoefficientBridge_deterministicOperator_square
  exact historyP15CoefficientBridgeXorAction_involutive
    (historyCoefficientControl layout)
    (historyP15CoefficientBridgeOuterCondition layout)
    (historyP15CoefficientBridge_outer_condition_controlInvariant layout)

private theorem historyP15CoefficientBridge_conjugatedLoop_eq_outerActual
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder -> AngleExpr) :
    operatorSequence ((List.finRange parameters.taylorOrder).map (fun index =>
      historyP15CoefficientBridge_conjugatedIteration layout
        (angles index) index)) =
      (ClassicalReversibleStage.conjunctionDirectOperator
          [historyBranchWire layout, historyLessThanTimeWire layout]
          (historyCoefficientControl layout) *
        historyP15CoefficientLoopOperator layout angles) *
        ClassicalReversibleStage.conjunctionDirectOperator
          [historyBranchWire layout, historyLessThanTimeWire layout]
          (historyCoefficientControl layout) := by
  simpa only [historyP15CoefficientBridge_conjugatedIteration,
    historyP15CoefficientLoopOperator, List.map_map, Function.comp_def] using
    (historyP15CoefficientBridge_conjugated_operatorSequence
      (ClassicalReversibleStage.conjunctionDirectOperator
        [historyBranchWire layout, historyLessThanTimeWire layout]
        (historyCoefficientControl layout))
      (historyP15CoefficientBridge_outerOperator_square layout)
      ((List.finRange parameters.taylorOrder).map (fun index =>
        historyP15CoefficientIterationOperator layout (angles index) index)))

/-- On the stable post-Q10 boundary, the literal P15 outer-control coefficient
word has exactly the pure branch-and-clock Taylor coefficient-loop meaning. -/
theorem historyP15TaylorCoefficientOperator_eq_historyTaylorCoefficientLoopOperator_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder -> AngleExpr)
    (input : QubitBasis qubits)
    (inside : historyP15PostQ10StablePredicate (layout := layout) widths input) :
    applyOperator (historyP15TaylorCoefficientOperator layout widths angles)
        (basisKet input) =
      applyOperator (historyTaylorCoefficientLoopOperator layout angles)
        (basisKet input) := by
  unfold historyP15TaylorCoefficientOperator historyTaylorCoefficientLoopOperator
  simp only [operatorSequence, Matrix.one_mul]
  rw [<- historyP15CoefficientBridge_conjugatedLoop_eq_outerActual]
  apply historyP15CoefficientBridge_coefficientLoop_conjugated_eq_pure_on_signalFiber
    layout widths angles input inside
  exact SubspaceMapComponent.basisKet_mem_basisSpan (by
    intro wire _
    rfl)

end

end SpectralSamplingProof.Components
