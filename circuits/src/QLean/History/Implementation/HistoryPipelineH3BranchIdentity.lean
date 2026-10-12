import QLean.History.Implementation.HistoryPipelineRepairedH3
import QLean.History.Implementation.HistoryPipelineH2BranchIdentity
import QLean.Spectral.Circuits.HistoryClockCleanRestoredStrong

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
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

/-- The recorded mask--compare--unmask target has the direct comparison action
on its genuine clean constant/borrow boundary. -/
theorem historyLessThanConstantOperator_apply_basisKet_of_clean119
    {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat)
    (input : QubitBasis qubits)
    (clean : historyLessThanConstantCleanInputPredicate spec input) :
    VerifiedCircuitCore.applyOperator
        (historyLessThanConstantOperator spec constant)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet
        (historyLessThanConstantDirectBasisAction spec constant input) := by
  rw [historyLessThanConstantOperator]
  rw [ClassicalReversibleStage.analyticOperator_eq_deterministicReference,
    unsignedLessThanXorDirtyOperator_eq_deterministicOperator]
  change VerifiedCircuitCore.applyOperator
      (operatorSequence
        ([(fun state => (ClassicalReversibleStage.xorConstant
            (List.ofFn spec.rhs.wire) constant).reference state),
          unsignedLessThanXorDirtyBasisAction spec,
          (fun state => (ClassicalReversibleStage.xorConstant
            (List.ofFn spec.rhs.wire) constant).reference state)].map
          deterministicOperator))
      (VerifiedCircuitCore.basisKet input) = _
  rw [operatorSequence_deterministicOperator,
    applyOperator_deterministicOperator_basisKet]
  simp only [List.foldl]
  rw [ClassicalReversibleStage.xorConstant_reference_apply,
    ClassicalReversibleStage.xorConstant_reference_apply]
  apply congrArg VerifiedCircuitCore.basisKet
  rw [unsignedLessThanXorDirtyBasisAction_eq_clean spec _]
  · exact historyP15LessThanConstantCleanBasisAction_eq_direct
      spec constant input clean
  · intro index
    rw [ClassicalReversibleStage.constantXorBasisAction_apply_outside
      (List.ofFn spec.rhs.wire) constant input (spec.borrow.wire index)]
    · exact clean.1 index
    · intro member
      simp only [List.mem_ofFn] at member
      rcases member with ⟨rhsIndex, equal⟩
      exact spec.rhsBorrowDifferent rhsIndex index equal

def h3AfterSelector119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.selector) 2 (historyBranchWire layout) input

def h3AfterTime119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  historyTaylorTimeComparisonBasisAction layout (h3AfterSelector119 layout input)

def h3AfterIdleEnd119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  historyTaylorIdleEndComparisonBasisAction layout (h3AfterTime119 layout input)

def h3BeforeUniform119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  historyTaylorActiveConjunctionBasisAction layout (h3AfterIdleEnd119 layout input)

theorem repairedH3SelectorEquality119_apply_basisKet
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits) :
    VerifiedCircuitCore.applyOperator
        (repairedH3SelectorEquality119 source domain).target
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet
        (h3AfterSelector119 (ExecutableLayout119 source domain) input) := by
  rw [repairedH3SelectorEquality119_target]
  simpa [h3AfterSelector119, historySelectorEqualityClassicalStage] using
    h3semanticVerification_i01_apply_basisKet (ExecutableLayout119 source domain) input

theorem repairedH3TimeComparison119_apply_basisKet
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate
      (ExecutableLayout119 source domain) input) :
    VerifiedCircuitCore.applyOperator
        (repairedH3TimeComparison119 source domain).target
        (VerifiedCircuitCore.basisKet
          (h3AfterSelector119 (ExecutableLayout119 source domain) input)) =
      VerifiedCircuitCore.basisKet
        (h3AfterTime119 (ExecutableLayout119 source domain) input) := by
  let layout := ExecutableLayout119 source domain
  let comparison := ((ScientificWidthGenericContract.correctedCleanEvidence259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)).clock
      ).clockTimeLessThan.toSpec
  have clean : historyLessThanConstantCleanInputPredicate comparison
      (h3AfterSelector119 layout input) := by
    change (∀ index,
        h3AfterSelector119 layout input
          ((historyBorrowRegister layout).wire index) = false) ∧
      ∀ index,
        h3AfterSelector119 layout input
          ((historyBoundRegister layout).wire index) = false
    constructor
    · intro index
      unfold h3AfterSelector119
      rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
      · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
          layout input auxiliary _
          (historyBorrowRegister_wire_mem_workspace layout index)
      · intro equal
        apply historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires
          layout index
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
    · intro index
      unfold h3AfterSelector119
      rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
      · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
          layout input auxiliary _
          (historyBoundRegister_wire_mem_workspace layout index)
      · intro equal
        apply historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires
          layout index
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
  unfold repairedH3TimeComparison119
  rw [historyLessThanConstantExactComponent_target]
  rw [historyLessThanConstantOperator_apply_basisKet_of_clean119]
  · apply congrArg VerifiedCircuitCore.basisKet
    rfl
  · exact clean

theorem repairedH3IdleEndComparison119_apply_basisKet
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate
      (ExecutableLayout119 source domain) input) :
    VerifiedCircuitCore.applyOperator
        (repairedH3IdleEndComparison119 source domain).target
        (VerifiedCircuitCore.basisKet
          (h3AfterTime119 (ExecutableLayout119 source domain) input)) =
      VerifiedCircuitCore.basisKet
        (h3AfterIdleEnd119 (ExecutableLayout119 source domain) input) := by
  let layout := ExecutableLayout119 source domain
  have clean : historyLessThanConstantCleanInputPredicate
      (((ScientificWidthGenericContract.correctedCleanEvidence259
        (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)).clock
          ).clockIdleEndLessThan.toSpec)
      (h3AfterTime119 layout input) := by
    change (∀ index,
        h3AfterTime119 layout input
          ((historyBorrowRegister layout).wire index) = false) ∧
      ∀ index,
        h3AfterTime119 layout input
          ((historyBoundRegister layout).wire index) = false
    constructor
    · intro index
      unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
      rw [xorWire_apply_other]
      · unfold h3AfterSelector119
        rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
        · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
            layout input auxiliary _
            (historyBorrowRegister_wire_mem_workspace layout index)
        · intro equal
          apply historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires
            layout index
          simp [historyTaylorBeforeGeneratorLiveWires, equal]
      · intro equal
        apply historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires
          layout index
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
    · intro index
      unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
      rw [xorWire_apply_other]
      · unfold h3AfterSelector119
        rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
        · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
            layout input auxiliary _
            (historyBoundRegister_wire_mem_workspace layout index)
        · intro equal
          apply historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires
            layout index
          simp [historyTaylorBeforeGeneratorLiveWires, equal]
      · intro equal
        apply historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires
          layout index
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
  unfold repairedH3IdleEndComparison119
  rw [historyLessThanConstantExactComponent_target]
  rw [historyLessThanConstantOperator_apply_basisKet_of_clean119]
  · apply congrArg VerifiedCircuitCore.basisKet
    rfl
  · exact clean

theorem repairedH3ActiveConjunction119_apply_basisKet
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits) :
    VerifiedCircuitCore.applyOperator
        (repairedH3ActiveConjunction119 source domain).target
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet (historyTaylorActiveConjunctionBasisAction
        (ExecutableLayout119 source domain) input) := by
  rw [repairedH3ActiveConjunction119_target]
  apply h3semanticVerification_conjunction_apply_basisKet_of_cleanWork
  · simp
  · exact historyTaylorActiveConjunctionLayout_nodup
      (ExecutableLayout119 source domain)
  · simp [ClassicalReversibleStage.minimumWorkCleanPredicate]

theorem h3AfterSelector119_eq_input_of_selector_false
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input)
    (selectorFalse :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 2 input = false) :
    h3AfterSelector119 layout input = input := by
  funext wire
  by_cases equal : wire = historyBranchWire layout
  · subst wire
    unfold h3AfterSelector119
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target]
    have branchZero := historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
      layout input auxiliary _ (historyBranchWire_mem_workspace layout)
    simp [branchZero, selectorFalse]
  · unfold h3AfterSelector119
    exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      _ _ _ _ equal input

theorem h3AfterIdleEnd119_branch_false_of_selector_false
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input)
    (selectorFalse :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 2 input = false) :
    h3AfterIdleEnd119 layout input (historyBranchWire layout) = false := by
  unfold h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
  rw [xorWire_apply_other _ _ (historyBranchWire_ne_lessThanIdleEndWire layout)]
  unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
  rw [xorWire_apply_other _ _ (historyBranchWire_ne_lessThanTimeWire layout)]
  rw [h3AfterSelector119_eq_input_of_selector_false
    layout input auxiliary selectorFalse]
  exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
    layout input auxiliary _ (historyBranchWire_mem_workspace layout)

theorem h3AfterIdleEnd119_active_zero
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input) :
    h3AfterIdleEnd119 layout input (historyActiveWire layout) = false := by
  unfold h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
  rw [xorWire_apply_other _ _
    (historyLessThanIdleEndWire_ne_activeWire layout).symm]
  unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
  rw [xorWire_apply_other _ _
    (historyLessThanTimeWire_ne_activeWire layout).symm]
  unfold h3AfterSelector119
  rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
  · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
      layout input auxiliary _ (historyActiveWire_mem_workspace layout)
  · exact (historyBranchWire_ne_activeWire layout).symm

private theorem externallyControlledStrictUnitaryExactOperatorComponent_circuit119
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    (externallyControlledStrictUnitaryExactOperatorComponent
        symbolValue layout plan).toExact.circuit =
      VerifiedCircuitCore.Circuit.sequence
        (plan.map fun leaf => leaf.compile layout) := by
  induction plan with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      change VerifiedCircuitCore.Circuit.seq (first.compile layout)
          (externallyControlledStrictUnitaryExactOperatorComponent
            symbolValue layout rest).toExact.circuit =
        VerifiedCircuitCore.Circuit.seq (first.compile layout)
          (VerifiedCircuitCore.Circuit.sequence
            (rest.map fun leaf => leaf.compile layout))
      rw [inductionHypothesis]

theorem h3ActiveConjunction119_fixed_of_branch_false
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (branchFalse : input (historyBranchWire layout) = false) :
    historyTaylorActiveConjunctionBasisAction layout input = input := by
  funext wire
  simp [historyTaylorActiveConjunctionBasisAction,
    ClassicalReversibleStage.conjunctionDirectBasisAction,
    ClassicalReversibleStage.allWiresTrue,
    ClassicalReversibleStage.readWires, branchFalse, xorWire]

theorem repairedH3UniformInverse119_apply_basisKet_of_active_zero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (activeZero : input (historyActiveWire
      (ExecutableLayout119 source domain)) = false)
    (workClean : externallyControlledCleanWorkPredicate
      (historyOrderUniformExternalControlCleanWorkValid
        (ExecutableLayout119 source domain)
        (ExecutableClockEvidence119 source domain).uniformExternalControl)
      input) :
    VerifiedCircuitCore.applyOperator
        (historyOrderUniformPreparationInverseExactComponent
          (ExecutableLayout119 source domain)
          (ExecutableClockEvidence119 source domain).uniformExternalControl).target
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).uniformExternalControl
  let exact := historyOrderUniformPreparationInverseExactComponent layout evidence
  let cleanComponent :=
    historyOrderUniformPreparationInverseCleanSubspaceMapComponent
      (fun _ => 0) layout evidence
  have sameCircuit : exact.circuit = cleanComponent.circuit := by
    dsimp [exact, cleanComponent,
      historyOrderUniformPreparationInverseExactComponent]
    rw [externallyControlledStrictUnitaryExactOperatorComponent_circuit119]
    rw [historyOrderUniformPreparationInverseCleanSubspaceMapComponent_circuit]
    congr 1
  have cleanMem : VerifiedCircuitCore.basisKet input ∈
      cleanComponent.inputSubspace := by
    rw [(historyOrderUniformPreparationInverseCleanSubspaceMapComponent_spaces
      (fun _ => 0) layout evidence).1]
    exact SubspaceMapComponent.basisKet_mem_basisSpan workClean
  calc
    VerifiedCircuitCore.applyOperator exact.target
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.applyOperator
        (Circuit.denote
          (primitiveGateOperatorWithSymbols (qubits := (ExecutableRaw119 source).history.qubits)
            (fun _ => 0)) exact.circuit)
        (VerifiedCircuitCore.basisKet input) := by rw [exact.correct]
    _ = VerifiedCircuitCore.applyOperator
        (Circuit.denote
          (primitiveGateOperatorWithSymbols (qubits := (ExecutableRaw119 source).history.qubits)
            (fun _ => 0)) cleanComponent.circuit)
        (VerifiedCircuitCore.basisKet input) := by rw [sameCircuit]
    _ = VerifiedCircuitCore.applyOperator cleanComponent.target
        (VerifiedCircuitCore.basisKet input) := cleanComponent.correct _ cleanMem
    _ = VerifiedCircuitCore.basisKet input := by
      rw [historyOrderUniformPreparationInverseCleanSubspaceMapComponent_target]
      exact h3semanticVerification_i02_apply_basisKet_of_active_zero layout
        (ExecutableClockEvidence119 source domain) input activeZero

private theorem h3_sharedPool_ge_five119
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

private theorem h3_idleFlag_ne_branch119
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
  have sharedAtLeast := h3_sharedPool_ge_five119 layout
  omega

private theorem h3_idleFlag_ne_active119
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
  have sharedAtLeast := h3_sharedPool_ge_five119 layout
  omega

private theorem h3_idleConjunction_nodup119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ([historyBranchWire layout, historyIdleFlag layout] ++ [] ++
      [historyActiveWire layout]).Nodup := by
  simp [(h3_idleFlag_ne_branch119 layout).symm,
    historyBranchWire_ne_activeWire layout, h3_idleFlag_ne_active119 layout]

private theorem h3_orderCnotSequence_apply_basisKet_of_active_zero119
    {qubits : Nat} (wires : List (Fin qubits)) (active : Fin qubits)
    (input : QubitBasis qubits) (activeZero : input active = false) :
    VerifiedCircuitCore.applyOperator
        (operatorSequence (wires.map fun target =>
          reversibleAnalyticCnotOperator active target))
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  induction wires with
  | nil =>
      change Matrix.mulVec (1 : VerifiedCircuitCore.Operator (QubitBasis qubits))
          (VerifiedCircuitCore.basisKet input) = _
      rw [Matrix.one_mulVec]
  | cons first rest inductionHypothesis =>
      simp only [List.map_cons, operatorSequence,
        VerifiedCircuitCore.applyOperator_mul]
      rw [h3semanticVerification_cnot_apply_basisKet]
      have firstFixed : xorWire first (input active) input = input := by
        funext wire
        simp [xorWire, activeZero]
      rw [firstFixed, inductionHypothesis]

/-- The repaired idle transform has the same inactive-branch behavior as the
legacy transform.  Its order-register layer may contain only the bits set in
`binaryLabels - 1`; when the conjunction control is zero, every one of those
CNOTs is nevertheless inactive. -/
theorem repairedH3IdleTransformOperator119_apply_basisKet_of_branch_false
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryIdleTransformEvidence layout)
    (binaryLabels : Nat) (angle : ℝ) (input : QubitBasis qubits)
    (branchFalse : input (historyBranchWire layout) = false)
    (activeZero : input (historyActiveWire layout) = false) :
    VerifiedCircuitCore.applyOperator
        (repairedH3IdleTransformOperator119 layout evidence binaryLabels angle)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  let afterEnd := xorWire (historyIdleFlag layout)
    (input (historyLessThanIdleEndWire layout)) input
  let afterTime := xorWire (historyIdleFlag layout)
    (afterEnd (historyLessThanTimeWire layout)) afterEnd
  have endStep := h3semanticVerification_cnot_apply_basisKet
    (historyLessThanIdleEndWire layout) (historyIdleFlag layout) input
  have timeStep := h3semanticVerification_cnot_apply_basisKet
    (historyLessThanTimeWire layout) (historyIdleFlag layout) afterEnd
  have branchAfterTime : afterTime (historyBranchWire layout) = false := by
    dsimp [afterTime, afterEnd]
    rw [xorWire_apply_other _ _ (h3_idleFlag_ne_branch119 layout).symm,
      xorWire_apply_other _ _ (h3_idleFlag_ne_branch119 layout).symm]
    exact branchFalse
  have activeAfterTime : afterTime (historyActiveWire layout) = false := by
    dsimp [afterTime, afterEnd]
    rw [xorWire_apply_other _ _ (h3_idleFlag_ne_active119 layout).symm,
      xorWire_apply_other _ _ (h3_idleFlag_ne_active119 layout).symm]
    exact activeZero
  have conjunctionStep : VerifiedCircuitCore.applyOperator
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyIdleFlag layout] []
        (historyActiveWire layout)).analyticOperator
      (VerifiedCircuitCore.basisKet afterTime) =
      VerifiedCircuitCore.basisKet afterTime := by
    rw [h3semanticVerification_conjunction_apply_basisKet_of_cleanWork]
    · congr 1
      funext wire
      simp [ClassicalReversibleStage.conjunctionDirectBasisAction,
        ClassicalReversibleStage.allWiresTrue,
        ClassicalReversibleStage.readWires, branchAfterTime, xorWire]
    · simp
    · exact h3_idleConjunction_nodup119 layout
    · simp [ClassicalReversibleStage.minimumWorkCleanPredicate]
  have orderStep := h3_orderCnotSequence_apply_basisKet_of_active_zero119
    (repairedH3IdleOrderTargets119 layout binaryLabels)
    (historyActiveWire layout) afterTime activeAfterTime
  have rotationStep := h3semanticVerification_controlled_single_apply_basisKet_of_control_false
    (historyActiveWire layout) layout.coefficientSignal
    evidence.active_ne_coefficient (localRy angle) afterTime activeAfterTime
  have timeRestore : xorWire (historyIdleFlag layout)
      (afterTime (historyLessThanTimeWire layout)) afterTime = afterEnd := by
    funext wire
    dsimp [afterTime]
    simp [xorWire, evidence.time_ne_idle]
  have endRestore : xorWire (historyIdleFlag layout)
      (afterEnd (historyLessThanIdleEndWire layout)) afterEnd = input := by
    funext wire
    dsimp [afterEnd]
    simp [xorWire, evidence.idleEnd_ne_idle]
  unfold repairedH3IdleTransformOperator119
  simp only [operatorSequence, VerifiedCircuitCore.applyOperator_mul]
  rw [endStep, timeStep, conjunctionStep, orderStep, rotationStep,
    conjunctionStep]
  rw [h3semanticVerification_cnot_apply_basisKet, timeRestore,
    h3semanticVerification_cnot_apply_basisKet, endRestore]
  change Matrix.mulVec (1 : VerifiedCircuitCore.Operator (QubitBasis qubits))
      (VerifiedCircuitCore.basisKet input) = _
  rw [Matrix.one_mulVec]

/-- In the physical-clock sector both comparison flags are true.  Their two
XORs therefore cancel on the idle flag, so the repaired idle transform is
inactive independently of the order value. -/
theorem repairedH3IdleTransformOperator119_apply_basisKet_of_active_clock
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryIdleTransformEvidence layout)
    (binaryLabels : Nat) (angle : ℝ) (input : QubitBasis qubits)
    (idleEndTrue : input (historyLessThanIdleEndWire layout) = true)
    (timeTrue : input (historyLessThanTimeWire layout) = true)
    (idleZero : input (historyIdleFlag layout) = false)
    (activeZero : input (historyActiveWire layout) = false) :
    VerifiedCircuitCore.applyOperator
        (repairedH3IdleTransformOperator119 layout evidence binaryLabels angle)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  let afterEnd := xorWire (historyIdleFlag layout)
    (input (historyLessThanIdleEndWire layout)) input
  let afterTime := xorWire (historyIdleFlag layout)
    (afterEnd (historyLessThanTimeWire layout)) afterEnd
  have endStep := h3semanticVerification_cnot_apply_basisKet
    (historyLessThanIdleEndWire layout) (historyIdleFlag layout) input
  have timeStep := h3semanticVerification_cnot_apply_basisKet
    (historyLessThanTimeWire layout) (historyIdleFlag layout) afterEnd
  have idleAfterTime : afterTime (historyIdleFlag layout) = false := by
    dsimp [afterTime, afterEnd]
    simp [xorWire, idleEndTrue, timeTrue, idleZero, evidence.time_ne_idle]
  have activeAfterTime : afterTime (historyActiveWire layout) = false := by
    dsimp [afterTime, afterEnd]
    rw [xorWire_apply_other _ _ (h3_idleFlag_ne_active119 layout).symm,
      xorWire_apply_other _ _ (h3_idleFlag_ne_active119 layout).symm]
    exact activeZero
  have conjunctionStep : VerifiedCircuitCore.applyOperator
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire layout, historyIdleFlag layout] []
        (historyActiveWire layout)).analyticOperator
      (VerifiedCircuitCore.basisKet afterTime) =
      VerifiedCircuitCore.basisKet afterTime := by
    rw [h3semanticVerification_conjunction_apply_basisKet_of_cleanWork]
    · congr 1
      funext wire
      simp [ClassicalReversibleStage.conjunctionDirectBasisAction,
        ClassicalReversibleStage.allWiresTrue,
        ClassicalReversibleStage.readWires, idleAfterTime, xorWire]
    · simp
    · exact h3_idleConjunction_nodup119 layout
    · simp [ClassicalReversibleStage.minimumWorkCleanPredicate]
  have orderStep := h3_orderCnotSequence_apply_basisKet_of_active_zero119
    (repairedH3IdleOrderTargets119 layout binaryLabels)
    (historyActiveWire layout) afterTime activeAfterTime
  have rotationStep := h3semanticVerification_controlled_single_apply_basisKet_of_control_false
    (historyActiveWire layout) layout.coefficientSignal
    evidence.active_ne_coefficient (localRy angle) afterTime activeAfterTime
  have timeRestore : xorWire (historyIdleFlag layout)
      (afterTime (historyLessThanTimeWire layout)) afterTime = afterEnd := by
    funext wire
    dsimp [afterTime]
    simp [xorWire, evidence.time_ne_idle]
  have endRestore : xorWire (historyIdleFlag layout)
      (afterEnd (historyLessThanIdleEndWire layout)) afterEnd = input := by
    funext wire
    dsimp [afterEnd]
    simp [xorWire, evidence.idleEnd_ne_idle]
  unfold repairedH3IdleTransformOperator119
  simp only [operatorSequence, VerifiedCircuitCore.applyOperator_mul]
  rw [endStep, timeStep, conjunctionStep, orderStep, rotationStep,
    conjunctionStep]
  rw [h3semanticVerification_cnot_apply_basisKet, timeRestore,
    h3semanticVerification_cnot_apply_basisKet, endRestore]
  change Matrix.mulVec (1 : VerifiedCircuitCore.Operator (QubitBasis qubits))
      (VerifiedCircuitCore.basisKet input) = _
  rw [Matrix.one_mulVec]

private theorem h3AfterTime119_comparison_work_clean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input) :
    (forall index, h3AfterTime119 layout input
        ((historyBorrowRegister layout).wire index) = false) ∧
      forall index, h3AfterTime119 layout input
        ((historyBoundRegister layout).wire index) = false := by
  constructor
  · intro index
    unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
    rw [xorWire_apply_other]
    · unfold h3AfterSelector119
      rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
      · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
          layout input auxiliary _
          (historyBorrowRegister_wire_mem_workspace layout index)
      · intro equal
        apply historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires
          layout index
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
    · intro equal
      apply historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires
        layout index
      simp [historyTaylorBeforeGeneratorLiveWires, equal]
  · intro index
    unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
    rw [xorWire_apply_other]
    · unfold h3AfterSelector119
      rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
      · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
          layout input auxiliary _
          (historyBoundRegister_wire_mem_workspace layout index)
      · intro equal
        apply historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires
          layout index
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
    · intro equal
      apply historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires
        layout index
      simp [historyTaylorBeforeGeneratorLiveWires, equal]

theorem h3AfterIdleEnd119_comparison_work_clean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input) :
    (forall index, h3AfterIdleEnd119 layout input
        ((historyBorrowRegister layout).wire index) = false) ∧
      forall index, h3AfterIdleEnd119 layout input
        ((historyBoundRegister layout).wire index) = false := by
  have afterTimeClean := h3AfterTime119_comparison_work_clean
    layout input auxiliary
  constructor
  · intro index
    unfold h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
    rw [xorWire_apply_other]
    · exact afterTimeClean.1 index
    · intro equal
      apply historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires
        layout index
      simp [historyTaylorBeforeGeneratorLiveWires, equal]
  · intro index
    unfold h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
    rw [xorWire_apply_other]
    · exact afterTimeClean.2 index
    · intro equal
      apply historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires
        layout index
      simp [historyTaylorBeforeGeneratorLiveWires, equal]

private theorem h3AfterIdleEnd119_uniform_work_zero
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input)
    (index : Fin 2) :
    h3AfterIdleEnd119 layout input
        ((historyUniformControlWork layout).wire index) = false := by
  have notLive : (historyUniformControlWork layout).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
    simpa [historyUniformControlWork] using
      historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
        layout 0 (by
          unfold historyClockWorkspaceWidth
          omega) (by
          unfold historySharedPoolWidth historyStructuralPoolWidth
          omega) index
  unfold h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
  rw [xorWire_apply_other]
  · unfold h3AfterTime119 historyTaylorTimeComparisonBasisAction
    rw [xorWire_apply_other]
    · unfold h3AfterSelector119
      rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other]
      · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
          layout input auxiliary _
          (historyUniformControlWork_wire_mem_workspace layout index)
      · intro equal
        apply notLive
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
    · intro equal
      apply notLive
      simp [historyTaylorBeforeGeneratorLiveWires, equal]
  · intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]

theorem repairedH3IdleEndComparison119_restore_basisKet
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate
      (ExecutableLayout119 source domain) input) :
    VerifiedCircuitCore.applyOperator
        (repairedH3IdleEndComparison119 source domain).target
        (VerifiedCircuitCore.basisKet
          (h3AfterIdleEnd119 (ExecutableLayout119 source domain) input)) =
      VerifiedCircuitCore.basisKet
        (h3AfterTime119 (ExecutableLayout119 source domain) input) := by
  let layout := ExecutableLayout119 source domain
  unfold repairedH3IdleEndComparison119
  rw [historyLessThanConstantExactComponent_target]
  rw [historyLessThanConstantOperator_apply_basisKet_of_clean119]
  · exact congrArg VerifiedCircuitCore.basisKet
      (historyTaylorIdleEndComparisonBasisAction_involutive119
        layout (h3AfterTime119 layout input))
  · change (forall index, h3AfterIdleEnd119 layout input
        ((historyBorrowRegister layout).wire index) = false) ∧
      forall index, h3AfterIdleEnd119 layout input
        ((historyBoundRegister layout).wire index) = false
    exact h3AfterIdleEnd119_comparison_work_clean layout input auxiliary

theorem repairedH3TimeComparison119_restore_basisKet
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate
      (ExecutableLayout119 source domain) input) :
    VerifiedCircuitCore.applyOperator
        (repairedH3TimeComparison119 source domain).target
        (VerifiedCircuitCore.basisKet
          (h3AfterTime119 (ExecutableLayout119 source domain) input)) =
      VerifiedCircuitCore.basisKet
        (h3AfterSelector119 (ExecutableLayout119 source domain) input) := by
  let layout := ExecutableLayout119 source domain
  unfold repairedH3TimeComparison119
  rw [historyLessThanConstantExactComponent_target]
  rw [historyLessThanConstantOperator_apply_basisKet_of_clean119]
  · exact congrArg VerifiedCircuitCore.basisKet
      (historyTaylorTimeComparisonBasisAction_involutive119
        layout (h3AfterSelector119 layout input))
  · change (forall index, h3AfterTime119 layout input
        ((historyBorrowRegister layout).wire index) = false) ∧
      forall index, h3AfterTime119 layout input
        ((historyBoundRegister layout).wire index) = false
    exact h3AfterTime119_comparison_work_clean layout input auxiliary

theorem repairedH3Projector119_apply_basisKet_of_auxiliary
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate
      (ExecutableLayout119 source domain) input) :
    VerifiedCircuitCore.applyOperator
        (historyProjectorControlExactComponent internalZeroSymbolEnvironment
          (ExecutableLayout119 source domain)
          (ExecutableClockEvidence119 source domain).projectorControl).target
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  let layout := ExecutableLayout119 source domain
  have branchZero : input (historyBranchWire layout) = false :=
    historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem layout input auxiliary _
      (historyBranchWire_mem_workspace layout)
  rw [historyProjectorControlExactComponent_target]
  rw [h3I06_projectorControlOperator_apply_basisKet_of_auxiliaryBoundary
    layout input auxiliary]
  apply congrArg VerifiedCircuitCore.basisKet
  funext wire
  simp [h3I06BasisAction, h3I06ProjectorPredicate, branchZero, xorWire]

theorem repairedH3ClockIncrement119_apply_basisKet_of_auxiliary
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate
      (ExecutableLayout119 source domain) input) :
    VerifiedCircuitCore.applyOperator
        (historyControlledClockIncrementExactComponent internalZeroSymbolEnvironment
          (ExecutableLayout119 source domain)
          (ExecutableClockEvidence119 source domain).controlledIncrement).target
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).controlledIncrement
  let spec := historyControlledClockIncrementSpec layout evidence
  have clean : controlledAddConstantMod2PowCleanPredicate spec input := by
    constructor
    · intro index
      exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
        layout input auxiliary _
        (historyClockMaskedConstantRegister_wire_mem_workspace layout index)
    · exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
        layout input auxiliary _ (historyClockIncrementCarry_mem_workspace layout)
  have controlZero : input spec.control = false := by
    exact historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
      layout input auxiliary _ (historyBranchWire_mem_workspace layout)
  rw [historyControlledClockIncrementExactComponent_target]
  unfold controlledAddConstantMod2PowDirtyOperator
  rw [ClassicalReversibleStage.analyticOperator_eq_deterministicReference,
    applyOperator_deterministicOperator_basisKet,
    controlledAddConstantMod2PowStage_reference_apply_of_clean spec input clean]
  apply congrArg VerifiedCircuitCore.basisKet
  simp [controlledAddConstantMod2PowBasisAction, controlZero]

theorem repairedH3RecordedTarget119_apply_basisKet_of_selector_false
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate
      (ExecutableLayout119 source domain) input)
    (selectorFalse :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires (ExecutableLayout119 source domain).selector) 2
        input = false) :
    VerifiedCircuitCore.applyOperator
        (repairedH3RecordedTarget119 source domain)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  have branchFalse : h3AfterIdleEnd119 layout input
      (historyBranchWire layout) = false :=
    h3AfterIdleEnd119_branch_false_of_selector_false
      layout input auxiliary selectorFalse
  have activeZero : h3AfterIdleEnd119 layout input
      (historyActiveWire layout) = false :=
    h3AfterIdleEnd119_active_zero layout input auxiliary
  have uniformWork : externallyControlledCleanWorkPredicate
      (historyOrderUniformExternalControlCleanWorkValid
        layout clock.uniformExternalControl)
      (h3AfterIdleEnd119 layout input) := by
    change h3AfterIdleEnd119 layout input
          ((historyUniformControlWork layout).wire 0) = false ∧
      h3AfterIdleEnd119 layout input
          ((historyUniformControlWork layout).wire 1) = false
    exact ⟨h3AfterIdleEnd119_uniform_work_zero
        layout input auxiliary 0,
      h3AfterIdleEnd119_uniform_work_zero layout input auxiliary 1⟩
  unfold repairedH3RecordedTarget119 repairedH3Components119
  simp only [List.map_cons, List.map_nil, operatorSequence,
    VerifiedCircuitCore.applyOperator_mul, Matrix.one_mul]
  rw [repairedH3SelectorEquality119_apply_basisKet source domain input]
  rw [repairedH3TimeComparison119_apply_basisKet
    source domain input auxiliary]
  rw [repairedH3IdleEndComparison119_apply_basisKet
    source domain input auxiliary]
  rw [repairedH3ActiveConjunction119_apply_basisKet]
  rw [h3ActiveConjunction119_fixed_of_branch_false
    layout (h3AfterIdleEnd119 layout input) branchFalse]
  rw [repairedH3UniformInverse119_apply_basisKet_of_active_zero
    source domain (h3AfterIdleEnd119 layout input) activeZero uniformWork]
  rw [repairedH3ActiveConjunction119_apply_basisKet]
  rw [h3ActiveConjunction119_fixed_of_branch_false
    layout (h3AfterIdleEnd119 layout input) branchFalse]
  rw [repairedH3IdleTransform119_target]
  rw [repairedH3IdleTransformOperator119_apply_basisKet_of_branch_false
    layout clock.idleTransform source.historyParameters.binaryLabels
    (repairedH3IdleAngle119 source).uniformValue
    (h3AfterIdleEnd119 layout input) branchFalse activeZero]
  rw [repairedH3ActiveConjunction119_apply_basisKet]
  rw [h3ActiveConjunction119_fixed_of_branch_false
    layout (h3AfterIdleEnd119 layout input) branchFalse]
  rw [repairedH3CoefficientRotation119_target]
  rw [h3semanticVerification_controlled_single_apply_basisKet_of_control_false
    (historyActiveWire layout) layout.coefficientSignal
    clock.coefficientControl_ne_signal
    (localRy compiledIdleCoefficientAngle119.uniformValue)
    (h3AfterIdleEnd119 layout input) activeZero]
  rw [repairedH3ActiveConjunction119_apply_basisKet]
  rw [h3ActiveConjunction119_fixed_of_branch_false
    layout (h3AfterIdleEnd119 layout input) branchFalse]
  rw [repairedH3IdleEndComparison119_restore_basisKet
    source domain input auxiliary]
  rw [repairedH3TimeComparison119_restore_basisKet
    source domain input auxiliary]
  rw [h3AfterSelector119_eq_input_of_selector_false
    layout input auxiliary selectorFalse]
  rw [repairedH3Projector119_apply_basisKet_of_auxiliary
    source domain input auxiliary]
  rw [repairedH3ClockIncrement119_apply_basisKet_of_auxiliary
    source domain input auxiliary]
  rw [repairedH3SelectorEquality119_apply_basisKet source domain input]
  rw [h3AfterSelector119_eq_input_of_selector_false
    layout input auxiliary selectorFalse]

theorem correctedBranchH3_identity119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (branchNeTwo : branch.val ≠ 2) :
    VerifiedCircuitCore.applyOperator
        (repairedH3RecordedTarget119 source domain)
        (VerifiedCircuitCore.basisKet
          (correctedBranchHistoryBasis119 source domain fits branch index)) =
      VerifiedCircuitCore.basisKet
        (correctedBranchHistoryBasis119 source domain fits branch index) := by
  apply repairedH3RecordedTarget119_apply_basisKet_of_selector_false
  · exact correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits branch index
  · rw [correctedBranchHistoryBasis119_selector_two]
    simp [branchNeTwo]

end
end ExecutableHistoryExecutableHistory
