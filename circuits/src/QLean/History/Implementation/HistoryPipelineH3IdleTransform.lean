import QLean.History.Implementation.HistoryPipelineH3ActiveLogical

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

def h3CnotTargetsBasisAction119
    {qubits : Nat} (targets : List (Fin qubits)) (control : Fin qubits)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  targets.foldl (fun state target => xorWire target (state control) state) input

theorem h3CnotTargetsOperator119_apply_basisKet
    {qubits : Nat} (targets : List (Fin qubits)) (control : Fin qubits)
    (input : QubitBasis qubits) :
    applyOperator
        (operatorSequence (targets.map fun target =>
          reversibleAnalyticCnotOperator control target))
        (basisKet input) =
      basisKet (h3CnotTargetsBasisAction119 targets control input) := by
  induction targets generalizing input with
  | nil =>
      change Matrix.mulVec (1 : Operator (QubitBasis qubits))
          (basisKet input) = basisKet input
      rw [Matrix.one_mulVec]
  | cons first rest inductionHypothesis =>
      simp only [List.map_cons, operatorSequence, applyOperator_mul]
      rw [h3semanticVerification_cnot_apply_basisKet]
      change applyOperator
          (operatorSequence (rest.map fun target =>
            reversibleAnalyticCnotOperator control target))
          (basisKet (xorWire first (input control) input)) =
        basisKet (h3CnotTargetsBasisAction119 rest control
          (xorWire first (input control) input))
      exact inductionHypothesis _

theorem h3CnotTargetsBasisAction119_apply_outside
    {qubits : Nat} (targets : List (Fin qubits)) (control wire : Fin qubits)
    (input : QubitBasis qubits)
    (outside : ∀ target, target ∈ targets → target ≠ wire) :
    h3CnotTargetsBasisAction119 targets control input wire = input wire := by
  induction targets generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      unfold h3CnotTargetsBasisAction119
      simp only [List.foldl_cons]
      change h3CnotTargetsBasisAction119 rest control
          (xorWire first (input control) input) wire = input wire
      rw [inductionHypothesis]
      · exact xorWire_apply_other first wire (outside first (by simp)).symm
          (input control) input
      · intro target member
        exact outside target (by simp [member])

theorem h3CnotTargetsBasisAction119_apply_of_control_true
    {qubits : Nat} (targets : List (Fin qubits)) (control wire : Fin qubits)
    (input : QubitBasis qubits)
    (nodup : targets.Nodup)
    (controlOutside : ∀ target, target ∈ targets → control ≠ target)
    (controlTrue : input control = true) :
    h3CnotTargetsBasisAction119 targets control input wire =
      if wire ∈ targets then !input wire else input wire := by
  induction targets generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      have firstOutside : first ∉ rest := (List.nodup_cons.mp nodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      have controlNeFirst : control ≠ first := controlOutside first (by simp)
      have controlAfter : xorWire first (input control) input control = true := by
        rw [xorWire_apply_other first control controlNeFirst]
        exact controlTrue
      unfold h3CnotTargetsBasisAction119
      simp only [List.foldl_cons]
      change h3CnotTargetsBasisAction119 rest control
          (xorWire first (input control) input) wire = _
      rw [inductionHypothesis _ restNodup (fun target member =>
        controlOutside target (by simp [member])) controlAfter]
      by_cases restMember : wire ∈ rest
      · have wireNeFirst : wire ≠ first := by
          intro equal
          subst wire
          exact firstOutside restMember
        rw [if_pos restMember, if_pos (by simp [restMember])]
        rw [xorWire_apply_other first wire wireNeFirst]
      · rw [if_neg restMember]
        by_cases equal : wire = first
        · subst wire
          simp [xorWire, controlTrue, firstOutside]
        · rw [if_neg (by simp [equal, restMember])]
          rw [xorWire_apply_other first wire equal]

theorem repairedH3IdleOrderTargets119_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (binaryLabels : Nat) :
    (repairedH3IdleOrderTargets119 layout binaryLabels).Nodup := by
  unfold repairedH3IdleOrderTargets119 h3ConstantBitIndices119
  have base : (List.ofFn (fun index :
      Fin (historyOrderWidth parameters.taylorOrder) => index)).Nodup :=
    List.nodup_ofFn.mpr fun _ _ equal => equal
  exact (base.filter _).map layout.order.injective

theorem repairedH3IdleOrderTargets119_order_mem_iff
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (binaryLabels : Nat)
    (orderIndex : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire orderIndex ∈
        repairedH3IdleOrderTargets119 layout binaryLabels ↔
      (binaryLabels - 1).testBit orderIndex.val := by
  simp [repairedH3IdleOrderTargets119, h3ConstantBitIndices119,
    layout.order.injective.eq_iff]

theorem h3CnotTargetsBasisAction119_repaired_final_eq_zero
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryIdleTransformEvidence layout)
    (binaryLabels : Nat) (input : QubitBasis qubits)
    (controlTrue : input (historyActiveWire layout) = true)
    (inputOrder : ∀ orderIndex,
      input (layout.order.wire orderIndex) =
        (binaryLabels - 1).testBit orderIndex.val) :
    h3CnotTargetsBasisAction119
        (repairedH3IdleOrderTargets119 layout binaryLabels)
        (historyActiveWire layout) input =
      writeRegisterValue layout.order 0 input := by
  funext wire
  rw [h3CnotTargetsBasisAction119_apply_of_control_true]
  · by_cases inside : ∃ orderIndex, layout.order.wire orderIndex = wire
    · rcases inside with ⟨orderIndex, rfl⟩
      rw [writeRegisterValue_apply_wire]
      by_cases bit : (binaryLabels - 1).testBit orderIndex.val
      · rw [if_pos ((repairedH3IdleOrderTargets119_order_mem_iff
          layout binaryLabels orderIndex).2 bit), inputOrder, bit]
        simp
      · have bitFalse : (binaryLabels - 1).testBit orderIndex.val = false :=
          Bool.eq_false_of_not_eq_true bit
        have notMember : layout.order.wire orderIndex ∉
            repairedH3IdleOrderTargets119 layout binaryLabels := by
          intro member
          exact bit ((repairedH3IdleOrderTargets119_order_mem_iff
            layout binaryLabels orderIndex).1 member)
        rw [if_neg notMember, inputOrder, bitFalse]
        simp
    · rw [if_neg]
      · exact (writeRegisterValue_apply_outside layout.order 0 input wire
          (fun orderIndex equal => inside ⟨orderIndex, equal⟩)).symm
      · intro member
        have orderMember := repairedH3IdleOrderTargets119_mem_order
          layout binaryLabels wire member
        simp only [historyRegisterWires, List.mem_ofFn] at orderMember
        rcases orderMember with ⟨orderIndex, equal⟩
        exact inside ⟨orderIndex, equal⟩
  · exact repairedH3IdleOrderTargets119_nodup layout binaryLabels
  · intro target member
    exact evidence.active_ne_order target
      (repairedH3IdleOrderTargets119_mem_order layout binaryLabels target member)
  · exact controlTrue

private theorem h3IdleFlag_ne_branch119
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
  have sharedAtLeast : 5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
    calc
      5 ≤ historyStructuralPoolWidth parameters := by
        unfold historyStructuralPoolWidth
        omega
      _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
        Nat.le_max_right _ _
  omega

private theorem h3IdleFlag_ne_active119
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
  have sharedAtLeast : 5 ≤ historySharedPoolWidth parameters generatorWorkWidth := by
    calc
      5 ≤ historyStructuralPoolWidth parameters := by
        unfold historyStructuralPoolWidth
        omega
      _ ≤ historySharedPoolWidth parameters generatorWorkWidth :=
        Nat.le_max_right _ _
  omega

private theorem h3WorkspaceWire_ne_coefficient119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (workspaceIndex : Fin
      (historyClockWorkspaceWidth parameters generatorWorkWidth)) :
    layout.workspace.wire workspaceIndex ≠ layout.coefficientSignal := by
  have split := List.nodup_append.mp layout.allWiresNodup
  have coefficientInPrefix : layout.coefficientSignal ∈
      historyRegisterWires layout.selector ++
        historyRegisterWires layout.data ++ historyRegisterWires layout.clock ++
        historyRegisterWires layout.order ++
        historyRegisterWires layout.generatorSignal ++
        [layout.coefficientSignal, layout.orderBoundarySignal,
          layout.projectorSignal, layout.clockBoundarySignal] := by
    simp
  have workspaceMember : layout.workspace.wire workspaceIndex ∈
      historyRegisterWires layout.workspace :=
    List.mem_ofFn.mpr ⟨workspaceIndex, rfl⟩
  exact (split.2.2 _ coefficientInPrefix _ workspaceMember).symm

private theorem h3IdleFlag_ne_coefficient119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyIdleFlag layout ≠ layout.coefficientSignal := by
  change layout.workspace.wire _ ≠ layout.coefficientSignal
  exact h3WorkspaceWire_ne_coefficient119 layout _

private theorem h3IdleConjunctionNodup119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ([historyBranchWire layout, historyIdleFlag layout] ++ [] ++
      [historyActiveWire layout]).Nodup := by
  simp [(h3IdleFlag_ne_branch119 layout).symm,
    historyBranchWire_ne_activeWire layout, h3IdleFlag_ne_active119 layout]

theorem h3IdleConjunctionOperator119_apply_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    applyOperator
        (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
          [historyBranchWire layout, historyIdleFlag layout] []
          (historyActiveWire layout)).analyticOperator
        (basisKet input) =
      basisKet (ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyIdleFlag layout]
        (historyActiveWire layout) input) := by
  rw [h3semanticVerification_conjunction_apply_basisKet_of_cleanWork]
  · simp
  · exact h3IdleConjunctionNodup119 layout
  · simp [ClassicalReversibleStage.minimumWorkCleanPredicate]

def h3IdleTransformCleanAction119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (binaryLabels : Nat) (input : QubitBasis qubits) : QubitBasis qubits :=
  let afterEnd := xorWire (historyIdleFlag layout)
    (input (historyLessThanIdleEndWire layout)) input
  let afterTime := xorWire (historyIdleFlag layout)
    (afterEnd (historyLessThanTimeWire layout)) afterEnd
  let afterConjunction :=
    ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) afterTime
  let afterOrder := h3CnotTargetsBasisAction119
    (repairedH3IdleOrderTargets119 layout binaryLabels)
    (historyActiveWire layout) afterConjunction
  let afterRestoreConjunction :=
    ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) afterOrder
  let afterTimeRestore := xorWire (historyIdleFlag layout)
    (afterRestoreConjunction (historyLessThanTimeWire layout))
    afterRestoreConjunction
  xorWire (historyIdleFlag layout)
    (afterTimeRestore (historyLessThanIdleEndWire layout)) afterTimeRestore

def h3IdleTransformDirtyAction119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (binaryLabels : Nat) (input : QubitBasis qubits) : QubitBasis qubits :=
  let afterEnd := xorWire (historyIdleFlag layout)
    (input (historyLessThanIdleEndWire layout)) input
  let afterTime := xorWire (historyIdleFlag layout)
    (afterEnd (historyLessThanTimeWire layout)) afterEnd
  let afterConjunction :=
    ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) afterTime
  let afterOrder := h3CnotTargetsBasisAction119
    (repairedH3IdleOrderTargets119 layout binaryLabels)
    (historyActiveWire layout) afterConjunction
  let afterRotation := replaceQubitWire afterOrder layout.coefficientSignal true
  let afterRestoreConjunction :=
    ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) afterRotation
  let afterTimeRestore := xorWire (historyIdleFlag layout)
    (afterRestoreConjunction (historyLessThanTimeWire layout))
    afterRestoreConjunction
  xorWire (historyIdleFlag layout)
    (afterTimeRestore (historyLessThanIdleEndWire layout)) afterTimeRestore

theorem repairedH3IdleTransformOperator119_apply_basisKet_idle
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryIdleTransformEvidence layout)
    (binaryLabels : Nat) (angle : ℝ) (input : QubitBasis qubits)
    (branchTrue : input (historyBranchWire layout) = true)
    (idleEndTrue : input (historyLessThanIdleEndWire layout) = true)
    (timeFalse : input (historyLessThanTimeWire layout) = false)
    (idleZero : input (historyIdleFlag layout) = false)
    (activeZero : input (historyActiveWire layout) = false)
    (coefficientZero : input layout.coefficientSignal = false) :
    applyOperator
        (repairedH3IdleTransformOperator119 layout evidence binaryLabels angle)
        (basisKet input) =
      ((Real.cos (angle / 2) : Real) : Complex) •
          basisKet (h3IdleTransformCleanAction119 layout binaryLabels input) +
        ((Real.sin (angle / 2) : Real) : Complex) •
          basisKet (h3IdleTransformDirtyAction119 layout binaryLabels input) := by
  let afterEnd := xorWire (historyIdleFlag layout)
    (input (historyLessThanIdleEndWire layout)) input
  let afterTime := xorWire (historyIdleFlag layout)
    (afterEnd (historyLessThanTimeWire layout)) afterEnd
  let afterConjunction :=
    ClassicalReversibleStage.conjunctionDirectBasisAction
      [historyBranchWire layout, historyIdleFlag layout]
      (historyActiveWire layout) afterTime
  let afterOrder := h3CnotTargetsBasisAction119
    (repairedH3IdleOrderTargets119 layout binaryLabels)
    (historyActiveWire layout) afterConjunction
  have endStep := h3semanticVerification_cnot_apply_basisKet
    (historyLessThanIdleEndWire layout) (historyIdleFlag layout) input
  have timeStep := h3semanticVerification_cnot_apply_basisKet
    (historyLessThanTimeWire layout) (historyIdleFlag layout) afterEnd
  have conjunctionStep := h3IdleConjunctionOperator119_apply_basisKet layout afterTime
  have orderStep := h3CnotTargetsOperator119_apply_basisKet
    (repairedH3IdleOrderTargets119 layout binaryLabels)
    (historyActiveWire layout) afterConjunction
  have afterEndIdle : afterEnd (historyIdleFlag layout) = true := by
    simp [afterEnd, xorWire, idleEndTrue, idleZero]
  have afterEndTime : afterEnd (historyLessThanTimeWire layout) = false := by
    unfold afterEnd
    rw [xorWire_apply_other _ _ evidence.time_ne_idle]
    exact timeFalse
  have afterTimeIdle : afterTime (historyIdleFlag layout) = true := by
    simp [afterTime, xorWire, afterEndTime, afterEndIdle]
  have afterEndBranch : afterEnd (historyBranchWire layout) = true := by
    unfold afterEnd
    rw [xorWire_apply_other _ _ (h3IdleFlag_ne_branch119 layout).symm]
    exact branchTrue
  have afterTimeBranch : afterTime (historyBranchWire layout) = true := by
    unfold afterTime
    rw [xorWire_apply_other _ _ (h3IdleFlag_ne_branch119 layout).symm]
    exact afterEndBranch
  have afterEndActive : afterEnd (historyActiveWire layout) = false := by
    unfold afterEnd
    rw [xorWire_apply_other _ _ (h3IdleFlag_ne_active119 layout).symm]
    exact activeZero
  have afterTimeActive : afterTime (historyActiveWire layout) = false := by
    unfold afterTime
    rw [xorWire_apply_other _ _ (h3IdleFlag_ne_active119 layout).symm]
    exact afterEndActive
  have afterConjunctionActive :
      afterConjunction (historyActiveWire layout) = true := by
    simp [afterConjunction,
      ClassicalReversibleStage.conjunctionDirectBasisAction,
      ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires, xorWire, afterTimeBranch,
      afterTimeIdle, afterTimeActive]
  have afterEndCoefficient : afterEnd layout.coefficientSignal = false := by
    unfold afterEnd
    rw [xorWire_apply_other _ _ (h3IdleFlag_ne_coefficient119 layout).symm]
    exact coefficientZero
  have afterTimeCoefficient : afterTime layout.coefficientSignal = false := by
    unfold afterTime
    rw [xorWire_apply_other _ _ (h3IdleFlag_ne_coefficient119 layout).symm]
    exact afterEndCoefficient
  have afterConjunctionCoefficient :
      afterConjunction layout.coefficientSignal = false := by
    unfold afterConjunction
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other]
    · exact afterTimeCoefficient
    · exact evidence.active_ne_coefficient.symm
  have afterOrderActive : afterOrder (historyActiveWire layout) = true := by
    unfold afterOrder
    rw [h3CnotTargetsBasisAction119_apply_outside]
    · exact afterConjunctionActive
    · intro target member
      exact (evidence.active_ne_order target
        (repairedH3IdleOrderTargets119_mem_order layout binaryLabels target member)).symm
  have afterOrderCoefficient : afterOrder layout.coefficientSignal = false := by
    unfold afterOrder
    rw [h3CnotTargetsBasisAction119_apply_outside]
    · exact afterConjunctionCoefficient
    · intro target member
      rcases List.mem_ofFn.mp
        (repairedH3IdleOrderTargets119_mem_order layout binaryLabels target member) with
        ⟨orderIndex, rfl⟩
      exact (layout.orderWire_separated orderIndex).2.2.1
        layout.coefficientSignal (by simp)
  have rotationStep : applyOperator
      (embedControlledSingleQubitOperator (historyActiveWire layout)
        layout.coefficientSignal evidence.active_ne_coefficient (localRy angle))
      (basisKet afterOrder) =
        ((Real.cos (angle / 2) : Real) : Complex) • basisKet afterOrder +
          ((Real.sin (angle / 2) : Real) : Complex) •
            basisKet (replaceQubitWire afterOrder layout.coefficientSignal true) := by
    rw [embedControlledSingleQubitOperator_eq_predicate119]
    exact applyOperator_predicateControlledRy_basisKet_of_true_false119
      (fun basis : QubitBasis qubits => basis (historyActiveWire layout))
      layout.coefficientSignal angle afterOrder afterOrderActive afterOrderCoefficient
  unfold repairedH3IdleTransformOperator119
  simp only [operatorSequence, applyOperator_mul]
  rw [endStep, timeStep, conjunctionStep, orderStep, rotationStep]
  simp_rw [applyOperator_add, applyOperator_smul]
  rw [h3IdleConjunctionOperator119_apply_basisKet,
    h3IdleConjunctionOperator119_apply_basisKet]
  rw [h3semanticVerification_cnot_apply_basisKet, h3semanticVerification_cnot_apply_basisKet,
    h3semanticVerification_cnot_apply_basisKet, h3semanticVerification_cnot_apply_basisKet]
  have oneApply (state : State (QubitBasis qubits)) :
      applyOperator (1 : Operator (QubitBasis qubits)) state = state := by
    exact Matrix.one_mulVec state
  simp_rw [oneApply]
  change
    ((Real.cos (angle / 2) : Real) : Complex) •
        basisKet (h3IdleTransformCleanAction119 layout binaryLabels input) +
      ((Real.sin (angle / 2) : Real) : Complex) •
        basisKet (h3IdleTransformDirtyAction119 layout binaryLabels input) = _
  rfl

end
end ExecutableHistoryExecutableHistory
