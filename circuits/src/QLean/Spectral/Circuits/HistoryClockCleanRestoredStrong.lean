import QLean.Spectral.Circuits.HistoryClockCleanRestored
import QLean.Spectral.Circuits.HistoryH3I06CleanBridge

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

/-- The externally controlled I02 inverse is literally identity on a basis
ket when its frozen active control is zero. -/
theorem h3semanticVerification_i02_apply_basisKet_of_active_zero
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryClockConcreteSourceOrderEvidence layout)
    (input : QubitBasis qubits)
    (activeZero : input (historyActiveWire layout) = false) :
    applyOperator
        (ExternallyControlledPrimitivePlan.semanticPlanOperator (fun _ => 0)
          (historyOrderUniformExternalControlLayout layout
            evidence.uniformExternalControl)
          (shuklaVedulaWidthOnlyUniformInversePlan
            (historyOrderUniformPreparationParameters parameters)))
        (basisKet input) = basisKet input := by
  rw [ExternallyControlledPrimitivePlan.semanticPlanOperator_eq_controlledWireLift]
  funext output
  rw [applyOperator_basisKet,
    externallyControlledWireLiftOperator_apply]
  simp [historyOrderUniformExternalControlLayout, activeZero, basisKet]

/-- A controlled one-qubit semantic operator is identity on a control-false
basis ket, independently of its local matrix. -/
theorem h3semanticVerification_controlled_single_apply_basisKet_of_control_false
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ) (input : QubitBasis qubits)
    (controlFalse : input control = false) :
    applyOperator
        (embedControlledSingleQubitOperator control target different localOperator)
        (basisKet input) = basisKet input := by
  funext output
  rw [applyOperator_basisKet,
    embedControlledSingleQubitOperator_apply_sparse]
  simp only [controlFalse, Bool.false_eq_true, ↓reduceIte, basisKet]
  by_cases outside : agreesExcept target output input
  · by_cases targetEqual : output target = input target
    · have equal : output = input := by
        funext wire
        by_cases isTarget : wire = target
        · simpa [isTarget] using targetEqual
        · exact outside wire isTarget
      subst output
      simp [agreesExcept]
    · have different : output ≠ input := by
        intro equal
        apply targetEqual
        exact congrFun equal target
      simp [outside, targetEqual, different]
  · have different : output ≠ input := by
      intro equal
      apply outside
      subst output
      exact fun _ _ => rfl
    simp [outside, different]

/-- The actual I01 target has the expected scratch-free equality action. -/
theorem h3semanticVerification_i01_apply_basisKet
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    applyOperator (historySelectorEqualityClassicalStage layout).analyticOperator
      (basisKet input) =
      basisKet
        (ClassicalReversibleStage.equalityToConstantDirectBasisAction
          (historyRegisterWires layout.selector) 2 (historyBranchWire layout)
          input) := by
  rw [ClassicalReversibleStage.analyticOperator_eq_deterministicReference,
    applyOperator_deterministicOperator_basisKet]
  apply congrArg basisKet
  simpa [historySelectorEqualityClassicalStage,
    ClassicalReversibleStage.equalityToConstantDirectBasisAction] using
    (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork_reference_apply_of_cleanWork
      (historyRegisterWires layout.selector) [] 2 (historyBranchWire layout)
      input (by simp [historyRegisterWires])
      (historyTaylorSelectorEqualityLayout_nodup layout)
      (by simp))

/-- The semantic CNOT is the corresponding deterministic XOR on basis kets. -/
theorem h3semanticVerification_cnot_apply_basisKet
    {qubits : Nat} (control target : Fin qubits) (input : QubitBasis qubits) :
    applyOperator (reversibleAnalyticCnotOperator control target) (basisKet input) =
      basisKet (xorWire target (input control) input) := by
  simpa [reversibleAnalyticCnotOperator] using
    (applyOperator_deterministicOperator_basisKet
      (fun basis : QubitBasis qubits => xorWire target (basis control) basis)
      input)

/-- The source-faithful conjunction compiler has its direct Boolean action
on an explicitly clean minimum-work boundary. -/
theorem h3semanticVerification_conjunction_apply_basisKet_of_cleanWork
    {qubits : Nat} (controls scratches : List (Fin qubits)) (target : Fin qubits)
    (input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length + 2)
    (layoutNodup : (controls ++ scratches ++ [target]).Nodup)
    (clean : ClassicalReversibleStage.minimumWorkCleanPredicate scratches input) :
    applyOperator
        (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
          controls scratches target).analyticOperator
        (basisKet input) =
      basisKet (ClassicalReversibleStage.conjunctionDirectBasisAction
        controls target input) := by
  rw [ClassicalReversibleStage.analyticOperator_eq_deterministicReference,
    applyOperator_deterministicOperator_basisKet]
  apply congrArg basisKet
  simpa [ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork,
    ClassicalReversibleStage.conjunctionDirectBasisAction] using
    (ClassicalReversibleStage.minimumWorkPositiveMultiControlledX_reference_apply_of_cleanWork
      controls scratches target input enoughScratch layoutNodup clean)

/- Experimental pointwise expansion retained while the dedicated I06 bridge
scratch closes the corresponding public theorem. -/
/-
private def h3semanticVerification_i06_actual_basis_action
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  let branchToggle := xorWire layout.projectorSignal
    (input (historyBranchWire layout)) input
  let equality := ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.order) 0 (historyEqualityFlag layout) branchToggle
  let conjunction := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyEqualityFlag layout]
    (historyCoefficientControl layout) equality
  let projectorToggle := xorWire layout.projectorSignal
    (conjunction (historyCoefficientControl layout)) conjunction
  let unconjunction := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyEqualityFlag layout]
    (historyCoefficientControl layout) projectorToggle
  ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
    unconjunction

private theorem h3semanticVerification_branch_ne_equality_flag
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
  unfold historySharedPoolWidth historyStructuralPoolWidth at valuesEqual
  omega

private theorem h3semanticVerification_branch_ne_coefficient_control
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyBranchWire layout ≠ historyCoefficientControl layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  unfold historySharedPoolWidth historyStructuralPoolWidth at valuesEqual
  omega

private theorem h3semanticVerification_equality_flag_ne_coefficient_control
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyEqualityFlag layout ≠ historyCoefficientControl layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

private theorem h3semanticVerification_order_eq_xor_invariant
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (target : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (outside : ∀ index, target ≠ layout.order.wire index) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) 0 (xorWire target value input) =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) 0 input := by
  apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
  intro wire member
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  exact xorWire_apply_other target (layout.order.wire index)
    (outside index).symm value input

private theorem h3semanticVerification_order_ne_projector
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire index ≠ layout.projectorSignal := by
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
      reservedWires, workspaceWires, List.append_assoc] using layout.allWiresNodup
  have selectorSplit := List.nodup_append.mp normalized
  have dataSplit := List.nodup_append.mp selectorSplit.2.1
  have clockSplit := List.nodup_append.mp dataSplit.2.1
  have orderSplit := List.nodup_append.mp clockSplit.2.1
  exact orderSplit.2.2 _ (List.mem_ofFn.mpr ⟨index, rfl⟩) _
    (List.mem_append_right _ (List.mem_append_left _ (by simp [reservedWires])))

private theorem h3semanticVerification_order_ne_equality_flag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire index ≠ historyEqualityFlag layout := by
  unfold historyEqualityFlag
  exact (layout.orderWire_separated index).2.2.2 _

private theorem h3semanticVerification_order_ne_coefficient_control
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire index ≠ historyCoefficientControl layout := by
  unfold historyCoefficientControl
  exact (layout.orderWire_separated index).2.2.2 _

private theorem h3semanticVerification_i06_actual_basis_action_eq_h3_action
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (clean : h3I06CleanInputPredicate layout input) :
    h3semanticVerification_i06_actual_basis_action layout input = h3I06BasisAction layout input := by
  let branchToggle := xorWire layout.projectorSignal
    (input (historyBranchWire layout)) input
  let equality := ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.order) 0 (historyEqualityFlag layout) branchToggle
  let conjunction := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyEqualityFlag layout]
    (historyCoefficientControl layout) equality
  let projectorToggle := xorWire layout.projectorSignal
    (conjunction (historyCoefficientControl layout)) conjunction
  let unconjunction := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyEqualityFlag layout]
    (historyCoefficientControl layout) projectorToggle
  let degreeZero := ClassicalReversibleStage.littleEndianRegisterEqualsNat
    (historyRegisterWires layout.order) 0 input
  have projector_ne_equality : layout.projectorSignal ≠ historyEqualityFlag layout := by
    unfold historyEqualityFlag
    exact (h3semanticVerification_workspace_wire_ne_projector layout _).symm
  have projector_ne_coefficient : layout.projectorSignal ≠
      historyCoefficientControl layout := by
    unfold historyCoefficientControl
    exact (h3semanticVerification_workspace_wire_ne_projector layout _).symm
  have degree_branchToggle :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 branchToggle = degreeZero := by
    dsimp [branchToggle, degreeZero]
    exact h3semanticVerification_order_eq_xor_invariant layout layout.projectorSignal
      (input (historyBranchWire layout)) input
      (fun index => (h3semanticVerification_order_ne_projector layout index).symm)
  have equality_branch : equality (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    calc
      equality (historyBranchWire layout) = branchToggle (historyBranchWire layout) := by
        dsimp [equality]
        exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          _ _ _ _ (h3semanticVerification_branch_ne_equality_flag layout) branchToggle
      _ = input (historyBranchWire layout) := by
        dsimp [branchToggle]
        exact xorWire_apply_other _ _ evidence.projectorControl.branch_ne_projector _ _
  have equality_flag : equality (historyEqualityFlag layout) = degreeZero := by
    dsimp [equality]
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
      degree_branchToggle, clean.1]
    cases degreeZero <;> rfl
  have equality_control : equality (historyCoefficientControl layout) = false := by
    calc
      equality (historyCoefficientControl layout) =
          branchToggle (historyCoefficientControl layout) := by
        dsimp [equality]
        exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          _ _ _ _ (h3semanticVerification_equality_flag_ne_coefficient_control layout) branchToggle
      _ = input (historyCoefficientControl layout) := by
        dsimp [branchToggle]
        exact xorWire_apply_other _ _ projector_ne_coefficient _ _
      _ = false := clean.2
  have equality_projector : equality layout.projectorSignal =
      (input layout.projectorSignal != input (historyBranchWire layout)) := by
    calc
      equality layout.projectorSignal = branchToggle layout.projectorSignal := by
        dsimp [equality]
        exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          _ _ _ _ projector_ne_equality.symm branchToggle
      _ = _ := by
        dsimp [branchToggle]
        exact xorWire_apply_same _ _ _
  have conjunction_branch : conjunction (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    calc
      conjunction (historyBranchWire layout) = equality (historyBranchWire layout) := by
        dsimp [conjunction]
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          _ _ _ (h3semanticVerification_branch_ne_coefficient_control layout) equality
      _ = _ := equality_branch
  have conjunction_flag : conjunction (historyEqualityFlag layout) = degreeZero := by
    calc
      conjunction (historyEqualityFlag layout) = equality (historyEqualityFlag layout) := by
        dsimp [conjunction]
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          _ _ _ (h3semanticVerification_equality_flag_ne_coefficient_control layout) equality
      _ = _ := equality_flag
  have conjunction_control : conjunction (historyCoefficientControl layout) =
      (input (historyBranchWire layout) && degreeZero) := by
    dsimp [conjunction]
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target,
      equality_control]
    simp only [Bool.false_bne]
    simp [ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires, equality_branch, equality_flag]
  have conjunction_projector : conjunction layout.projectorSignal =
      (input layout.projectorSignal != input (historyBranchWire layout)) := by
    calc
      conjunction layout.projectorSignal = equality layout.projectorSignal := by
        dsimp [conjunction]
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          _ _ _ projector_ne_coefficient.symm equality
      _ = _ := equality_projector
  have projector_branch : projectorToggle (historyBranchWire layout) =
      input (historyBranchWire layout) := by
    dsimp [projectorToggle]
    rw [xorWire_apply_other _ _ evidence.projectorControl.branch_ne_projector]
    exact conjunction_branch
  have projector_flag : projectorToggle (historyEqualityFlag layout) = degreeZero := by
    dsimp [projectorToggle]
    rw [xorWire_apply_other _ _ projector_ne_equality]
    exact conjunction_flag
  have projector_control : projectorToggle (historyCoefficientControl layout) =
      (input (historyBranchWire layout) && degreeZero) := by
    dsimp [projectorToggle]
    rw [xorWire_apply_other _ _ projector_ne_coefficient]
    exact conjunction_control
  have projector_projector : projectorToggle layout.projectorSignal =
      (input layout.projectorSignal !=
        (input (historyBranchWire layout) && !degreeZero)) := by
    dsimp [projectorToggle]
    rw [xorWire_apply_same, conjunction_control]
    rw [equality_projector]
    cases input (historyBranchWire layout) <;> cases degreeZero <;>
      cases input layout.projectorSignal <;> rfl
  have unconjunction_control : unconjunction (historyCoefficientControl layout) = false := by
    dsimp [unconjunction]
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target,
      projector_control]
    simp only [Bool.and_self, Bool.not_false_eq_true, Bool.false_bne]
    simp [ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires, projector_branch, projector_flag]
  have unconjunction_flag : unconjunction (historyEqualityFlag layout) = degreeZero := by
    calc
      unconjunction (historyEqualityFlag layout) =
          projectorToggle (historyEqualityFlag layout) := by
        dsimp [unconjunction]
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          _ _ _ (h3semanticVerification_equality_flag_ne_coefficient_control layout) projectorToggle
      _ = _ := projector_flag
  have unconjunction_projector : unconjunction layout.projectorSignal =
      (input layout.projectorSignal !=
        (input (historyBranchWire layout) && !degreeZero)) := by
    calc
      unconjunction layout.projectorSignal = projectorToggle layout.projectorSignal := by
        dsimp [unconjunction]
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          _ _ _ projector_ne_coefficient.symm projectorToggle
      _ = _ := projector_projector
  have degree_unconjunction :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 unconjunction = degreeZero := by
    dsimp [unconjunction, projectorToggle, conjunction, equality, branchToggle,
      degreeZero]
    repeat' first
      | rw [h3semanticVerification_order_eq_xor_invariant layout _ _ _]
    all_goals
      try exact fun index => (h3semanticVerification_order_ne_coefficient_control layout index).symm
      try exact fun index => (h3semanticVerification_order_ne_projector layout index).symm
      try exact fun index => (h3semanticVerification_order_ne_equality_flag layout index).symm
  unfold h3semanticVerification_i06_actual_basis_action h3I06BasisAction h3I06ProjectorPredicate
  change ClassicalReversibleStage.equalityToConstantDirectBasisAction
      (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
      unconjunction = xorWire layout.projectorSignal
        (input (historyBranchWire layout) && !degreeZero) input
  funext wire
  by_cases isProjector : wire = layout.projectorSignal
  · subst wire
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      _ _ _ _ projector_ne_equality.symm, unconjunction_projector,
      xorWire_apply_same]
  · by_cases isEquality : wire = historyEqualityFlag layout
    · subst wire
      rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
        unconjunction_flag, degree_unconjunction]
      cases degreeZero <;> rfl
    · by_cases isControl : wire = historyCoefficientControl layout
      · subst wire
        rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          _ _ _ _ (h3semanticVerification_equality_flag_ne_coefficient_control layout),
          unconjunction_control, xorWire_apply_other _ _ (by
            intro equal
            exact projector_ne_coefficient equal.symm)]
        exact clean.2.symm
      · calc
          ClassicalReversibleStage.equalityToConstantDirectBasisAction
              (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
              unconjunction wire = unconjunction wire :=
            ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
              _ _ _ _ isEquality unconjunction
          _ = projectorToggle wire := by
            dsimp [unconjunction]
            exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
              _ _ _ isControl projectorToggle
          _ = conjunction wire := by
            dsimp [projectorToggle]
            exact xorWire_apply_other _ _ isProjector _ _
          _ = equality wire := by
            dsimp [conjunction]
            exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
              _ _ _ isControl equality
          _ = branchToggle wire := by
            dsimp [equality]
            exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
              _ _ _ _ isEquality branchToggle
          _ = input wire := by
            dsimp [branchToggle]
            exact xorWire_apply_other _ _ isProjector _ _
          _ = xorWire layout.projectorSignal
              (input (historyBranchWire layout) && !degreeZero) input wire := by
            symm
            exact xorWire_apply_other _ _ isProjector _ _
-/

end

end SpectralSamplingProof.Components
