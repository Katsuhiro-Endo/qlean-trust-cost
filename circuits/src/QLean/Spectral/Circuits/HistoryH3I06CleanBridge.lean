import QLean.Spectral.Circuits.HistoryClockClean
import QLean.Spectral.Analysis.HistoryClockCheckpointSpecifications

/-!
# H3 I06 clean-entry bridge (scratch)

This isolated check connects the actual six-step P16 I06 Exact component to
the H3 deterministic projector action on the all-zero Taylor workspace.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

theorem h3I06_auxiliaryBoundary_equalityFlag_zero
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAuxiliaryBoundaryPredicate layout input) :
    input (historyEqualityFlag layout) = false := by
  apply historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem layout input inside
  unfold historyEqualityFlag
  apply historyWorkspaceSlice_wire_mem

theorem h3I06_auxiliaryBoundary_coefficientControl_zero
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAuxiliaryBoundaryPredicate layout input) :
    input (historyCoefficientControl layout) = false := by
  apply historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem layout input inside
  unfold historyCoefficientControl
  apply historyWorkspaceSlice_wire_mem

theorem h3I06_auxiliaryBoundary_equalityWork_zero
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAuxiliaryBoundaryPredicate layout input)
    (index : Fin (historyEqualityWorkWidth parameters)) :
    (historyEqualityWork layout).read input index = false := by
  unfold Register.read
  apply historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem layout input inside
  unfold historyEqualityWork
  apply historyWorkspaceSlice_wire_mem

theorem h3I06_auxiliaryBoundary_implies_cleanInput
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAuxiliaryBoundaryPredicate layout input) :
    h3I06CleanInputPredicate layout input := by
  exact ⟨h3I06_auxiliaryBoundary_equalityFlag_zero layout input inside,
    h3I06_auxiliaryBoundary_coefficientControl_zero layout input inside⟩

theorem h3I06_equalityWork_ne_equalityFlag
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

theorem h3I06_equalityWork_ne_coefficientControl
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyEqualityWorkWidth parameters)) :
    (historyEqualityWork layout).wire index ≠ historyCoefficientControl layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

theorem h3I06_branch_ne_equalityFlag
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

theorem h3I06_branch_ne_coefficientControl
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

theorem h3I06_equalityFlag_ne_coefficientControl
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

theorem h3I06_order_wire_ne_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (orderIndex : Fin (historyOrderWidth parameters.taylorOrder))
    (workspaceIndex : Fin (historyClockWorkspaceWidth parameters generatorWorkWidth)) :
    layout.order.wire orderIndex ≠ layout.workspace.wire workspaceIndex :=
  (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex

theorem h3I06_equality_enoughScratch
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyRegisterWires layout.order).length ≤
      (historyRegisterWires (historyEqualityWork layout)).length + 2 := by
  simp only [historyRegisterWires, List.length_ofFn]
  unfold historyEqualityWorkWidth historyMaximumLabelWidth
  omega

theorem h3I06_equality_layout_nodup
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
    exact h3I06_equalityWork_ne_equalityFlag layout workIndex
  · intro orderWire orderMember trailing trailingMember
    simp only [historyRegisterWires, List.mem_ofFn] at orderMember
    rcases orderMember with ⟨orderIndex, rfl⟩
    rcases List.mem_append.mp trailingMember with workMember | flagMember
    · simp only [historyRegisterWires, List.mem_ofFn] at workMember
      rcases workMember with ⟨workIndex, rfl⟩
      unfold historyEqualityWork
      apply h3I06_order_wire_ne_workspace layout orderIndex
    · simp only [List.mem_singleton] at flagMember
      subst trailing
      unfold historyEqualityFlag
      apply h3I06_order_wire_ne_workspace layout orderIndex

theorem h3I06_conjunction_layout_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ([historyBranchWire layout, historyEqualityFlag layout] ++ [] ++
      [historyCoefficientControl layout]).Nodup := by
  simp [h3I06_branch_ne_equalityFlag layout,
    h3I06_branch_ne_coefficientControl layout,
    h3I06_equalityFlag_ne_coefficientControl layout]

theorem h3I06_orderEqualsNat_xorWire_invariant
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

theorem h3I06_order_wire_ne_equalityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire index ≠ historyEqualityFlag layout := by
  unfold historyEqualityFlag
  apply h3I06_order_wire_ne_workspace layout index

theorem h3I06_order_wire_ne_coefficientControl
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyOrderWidth parameters.taylorOrder)) :
    layout.order.wire index ≠ historyCoefficientControl layout := by
  unfold historyCoefficientControl
  apply h3I06_order_wire_ne_workspace layout index

theorem h3I06_projector_ne_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyClockWorkspaceWidth parameters generatorWorkWidth)) :
    layout.projectorSignal ≠ layout.workspace.wire index := by
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
  have generatorSplit := List.nodup_append.mp orderSplit.2.1
  have reservedSplit := List.nodup_append.mp generatorSplit.2.1
  exact reservedSplit.2.2 _ (by simp [reservedWires]) _
    (by exact List.mem_ofFn.mpr ⟨index, rfl⟩)

theorem h3I06_workspace_wire_ne_projector
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (wire : Fin qubits)
    (member : wire ∈ historyRegisterWires layout.workspace) :
    wire ≠ layout.projectorSignal := by
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  exact (h3I06_projector_ne_workspace layout index).symm

theorem h3I06_order_wire_ne_projector
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

def h3I06ActualBasisAction
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

def h3I06RecordedBasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  let branchToggle := xorWire layout.projectorSignal
    (input (historyBranchWire layout)) input
  let equality := (historyDegreeZeroEqualityClassicalStage layout).reference
    branchToggle
  let conjunction := (historyProjectorConjunctionClassicalStage layout).reference
    equality
  let projectorToggle := xorWire layout.projectorSignal
    (conjunction (historyCoefficientControl layout)) conjunction
  let unconjunction := (historyProjectorConjunctionClassicalStage layout).reference
    projectorToggle
  (historyDegreeZeroEqualityClassicalStage layout).reference unconjunction

theorem h3I06_projectorControlOperator_apply_basisKet_recorded
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    applyOperator (historyProjectorControlOperator layout) (basisKet input) =
      basisKet (h3I06RecordedBasisAction layout input) := by
  unfold historyProjectorControlOperator
  rw [ClassicalReversibleStage.analyticOperator_eq_deterministicReference,
    ClassicalReversibleStage.analyticOperator_eq_deterministicReference]
  unfold reversibleAnalyticCnotOperator
  dsimp
  simp only [operatorSequence, applyOperator_mul,
    applyOperator_deterministicOperator_basisKet]
  have applyOne (state : State (QubitBasis qubits)) :
      applyOperator (1 : Operator (QubitBasis qubits)) state = state := by
    funext output
    simp only [applyOperator, Matrix.mulVec, dotProduct, Matrix.one_apply]
    simp
  rw [applyOne]
  rfl

theorem h3I06_degreeZeroEquality_reference_eq_direct
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (workZero : ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) input) :
    (historyDegreeZeroEqualityClassicalStage layout).reference input =
      ClassicalReversibleStage.equalityToConstantDirectBasisAction
        (historyRegisterWires layout.order) 0 (historyEqualityFlag layout) input := by
  simpa [historyDegreeZeroEqualityClassicalStage,
    ClassicalReversibleStage.equalityToConstantDirectBasisAction] using
    (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork_reference_apply_of_cleanWork
      (historyRegisterWires layout.order)
      (historyRegisterWires (historyEqualityWork layout)) 0
      (historyEqualityFlag layout) input
      (h3I06_equality_enoughScratch layout)
      (h3I06_equality_layout_nodup layout) workZero)

theorem h3I06_projectorConjunction_reference_eq_direct
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    (historyProjectorConjunctionClassicalStage layout).reference input =
      ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyEqualityFlag layout]
        (historyCoefficientControl layout) input := by
  simpa [historyProjectorConjunctionClassicalStage,
    ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork,
    ClassicalReversibleStage.conjunctionDirectBasisAction] using
    (ClassicalReversibleStage.minimumWorkPositiveMultiControlledX_reference_apply_of_cleanWork
      [historyBranchWire layout, historyEqualityFlag layout] []
      (historyCoefficientControl layout) input (by simp)
      (h3I06_conjunction_layout_nodup layout) (by simp))

theorem h3I06_equalityWork_clean_xorProjector
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Bool) (input : QubitBasis qubits)
    (clean : ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) input) :
    ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout))
      (xorWire layout.projectorSignal value input) := by
  intro wire member
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  rw [xorWire_apply_other layout.projectorSignal
    ((historyEqualityWork layout).wire index) (by
      unfold historyEqualityWork
      exact (h3I06_projector_ne_workspace layout _).symm)]
  exact clean _ (by simp [historyRegisterWires])

theorem h3I06_equalityWork_clean_directEquality
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (clean : ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) input) :
    ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout))
      (ClassicalReversibleStage.equalityToConstantDirectBasisAction
        (historyRegisterWires layout.order) 0 (historyEqualityFlag layout) input) := by
  intro wire member
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
    (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
    ((historyEqualityWork layout).wire index)
    (h3I06_equalityWork_ne_equalityFlag layout index)]
  exact clean _ (by simp [historyRegisterWires])

theorem h3I06_equalityWork_clean_directConjunction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (clean : ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) input) :
    ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout))
      (ClassicalReversibleStage.conjunctionDirectBasisAction
        [historyBranchWire layout, historyEqualityFlag layout]
        (historyCoefficientControl layout) input) := by
  intro wire member
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
    [historyBranchWire layout, historyEqualityFlag layout]
    (historyCoefficientControl layout) ((historyEqualityWork layout).wire index)
    (h3I06_equalityWork_ne_coefficientControl layout index)]
  exact clean _ (by simp [historyRegisterWires])

theorem h3I06_recordedBasisAction_eq_actualBasisAction_of_cleanWork
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inputClean : ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) input) :
    h3I06RecordedBasisAction layout input = h3I06ActualBasisAction layout input := by
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
  have branchClean := h3I06_equalityWork_clean_xorProjector
    layout (input (historyBranchWire layout)) input inputClean
  have equalityClean := h3I06_equalityWork_clean_directEquality
    layout branchToggle branchClean
  have conjunctionClean := h3I06_equalityWork_clean_directConjunction
    layout equality equalityClean
  have projectorClean := h3I06_equalityWork_clean_xorProjector
    layout (conjunction (historyCoefficientControl layout)) conjunction conjunctionClean
  have unconjunctionClean := h3I06_equalityWork_clean_directConjunction
    layout projectorToggle projectorClean
  unfold h3I06RecordedBasisAction h3I06ActualBasisAction
  dsimp only
  rw [h3I06_degreeZeroEquality_reference_eq_direct layout branchToggle branchClean,
    h3I06_projectorConjunction_reference_eq_direct layout equality,
    h3I06_projectorConjunction_reference_eq_direct layout projectorToggle,
    h3I06_degreeZeroEquality_reference_eq_direct layout unconjunction
      unconjunctionClean]

theorem h3I06_actualBasisAction_eq_h3BasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (clean : h3I06CleanInputPredicate layout input) :
    h3I06ActualBasisAction layout input = h3I06BasisAction layout input := by
  let b : Bool := input (historyBranchWire layout)
  let d : Bool := ClassicalReversibleStage.littleEndianRegisterEqualsNat
    (historyRegisterWires layout.order) 0 input
  let s1 := xorWire layout.projectorSignal b input
  let s2 := ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.order) 0 (historyEqualityFlag layout) s1
  let s3 := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyEqualityFlag layout]
    (historyCoefficientControl layout) s2
  let s4 := xorWire layout.projectorSignal
    (s3 (historyCoefficientControl layout)) s3
  let s5 := ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyEqualityFlag layout]
    (historyCoefficientControl layout) s4
  let s6 := ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.order) 0 (historyEqualityFlag layout) s5
  have eMem : historyEqualityFlag layout ∈ historyRegisterWires layout.workspace := by
    unfold historyEqualityFlag
    apply historyWorkspaceSlice_wire_mem
  have cMem : historyCoefficientControl layout ∈ historyRegisterWires layout.workspace := by
    unfold historyCoefficientControl
    apply historyWorkspaceSlice_wire_mem
  have bMem := historyBranchWire_mem_workspace layout
  have b_ne_p : historyBranchWire layout ≠ layout.projectorSignal :=
    h3I06_workspace_wire_ne_projector layout _ bMem
  have e_ne_p : historyEqualityFlag layout ≠ layout.projectorSignal :=
    h3I06_workspace_wire_ne_projector layout _ eMem
  have c_ne_p : historyCoefficientControl layout ≠ layout.projectorSignal :=
    h3I06_workspace_wire_ne_projector layout _ cMem
  have s1Order : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order) 0 s1 = d := by
    dsimp [s1, d]
    exact h3I06_orderEqualsNat_xorWire_invariant layout
      layout.projectorSignal b input (fun index =>
        (h3I06_order_wire_ne_projector layout index).symm)
  have s1E : s1 (historyEqualityFlag layout) = false := by
    dsimp [s1]
    rw [xorWire_apply_other layout.projectorSignal (historyEqualityFlag layout)
      e_ne_p b]
    exact clean.1
  have s1C : s1 (historyCoefficientControl layout) = false := by
    dsimp [s1]
    rw [xorWire_apply_other layout.projectorSignal
      (historyCoefficientControl layout) c_ne_p b]
    exact clean.2
  have s1B : s1 (historyBranchWire layout) = b := by
    dsimp [s1, b]
    rw [xorWire_apply_other layout.projectorSignal (historyBranchWire layout)
      b_ne_p]
  have s1P : s1 layout.projectorSignal = (input layout.projectorSignal != b) := by
    dsimp [s1]
    rw [xorWire_apply_same]
  have s2Order : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order) 0 s2 = d := by
    calc
      _ = ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 s1 := by
        apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
        intro wire member
        simp only [historyRegisterWires, List.mem_ofFn] at member
        rcases member with ⟨index, rfl⟩
        dsimp [s2]
        exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
          (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
          (layout.order.wire index)
          (h3I06_order_wire_ne_equalityFlag layout index) s1
      _ = d := s1Order
  have s2E : s2 (historyEqualityFlag layout) = d := by
    dsimp [s2]
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
      s1E, s1Order]
    cases d <;> rfl
  have s2B : s2 (historyBranchWire layout) = b := by
    dsimp [s2]
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
      (historyBranchWire layout) (h3I06_branch_ne_equalityFlag layout)]
    exact s1B
  have s2C : s2 (historyCoefficientControl layout) = false := by
    dsimp [s2]
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
       (historyCoefficientControl layout)
       (h3I06_equalityFlag_ne_coefficientControl layout).symm]
    exact s1C
  have s2P : s2 layout.projectorSignal = (input layout.projectorSignal != b) := by
    dsimp [s2]
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
      layout.projectorSignal e_ne_p.symm]
    exact s1P
  have s3Order : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order) 0 s3 = d := by
    calc
      _ = ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 s2 := by
        apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
        intro wire member
        simp only [historyRegisterWires, List.mem_ofFn] at member
        rcases member with ⟨index, rfl⟩
        dsimp [s3]
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyEqualityFlag layout]
          (historyCoefficientControl layout) (layout.order.wire index)
          (h3I06_order_wire_ne_coefficientControl layout index) s2
      _ = d := s2Order
  have s3C : s3 (historyCoefficientControl layout) = (b && d) := by
    dsimp [s3]
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target]
    simp [ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires, s2C, s2B, s2E]
  have s3B : s3 (historyBranchWire layout) = b := by
    dsimp [s3]
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyEqualityFlag layout]
      (historyCoefficientControl layout) (historyBranchWire layout)
      (h3I06_branch_ne_coefficientControl layout)]
    exact s2B
  have s3E : s3 (historyEqualityFlag layout) = d := by
    dsimp [s3]
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyEqualityFlag layout]
      (historyCoefficientControl layout) (historyEqualityFlag layout)
      (h3I06_equalityFlag_ne_coefficientControl layout)]
    exact s2E
  have s3P : s3 layout.projectorSignal = (input layout.projectorSignal != b) := by
    dsimp [s3]
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyEqualityFlag layout]
      (historyCoefficientControl layout) layout.projectorSignal c_ne_p.symm]
    exact s2P
  have s4Order : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order) 0 s4 = d := by
    calc
      _ = ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 s3 := by
        dsimp [s4]
        exact h3I06_orderEqualsNat_xorWire_invariant layout
          layout.projectorSignal (s3 (historyCoefficientControl layout)) s3
          (fun index => (h3I06_order_wire_ne_projector layout index).symm)
      _ = d := s3Order
  have s4B : s4 (historyBranchWire layout) = b := by
    dsimp [s4]
    rw [xorWire_apply_other layout.projectorSignal (historyBranchWire layout)
      b_ne_p]
    exact s3B
  have s4E : s4 (historyEqualityFlag layout) = d := by
    dsimp [s4]
    rw [xorWire_apply_other layout.projectorSignal (historyEqualityFlag layout)
      e_ne_p]
    exact s3E
  have s4C : s4 (historyCoefficientControl layout) = (b && d) := by
    dsimp [s4]
    rw [xorWire_apply_other layout.projectorSignal
      (historyCoefficientControl layout) c_ne_p]
    exact s3C
  have s4P : s4 layout.projectorSignal =
      ((input layout.projectorSignal != b) != (b && d)) := by
    dsimp [s4]
    rw [xorWire_apply_same, s3P, s3C]
  have s5Order : ClassicalReversibleStage.littleEndianRegisterEqualsNat
      (historyRegisterWires layout.order) 0 s5 = d := by
    calc
      _ = ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 s4 := by
        apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
        intro wire member
        simp only [historyRegisterWires, List.mem_ofFn] at member
        rcases member with ⟨index, rfl⟩
        dsimp [s5]
        exact ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
          [historyBranchWire layout, historyEqualityFlag layout]
          (historyCoefficientControl layout) (layout.order.wire index)
          (h3I06_order_wire_ne_coefficientControl layout index) s4
      _ = d := s4Order
  have s5C : s5 (historyCoefficientControl layout) = false := by
    dsimp [s5]
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target]
    simp [ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires, s4C, s4B, s4E]
  have s5P : s5 layout.projectorSignal =
      ((input layout.projectorSignal != b) != (b && d)) := by
    dsimp [s5]
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyEqualityFlag layout]
      (historyCoefficientControl layout) layout.projectorSignal c_ne_p.symm]
    exact s4P
  have s6E : s6 (historyEqualityFlag layout) = false := by
    dsimp [s6]
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target]
    have s5E : s5 (historyEqualityFlag layout) = d := by
      dsimp [s5]
      rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
        [historyBranchWire layout, historyEqualityFlag layout]
        (historyCoefficientControl layout) (historyEqualityFlag layout)
        (h3I06_equalityFlag_ne_coefficientControl layout)]
      exact s4E
    rw [s5E, s5Order]
    cases d <;> rfl
  have s6C : s6 (historyCoefficientControl layout) = false := by
    dsimp [s6]
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
       (historyCoefficientControl layout)
       (h3I06_equalityFlag_ne_coefficientControl layout).symm]
    exact s5C
  have s6P : s6 layout.projectorSignal =
      ((input layout.projectorSignal != b) != (b && d)) := by
    dsimp [s6]
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
      layout.projectorSignal e_ne_p.symm]
    exact s5P
  unfold h3I06ActualBasisAction h3I06BasisAction h3I06ProjectorPredicate
  change s6 = xorWire layout.projectorSignal (b && !d) input
  funext wire
  by_cases wireP : wire = layout.projectorSignal
  · subst wire
    rw [s6P]
    rw [xorWire_apply_same]
    cases input layout.projectorSignal <;> cases b <;> cases d <;> rfl
  by_cases wireE : wire = historyEqualityFlag layout
  · subst wire
    rw [s6E, xorWire_apply_other layout.projectorSignal
      (historyEqualityFlag layout) e_ne_p]
    exact clean.1.symm
  by_cases wireC : wire = historyCoefficientControl layout
  · subst wire
    rw [s6C, xorWire_apply_other layout.projectorSignal
      (historyCoefficientControl layout) c_ne_p]
    exact clean.2.symm
  have s6Other : s6 wire = input wire := by
    dsimp [s6]
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
      wire wireE]
    dsimp [s5]
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyEqualityFlag layout]
      (historyCoefficientControl layout) wire wireC]
    dsimp [s4]
    rw [xorWire_apply_other layout.projectorSignal wire wireP]
    dsimp [s3]
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
      [historyBranchWire layout, historyEqualityFlag layout]
      (historyCoefficientControl layout) wire wireC]
    dsimp [s2]
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
      (historyRegisterWires layout.order) 0 (historyEqualityFlag layout)
      wire wireE]
    dsimp [s1]
    exact xorWire_apply_other layout.projectorSignal wire wireP b input
  rw [s6Other, xorWire_apply_other layout.projectorSignal wire wireP]

theorem h3I06_projectorControlOperator_apply_basisKet_of_cleanEntry
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (workClean : ClassicalReversibleStage.minimumWorkCleanPredicate
      (historyRegisterWires (historyEqualityWork layout)) input)
    (clean : h3I06CleanInputPredicate layout input) :
    applyOperator (historyProjectorControlOperator layout) (basisKet input) =
      basisKet (h3I06BasisAction layout input) := by
  rw [h3I06_projectorControlOperator_apply_basisKet_recorded,
    h3I06_recordedBasisAction_eq_actualBasisAction_of_cleanWork layout input workClean,
    h3I06_actualBasisAction_eq_h3BasisAction layout input clean]

theorem h3I06_projectorControlOperator_apply_basisKet_of_auxiliaryBoundary
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAuxiliaryBoundaryPredicate layout input) :
    applyOperator (historyProjectorControlOperator layout) (basisKet input) =
      basisKet (h3I06BasisAction layout input) := by
  apply h3I06_projectorControlOperator_apply_basisKet_of_cleanEntry layout input
  · intro wire member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨index, rfl⟩
    exact h3I06_auxiliaryBoundary_equalityWork_zero layout input inside index
  · exact h3I06_auxiliaryBoundary_implies_cleanInput layout input inside

end SpectralSamplingProof.Components
