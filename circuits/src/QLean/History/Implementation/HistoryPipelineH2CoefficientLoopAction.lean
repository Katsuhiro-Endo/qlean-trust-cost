import QLean.History.Implementation.HistoryPipelineControlledLoopAction
import QLean.History.Implementation.HistoryPipelineH2PostLocality

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

theorem historyTaylorCoefficientIndex_succ_lt_orderPow119
    {parameters : HistoryBlockParameters}
    (index : Fin parameters.taylorOrder) :
    index.val + 1 < 2 ^ historyOrderWidth parameters.taylorOrder := by
  have logBound : parameters.taylorOrder <
      2 ^ (Nat.log2 parameters.taylorOrder + 1) := by
    exact Nat.lt_log2_self
  have widthEq : historyOrderWidth parameters.taylorOrder =
      Nat.log2 parameters.taylorOrder + 1 := by
    unfold historyOrderWidth
    omega
  rw [widthEq]
  exact lt_of_le_of_lt (Nat.succ_le_of_lt index.isLt) logBound

theorem historyTaylorCoefficientIterationPredicate_replace119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (index : Fin parameters.taylorOrder) (value : Bool) :
    ((replaceQubitWire input layout.coefficientSignal value)
          (historyBranchWire layout) &&
        historyTaylorClockLessThanTimeValue layout
          (replaceQubitWire input layout.coefficientSignal value) &&
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1)
          (replaceQubitWire input layout.coefficientSignal value)) =
      (input (historyBranchWire layout) &&
        historyTaylorClockLessThanTimeValue layout input &&
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) input) := by
  have separated := layout.postGeneratorSignal_separated
    layout.coefficientSignal (by simp)
  have branchNe : historyBranchWire layout ≠ layout.coefficientSignal := by
    have member := historyBranchWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, equal⟩
    exact equal.symm ▸ separated.2.2 workspaceIndex
  have clockSame :
      layout.clock.read
          (replaceQubitWire input layout.coefficientSignal value) =
        layout.clock.read input := by
    funext clockIndex
    exact replaceQubitWire_outside input layout.coefficientSignal
      (layout.clock.wire clockIndex) value (separated.2.1 clockIndex)
  have orderSame :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1)
          (replaceQubitWire input layout.coefficientSignal value) =
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) input := by
    apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
    intro wire member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨orderIndex, rfl⟩
    exact replaceQubitWire_outside input layout.coefficientSignal
      (layout.order.wire orderIndex) value
      ((layout.orderWire_separated orderIndex).2.2.1
        layout.coefficientSignal (by simp))
  rw [replaceQubitWire_outside input layout.coefficientSignal
    (historyBranchWire layout) value branchNe]
  unfold historyTaylorClockLessThanTimeValue
  rw [clockSame, orderSame]

/-- Exact action of the independently specified Taylor coefficient loop on a
post-increment basis ket whose order register contains `selected + 1`. -/
theorem applyOperator_historyTaylorCoefficientLoopOperator_selected119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr)
    (selected : Fin parameters.taylorOrder)
    (input : QubitBasis qubits)
    (branchTrue : input (historyBranchWire layout) = true)
    (clockTrue : historyTaylorClockLessThanTimeValue layout input = true)
    (orderSelected :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (selected.val + 1) input = true)
    (signalFalse : input layout.coefficientSignal = false) :
    applyOperator (historyTaylorCoefficientLoopOperator layout angles)
        (basisKet input) =
      ((Real.cos ((angles selected).uniformValue / 2) : Real) : Complex) •
          basisKet input +
        ((Real.sin ((angles selected).uniformValue / 2) : Real) : Complex) •
          basisKet (replaceQubitWire input layout.coefficientSignal true) := by
  let predicate : Fin parameters.taylorOrder → QubitBasis qubits → Bool :=
    fun index basis =>
      basis (historyBranchWire layout) &&
        historyTaylorClockLessThanTimeValue layout basis &&
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) (index.val + 1) basis
  have selectedPredicate : predicate selected input = true := by
    simp [predicate, branchTrue, clockTrue, orderSelected]
  have otherPredicate : ∀ index, index ≠ selected →
      predicate index input = false := by
    intro index indexNe
    have indexBound := historyTaylorCoefficientIndex_succ_lt_orderPow119 index
    have selectedBound :=
      historyTaylorCoefficientIndex_succ_lt_orderPow119 selected
    have registerLength :
        (historyRegisterWires layout.order).length =
          historyOrderWidth parameters.taylorOrder := by
      simp [historyRegisterWires]
    have selectedValue :
        ClassicalReversibleStage.littleEndianListNat
            (ClassicalReversibleStage.readWires
              (historyRegisterWires layout.order) input) =
          selected.val + 1 := by
      rw [ClassicalReversibleStage.littleEndianRegisterEqualsNat_eq_decide
        (historyRegisterWires layout.order) (selected.val + 1) input
        (by simpa [registerLength] using selectedBound)] at orderSelected
      simpa using orderSelected
    unfold predicate
    rw [branchTrue, clockTrue]
    simp only [Bool.true_and]
    rw [ClassicalReversibleStage.littleEndianRegisterEqualsNat_eq_decide
      (historyRegisterWires layout.order) (index.val + 1) input
      (by simpa [registerLength] using indexBound)]
    simp only [decide_eq_false_iff_not]
    intro equalValue
    apply indexNe
    apply Fin.ext
    omega
  unfold historyTaylorCoefficientLoopOperator
  apply applyOperator_single_selected_controlledRy_loop119
    predicate layout.coefficientSignal
    (fun index => (angles index).uniformValue) selected input signalFalse
    selectedPredicate otherPredicate
  intro index value
  exact historyTaylorCoefficientIterationPredicate_replace119
    layout input index value

end
end ExecutableHistoryExecutableHistory
