import QLean.History.Implementation.HistoryPipelineH2RaisedBasis

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof.Analytic
open ExecutableHistoryHistoryEmbedding

noncomputable section

theorem writeRegisterValue_xorWire_commute119
    {qubits width : Nat}
    (register : Register qubits width)
    (signal : Fin qubits)
    (separated : ∀ index, register.wire index ≠ signal)
    (value : Nat) (control : Bool) (input : QubitBasis qubits) :
    writeRegisterValue register value (xorWire signal control input) =
      xorWire signal control (writeRegisterValue register value input) := by
  funext wire
  by_cases inside : ∃ index, register.wire index = wire
  · rcases inside with ⟨index, rfl⟩
    rw [writeRegisterValue_apply_wire]
    rw [xorWire_apply_other signal (register.wire index) (separated index)]
    rw [writeRegisterValue_apply_wire]
  · have outside : ∀ index, register.wire index ≠ wire := by
      intro index equal
      exact inside ⟨index, equal⟩
    rw [writeRegisterValue_apply_outside register value _ wire outside]
    by_cases equal : wire = signal
    · subst wire
      simp only [xorWire_apply_same]
      rw [writeRegisterValue_apply_outside register value input signal outside]
    · rw [xorWire_apply_other signal wire equal,
        xorWire_apply_other signal wire equal,
        writeRegisterValue_apply_outside register value input wire outside]

theorem littleEndianRegisterEqualsNat_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value constant : Nat) (input : QubitBasis qubits) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) constant
        (writeRegisterValue layout.order value input) =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) constant input := by
  apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
  intro wire member
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨selectorIndex, rfl⟩
  exact writeRegisterValue_apply_outside layout.order value input
    (layout.selector.wire selectorIndex) (by
      intro orderIndex equal
      exact (layout.orderWire_separated orderIndex).1 selectorIndex equal)

theorem historyTaylorClockLessThanTimeValue_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    historyTaylorClockLessThanTimeValue layout
        (writeRegisterValue layout.order value input) =
      historyTaylorClockLessThanTimeValue layout input := by
  unfold historyTaylorClockLessThanTimeValue
  apply congrArg₂ unsignedLessThanBits
  · funext clockIndex
    exact writeRegisterValue_apply_outside layout.order value input
      (layout.clock.wire clockIndex) (by
        intro orderIndex equal
        exact (layout.orderWire_separated orderIndex).2.1 clockIndex equal)
  · rfl

theorem historyTaylorClockLessThanIdleEndValue_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    historyTaylorClockLessThanIdleEndValue layout
        (writeRegisterValue layout.order value input) =
      historyTaylorClockLessThanIdleEndValue layout input := by
  unfold historyTaylorClockLessThanIdleEndValue
  apply congrArg₂ unsignedLessThanBits
  · funext clockIndex
    exact writeRegisterValue_apply_outside layout.order value input
      (layout.clock.wire clockIndex) (by
        intro orderIndex equal
        exact (layout.orderWire_separated orderIndex).2.1 clockIndex equal)
  · rfl

theorem historyTaylorSelectorEqualityBasisAction_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    historyTaylorSelectorEqualityBasisAction layout
        (writeRegisterValue layout.order value input) =
      writeRegisterValue layout.order value
        (historyTaylorSelectorEqualityBasisAction layout input) := by
  unfold historyTaylorSelectorEqualityBasisAction
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [littleEndianRegisterEqualsNat_write_order119]
  exact (writeRegisterValue_xorWire_commute119 layout.order
    (historyBranchWire layout) (by
      intro orderIndex
      have member := historyBranchWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      intro equal
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm))
    value _ input).symm

theorem historyTaylorTimeComparisonBasisAction_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    historyTaylorTimeComparisonBasisAction layout
        (writeRegisterValue layout.order value input) =
      writeRegisterValue layout.order value
        (historyTaylorTimeComparisonBasisAction layout input) := by
  unfold historyTaylorTimeComparisonBasisAction
  rw [historyTaylorClockLessThanTimeValue_write_order119]
  exact (writeRegisterValue_xorWire_commute119 layout.order
    (historyLessThanTimeWire layout) (by
      intro orderIndex
      have member := historyLessThanTimeWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      intro equal
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm))
    value _ input).symm

theorem historyTaylorIdleEndComparisonBasisAction_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    historyTaylorIdleEndComparisonBasisAction layout
        (writeRegisterValue layout.order value input) =
      writeRegisterValue layout.order value
        (historyTaylorIdleEndComparisonBasisAction layout input) := by
  unfold historyTaylorIdleEndComparisonBasisAction
  rw [historyTaylorClockLessThanIdleEndValue_write_order119]
  exact (writeRegisterValue_xorWire_commute119 layout.order
    (historyLessThanIdleEndWire layout) (by
      intro orderIndex
      have member := historyLessThanIdleEndWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      intro equal
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (equal.trans member.symm))
    value _ input).symm

theorem h2AfterIdleEnd119_write_order119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Nat) (input : QubitBasis qubits) :
    h2AfterIdleEnd119 layout (writeRegisterValue layout.order value input) =
      writeRegisterValue layout.order value (h2AfterIdleEnd119 layout input) := by
  unfold h2AfterIdleEnd119 h2AfterTime119 h2AfterSelector119
  rw [historyTaylorSelectorEqualityBasisAction_write_order119,
    historyTaylorTimeComparisonBasisAction_write_order119,
    historyTaylorIdleEndComparisonBasisAction_write_order119]

theorem h2AfterIdleEnd119_raiseHistoryLabel119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (labelLt : index.state.label.val < source.historyParameters.taylorOrder) :
    h2AfterIdleEnd119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch
          (raiseHistoryLabel119 source index configuration labelLt)) =
      writeRegisterValue (ExecutableLayout119 source domain).order
        (index.state.label.val + 1)
        (h2AfterIdleEnd119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits branch
            (replaceConfiguration119 source index configuration))) := by
  rw [← writeRegisterValue_correctedBranchHistoryBasis119_raiseLabel]
  exact h2AfterIdleEnd119_write_order119
    (ExecutableLayout119 source domain) (index.state.label.val + 1)
    (correctedBranchHistoryBasis119 source domain fits branch
      (replaceConfiguration119 source index configuration))

theorem replaceQubitWire_xorWire_commute119
    {qubits : Nat}
    (signal target : Fin qubits) (different : signal ≠ target)
    (control value : Bool) (input : QubitBasis qubits) :
    replaceQubitWire (xorWire signal control input) target value =
      xorWire signal control (replaceQubitWire input target value) := by
  funext wire
  by_cases signalWire : wire = signal
  · subst wire
    simp [xorWire, replaceQubitWire, different]
  · by_cases targetWire : wire = target
    · subst wire
      simp [xorWire, replaceQubitWire, different, signalWire]
    · simp [xorWire, replaceQubitWire, signalWire, targetWire]

theorem littleEndianRegisterEqualsNat_replace_coefficient119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (constant : Nat) (value : Bool) (input : QubitBasis qubits) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) constant
        (replaceQubitWire input layout.coefficientSignal value) =
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) constant input := by
  have separated := layout.postGeneratorSignal_separated
    layout.coefficientSignal (by simp)
  apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
  intro wire member
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨selectorIndex, rfl⟩
  exact replaceQubitWire_outside input layout.coefficientSignal
    (layout.selector.wire selectorIndex) value (separated.1 selectorIndex)

theorem historyTaylorClockLessThanTimeValue_replace_coefficient119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Bool) (input : QubitBasis qubits) :
    historyTaylorClockLessThanTimeValue layout
        (replaceQubitWire input layout.coefficientSignal value) =
      historyTaylorClockLessThanTimeValue layout input := by
  have separated := layout.postGeneratorSignal_separated
    layout.coefficientSignal (by simp)
  unfold historyTaylorClockLessThanTimeValue
  apply congrArg₂ unsignedLessThanBits
  · funext clockIndex
    exact replaceQubitWire_outside input layout.coefficientSignal
      (layout.clock.wire clockIndex) value (separated.2.1 clockIndex)
  · rfl

theorem historyTaylorClockLessThanIdleEndValue_replace_coefficient119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Bool) (input : QubitBasis qubits) :
    historyTaylorClockLessThanIdleEndValue layout
        (replaceQubitWire input layout.coefficientSignal value) =
      historyTaylorClockLessThanIdleEndValue layout input := by
  have separated := layout.postGeneratorSignal_separated
    layout.coefficientSignal (by simp)
  unfold historyTaylorClockLessThanIdleEndValue
  apply congrArg₂ unsignedLessThanBits
  · funext clockIndex
    exact replaceQubitWire_outside input layout.coefficientSignal
      (layout.clock.wire clockIndex) value (separated.2.1 clockIndex)
  · rfl

theorem h2AfterIdleEnd119_replace_coefficient119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (value : Bool) (input : QubitBasis qubits) :
    h2AfterIdleEnd119 layout
        (replaceQubitWire input layout.coefficientSignal value) =
      replaceQubitWire (h2AfterIdleEnd119 layout input)
        layout.coefficientSignal value := by
  have separated := layout.postGeneratorSignal_separated
    layout.coefficientSignal (by simp)
  have branchNe : historyBranchWire layout ≠ layout.coefficientSignal := by
    have member := historyBranchWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
    exact member.symm ▸ separated.2.2 workspaceIndex
  have timeNe : historyLessThanTimeWire layout ≠ layout.coefficientSignal := by
    have member := historyLessThanTimeWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
    exact member.symm ▸ separated.2.2 workspaceIndex
  have idleNe : historyLessThanIdleEndWire layout ≠ layout.coefficientSignal := by
    have member := historyLessThanIdleEndWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
    exact member.symm ▸ separated.2.2 workspaceIndex
  unfold h2AfterIdleEnd119 h2AfterTime119 h2AfterSelector119
    historyTaylorSelectorEqualityBasisAction
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [littleEndianRegisterEqualsNat_replace_coefficient119]
  rw [← replaceQubitWire_xorWire_commute119
    (historyBranchWire layout) layout.coefficientSignal branchNe]
  unfold historyTaylorTimeComparisonBasisAction
  rw [historyTaylorClockLessThanTimeValue_replace_coefficient119]
  rw [← replaceQubitWire_xorWire_commute119
    (historyLessThanTimeWire layout) layout.coefficientSignal timeNe]
  unfold historyTaylorIdleEndComparisonBasisAction
  rw [historyTaylorClockLessThanIdleEndValue_replace_coefficient119]
  rw [← replaceQubitWire_xorWire_commute119
    (historyLessThanIdleEndWire layout) layout.coefficientSignal idleNe]

end
end ExecutableHistoryExecutableHistory
