import QLean.History.Implementation.HistoryPipelineSelectedBasisFacts
import QLean.History.Implementation.HistoryPipelineH2QEntry

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

theorem h2BeforeQ119_apply_of_not_mem_live
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
    h2BeforeQ119 layout input wire = input wire := by
  have branchNe : wire ≠ historyBranchWire layout := by
    intro equal
    apply outside
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  have timeNe : wire ≠ historyLessThanTimeWire layout := by
    intro equal
    apply outside
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  have idleNe : wire ≠ historyLessThanIdleEndWire layout := by
    intro equal
    apply outside
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  have activeNe : wire ≠ historyActiveWire layout := by
    intro equal
    apply outside
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  unfold h2BeforeQ119 historyTaylorActiveConjunctionBasisAction
    h2AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
    h2AfterTime119 historyTaylorTimeComparisonBasisAction
    h2AfterSelector119 historyTaylorSelectorEqualityBasisAction
  rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other
    _ _ wire activeNe]
  rw [xorWire_apply_other _ wire idleNe]
  rw [xorWire_apply_other _ wire timeNe]
  exact ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_other
    (historyRegisterWires layout.selector) 1 (historyBranchWire layout) wire
    branchNe input

theorem historyPrefix_wire_not_mem_beforeGeneratorLiveWires119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (wire : Fin qubits)
    (member : wire ∈
      historyRegisterWires layout.selector ++
      historyRegisterWires layout.data ++
      historyRegisterWires layout.clock ++
      historyRegisterWires layout.order ++
      historyRegisterWires layout.generatorSignal ++
      [layout.coefficientSignal, layout.orderBoundarySignal,
        layout.projectorSignal, layout.clockBoundarySignal]) :
    wire ∉ historyTaylorBeforeGeneratorLiveWires layout := by
  intro live
  have workspaceMember : wire ∈ historyRegisterWires layout.workspace := by
    simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
      List.not_mem_nil, or_false] at live
    rcases live with equal | equal | equal | equal
    · rw [equal]
      exact historyBranchWire_mem_workspace layout
    · rw [equal]
      exact historyLessThanTimeWire_mem_workspace layout
    · rw [equal]
      exact historyLessThanIdleEndWire_mem_workspace layout
    · rw [equal]
      exact historyActiveWire_mem_workspace layout
  have split := List.nodup_append.mp layout.allWiresNodup
  exact split.2.2 wire member wire workspaceMember rfl

theorem historyGeneratorWorkRegister_wire_not_mem_live119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin generatorWorkWidth) :
    (historyGeneratorWorkRegister layout).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyGeneratorWorkRegister
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  have workFits := Nat.le_max_left generatorWorkWidth
    (historyStructuralPoolWidth parameters)
  unfold historySharedPoolWidth
  omega

theorem historyAfterSelector_wire_not_mem_selector119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (wire : Fin qubits)
    (member : wire ∈
      historyRegisterWires layout.data ++
      historyRegisterWires layout.clock ++
      historyRegisterWires layout.order ++
      historyRegisterWires layout.generatorSignal ++
      [layout.coefficientSignal, layout.orderBoundarySignal,
        layout.projectorSignal, layout.clockBoundarySignal] ++
      historyRegisterWires layout.workspace) :
    wire ∉ historyRegisterWires layout.selector := by
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
  have split := List.nodup_append.mp normalized
  intro selectorMember
  apply split.2.2 wire selectorMember wire
  · simpa [dataWires, clockWires, orderWires, generatorWires,
      reservedWires, workspaceWires, List.append_assoc] using member
  · rfl

theorem h2BeforeQ119_q10RestrictedBasis_eq_success119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    restrictToPlacedWires evidence.placement.embedding.placement
        (h2BeforeQ119 layout
          (correctedBranchHistoryBasis119 source domain fits branch index)) =
      canonicalCoreSuccessBasis119 (ExecutableQParameters119 source domain)
        (executableQConfiguration119 source domain
          index.state.configuration) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  rw [← executableQ10RestrictedBasis_eq_success119 source domain fits index]
  funext coreIndex
  change h2BeforeQ119 layout
      (correctedBranchHistoryBasis119 source domain fits branch index)
      (evidence.placement.embedding.placement coreIndex) =
    executableHistoryBasis119 source domain fits index
      (evidence.placement.embedding.placement coreIndex)
  have sourceOrder := historyP15Q10Placement_sourceOrder
    (layout := layout) widths
  have placedMember : evidence.placement.embedding.placement coreIndex ∈
      historyRegisterWires layout.generatorSignal ++
        historyRegisterWires (historyGeneratorWorkRegister layout) ++
        historyRegisterWires layout.data := by
    rw [← sourceOrder]
    exact List.mem_ofFn.mpr ⟨coreIndex, rfl⟩
  have notLive : evidence.placement.embedding.placement coreIndex ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
    rcases List.mem_append.mp placedMember with ancillaMember | dataMember
    · rcases List.mem_append.mp ancillaMember with signalMember | workMember
      · apply historyPrefix_wire_not_mem_beforeGeneratorLiveWires119 layout
        simp [List.mem_append, signalMember]
      · simp only [historyRegisterWires, List.mem_ofFn] at workMember
        rcases workMember with ⟨workIndex, workEqual⟩
        rw [← workEqual]
        exact historyGeneratorWorkRegister_wire_not_mem_live119 layout workIndex
    · apply historyPrefix_wire_not_mem_beforeGeneratorLiveWires119 layout
      simp [List.mem_append, dataMember]
  rw [h2BeforeQ119_apply_of_not_mem_live _ _ _ notLive]
  apply correctedBranchHistoryBasis119_apply_of_not_selector
  apply historyAfterSelector_wire_not_mem_selector119 layout
  rcases List.mem_append.mp placedMember with ancillaMember | dataMember
  · rcases List.mem_append.mp ancillaMember with signalMember | workMember
    · simp [List.mem_append, signalMember]
    · simp only [historyRegisterWires, List.mem_ofFn] at workMember
      rcases workMember with ⟨workIndex, workEqual⟩
      have workspaceMember :=
        historyGeneratorWorkRegister_wire_mem_workspace layout workIndex
      rw [workEqual] at workspaceMember
      simp [List.mem_append, workspaceMember]
  · simp [List.mem_append, dataMember]

end
end ExecutableHistoryExecutableHistory
