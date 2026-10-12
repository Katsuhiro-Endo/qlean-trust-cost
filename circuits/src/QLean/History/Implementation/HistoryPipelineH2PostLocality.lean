import QLean.History.Implementation.HistoryPipelineControlledRotationAction
import QLean.Circuits.Foundation.OperatorLocalityAnalytic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components

noncomputable section

/-- Every wire which the mathematical post-Q10 H2 word may write.  In
particular, Q10's placed generator/data wires are deliberately absent. -/
def h2PostWriteSupport119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Finset (Fin qubits) :=
  Finset.univ.image layout.order.wire ∪
    {layout.coefficientSignal, layout.orderBoundarySignal,
      historyActiveWire layout, historyLessThanIdleEndWire layout,
      historyLessThanTimeWire layout, historyBranchWire layout}

private theorem historyP15PostSignal_ne_placement119
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

private theorem historyP15OrderWire_ne_placement119
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

theorem h2PostWriteSupport119_ne_placement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (wire : Fin qubits)
    (member : wire ∈ h2PostWriteSupport119 layout)
    (source : Fin (p.ancillaWidth + p.systemWidth)) :
    wire ≠ (historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths).placement.embedding.placement source := by
  simp only [h2PostWriteSupport119, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with ⟨index, _, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl
  · exact historyP15OrderWire_ne_placement119 widths index source
  · exact historyP15PostSignal_ne_placement119 widths _ (by simp) source
  · exact historyP15PostSignal_ne_placement119 widths _ (by simp) source
  · exact historyP15Q10LiveWire_ne_placement widths _ (by
      simp [historyTaylorBeforeGeneratorLiveWires]) source
  · exact historyP15Q10LiveWire_ne_placement widths _ (by
      simp [historyTaylorBeforeGeneratorLiveWires]) source
  · exact historyP15Q10LiveWire_ne_placement widths _ (by
      simp [historyTaylorBeforeGeneratorLiveWires]) source
  · exact historyP15Q10LiveWire_ne_placement widths _ (by
      simp [historyTaylorBeforeGeneratorLiveWires]) source

theorem historyTaylorActiveConjunctionOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    OperatorPreservesOutside {historyActiveWire layout}
      (historyTaylorActiveConjunctionOperator layout) := by
  unfold historyTaylorActiveConjunctionOperator
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  unfold historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
  apply xorWire_apply_other
  simpa using outside

theorem historyTaylorInvalidClockOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    OperatorPreservesOutside {layout.coefficientSignal}
      (historyTaylorInvalidClockOperator layout) := by
  unfold historyTaylorInvalidClockOperator
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  unfold historyTaylorInvalidClockBasisAction
  apply xorWire_apply_other
  simpa using outside

theorem historyTaylorOrderBoundaryOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    OperatorPreservesOutside {layout.orderBoundarySignal}
      (historyTaylorOrderBoundaryOperator layout) := by
  unfold historyTaylorOrderBoundaryOperator
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  unfold historyTaylorOrderBoundaryBasisAction
  apply xorWire_apply_other
  simpa using outside

theorem historyTaylorIdleBoundaryOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    OperatorPreservesOutside {layout.orderBoundarySignal}
      (historyTaylorIdleBoundaryOperator layout) := by
  unfold historyTaylorIdleBoundaryOperator
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  unfold historyTaylorIdleBoundaryBasisAction
  apply xorWire_apply_other
  simpa using outside

theorem historyTaylorDegreeIncrementOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    OperatorPreservesOutside (Finset.univ.image layout.order.wire)
      (historyTaylorDegreeIncrementOperator layout) := by
  unfold historyTaylorDegreeIncrementOperator
    predicateControlledAddMod2PowOperator
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  apply predicateControlledAddMod2PowBasisAction_apply_outside
  intro index equal
  apply outside
  exact Finset.mem_image.mpr ⟨index, Finset.mem_univ _, equal.symm⟩

theorem historyTaylorCoefficientIterationOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : VerifiedCircuitCore.AngleExpr)
    (index : Fin parameters.taylorOrder) :
    OperatorPreservesOutside {layout.coefficientSignal}
      (historyTaylorCoefficientIterationOperator layout angle index) := by
  unfold historyTaylorCoefficientIterationOperator
  exact OperatorPreservesOutside.predicateControlledSingleQubitOperator
    _ _ _

theorem historyTaylorCoefficientLoopOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr) :
    OperatorPreservesOutside {layout.coefficientSignal}
      (historyTaylorCoefficientLoopOperator layout angles) := by
  unfold historyTaylorCoefficientLoopOperator
  apply OperatorPreservesOutside.operatorSequence_of_forall
  intro operator member
  simp only [List.mem_map] at member
  rcases member with ⟨index, _, rfl⟩
  exact historyTaylorCoefficientIterationOperator_local119 layout _ index

theorem historyTaylorIdleCoefficientOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : VerifiedCircuitCore.AngleExpr) :
    OperatorPreservesOutside {layout.coefficientSignal}
      (historyTaylorIdleCoefficientOperator layout angle) := by
  unfold historyTaylorIdleCoefficientOperator
  exact OperatorPreservesOutside.predicateControlledSingleQubitOperator
    _ _ _

theorem historyTaylorSelectorEqualityOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    OperatorPreservesOutside {historyBranchWire layout}
      (historyTaylorSelectorEqualityOperator layout) := by
  unfold historyTaylorSelectorEqualityOperator
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  unfold historyTaylorSelectorEqualityBasisAction
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  apply xorWire_apply_other
  simpa using outside

theorem historyTaylorTimeComparisonOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    OperatorPreservesOutside {historyLessThanTimeWire layout}
      (historyTaylorTimeComparisonOperator layout) := by
  unfold historyTaylorTimeComparisonOperator
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  unfold historyTaylorTimeComparisonBasisAction
  apply xorWire_apply_other
  simpa using outside

theorem historyTaylorIdleEndComparisonOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    OperatorPreservesOutside {historyLessThanIdleEndWire layout}
      (historyTaylorIdleEndComparisonOperator layout) := by
  unfold historyTaylorIdleEndComparisonOperator
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  unfold historyTaylorIdleEndComparisonBasisAction
  apply xorWire_apply_other
  simpa using outside

def h2PostOperator119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr) :
    VerifiedCircuitCore.Operator (QubitBasis qubits) :=
  operatorSequence
    [historyTaylorActiveConjunctionOperator layout,
     historyTaylorInvalidClockOperator layout,
     historyTaylorOrderBoundaryOperator layout,
     historyTaylorIdleBoundaryOperator layout,
     historyTaylorDegreeIncrementOperator layout,
     historyTaylorCoefficientLoopOperator layout angles,
     historyTaylorIdleCoefficientOperator layout idleAngle,
     operatorSequence
       [historyTaylorIdleEndComparisonOperator layout,
        historyTaylorTimeComparisonOperator layout,
        historyTaylorSelectorEqualityOperator layout]]

theorem h2PostOperator_local119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr) :
    OperatorPreservesOutside (h2PostWriteSupport119 layout)
      (h2PostOperator119 layout angles idleAngle) := by
  unfold h2PostOperator119
  apply OperatorPreservesOutside.operatorSequence_of_forall
  intro operator member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (historyTaylorActiveConjunctionOperator_local119 layout).mono (by
      intro wire member
      simp only [Finset.mem_singleton] at member
      subst wire
      simp [h2PostWriteSupport119])
  · exact (historyTaylorInvalidClockOperator_local119 layout).mono (by
      intro wire member
      simp only [Finset.mem_singleton] at member
      subst wire
      simp [h2PostWriteSupport119])
  · exact (historyTaylorOrderBoundaryOperator_local119 layout).mono (by
      intro wire member
      simp only [Finset.mem_singleton] at member
      subst wire
      simp [h2PostWriteSupport119])
  · exact (historyTaylorIdleBoundaryOperator_local119 layout).mono (by
      intro wire member
      simp only [Finset.mem_singleton] at member
      subst wire
      simp [h2PostWriteSupport119])
  · exact (historyTaylorDegreeIncrementOperator_local119 layout).mono (by
      intro wire member
      exact Finset.mem_union_left _ member)
  · exact (historyTaylorCoefficientLoopOperator_local119 layout angles).mono (by
      intro wire member
      simp only [Finset.mem_singleton] at member
      subst wire
      simp [h2PostWriteSupport119])
  · exact (historyTaylorIdleCoefficientOperator_local119 layout idleAngle).mono (by
      intro wire member
      simp only [Finset.mem_singleton] at member
      subst wire
      simp [h2PostWriteSupport119])
  · apply OperatorPreservesOutside.operatorSequence_of_forall
    intro restore member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact (historyTaylorIdleEndComparisonOperator_local119 layout).mono (by
        intro wire member
        simp only [Finset.mem_singleton] at member
        subst wire
        simp [h2PostWriteSupport119])
    · exact (historyTaylorTimeComparisonOperator_local119 layout).mono (by
        intro wire member
        simp only [Finset.mem_singleton] at member
        subst wire
        simp [h2PostWriteSupport119])
    · exact (historyTaylorSelectorEqualityOperator_local119 layout).mono (by
        intro wire member
        simp only [Finset.mem_singleton] at member
        subst wire
        simp [h2PostWriteSupport119])

end
end ExecutableHistoryExecutableHistory
