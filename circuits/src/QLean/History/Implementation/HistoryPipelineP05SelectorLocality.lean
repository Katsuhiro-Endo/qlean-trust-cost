import QLean.History.Implementation.HistoryPipelineH3FullLogicalEquality
import QLean.History.Implementation.HistoryPipelineH2LogicalSupport

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components

noncomputable section

def historyNonselectorTail119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    List (Fin qubits) :=
  historyRegisterWires layout.data ++ historyRegisterWires layout.clock ++
    historyRegisterWires layout.order ++ historyRegisterWires layout.generatorSignal ++
    [layout.coefficientSignal, layout.orderBoundarySignal,
      layout.projectorSignal, layout.clockBoundarySignal] ++
    historyRegisterWires layout.workspace

theorem selector_wire_ne_historyNonselectorTail119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (selectorIndex : Fin 2) (wire : Fin qubits)
    (inTail : wire ∈ historyNonselectorTail119 layout) :
    layout.selector.wire selectorIndex ≠ wire := by
  have normalized :
      (historyRegisterWires layout.selector ++
        historyNonselectorTail119 layout).Nodup := by
    simpa [historyNonselectorTail119, List.append_assoc] using
      layout.allWiresNodup
  have split := List.nodup_append.mp normalized
  exact split.2.2 _ (List.mem_ofFn.mpr ⟨selectorIndex, rfl⟩) _ inTail

def OperatorPreservesWire119 {qubits : Nat}
    (wire : Fin qubits)
    (operator : VerifiedCircuitCore.Operator (QubitBasis qubits)) : Prop :=
  ∀ output input, operator output input ≠ 0 → output wire = input wire

theorem preservesWire119_of_preservesOutside
    {qubits : Nat} {support : Finset (Fin qubits)}
    {operator : VerifiedCircuitCore.Operator (QubitBasis qubits)}
    (localProof : OperatorPreservesOutside support operator)
    (wire : Fin qubits) (outside : wire ∉ support) :
    OperatorPreservesWire119 wire operator := by
  intro output input nonzero
  exact localProof output input nonzero wire outside

theorem OperatorPreservesWire119.one {qubits : Nat} (wire : Fin qubits) :
    OperatorPreservesWire119 wire
      (1 : VerifiedCircuitCore.Operator (QubitBasis qubits)) := by
  exact preservesWire119_of_preservesOutside
    (OperatorPreservesOutside.one (∅ : Finset (Fin qubits)))
    wire (by simp)

theorem OperatorPreservesWire119.mul
    {qubits : Nat} {wire : Fin qubits}
    {first second : VerifiedCircuitCore.Operator (QubitBasis qubits)}
    (firstLocal : OperatorPreservesWire119 wire first)
    (secondLocal : OperatorPreservesWire119 wire second) :
    OperatorPreservesWire119 wire (second * first) := by
  intro output input nonzero
  rw [Matrix.mul_apply] at nonzero
  by_contra changed
  apply nonzero
  apply Finset.sum_eq_zero
  intro middle _
  by_cases firstZero : first middle input = 0
  · simp [firstZero]
  by_cases secondZero : second output middle = 0
  · simp [secondZero]
  have middleInput := firstLocal middle input firstZero
  have outputMiddle := secondLocal output middle secondZero
  exact False.elim (changed (outputMiddle.trans middleInput))

theorem operatorSequence_preservesWire119
    {qubits : Nat} (wire : Fin qubits)
    (operators : List (VerifiedCircuitCore.Operator (QubitBasis qubits)))
    (localProof : ∀ operator, operator ∈ operators →
      OperatorPreservesWire119 wire operator) :
    OperatorPreservesWire119 wire (operatorSequence operators) := by
  induction operators with
  | nil => simpa [operatorSequence] using OperatorPreservesWire119.one wire
  | cons first rest ih =>
      have firstLocal := localProof first (by simp)
      have restLocal : OperatorPreservesWire119 wire (operatorSequence rest) := by
        apply ih
        intro operator member
        exact localProof operator (by simp [member])
      simpa [operatorSequence] using firstLocal.mul restLocal

theorem h2PostWriteSupport119_selector_outside
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (selectorIndex : Fin 2) :
    layout.selector.wire selectorIndex ∉ h2PostWriteSupport119 layout := by
  intro member
  simp only [h2PostWriteSupport119, Finset.mem_union, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with ⟨orderIndex, _, equal⟩ | equal | equal | equal | equal |
      equal | equal
  · exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
      (by simp [historyNonselectorTail119, historyRegisterWires]) equal.symm
  · exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
      (by simp [historyNonselectorTail119, historyRegisterWires]) equal
  · exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
      (by simp [historyNonselectorTail119, historyRegisterWires]) equal
  · exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
      (by
        apply List.mem_append_right
        exact historyActiveWire_mem_workspace layout) equal
  · exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
      (by
        apply List.mem_append_right
        exact historyLessThanIdleEndWire_mem_workspace layout) equal
  · exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
      (by
        apply List.mem_append_right
        exact historyLessThanTimeWire_mem_workspace layout) equal
  · exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
      (by
        apply List.mem_append_right
        exact historyBranchWire_mem_workspace layout) equal

theorem h2Q10Placement_selector_outside119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (selectorIndex : Fin 2) :
    (ExecutableLayout119 source domain).selector.wire selectorIndex ∉
      Finset.univ.image
        (ExecutableH2Q10Specification119 source domain).layout.placement := by
  intro member
  rcases Finset.mem_image.mp member with ⟨coreIndex, _, equal⟩
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  have placedMember :
      (ExecutableH2Q10Specification119 source domain).layout.placement coreIndex ∈
        historyRegisterWires layout.generatorSignal ++
          historyRegisterWires (historyGeneratorWorkRegister layout) ++
          historyRegisterWires layout.data := by
    rw [← historyP15Q10Placement_sourceOrder (layout := layout) widths]
    exact List.mem_ofFn.mpr ⟨coreIndex, rfl⟩
  have tailMember :
      (ExecutableH2Q10Specification119 source domain).layout.placement coreIndex ∈
        historyNonselectorTail119 layout := by
    rcases List.mem_append.mp placedMember with first | dataMember
    · rcases List.mem_append.mp first with signalMember | workMember
      · simp [historyNonselectorTail119, signalMember]
      · have workspaceMember :
            (ExecutableH2Q10Specification119 source domain).layout.placement
                coreIndex ∈ historyRegisterWires layout.workspace := by
          rcases List.mem_ofFn.mp workMember with ⟨workIndex, workEqual⟩
          rw [← workEqual]
          exact historyGeneratorWorkRegister_wire_mem_workspace layout workIndex
        simp [historyNonselectorTail119, workspaceMember]
    · simp [historyNonselectorTail119, dataMember]
  exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
    tailMember equal.symm

theorem executableH2Target_preserves_selector_wire119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (selectorIndex : Fin 2) :
    let layout := ExecutableLayout119 source domain
    OperatorPreservesWire119 (layout.selector.wire selectorIndex)
      (h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let clean := ScientificWidthGenericContract.correctedCleanEvidence259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let angles := fun coefficientIndex : Fin source.historyParameters.taylorOrder =>
    correctedTaylorCoefficientAngle119 source.toCommonSource119
      coefficientIndex.val
  let pre := operatorSequence
    [historyTaylorSelectorEqualityOperator layout,
     historyTaylorTimeComparisonOperator layout,
     historyTaylorIdleEndComparisonOperator layout,
     historyTaylorActiveConjunctionOperator layout]
  let q10 := h2ControlledQ10CleanOperator
    (ExecutableH2Q10Specification119 source domain)
  let post := h2PostOperator119 layout angles compiledIdleCoefficientAngle119
  have preLocal : OperatorPreservesWire119
      (layout.selector.wire selectorIndex) pre := by
    apply operatorSequence_preservesWire119
    intro operator member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact preservesWire119_of_preservesOutside
        (historyTaylorSelectorEqualityOperator_local119 layout)
        _ (by
          simp only [Finset.mem_singleton]
          exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
            (by
              apply List.mem_append_right
              exact historyBranchWire_mem_workspace layout))
    · exact preservesWire119_of_preservesOutside
        (historyTaylorTimeComparisonOperator_local119 layout)
        _ (by
          simp only [Finset.mem_singleton]
          exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
            (by
              apply List.mem_append_right
              exact historyLessThanTimeWire_mem_workspace layout))
    · exact preservesWire119_of_preservesOutside
        (historyTaylorIdleEndComparisonOperator_local119 layout)
        _ (by
          simp only [Finset.mem_singleton]
          exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
            (by
              apply List.mem_append_right
              exact historyLessThanIdleEndWire_mem_workspace layout))
    · exact preservesWire119_of_preservesOutside
        (historyTaylorActiveConjunctionOperator_local119 layout)
        _ (by
          simp only [Finset.mem_singleton]
          exact selector_wire_ne_historyNonselectorTail119 layout selectorIndex _
            (by
              apply List.mem_append_right
              exact historyActiveWire_mem_workspace layout))
  have q10Local : OperatorPreservesWire119
      (layout.selector.wire selectorIndex) q10 :=
    preservesWire119_of_preservesOutside
      (executableH2Q10_operator_local119 source domain) _
      (h2Q10Placement_selector_outside119 source domain selectorIndex)
  have postLocal : OperatorPreservesWire119
      (layout.selector.wire selectorIndex) post :=
    preservesWire119_of_preservesOutside
      (h2PostOperator_local119 layout angles compiledIdleCoefficientAngle119) _
        (h2PostWriteSupport119_selector_outside layout selectorIndex)
  have productLocal : OperatorPreservesWire119
      (layout.selector.wire selectorIndex) (post * (q10 * pre)) :=
    (preLocal.mul q10Local).mul postLocal
  change OperatorPreservesWire119 (layout.selector.wire selectorIndex)
    (h2TaylorCleanOperator
      (historyP15H2CleanUnderstandingSpecification layout clean widths angles
        compiledIdleCoefficientAngle119))
  rw [h2TaylorCleanOperator_historyP15_decompose119 layout clean widths
    angles compiledIdleCoefficientAngle119]
  exact productLocal

end

end ExecutableHistoryExecutableHistory
