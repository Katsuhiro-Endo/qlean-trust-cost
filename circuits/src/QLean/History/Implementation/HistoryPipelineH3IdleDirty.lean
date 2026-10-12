import QLean.History.Implementation.HistoryPipelineH3IdleInvocation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

theorem h3ActiveTailBasisAction119_coefficientSignal
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits) :
    h3ActiveTailBasisAction119 source domain input
        (ExecutableLayout119 source domain).coefficientSignal =
      input (ExecutableLayout119 source domain).coefficientSignal := by
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  let afterActive := historyTaylorActiveConjunctionBasisAction layout input
  let afterIdle := historyTaylorIdleEndComparisonBasisAction layout afterActive
  let afterTime := historyTaylorTimeComparisonBasisAction layout afterIdle
  let afterProjector := h3I06BasisAction layout afterTime
  have separated := layout.postGeneratorSignal_separated
    layout.coefficientSignal (by simp)
  have coefficientNeWorkspace (index : Fin
      (historyClockWorkspaceWidth
        (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
          (ExecutableAdmissible119 source domain).analytic)
        (ExecutableRaw119 source).history.generatorWorkWidth)) :
      layout.coefficientSignal ≠ layout.workspace.wire index :=
    (separated.2.2 index).symm
  have coefficientNeActive : layout.coefficientSignal ≠
      historyActiveWire layout := by
    unfold historyActiveWire
    exact coefficientNeWorkspace _
  have coefficientNeIdleEnd : layout.coefficientSignal ≠
      historyLessThanIdleEndWire layout := by
    unfold historyLessThanIdleEndWire
    exact coefficientNeWorkspace _
  have coefficientNeTime : layout.coefficientSignal ≠
      historyLessThanTimeWire layout := by
    unfold historyLessThanTimeWire
    exact coefficientNeWorkspace _
  have coefficientNeBranch : layout.coefficientSignal ≠
      historyBranchWire layout := by
    unfold historyBranchWire
    exact coefficientNeWorkspace _
  have coefficientNeProjector : layout.coefficientSignal ≠
      layout.projectorSignal := by
    let leadingWires := historyRegisterWires layout.selector ++
      historyRegisterWires layout.data ++ historyRegisterWires layout.clock ++
      historyRegisterWires layout.order ++
      historyRegisterWires layout.generatorSignal
    let reserved := [layout.coefficientSignal, layout.orderBoundarySignal,
      layout.projectorSignal, layout.clockBoundarySignal]
    let workspace := historyRegisterWires layout.workspace
    have normalized : (leadingWires ++ reserved ++ workspace).Nodup := by
      simpa [leadingWires, reserved, workspace, List.append_assoc] using
        layout.allWiresNodup
    have leadingReservedNodup := (List.nodup_append.mp normalized).1
    have reservedNodup := (List.nodup_append.mp leadingReservedNodup).2.1
    have explicitReserved : [layout.coefficientSignal,
        layout.orderBoundarySignal, layout.projectorSignal,
        layout.clockBoundarySignal].Nodup := by
      simpa [reserved] using reservedNodup
    have coefficientNotTail := (List.nodup_cons.mp explicitReserved).1
    simp only [List.mem_cons, not_or] at coefficientNotTail
    exact coefficientNotTail.2.1
  have afterClockCoefficient :
      controlledAddConstantMod2PowBasisAction
          (historyControlledClockIncrementSpec layout clock.controlledIncrement)
          afterProjector layout.coefficientSignal =
        afterProjector layout.coefficientSignal := by
    apply controlledAddConstantMod2PowBasisAction_apply_outside
    intro clockIndex equal
    exact separated.2.1 clockIndex equal.symm
  unfold h3ActiveTailBasisAction119
  unfold h3AfterSelector119
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [xorWire_apply_other _ _ coefficientNeBranch]
  rw [afterClockCoefficient]
  unfold afterProjector h3I06BasisAction
  rw [xorWire_apply_other _ _ coefficientNeProjector]
  unfold afterTime historyTaylorTimeComparisonBasisAction
  rw [xorWire_apply_other _ _ coefficientNeTime]
  unfold afterIdle historyTaylorIdleEndComparisonBasisAction
  rw [xorWire_apply_other _ _ coefficientNeIdleEnd]
  unfold afterActive historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
  rw [xorWire_apply_other _ _ coefficientNeActive]

/-- The inactive suffix remains a deterministic basis permutation even when
the coefficient signal contains the dirty sine branch. -/
theorem h3IdlePostTransformOperator119_apply_basisKet_logical_coefficient
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (value : Bool) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let expected := h3ZeroOrder119 layout (h3BeforeUniform119 layout logical)
    let input := replaceQubitWire expected layout.coefficientSignal value
    VerifiedCircuitCore.applyOperator
        (h3IdlePostTransformOperator119 source domain)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet
        (h3ActiveTailBasisAction119 source domain input) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  let zeroIndex := h3OrderZeroIndex119 source index
  let zeroLogical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 zeroIndex
  let expected := h3ZeroOrder119 layout
    (h3BeforeUniform119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h3SelectedBranch119 index))
  let input := replaceQubitWire expected layout.coefficientSignal value
  let afterActive := historyTaylorActiveConjunctionBasisAction layout input
  let afterIdle := historyTaylorIdleEndComparisonBasisAction layout afterActive
  let afterTime := historyTaylorTimeComparisonBasisAction layout afterIdle
  let afterProjector := h3I06BasisAction layout afterTime
  have expectedEq : expected = h3BeforeUniform119 layout zeroLogical :=
    h3ZeroOrder119_before_eq_orderZeroIndex source domain fits index
  have clockIdleZero : ¬ zeroIndex.clock.val <
      source.historyParameters.physicalClocks := by
    simpa [zeroIndex] using clockIdle
  have values := h3BeforeUniform119_idle_clean_values
    source domain fits zeroIndex clockIdleZero
  have separated := layout.postGeneratorSignal_separated
    layout.coefficientSignal (by simp)
  have workspaceOutside
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace) :
      wire ≠ layout.coefficientSignal := by
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨workspaceIndex, rfl⟩
    exact separated.2.2 workspaceIndex
  have inputWorkspace
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace) :
      input wire = expected wire := by
    unfold input
    exact replaceQubitWire_outside expected layout.coefficientSignal wire value
      (workspaceOutside wire member)
  have branchTrue : input (historyBranchWire layout) = true := by
    rw [inputWorkspace _ (historyBranchWire_mem_workspace layout)]
    rw [expectedEq]
    exact values.1
  have timeFalse : input (historyLessThanTimeWire layout) = false := by
    rw [inputWorkspace _ (historyLessThanTimeWire_mem_workspace layout)]
    rw [expectedEq]
    exact values.2.1
  have activeFalse : input (historyActiveWire layout) = false := by
    rw [inputWorkspace _ (historyActiveWire_mem_workspace layout)]
    rw [expectedEq]
    exact values.2.2.2.2.1
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout zeroLogical :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 zeroIndex
  have zeroOfNotLive
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace)
      (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
      input wire = false := by
    rw [inputWorkspace wire member]
    calc
      expected wire = h3BeforeUniform119 layout zeroLogical wire :=
        congrFun expectedEq wire
      _ = zeroLogical wire :=
        h3BeforeUniform119_workspace_of_not_live layout zeroLogical wire notLive
      _ = false := historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
        layout zeroLogical auxiliary wire member
  have afterActiveZero
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
      afterActive wire = input wire := by
    unfold afterActive historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other]
    intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  have restoredZero
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace)
      (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
      afterTime wire = false := by
    calc
      afterTime wire = input wire :=
        h3ActiveRestoredComparisons119_apply_other layout input wire notLive
      _ = false := zeroOfNotLive wire member notLive
  have idleComparisonClean :
      (forall i, afterActive ((historyBorrowRegister layout).wire i) = false) ∧
        forall i, afterActive ((historyBoundRegister layout).wire i) = false := by
    constructor
    · intro i
      rw [afterActiveZero _
        (historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires layout i)]
      exact zeroOfNotLive _ (historyBorrowRegister_wire_mem_workspace layout i)
        (historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires layout i)
    · intro i
      rw [afterActiveZero _
        (historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires layout i)]
      exact zeroOfNotLive _ (historyBoundRegister_wire_mem_workspace layout i)
        (historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires layout i)
  have timeComparisonClean :
      (forall i, afterIdle ((historyBorrowRegister layout).wire i) = false) ∧
        forall i, afterIdle ((historyBoundRegister layout).wire i) = false := by
    constructor
    · intro i
      unfold afterIdle historyTaylorIdleEndComparisonBasisAction
      rw [xorWire_apply_other]
      · exact idleComparisonClean.1 i
      · intro equal
        apply historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires layout i
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
    · intro i
      unfold afterIdle historyTaylorIdleEndComparisonBasisAction
      rw [xorWire_apply_other]
      · exact idleComparisonClean.2 i
      · intro equal
        apply historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires layout i
        simp [historyTaylorBeforeGeneratorLiveWires, equal]
  have projectorWorkClean :
      ClassicalReversibleStage.minimumWorkCleanPredicate
          (historyRegisterWires (historyEqualityWork layout)) afterTime ∧
        h3I06CleanInputPredicate layout afterTime := by
    constructor
    · intro wire member
      simp only [historyRegisterWires, List.mem_ofFn] at member
      rcases member with ⟨i, rfl⟩
      exact restoredZero _ (by
          unfold historyEqualityWork
          apply historyWorkspaceSlice_wire_mem)
        (h3EqualityWork_not_live119 layout i)
    · change afterTime (historyEqualityFlag layout) = false ∧
        afterTime (historyCoefficientControl layout) = false
      constructor
      · exact restoredZero _ (by
          unfold historyEqualityFlag
          apply historyWorkspaceSlice_wire_mem)
          (h3EqualityFlag_not_live119 layout)
      · exact restoredZero _ (by
          unfold historyCoefficientControl
          apply historyWorkspaceSlice_wire_mem)
          (h3CoefficientControl_not_live119 layout)
  have clockWorkClean : controlledAddConstantMod2PowCleanPredicate
      (historyControlledClockIncrementSpec layout clock.controlledIncrement)
      afterProjector := by
    change (forall i, afterProjector
        ((historyClockMaskedConstantRegister layout).wire i) = false) ∧
      afterProjector (historyClockIncrementCarry layout) = false
    constructor
    · intro i
      unfold afterProjector h3I06BasisAction
      rw [xorWire_apply_other]
      · exact restoredZero _
          (historyClockMaskedConstantRegister_wire_mem_workspace layout i)
          (h3ClockMasked_not_live119 layout i)
      · unfold historyClockMaskedConstantRegister
        exact h3WorkspaceWire_ne_projector119 layout _
    · unfold afterProjector h3I06BasisAction
      rw [xorWire_apply_other]
      · exact restoredZero _ (historyClockIncrementCarry_mem_workspace layout)
          (h3ClockCarry_not_live119 layout)
      · unfold historyClockIncrementCarry
        exact h3WorkspaceWire_ne_projector119 layout _
  exact h3IdlePostTransformOperator119_apply_basisKet source domain input
    branchTrue timeFalse activeFalse idleComparisonClean timeComparisonClean
    projectorWorkClean clockWorkClean

end
end ExecutableHistoryExecutableHistory
