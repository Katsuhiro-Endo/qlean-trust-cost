import QLean.History.Implementation.HistoryPipelineH3IdleTail

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
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

/-- All clean-work obligations of the inactive post-transform suffix follow
from the logical zero-order history basis. -/
theorem h3IdlePostTransformOperator119_apply_basisKet_logical
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let expected := h3ZeroOrder119 layout (h3BeforeUniform119 layout logical)
    VerifiedCircuitCore.applyOperator
        (h3IdlePostTransformOperator119 source domain)
        (VerifiedCircuitCore.basisKet expected) =
      VerifiedCircuitCore.basisKet
        (h3ActiveTailBasisAction119 source domain expected) := by
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
  let afterActive := historyTaylorActiveConjunctionBasisAction layout expected
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
  have branchTrue : expected (historyBranchWire layout) = true := by
    rw [expectedEq]
    exact values.1
  have timeFalse : expected (historyLessThanTimeWire layout) = false := by
    rw [expectedEq]
    exact values.2.1
  have activeFalse : expected (historyActiveWire layout) = false := by
    rw [expectedEq]
    exact values.2.2.2.2.1
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout zeroLogical :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 zeroIndex
  have zeroOfNotLive
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace)
      (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
      expected wire = false := by
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
      afterActive wire = expected wire := by
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
      afterTime wire = expected wire :=
        h3ActiveRestoredComparisons119_apply_other layout expected wire notLive
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
  exact h3IdlePostTransformOperator119_apply_basisKet source domain expected
    branchTrue timeFalse activeFalse idleComparisonClean timeComparisonClean
    projectorWorkClean clockWorkClean

end
end ExecutableHistoryExecutableHistory
