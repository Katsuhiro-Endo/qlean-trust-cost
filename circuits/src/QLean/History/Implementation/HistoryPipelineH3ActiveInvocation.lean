import QLean.History.Implementation.HistoryPipelineH3ActiveSupport

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
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

theorem h3UniformMiddle119_workspace_zero_of_not_live
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (middle : QubitBasis (ExecutableRaw119 source).history.qubits)
    (outsideEqual :
      let layout := ExecutableLayout119 source domain
      let before := h3BeforeUniform119 layout
        (correctedBranchHistoryBasis119 source domain fits
          h3SelectedBranch119 index)
      restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout
            (ExecutableClockEvidence119 source domain).uniformExternalControl
          ).placement middle =
        restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout
            (ExecutableClockEvidence119 source domain).uniformExternalControl
          ).placement before)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (member : wire ∈ historyRegisterWires
      (ExecutableLayout119 source domain).workspace)
    (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires
      (ExecutableLayout119 source domain)) :
    middle wire = false := by
  dsimp only at outsideEqual
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).uniformExternalControl
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout logical :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 index
  calc
    middle wire = before wire :=
      h3OutsideEqual_workspace_member119 layout evidence middle before
        outsideEqual wire member
    _ = logical wire :=
      h3BeforeUniform119_workspace_of_not_live layout logical wire notLive
    _ = false := historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
      layout logical auxiliary wire member

theorem h3ActiveRestoredComparisons119_apply_other
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
    let afterActive := historyTaylorActiveConjunctionBasisAction layout input
    let afterIdle := historyTaylorIdleEndComparisonBasisAction layout afterActive
    let afterTime := historyTaylorTimeComparisonBasisAction layout afterIdle
    afterTime wire = input wire := by
  dsimp only
  unfold historyTaylorTimeComparisonBasisAction
    historyTaylorIdleEndComparisonBasisAction
    historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
  rw [xorWire_apply_other, xorWire_apply_other, xorWire_apply_other]
  · intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  · intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]
  · intro equal
    apply notLive
    simp [historyTaylorBeforeGeneratorLiveWires, equal]

/-- The active tail no longer needs caller-supplied clean facts.  They follow
from the logical clean input and the outside-wire equality forced by the
uniform inverse. -/
theorem h3ActiveTailOperator119_apply_basisKet_of_uniform_outside
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (middle : QubitBasis (ExecutableRaw119 source).history.qubits)
    (outsideEqual :
      let layout := ExecutableLayout119 source domain
      let before := h3BeforeUniform119 layout
        (correctedBranchHistoryBasis119 source domain fits
          h3SelectedBranch119 index)
      restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout
            (ExecutableClockEvidence119 source domain).uniformExternalControl
          ).placement middle =
        restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout
            (ExecutableClockEvidence119 source domain).uniformExternalControl
          ).placement before) :
    VerifiedCircuitCore.applyOperator (h3ActiveTailOperator119 source domain)
        (VerifiedCircuitCore.basisKet middle) =
      (-1 : Complex) • VerifiedCircuitCore.basisKet
        (h3ActiveTailBasisAction119 source domain middle) := by
  dsimp only at outsideEqual
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  let afterActive := historyTaylorActiveConjunctionBasisAction layout middle
  let afterIdle := historyTaylorIdleEndComparisonBasisAction layout afterActive
  let afterTime := historyTaylorTimeComparisonBasisAction layout afterIdle
  let afterProjector := h3I06BasisAction layout afterTime
  have values := h3UniformMiddle119_active_clean_values
    source domain fits index clockActive middle outsideEqual
  have zeroOfNotLive
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace)
      (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
      middle wire = false :=
    h3UniformMiddle119_workspace_zero_of_not_live
      source domain fits index middle outsideEqual wire member notLive
  have afterActiveZero
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (notLive : wire ∉ historyTaylorBeforeGeneratorLiveWires layout) :
      afterActive wire = middle wire := by
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
      afterTime wire = middle wire :=
        h3ActiveRestoredComparisons119_apply_other layout middle wire notLive
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
  exact h3ActiveTailOperator119_apply_basisKet source domain middle
    values.1 values.2.1 values.2.2.1 values.2.2.2.1
    values.2.2.2.2.1 values.2.2.2.2.2 idleComparisonClean
    timeComparisonClean projectorWorkClean clockWorkClean

end
end ExecutableHistoryExecutableHistory
