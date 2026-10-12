import QLean.History.Implementation.HistoryPipelineCorrectedSelectorPhysical
import QLean.History.Implementation.HistoryPipelineHistoryCleanInput

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

/-- A logical history basis state with the two physical selector wires fixed
to a chosen LCU branch.  All non-selector wires are taken literally from the
clean logical history embedding. -/
def correctedBranchHistoryBasis119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    QubitBasis (ExecutableRaw119 source).history.qubits :=
  fixedOutsideBasisEmbedding
    (correctedSelectorPlacement119 source domain)
    (correctedSelectorOutside119 source domain
      (executableHistoryBasis119 source domain fits index))
    (correctedSelectorBranchBasis119 branch)

@[simp] theorem correctedBranchHistoryBasis119_restrict_selector
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    restrictToPlacedWires (correctedSelectorPlacement119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      correctedSelectorBranchBasis119 branch := by
  exact restrictToPlacedWires_mergePlacedAndOutsideBasis _ _ _

@[simp] theorem correctedBranchHistoryBasis119_restrict_outside
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    restrictToOutsideWires (correctedSelectorPlacement119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      restrictToOutsideWires (correctedSelectorPlacement119 source domain)
        (executableHistoryBasis119 source domain fits index) := by
  exact restrictToOutsideWires_mergePlacedAndOutsideBasis _ _ _

theorem correctedBranchHistoryBasis119_apply_outside
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (outside : ∀ selectorIndex,
      correctedSelectorPlacement119 source domain selectorIndex ≠ wire) :
    correctedBranchHistoryBasis119 source domain fits branch index wire =
      executableHistoryBasis119 source domain fits index wire := by
  let external : OutsideWire (correctedSelectorPlacement119 source domain) :=
    ⟨wire, outside⟩
  have atOutside := congrFun
    (correctedBranchHistoryBasis119_restrict_outside
      source domain fits branch index) external
  exact atOutside

theorem correctedBranchHistoryBasis119_apply_of_not_selector
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (outside : wire ∉
      historyRegisterWires (ExecutableLayout119 source domain).selector) :
    correctedBranchHistoryBasis119 source domain fits branch index wire =
      executableHistoryBasis119 source domain fits index wire := by
  apply correctedBranchHistoryBasis119_apply_outside
  intro selectorIndex equal
  apply outside
  rw [← equal]
  exact List.mem_ofFn.mpr ⟨selectorIndex, rfl⟩

theorem correctedBranchHistoryBasis119_workspace_zero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    ∀ workspaceIndex,
      correctedBranchHistoryBasis119 source domain fits branch index
          ((ExecutableLayout119 source domain).workspace.wire workspaceIndex) =
        false := by
  intro workspaceIndex
  rw [correctedBranchHistoryBasis119_apply_of_not_selector]
  · exact executableHistoryBasis119_workspace_zero
      source domain fits index workspaceIndex
  · intro selectorMember
    simp only [historyRegisterWires, List.mem_ofFn] at selectorMember
    rcases selectorMember with ⟨selectorIndex, equal⟩
    exact (ExecutableLayout119 source domain).selector_wire_ne_workspace_wire
      selectorIndex workspaceIndex equal

theorem correctedBranchHistoryBasis119_p15_auxiliary
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    historyTaylorAuxiliaryBoundaryPredicate
        (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index) := by
  intro workspaceIndex
  exact correctedBranchHistoryBasis119_workspace_zero
    source domain fits branch index workspaceIndex

theorem correctedBranchHistoryBasis119_selector_value
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    ClassicalReversibleStage.littleEndianListNat
        (ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).selector)
          (correctedBranchHistoryBasis119 source domain fits branch index)) =
      branch.val := by
  have restricted := correctedBranchHistoryBasis119_restrict_selector
    source domain fits branch index
  have bit0 := congrFun restricted (0 : Fin 2)
  have bit1 := congrFun restricted (Fin.succ (0 : Fin 1))
  simp only [ClassicalReversibleStage.readWires, historyRegisterWires]
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [List.map_cons, List.map_nil]
  rw [show correctedBranchHistoryBasis119 source domain fits branch index
      ((ExecutableLayout119 source domain).selector.wire (0 : Fin 2)) =
        correctedSelectorBranchBasis119 branch 0 by exact bit0]
  rw [show correctedBranchHistoryBasis119 source domain fits branch index
      ((ExecutableLayout119 source domain).selector.wire (Fin.succ (0 : Fin 1))) =
        correctedSelectorBranchBasis119 branch (Fin.succ (0 : Fin 1)) by exact bit1]
  fin_cases branch <;> decide

@[simp] theorem correctedBranchHistoryBasis119_selector_one
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires (ExecutableLayout119 source domain).selector) 1
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      decide (branch.val = 1) := by
  rw [ClassicalReversibleStage.littleEndianRegisterEqualsNat_eq_decide]
  · rw [correctedBranchHistoryBasis119_selector_value]
  · norm_num [historyRegisterWires]

@[simp] theorem correctedBranchHistoryBasis119_selector_two
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires (ExecutableLayout119 source domain).selector) 2
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      decide (branch.val = 2) := by
  rw [ClassicalReversibleStage.littleEndianRegisterEqualsNat_eq_decide]
  · rw [correctedBranchHistoryBasis119_selector_value]
  · norm_num [historyRegisterWires]

end

end ExecutableHistoryExecutableHistory
