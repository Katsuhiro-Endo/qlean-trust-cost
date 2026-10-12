import QLean.History.Implementation.HistoryPipelineP05SelectorLocality
import QLean.History.Implementation.HistoryPipelineH2FullEquality

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

noncomputable def executableH2Target119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    VerifiedCircuitCore.Operator
      (QubitBasis (ExecutableRaw119 source).history.qubits) :=
  h2TaylorCleanOperator
    (historyP15H2CleanUnderstandingSpecification
      (ExecutableLayout119 source domain)
      (ScientificWidthGenericContract.correctedCleanEvidence259
        (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
      (ExecutableAdmissible119 source domain).placementWidths
      (fun degree => correctedTaylorCoefficientAngle119
        source.toCommonSource119 degree.val)
      compiledIdleCoefficientAngle119)

noncomputable def repairedSelectMiddle119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    VerifiedCircuitCore.Operator
      (QubitBasis (ExecutableRaw119 source).history.qubits) :=
  repairedH3RecordedTarget119 source domain *
    executableH2Target119 source domain

theorem repairedH3RecordedTarget119_mem_unitaryGroup
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    repairedH3RecordedTarget119 source domain ∈
      Matrix.unitaryGroup
        (QubitBasis (ExecutableRaw119 source).history.qubits) ℂ := by
  have hmem := VerifiedCircuitCore.primitiveCircuit_denote_mem_unitaryGroup
    internalZeroSymbolEnvironment (repairedH3Component119 source domain).circuit
  rw [(repairedH3Component119 source domain).correct,
    repairedH3Component119_target] at hmem
  exact hmem

theorem unitary_entry_zero_of_fixed_row119
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : VerifiedCircuitCore.Operator basis)
    (unitary : operator ∈ Matrix.unitaryGroup basis ℂ)
    (fixed input : basis)
    (fixedAction : VerifiedCircuitCore.applyOperator operator
      (VerifiedCircuitCore.basisKet fixed) =
        VerifiedCircuitCore.basisKet fixed)
    (different : fixed ≠ input) :
    operator fixed input = 0 := by
  have leftInverse : star operator * operator = 1 :=
    (Matrix.mem_unitaryGroup_iff').1 unitary
  have column : ∀ output, operator output fixed =
      if output = fixed then 1 else 0 := by
    intro output
    have point := congrFun fixedAction output
    simpa [VerifiedCircuitCore.applyOperator_basisKet,
      VerifiedCircuitCore.basisKet_apply] using point
  have entry := congrFun (congrFun leftInverse fixed) input
  simp only [Matrix.mul_apply, Matrix.one_apply] at entry
  rw [if_neg different] at entry
  rw [Finset.sum_eq_single fixed] at entry
  · simpa [Matrix.star_apply, column]
      using entry
  · intro other _ otherNe
    simp [Matrix.star_apply, column, otherNe]
  · simp

theorem correctedBranchHistoryBasis119_q10CanonicalAllZero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    q10CanonicalCoreAllZeroInputPredicate (ExecutableQParameters119 source domain)
      (restrictToPlacedWires evidence.placement.embedding.placement
        (correctedBranchHistoryBasis119 source domain fits branch index)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  let restricted := restrictToPlacedWires evidence.placement.embedding.placement
    (correctedBranchHistoryBasis119 source domain fits branch index)
  let joint := coreBasisToJoint restricted
  let system : RegisterBasis (ExecutableQParameters119 source domain).systemWidth :=
    fun systemIndex => joint (Wire.system systemIndex)
  have jointEqual : joint = zeroAncillaJointBasis
      (ExecutableQParameters119 source domain) system := by
    funext wire
    cases wire with
    | ancilla ancillaIndex =>
        change correctedBranchHistoryBasis119 source domain fits branch index
          (evidence.placement.embedding.placement
            (wireToCanonicalFin (Wire.ancilla ancillaIndex))) = false
        rw [correctedBranchHistoryBasis119_apply_outside]
        · exact executableQ10Placement_ancilla_zero119 source domain fits index
            ancillaIndex
        · intro selectorIndex equal
          have member := executableQ10Placement_ancilla_mem119
            source domain ancillaIndex
          have tailMember :
              evidence.placement.embedding.placement
                  (wireToCanonicalFin (Wire.ancilla ancillaIndex)) ∈
                historyNonselectorTail119 layout := by
            rcases List.mem_append.mp member with signalMember | workMember
            · unfold historyNonselectorTail119
              exact List.mem_append_left _
                (List.mem_append_left _
                  (List.mem_append_right _ signalMember))
            · have workspaceMember :
                  evidence.placement.embedding.placement
                      (wireToCanonicalFin (Wire.ancilla ancillaIndex)) ∈
                    historyRegisterWires layout.workspace := by
                simp only [historyRegisterWires, List.mem_ofFn] at workMember
                rcases workMember with ⟨workIndex, workEqual⟩
                rw [← workEqual]
                exact historyGeneratorWorkRegister_wire_mem_workspace
                  layout workIndex
              unfold historyNonselectorTail119
              exact List.mem_append_right _ workspaceMember
          exact selector_wire_ne_historyNonselectorTail119
            layout selectorIndex _ tailMember
            (by simpa [correctedSelectorPlacement119, layout] using equal)
    | system systemIndex =>
        rfl
  change q11AllZeroAncillaInputPredicate
    (ExecutableQParameters119 source domain) joint
  rw [jointEqual]
  exact q11AllZeroAncillaInputPredicate_zeroAncillaJointBasis
    (ExecutableQParameters119 source domain) system

theorem correctedBranchHistoryBasis119_p15FullCleanInput
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    historyP15FullCleanInputPredicate
        (layout := ExecutableLayout119 source domain)
        (p := source.qParameters)
        (ExecutableAdmissible119 source domain).placementWidths
        (correctedBranchHistoryBasis119 source domain fits branch index) := by
  unfold historyP15FullCleanInputPredicate historyP15WithQ10Input
    historyP15Q10PlacedInputPredicate externallyControlledPlacedInputPredicate
  constructor
  · exact correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits branch index
  · let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    constructor
    · rw [externallyControlledCleanWorkPredicate_iff_controlWork_zero]
      intro wire member
      rw [historyP15Q10Placement_compilerWork] at member
      simp only [historyRegisterWires, List.mem_ofFn] at member
      rcases member with ⟨workIndex, rfl⟩
      have workspaceMember := historyControlledWork_wire_mem_workspace
        layout workIndex
      simp only [historyRegisterWires, List.mem_ofFn] at workspaceMember
      rcases workspaceMember with ⟨workspaceIndex, equal⟩
      rw [← equal]
      exact correctedBranchHistoryBasis119_workspace_zero source domain fits
        branch index workspaceIndex
    · exact correctedBranchHistoryBasis119_q10CanonicalAllZero
        source domain fits branch index

theorem executableH2Target119_output_supported
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex : OldHistoryIndex119 source) :
    VerifiedCircuitCore.applyOperator (executableH2Target119 source domain)
        (VerifiedCircuitCore.basisKet
          (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
            inputIndex)) ∈
      SubspaceMapComponent.basisSpan
        (historyP15FullCleanOutputPredicate
          (layout := ExecutableLayout119 source domain)
          (p := source.qParameters)
          (ExecutableAdmissible119 source domain).placementWidths) := by
  let component := historyP15FullCleanH2Component
    (ExecutableLayout119 source domain)
    (ScientificWidthGenericContract.correctedCleanEvidence259
      (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
    (ExecutableAdmissible119 source domain).placementWidths
    (fun coefficientIndex => correctedTaylorCoefficientAngle119
      source.toCommonSource119 coefficientIndex.val)
    compiledIdleCoefficientAngle119
  have inputMem : VerifiedCircuitCore.basisKet
        (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
          inputIndex) ∈ component.inputSubspace := by
    rw [(historyP15FullCleanH2Component_spaces
      (ExecutableLayout119 source domain)
      (ScientificWidthGenericContract.correctedCleanEvidence259
        (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
      (ExecutableAdmissible119 source domain).placementWidths
      (fun coefficientIndex => correctedTaylorCoefficientAngle119
        source.toCommonSource119 coefficientIndex.val)
      compiledIdleCoefficientAngle119).1]
    apply SubspaceMapComponent.basisKet_mem_basisSpan
    exact correctedBranchHistoryBasis119_p15FullCleanInput
      source domain fits h2SelectedBranch119 inputIndex
  have mapped := component.target_maps
    (VerifiedCircuitCore.basisKet
      (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
        inputIndex)) inputMem
  rw [historyP15FullCleanH2Component_target,
    (historyP15FullCleanH2Component_spaces
      (ExecutableLayout119 source domain)
      (ScientificWidthGenericContract.correctedCleanEvidence259
        (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
      (ExecutableAdmissible119 source domain).placementWidths
      (fun coefficientIndex => correctedTaylorCoefficientAngle119
        source.toCommonSource119 coefficientIndex.val)
      compiledIdleCoefficientAngle119).2] at mapped
  exact mapped

theorem executableH2Target119_nonzero_output_predicate
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex : OldHistoryIndex119 source)
    (output : QubitBasis (ExecutableRaw119 source).history.qubits)
    (nonzero : executableH2Target119 source domain output
      (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
        inputIndex) ≠ 0) :
    historyP15FullCleanOutputPredicate
      (layout := ExecutableLayout119 source domain)
      (p := source.qParameters)
      (ExecutableAdmissible119 source domain).placementWidths output := by
  by_contra outside
  have zero := SubspaceMapComponent.basisSpan_apply_eq_zero
    (executableH2Target119_output_supported source domain fits inputIndex)
    output outside
  simp only [VerifiedCircuitCore.applyOperator_basisKet] at zero
  exact nonzero zero

theorem executableH2Target119_nonzero_selector_value_one
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex : OldHistoryIndex119 source)
    (output : QubitBasis (ExecutableRaw119 source).history.qubits)
    (nonzero : executableH2Target119 source domain output
      (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
        inputIndex) ≠ 0) :
    ClassicalReversibleStage.littleEndianListNat
        (ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).selector)
          output) = 1 := by
  have wireEqual : ∀ selectorIndex : Fin 2,
      output ((ExecutableLayout119 source domain).selector.wire selectorIndex) =
        correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
          inputIndex
          ((ExecutableLayout119 source domain).selector.wire selectorIndex) := by
    intro selectorIndex
    exact executableH2Target_preserves_selector_wire119 source domain
      selectorIndex output
      (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
        inputIndex) nonzero
  have readsEqual :
      ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).selector)
          output =
        ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).selector)
          (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
            inputIndex) := by
    simp only [ClassicalReversibleStage.readWires, historyRegisterWires]
    apply List.map_congr_left
    intro wire member
    simp only [List.mem_ofFn] at member
    rcases member with ⟨selectorIndex, rfl⟩
    exact wireEqual selectorIndex
  rw [readsEqual, correctedBranchHistoryBasis119_selector_value]
  rfl

theorem repairedH3RecordedTarget119_identity_on_h2_support
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex : OldHistoryIndex119 source)
    (middle : QubitBasis (ExecutableRaw119 source).history.qubits)
    (nonzero : executableH2Target119 source domain middle
      (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
        inputIndex) ≠ 0) :
    VerifiedCircuitCore.applyOperator (repairedH3RecordedTarget119 source domain)
        (VerifiedCircuitCore.basisKet middle) =
      VerifiedCircuitCore.basisKet middle := by
  apply repairedH3RecordedTarget119_apply_basisKet_of_selector_false
  · exact (executableH2Target119_nonzero_output_predicate
      source domain fits inputIndex middle nonzero).2
  · rw [ClassicalReversibleStage.littleEndianRegisterEqualsNat_eq_decide]
    · rw [executableH2Target119_nonzero_selector_value_one
        source domain fits inputIndex middle nonzero]
      decide
    · norm_num [historyRegisterWires]

theorem correctedBranchH3_cross_from_two_zero119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputBranch : Fin 4)
    (outputIndex inputIndex : OldHistoryIndex119 source)
    (outputNeTwo : outputBranch.val ≠ 2) :
    repairedH3RecordedTarget119 source domain
        (correctedBranchHistoryBasis119 source domain fits outputBranch
          outputIndex)
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          inputIndex) = 0 := by
  apply unitary_entry_zero_of_fixed_row119
    (repairedH3RecordedTarget119 source domain)
    (repairedH3RecordedTarget119_mem_unitaryGroup source domain)
  · exact correctedBranchH3_identity119 source domain fits outputBranch
      outputIndex outputNeTwo
  · intro equal
    have selectorEqual := congrArg
      (ClassicalReversibleStage.littleEndianListNat ∘
        ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).selector))
      equal
    change ClassicalReversibleStage.littleEndianListNat
        (ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).selector)
          (correctedBranchHistoryBasis119 source domain fits outputBranch
            outputIndex)) =
      ClassicalReversibleStage.littleEndianListNat
        (ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).selector)
          (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
            inputIndex)) at selectorEqual
    rw [correctedBranchHistoryBasis119_selector_value,
      correctedBranchHistoryBasis119_selector_value] at selectorEqual
    exact outputNeTwo selectorEqual

theorem repairedSelectMiddle119_branch_zero_action
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex : OldHistoryIndex119 source) :
    VerifiedCircuitCore.applyOperator
        (repairedSelectMiddle119 source domain)
        (VerifiedCircuitCore.basisKet
          (correctedBranchHistoryBasis119 source domain fits
            ⟨0, by decide⟩ inputIndex)) =
      VerifiedCircuitCore.basisKet
        (correctedBranchHistoryBasis119 source domain fits
          ⟨0, by decide⟩ inputIndex) := by
  unfold repairedSelectMiddle119
  rw [VerifiedCircuitCore.applyOperator_mul]
  rw [show VerifiedCircuitCore.applyOperator (executableH2Target119 source domain)
      (VerifiedCircuitCore.basisKet
        (correctedBranchHistoryBasis119 source domain fits
          ⟨0, by decide⟩ inputIndex)) =
        VerifiedCircuitCore.basisKet
          (correctedBranchHistoryBasis119 source domain fits
            ⟨0, by decide⟩ inputIndex) by
      exact correctedBranchH2_identity119 source domain fits
        ⟨0, by decide⟩ inputIndex (by decide)]
  exact correctedBranchH3_identity119 source domain fits
    ⟨0, by decide⟩ inputIndex (by decide)

theorem repairedSelectMiddle119_branch_zero_entry
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputBranch : Fin 4)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    repairedSelectMiddle119 source domain
        (correctedBranchHistoryBasis119 source domain fits outputBranch outputIndex)
        (correctedBranchHistoryBasis119 source domain fits
          ⟨0, by decide⟩ inputIndex) =
      if outputBranch = ⟨0, by decide⟩ ∧ outputIndex = inputIndex then 1 else 0 := by
  have action := repairedSelectMiddle119_branch_zero_action
    source domain fits inputIndex
  have point := congrFun action
    (correctedBranchHistoryBasis119 source domain fits outputBranch outputIndex)
  simp only [VerifiedCircuitCore.applyOperator_basisKet,
    VerifiedCircuitCore.basisKet_apply] at point
  rw [point]
  congr 1
  apply propext
  constructor
  · intro equal
    have selectorEqual := congrArg
      (ClassicalReversibleStage.littleEndianListNat ∘
        ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).selector))
      equal
    change ClassicalReversibleStage.littleEndianListNat
        (ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).selector)
          (correctedBranchHistoryBasis119 source domain fits outputBranch
            outputIndex)) =
      ClassicalReversibleStage.littleEndianListNat
        (ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).selector)
          (correctedBranchHistoryBasis119 source domain fits
            ⟨0, by decide⟩ inputIndex)) at selectorEqual
    rw [correctedBranchHistoryBasis119_selector_value,
      correctedBranchHistoryBasis119_selector_value] at selectorEqual
    have branchEqual : outputBranch = ⟨0, by decide⟩ := by
      apply Fin.ext
      exact selectorEqual
    subst outputBranch
    have injective := correctedBranchHistoryBasis119_injective_index
      source domain fits ⟨0, by decide⟩
    exact ⟨rfl, injective equal⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem repairedSelectMiddle119_branch_one_column
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex : OldHistoryIndex119 source)
    (output : QubitBasis (ExecutableRaw119 source).history.qubits) :
    repairedSelectMiddle119 source domain output
        (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
          inputIndex) =
      executableH2Target119 source domain output
        (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
          inputIndex) := by
  unfold repairedSelectMiddle119
  rw [Matrix.mul_apply]
  calc
    ∑ middle, repairedH3RecordedTarget119 source domain output middle *
        executableH2Target119 source domain middle
          (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
            inputIndex) =
      ∑ middle, (if output = middle then 1 else 0) *
        executableH2Target119 source domain middle
          (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
            inputIndex) := by
        apply Finset.sum_congr rfl
        intro middle _
        by_cases coefficientZero : executableH2Target119 source domain middle
            (correctedBranchHistoryBasis119 source domain fits
              h2SelectedBranch119 inputIndex) = 0
        · simp [coefficientZero]
        · have action := repairedH3RecordedTarget119_identity_on_h2_support
            source domain fits inputIndex middle coefficientZero
          have point := congrFun action output
          simp only [VerifiedCircuitCore.applyOperator_basisKet,
            VerifiedCircuitCore.basisKet_apply] at point
          rw [point]
    _ = executableH2Target119 source domain output
        (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
          inputIndex) := by
      simp

theorem executableH2Target119_cross_branch_zero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputBranch : Fin 4)
    (outputIndex inputIndex : OldHistoryIndex119 source)
    (outputNeOne : outputBranch ≠ h2SelectedBranch119) :
    executableH2Target119 source domain
        (correctedBranchHistoryBasis119 source domain fits outputBranch
          outputIndex)
        (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
          inputIndex) = 0 := by
  by_contra nonzero
  have value := executableH2Target119_nonzero_selector_value_one
    source domain fits inputIndex
    (correctedBranchHistoryBasis119 source domain fits outputBranch outputIndex)
    nonzero
  rw [correctedBranchHistoryBasis119_selector_value] at value
  apply outputNeOne
  apply Fin.ext
  simpa [h2SelectedBranch119] using value

theorem repairedSelectMiddle119_branch_one_entry
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputBranch : Fin 4)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    repairedSelectMiddle119 source domain
        (correctedBranchHistoryBasis119 source domain fits outputBranch outputIndex)
        (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
          inputIndex) =
      if outputBranch = h2SelectedBranch119 then
        (HistoryBlockEncoding.HistorySpec.L1 source.historyParameters
          (commonModelQ119 source.toCommonSource119) outputIndex inputIndex :
            Complex)
      else 0 := by
  rw [repairedSelectMiddle119_branch_one_column]
  split_ifs with selected
  · subst outputBranch
    simpa [executableH2Target119] using
      executableH2_all_logical_entry_eq_L1_119
        source domain fits inputIndex outputIndex
  · exact executableH2Target119_cross_branch_zero
      source domain fits outputBranch outputIndex inputIndex selected

theorem repairedSelectMiddle119_branch_two_entry
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputBranch : Fin 4)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    repairedSelectMiddle119 source domain
        (correctedBranchHistoryBasis119 source domain fits outputBranch outputIndex)
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          inputIndex) =
      if outputBranch = h3SelectedBranch119 then
        (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
          outputIndex inputIndex : Real) : Complex))
      else 0 := by
  unfold repairedSelectMiddle119
  rw [Matrix.mul_apply]
  have h2Action := correctedBranchH2_identity119 source domain fits
    h3SelectedBranch119 inputIndex (by decide)
  have h2Column : ∀ middle,
      executableH2Target119 source domain middle
          (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
            inputIndex) =
        if middle = correctedBranchHistoryBasis119 source domain fits
            h3SelectedBranch119 inputIndex then 1 else 0 := by
    intro middle
    have point := congrFun h2Action middle
    simpa [executableH2Target119,
      VerifiedCircuitCore.applyOperator_basisKet,
      VerifiedCircuitCore.basisKet_apply] using point
  simp_rw [h2Column]
  rw [Finset.sum_eq_single
    (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
      inputIndex)]
  · simp only [if_pos, mul_one]
    split_ifs with selected
    · subst outputBranch
      exact repairedH3RecordedTarget119_all_logical_entries
        source domain fits inputIndex outputIndex
    · exact correctedBranchH3_cross_from_two_zero119 source domain fits
        outputBranch outputIndex inputIndex (by
          intro value
          apply selected
          apply Fin.ext
          exact value)
  · intro other _ different
    simp [different]
  · simp

end
end ExecutableHistoryExecutableHistory
