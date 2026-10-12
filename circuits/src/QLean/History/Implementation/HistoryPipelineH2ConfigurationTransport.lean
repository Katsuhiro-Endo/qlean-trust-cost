import QLean.History.Implementation.HistoryPipelineH2LiveFacts

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

def replaceConfiguration119
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters) :
    OldHistoryIndex119 source :=
  { clock := index.clock
    state :=
      { label := index.state.label
        configuration := configuration } }

@[simp] theorem replaceConfiguration119_clock
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters) :
    (replaceConfiguration119 source index configuration).clock = index.clock := rfl

@[simp] theorem replaceConfiguration119_label
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters) :
    (replaceConfiguration119 source index configuration).state.label =
      index.state.label := rfl

@[simp] theorem replaceConfiguration119_configuration
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters) :
    (replaceConfiguration119 source index configuration).state.configuration =
      configuration := rfl

theorem executableQ10Outside_not_data119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (outside : OutsideWire
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := ExecutableLayout119 source domain)
        (ExecutableAdmissible119 source domain).placementWidths).placement.embedding.placement)
    (dataIndex : Fin (ExecutableRaw119 source).history.dataWidth) :
    (ExecutableLayout119 source domain).data.wire dataIndex ≠ outside.1 := by
  let systemIndex : Fin source.qParameters.systemWidth :=
    Fin.cast (executableHistory_dataWidth_eq_system119 source) dataIndex
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := ExecutableLayout119 source domain)
    (ExecutableAdmissible119 source domain).placementWidths
  have placed := executableQ10Placement_system_wire119
    source domain systemIndex
  have placed' : evidence.placement.embedding.placement
        (wireToCanonicalFin (Wire.system systemIndex)) =
      (ExecutableLayout119 source domain).data.wire dataIndex := by
    simpa [evidence, systemIndex] using placed
  intro equal
  exact outside.2 (wireToCanonicalFin (Wire.system systemIndex))
    (placed'.trans equal)

theorem executableHistoryBasis119_replaceConfiguration_outside
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (outside : OutsideWire
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := ExecutableLayout119 source domain)
        (ExecutableAdmissible119 source domain).placementWidths).placement.embedding.placement) :
    executableHistoryBasis119 source domain fits
        (replaceConfiguration119 source index configuration) outside.1 =
      executableHistoryBasis119 source domain fits index outside.1 := by
  have noData : ∀ dataIndex,
      (ExecutableLayout119 source domain).data.wire dataIndex ≠ outside.1 :=
    executableQ10Outside_not_data119 source domain outside
  unfold executableHistoryBasis119
  rw [writeRegisterBits_apply_outside
      (ExecutableLayout119 source domain).data
      (dataBits119 source
        (replaceConfiguration119 source index configuration).state.configuration)
      _ outside.1 noData]
  rw [writeRegisterBits_apply_outside
      (ExecutableLayout119 source domain).data
      (dataBits119 source index.state.configuration)
      _ outside.1 noData]
  rfl

theorem correctedBranchHistoryBasis119_replaceConfiguration_outside
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (outside : OutsideWire
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := ExecutableLayout119 source domain)
        (ExecutableAdmissible119 source domain).placementWidths).placement.embedding.placement) :
    correctedBranchHistoryBasis119 source domain fits branch
        (replaceConfiguration119 source index configuration) outside.1 =
      correctedBranchHistoryBasis119 source domain fits branch index outside.1 := by
  by_cases selectorMember : outside.1 ∈
      historyRegisterWires (ExecutableLayout119 source domain).selector
  · simp only [historyRegisterWires, List.mem_ofFn] at selectorMember
    rcases selectorMember with ⟨selectorIndex, equal⟩
    rw [← equal]
    have left := congrFun
      (correctedBranchHistoryBasis119_restrict_selector source domain fits branch
        (replaceConfiguration119 source index configuration)) selectorIndex
    have right := congrFun
      (correctedBranchHistoryBasis119_restrict_selector source domain fits branch
        index) selectorIndex
    exact left.trans right.symm
  · rw [correctedBranchHistoryBasis119_apply_of_not_selector,
      correctedBranchHistoryBasis119_apply_of_not_selector]
    · exact executableHistoryBasis119_replaceConfiguration_outside
        source domain fits index configuration outside
    · exact selectorMember
    · exact selectorMember

theorem h2BeforeQ119_replaceConfiguration_outside
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    restrictToOutsideWires evidence.placement.embedding.placement
        (h2BeforeQ119 layout
          (correctedBranchHistoryBasis119 source domain fits branch
            (replaceConfiguration119 source index configuration))) =
      restrictToOutsideWires evidence.placement.embedding.placement
        (h2BeforeQ119 layout
          (correctedBranchHistoryBasis119 source domain fits branch index)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  funext outside
  change h2BeforeQ119 layout
      (correctedBranchHistoryBasis119 source domain fits branch
        (replaceConfiguration119 source index configuration)) outside.1 =
    h2BeforeQ119 layout
      (correctedBranchHistoryBasis119 source domain fits branch index) outside.1
  by_cases live : outside.1 ∈ historyTaylorBeforeGeneratorLiveWires layout
  · simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
      List.not_mem_nil, or_false] at live
    rcases live with equal | equal | equal | equal
    · rw [equal, h2BeforeQ119_branch_flag_value,
        h2BeforeQ119_branch_flag_value]
    · rw [equal, h2BeforeQ119_time_flag_value,
        h2BeforeQ119_time_flag_value]
      rfl
    · rw [equal, h2BeforeQ119_idle_flag_value,
        h2BeforeQ119_idle_flag_value]
      unfold historyTaylorClockLessThanIdleEndValue
      rw [correctedBranchHistoryBasis119_read_clock,
        correctedBranchHistoryBasis119_read_clock]
      rfl
    · rw [equal, h2BeforeQ119_active_selected_value,
        h2BeforeQ119_active_selected_value]
      rfl
  · rw [h2BeforeQ119_apply_of_not_mem_live layout _ outside.1 live,
      h2BeforeQ119_apply_of_not_mem_live layout _ outside.1 live]
    exact correctedBranchHistoryBasis119_replaceConfiguration_outside
      source domain fits branch index configuration outside

theorem h2SelectedQOutput119_eq_before_replaceConfiguration
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (outputConfiguration : QConfiguration source.qParameters) :
    h2SelectedQOutput119 source domain fits index outputConfiguration =
      h2BeforeQ119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
          (replaceConfiguration119 source index outputConfiguration)) := by
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  apply (fullBasis_eq_iff_restrictions_eq
    evidence.placement.embedding.placement _ _).2
  constructor
  · rw [h2SelectedQOutput119_restrict_placed]
    simpa using (h2BeforeQ119_q10RestrictedBasis_eq_success119
      source domain fits h2SelectedBranch119
        (replaceConfiguration119 source index outputConfiguration)).symm
  · rw [h2SelectedQOutput119_restrict_outside]
    exact (h2BeforeQ119_replaceConfiguration_outside source domain fits
      h2SelectedBranch119 index outputConfiguration).symm

theorem executableH2Q10_selected_logical_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (outputConfiguration : QConfiguration source.qParameters) :
    h2ControlledQ10CleanOperator
        (ExecutableH2Q10Specification119 source domain)
        (h2BeforeQ119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits
            h2SelectedBranch119
            (replaceConfiguration119 source index outputConfiguration)))
        (h2BeforeQ119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits
            h2SelectedBranch119 index)) =
      (HistoryBlockEncoding.QModel.configurationQMatrix
          (executableQConfiguration119 source domain outputConfiguration)
          (executableQConfiguration119 source domain
            index.state.configuration) : ℂ) /
        ((3 * (ExecutableH2Q10Specification119 source domain).p.K : Nat) : ℂ) := by
  rw [← h2SelectedQOutput119_eq_before_replaceConfiguration]
  exact executableH2Q10_selected_clean_success_entry119
    source domain fits index clockActive outputConfiguration

end
end ExecutableHistoryExecutableHistory
