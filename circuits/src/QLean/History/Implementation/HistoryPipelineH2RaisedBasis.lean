import QLean.History.Implementation.HistoryPipelineH2PostSequenceAction
import QLean.History.Implementation.HistoryPipelineH2BranchIdentity
import QLean.History.Implementation.HistoryPipelineH2ConfigurationTransport

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

def raiseHistoryLabel119
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (labelLt : index.state.label.val < source.historyParameters.taylorOrder) :
    OldHistoryIndex119 source :=
  { clock := index.clock
    state :=
      { label :=
          { val := index.state.label.val + 1
            isLt := lt_of_le_of_lt (Nat.succ_le_of_lt labelLt)
              source.historyWellFormed.2.2.2.1 }
        configuration := configuration } }

@[simp] theorem raiseHistoryLabel119_clock
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (labelLt : index.state.label.val < source.historyParameters.taylorOrder) :
    (raiseHistoryLabel119 source index configuration labelLt).clock =
      index.clock := rfl

@[simp] theorem raiseHistoryLabel119_label_val
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (labelLt : index.state.label.val < source.historyParameters.taylorOrder) :
    (raiseHistoryLabel119 source index configuration labelLt).state.label.val =
      index.state.label.val + 1 := rfl

@[simp] theorem raiseHistoryLabel119_configuration
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (labelLt : index.state.label.val < source.historyParameters.taylorOrder) :
    (raiseHistoryLabel119 source index configuration labelLt).state.configuration =
      configuration := rfl

theorem executableHistoryBasis119_raiseLabel_outside_order
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (labelLt : index.state.label.val < source.historyParameters.taylorOrder)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (outside : ∀ orderIndex,
      (ExecutableLayout119 source domain).order.wire orderIndex ≠ wire) :
    executableHistoryBasis119 source domain fits
        (raiseHistoryLabel119 source index configuration labelLt) wire =
      executableHistoryBasis119 source domain fits
        (replaceConfiguration119 source index configuration) wire := by
  have clockBitsEqual :
      clockBits119 source fits
          (raiseHistoryLabel119 source index configuration labelLt) =
        clockBits119 source fits
          (replaceConfiguration119 source index configuration) := by
    funext bit
    rfl
  unfold executableHistoryBasis119
  rw [clockBitsEqual]
  simp [raiseHistoryLabel119, replaceConfiguration119,
    writeRegisterBits, outside]

theorem correctedBranchHistoryBasis119_raiseLabel_outside_order
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (labelLt : index.state.label.val < source.historyParameters.taylorOrder)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (outside : ∀ orderIndex,
      (ExecutableLayout119 source domain).order.wire orderIndex ≠ wire) :
    correctedBranchHistoryBasis119 source domain fits branch
        (raiseHistoryLabel119 source index configuration labelLt) wire =
      correctedBranchHistoryBasis119 source domain fits branch
        (replaceConfiguration119 source index configuration) wire := by
  by_cases selectorMember : wire ∈
      historyRegisterWires (ExecutableLayout119 source domain).selector
  · simp only [historyRegisterWires, List.mem_ofFn] at selectorMember
    rcases selectorMember with ⟨selectorIndex, rfl⟩
    have left := congrFun
      (correctedBranchHistoryBasis119_restrict_selector source domain fits branch
        (raiseHistoryLabel119 source index configuration labelLt)) selectorIndex
    have right := congrFun
      (correctedBranchHistoryBasis119_restrict_selector source domain fits branch
        (replaceConfiguration119 source index configuration)) selectorIndex
    exact left.trans right.symm
  · rw [correctedBranchHistoryBasis119_apply_of_not_selector,
      correctedBranchHistoryBasis119_apply_of_not_selector]
    · exact executableHistoryBasis119_raiseLabel_outside_order
        source domain fits index configuration labelLt wire outside
    · exact selectorMember
    · exact selectorMember

theorem writeRegisterValue_correctedBranchHistoryBasis119_raiseLabel
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (labelLt : index.state.label.val < source.historyParameters.taylorOrder) :
    writeRegisterValue (ExecutableLayout119 source domain).order
        (index.state.label.val + 1)
        (correctedBranchHistoryBasis119 source domain fits branch
          (replaceConfiguration119 source index configuration)) =
      correctedBranchHistoryBasis119 source domain fits branch
        (raiseHistoryLabel119 source index configuration labelLt) := by
  funext wire
  by_cases inside : ∃ orderIndex,
      (ExecutableLayout119 source domain).order.wire orderIndex = wire
  · rcases inside with ⟨orderIndex, rfl⟩
    rw [writeRegisterValue_apply_wire]
    have readRaised := congrFun
      (correctedBranchHistoryBasis119_read_order source domain fits branch
        (raiseHistoryLabel119 source index configuration labelLt)) orderIndex
    change (index.state.label.val + 1).testBit orderIndex.val =
      (ExecutableLayout119 source domain).order.read
        (correctedBranchHistoryBasis119 source domain fits branch
          (raiseHistoryLabel119 source index configuration labelLt)) orderIndex
    rw [readRaised]
    rfl
  · rw [writeRegisterValue_apply_outside]
    · exact (correctedBranchHistoryBasis119_raiseLabel_outside_order
        source domain fits branch index configuration labelLt wire
        (fun orderIndex equal => inside ⟨orderIndex, equal⟩)).symm
    · intro orderIndex equal
      exact inside ⟨orderIndex, equal⟩

end
end ExecutableHistoryExecutableHistory
