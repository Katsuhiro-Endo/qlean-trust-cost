import QLean.History.Implementation.HistoryPipelineH2SelectedQInput

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

def h2SelectedBranch119 : Fin 4 := ⟨1, by omega⟩

def h2SelectedQOutput119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (outputConfiguration : QConfiguration source.qParameters) :
    QubitBasis (ExecutableRaw119 source).history.qubits :=
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  let input := h2BeforeQ119 layout
    (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119 index)
  mergePlacedAndOutsideBasis evidence.placement.embedding.placement
    (canonicalCoreSuccessBasis119 (ExecutableQParameters119 source domain)
      (executableQConfiguration119 source domain outputConfiguration))
    (restrictToOutsideWires evidence.placement.embedding.placement input)

theorem h2SelectedQOutput119_restrict_placed
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (outputConfiguration : QConfiguration source.qParameters) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    restrictToPlacedWires evidence.placement.embedding.placement
        (h2SelectedQOutput119 source domain fits index outputConfiguration) =
      canonicalCoreSuccessBasis119 (ExecutableQParameters119 source domain)
        (executableQConfiguration119 source domain outputConfiguration) := by
  dsimp only [h2SelectedQOutput119]
  exact restrictToPlacedWires_mergePlacedAndOutsideBasis _ _ _

theorem h2SelectedQOutput119_restrict_outside
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (outputConfiguration : QConfiguration source.qParameters) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    restrictToOutsideWires evidence.placement.embedding.placement
        (h2SelectedQOutput119 source domain fits index outputConfiguration) =
      restrictToOutsideWires evidence.placement.embedding.placement
        (h2BeforeQ119 layout
          (correctedBranchHistoryBasis119 source domain fits
            h2SelectedBranch119 index)) := by
  dsimp only [h2SelectedQOutput119]
  exact restrictToOutsideWires_mergePlacedAndOutsideBasis _ _ _

theorem executableH2Q10_selected_clean_success_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (outputConfiguration : QConfiguration source.qParameters) :
    h2ControlledQ10CleanOperator
        (ExecutableH2Q10Specification119 source domain)
        (h2SelectedQOutput119 source domain fits index outputConfiguration)
        (h2BeforeQ119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits
            h2SelectedBranch119 index)) =
      (HistoryBlockEncoding.QModel.configurationQMatrix
          (executableQConfiguration119 source domain outputConfiguration)
          (executableQConfiguration119 source domain
            index.state.configuration) : ℂ) /
        ((3 * (ExecutableH2Q10Specification119 source domain).p.K : Nat) : ℂ) := by
  apply executableH2Q10_clean_success_entry119
  · change h2BeforeQ119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h2SelectedBranch119 index)
        (historyActiveWire (ExecutableLayout119 source domain)) = true
    simpa [h2SelectedBranch119, clockActive] using
      h2BeforeQ119_active_selected_value source domain fits
        h2SelectedBranch119 index
  · exact h2SelectedQOutput119_restrict_outside
      source domain fits index outputConfiguration
  · exact h2SelectedQOutput119_restrict_placed
      source domain fits index outputConfiguration
  · exact h2BeforeQ119_q10RestrictedBasis_eq_success119
      source domain fits h2SelectedBranch119 index

end
end ExecutableHistoryExecutableHistory
