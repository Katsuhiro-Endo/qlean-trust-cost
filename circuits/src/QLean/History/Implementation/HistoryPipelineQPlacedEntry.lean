import QLean.History.Implementation.HistoryPipelineQSuccessEntry
import QLean.History.Implementation.HistoryPipelineHistoryCleanInput

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

def executableQConfiguration119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (configuration : QConfiguration source.qParameters) :
    QConfiguration (ExecutableQParameters119 source domain) :=
  Eq.mp (congrArg QConfiguration
    (executableQParameters_eq119 source domain).symm) configuration

theorem executableQ10Placement_system_wire119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (systemIndex : Fin source.qParameters.systemWidth) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    evidence.placement.embedding.placement
        (wireToCanonicalFin (Wire.system systemIndex)) =
      layout.data.wire
        (Fin.cast (executableHistory_dataWidth_eq_system119 source).symm
          systemIndex) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  let coreIndex : Fin
      ((ExecutableQParameters119 source domain).ancillaWidth +
        (ExecutableQParameters119 source domain).systemWidth) :=
    wireToCanonicalFin (Wire.system systemIndex)
  let ancillaWires := historyRegisterWires layout.generatorSignal ++
    historyRegisterWires (historyGeneratorWorkRegister layout)
  let dataIndex : Fin (ExecutableRaw119 source).history.dataWidth :=
    Fin.cast (executableHistory_dataWidth_eq_system119 source).symm systemIndex
  have sourceOrder := historyP15Q10Placement_sourceOrder
    (layout := layout) widths
  have sourceOrder' :
      List.ofFn evidence.placement.embedding.placement =
        ancillaWires ++ historyRegisterWires layout.data := by
    simpa [evidence, ancillaWires] using sourceOrder
  have ancillaLength : ancillaWires.length =
      (ExecutableQParameters119 source domain).ancillaWidth := by
    simp [ancillaWires, historyRegisterWires, widths.signal_eq, widths.work_eq]
  have coreAt : coreIndex.val =
      (ExecutableQParameters119 source domain).ancillaWidth + systemIndex.val := by
    rfl
  have corePast : ancillaWires.length ≤ coreIndex.val := by
    rw [ancillaLength, coreAt]
    omega
  have coreNotLt : ¬ coreIndex.val < ancillaWires.length :=
    Nat.not_lt_of_ge corePast
  have shifted : coreIndex.val - ancillaWires.length = dataIndex.val := by
    rw [ancillaLength, coreAt]
    simp [dataIndex]
  have atIndex := congrArg (fun wires => wires[coreIndex.val]?) sourceOrder'
  have result :
      some (evidence.placement.embedding.placement coreIndex) =
        some (layout.data.wire dataIndex) := by
    simpa only [List.getElem?_ofFn, coreIndex.isLt, dif_pos, Fin.eta,
      List.getElem?_append, coreNotLt, if_neg, if_false, shifted,
      historyRegisterWires, List.getElem?_ofFn, dataIndex.isLt] using atIndex
  exact Option.some.inj result

theorem executableQ10RestrictedBasis_eq_success119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    restrictToPlacedWires evidence.placement.embedding.placement
        (executableHistoryBasis119 source domain fits index) =
      canonicalCoreSuccessBasis119 (ExecutableQParameters119 source domain)
        (executableQConfiguration119 source domain
          index.state.configuration) := by
  dsimp only
  cases executableQParameters_eq119 source domain
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  have jointEqual :
      coreBasisToJoint
          (restrictToPlacedWires evidence.placement.embedding.placement
            (executableHistoryBasis119 source domain fits index)) =
        combineBasis
          (allZeroAncilla
            (ExecutableQParameters119 source domain).ancillaWidth)
          (delimiterEncoding
            (executableQConfiguration119 source domain
              index.state.configuration)) := by
    funext wire
    cases wire with
    | ancilla ancillaIndex =>
        change executableHistoryBasis119 source domain fits index
          (evidence.placement.embedding.placement
            (wireToCanonicalFin (Wire.ancilla ancillaIndex))) = false
        exact executableQ10Placement_ancilla_zero119 source domain fits index
          ancillaIndex
    | system systemIndex =>
        change executableHistoryBasis119 source domain fits index
          (evidence.placement.embedding.placement
            (wireToCanonicalFin (Wire.system systemIndex))) =
          delimiterEncoding index.state.configuration systemIndex
        rw [executableQ10Placement_system_wire119 source domain systemIndex]
        change (ExecutableLayout119 source domain).data.read
            (executableHistoryBasis119 source domain fits index)
            (Fin.cast (executableHistory_dataWidth_eq_system119 source).symm
              systemIndex) = _
        rw [executableHistoryBasis119_read_data source domain fits index]
        rfl
  funext coreIndex
  change restrictToPlacedWires evidence.placement.embedding.placement
      (executableHistoryBasis119 source domain fits index) coreIndex =
    canonicalCoreSuccessBasis119 (ExecutableQParameters119 source domain)
      (executableQConfiguration119 source domain
        index.state.configuration) coreIndex
  have bitEqual := congrFun jointEqual (canonicalFinToWire coreIndex)
  change restrictToPlacedWires evidence.placement.embedding.placement
      (executableHistoryBasis119 source domain fits index) coreIndex =
    combineBasis (allZeroAncilla source.qParameters.ancillaWidth)
      (delimiterEncoding
        (executableQConfiguration119 source domain
          index.state.configuration))
      (canonicalFinToWire coreIndex)
  simp only [coreBasisToJoint,
    wireToCanonicalFin_canonicalFinToWire] at bitEqual
  exact bitEqual

end

end ExecutableHistoryExecutableHistory
