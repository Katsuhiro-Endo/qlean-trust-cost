import QLean.History.Implementation.HistoryPipelineHistoryEmbedding

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryHistoryCleanInput

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryExecutableHistory
open ExecutableHistoryHistoryEmbedding

noncomputable section

abbrev ExecutableQParameters119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  (GeneratorRawSchema.generatedP17P44Binding206
    (ExecutableRaw119 source).generator
    (ExecutableAdmissible119 source domain).generator).parameters

theorem executableQParameters_eq119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    ExecutableQParameters119 source domain = source.qParameters := by
  apply qParameters_eq119 <;> rfl

private def encodedHistoryWires119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    List (Fin (ExecutableRaw119 source).history.qubits) :=
  historyRegisterWires (ExecutableLayout119 source domain).data ++
    historyRegisterWires (ExecutableLayout119 source domain).clock ++
    historyRegisterWires (ExecutableLayout119 source domain).order

private def unencodedHistoryTailWires119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    List (Fin (ExecutableRaw119 source).history.qubits) :=
  historyRegisterWires (ExecutableLayout119 source domain).generatorSignal ++
    [(ExecutableLayout119 source domain).coefficientSignal,
      (ExecutableLayout119 source domain).orderBoundarySignal,
      (ExecutableLayout119 source domain).projectorSignal,
      (ExecutableLayout119 source domain).clockBoundarySignal] ++
    historyRegisterWires (ExecutableLayout119 source domain).workspace

theorem encodedHistoryWires_disjoint_tail119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    ∀ encoded ∈ encodedHistoryWires119 source domain,
      ∀ tail ∈ unencodedHistoryTailWires119 source domain,
        encoded ≠ tail := by
  let layout := ExecutableLayout119 source domain
  let selectorWires := historyRegisterWires layout.selector
  let encodedWires := encodedHistoryWires119 source domain
  let tailWires := unencodedHistoryTailWires119 source domain
  have normalized : (selectorWires ++ (encodedWires ++ tailWires)).Nodup := by
    simpa [layout, selectorWires, encodedWires, tailWires,
      encodedHistoryWires119, unencodedHistoryTailWires119,
      List.append_assoc] using layout.allWiresNodup
  have encodedTailNodup : (encodedWires ++ tailWires).Nodup :=
    (List.nodup_append.mp normalized).2.1
  exact (List.nodup_append.mp encodedTailNodup).2.2

theorem executableHistoryBasis119_apply_of_tail_mem
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (tail : wire ∈ unencodedHistoryTailWires119 source domain) :
    executableHistoryBasis119 source domain fits index wire = false := by
  unfold executableHistoryBasis119
  calc
    writeRegisterBits (ExecutableLayout119 source domain).data
        (dataBits119 source index.state.configuration)
        (writeRegisterBits (ExecutableLayout119 source domain).clock
          (clockBits119 source fits index)
          (writeRegisterBits (ExecutableLayout119 source domain).order
            (orderBits119 source fits index) (fun _ => false))) wire =
      writeRegisterBits (ExecutableLayout119 source domain).clock
        (clockBits119 source fits index)
        (writeRegisterBits (ExecutableLayout119 source domain).order
          (orderBits119 source fits index) (fun _ => false)) wire :=
      writeRegisterBits_apply_outside _ _ _ _ (by
        intro dataIndex equal
        exact encodedHistoryWires_disjoint_tail119 source domain
          ((ExecutableLayout119 source domain).data.wire dataIndex)
          (List.mem_append_left _
            (List.mem_append_left _
              (List.mem_ofFn.mpr ⟨dataIndex, rfl⟩)))
          wire tail equal)
    _ = writeRegisterBits (ExecutableLayout119 source domain).order
          (orderBits119 source fits index) (fun _ => false) wire :=
      writeRegisterBits_apply_outside _ _ _ _ (by
        intro clockIndex equal
        exact encodedHistoryWires_disjoint_tail119 source domain
          ((ExecutableLayout119 source domain).clock.wire clockIndex)
          (List.mem_append_left _
            (List.mem_append_right _
              (List.mem_ofFn.mpr ⟨clockIndex, rfl⟩)))
          wire tail equal)
    _ = false :=
      writeRegisterBits_apply_outside _ _ _ _ (by
        intro orderIndex equal
        exact encodedHistoryWires_disjoint_tail119 source domain
          ((ExecutableLayout119 source domain).order.wire orderIndex)
          (List.mem_append_right _
            (List.mem_ofFn.mpr ⟨orderIndex, rfl⟩))
          wire tail equal)

theorem executableHistoryBasis119_workspace_zero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    ∀ workspaceIndex,
      executableHistoryBasis119 source domain fits index
          ((ExecutableLayout119 source domain).workspace.wire workspaceIndex) = false := by
  intro workspaceIndex
  apply executableHistoryBasis119_apply_of_tail_mem source domain fits index
  exact List.mem_append_right _
    (List.mem_ofFn.mpr ⟨workspaceIndex, rfl⟩)

theorem executableHistoryBasis119_generatorWork_zero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    ∀ workIndex,
      executableHistoryBasis119 source domain fits index
          ((historyGeneratorWorkRegister (ExecutableLayout119 source domain)).wire
            workIndex) = false := by
  intro workIndex
  apply executableHistoryBasis119_apply_of_tail_mem source domain fits index
  have workspaceMember := historyGeneratorWorkRegister_wire_mem_workspace
    (ExecutableLayout119 source domain) workIndex
  exact List.mem_append_right _ workspaceMember

theorem executableHistoryBasis119_p15_auxiliary
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    historyTaylorAuxiliaryBoundaryPredicate
        (ExecutableLayout119 source domain)
        (executableHistoryBasis119 source domain fits index) := by
  intro workspaceIndex
  exact executableHistoryBasis119_workspace_zero source domain fits index workspaceIndex

theorem executableHistoryBasis119_correctedClockClean
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    historyClockBranchUncomputedStrongOutputPredicate
        (ExecutableLayout119 source domain)
        (executableHistoryBasis119 source domain fits index) := by
  constructor
  · exact executableHistoryBasis119_p15_auxiliary source domain fits index
  · exact historyTaylorAuxiliaryBoundaryPredicate_implies_historyClockCleanPredicate
      (ExecutableLayout119 source domain)
      (executableHistoryBasis119 source domain fits index)
      (executableHistoryBasis119_p15_auxiliary source domain fits index)

theorem executableQ10Placement_ancilla_mem119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (ancillaIndex : Fin (ExecutableQParameters119 source domain).ancillaWidth) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    evidence.placement.embedding.placement
        (wireToCanonicalFin (Wire.ancilla ancillaIndex)) ∈
      historyRegisterWires layout.generatorSignal ++
        historyRegisterWires (historyGeneratorWorkRegister layout) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  let coreIndex : Fin
      ((ExecutableQParameters119 source domain).ancillaWidth +
        (ExecutableQParameters119 source domain).systemWidth) :=
    wireToCanonicalFin (Wire.ancilla ancillaIndex)
  let ancillaWires := historyRegisterWires layout.generatorSignal ++
    historyRegisterWires (historyGeneratorWorkRegister layout)
  have sourceOrder := historyP15Q10Placement_sourceOrder
    (layout := layout) widths
  have sourceOrder' :
      List.ofFn evidence.placement.embedding.placement =
        ancillaWires ++ historyRegisterWires layout.data := by
    simpa [evidence, ancillaWires] using sourceOrder
  have ancillaLength : ancillaWires.length =
      (ExecutableQParameters119 source domain).ancillaWidth := by
    simp [ancillaWires, historyRegisterWires, widths.signal_eq, widths.work_eq]
  have coreLtAncilla : coreIndex.val <
      (ExecutableQParameters119 source domain).ancillaWidth := by
    exact ancillaIndex.isLt
  have coreLtPrefix : coreIndex.val < ancillaWires.length := by
    rw [ancillaLength]
    exact coreLtAncilla
  have atIndex := congrArg (fun wires => wires[coreIndex.val]?) sourceOrder'
  have someEqual :
      some (evidence.placement.embedding.placement coreIndex) =
        ancillaWires[coreIndex.val]? := by
    simpa only [List.getElem?_ofFn, coreIndex.isLt, dif_pos, Fin.eta,
      List.getElem?_append, coreLtPrefix, if_pos] using atIndex
  have getSome := someEqual.symm
  rw [List.getElem?_eq_some_iff] at getSome
  rcases getSome with ⟨elementFits, elementEqual⟩
  change evidence.placement.embedding.placement coreIndex ∈ ancillaWires
  rw [← elementEqual]
  exact List.getElem_mem elementFits

theorem executableQ10Placement_ancilla_zero119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (ancillaIndex : Fin (ExecutableQParameters119 source domain).ancillaWidth) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    executableHistoryBasis119 source domain fits index
      (evidence.placement.embedding.placement
        (wireToCanonicalFin (Wire.ancilla ancillaIndex))) = false := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  have member := executableQ10Placement_ancilla_mem119 source domain ancillaIndex
  rcases List.mem_append.mp member with signalMember | workMember
  · apply executableHistoryBasis119_apply_of_tail_mem source domain fits index
    exact List.mem_append_left _ (List.mem_append_left _ signalMember)
  · simp only [historyRegisterWires, List.mem_ofFn] at workMember
    rcases workMember with ⟨workIndex, workEqual⟩
    rw [← workEqual]
    exact executableHistoryBasis119_generatorWork_zero source domain fits index workIndex

theorem executableHistoryBasis119_q10CanonicalAllZero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    q10CanonicalCoreAllZeroInputPredicate (ExecutableQParameters119 source domain)
      (restrictToPlacedWires evidence.placement.embedding.placement
        (executableHistoryBasis119 source domain fits index)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  let restricted := restrictToPlacedWires evidence.placement.embedding.placement
    (executableHistoryBasis119 source domain fits index)
  let joint := coreBasisToJoint restricted
  let system : RegisterBasis (ExecutableQParameters119 source domain).systemWidth :=
    fun systemIndex => joint (Wire.system systemIndex)
  have jointEqual : joint = zeroAncillaJointBasis
      (ExecutableQParameters119 source domain) system := by
    funext wire
    cases wire with
    | ancilla ancillaIndex =>
        change executableHistoryBasis119 source domain fits index
          (evidence.placement.embedding.placement
            (wireToCanonicalFin (Wire.ancilla ancillaIndex))) = false
        exact executableQ10Placement_ancilla_zero119 source domain fits index
          ancillaIndex
    | system systemIndex =>
        rfl
  change q11AllZeroAncillaInputPredicate
    (ExecutableQParameters119 source domain) joint
  rw [jointEqual]
  exact q11AllZeroAncillaInputPredicate_zeroAncillaJointBasis
    (ExecutableQParameters119 source domain) system

theorem executableHistoryBasis119_p15FullCleanInput
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    historyP15FullCleanInputPredicate
        (layout := ExecutableLayout119 source domain)
        (p := source.qParameters)
        (ExecutableAdmissible119 source domain).placementWidths
        (executableHistoryBasis119 source domain fits index) := by
  unfold historyP15FullCleanInputPredicate historyP15WithQ10Input
    historyP15Q10PlacedInputPredicate externallyControlledPlacedInputPredicate
  constructor
  · exact executableHistoryBasis119_p15_auxiliary source domain fits index
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
      exact executableHistoryBasis119_apply_of_tail_mem source domain fits index
        _ (List.mem_append_right _ workspaceMember)
    · exact executableHistoryBasis119_q10CanonicalAllZero source domain fits index

end
end ExecutableHistoryHistoryCleanInput
