import QLean.History.Implementation.HistoryPipelineH2IdleEntry

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

/-- Fixing the physical selector branch does not identify two distinct logical
history indices.  This is the small injectivity fact needed to turn the exact
post-H2 basis action into an exhaustive clean logical support statement. -/
theorem correctedBranchHistoryBasis119_injective_index
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4) :
    Function.Injective
      (correctedBranchHistoryBasis119 source domain fits branch) := by
  intro left right equal
  apply executableHistoryBasis119_injective source domain fits
  funext wire
  let layout := ExecutableLayout119 source domain
  let selectorWires := historyRegisterWires layout.selector
  let dataWires := historyRegisterWires layout.data
  let clockWires := historyRegisterWires layout.clock
  let orderWires := historyRegisterWires layout.order
  let generatorWires := historyRegisterWires layout.generatorSignal
  let reservedWires := [layout.coefficientSignal, layout.orderBoundarySignal,
    layout.projectorSignal, layout.clockBoundarySignal]
  let workspaceWires := historyRegisterWires layout.workspace
  have normalized :
      (selectorWires ++ (dataWires ++ (clockWires ++ (orderWires ++
        (generatorWires ++ (reservedWires ++ workspaceWires)))))).Nodup := by
    simpa [layout, selectorWires, dataWires, clockWires, orderWires,
      generatorWires, reservedWires, workspaceWires, List.append_assoc] using
      layout.allWiresNodup
  have selectorSplit := List.nodup_append.mp normalized
  by_cases selectorMember : wire ∈ selectorWires
  · have outsideData : ∀ dataIndex, layout.data.wire dataIndex ≠ wire := by
      intro dataIndex wireEq
      apply selectorSplit.2.2 wire selectorMember
        (layout.data.wire dataIndex)
      · exact List.mem_append_left _
          (List.mem_ofFn.mpr ⟨dataIndex, rfl⟩)
      · exact wireEq.symm
    have tailNormalized :
        (dataWires ++ (clockWires ++ (orderWires ++
          (generatorWires ++ (reservedWires ++ workspaceWires))))).Nodup :=
      selectorSplit.2.1
    have dataSplit := List.nodup_append.mp tailNormalized
    have outsideClock : ∀ clockIndex, layout.clock.wire clockIndex ≠ wire := by
      intro clockIndex wireEq
      apply selectorSplit.2.2 wire selectorMember
        (layout.clock.wire clockIndex)
      · exact List.mem_append_right dataWires
          (List.mem_append_left _ (List.mem_ofFn.mpr ⟨clockIndex, rfl⟩))
      · exact wireEq.symm
    have outsideOrder : ∀ orderIndex, layout.order.wire orderIndex ≠ wire := by
      intro orderIndex wireEq
      apply selectorSplit.2.2 wire selectorMember
        (layout.order.wire orderIndex)
      · exact List.mem_append_right dataWires
          (List.mem_append_right clockWires
            (List.mem_append_left _ (List.mem_ofFn.mpr ⟨orderIndex, rfl⟩)))
      · exact wireEq.symm
    unfold executableHistoryBasis119
    rw [writeRegisterBits_apply_outside _ _ _ _ outsideData,
      writeRegisterBits_apply_outside _ _ _ _ outsideClock,
      writeRegisterBits_apply_outside _ _ _ _ outsideOrder]
    rw [writeRegisterBits_apply_outside _ _ _ _ outsideData,
      writeRegisterBits_apply_outside _ _ _ _ outsideClock,
      writeRegisterBits_apply_outside _ _ _ _ outsideOrder]
  · have leftOutside := correctedBranchHistoryBasis119_apply_of_not_selector
      source domain fits branch left wire selectorMember
    have rightOutside := correctedBranchHistoryBasis119_apply_of_not_selector
      source domain fits branch right wire selectorMember
    exact leftOutside.symm.trans ((congrFun equal wire).trans rightOutside)

/-- The H2 entry-predicate prefix never touches a wire of the placed Q10
register. -/
theorem h2BeforeQ119_restrict_q10_eq_input119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let widths := (ExecutableAdmissible119 source domain).placementWidths
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    let input := correctedBranchHistoryBasis119 source domain fits branch index
    restrictToPlacedWires evidence.placement.embedding.placement
        (h2BeforeQ119 layout input) =
      restrictToPlacedWires evidence.placement.embedding.placement input := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  let input := correctedBranchHistoryBasis119 source domain fits branch index
  funext coreIndex
  change h2BeforeQ119 layout input
      (evidence.placement.embedding.placement coreIndex) =
    input (evidence.placement.embedding.placement coreIndex)
  have sourceOrder := historyP15Q10Placement_sourceOrder
    (layout := layout) widths
  have placedMember : evidence.placement.embedding.placement coreIndex ∈
      historyRegisterWires layout.generatorSignal ++
        historyRegisterWires (historyGeneratorWorkRegister layout) ++
        historyRegisterWires layout.data := by
    rw [← sourceOrder]
    exact List.mem_ofFn.mpr ⟨coreIndex, rfl⟩
  apply h2BeforeQ119_apply_of_not_mem_live
  rcases List.mem_append.mp placedMember with ancillaMember | dataMember
  · rcases List.mem_append.mp ancillaMember with signalMember | workMember
    · apply historyPrefix_wire_not_mem_beforeGeneratorLiveWires119 layout
      simp [List.mem_append, signalMember]
    · simp only [historyRegisterWires, List.mem_ofFn] at workMember
      rcases workMember with ⟨workIndex, workEqual⟩
      rw [← workEqual]
      exact historyGeneratorWorkRegister_wire_not_mem_live119 layout workIndex
  · apply historyPrefix_wire_not_mem_beforeGeneratorLiveWires119 layout
    simp [List.mem_append, dataMember]

/-- A two-stage product with disjoint write supports has at most the canonical
middle basis selected by its placed and outside restrictions. -/
theorem two_stage_product_entry_eq_canonical_middle119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (postSupport : Finset (Fin targetQubits))
    (post q10 : VerifiedCircuitCore.Operator (QubitBasis targetQubits))
    (postLocal : OperatorPreservesOutside postSupport post)
    (postDisjoint : ∀ wire, wire ∈ postSupport → ∀ source,
      wire ≠ placement source)
    (q10Local : OperatorPreservesOutside
      (Finset.univ.image placement) q10)
    (row input expected : QubitBasis targetQubits)
    (expectedPlaced : restrictToPlacedWires placement expected =
      restrictToPlacedWires placement row)
    (expectedOutside : restrictToOutsideWires placement expected =
      restrictToOutsideWires placement input) :
    (post * q10) row input = post row expected * q10 expected input := by
  rw [Matrix.mul_apply]
  change (∑ middle, post row middle * q10 middle input) = _
  rw [Fintype.sum_eq_single expected]
  intro middle middleNe
  by_cases postZero : post row middle = 0
  · rw [postZero]
    simp
  by_cases q10Zero : q10 middle input = 0
  · rw [q10Zero]
    simp
  have middleEq : middle = expected := by
    apply (fullBasis_eq_iff_restrictions_eq placement _ _).2
    constructor
    · funext source
      have middleBit := postLocal row middle postZero
        (placement source) (by
          intro member
          exact (postDisjoint _ member source) rfl)
      exact middleBit.symm.trans
        (congrFun expectedPlaced source).symm
    · funext outside
      have middleBit := q10Local middle input q10Zero outside.1 (by
        intro member
        rcases Finset.mem_image.mp member with ⟨placed, _, equal⟩
        exact outside.2 placed equal)
      exact middleBit.trans (congrFun expectedOutside outside).symm
  exact (middleNe middleEq).elim

/-- Exact clean logical row support of the active-clock H2 post word. -/
theorem h2PostOperator_active_logical_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (labelTaylor : inputIndex.state.label.val <
      source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let replaced := replaceConfiguration119 source inputIndex
      outputIndex.state.configuration
    let expected := h2BeforeQ119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h2SelectedBranch119 replaced)
    let raised := raiseHistoryLabel119 source inputIndex
      outputIndex.state.configuration labelTaylor
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    h2PostOperator119 layout
        (fun coefficientIndex => correctedTaylorCoefficientAngle119
          source.toCommonSource119 coefficientIndex.val)
        compiledIdleCoefficientAngle119 row expected =
      if outputIndex = raised then
        (((-(omegaH119 source.toCommonSource119) /
          ((inputIndex.state.label.val + 1 : Nat) : Real)) : Real) : Complex)
      else 0 := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let replaced := replaceConfiguration119 source inputIndex
    outputIndex.state.configuration
  let raised := raiseHistoryLabel119 source inputIndex
    outputIndex.state.configuration labelTaylor
  let expected := h2BeforeQ119 layout
    (correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 replaced)
  let row := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 outputIndex
  let raisedBasis := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 raised
  have action := applyOperator_h2PostOperator_active_taylor119 source domain fits
    inputIndex outputIndex.state.configuration clockActive labelTaylor
  have rowSignalFalse : row layout.coefficientSignal = false := by
    exact correctedBranchHistoryBasis119_coefficientSignal_false119 source
      domain fits h2SelectedBranch119 outputIndex
  have rowNeDirty : row ≠
      replaceQubitWire raisedBasis layout.coefficientSignal true := by
    intro equal
    have atSignal := congrFun equal layout.coefficientSignal
    simp [replaceQubitWire, rowSignalFalse] at atSignal
  have basisEqIff : row = raisedBasis ↔ outputIndex = raised := by
    constructor
    · intro equal
      exact correctedBranchHistoryBasis119_injective_index source domain fits
        h2SelectedBranch119 equal
    · intro equal
      exact congrArg
        (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119)
        equal
  have entryAction := congrFun action row
  simp only [VerifiedCircuitCore.applyOperator_basisKet] at entryAction
  rw [entryAction]
  dsimp only [row, raisedBasis, raised] at rowSignalFalse rowNeDirty basisEqIff ⊢
  simp only [Pi.add_apply, Pi.smul_apply, VerifiedCircuitCore.basisKet,
    VerifiedMath.Basis.vector_apply, smul_eq_mul]
  by_cases indexEq : outputIndex = raised
  · rw [if_pos indexEq]
    have basisEq := basisEqIff.2 indexEq
    rw [if_pos basisEq, if_neg rowNeDirty]
    simp only [mul_one, mul_zero, add_zero]
    exact_mod_cast
      correctedTaylorCoefficient_clean_amplitude119
        source.toCommonSource119 inputIndex.state.label.val
  · rw [if_neg indexEq]
    have basisNe := fun equal => indexEq (basisEqIff.1 equal)
    rw [if_neg basisNe, if_neg rowNeDirty]
    simp only [mul_zero, zero_add]

/-- The active H2 `post * Q10` block has exactly the mathematical Taylor-row
support; all other clean logical rows are zero. -/
theorem h2PostQ10_active_logical_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (labelTaylor : inputIndex.state.label.val <
      source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let input := h2BeforeQ119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h2SelectedBranch119 inputIndex)
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    let raised := raiseHistoryLabel119 source inputIndex
      outputIndex.state.configuration labelTaylor
    (h2PostOperator119 layout
        (fun coefficientIndex => correctedTaylorCoefficientAngle119
          source.toCommonSource119 coefficientIndex.val)
        compiledIdleCoefficientAngle119 *
      h2ControlledQ10CleanOperator
        (ExecutableH2Q10Specification119 source domain)) row input =
      (if outputIndex = raised then
        (((-(omegaH119 source.toCommonSource119) /
          ((inputIndex.state.label.val + 1 : Nat) : Real)) : Real) : Complex)
       else 0) *
        ((HistoryBlockEncoding.QModel.configurationQMatrix
            (executableQConfiguration119 source domain
              outputIndex.state.configuration)
            (executableQConfiguration119 source domain
              inputIndex.state.configuration) : Complex) /
          ((3 * (ExecutableH2Q10Specification119 source domain).p.K : Nat) :
            Complex)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  let placement := evidence.placement.embedding.placement
  let post := h2PostOperator119 layout
    (fun coefficientIndex => correctedTaylorCoefficientAngle119
      source.toCommonSource119 coefficientIndex.val)
    compiledIdleCoefficientAngle119
  let q10 := h2ControlledQ10CleanOperator
    (ExecutableH2Q10Specification119 source domain)
  let input := h2BeforeQ119 layout
    (correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex)
  let replaced := replaceConfiguration119 source inputIndex
    outputIndex.state.configuration
  let expected := h2BeforeQ119 layout
    (correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 replaced)
  let row := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 outputIndex
  have expectedPlaced : restrictToPlacedWires placement expected =
      restrictToPlacedWires placement row := by
    calc
      restrictToPlacedWires placement expected =
          canonicalCoreSuccessBasis119 (ExecutableQParameters119 source domain)
            (executableQConfiguration119 source domain
              outputIndex.state.configuration) := by
        exact h2BeforeQ119_q10RestrictedBasis_eq_success119 source domain fits
          h2SelectedBranch119 replaced
      _ = restrictToPlacedWires placement
          (h2BeforeQ119 layout row) := by
        symm
        exact h2BeforeQ119_q10RestrictedBasis_eq_success119 source domain fits
          h2SelectedBranch119 outputIndex
      _ = restrictToPlacedWires placement row :=
        h2BeforeQ119_restrict_q10_eq_input119 source domain fits
          h2SelectedBranch119 outputIndex
  have expectedOutside : restrictToOutsideWires placement expected =
      restrictToOutsideWires placement input := by
    exact h2BeforeQ119_replaceConfiguration_outside source domain fits
      h2SelectedBranch119 inputIndex outputIndex.state.configuration
  rw [two_stage_product_entry_eq_canonical_middle119 placement
    (h2PostWriteSupport119 layout) post q10
    (h2PostOperator_local119 layout
      (fun coefficientIndex => correctedTaylorCoefficientAngle119
        source.toCommonSource119 coefficientIndex.val)
      compiledIdleCoefficientAngle119)
    (h2PostWriteSupport119_ne_placement widths)
    (executableH2Q10_operator_local119 source domain)
    row input expected expectedPlaced expectedOutside]
  dsimp only [post, q10, row, expected, replaced, input]
  rw [h2PostOperator_active_logical_entry119 source domain fits inputIndex
    outputIndex clockActive labelTaylor]
  rw [executableH2Q10_selected_logical_entry119 source domain fits inputIndex
    clockActive outputIndex.state.configuration]

/-- Exhaustive active-clock clean logical entry of the actual H2 target. -/
theorem executableH2_active_logical_clean_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (labelTaylor : inputIndex.state.label.val <
      source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    let raised := raiseHistoryLabel119 source inputIndex
      outputIndex.state.configuration labelTaylor
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        row input =
      (if outputIndex = raised then
        (((-(omegaH119 source.toCommonSource119) /
          ((inputIndex.state.label.val + 1 : Nat) : Real)) : Real) : Complex)
       else 0) *
        ((HistoryBlockEncoding.QModel.configurationQMatrix
            (executableQConfiguration119 source domain
              outputIndex.state.configuration)
            (executableQConfiguration119 source domain
              inputIndex.state.configuration) : Complex) /
          ((3 * (ExecutableH2Q10Specification119 source domain).p.K : Nat) :
            Complex)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let clean := ScientificWidthGenericContract.correctedCleanEvidence259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let angles : Fin
      (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic).taylorOrder →
        VerifiedCircuitCore.AngleExpr :=
    fun coefficientIndex => correctedTaylorCoefficientAngle119
      source.toCommonSource119 coefficientIndex.val
  let pre := operatorSequence
    [historyTaylorSelectorEqualityOperator layout,
     historyTaylorTimeComparisonOperator layout,
     historyTaylorIdleEndComparisonOperator layout,
     historyTaylorActiveConjunctionOperator layout]
  let q10 := h2ControlledQ10CleanOperator
    (historyP15ControlledQ10UnderstandingSpecification
      (ExecutableH2Q10Specification119 source domain).p layout widths)
  let post := h2PostOperator119 layout angles compiledIdleCoefficientAngle119
  let input := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 inputIndex
  let row := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 outputIndex
  have operatorEq :
      h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout clean widths
            angles compiledIdleCoefficientAngle119) =
        post * (q10 * pre) :=
    h2TaylorCleanOperator_historyP15_decompose119 layout clean widths
      angles compiledIdleCoefficientAngle119
  calc
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout clean widths angles
          compiledIdleCoefficientAngle119) row input =
      VerifiedCircuitCore.applyOperator
        (h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout clean widths
            angles compiledIdleCoefficientAngle119))
        (VerifiedCircuitCore.basisKet input) row := by
          symm
          exact VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = VerifiedCircuitCore.applyOperator (post * (q10 * pre))
        (VerifiedCircuitCore.basisKet input) row := by rw [operatorEq]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator q10
          (VerifiedCircuitCore.applyOperator pre
            (VerifiedCircuitCore.basisKet input))) row := by
      rw [VerifiedCircuitCore.applyOperator_mul,
        VerifiedCircuitCore.applyOperator_mul]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator q10
          (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input))) row := by
      rw [h2BeforeOperators_apply_basisKet119]
    _ = VerifiedCircuitCore.applyOperator (post * q10)
        (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input)) row := by
      rw [VerifiedCircuitCore.applyOperator_mul]
    _ = (post * q10) row (h2BeforeQ119 layout input) :=
      VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = _ := h2PostQ10_active_logical_entry119 source domain fits inputIndex
      outputIndex clockActive labelTaylor

/-- The actual H2 clean logical block equals `L1` for every active-clock input
strictly below the Taylor boundary, including all zero rows. -/
theorem executableH2_active_logical_entry_eq_L1_119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (labelTaylor : inputIndex.state.label.val <
      source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        row input =
      (HistoryBlockEncoding.HistorySpec.L1 source.historyParameters
        (commonModelQ119 source.toCommonSource119) outputIndex inputIndex :
          Complex) := by
  dsimp only
  let raised := raiseHistoryLabel119 source inputIndex
    outputIndex.state.configuration labelTaylor
  by_cases indexEq : outputIndex = raised
  · have rowEq := congrArg
      (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119)
      indexEq
    rw [rowEq]
    rw [executableH2_active_taylor_entry_eq_L1_119 source domain fits
      inputIndex outputIndex.state.configuration clockActive labelTaylor]
    rw [indexEq]
    have raisedIdem : raiseHistoryLabel119 source inputIndex
        raised.state.configuration labelTaylor = raised := by
      rfl
    rw [raisedIdem]
  · rw [executableH2_active_logical_clean_entry119 source domain fits
      inputIndex outputIndex clockActive labelTaylor]
    rw [if_neg indexEq]
    simp only [zero_mul]
    have l1Zero : HistoryBlockEncoding.HistorySpec.L1 source.historyParameters
        (commonModelQ119 source.toCommonSource119) outputIndex inputIndex = 0 := by
      unfold HistoryBlockEncoding.HistorySpec.L1
      by_cases clockEq : outputIndex.clock = inputIndex.clock
      · rw [if_pos clockEq]
        have outputActive : outputIndex.clock.val <
            source.historyParameters.physicalClocks := by
          simpa [clockEq] using clockActive
        rw [if_pos outputActive]
        unfold HistoryBlockEncoding.HistorySpec.deltaTay
        by_cases labelEq : outputIndex.state.label.val =
            inputIndex.state.label.val + 1
        · exfalso
          apply indexEq
          apply oldHistoryIndex_ext119
          · simpa [raised, raiseHistoryLabel119] using clockEq
          · apply labelState_ext119
            · apply Fin.ext
              simpa [raised, raiseHistoryLabel119] using labelEq
            · rfl
        · rw [if_neg (by
            intro conjunction
            exact labelEq conjunction.1)]
      · rw [if_neg clockEq]
    rw [l1Zero]
    norm_num

end
end ExecutableHistoryExecutableHistory
