import QLean.History.Implementation.HistoryPipelineH3IdleNonfinal

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
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

private theorem littleEndianListNat_zero_mem_false119
    (bits : List Bool)
    (valueZero : ClassicalReversibleStage.littleEndianListNat bits = 0) :
    ∀ bit ∈ bits, bit = false := by
  induction bits with
  | nil => simp
  | cons head tail inductionHypothesis =>
      intro bit member
      simp only [ClassicalReversibleStage.littleEndianListNat] at valueZero
      rcases List.mem_cons.mp member with equal | tailMember
      · subst bit
        cases head <;> simp_all
      · apply inductionHypothesis
        · cases head <;> simp_all
        · exact tailMember

private theorem h3BeforeUniform119_projectorSignal_false119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    h3BeforeUniform119 layout logical layout.projectorSignal = false := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  have activeNe : historyActiveWire layout ≠ layout.projectorSignal := by
    unfold historyActiveWire
    exact h3WorkspaceWire_ne_projector119 layout _
  have idleEndNe : historyLessThanIdleEndWire layout ≠
      layout.projectorSignal := by
    unfold historyLessThanIdleEndWire
    exact h3WorkspaceWire_ne_projector119 layout _
  have timeNe : historyLessThanTimeWire layout ≠ layout.projectorSignal := by
    unfold historyLessThanTimeWire
    exact h3WorkspaceWire_ne_projector119 layout _
  have branchNe : historyBranchWire layout ≠ layout.projectorSignal := by
    rcases List.mem_ofFn.mp (historyBranchWire_mem_workspace layout) with
      ⟨workspaceIndex, equal⟩
    rw [← equal]
    exact h3WorkspaceWire_ne_projector119 layout workspaceIndex
  unfold h3BeforeUniform119 historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
    h3AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
    h3AfterTime119 historyTaylorTimeComparisonBasisAction
    h3AfterSelector119
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [xorWire_apply_other _ _ activeNe.symm,
    xorWire_apply_other _ _ idleEndNe.symm,
    xorWire_apply_other _ _ timeNe.symm,
    xorWire_apply_other _ _ branchNe.symm]
  exact correctedBranchHistoryBasis119_projectorSignal_false119
    source domain fits h3SelectedBranch119 index

private theorem h3OutsideEqual_projector119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryOrderUniformExternalControlEvidence layout)
    (output input : QubitBasis qubits)
    (outsideEqual :
      restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout evidence).placement
          output =
        restrictToOutsideWires
          (historyOrderUniformExternalControlLayout layout evidence).placement
          input) :
    output layout.projectorSignal = input layout.projectorSignal := by
  let controlled := historyOrderUniformExternalControlLayout layout evidence
  have orderNeProjector
      (orderIndex : Fin (historyOrderWidth parameters.taylorOrder)) :
      layout.order.wire orderIndex ≠ layout.projectorSignal := by
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
      simpa [selectorWires, dataWires, clockWires, orderWires, generatorWires,
        reservedWires, workspaceWires, List.append_assoc] using
          layout.allWiresNodup
    have selectorSplit := List.nodup_append.mp normalized
    have dataSplit := List.nodup_append.mp selectorSplit.2.1
    have clockSplit := List.nodup_append.mp dataSplit.2.1
    have orderSplit := List.nodup_append.mp clockSplit.2.1
    exact orderSplit.2.2 _ (List.mem_ofFn.mpr ⟨orderIndex, rfl⟩) _
      (List.mem_append_right _
        (List.mem_append_left _ (by simp [reservedWires])))
  let outside : OutsideWire controlled.placement :=
    ⟨layout.projectorSignal, by
      intro orderIndex
      change layout.order.wire orderIndex ≠ layout.projectorSignal
      exact orderNeProjector orderIndex⟩
  have point := congrFun outsideEqual outside
  change output outside.val = input outside.val at point
  simpa [outside] using point

/-- If an active H3 column reaches a clean logical row with nonzero amplitude,
the uniform-inverse middle basis is forced to be the unique zero-order basis. -/
theorem h3ActiveTailOperator119_middle_unique_of_logical_row
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index outputIndex : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (middle : QubitBasis (ExecutableRaw119 source).history.qubits)
    (uniformNonzero :
      (historyOrderUniformPreparationInverseExactComponent
        (ExecutableLayout119 source domain)
        (ExecutableClockEvidence119 source domain).uniformExternalControl
      ).target middle
        (h3BeforeUniform119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits
            h3SelectedBranch119 index)) ≠ 0)
    (tailNonzero :
      h3ActiveTailOperator119 source domain
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          outputIndex) middle ≠ 0) :
    let layout := ExecutableLayout119 source domain
    let before := h3BeforeUniform119 layout
      (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
        index)
    middle = h3ZeroOrder119 layout before := by
  dsimp only at tailNonzero ⊢
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).uniformExternalControl
  let controlled := historyOrderUniformExternalControlLayout layout evidence
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let row := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 outputIndex
  let before := h3BeforeUniform119 layout logical
  let expected := h3ZeroOrder119 layout before
  let action := h3ActiveTailBasisAction119 source domain middle
  have outsideMiddle := h3UniformInverse119_nonzero_outside_eq
    source domain fits index middle uniformNonzero
  have actionMiddle := h3ActiveTailOperator119_apply_basisKet_of_uniform_outside
    source domain fits index clockActive middle outsideMiddle
  have rowEq : row = action := by
    by_contra unequal
    have point := congrFun actionMiddle row
    have zero : h3ActiveTailOperator119 source domain row middle = 0 := by
      simpa [VerifiedCircuitCore.applyOperator_basisKet,
        VerifiedCircuitCore.basisKet_apply, action, unequal] using point
    exact tailNonzero zero
  have rowProjector : row layout.projectorSignal = false :=
    correctedBranchHistoryBasis119_projectorSignal_false119
      source domain fits h3SelectedBranch119 outputIndex
  have actionProjector : action layout.projectorSignal = false := by
    rw [← rowEq]
    exact rowProjector
  have beforeProjector : before layout.projectorSignal = false :=
    h3BeforeUniform119_projectorSignal_false119 source domain fits index
  have middleProjector : middle layout.projectorSignal = false := by
    exact (h3OutsideEqual_projector119 layout evidence middle before
      outsideMiddle).trans beforeProjector
  have cleanValues := h3UniformMiddle119_active_clean_values
    source domain fits index clockActive middle outsideMiddle
  have middleBranch : middle (historyBranchWire layout) = true := cleanValues.1
  have projectorFormula := h3ActiveTailBasisAction119_projectorSignal
    source domain middle
  change action layout.projectorSignal = _ at projectorFormula
  have orderZero :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) 0 middle = true := by
    by_contra notTrue
    have isFalse :
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order) 0 middle = false :=
      Bool.eq_false_of_not_eq_true notTrue
    rw [projectorFormula, middleProjector, middleBranch, isFalse] at actionProjector
    contradiction
  have listZero :
      ClassicalReversibleStage.littleEndianListNat
          (ClassicalReversibleStage.readWires
            (historyRegisterWires layout.order) middle) = 0 := by
    rw [ClassicalReversibleStage.littleEndianRegisterEqualsNat_eq_decide
      (historyRegisterWires layout.order) 0 middle (by positivity)] at orderZero
    exact of_decide_eq_true orderZero
  have middleOrderZero
      (orderIndex : Fin (historyOrderWidth
        source.historyParameters.taylorOrder)) :
      middle (layout.order.wire orderIndex) = false := by
    apply littleEndianListNat_zero_mem_false119 _ listZero
    simp only [ClassicalReversibleStage.readWires, historyRegisterWires,
      List.map_ofFn]
    exact List.mem_ofFn.mpr ⟨orderIndex, rfl⟩
  have placedEqual : restrictToPlacedWires controlled.placement middle =
      restrictToPlacedWires controlled.placement expected := by
    funext orderIndex
    change middle (layout.order.wire orderIndex) =
      expected (layout.order.wire orderIndex)
    rw [middleOrderZero]
    unfold expected h3ZeroOrder119
    rw [writeRegisterValue_apply_wire]
    simp
  have outsideExpected := h3ZeroOrder119_uniform_outside_eq
    source domain fits index
  apply (fullBasis_eq_iff_restrictions_eq controlled.placement
    middle expected).2
  exact ⟨placedEqual, outsideMiddle.trans outsideExpected.symm⟩

/-- Exact active-clock H3 entry on every clean logical output row. -/
theorem repairedH3RecordedTarget119_active_all_rows_physical
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (clockNext : inputIndex.clock.val + 1 <
      source.historyParameters.clockEnd) :
    repairedH3RecordedTarget119 source domain
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          outputIndex)
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          inputIndex) =
      if outputIndex = h3ActiveOutputIndex119 source inputIndex clockNext then
        if inputIndex.state.label.val ≤ source.historyParameters.taylorOrder then
          -(((1 / Real.sqrt
            (source.historyParameters.taylorOrder + 1) : Real) : Complex))
        else 0
      else 0 := by
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 inputIndex
  let row := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 outputIndex
  let before := h3BeforeUniform119 layout logical
  let expected := h3ZeroOrder119 layout before
  let expectedRow := h3ActiveTailBasisAction119 source domain expected
  let uniform := (historyOrderUniformPreparationInverseExactComponent layout
    (ExecutableClockEvidence119 source domain).uniformExternalControl).target
  let tail := h3ActiveTailOperator119 source domain
  have targetEq := repairedH3RecordedTarget119_decompose_active source domain
  have prefixAction := h3ActivePrefixOperator119_apply_basisKet
    source domain fits inputIndex
  have actionExpected := h3ActiveTailOperator119_apply_basisKet_of_uniform_outside
    source domain fits inputIndex clockActive expected
      (h3ZeroOrder119_uniform_outside_eq source domain fits inputIndex)
  have tailExpected : tail row expected =
      if row = expectedRow then (-1 : Complex) else 0 := by
    have point := congrFun actionExpected row
    by_cases equal : row = expectedRow
    · subst row
      simpa [VerifiedCircuitCore.applyOperator_basisKet,
        VerifiedCircuitCore.basisKet_apply, expectedRow] using point
    · simpa [VerifiedCircuitCore.applyOperator_basisKet,
        VerifiedCircuitCore.basisKet_apply, expectedRow, equal] using point
  have uniformExpected : uniform expected before =
      if inputIndex.state.label.val ≤ source.historyParameters.taylorOrder then
        (((1 / Real.sqrt
          (source.historyParameters.taylorOrder + 1) : Real) : Complex))
      else 0 :=
    h3UniformInverse_zero_order_entry119
      source domain fits inputIndex clockActive
  have expectedRowEq : expectedRow =
      correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
        (h3ActiveOutputIndex119 source inputIndex clockNext) :=
    h3ActiveTailBasisAction119_expected_eq_logical
      source domain fits inputIndex clockNext
  calc
    repairedH3RecordedTarget119 source domain row logical =
        VerifiedCircuitCore.applyOperator
          (repairedH3RecordedTarget119 source domain)
          (VerifiedCircuitCore.basisKet logical) row := by
      symm
      exact VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = VerifiedCircuitCore.applyOperator (tail * uniform)
          (VerifiedCircuitCore.applyOperator
            (h3ActivePrefixOperator119 source domain)
            (VerifiedCircuitCore.basisKet logical)) row := by
      rw [targetEq, VerifiedCircuitCore.applyOperator_mul]
    _ = VerifiedCircuitCore.applyOperator (tail * uniform)
          (VerifiedCircuitCore.basisKet before) row := by rw [prefixAction]
    _ = (tail * uniform) row before := by
      exact VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = ∑ middle, tail row middle * uniform middle before := by
      rw [Matrix.mul_apply]
    _ = tail row expected * uniform expected before := by
      rw [Fintype.sum_eq_single expected]
      intro middle middleNe
      by_cases uniformZero : uniform middle before = 0
      · rw [uniformZero]
        simp
      by_cases tailZero : tail row middle = 0
      · rw [tailZero]
        simp
      have middleEq :=
        h3ActiveTailOperator119_middle_unique_of_logical_row
          source domain fits inputIndex outputIndex clockActive middle
            uniformZero tailZero
      exact (middleNe middleEq).elim
    _ = if outputIndex = h3ActiveOutputIndex119 source inputIndex clockNext then
          if inputIndex.state.label.val ≤
              source.historyParameters.taylorOrder then
            -(((1 / Real.sqrt
              (source.historyParameters.taylorOrder + 1) : Real) : Complex))
          else 0
        else 0 := by
      rw [tailExpected, uniformExpected, expectedRowEq]
      have embeddingInjective :=
        correctedBranchHistoryBasis119_injective_index source domain fits
          h3SelectedBranch119
      by_cases equal : outputIndex =
          h3ActiveOutputIndex119 source inputIndex clockNext
      · subst outputIndex
        simp [row]
      · have rowNe : row ≠ correctedBranchHistoryBasis119 source domain fits
            h3SelectedBranch119
            (h3ActiveOutputIndex119 source inputIndex clockNext) := by
          intro rowEqual
          exact equal (embeddingInjective rowEqual)
        simp [row, rowNe, equal]

end
end ExecutableHistoryExecutableHistory
