import QLean.History.Implementation.HistoryPipelineH3BranchIdentity

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

theorem correctedBranchHistoryBasis119_read_clock
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    (ExecutableLayout119 source domain).clock.read
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      clockBits119 source fits index := by
  funext bit
  change correctedBranchHistoryBasis119 source domain fits branch index
      ((ExecutableLayout119 source domain).clock.wire bit) = _
  rw [correctedBranchHistoryBasis119_apply_of_not_selector]
  · exact congrFun (executableHistoryBasis119_read_clock source domain fits index) bit
  · intro member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨selectorIndex, equal⟩
    have normalized :
        (historyRegisterWires (ExecutableLayout119 source domain).selector ++
          (historyRegisterWires (ExecutableLayout119 source domain).data ++
          (historyRegisterWires (ExecutableLayout119 source domain).clock ++
          (historyRegisterWires (ExecutableLayout119 source domain).order ++
          (historyRegisterWires (ExecutableLayout119 source domain).generatorSignal ++
          ([(ExecutableLayout119 source domain).coefficientSignal,
            (ExecutableLayout119 source domain).orderBoundarySignal,
            (ExecutableLayout119 source domain).projectorSignal,
            (ExecutableLayout119 source domain).clockBoundarySignal] ++
          historyRegisterWires (ExecutableLayout119 source domain).workspace)))))).Nodup := by
      simpa [List.append_assoc] using
        (ExecutableLayout119 source domain).allWiresNodup
    have separated := (List.nodup_append.mp normalized).2.2
    apply separated
      ((ExecutableLayout119 source domain).selector.wire selectorIndex)
      (List.mem_ofFn.mpr ⟨selectorIndex, rfl⟩)
      ((ExecutableLayout119 source domain).clock.wire bit)
    · simp [historyRegisterWires]
    · exact equal

theorem correctedBranchHistoryBasis119_read_order
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    (ExecutableLayout119 source domain).order.read
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      orderBits119 source fits index := by
  funext bit
  change correctedBranchHistoryBasis119 source domain fits branch index
      ((ExecutableLayout119 source domain).order.wire bit) = _
  rw [correctedBranchHistoryBasis119_apply_of_not_selector]
  · exact congrFun (executableHistoryBasis119_read_order source domain fits index) bit
  · intro member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨selectorIndex, equal⟩
    have normalized :
        (historyRegisterWires (ExecutableLayout119 source domain).selector ++
          (historyRegisterWires (ExecutableLayout119 source domain).data ++
          (historyRegisterWires (ExecutableLayout119 source domain).clock ++
          (historyRegisterWires (ExecutableLayout119 source domain).order ++
          (historyRegisterWires (ExecutableLayout119 source domain).generatorSignal ++
          ([(ExecutableLayout119 source domain).coefficientSignal,
            (ExecutableLayout119 source domain).orderBoundarySignal,
            (ExecutableLayout119 source domain).projectorSignal,
            (ExecutableLayout119 source domain).clockBoundarySignal] ++
          historyRegisterWires (ExecutableLayout119 source domain).workspace)))))).Nodup := by
      simpa [List.append_assoc] using
        (ExecutableLayout119 source domain).allWiresNodup
    have separated := (List.nodup_append.mp normalized).2.2
    apply separated
      ((ExecutableLayout119 source domain).selector.wire selectorIndex)
      (List.mem_ofFn.mpr ⟨selectorIndex, rfl⟩)
      ((ExecutableLayout119 source domain).order.wire bit)
    · simp [historyRegisterWires]
    · exact equal

theorem correctedBranchHistoryBasis119_clockLessThanTime
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    historyTaylorClockLessThanTimeValue
        (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      decide (index.clock.val < source.historyParameters.physicalClocks) := by
  let width := historyClockWidth source.historyParameters.physicalClocks
    source.historyParameters.taylorOrder
    (source.historyBlocks *
      historyIdleBlockSize source.historyParameters.taylorOrder - 1)
  have timeBound : source.historyParameters.physicalClocks < 2 ^ width := by
    apply lt_of_lt_of_le source.historyWellFormed.2.2.2.2
    exact le_of_lt fits.clock_fits
  have constantBits :
      (fun bit : Fin width =>
        source.historyParameters.physicalClocks.testBit bit.val) =
      qubitBasisOfLittleEndianIndex
        (⟨source.historyParameters.physicalClocks, timeBound⟩ : Fin (2 ^ width)) := by
    funext bit
    rfl
  unfold historyTaylorClockLessThanTimeValue
  rw [unsignedLessThanBits_eq_decide_lt]
  change decide
    (qubitBasisLittleEndianIndex width
        ((ExecutableLayout119 source domain).clock.read
          (correctedBranchHistoryBasis119 source domain fits branch index)) <
      qubitBasisLittleEndianIndex width
        (fun bit : Fin width =>
          source.historyParameters.physicalClocks.testBit bit.val)) = _
  rw [correctedBranchHistoryBasis119_read_clock, constantBits]
  simp only [clockBits119, qubitBasisLittleEndianIndex_basis]

theorem littleEndianListNat_ofFn119 {width : Nat}
    (basis : QubitBasis width) :
    ClassicalReversibleStage.littleEndianListNat (List.ofFn basis) =
      qubitBasisLittleEndianIndex width basis := by
  induction width with
  | zero => rfl
  | succ width inductionHypothesis =>
      rw [List.ofFn_succ]
      simp only [ClassicalReversibleStage.littleEndianListNat,
        qubitBasisLittleEndianIndex]
      rw [inductionHypothesis (fun wire => basis wire.succ)]
      cases basis 0 <;> rfl

theorem correctedBranchHistoryBasis119_order_value
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    ClassicalReversibleStage.littleEndianListNat
        (ClassicalReversibleStage.readWires
          (historyRegisterWires (ExecutableLayout119 source domain).order)
          (correctedBranchHistoryBasis119 source domain fits branch index)) =
      index.state.label.val := by
  simp only [ClassicalReversibleStage.readWires, historyRegisterWires,
    List.map_ofFn]
  change ClassicalReversibleStage.littleEndianListNat
      (List.ofFn ((ExecutableLayout119 source domain).order.read
        (correctedBranchHistoryBasis119 source domain fits branch index))) = _
  rw [correctedBranchHistoryBasis119_read_order]
  rw [littleEndianListNat_ofFn119]
  change qubitBasisLittleEndianIndex
      (historyOrderWidth source.historyParameters.taylorOrder)
      (orderBits119 source fits index) = index.state.label.val
  simp only [orderBits119, qubitBasisLittleEndianIndex_basis]

theorem correctedBranchHistoryBasis119_order_equals
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (constant : Nat)
    (constantFits : constant < 2 ^
      (historyRegisterWires
        (ExecutableLayout119 source domain).order).length) :
    ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires (ExecutableLayout119 source domain).order)
        constant
        (correctedBranchHistoryBasis119 source domain fits branch index) =
      decide (index.state.label.val = constant) := by
  rw [ClassicalReversibleStage.littleEndianRegisterEqualsNat_eq_decide]
  · rw [correctedBranchHistoryBasis119_order_value]
  · exact constantFits

theorem h2BeforeQ119_active_selected_value
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source) :
    h2BeforeQ119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch index)
        (historyActiveWire (ExecutableLayout119 source domain)) =
      (decide (branch.val = 1) &&
        decide (index.clock.val < source.historyParameters.physicalClocks)) := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits branch index
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits branch index
  have afterSelector :=
    historyTaylorSelectorEqualityBasisAction_maps_phase layout input auxiliary
  have afterTime := historyTaylorTimeComparisonBasisAction_maps_phase
    layout (h2AfterSelector119 layout input) afterSelector
  have afterIdle := historyTaylorIdleEndComparisonBasisAction_maps_phase
    layout (h2AfterTime119 layout input) afterTime
  have before := historyTaylorActiveConjunctionBasisAction_maps_phase
    layout (h2AfterIdleEnd119 layout input) afterIdle
  have selectorStable :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 1
          (historyTaylorActiveConjunctionBasisAction layout
            (h2AfterIdleEnd119 layout input)) =
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 1 input := by
    unfold historyTaylorActiveConjunctionBasisAction
      h2AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
      h2AfterTime119 historyTaylorTimeComparisonBasisAction
      h2AfterSelector119 historyTaylorSelectorEqualityBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
      ClassicalReversibleStage.equalityToConstantDirectBasisAction
    rw [layout.selectorEqualsNat_xorWire_workspace
      (historyActiveWire layout) (historyActiveWire_mem_workspace layout)]
    rw [layout.selectorEqualsNat_xorWire_workspace
      (historyLessThanIdleEndWire layout)
      (historyLessThanIdleEndWire_mem_workspace layout)]
    rw [layout.selectorEqualsNat_xorWire_workspace
      (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_mem_workspace layout)]
    rw [layout.selectorEqualsNat_xorWire_workspace
      (historyBranchWire layout) (historyBranchWire_mem_workspace layout)]
  have clockStable :
      historyTaylorClockLessThanTimeValue layout
          (historyTaylorActiveConjunctionBasisAction layout
            (h2AfterIdleEnd119 layout input)) =
        historyTaylorClockLessThanTimeValue layout input := by
    unfold historyTaylorClockLessThanTimeValue
      historyTaylorActiveConjunctionBasisAction
      h2AfterIdleEnd119 historyTaylorIdleEndComparisonBasisAction
      h2AfterTime119 historyTaylorTimeComparisonBasisAction
      h2AfterSelector119 historyTaylorSelectorEqualityBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
      ClassicalReversibleStage.equalityToConstantDirectBasisAction
    rw [layout.clock_read_xorWire_workspace
      (historyActiveWire layout) (historyActiveWire_mem_workspace layout)]
    rw [layout.clock_read_xorWire_workspace
      (historyLessThanIdleEndWire layout)
      (historyLessThanIdleEndWire_mem_workspace layout)]
    rw [layout.clock_read_xorWire_workspace
      (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_mem_workspace layout)]
    rw [layout.clock_read_xorWire_workspace
      (historyBranchWire layout) (historyBranchWire_mem_workspace layout)]
  change h2BeforeQ119 layout input (historyActiveWire layout) = _
  unfold h2BeforeQ119
  rw [before.2.2.2.1, before.1, before.2.1,
    selectorStable, clockStable]
  rw [correctedBranchHistoryBasis119_selector_one,
    correctedBranchHistoryBasis119_clockLessThanTime]

end
end ExecutableHistoryExecutableHistory
