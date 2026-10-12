import QLean.History.Implementation.HistoryPipelineH2LogicalSupport

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

/-- Increment a logical history label anywhere below the last binary label.
Unlike `raiseHistoryLabel119`, this includes the idle padding range above the
Taylor order. -/
def incrementHistoryLabel119
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (nextFits : index.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    OldHistoryIndex119 source :=
  { clock := index.clock
    state :=
      { label := ⟨index.state.label.val + 1, nextFits⟩
        configuration := configuration } }

@[simp] theorem incrementHistoryLabel119_clock
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (nextFits : index.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    (incrementHistoryLabel119 source index configuration nextFits).clock =
      index.clock := rfl

@[simp] theorem incrementHistoryLabel119_label_val
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (nextFits : index.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    (incrementHistoryLabel119 source index configuration nextFits).state.label.val =
      index.state.label.val + 1 := rfl

@[simp] theorem incrementHistoryLabel119_configuration
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (nextFits : index.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    (incrementHistoryLabel119 source index configuration nextFits).state.configuration =
      configuration := rfl

theorem executableHistoryBasis119_incrementLabel_outside_order
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (nextFits : index.state.label.val + 1 <
      source.historyParameters.binaryLabels)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (outside : ∀ orderIndex,
      (ExecutableLayout119 source domain).order.wire orderIndex ≠ wire) :
    executableHistoryBasis119 source domain fits
        (incrementHistoryLabel119 source index configuration nextFits) wire =
      executableHistoryBasis119 source domain fits
        (replaceConfiguration119 source index configuration) wire := by
  have clockBitsEqual :
      clockBits119 source fits
          (incrementHistoryLabel119 source index configuration nextFits) =
        clockBits119 source fits
          (replaceConfiguration119 source index configuration) := by
    funext bit
    rfl
  unfold executableHistoryBasis119
  rw [clockBitsEqual]
  simp [incrementHistoryLabel119, replaceConfiguration119,
    writeRegisterBits, outside]

theorem correctedBranchHistoryBasis119_incrementLabel_outside_order
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (nextFits : index.state.label.val + 1 <
      source.historyParameters.binaryLabels)
    (wire : Fin (ExecutableRaw119 source).history.qubits)
    (outside : ∀ orderIndex,
      (ExecutableLayout119 source domain).order.wire orderIndex ≠ wire) :
    correctedBranchHistoryBasis119 source domain fits branch
        (incrementHistoryLabel119 source index configuration nextFits) wire =
      correctedBranchHistoryBasis119 source domain fits branch
        (replaceConfiguration119 source index configuration) wire := by
  by_cases selectorMember : wire ∈
      historyRegisterWires (ExecutableLayout119 source domain).selector
  · simp only [historyRegisterWires, List.mem_ofFn] at selectorMember
    rcases selectorMember with ⟨selectorIndex, rfl⟩
    have left := congrFun
      (correctedBranchHistoryBasis119_restrict_selector source domain fits branch
        (incrementHistoryLabel119 source index configuration nextFits)) selectorIndex
    have right := congrFun
      (correctedBranchHistoryBasis119_restrict_selector source domain fits branch
        (replaceConfiguration119 source index configuration)) selectorIndex
    exact left.trans right.symm
  · rw [correctedBranchHistoryBasis119_apply_of_not_selector,
      correctedBranchHistoryBasis119_apply_of_not_selector]
    · exact executableHistoryBasis119_incrementLabel_outside_order
        source domain fits index configuration nextFits wire outside
    · exact selectorMember
    · exact selectorMember

theorem writeRegisterValue_correctedBranchHistoryBasis119_incrementLabel
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (nextFits : index.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    writeRegisterValue (ExecutableLayout119 source domain).order
        (index.state.label.val + 1)
        (correctedBranchHistoryBasis119 source domain fits branch
          (replaceConfiguration119 source index configuration)) =
      correctedBranchHistoryBasis119 source domain fits branch
        (incrementHistoryLabel119 source index configuration nextFits) := by
  funext wire
  by_cases inside : ∃ orderIndex,
      (ExecutableLayout119 source domain).order.wire orderIndex = wire
  · rcases inside with ⟨orderIndex, rfl⟩
    rw [writeRegisterValue_apply_wire]
    have readIncremented := congrFun
      (correctedBranchHistoryBasis119_read_order source domain fits branch
        (incrementHistoryLabel119 source index configuration nextFits)) orderIndex
    change (index.state.label.val + 1).testBit orderIndex.val =
      (ExecutableLayout119 source domain).order.read
        (correctedBranchHistoryBasis119 source domain fits branch
          (incrementHistoryLabel119 source index configuration nextFits)) orderIndex
    rw [readIncremented]
    rfl
  · rw [writeRegisterValue_apply_outside]
    · exact (correctedBranchHistoryBasis119_incrementLabel_outside_order
        source domain fits branch index configuration nextFits wire
        (fun orderIndex equal => inside ⟨orderIndex, equal⟩)).symm
    · intro orderIndex equal
      exact inside ⟨orderIndex, equal⟩

theorem h2AfterIdleEnd119_incrementHistoryLabel119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (nextFits : index.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    h2AfterIdleEnd119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits branch
          (incrementHistoryLabel119 source index configuration nextFits)) =
      writeRegisterValue (ExecutableLayout119 source domain).order
        (index.state.label.val + 1)
        (h2AfterIdleEnd119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits branch
            (replaceConfiguration119 source index configuration))) := by
  rw [← writeRegisterValue_correctedBranchHistoryBasis119_incrementLabel]
  exact h2AfterIdleEnd119_write_order119
    (ExecutableLayout119 source domain) (index.state.label.val + 1)
    (correctedBranchHistoryBasis119 source domain fits branch
      (replaceConfiguration119 source index configuration))

/-- Full-range idle action below the final logical binary label.  This is the
idle analogue of `applyOperator_h2PostOperator_idle_taylor119`, but it does
not restrict the input label to the Taylor range. -/
theorem applyOperator_h2PostOperator_idle_nonterminal119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (nextFits : index.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    let layout := ExecutableLayout119 source domain
    let logicalInput := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 index
    let logicalOutput := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119
      (incrementHistoryLabel119 source index index.state.configuration nextFits)
    VerifiedCircuitCore.applyOperator
        (h2PostOperator119 layout
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout logicalInput)) =
      ((Real.cos (compiledIdleCoefficientAngle119.uniformValue / 2) : Real) :
          Complex) • VerifiedCircuitCore.basisKet logicalOutput +
        ((Real.sin (compiledIdleCoefficientAngle119.uniformValue / 2) : Real) :
          Complex) •
          VerifiedCircuitCore.basisKet (replaceQubitWire logicalOutput
            layout.coefficientSignal true) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let newIndex := incrementHistoryLabel119 source index
    index.state.configuration nextFits
  let logicalInput := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 index
  let logicalOutput := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 newIndex
  let stable := h2AfterIdleEnd119 layout logicalInput
  let incremented := h2AfterIdleEnd119 layout logicalOutput
  have taylorOrderEq :
      (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic).taylorOrder =
        source.historyParameters.taylorOrder := by
    rfl
  have stablePredicate : historyTaylorPostGeneratorStablePredicate layout stable :=
    h2AfterIdleEnd119_postStable119 source domain fits h2SelectedBranch119 index
  have branchStable : stable (historyBranchWire layout) = true :=
    h2AfterIdleEnd119_branch_flag_selected source domain fits index
  have timeFlagStable : stable (historyLessThanTimeWire layout) = false :=
    h2AfterIdleEnd119_time_flag_idle119 source domain fits index clockIdle
  have idleFlagStable : stable (historyLessThanIdleEndWire layout) = true :=
    h2AfterIdleEnd119_idle_flag_logical119 source domain fits index
  have clockFalse : historyTaylorClockLessThanTimeValue layout stable = false := by
    rw [← stablePredicate.2.1]
    exact timeFlagStable
  have idleClockTrue :
      historyTaylorClockLessThanIdleEndValue layout stable = true := by
    rw [← stablePredicate.2.2.1]
    exact idleFlagStable
  have activeStep :
      historyTaylorActiveConjunctionBasisAction layout
          (h2BeforeQ119 layout logicalInput) = stable :=
    historyTaylorActiveConjunctionBasisAction_involutive119 layout stable
  have invalidStep :
      historyTaylorInvalidClockBasisAction layout stable = stable := by
    unfold historyTaylorInvalidClockBasisAction
      historyTaylorInvalidClockCondition
    rw [branchStable, idleFlagStable]
    simp [xorWire]
  have orderBoundaryStep :
      historyTaylorOrderBoundaryBasisAction layout stable = stable := by
    unfold historyTaylorOrderBoundaryBasisAction
      historyTaylorOrderBoundaryCondition
    rw [branchStable, clockFalse]
    simp [xorWire]
  have idleIntervalTrue :
      historyTaylorIdleIntervalCondition layout stable = true := by
    unfold historyTaylorIdleIntervalCondition
    rw [idleClockTrue, clockFalse]
    rfl
  have nextBound : index.state.label.val + 1 <
      2 ^ historyOrderWidth
        (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
          (ExecutableAdmissible119 source domain).analytic).taylorOrder := by
    have logicalBound : index.state.label.val + 1 <
        2 ^ historyOrderWidth source.historyParameters.taylorOrder :=
      lt_of_lt_of_le nextFits fits.label_fits
    rw [taylorOrderEq]
    exact logicalBound
  have boundaryNe : index.state.label.val ≠
      historyIdleBlockSize source.historyParameters.taylorOrder - 1 := by
    have capacityEq : historyIdleBlockSize source.historyParameters.taylorOrder =
        2 ^ historyOrderWidth source.historyParameters.taylorOrder := rfl
    rw [capacityEq]
    have logicalBound : index.state.label.val + 1 <
        2 ^ historyOrderWidth source.historyParameters.taylorOrder :=
      lt_of_lt_of_le nextFits fits.label_fits
    omega
  have boundaryNe' : index.state.label.val ≠
      historyIdleBlockSize
        (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
          (ExecutableAdmissible119 source domain).analytic).taylorOrder - 1 := by
    rw [taylorOrderEq]
    exact boundaryNe
  have boundaryFits :
      historyIdleBlockSize
          (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic).taylorOrder - 1 <
        2 ^ (historyRegisterWires layout.order).length := by
    simp [historyIdleBlockSize, historyRegisterWires, layout]
  have boundaryFalse :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
          (historyRegisterWires layout.order)
          (historyIdleBlockSize
            (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
              (ExecutableAdmissible119 source domain).analytic).taylorOrder - 1)
          stable = false := by
    have sameOrder :
        ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order)
            (historyIdleBlockSize
              (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
                (ExecutableAdmissible119 source domain).analytic).taylorOrder - 1)
            stable =
          ClassicalReversibleStage.littleEndianRegisterEqualsNat
            (historyRegisterWires layout.order)
            (historyIdleBlockSize
              (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
                (ExecutableAdmissible119 source domain).analytic).taylorOrder - 1)
            logicalInput := by
      apply ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
      intro wire member
      simp only [historyRegisterWires, List.mem_ofFn] at member
      rcases member with ⟨orderIndex, rfl⟩
      exact congrFun (h2AfterIdleEnd119_read_order119 layout logicalInput)
        orderIndex
    rw [sameOrder,
      correctedBranchHistoryBasis119_order_equals source domain fits
        h2SelectedBranch119 index
        (historyIdleBlockSize
          (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
            (ExecutableAdmissible119 source domain).analytic).taylorOrder - 1)
        boundaryFits]
    simp [boundaryNe']
  have idleBoundaryStep :
      historyTaylorIdleBoundaryBasisAction layout stable = stable := by
    unfold historyTaylorIdleBoundaryBasisAction
      historyTaylorIdleBoundaryCondition
    rw [branchStable, idleIntervalTrue, boundaryFalse]
    simp [xorWire]
  have registerValueStable : registerValue layout.order stable =
      index.state.label.val :=
    registerValue_h2AfterIdleEnd_correctedBranch119
      source domain fits h2SelectedBranch119 index
  have degreeCondition :
      historyTaylorDegreeIncrementCondition layout stable = true := by
    simp [historyTaylorDegreeIncrementCondition, branchStable, idleClockTrue]
  have degreeStep :
      historyTaylorDegreeIncrementBasisAction layout stable = incremented := by
    unfold historyTaylorDegreeIncrementBasisAction
      predicateControlledAddMod2PowBasisAction
    rw [if_pos degreeCondition, registerValueStable,
      Nat.mod_eq_of_lt nextBound]
    exact (h2AfterIdleEnd119_incrementHistoryLabel119 source domain fits
      h2SelectedBranch119 index index.state.configuration nextFits).symm
  have incrementedPredicate :
      historyTaylorPostGeneratorStablePredicate layout incremented :=
    h2AfterIdleEnd119_postStable119 source domain fits h2SelectedBranch119 newIndex
  have branchIncremented : incremented (historyBranchWire layout) = true :=
    h2AfterIdleEnd119_branch_flag_selected source domain fits newIndex
  have timeFlagIncremented :
      incremented (historyLessThanTimeWire layout) = false :=
    h2AfterIdleEnd119_time_flag_idle119 source domain fits newIndex
      (by simpa [newIndex] using clockIdle)
  have clockFalseIncremented :
      historyTaylorClockLessThanTimeValue layout incremented = false := by
    rw [← incrementedPredicate.2.1]
    exact timeFlagIncremented
  have idleFlagIncremented :
      incremented (historyLessThanIdleEndWire layout) = true :=
    h2AfterIdleEnd119_idle_flag_logical119 source domain fits newIndex
  have idleClockTrueIncremented :
      historyTaylorClockLessThanIdleEndValue layout incremented = true := by
    rw [← incrementedPredicate.2.2.1]
    exact idleFlagIncremented
  have coefficientLoopFixes :
      VerifiedCircuitCore.applyOperator
          (historyTaylorCoefficientLoopOperator layout
            (fun coefficientIndex => correctedTaylorCoefficientAngle119
              source.toCommonSource119 coefficientIndex.val))
          (VerifiedCircuitCore.basisKet incremented) =
        VerifiedCircuitCore.basisKet incremented :=
    historyTaylorCoefficientLoopOperator_apply_basisKet_of_clock_false119
      layout _ incremented clockFalseIncremented
  have idlePredicateTrue :
      (incremented (historyBranchWire layout) &&
        historyTaylorIdleIntervalCondition layout incremented) = true := by
    unfold historyTaylorIdleIntervalCondition
    rw [branchIncremented, idleClockTrueIncremented, clockFalseIncremented]
    rfl
  have idleSignalFalse : incremented layout.coefficientSignal = false := by
    calc
      incremented layout.coefficientSignal =
          logicalOutput layout.coefficientSignal :=
        h2AfterIdleEnd119_coefficientSignal119 layout logicalOutput
      _ = false := correctedBranchHistoryBasis119_coefficientSignal_false119
        source domain fits h2SelectedBranch119 newIndex
  have restoreClean :
      VerifiedCircuitCore.applyOperator
          (operatorSequence
            [historyTaylorIdleEndComparisonOperator layout,
             historyTaylorTimeComparisonOperator layout,
             historyTaylorSelectorEqualityOperator layout])
          (VerifiedCircuitCore.basisKet incremented) =
        VerifiedCircuitCore.basisKet logicalOutput :=
    h2RestoreEntryFlags_apply_basisKet119 layout logicalOutput
  have restoreDirty :
      VerifiedCircuitCore.applyOperator
          (operatorSequence
            [historyTaylorIdleEndComparisonOperator layout,
             historyTaylorTimeComparisonOperator layout,
             historyTaylorSelectorEqualityOperator layout])
          (VerifiedCircuitCore.basisKet
            (replaceQubitWire incremented layout.coefficientSignal true)) =
        VerifiedCircuitCore.basisKet
          (replaceQubitWire logicalOutput layout.coefficientSignal true) := by
    rw [← h2AfterIdleEnd119_replace_coefficient119]
    exact h2RestoreEntryFlags_apply_basisKet119 layout
      (replaceQubitWire logicalOutput layout.coefficientSignal true)
  exact applyOperator_h2PostOperator_idle_of_stage_actions119
    layout _ compiledIdleCoefficientAngle119
    (h2BeforeQ119 layout logicalInput) stable incremented logicalOutput
    activeStep invalidStep orderBoundaryStep idleBoundaryStep degreeStep
    coefficientLoopFixes idlePredicateTrue idleSignalFalse
    restoreClean restoreDirty

/-- The complete H2 column on an idle clock and a nonterminal binary label. -/
theorem applyOperator_executableH2_idle_nonterminal119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (nextFits : inputIndex.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex
    let raised := incrementHistoryLabel119 source inputIndex
      inputIndex.state.configuration nextFits
    let output := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 raised
    VerifiedCircuitCore.applyOperator
        (h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout
            (ScientificWidthGenericContract.correctedCleanEvidence259
              (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
            (ExecutableAdmissible119 source domain).placementWidths
            (fun coefficientIndex => correctedTaylorCoefficientAngle119
              source.toCommonSource119 coefficientIndex.val)
            compiledIdleCoefficientAngle119))
        (VerifiedCircuitCore.basisKet input) =
      (-1 : Complex) • VerifiedCircuitCore.basisKet output := by
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
  let raised := incrementHistoryLabel119 source inputIndex
    inputIndex.state.configuration nextFits
  let output := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 raised
  have operatorEq :
      h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout clean widths
            angles compiledIdleCoefficientAngle119) =
        post * (q10 * pre) :=
    h2TaylorCleanOperator_historyP15_decompose119 layout clean widths
      angles compiledIdleCoefficientAngle119
  have activeFalse :
      (h2BeforeQ119 layout input) (historyActiveWire layout) = false :=
    h2BeforeQ119_active_false_of_idle_clock119 source domain fits inputIndex
      clockIdle
  have q10Fixed : VerifiedCircuitCore.applyOperator q10
      (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input)) =
        VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input) := by
    exact executableH2Q10_apply_basisKet_of_active_false119 source domain
      (h2BeforeQ119 layout input) activeFalse
  have postAction := applyOperator_h2PostOperator_idle_nonterminal119
    source domain fits inputIndex clockIdle nextFits
  have idleSinZero :
      Real.sin (compiledIdleCoefficientAngle119.uniformValue / 2) = 0 := by
    rw [compiledIdleCoefficientAngle119_value]
    simp
  have idleCosNeg :
      ((Real.cos (compiledIdleCoefficientAngle119.uniformValue / 2) : Real) :
          Complex) = (-1 : Complex) := by
    exact_mod_cast idleCoefficient_clean_amplitude119
  calc
    VerifiedCircuitCore.applyOperator
        (h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout clean widths
            angles compiledIdleCoefficientAngle119))
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.applyOperator (post * (q10 * pre))
        (VerifiedCircuitCore.basisKet input) := by rw [operatorEq]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator q10
          (VerifiedCircuitCore.applyOperator pre
            (VerifiedCircuitCore.basisKet input))) := by
      rw [VerifiedCircuitCore.applyOperator_mul,
        VerifiedCircuitCore.applyOperator_mul]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator q10
          (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input))) := by
      rw [h2BeforeOperators_apply_basisKet119]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input)) := by
      rw [q10Fixed]
    _ = ((Real.cos (compiledIdleCoefficientAngle119.uniformValue / 2) : Real) :
          Complex) • VerifiedCircuitCore.basisKet output +
        ((Real.sin (compiledIdleCoefficientAngle119.uniformValue / 2) : Real) :
          Complex) •
          VerifiedCircuitCore.basisKet
            (replaceQubitWire output layout.coefficientSignal true) := postAction
    _ = (-1 : Complex) • VerifiedCircuitCore.basisKet output := by
      rw [idleSinZero, idleCosNeg]
      simp

/-- Every clean logical row of a nonterminal idle H2 column. -/
theorem executableH2_idle_nonterminal_logical_clean_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (nextFits : inputIndex.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    let raised := incrementHistoryLabel119 source inputIndex
      inputIndex.state.configuration nextFits
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        row input = if outputIndex = raised then (-1 : Complex) else 0 := by
  dsimp only
  let input := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 inputIndex
  let row := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 outputIndex
  let raised := incrementHistoryLabel119 source inputIndex
    inputIndex.state.configuration nextFits
  let output := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 raised
  have action := applyOperator_executableH2_idle_nonterminal119 source domain fits
    inputIndex clockIdle nextFits
  have entryAction := congrFun action row
  simp only [VerifiedCircuitCore.applyOperator_basisKet] at entryAction
  rw [entryAction]
  simp only [Pi.smul_apply, VerifiedCircuitCore.basisKet,
    VerifiedMath.Basis.vector_apply, smul_eq_mul]
  have basisEqIff : row = output ↔ outputIndex = raised := by
    constructor
    · intro equal
      exact correctedBranchHistoryBasis119_injective_index source domain fits
        h2SelectedBranch119 equal
    · intro equal
      exact congrArg
        (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119)
        equal
  by_cases indexEq : outputIndex = raised
  · rw [if_pos indexEq, if_pos (basisEqIff.2 indexEq)]
    norm_num
  · rw [if_neg indexEq, if_neg (fun equal => indexEq (basisEqIff.1 equal))]
    norm_num

/-- Full nonterminal idle-clock equality of the actual H2 block with `L1`. -/
theorem executableH2_idle_nonterminal_entry_eq_L1_119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (nextFits : inputIndex.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
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
  let raised := incrementHistoryLabel119 source inputIndex
    inputIndex.state.configuration nextFits
  rw [executableH2_idle_nonterminal_logical_clean_entry119 source domain fits
    inputIndex outputIndex clockIdle nextFits]
  unfold HistoryBlockEncoding.HistorySpec.L1
  by_cases clockEq : outputIndex.clock = inputIndex.clock
  · rw [if_pos clockEq]
    have outputIdle : ¬ outputIndex.clock.val <
        source.historyParameters.physicalClocks := by
      simpa [clockEq] using clockIdle
    rw [if_neg outputIdle]
    unfold HistoryBlockEncoding.HistorySpec.deltaIdle
    by_cases indexEq : outputIndex = raised
    · rw [if_pos indexEq]
      have transition : outputIndex.state.label.val =
          inputIndex.state.label.val + 1 ∧
          outputIndex.state.configuration = inputIndex.state.configuration := by
        subst outputIndex
        simp [raised, incrementHistoryLabel119]
      rw [if_pos transition]
      norm_num
    · rw [if_neg indexEq]
      have noTransition : ¬(outputIndex.state.label.val =
          inputIndex.state.label.val + 1 ∧
          outputIndex.state.configuration = inputIndex.state.configuration) := by
        intro transition
        apply indexEq
        apply oldHistoryIndex_ext119
        · simpa [raised, incrementHistoryLabel119] using clockEq
        · apply labelState_ext119
          · apply Fin.ext
            simpa [raised, incrementHistoryLabel119] using transition.1
          · simpa [raised, incrementHistoryLabel119] using transition.2
      rw [if_neg noTransition]
      norm_num
  · rw [if_neg clockEq]
    have indexNe : outputIndex ≠ raised := by
      intro indexEq
      apply clockEq
      simpa [raised, incrementHistoryLabel119] using
        congrArg (fun current : OldHistoryIndex119 source => current.clock) indexEq
    rw [if_neg indexNe]
    norm_num

end
end ExecutableHistoryExecutableHistory
