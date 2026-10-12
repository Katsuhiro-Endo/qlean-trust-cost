import QLean.Generator.Implementation.QVerifiedDecoderComponents
import QLean.Generator.Analysis.QOracleConcreteAnalyticSpecs

/-!
# Q event branch の strict 階層 component 第4版

event compute の周期算術と membership を第2版の公開 component root へ差し替え、
candidate・sort・writer は既存の明示的 compiled leaf 契約として維持する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- column event compute は、V2算術・membership rootを含む八子componentの解析列に一致する。 -/
theorem computeColumnEventCandidateUpdateAndSortCircuit_eq_stateSpec
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnEventCandidateUpdateAndSortCleanInput p slot offset input) :
    (computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output := by
  let states := ColumnEventCandidateUpdateAndSortStateSpec p slot offset input
  have selectorEq :
      (columnEventSelectorCompute p slot offset).runBasis
          reversibleGatePermutation input = states.afterSelector := by
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      selectorEqualsConstantAnalyticAction, columnEventSelectorMatches,
      diagonalSelectorMatches] using
      runBasis_columnEventSelectorCompute p slot offset input clean.selector_scratch
  have movedEq :
      (columnEventMovedCopy p slot).runBasis reversibleGatePermutation
          states.afterSelector = states.afterMovedCopy := by
    exact runBasis_columnEventMovedCopy_eq_controlledCopyReference p slot
      states.afterSelector
  have moveEq :
      (columnEventMoveForward p offset).runBasis reversibleGatePermutation
          states.afterMovedCopy = states.afterMove := by
    exact (verifiedIncrementWordMod2PowInPlaceCleanComponent (columnEventCoordinate p offset)
      (decoderAndScratchWires p)
      (columnEventMoveLayout_canonical p slot offset).enough_scratch
      (columnEventMoveLayout_canonical p slot offset).coordinate_scratch_nodup
      ).runBasis_correct states.afterMovedCopy clean.move_scratch
  have membershipEq :
      (columnEventMembership p slot).runBasis reversibleGatePermutation
          states.afterMove = states.afterMembership := by
    exact (verifiedXorMembershipMatchGoodAndAbsentFlagsCleanComponent p (columnKeyWires p)
      (columnKeyWires_membershipInputLayout p) slot true).runBasis_correct
        states.afterMove clean.membership_clean
  have branchEq :
      (columnEventBranchCompute p slot offset).runBasis
          reversibleGatePermutation states.afterMembership = states.afterBranch := by
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      positiveControlAnalyticAction] using
      runBasis_columnEventBranchCompute_canonical p slot offset
        states.afterMembership clean.branch_scratch
  have candidatesEq :
      (xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
          reversibleGatePermutation states.afterBranch = states.afterCandidates := by
    have result := (verifiedXorConfigurationIntoCandidateRegisterCleanComponent p (columnKeyWires p)
      (columnKeyWires_candidateInputLayout p)).runBasis_correct
        states.afterBranch trivial
    change (xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
      reversibleGatePermutation states.afterBranch =
        ConfigurationToCandidateRegisterXorSpec p (columnKeyWires p) states.afterBranch at result
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedXorConfigurationIntoCandidateRegisterCleanComponent] using result
  have modifyEq :
      (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
          states.afterCandidates = states.afterModify := by
    have result := (verifiedControlledUpdateSelectedCandidateWordCleanComponent p (.column slot offset)).runBasis_correct
      states.afterCandidates trivial
    change (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
      states.afterCandidates =
        ControlledSelectedColumnCandidateWordUpdateSpec p slot offset states.afterCandidates at result
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedControlledUpdateSelectedCandidateWordCleanComponent, verifiedControlledUpdateSelectedColumnCandidateWordCleanComponent] using result
  have sortEq :
      (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
          states.afterModify = states.output := by
    have result := (verifiedReversibleCandidateSortWithHistoryRestorationCleanComponent p).runBasis_correct
      states.afterModify clean.sort_clean
    change (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
      states.afterModify =
        CanonicalCandidateSortWithHistoryRestorationSpec p (qTypedBitonicSchedule p) states.afterModify at result
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedReversibleCandidateSortWithHistoryRestorationCleanComponent] using result
  change
    (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
      ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
        ((xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
          reversibleGatePermutation
          ((columnEventBranchCompute p slot offset).runBasis
            reversibleGatePermutation
            ((columnEventMembership p slot).runBasis reversibleGatePermutation
              ((columnEventMoveForward p offset).runBasis reversibleGatePermutation
                ((columnEventMovedCopy p slot).runBasis reversibleGatePermutation
                  ((columnEventSelectorCompute p slot offset).runBasis
                    reversibleGatePermutation input))))))) = states.output
  rw [selectorEq, movedEq, moveEq, membershipEq, branchEq, candidatesEq,
    modifyEq, sortEq]

/-- row event compute は、V2算術・membership rootを含む八子componentの解析列に一致する。 -/
theorem computeRowEventPredecessorCandidateUpdateAndSortCircuit_eq_stateSpec
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowEventPredecessorCandidateUpdateAndSortCleanInput p slot offset input) :
    (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output := by
  let states := RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input
  have selectorEq :
      (rowEventSelectorCompute p slot offset).runBasis
          reversibleGatePermutation input = states.afterSelector := by
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      selectorEqualsConstantAnalyticAction, rowEventSelectorMatches,
      diagonalSelectorMatches] using
      runBasis_rowEventSelectorCompute p slot offset input clean.selector_scratch
  have movedEq :
      (rowEventMovedCopy p slot).runBasis reversibleGatePermutation
          states.afterSelector = states.afterMovedCopy := by
    exact runBasis_rowEventMovedCopy_eq_controlledCopyReference p slot
      states.afterSelector
  have moveEq :
      (rowEventMoveBackward p offset).runBasis reversibleGatePermutation
          states.afterMovedCopy = states.afterMove := by
    have result := (verifiedDecrementWordMod2PowInPlaceCleanComponent (columnEventCoordinate p offset)
      (decoderAndScratchWires p)
      (columnEventMoveLayout_canonical p slot offset).enough_scratch
      (columnEventMoveLayout_canonical p slot offset).coordinate_scratch_nodup
      ).runBasis_correct states.afterMovedCopy clean.move_scratch
    change (decrementWordMod2PowInPlaceCircuit (columnEventCoordinate p offset)
      (decoderAndScratchWires p)).runBasis reversibleGatePermutation
        states.afterMovedCopy = decrementWordBorrowSequenceReference []
          (columnEventCoordinate p offset) states.afterMovedCopy at result
    simpa [rowEventMoveBackward, columnEventCoordinate, states,
      RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates] using result
  have membershipEq :
      (rowEventMembership p slot).runBasis reversibleGatePermutation
          states.afterMove = states.afterMembership := by
    exact (verifiedXorMembershipMatchGoodAndAbsentFlagsCleanComponent p (systemWires p)
      (systemWires_membershipInputLayout p) slot false).runBasis_correct
        states.afterMove clean.membership_clean
  have branchEq :
      (rowEventBranchCompute p slot offset).runBasis reversibleGatePermutation
          states.afterMembership = states.afterBranch := by
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      positiveControlAnalyticAction] using
      runBasis_rowEventBranchCompute_canonical p slot offset
        states.afterMembership clean.branch_scratch
  have candidatesEq :
      (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
          reversibleGatePermutation states.afterBranch = states.afterCandidates := by
    have result := (verifiedXorConfigurationIntoCandidateRegisterCleanComponent p (systemWires p)
      (systemWires_candidateInputLayout p)).runBasis_correct
        states.afterBranch trivial
    change (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
      reversibleGatePermutation states.afterBranch =
        ConfigurationToCandidateRegisterXorSpec p (systemWires p) states.afterBranch at result
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedXorConfigurationIntoCandidateRegisterCleanComponent] using result
  have modifyEq :
      (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
          states.afterCandidates = states.afterModify := by
    have result := (verifiedControlledUpdateSelectedCandidateWordCleanComponent p (.row slot offset)).runBasis_correct
      states.afterCandidates clean.update_clean
    change (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
      states.afterCandidates =
        ControlledSelectedRowCandidateWordUpdateSpec p slot offset states.afterCandidates at result
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedControlledUpdateSelectedCandidateWordCleanComponent, verifiedControlledUpdateSelectedRowCandidateWordCleanComponent] using result
  have sortEq :
      (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
          states.afterModify = states.output := by
    have result := (verifiedReversibleCandidateSortWithHistoryRestorationCleanComponent p).runBasis_correct
      states.afterModify clean.sort_clean
    change (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
      states.afterModify =
        CanonicalCandidateSortWithHistoryRestorationSpec p (qTypedBitonicSchedule p) states.afterModify at result
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedReversibleCandidateSortWithHistoryRestorationCleanComponent] using result
  change
    (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
      ((controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
        ((xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
          reversibleGatePermutation
          ((rowEventBranchCompute p slot offset).runBasis reversibleGatePermutation
            ((rowEventMembership p slot).runBasis reversibleGatePermutation
              ((rowEventMoveBackward p offset).runBasis reversibleGatePermutation
                ((rowEventMovedCopy p slot).runBasis reversibleGatePermutation
                  ((rowEventSelectorCompute p slot offset).runBasis
                    reversibleGatePermutation input))))))) = states.output
  rw [selectorEq, movedEq, moveEq, membershipEq, branchEq, candidatesEq,
    modifyEq, sortEq]

/-- V2算術・membership rootsから構成したcolumn event compute component。 -/
def verifiedComputeColumnEventCandidateUpdateAndSortCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := computeColumnEventCandidateUpdateAndSortCircuit p slot offset
  reference := fun input => (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output
  inputCondition := ColumnEventCandidateUpdateAndSortCleanInput p slot offset
  outputCondition := fun _ => True
  restoration := fun _ _ => True
  runBasis_correct := computeColumnEventCandidateUpdateAndSortCircuit_eq_stateSpec p slot offset
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- V2算術・membership rootsから構成したrow event compute component。 -/
def verifiedComputeRowEventPredecessorCandidateUpdateAndSortCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset
  reference := fun input => (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output
  inputCondition := RowEventPredecessorCandidateUpdateAndSortCleanInput p slot offset
  outputCondition := fun _ => True
  restoration := fun _ _ => True
  runBasis_correct := computeRowEventPredecessorCandidateUpdateAndSortCircuit_eq_stateSpec p slot offset
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- column compute と writer use の公開契約だけで記述する、column event のclean入力。 -/
def ColumnEventResultComputeUseUncomputeInput (p : QParameters) (slot : Fin p.K)
    (offset : Fin 6) (input : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  (verifiedComputeColumnEventCandidateUpdateAndSortCleanComponent p slot offset).inputCondition input ∧
    (verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).inputCondition
      ((verifiedComputeColumnEventCandidateUpdateAndSortCleanComponent p slot offset).reference input)

/-- row compute と writer use の公開契約だけで記述する、row event のclean入力。 -/
def RowEventResultComputeUseUncomputeInput (p : QParameters) (slot : Fin p.K)
    (offset : Fin 6) (input : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  (verifiedComputeRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).inputCondition input ∧
    (verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).inputCondition
      ((verifiedComputeRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).reference input)

/-- column computeとcompiled writer useを局所C-U-Uで合成する。 -/
noncomputable def verifiedColumnEventResultComputeUseUncomputeCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := columnEventResultComputeUseUncomputeCircuit p slot offset
  reference := ColumnEventComputeUseUncomputeReference p slot offset
  inputCondition := ColumnEventResultComputeUseUncomputeInput p slot offset
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = ColumnEventComputeUseUncomputeReference p slot offset input
  runBasis_correct := by
    intro input clean
    rw [columnEventResultComputeUseUncomputeCircuit,
      applyColumnEventReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
    have computeEq := (verifiedComputeColumnEventCandidateUpdateAndSortCleanComponent p slot offset).runBasis_correct
      input clean.1
    change (computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output at computeEq
    have useEq := (verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).runBasis_correct
      ((verifiedComputeColumnEventCandidateUpdateAndSortCleanComponent p slot offset).reference input) clean.2
    change (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
      ((ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output) =
        (verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference
          ((ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output) at useEq
    have preserveActual : BasisAgreeOn (columnEventCandidateUpdateAndSortSupport p)
        ((xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
          ((computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input))
        ((computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input) := by
      rw [computeEq, useEq]
      exact columnEventDelimiterAndSelectorOutputs_preserveComputeSupport p offset _ clean.2
    calc
      (Circuit.computeUseUncompute id (computeColumnEventCandidateUpdateAndSortCircuit p slot offset)
          (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset)).runBasis reversibleGatePermutation input =
        restoreSupport (columnEventCandidateUpdateAndSortSupport p) input
          ((xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
            ((computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis
              reversibleGatePermutation input)) :=
        Circuit.computeUseUncompute_local_clean (columnEventCandidateUpdateAndSortSupport p)
          (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset) input
          (computeColumnEventCandidateUpdateAndSortCircuit_usesOnly p slot offset) preserveActual
      _ = ColumnEventComputeUseUncomputeReference p slot offset input := by
        rw [computeEq, useEq]
        rfl
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- row computeとcompiled writer useを局所C-U-Uで合成する。 -/
noncomputable def verifiedRowEventResultComputeUseUncomputeCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := rowEventResultComputeUseUncomputeCircuit p slot offset
  reference := RowEventComputeUseUncomputeReference p slot offset
  inputCondition := RowEventResultComputeUseUncomputeInput p slot offset
  outputCondition := fun _ => True
  restoration := fun input output => output = RowEventComputeUseUncomputeReference p slot offset input
  runBasis_correct := by
    intro input clean
    rw [rowEventResultComputeUseUncomputeCircuit,
      applyRowEventReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
    have computeEq := (verifiedComputeRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).runBasis_correct
      input clean.1
    change (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output at computeEq
    have useEq := (verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).runBasis_correct
      ((verifiedComputeRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).reference input) clean.2
    change (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
      ((RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output) =
        (verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference
          ((RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output) at useEq
    have preserveActual : BasisAgreeOn (rowEventPredecessorCandidateUpdateAndSortSupport p)
        ((xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
          ((computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input))
        ((computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input) := by
      rw [computeEq, useEq]
      exact rowEventPredecessorDelimiterAndSelectorOutputs_preserveComputeSupport p offset _ clean.2
    calc
      (Circuit.computeUseUncompute id (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset)
          (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset)).runBasis reversibleGatePermutation input =
        restoreSupport (rowEventPredecessorCandidateUpdateAndSortSupport p) input
          ((xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
            ((computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis
              reversibleGatePermutation input)) :=
        Circuit.computeUseUncompute_local_clean (rowEventPredecessorCandidateUpdateAndSortSupport p)
          (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset) input
          (computeRowEventPredecessorCandidateUpdateAndSortCircuit_usesOnly p slot offset) preserveActual
      _ = RowEventComputeUseUncomputeReference p slot offset input := by
        rw [computeEq, useEq]
        rfl
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- column event の外部観測関係と全外部wire復元をpure generic契約へ代入した仕様。 -/
def ColumnEventRestoredObservationSpec
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  RestoredObservationSpec
    (fun source target => ColumnEventBranchReferenceResult p offset source
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset source).output target)
    (fun source target => ∀ wire,
      wire ∉ rowOutputWires p → wire ∉ selectorOutputWires p →
        wire ≠ activeWire p → target wire = source wire)
    input output

/-- pure generic column event契約を、旧physical仕様へ変換する薄い解析bridge。 -/
theorem ColumnEventRestoredObservationSpec.toPhysical
    {p : QParameters} {slot : Fin p.K} {offset : Fin 6}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (spec : ColumnEventRestoredObservationSpec p slot offset input output) :
    ColumnEventRestoredReferenceIdentification p offset input
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output output := by
  exact {
    toColumnEventBranchReferenceResult := spec.observation_correct
    outside_restored := spec.restoration_correct }

/-- 旧physical column event仕様を、pure generic契約へ閉じ込める薄い解析bridge。 -/
theorem ColumnEventRestoredObservationSpec.ofPhysical
    {p : QParameters} {slot : Fin p.K} {offset : Fin 6}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (spec : ColumnEventRestoredReferenceIdentification p offset input
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output output) :
    ColumnEventRestoredObservationSpec p slot offset input output := by
  exact {
    observation_correct := spec.toColumnEventBranchReferenceResult
    restoration_correct := spec.outside_restored }

/-- column event のpure generic契約は全物理wire上で出力を一意に定める。 -/
theorem ColumnEventRestoredObservationSpec.unique
    {p : QParameters} {slot : Fin p.K} {offset : Fin 6}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : ColumnEventRestoredObservationSpec p slot offset input left)
    (rightSpec : ColumnEventRestoredObservationSpec p slot offset input right) :
    left = right :=
  leftSpec.toPhysical.unique rightSpec.toPhysical

/-- row event の外部観測関係と全外部wire復元をpure generic契約へ代入した仕様。 -/
def RowEventRestoredObservationSpec
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  RestoredObservationSpec
    (fun source target => RowEventBranchReferenceResult p offset source
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset source).output target)
    (fun source target => ∀ wire,
      wire ∉ columnKeyWires p → wire ∉ columnSelectorWires p →
        wire ≠ keySignalWire p → target wire = source wire)
    input output

/-- pure generic row event契約を、旧physical仕様へ変換する薄い解析bridge。 -/
theorem RowEventRestoredObservationSpec.toPhysical
    {p : QParameters} {slot : Fin p.K} {offset : Fin 6}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (spec : RowEventRestoredObservationSpec p slot offset input output) :
    RowEventRestoredReferenceIdentification p offset input
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output output := by
  exact {
    toRowEventBranchReferenceResult := spec.observation_correct
    outside_restored := spec.restoration_correct }

/-- 旧physical row event仕様を、pure generic契約へ閉じ込める薄い解析bridge。 -/
theorem RowEventRestoredObservationSpec.ofPhysical
    {p : QParameters} {slot : Fin p.K} {offset : Fin 6}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (spec : RowEventRestoredReferenceIdentification p offset input
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output output) :
    RowEventRestoredObservationSpec p slot offset input output := by
  exact {
    observation_correct := spec.toRowEventBranchReferenceResult
    restoration_correct := spec.outside_restored }

/-- row event のpure generic契約は全物理wire上で出力を一意に定める。 -/
theorem RowEventRestoredObservationSpec.unique
    {p : QParameters} {slot : Fin p.K} {offset : Fin 6}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : RowEventRestoredObservationSpec p slot offset input left)
    (rightSpec : RowEventRestoredObservationSpec p slot offset input right) :
    left = right :=
  leftSpec.toPhysical.unique rightSpec.toPhysical

/-- 最終pure解析仕様をreferenceに持つcolumn event公開component。 -/
noncomputable def verifiedApplyColumnEventReferenceAndRestoreWorkCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  CleanComponent.refineReference
    (verifiedColumnEventResultComputeUseUncomputeCleanComponent p slot offset)
    (uniqueAnalyticReference (ColumnEventRestoredObservationSpec p slot offset))
    (ColumnEventResultComputeUseUncomputeInput p slot offset)
    (fun _ => True)
    (ColumnEventRestoredObservationSpec p slot offset)
    (by intro _ clean; exact clean)
    (by
      intro input clean
      have composedSpec := ColumnEventRestoredObservationSpec.ofPhysical
        (identifyColumnEventImplementationWithRestoredReference p slot offset input clean)
      have uniqueOutput : ∃! output,
          ColumnEventRestoredObservationSpec p slot offset input output :=
        ⟨ColumnEventComputeUseUncomputeReference p slot offset input, composedSpec,
          fun other otherSpec => otherSpec.unique composedSpec⟩
      exact (uniqueAnalyticReference_eq uniqueOutput composedSpec).symm)
    (by simp)
    (by
      intro input clean
      have composedSpec := ColumnEventRestoredObservationSpec.ofPhysical
        (identifyColumnEventImplementationWithRestoredReference p slot offset input clean)
      have uniqueOutput : ∃! output,
          ColumnEventRestoredObservationSpec p slot offset input output :=
        ⟨ColumnEventComputeUseUncomputeReference p slot offset input, composedSpec,
          fun other otherSpec => otherSpec.unique composedSpec⟩
      exact uniqueAnalyticReference_spec uniqueOutput)

/-- 最終pure解析仕様をreferenceに持つrow event公開component。 -/
noncomputable def verifiedApplyRowEventReferenceAndRestoreWorkCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  CleanComponent.refineReference
    (verifiedRowEventResultComputeUseUncomputeCleanComponent p slot offset)
    (uniqueAnalyticReference (RowEventRestoredObservationSpec p slot offset))
    (RowEventResultComputeUseUncomputeInput p slot offset)
    (fun _ => True)
    (RowEventRestoredObservationSpec p slot offset)
    (by intro _ clean; exact clean)
    (by
      intro input clean
      have composedSpec := RowEventRestoredObservationSpec.ofPhysical
        (identifyRowEventImplementationWithRestoredReference p slot offset input clean)
      have uniqueOutput : ∃! output,
          RowEventRestoredObservationSpec p slot offset input output :=
        ⟨RowEventComputeUseUncomputeReference p slot offset input, composedSpec,
          fun other otherSpec => otherSpec.unique composedSpec⟩
      exact (uniqueAnalyticReference_eq uniqueOutput composedSpec).symm)
    (by simp)
    (by
      intro input clean
      have composedSpec := RowEventRestoredObservationSpec.ofPhysical
        (identifyRowEventImplementationWithRestoredReference p slot offset input clean)
      have uniqueOutput : ∃! output,
          RowEventRestoredObservationSpec p slot offset input output :=
        ⟨RowEventComputeUseUncomputeReference p slot offset input, composedSpec,
          fun other otherSpec => otherSpec.unique composedSpec⟩
      exact uniqueAnalyticReference_spec uniqueOutput)

end ReversibleCircuit

end ProbabilityGeneratorQProof
