import QLean.Generator.Implementation.QVerifiedOracleComponents
import QLean.Generator.Implementation.QVerifiedDecoderComponents
import QLean.Generator.Implementation.QVerifiedOracleEventComponents

/-!
# Q oracle全体を公開子componentから組み立てる第2版

このmoduleは、persistent compute、有限branch列、外側のuncomputeという自然な境界を
`CleanComponent`として公開する。巨大行列や全基底の列挙は行わない。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 複数sourceのparityに応じてtargetだけをXORする純粋基底作用。 -/
def SourceParityTargetXorSpec
    {ancillaQubits systemQubits : Nat}
    (sources : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if boolParity (readWires sources input) then xBasisAction target input else input

/-- degree suffixのparityを各present flagへ順にXORする純粋基底作用。 -/
def DegreeSuffixParitySlotPresenceXorSpec
    {ancillaQubits systemQubits : Nat}
    (degreeFlags : List (Wire ancillaQubits systemQubits)) :
    Nat → List (Wire ancillaQubits systemQubits) →
      JointBasis ancillaQubits systemQubits →
      JointBasis ancillaQubits systemQubits
  | _, [], input => input
  | slot, presentFlag :: presentFlags, input =>
      let next := SourceParityTargetXorSpec (degreeFlags.drop slot) presentFlag input
      DegreeSuffixParitySlotPresenceXorSpec degreeFlags (slot + 1) presentFlags next

/-- 一つのtarget bitを反転する回路wrapper。 -/
def flipTargetBitCircuit
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  .gate (.x target)

/-- 一つのtarget bitを反転する計算基底上の解析作用。 -/
def FlipTargetBitReference
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  xBasisAction target input

/-- 共有persistent flag計算を回路実装から独立な関数合成として表す。 -/
noncomputable def SharedPersistentFlagsReference
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p) (rowMode : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let degree := oracleDegreeWires p
  let sources := if rowMode then degree.take (p.K - 1) else degree.drop 1
  let decoded := uniqueSpecificationReference
    (DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration) input
  let present := DegreeSuffixParitySlotPresenceXorSpec degree 0
    (oraclePresentWires p) decoded
  let conditioned := SourceParityTargetXorSpec sources
    (oracleDegreeConditionWire p) present
  FlipTargetBitReference (oracleOneWire p) conditioned

/-- slot-presence回路の全基底作用を、有限リスト再帰の純粋作用へ結ぶ。 -/
theorem runBasis_xorDegreeSuffixParityIntoSlotPresenceCircuit_eq_spec
    {ancillaQubits systemQubits : Nat}
    (degreeFlags presentFlags : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (input : JointBasis ancillaQubits systemQubits)
    (degreeDisjointPresent : degreeFlags.Disjoint presentFlags) :
    (xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags slot presentFlags).runBasis
        reversibleGatePermutation input =
      DegreeSuffixParitySlotPresenceXorSpec degreeFlags slot presentFlags input := by
  induction presentFlags generalizing slot input with
  | nil => rfl
  | cons presentFlag presentFlags inductionHypothesis =>
      have targetAbsent : presentFlag ∉ degreeFlags.drop slot := by
        intro member
        exact (List.disjoint_left.mp degreeDisjointPresent)
          (List.mem_of_mem_drop member) (by simp)
      have degreeDisjointTail : degreeFlags.Disjoint presentFlags :=
        (List.disjoint_cons_right.mp degreeDisjointPresent).2
      simp only [xorDegreeSuffixParityIntoSlotPresenceCircuit, runBasis_seq, DegreeSuffixParitySlotPresenceXorSpec]
      change
        (xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags (slot + 1) presentFlags).runBasis
            reversibleGatePermutation
            ((xorSourceParityIntoTargetCircuit (degreeFlags.drop slot) presentFlag).runBasis
              reversibleGatePermutation input) = _
      rw [runBasis_xorSourceParityIntoTargetCircuit (degreeFlags.drop slot) presentFlag input
        targetAbsent]
      change
        (xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags (slot + 1) presentFlags).runBasis
            reversibleGatePermutation
            (SourceParityTargetXorSpec (degreeFlags.drop slot) presentFlag input) = _
      exact inductionHypothesis (slot + 1)
        (SourceParityTargetXorSpec (degreeFlags.drop slot) presentFlag input)
        degreeDisjointTail

/-- XOR-source列を純粋parity作用へ結ぶ全入力component。 -/
def verifiedXorSourceParityIntoTargetCleanComponent
    {ancillaQubits systemQubits : Nat}
    (sources : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (targetAbsent : target ∉ sources) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := xorSourceParityIntoTargetCircuit sources target
  reference := SourceParityTargetXorSpec sources target
  inputCondition := fun _ => True
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = SourceParityTargetXorSpec sources target input
  runBasis_correct := by
    intro input _
    exact runBasis_xorSourceParityIntoTargetCircuit sources target input targetAbsent
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- degree one-hotからpresent列を作る有限fold component。 -/
def verifiedXorDegreeSuffixParityIntoSlotPresenceCleanComponent
    {ancillaQubits systemQubits : Nat}
    (degreeFlags presentFlags : List (Wire ancillaQubits systemQubits))
    (degreeDisjointPresent : degreeFlags.Disjoint presentFlags) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := slotPresenceCircuit degreeFlags presentFlags
  reference := DegreeSuffixParitySlotPresenceXorSpec degreeFlags 0 presentFlags
  inputCondition := fun _ => True
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = DegreeSuffixParitySlotPresenceXorSpec degreeFlags 0 presentFlags input
  runBasis_correct := by
    intro input _
    exact runBasis_xorDegreeSuffixParityIntoSlotPresenceCircuit_eq_spec degreeFlags presentFlags 0 input
      degreeDisjointPresent
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- 一個の可逆Xを純粋なbit反転作用へ結ぶ全入力component。 -/
def verifiedFlipTargetBitCleanComponent
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := flipTargetBitCircuit target
  reference := FlipTargetBitReference target
  inputCondition := fun _ => True
  outputCondition := fun _ => True
  restoration := fun input output => output = FlipTargetBitReference target input
  runBasis_correct := by intro input _; rfl
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- compact decoder・slot presence・degree condition・定数1を順に合成したpersistent子木。 -/
noncomputable def verifiedComputeSharedPersistentFlagsCleanComponent
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p) (rowMode : Bool) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  let degree := oracleDegreeWires p
  let sources := if rowMode then degree.take (p.K - 1) else degree.drop 1
  CleanComponent.seq
    (verifiedXorDelimiterLegalityAndDegreeOneHotIntoTargetsCleanComponent p inputWires layout configuration)
    (CleanComponent.seq
      (verifiedXorDegreeSuffixParityIntoSlotPresenceCleanComponent degree (oraclePresentWires p)
        (oracleDegreeWires_disjoint_presentWires p))
      (CleanComponent.seq
        (verifiedXorSourceParityIntoTargetCleanComponent sources (oracleDegreeConditionWire p)
          (oracleDegreeConditionWire_not_mem_degreeConditionSources p rowMode))
        (verifiedFlipTargetBitCleanComponent (oracleOneWire p))))

/-- persistent子木のASTは既存の正本`computeSharedDecoderPresenceParityAndOneFlagsCircuit`と定義的に一致する。 -/
theorem verifiedComputeSharedPersistentFlagsCleanComponent_circuit
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p) (rowMode : Bool) :
    (verifiedComputeSharedPersistentFlagsCleanComponent p inputWires layout configuration
      rowMode).circuit = computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode := by
  simp [verifiedComputeSharedPersistentFlagsCleanComponent, verifiedXorDelimiterLegalityAndDegreeOneHotIntoTargetsCleanComponent,
    verifiedXorDegreeSuffixParityIntoSlotPresenceCleanComponent, verifiedXorSourceParityIntoTargetCleanComponent,
    verifiedFlipTargetBitCleanComponent,
    VerifiedCircuitCore.CleanComponent.seqWithConditions,
    computeSharedDecoderPresenceParityAndOneFlagsCircuit,
    slotPresenceCircuit, xorSourceParityIntoTargetCircuit, flipTargetBitCircuit]

/-- 共有persistent componentのreferenceは独立な四段階の解析関数合成である。 -/
theorem verifiedComputeSharedPersistentFlagsCleanComponent_reference
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p) (rowMode : Bool) :
    (verifiedComputeSharedPersistentFlagsCleanComponent p inputWires layout configuration
      rowMode).reference =
        SharedPersistentFlagsReference p inputWires configuration rowMode := by
  rfl

/-- column用のpersistent flag群を計算する回路。 -/
def computeColumnOracleLegalityDegreePresenceAndConditionsCircuit
    (p : QParameters) : Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false

/-- row用のpersistent flag群を計算する回路。 -/
def computeRowOracleLegalityDegreePresenceAndConditionsCircuit
    (p : QParameters) : Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true

/-- column入力仕様からpersistent子木の入れ子clean条件を構成する。 -/
theorem columnPersistentChildren_inputCondition
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnOracleInputSpec p configuration selector input) :
    (verifiedComputeSharedPersistentFlagsCleanComponent p (columnKeyWires p)
      (columnKeyWires_compactDecoderInputLayout p) configuration false).inputCondition
      input := by
  exact ⟨clean.persistentClean.decoder, trivial, trivial, trivial⟩

/-- row入力仕様からpersistent子木の入れ子clean条件を構成する。 -/
theorem rowPersistentChildren_inputCondition
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowOracleInputSpec p configuration selector input) :
    (verifiedComputeSharedPersistentFlagsCleanComponent p (systemWires p)
      (systemWires_compactDecoderInputLayout p) configuration true).inputCondition
      input := by
  exact ⟨clean.persistentClean.decoder, trivial, trivial, trivial⟩

/-- column persistent computeを四つの公開子componentから組み立てる。 -/
noncomputable def verifiedComputeColumnOraclePersistentConditionsCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := computeColumnOracleLegalityDegreePresenceAndConditionsCircuit p
  reference := SharedPersistentFlagsReference p (columnKeyWires p)
    configuration false
  inputCondition := ColumnOracleInputSpec p configuration selector
  outputCondition := ColumnOraclePersistentConditionsSpec p configuration selector
  restoration := fun _ output =>
    ColumnOraclePersistentConditionsSpec p configuration selector output
  runBasis_correct := by
    intro input clean
    rw [computeColumnOracleLegalityDegreePresenceAndConditionsCircuit,
      ← verifiedComputeSharedPersistentFlagsCleanComponent_circuit p
      (columnKeyWires p) (columnKeyWires_compactDecoderInputLayout p)
      configuration false]
    simpa [verifiedComputeSharedPersistentFlagsCleanComponent_reference] using
      (verifiedComputeSharedPersistentFlagsCleanComponent p (columnKeyWires p)
      (columnKeyWires_compactDecoderInputLayout p) configuration false).runBasis_correct
        input (columnPersistentChildren_inputCondition p configuration selector
          input clean)
  outputCondition_correct := by
    intro input clean
    have actualSpec := clean.afterPersistent
    have runEq :
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
            reversibleGatePermutation input =
          (verifiedComputeSharedPersistentFlagsCleanComponent p (columnKeyWires p)
            (columnKeyWires_compactDecoderInputLayout p) configuration
            false).reference input := by
      rw [← verifiedComputeSharedPersistentFlagsCleanComponent_circuit p
        (columnKeyWires p) (columnKeyWires_compactDecoderInputLayout p)
        configuration false]
      exact (verifiedComputeSharedPersistentFlagsCleanComponent p (columnKeyWires p)
        (columnKeyWires_compactDecoderInputLayout p) configuration
        false).runBasis_correct input
          (columnPersistentChildren_inputCondition p configuration selector
            input clean)
    rw [runEq] at actualSpec
    exact actualSpec
  restoration_correct := by
    intro input clean
    have actualSpec := clean.afterPersistent
    have runEq :
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
            reversibleGatePermutation input =
          (verifiedComputeSharedPersistentFlagsCleanComponent p (columnKeyWires p)
            (columnKeyWires_compactDecoderInputLayout p) configuration
            false).reference input := by
      rw [← verifiedComputeSharedPersistentFlagsCleanComponent_circuit p
        (columnKeyWires p) (columnKeyWires_compactDecoderInputLayout p)
        configuration false]
      exact (verifiedComputeSharedPersistentFlagsCleanComponent p (columnKeyWires p)
        (columnKeyWires_compactDecoderInputLayout p) configuration
        false).runBasis_correct input
          (columnPersistentChildren_inputCondition p configuration selector
            input clean)
    rw [runEq] at actualSpec
    exact actualSpec

/-- row persistent computeを四つの公開子componentから組み立てる。 -/
noncomputable def verifiedComputeRowOraclePersistentConditionsCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := computeRowOracleLegalityDegreePresenceAndConditionsCircuit p
  reference := SharedPersistentFlagsReference p (systemWires p) configuration true
  inputCondition := RowOracleInputSpec p configuration selector
  outputCondition := RowOraclePersistentConditionsSpec p configuration selector
  restoration := fun _ output =>
    RowOraclePersistentConditionsSpec p configuration selector output
  runBasis_correct := by
    intro input clean
    rw [computeRowOracleLegalityDegreePresenceAndConditionsCircuit,
      ← verifiedComputeSharedPersistentFlagsCleanComponent_circuit p
      (systemWires p) (systemWires_compactDecoderInputLayout p)
      configuration true]
    simpa [verifiedComputeSharedPersistentFlagsCleanComponent_reference] using
      (verifiedComputeSharedPersistentFlagsCleanComponent p (systemWires p)
      (systemWires_compactDecoderInputLayout p) configuration true).runBasis_correct
        input (rowPersistentChildren_inputCondition p configuration selector
          input clean)
  outputCondition_correct := by
    intro input clean
    have actualSpec := clean.afterPersistent
    have runEq :
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
            reversibleGatePermutation input =
          (verifiedComputeSharedPersistentFlagsCleanComponent p (systemWires p)
            (systemWires_compactDecoderInputLayout p) configuration true).reference
            input := by
      rw [← verifiedComputeSharedPersistentFlagsCleanComponent_circuit p
        (systemWires p) (systemWires_compactDecoderInputLayout p)
        configuration true]
      exact (verifiedComputeSharedPersistentFlagsCleanComponent p (systemWires p)
        (systemWires_compactDecoderInputLayout p) configuration
        true).runBasis_correct input
          (rowPersistentChildren_inputCondition p configuration selector
            input clean)
    rw [runEq] at actualSpec
    exact actualSpec
  restoration_correct := by
    intro input clean
    have actualSpec := clean.afterPersistent
    have runEq :
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
            reversibleGatePermutation input =
          (verifiedComputeSharedPersistentFlagsCleanComponent p (systemWires p)
            (systemWires_compactDecoderInputLayout p) configuration true).reference
            input := by
      rw [← verifiedComputeSharedPersistentFlagsCleanComponent_circuit p
        (systemWires p) (systemWires_compactDecoderInputLayout p)
        configuration true]
      exact (verifiedComputeSharedPersistentFlagsCleanComponent p (systemWires p)
        (systemWires_compactDecoderInputLayout p) configuration
        true).runBasis_correct input
          (rowPersistentChildren_inputCondition p configuration selector
            input clean)
    rw [runEq] at actualSpec
    exact actualSpec

/-- 通常のevent clean条件からcolumn event公開親の全clean条件を導く。 -/
theorem ColumnEventResultComputeUseUncomputeInput.ofEventSortClean
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    ColumnEventResultComputeUseUncomputeInput p slot offset input := by
  have computeClean := ColumnEventCandidateUpdateAndSortCleanInput.ofEventSortClean p slot offset
    input clean
  have computeEq :=
    (verifiedComputeColumnEventCandidateUpdateAndSortCleanComponent p slot offset).runBasis_correct
      input computeClean
  change (computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
    (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output at computeEq
  have outputEq : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output =
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output :=
    (columnEventCandidateUpdateAndSortExecutionTrace_output p slot offset input).trans computeEq
  have outputClean := columnEventCandidateUpdateAndSortExecutionTrace_output_clean_of_afterBranch p
    slot offset input
      (columnEventCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input clean)
  rw [outputEq] at outputClean
  refine ⟨computeClean, ?_⟩
  change SortedWriterCleanInput p
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output ∧
    WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset)
        (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output)
  exact ⟨⟨outputClean.scratch_zero, outputClean.pair_zero⟩,
    xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_movedSelectorClean_column p
      (columnEventDegreeChange offset)
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output outputClean⟩

/-- 通常のevent clean条件からrow event公開親の全clean条件を導く。 -/
theorem RowEventResultComputeUseUncomputeInput.ofEventSortClean
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    RowEventResultComputeUseUncomputeInput p slot offset input := by
  have computeClean := RowEventPredecessorCandidateUpdateAndSortCleanInput.ofEventSortClean p slot offset
    input clean
  have computeEq :=
    (verifiedComputeRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).runBasis_correct
      input computeClean
  change (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
    (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output at computeEq
  have outputEq : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output =
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output :=
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output p slot offset input).trans computeEq
  have outputClean := rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_clean_of_afterBranch p
    slot offset input
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input clean)
  rw [outputEq] at outputClean
  refine ⟨computeClean, ?_⟩
  change SortedWriterCleanInput p
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output ∧
    WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (rowEventDegreeChange offset)
        (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output)
  exact ⟨⟨outputClean.scratch_zero, outputClean.pair_zero⟩,
    xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_movedSelectorClean p
      (rowEventDegreeChange offset)
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output outputClean⟩

/-- column の一 selector 分岐を、対角または event の公開 component へ解析的に振り分ける。 -/
noncomputable def ColumnSelectorDiagonalOrEventDispatchReference
    (p : QParameters) (configuration : QConfiguration p)
    (branch : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let slot := selectorSlot branch
  let offset := selectorOffset branch
  if diagonal : offset.val < 2 then
    (verifiedColumnDiagonalResultComputeUseUncomputeCleanComponent p slot
      ⟨offset.val, diagonal⟩ true
      (decide (slot.val < configuration.1.card))).reference input
  else
    (verifiedApplyColumnEventReferenceAndRestoreWorkCleanComponent p slot offset).reference input

/-- row の一 selector 分岐を、対角または event の公開 component へ解析的に振り分ける。 -/
noncomputable def RowSelectorDiagonalOrEventDispatchReference
    (p : QParameters) (configuration : QConfiguration p)
    (branch : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let slot := selectorSlot branch
  let offset := selectorOffset branch
  if diagonal : offset.val < 2 then
    (verifiedRowDiagonalResultComputeUseUncomputeCleanComponent p slot
      ⟨offset.val, diagonal⟩ true
      (decide (slot.val < configuration.1.card))).reference input
  else
    (verifiedApplyRowEventReferenceAndRestoreWorkCleanComponent p slot offset).reference input

/-- column branch-at の実回路作用は、振り分け先の公開 component reference に一致する。 -/
theorem runBasis_dispatchColumnSelectorToDiagonalOrEventCircuit_eq_childReference
    (p : QParameters) (configuration : QConfiguration p)
    (active branch : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnOraclePersistentConditionsSpec p configuration active input) :
    (dispatchColumnSelectorToDiagonalOrEventCircuit p branch).runBasis reversibleGatePermutation input =
      ColumnSelectorDiagonalOrEventDispatchReference p configuration branch input := by
  let slot := selectorSlot branch
  let offset := selectorOffset branch
  unfold dispatchColumnSelectorToDiagonalOrEventCircuit
  by_cases diagonal : offset.val < 2
  · rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal p slot offset diagonal]
    simp only [ColumnSelectorDiagonalOrEventDispatchReference, slot, offset, diagonal,
      dite_true]
    have childResult := (verifiedColumnDiagonalResultComputeUseUncomputeCleanComponent p slot
      ⟨offset.val, diagonal⟩ true
      (decide (slot.val < configuration.1.card))).runBasis_correct input
        (clean.diagonalClean slot)
    change (columnDiagonalResultComputeUseUncomputeCircuit p slot ⟨offset.val, diagonal⟩).runBasis
      reversibleGatePermutation input = _ at childResult
    exact childResult
  · rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset diagonal]
    simp only [ColumnSelectorDiagonalOrEventDispatchReference, slot, offset, diagonal,
      dite_false]
    have childResult :=
      (verifiedApplyColumnEventReferenceAndRestoreWorkCleanComponent p slot offset).runBasis_correct
        input (ColumnEventResultComputeUseUncomputeInput.ofEventSortClean p slot offset input
          clean.event_clean)
    change (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
      reversibleGatePermutation input = _ at childResult
    exact childResult

/-- row branch-at の実回路作用は、振り分け先の公開 component reference に一致する。 -/
theorem runBasis_dispatchRowSelectorToDiagonalOrEventCircuit_eq_childReference
    (p : QParameters) (configuration : QConfiguration p)
    (active branch : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowOraclePersistentConditionsSpec p configuration active input) :
    (dispatchRowSelectorToDiagonalOrEventCircuit p branch).runBasis reversibleGatePermutation input =
      RowSelectorDiagonalOrEventDispatchReference p configuration branch input := by
  let slot := selectorSlot branch
  let offset := selectorOffset branch
  unfold dispatchRowSelectorToDiagonalOrEventCircuit
  by_cases diagonal : offset.val < 2
  · rw [dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal p slot offset diagonal]
    simp only [RowSelectorDiagonalOrEventDispatchReference, slot, offset, diagonal,
      dite_true]
    have childResult := (verifiedRowDiagonalResultComputeUseUncomputeCleanComponent p slot
      ⟨offset.val, diagonal⟩ true
      (decide (slot.val < configuration.1.card))).runBasis_correct input
        (clean.diagonalClean slot)
    change (rowDiagonalResultComputeUseUncomputeCircuit p slot ⟨offset.val, diagonal⟩).runBasis
      reversibleGatePermutation input = _ at childResult
    exact childResult
  · rw [dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset diagonal]
    simp only [RowSelectorDiagonalOrEventDispatchReference, slot, offset, diagonal,
      dite_false]
    have childResult :=
      (verifiedApplyRowEventReferenceAndRestoreWorkCleanComponent p slot offset).runBasis_correct
        input (RowEventResultComputeUseUncomputeInput.ofEventSortClean p slot offset input
          clean.event_clean)
    change (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
      reversibleGatePermutation input = _ at childResult
    exact childResult

/-- column の child reference は persistent 解析条件を保存する。 -/
theorem dispatchColumnSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent
    (p : QParameters) (configuration : QConfiguration p)
    (active branch : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnOraclePersistentConditionsSpec p configuration active input) :
    ColumnOraclePersistentConditionsSpec p configuration active
      (ColumnSelectorDiagonalOrEventDispatchReference p configuration branch input) := by
  let slot := selectorSlot branch
  let offset := selectorOffset branch
  by_cases diagonal : offset.val < 2
  · simp only [ColumnSelectorDiagonalOrEventDispatchReference, offset, diagonal,
      dite_true]
    apply clean.of_supportAgreement
    intro wire supportMember
    have result := (verifiedColumnDiagonalResultComputeUseUncomputeCleanComponent p slot
      ⟨offset.val, diagonal⟩ true
      (decide (slot.val < configuration.1.card))).restoration_correct input
        (clean.diagonalClean slot)
    exact result.outside_restored wire
      ((List.disjoint_left.mp (columnEventCandidateUpdateAndSortSupport_disjoint_rowOutput p))
        supportMember)
      ((List.disjoint_left.mp
        (columnEventCandidateUpdateAndSortSupport_disjoint_selectorOutput p)) supportMember)
      (by
        intro equal
        subst wire
        exact negativeWire_not_mem_columnEventCandidateUpdateAndSortSupport p supportMember)
      (by
        intro equal
        subst wire
        exact activeWire_not_mem_columnEventCandidateUpdateAndSortSupport p supportMember)
  · simp only [ColumnSelectorDiagonalOrEventDispatchReference, offset, diagonal,
      dite_false]
    apply clean.of_supportAgreement
    exact (verifiedApplyColumnEventReferenceAndRestoreWorkCleanComponent p slot offset).restoration_correct
      input (ColumnEventResultComputeUseUncomputeInput.ofEventSortClean p slot offset input
        clean.event_clean) |>.observation_correct.support_restored

/-- row の child reference は persistent 解析条件を保存する。 -/
theorem dispatchRowSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent
    (p : QParameters) (configuration : QConfiguration p)
    (active branch : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowOraclePersistentConditionsSpec p configuration active input) :
    RowOraclePersistentConditionsSpec p configuration active
      (RowSelectorDiagonalOrEventDispatchReference p configuration branch input) := by
  let slot := selectorSlot branch
  let offset := selectorOffset branch
  by_cases diagonal : offset.val < 2
  · simp only [RowSelectorDiagonalOrEventDispatchReference, offset, diagonal,
      dite_true]
    apply clean.of_broadAgreement
    intro wire supportMember
    have result := (verifiedRowDiagonalResultComputeUseUncomputeCleanComponent p slot
      ⟨offset.val, diagonal⟩ true
      (decide (slot.val < configuration.1.card))).restoration_correct input
        (clean.diagonalClean slot)
    exact result.outside_restored wire
      ((List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnKey p))
        supportMember)
      ((List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnSelector p))
        supportMember)
      (by
        intro equal
        subst wire
        exact keySignalWire_not_mem_rowEventBroadSupport p supportMember)
  · simp only [RowSelectorDiagonalOrEventDispatchReference, offset, diagonal,
      dite_false]
    apply clean.of_broadAgreement
    exact (verifiedApplyRowEventReferenceAndRestoreWorkCleanComponent p slot offset).restoration_correct
      input (RowEventResultComputeUseUncomputeInput.ofEventSortClean p slot offset input
        clean.event_clean) |>.observation_correct.support_restored
/-- column branch-at を公開 child 契約から得る clean component。 -/
noncomputable def verifiedDispatchColumnSelectorToDiagonalOrEventCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (active branch : QSelector p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := dispatchColumnSelectorToDiagonalOrEventCircuit p branch
  reference := ColumnSelectorDiagonalOrEventDispatchReference p configuration branch
  inputCondition := ColumnOraclePersistentConditionsSpec p configuration active
  outputCondition := ColumnOraclePersistentConditionsSpec p configuration active
  restoration := fun input output =>
    output = ColumnSelectorDiagonalOrEventDispatchReference p configuration branch input ∧
      ColumnOraclePersistentConditionsSpec p configuration active output
  runBasis_correct := runBasis_dispatchColumnSelectorToDiagonalOrEventCircuit_eq_childReference
    p configuration active branch
  outputCondition_correct := dispatchColumnSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent
    p configuration active branch
  restoration_correct := by
    intro input clean
    exact ⟨rfl, dispatchColumnSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent p
      configuration active branch input clean⟩

/-- row branch-at を公開 child 契約から得る clean component。 -/
noncomputable def verifiedDispatchRowSelectorToDiagonalOrEventCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (active branch : QSelector p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := dispatchRowSelectorToDiagonalOrEventCircuit p branch
  reference := RowSelectorDiagonalOrEventDispatchReference p configuration branch
  inputCondition := RowOraclePersistentConditionsSpec p configuration active
  outputCondition := RowOraclePersistentConditionsSpec p configuration active
  restoration := fun input output =>
    output = RowSelectorDiagonalOrEventDispatchReference p configuration branch input ∧
      RowOraclePersistentConditionsSpec p configuration active output
  runBasis_correct := runBasis_dispatchRowSelectorToDiagonalOrEventCircuit_eq_childReference
    p configuration active branch
  outputCondition_correct := dispatchRowSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent
    p configuration active branch
  restoration_correct := by
    intro input clean
    exact ⟨rfl, dispatchRowSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent p
      configuration active branch input clean⟩

/-- clean component 列の回路等式は共有 core の一般合成則を直接再利用する。 -/
abbrev cleanSequenceComponents_circuit :=
  @VerifiedCircuitCore.CleanComponent.sequenceComponents_circuit

/-- column branch component 族を任意の selector 列に沿って合成する。 -/
noncomputable def verifiedColumnSelectorBranchSequenceCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) (branches : List (QSelector p)) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  CleanComponent.sequenceComponents reversibleGatePermutation
    (branches.map fun branch =>
      verifiedDispatchColumnSelectorToDiagonalOrEventCleanComponent p configuration active branch)

/-- row branch component 族を任意の selector 列に沿って合成する。 -/
noncomputable def verifiedRowSelectorBranchSequenceCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) (branches : List (QSelector p)) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  CleanComponent.sequenceComponents reversibleGatePermutation
    (branches.map fun branch =>
      verifiedDispatchRowSelectorToDiagonalOrEventCleanComponent p configuration active branch)

/-- persistent 条件は column branch component 列の各中間入力条件を帰納的に供給する。 -/
theorem columnBranchComponentSequence_inputCondition
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) (branches : List (QSelector p))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnOraclePersistentConditionsSpec p configuration active input) :
    (verifiedColumnSelectorBranchSequenceCleanComponent p configuration active
      branches).inputCondition input := by
  induction branches generalizing input with
  | nil => trivial
  | cons branch branches inductionHypothesis =>
      change ColumnOraclePersistentConditionsSpec p configuration active input ∧
        (verifiedColumnSelectorBranchSequenceCleanComponent p configuration active
          branches).inputCondition
          (ColumnSelectorDiagonalOrEventDispatchReference p configuration branch input)
      exact ⟨clean, inductionHypothesis _
        (dispatchColumnSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent p configuration
          active branch input clean)⟩

/-- persistent 条件は row branch component 列の各中間入力条件を帰納的に供給する。 -/
theorem rowBranchComponentSequence_inputCondition
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) (branches : List (QSelector p))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowOraclePersistentConditionsSpec p configuration active input) :
    (verifiedRowSelectorBranchSequenceCleanComponent p configuration active
      branches).inputCondition input := by
  induction branches generalizing input with
  | nil => trivial
  | cons branch branches inductionHypothesis =>
      change RowOraclePersistentConditionsSpec p configuration active input ∧
        (verifiedRowSelectorBranchSequenceCleanComponent p configuration active
          branches).inputCondition
          (RowSelectorDiagonalOrEventDispatchReference p configuration branch input)
      exact ⟨clean, inductionHypothesis _
        (dispatchRowSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent p configuration
          active branch input clean)⟩

/-- column branch component 列の解析 reference は persistent 条件を保存する。 -/
theorem columnBranchComponentSequence_preservesPersistent
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) (branches : List (QSelector p))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnOraclePersistentConditionsSpec p configuration active input) :
    ColumnOraclePersistentConditionsSpec p configuration active
      ((verifiedColumnSelectorBranchSequenceCleanComponent p configuration active
        branches).reference input) := by
  induction branches generalizing input with
  | nil => exact clean
  | cons branch branches inductionHypothesis =>
      exact inductionHypothesis _
        (dispatchColumnSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent p configuration
          active branch input clean)

/-- row branch component 列の解析 reference は persistent 条件を保存する。 -/
theorem rowBranchComponentSequence_preservesPersistent
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) (branches : List (QSelector p))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowOraclePersistentConditionsSpec p configuration active input) :
    RowOraclePersistentConditionsSpec p configuration active
      ((verifiedRowSelectorBranchSequenceCleanComponent p configuration active
        branches).reference input) := by
  induction branches generalizing input with
  | nil => exact clean
  | cons branch branches inductionHypothesis =>
      exact inductionHypothesis _
        (dispatchRowSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent p configuration
          active branch input clean)

/-- 全column selector branchを正本順にfoldする回路。 -/
def foldAllColumnSelectorBranchesCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  Circuit.sequence (columnOracleBranchList p)

/-- 全row selector branchを正本順にfoldする回路。 -/
def foldAllRowSelectorBranchesCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  Circuit.sequence (rowOracleBranchList p)

/-- column branch familyの有限fold参照。 -/
noncomputable def FoldedColumnSelectorBranchesReference
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth →
      JointBasis p.ancillaWidth p.systemWidth :=
  (verifiedColumnSelectorBranchSequenceCleanComponent p configuration
    active (List.ofFn fun branch : QSelector p => branch)).reference

/-- row branch familyの有限fold参照。 -/
noncomputable def FoldedRowSelectorBranchesReference
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth →
      JointBasis p.ancillaWidth p.systemWidth :=
  (verifiedRowSelectorBranchSequenceCleanComponent p configuration
    active (List.ofFn fun branch : QSelector p => branch)).reference

noncomputable def verifiedFoldAllColumnSelectorBranchesCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := foldAllColumnSelectorBranchesCircuit p
  reference := FoldedColumnSelectorBranchesReference p configuration active
  inputCondition := ColumnOraclePersistentConditionsSpec p configuration active
  outputCondition := ColumnOraclePersistentConditionsSpec p configuration active
  restoration := fun input output =>
    output = (verifiedColumnSelectorBranchSequenceCleanComponent p configuration
      active (List.ofFn fun branch : QSelector p => branch)).reference input ∧
      ColumnOraclePersistentConditionsSpec p configuration active output
  runBasis_correct := by
    intro input clean
    have childResult :=
      (verifiedColumnSelectorBranchSequenceCleanComponent p configuration active
        (List.ofFn fun branch : QSelector p => branch)).runBasis_correct input
          (columnBranchComponentSequence_inputCondition p configuration active
            _ input clean)
    change Circuit.runBasis reversibleGatePermutation
      (CleanComponent.sequenceComponents reversibleGatePermutation
      ((List.ofFn fun branch : QSelector p => branch).map fun branch =>
        verifiedDispatchColumnSelectorToDiagonalOrEventCleanComponent p configuration active branch)).circuit
        input = _ at childResult
    rw [cleanSequenceComponents_circuit] at childResult
    have circuitListEq :
        (((List.ofFn fun branch : QSelector p => branch).map fun branch =>
          verifiedDispatchColumnSelectorToDiagonalOrEventCleanComponent p configuration active branch).map
            fun component => component.circuit) =
          List.ofFn (dispatchColumnSelectorToDiagonalOrEventCircuit p) := by
      simp only [List.map_ofFn]
      apply congrArg List.ofFn
      funext branch
      rfl
    rw [circuitListEq] at childResult
    rw [← columnOracleBranchList_eq_ofFn] at childResult
    exact childResult
  outputCondition_correct := by
    intro input clean
    exact columnBranchComponentSequence_preservesPersistent p configuration
      active _ input clean
  restoration_correct := by
    intro input clean
    exact ⟨rfl, columnBranchComponentSequence_preservesPersistent p configuration
      active _ input clean⟩

/-- 全 (6K) row branch の有限 fold を公開する component。 -/
noncomputable def verifiedFoldAllRowSelectorBranchesCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := foldAllRowSelectorBranchesCircuit p
  reference := FoldedRowSelectorBranchesReference p configuration active
  inputCondition := RowOraclePersistentConditionsSpec p configuration active
  outputCondition := RowOraclePersistentConditionsSpec p configuration active
  restoration := fun input output =>
    output = (verifiedRowSelectorBranchSequenceCleanComponent p configuration
      active (List.ofFn fun branch : QSelector p => branch)).reference input ∧
      RowOraclePersistentConditionsSpec p configuration active output
  runBasis_correct := by
    intro input clean
    have childResult :=
      (verifiedRowSelectorBranchSequenceCleanComponent p configuration active
        (List.ofFn fun branch : QSelector p => branch)).runBasis_correct input
          (rowBranchComponentSequence_inputCondition p configuration active
            _ input clean)
    change Circuit.runBasis reversibleGatePermutation
      (CleanComponent.sequenceComponents reversibleGatePermutation
      ((List.ofFn fun branch : QSelector p => branch).map fun branch =>
        verifiedDispatchRowSelectorToDiagonalOrEventCleanComponent p configuration active branch)).circuit
        input = _ at childResult
    rw [cleanSequenceComponents_circuit] at childResult
    have circuitListEq :
        (((List.ofFn fun branch : QSelector p => branch).map fun branch =>
          verifiedDispatchRowSelectorToDiagonalOrEventCleanComponent p configuration active branch).map
            fun component => component.circuit) =
          List.ofFn (dispatchRowSelectorToDiagonalOrEventCircuit p) := by
      simp only [List.map_ofFn]
      apply congrArg List.ofFn
      funext branch
      rfl
    rw [circuitListEq] at childResult
    rw [← rowOracleBranchList_eq_ofFn] at childResult
    exact childResult
  outputCondition_correct := by
    intro input clean
    exact rowBranchComponentSequence_preservesPersistent p configuration
      active _ input clean
  restoration_correct := by
    intro input clean
    exact ⟨rfl, rowBranchComponentSequence_preservesPersistent p configuration
      active _ input clean⟩

/-- 一つの column branch reference は外側 uncompute の persistent support を保存する。 -/
theorem dispatchColumnSelectorToDiagonalOrEventCircuitChildReference_agreesPersistentSupport
    (p : QParameters) (configuration : QConfiguration p)
    (active branch : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnOraclePersistentConditionsSpec p configuration active input) :
    BasisAgreeOn (columnOraclePersistentSupport p)
      (ColumnSelectorDiagonalOrEventDispatchReference p configuration branch input) input := by
  let slot := selectorSlot branch
  let offset := selectorOffset branch
  by_cases diagonal : offset.val < 2
  · simp only [ColumnSelectorDiagonalOrEventDispatchReference, offset, diagonal, dite_true]
    intro wire supportMember
    have eventMember :=
      columnOraclePersistentSupport_subset_columnEventCandidateUpdateAndSortSupport p wire
        supportMember
    have result := (verifiedColumnDiagonalResultComputeUseUncomputeCleanComponent p slot
      ⟨offset.val, diagonal⟩ true
      (decide (slot.val < configuration.1.card))).restoration_correct input
        (clean.diagonalClean slot)
    exact result.outside_restored wire
      ((List.disjoint_left.mp (columnEventCandidateUpdateAndSortSupport_disjoint_rowOutput p))
        eventMember)
      ((List.disjoint_left.mp
        (columnEventCandidateUpdateAndSortSupport_disjoint_selectorOutput p)) eventMember)
      (by
        intro equal
        subst wire
        exact negativeWire_not_mem_columnEventCandidateUpdateAndSortSupport p eventMember)
      (by
        intro equal
        subst wire
        exact activeWire_not_mem_columnEventCandidateUpdateAndSortSupport p eventMember)
  · simp only [ColumnSelectorDiagonalOrEventDispatchReference, offset, diagonal, dite_false]
    intro wire supportMember
    exact (verifiedApplyColumnEventReferenceAndRestoreWorkCleanComponent p slot offset).restoration_correct
      input (ColumnEventResultComputeUseUncomputeInput.ofEventSortClean p slot offset input
        clean.event_clean) |>.observation_correct.support_restored wire
          (columnOraclePersistentSupport_subset_columnEventCandidateUpdateAndSortSupport p wire
            supportMember)

/-- 一つの row branch reference は外側 uncompute の persistent support を保存する。 -/
theorem dispatchRowSelectorToDiagonalOrEventCircuitChildReference_agreesPersistentSupport
    (p : QParameters) (configuration : QConfiguration p)
    (active branch : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowOraclePersistentConditionsSpec p configuration active input) :
    BasisAgreeOn (rowOraclePersistentSupport p)
      (RowSelectorDiagonalOrEventDispatchReference p configuration branch input) input := by
  let slot := selectorSlot branch
  let offset := selectorOffset branch
  by_cases diagonal : offset.val < 2
  · simp only [RowSelectorDiagonalOrEventDispatchReference, offset, diagonal, dite_true]
    intro wire supportMember
    have broadMember := rowOraclePersistentSupport_subset_rowEventBroadSupport p
      wire supportMember
    have result := (verifiedRowDiagonalResultComputeUseUncomputeCleanComponent p slot
      ⟨offset.val, diagonal⟩ true
      (decide (slot.val < configuration.1.card))).restoration_correct input
        (clean.diagonalClean slot)
    exact result.outside_restored wire
      ((List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnKey p))
        broadMember)
      ((List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnSelector p))
        broadMember)
      (by
        intro equal
        subst wire
        exact keySignalWire_not_mem_rowEventBroadSupport p broadMember)
  · simp only [RowSelectorDiagonalOrEventDispatchReference, offset, diagonal, dite_false]
    intro wire supportMember
    exact (verifiedApplyRowEventReferenceAndRestoreWorkCleanComponent p slot offset).restoration_correct
      input (RowEventResultComputeUseUncomputeInput.ofEventSortClean p slot offset input
        clean.event_clean) |>.observation_correct.support_restored wire
          (rowOraclePersistentSupport_subset_rowEventBroadSupport p wire
            supportMember)

/-- column branch の任意有限列は persistent support を保存する。 -/
theorem columnBranchComponentSequence_agreesPersistentSupport
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) (branches : List (QSelector p))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnOraclePersistentConditionsSpec p configuration active input) :
    BasisAgreeOn (columnOraclePersistentSupport p)
      ((verifiedColumnSelectorBranchSequenceCleanComponent p configuration active
        branches).reference input) input := by
  induction branches generalizing input with
  | nil => intro _ _; rfl
  | cons branch branches inductionHypothesis =>
      have firstAgreement :=
        dispatchColumnSelectorToDiagonalOrEventCircuitChildReference_agreesPersistentSupport p
          configuration active branch input clean
      have firstClean :=
        dispatchColumnSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent p configuration
          active branch input clean
      have tailAgreement := inductionHypothesis _ firstClean
      intro wire member
      exact (tailAgreement wire member).trans (firstAgreement wire member)

/-- row branch の任意有限列は persistent support を保存する。 -/
theorem rowBranchComponentSequence_agreesPersistentSupport
    (p : QParameters) (configuration : QConfiguration p)
    (active : QSelector p) (branches : List (QSelector p))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowOraclePersistentConditionsSpec p configuration active input) :
    BasisAgreeOn (rowOraclePersistentSupport p)
      ((verifiedRowSelectorBranchSequenceCleanComponent p configuration active
        branches).reference input) input := by
  induction branches generalizing input with
  | nil => intro _ _; rfl
  | cons branch branches inductionHypothesis =>
      have firstAgreement :=
        dispatchRowSelectorToDiagonalOrEventCircuitChildReference_agreesPersistentSupport p configuration
          active branch input clean
      have firstClean :=
        dispatchRowSelectorToDiagonalOrEventCircuitChildReference_preservesPersistent p configuration
          active branch input clean
      have tailAgreement := inductionHypothesis _ firstClean
      intro wire member
      exact (tailAgreement wire member).trans (firstAgreement wire member)

/-- column oracle の子 reference 合成を、外側 support 復元まで含む純粋関数にする。 -/
noncomputable def ColumnOraclePersistentBranchFoldReference
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let persistent := (verifiedComputeColumnOraclePersistentConditionsCleanComponent p
    configuration selector).reference input
  let branches := (verifiedFoldAllColumnSelectorBranchesCleanComponent p configuration
    selector).reference persistent
  restoreSupport (columnOraclePersistentSupport p) input branches

/-- row oracle の子 reference 合成を、外側 support 復元まで含む純粋関数にする。 -/
noncomputable def RowOraclePersistentBranchFoldReference
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let persistent := (verifiedComputeRowOraclePersistentConditionsCleanComponent p
    configuration selector).reference input
  let branches := (verifiedFoldAllRowSelectorBranchesCleanComponent p configuration
    selector).reference persistent
  restoreSupport (rowOraclePersistentSupport p) input branches

/-- column oracle 全体の実作用を persistent・finite fold・外側 C-U-U から合成する。 -/
theorem runBasis_applyColumnOracleReferenceAndRestoreWorkCircuit_eq_persistentBranchFoldReference
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnOracleInputSpec p configuration selector input) :
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input =
      ColumnOraclePersistentBranchFoldReference p configuration selector input := by
  let persistentComponent :=
    verifiedComputeColumnOraclePersistentConditionsCleanComponent p configuration selector
  let branchComponent :=
    verifiedFoldAllColumnSelectorBranchesCleanComponent p configuration selector
  have persistentEq := persistentComponent.runBasis_correct input clean
  change (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
    reversibleGatePermutation input = persistentComponent.reference input
      at persistentEq
  have persistentClean := persistentComponent.outputCondition_correct input clean
  have branchEq := branchComponent.runBasis_correct
    (persistentComponent.reference input) persistentClean
  change (Circuit.sequence (columnOracleBranchList p)).runBasis
    reversibleGatePermutation (persistentComponent.reference input) =
      branchComponent.reference (persistentComponent.reference input) at branchEq
  have branchPreserves : BasisAgreeOn (columnOraclePersistentSupport p)
      ((Circuit.sequence (columnOracleBranchList p)).runBasis
        reversibleGatePermutation
        ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
          reversibleGatePermutation input))
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input) := by
    rw [persistentEq, branchEq]
    exact columnBranchComponentSequence_agreesPersistentSupport p configuration
      selector _ (persistentComponent.reference input) persistentClean
  rw [applyColumnOracleReferenceAndRestoreWorkCircuit_eq_restorePersistentSupport p input
    branchPreserves]
  rw [persistentEq, branchEq]
  rfl

/-- row oracle 全体の実作用を persistent・finite fold・外側 C-U-U から合成する。 -/
theorem runBasis_applyRowOracleReferenceAndRestoreWorkCircuit_eq_persistentBranchFoldReference
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowOracleInputSpec p configuration selector input) :
    (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input =
      RowOraclePersistentBranchFoldReference p configuration selector input := by
  let persistentComponent :=
    verifiedComputeRowOraclePersistentConditionsCleanComponent p configuration selector
  let branchComponent :=
    verifiedFoldAllRowSelectorBranchesCleanComponent p configuration selector
  have persistentEq := persistentComponent.runBasis_correct input clean
  change (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
    reversibleGatePermutation input = persistentComponent.reference input
      at persistentEq
  have persistentClean := persistentComponent.outputCondition_correct input clean
  have branchEq := branchComponent.runBasis_correct
    (persistentComponent.reference input) persistentClean
  change (Circuit.sequence (rowOracleBranchList p)).runBasis
    reversibleGatePermutation (persistentComponent.reference input) =
      branchComponent.reference (persistentComponent.reference input) at branchEq
  have branchPreserves : BasisAgreeOn (rowOraclePersistentSupport p)
      ((Circuit.sequence (rowOracleBranchList p)).runBasis
        reversibleGatePermutation
        ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
          reversibleGatePermutation input))
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input) := by
    rw [persistentEq, branchEq]
    exact rowBranchComponentSequence_agreesPersistentSupport p configuration
      selector _ (persistentComponent.reference input) persistentClean
  rw [applyRowOracleReferenceAndRestoreWorkCircuit_eq_restorePersistentSupport p input
    branchPreserves]
  rw [persistentEq, branchEq]
  rfl

/-- 既存のwire-level解析完全性を用い、子合成referenceを独立なcolumn oracle仕様へ同定する境界補題。 -/
theorem identifyColumnOracleImplementationWithRestoredReference
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnOracleInputSpec p configuration selector input) :
    ColumnOracleRestoredReferenceIdentification p configuration selector input
      (ColumnOraclePersistentBranchFoldReference p configuration selector input) := by
  have actualSpec := identifyCompiledColumnOracleCircuitWithRestoredReference configuration
    selector input clean
  rw [runBasis_applyColumnOracleReferenceAndRestoreWorkCircuit_eq_persistentBranchFoldReference p
    configuration selector input clean] at actualSpec
  exact actualSpec

/-- 既存のwire-level解析完全性を用い、子合成referenceを独立なrow oracle仕様へ同定する境界補題。 -/
theorem identifyRowOracleImplementationWithRestoredReference
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowOracleInputSpec p configuration selector input) :
    RowOracleRestoredReferenceIdentification p configuration selector input
      (RowOraclePersistentBranchFoldReference p configuration selector input) := by
  have actualSpec := identifyCompiledRowOracleCircuitWithRestoredReference configuration
    selector input clean
  rw [runBasis_applyRowOracleReferenceAndRestoreWorkCircuit_eq_persistentBranchFoldReference p
    configuration selector input clean] at actualSpec
  exact actualSpec

/-- column oracle の解析仕様は、入力 configuration・selector・clean work を保存する。 -/
theorem ColumnOracleRestoredReferenceIdentification.preservesInputSpec
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (clean : ColumnOracleInputSpec p configuration selector input)
    (result : ColumnOracleRestoredReferenceIdentification p configuration selector input output) :
    ColumnOracleInputSpec p configuration selector output := by
  have agreement : BasisAgreeOn (columnEventCandidateUpdateAndSortSupport p) output input := by
    intro wire supportMember
    exact result.outside_restored wire
      ((List.disjoint_left.mp (columnEventCandidateUpdateAndSortSupport_disjoint_rowOutput p))
        supportMember)
      ((List.disjoint_left.mp
        (columnEventCandidateUpdateAndSortSupport_disjoint_selectorOutput p)) supportMember)
      (by
        intro equal
        subst wire
        exact negativeWire_not_mem_columnEventCandidateUpdateAndSortSupport p supportMember)
      (by
        intro equal
        subst wire
        exact activeWire_not_mem_columnEventCandidateUpdateAndSortSupport p supportMember)
  refine { column_key_bits := ?_, selector_bits := ?_, work_zero := ?_ }
  · calc
      readWires (columnKeyWires p) output =
          readWires (columnKeyWires p) input := by
        apply List.map_congr_left
        intro wire member
        exact agreement wire (by simp [columnEventCandidateUpdateAndSortSupport, member])
      _ = registerBitList (delimiterEncoding configuration) := clean.column_key_bits
  · calc
      readWires (columnSelectorWires p) output =
          readWires (columnSelectorWires p) input := by
        apply List.map_congr_left
        intro wire member
        exact agreement wire (by simp [columnEventCandidateUpdateAndSortSupport, member])
      _ = constantBits selector.val (columnSelectorWires p).length :=
        clean.selector_bits
  · intro wire member
    exact (agreement wire (by simp [columnEventCandidateUpdateAndSortSupport, member])).trans
      (clean.work_zero wire member)

/-- row oracle の解析仕様は、入力 configuration・selector・clean work を保存する。 -/
theorem RowOracleRestoredReferenceIdentification.preservesInputSpec
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (clean : RowOracleInputSpec p configuration selector input)
    (result : RowOracleRestoredReferenceIdentification p configuration selector input output) :
    RowOracleInputSpec p configuration selector output := by
  have agreement : BasisAgreeOn (rowEventBroadSupport p) output input := by
    intro wire supportMember
    exact result.outside_restored wire
      ((List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnKey p))
        supportMember)
      ((List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnSelector p))
        supportMember)
      (by
        intro equal
        subst wire
        exact keySignalWire_not_mem_rowEventBroadSupport p supportMember)
  refine { system_bits := ?_, selector_bits := ?_, work_zero := ?_ }
  · calc
      readWires (systemWires p) output = readWires (systemWires p) input := by
        apply List.map_congr_left
        intro wire member
        exact agreement wire (by simp [rowEventBroadSupport, member])
      _ = registerBitList (delimiterEncoding configuration) := clean.system_bits
  · calc
      readWires (rowSelectorWires p) output =
          readWires (rowSelectorWires p) input := by
        apply List.map_congr_left
        intro wire member
        exact agreement wire (by simp [rowEventBroadSupport, member])
      _ = constantBits selector.val (rowSelectorWires p).length :=
        clean.selector_bits
  · intro wire member
    exact (agreement wire (by simp [rowEventBroadSupport, member])).trans
      (clean.work_zero wire member)

/-- column oracle の外部観測作用と全非出力wire復元をpure generic契約へ代入した仕様。 -/
def ColumnOracleRestoredReferenceSpec
    (p : QParameters) (configuration : QConfiguration p) (selector : QSelector p)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  RestoredObservationSpec
    (fun source target => observeColumnOracle p target =
      columnOracleAnalyticAction configuration selector (observeColumnOracle p source))
    (fun source target => ∀ wire,
      wire ∉ rowOutputWires p → wire ∉ selectorOutputWires p →
        wire ≠ negativeWire p → wire ≠ activeWire p →
          target wire = source wire)
    input output

/-- pure generic column oracle契約を、旧physical仕様へ変換する薄い解析bridge。 -/
theorem ColumnOracleRestoredReferenceSpec.toPhysical
    {p : QParameters} {configuration : QConfiguration p} {selector : QSelector p}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (spec : ColumnOracleRestoredReferenceSpec p configuration selector input output) :
    ColumnOracleRestoredReferenceIdentification p configuration selector input output := by
  exact {
    observation := spec.observation_correct
    outside_restored := spec.restoration_correct }

/-- 旧physical column oracle仕様を、pure generic契約へ閉じ込める薄い解析bridge。 -/
theorem ColumnOracleRestoredReferenceSpec.ofPhysical
    {p : QParameters} {configuration : QConfiguration p} {selector : QSelector p}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (spec : ColumnOracleRestoredReferenceIdentification p configuration selector input output) :
    ColumnOracleRestoredReferenceSpec p configuration selector input output := by
  exact {
    observation_correct := spec.observation
    restoration_correct := spec.outside_restored }

/-- column oracle のpure generic契約は全物理wire上で出力を一意に定める。 -/
theorem ColumnOracleRestoredReferenceSpec.unique
    {p : QParameters} {configuration : QConfiguration p} {selector : QSelector p}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : ColumnOracleRestoredReferenceSpec p configuration selector input left)
    (rightSpec : ColumnOracleRestoredReferenceSpec p configuration selector input right) :
    left = right :=
  leftSpec.toPhysical.unique rightSpec.toPhysical

/-- row oracle の外部観測作用と全非出力wire復元をpure generic契約へ代入した仕様。 -/
def RowOracleRestoredReferenceSpec
    (p : QParameters) (configuration : QConfiguration p) (selector : QSelector p)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  RestoredObservationSpec
    (fun source target => observeRowOracle p target =
      rowOracleAnalyticAction configuration selector (observeRowOracle p source))
    (fun source target => ∀ wire,
      wire ∉ columnKeyWires p → wire ∉ columnSelectorWires p →
        wire ≠ keySignalWire p → target wire = source wire)
    input output

/-- pure generic row oracle契約を、旧physical仕様へ変換する薄い解析bridge。 -/
theorem RowOracleRestoredReferenceSpec.toPhysical
    {p : QParameters} {configuration : QConfiguration p} {selector : QSelector p}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (spec : RowOracleRestoredReferenceSpec p configuration selector input output) :
    RowOracleRestoredReferenceIdentification p configuration selector input output := by
  exact {
    observation := spec.observation_correct
    outside_restored := spec.restoration_correct }

/-- 旧physical row oracle仕様を、pure generic契約へ閉じ込める薄い解析bridge。 -/
theorem RowOracleRestoredReferenceSpec.ofPhysical
    {p : QParameters} {configuration : QConfiguration p} {selector : QSelector p}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (spec : RowOracleRestoredReferenceIdentification p configuration selector input output) :
    RowOracleRestoredReferenceSpec p configuration selector input output := by
  exact {
    observation_correct := spec.observation
    restoration_correct := spec.outside_restored }

/-- row oracle のpure generic契約は全物理wire上で出力を一意に定める。 -/
theorem RowOracleRestoredReferenceSpec.unique
    {p : QParameters} {configuration : QConfiguration p} {selector : QSelector p}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : RowOracleRestoredReferenceSpec p configuration selector input left)
    (rightSpec : RowOracleRestoredReferenceSpec p configuration selector input right) :
    left = right :=
  leftSpec.toPhysical.unique rightSpec.toPhysical

/--
column oracle の階層実装が、子 component から合成した参照関数どおりに動くことを保持する。
解析的な正本参照関数への同定はまだ行わず、実装合成と解析同定の証明境界を分離する。
-/
noncomputable def verifiedColumnOraclePersistentComputeBranchFoldUncomputeCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := columnOraclePersistentComputeBranchFoldUncomputeCircuit p
  reference := ColumnOraclePersistentBranchFoldReference p configuration selector
  inputCondition := ColumnOracleInputSpec p configuration selector
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = ColumnOraclePersistentBranchFoldReference p configuration selector input
  runBasis_correct :=
    runBasis_applyColumnOracleReferenceAndRestoreWorkCircuit_eq_persistentBranchFoldReference p
      configuration selector
  outputCondition_correct := by simp
  restoration_correct := by intro input _; rfl

/--
column oracle の実装参照関数を、回路非依存の解析的正本参照関数へ精密化する。
`basisSpecBridge` はこの精密化の同定証拠にだけ用い、子 component の実装証明を展開しない。
-/
noncomputable def verifiedApplyColumnOracleReferenceAndRestoreWorkCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  CleanComponent.refineReference
    (verifiedColumnOraclePersistentComputeBranchFoldUncomputeCleanComponent p configuration selector)
    (uniqueAnalyticReference
      (ColumnOracleRestoredReferenceSpec p configuration selector))
    (ColumnOracleInputSpec p configuration selector)
    (ColumnOracleInputSpec p configuration selector)
    (ColumnOracleRestoredReferenceSpec p configuration selector)
    (by intro _ clean; exact clean)
    (by
      intro input clean
      have composedSpec := ColumnOracleRestoredReferenceSpec.ofPhysical
        (identifyColumnOracleImplementationWithRestoredReference p configuration selector
          input clean)
      have uniqueOutput : ∃! output,
          ColumnOracleRestoredReferenceSpec p configuration selector input output :=
        ⟨ColumnOraclePersistentBranchFoldReference p configuration selector input, composedSpec,
          fun other otherSpec => otherSpec.unique composedSpec⟩
      exact (uniqueAnalyticReference_eq uniqueOutput composedSpec).symm)
    (by
      intro input clean
      have composedSpec := ColumnOracleRestoredReferenceSpec.ofPhysical
        (identifyColumnOracleImplementationWithRestoredReference p configuration selector
          input clean)
      have uniqueOutput : ∃! output,
          ColumnOracleRestoredReferenceSpec p configuration selector input output :=
        ⟨ColumnOraclePersistentBranchFoldReference p configuration selector input, composedSpec,
          fun other otherSpec => otherSpec.unique composedSpec⟩
      exact (uniqueAnalyticReference_spec uniqueOutput).toPhysical.preservesInputSpec clean)
    (by
      intro input clean
      have composedSpec := ColumnOracleRestoredReferenceSpec.ofPhysical
        (identifyColumnOracleImplementationWithRestoredReference p configuration selector
          input clean)
      have uniqueOutput : ∃! output,
          ColumnOracleRestoredReferenceSpec p configuration selector input output :=
        ⟨ColumnOraclePersistentBranchFoldReference p configuration selector input, composedSpec,
          fun other otherSpec => otherSpec.unique composedSpec⟩
      exact uniqueAnalyticReference_spec uniqueOutput)

/--
row oracle の階層実装が、子 component から合成した参照関数どおりに動くことを保持する。
解析的な正本参照関数への同定はまだ行わず、実装合成と解析同定の証明境界を分離する。
-/
noncomputable def verifiedRowOraclePersistentComputeBranchFoldUncomputeCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := rowOraclePersistentComputeBranchFoldUncomputeCircuit p
  reference := RowOraclePersistentBranchFoldReference p configuration selector
  inputCondition := RowOracleInputSpec p configuration selector
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = RowOraclePersistentBranchFoldReference p configuration selector input
  runBasis_correct := runBasis_applyRowOracleReferenceAndRestoreWorkCircuit_eq_persistentBranchFoldReference p
    configuration selector
  outputCondition_correct := by simp
  restoration_correct := by intro input _; rfl

/--
row oracle の実装参照関数を、回路非依存の解析的正本参照関数へ精密化する。
`basisSpecBridge` はこの精密化の同定証拠にだけ用い、子 component の実装証明を展開しない。
-/
noncomputable def verifiedApplyRowOracleReferenceAndRestoreWorkCleanComponent
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  CleanComponent.refineReference
    (verifiedRowOraclePersistentComputeBranchFoldUncomputeCleanComponent p configuration selector)
    (uniqueAnalyticReference
      (RowOracleRestoredReferenceSpec p configuration selector))
    (RowOracleInputSpec p configuration selector)
    (RowOracleInputSpec p configuration selector)
    (RowOracleRestoredReferenceSpec p configuration selector)
    (by intro _ clean; exact clean)
    (by
      intro input clean
      have composedSpec := RowOracleRestoredReferenceSpec.ofPhysical
        (identifyRowOracleImplementationWithRestoredReference p configuration selector
          input clean)
      have uniqueOutput : ∃! output,
          RowOracleRestoredReferenceSpec p configuration selector input output :=
        ⟨RowOraclePersistentBranchFoldReference p configuration selector input, composedSpec,
          fun other otherSpec => otherSpec.unique composedSpec⟩
      exact (uniqueAnalyticReference_eq uniqueOutput composedSpec).symm)
    (by
      intro input clean
      have composedSpec := RowOracleRestoredReferenceSpec.ofPhysical
        (identifyRowOracleImplementationWithRestoredReference p configuration selector
          input clean)
      have uniqueOutput : ∃! output,
          RowOracleRestoredReferenceSpec p configuration selector input output :=
        ⟨RowOraclePersistentBranchFoldReference p configuration selector input, composedSpec,
          fun other otherSpec => otherSpec.unique composedSpec⟩
      exact (uniqueAnalyticReference_spec uniqueOutput).toPhysical.preservesInputSpec clean)
    (by
      intro input clean
      have composedSpec := RowOracleRestoredReferenceSpec.ofPhysical
        (identifyRowOracleImplementationWithRestoredReference p configuration selector
          input clean)
      have uniqueOutput : ∃! output,
          RowOracleRestoredReferenceSpec p configuration selector input output :=
        ⟨RowOraclePersistentBranchFoldReference p configuration selector input, composedSpec,
          fun other otherSpec => otherSpec.unique composedSpec⟩
      exact uniqueAnalyticReference_spec uniqueOutput)

end ReversibleCircuit

end ProbabilityGeneratorQProof
