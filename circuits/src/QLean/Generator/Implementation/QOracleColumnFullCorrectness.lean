import QLean.Generator.Implementation.QOracleColumnCanonicalComplete

/-!
# Q column oracle の一般基底作用

このファイルでは、外部出力 register を任意の XOR accumulator として残したまま、
column-key、column-selector、oracle work のみを指定する一般入力から、全 `6K` 分岐と
persistent uncompute を含む column oracle の基底作用を証明する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/--
Column oracle の一般入力仕様。外部の row-output、selector-output、negative、active は
任意の XOR accumulator でよく、ここでは入力 configuration、selector、clean work だけを要求する。
-/
structure ColumnOracleInputSpec (p : QParameters)
    (configuration : QConfiguration p) (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- column-key register は入力 configuration の delimiter 符号である。 -/
  column_key_bits : readWires (columnKeyWires p) input =
    registerBitList (delimiterEncoding configuration)
  /-- column-selector register は指定 selector の little-endian 定数 bit 列である。 -/
  selector_bits : readWires (columnSelectorWires p) input =
    constantBits selector.val (columnSelectorWires p).length
  /-- canonical oracle work の全 wire は 0 で初期化されている。 -/
  work_zero : ∀ wire ∈ diagonalOracleWorkWires p, input wire = false

/-- 一般 column oracle 入力では、任意の canonical oracle slice が 0 である。 -/
theorem ColumnOracleInputSpec.slice_zero
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleInputSpec p configuration selector input)
    {width : Nat} (slice : RegisterSlice p.oracleWorkWidth width) :
    ∀ wire ∈ ((QLayout.oracleSlice slice).wireList :
      List (Wire p.ancillaWidth p.systemWidth)), input wire = false := by
  intro wire member
  exact specification.work_zero wire (by
    simpa [diagonalOracleWorkWires] using
      oracleSliceWire_mem_oracleWork p slice member)

/-- 一般 column oracle 入力は persistent decoder の clean 条件を満たす。 -/
theorem ColumnOracleInputSpec.persistentClean
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleInputSpec p configuration selector input) :
    OraclePersistentCleanInput p (columnKeyWires p) configuration input := by
  refine {
    decoder := {
      input_bits := specification.column_key_bits
      suffix_zero := ?_
      degree_zero := ?_
      compare_zero := ?_
      and_zero := ?_
      legal_zero := ?_ }
    present_zero := ?_
    special_zero := ?_ }
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).candidate
    simpa [decoderSuffixWires, RegisterSlice.wireList] using
      List.mem_of_mem_take member
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).degree
    simpa [oracleDegreeWires, RegisterSlice.wireList] using member
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).compareWork
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member
  · intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).andWork
    simpa [oracleAndWorkWires, RegisterSlice.wireList] using member
  · apply specification.slice_zero (OracleWorkLayout.canonical p).legal
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).legal).ancillaWire 0 ∈ _
    simp [RegisterSlice.wireList]
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).present
    simpa [oraclePresentWires, RegisterSlice.wireList] using member
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact specification.slice_zero (oraclePersistentSpecialSlice p) wire
      (by simpa [oraclePersistentSpecialWires] using member)

/-- 一般 column oracle 入力に対する persistent compute の数学的出力仕様。 -/
theorem ColumnOracleInputSpec.persistentOutput
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleInputSpec p configuration selector input) :
    OraclePersistentOutputSpec p configuration false
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input) := by
  exact computeSharedDecoderPresenceParityAndOneFlagsCircuit_correct_of_clean p (columnKeyWires p)
    (columnKeyWires_oraclePersistentInputLayout p) configuration input
    specification.persistentClean false

/-- 一般 column oracle 入力は event candidate/sort の全 clean 条件も満たす。 -/
theorem ColumnOracleInputSpec.eventSortClean
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleInputSpec p configuration selector input) :
    EventSortCleanInput p input := by
  refine {
    moved_selector := {
      compare_zero := ?_
      scratch_zero := ?_
      position_zero := ?_
      pair_zero := ?_ }
    sort_compare_zero := ?_
    sort_scratch_zero := ?_
    sort_history_zero := ?_ }
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).compareWork
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member
  · intro wire member
    exact specification.work_zero wire
      (decoderAndScratchWire_mem_diagonalOracleWorkWires p member)
  · apply specification.slice_zero (OracleWorkLayout.canonical p).positionMatch
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).positionMatch).ancillaWire _ ∈ _
    simp [RegisterSlice.wireList]
  · apply specification.slice_zero (OracleWorkLayout.canonical p).pair
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).pair).ancillaWire _ ∈ _
    simp [RegisterSlice.wireList]
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    simp only [sortCompareWorkWires, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with compareMember | extraMember
    · apply specification.slice_zero
        (OracleWorkLayout.canonical p).compareWork
      simpa [RegisterSlice.wireList] using compareMember
    · subst wire
      apply specification.slice_zero (OracleWorkLayout.canonical p).andWork
      simp [RegisterSlice.wireList]
  · intro wire member
    rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
    apply specification.slice_zero (OracleWorkLayout.canonical p).andWork
    rw [RegisterSlice.wireList]
    apply List.mem_map.mpr
    exact ⟨⟨index.val + 1, by
      simp [QParameters.andWorkWidth] at index ⊢
      omega⟩, List.mem_finRange _, rfl⟩
  · intro instruction instructionMember
    apply specification.slice_zero (OracleWorkLayout.canonical p).sortFlags
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history, rfl⟩

/-- column-selector は column-key と canonical oracle-work の双方と交わらない。 -/
theorem columnSelectorWires_disjoint_columnKeyAndOracleWork (p : QParameters) :
    (columnSelectorWires p).Disjoint
      (columnKeyWires p ++ diagonalOracleWorkWires p) := by
  rw [List.disjoint_append_right]
  exact ⟨(columnKeyWires_disjoint_columnSelectorWires p).symm,
    columnSelectorWires_disjoint_diagonalOracleWork p⟩

/--
一般 delimiter・selector・全 0 work から persistent compute を実行すると、各 event branch が
必要とする persistent 入力仕様が、外部 accumulator に仮定を置かずに得られる。
-/
theorem ColumnOracleInputSpec.afterPersistent
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleInputSpec p configuration selector input) :
    ColumnOraclePersistentConditionsSpec p configuration selector
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input) := by
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
    reversibleGatePermutation input
  have persistentClean := specification.persistentClean
  have persistentOutput := specification.persistentOutput
  have persistentUses : circuitUsesOnly
      (columnKeyWires p ++ diagonalOracleWorkWires p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false) := by
    simpa using columnOraclePersistentCompute_usesOnly p
  have preservePre {width : Nat}
      (slice : RegisterSlice p.oracleWorkWidth width)
      (degreeBefore : (OracleWorkLayout.canonical p).degree.start +
        p.degreeWidth ≤ slice.start)
      (specialBefore : (oraclePersistentSpecialSlice p).start + 2 ≤ slice.start)
      (beforeCandidate : slice.start + width ≤
        (OracleWorkLayout.canonical p).candidate.start)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
      persistent wire = input wire := by
    simpa [persistent] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_preCandidateSlice p (columnKeyWires p)
        (columnKeyWires_disjoint_diagonalOracleWorkWires p) false input slice
          degreeBefore specialBefore beforeCandidate wire member
  have preserveMiddle {width : Nat}
      (slice : RegisterSlice p.oracleWorkWidth width)
      (candidateBefore : (OracleWorkLayout.canonical p).candidate.start +
        p.candidateWidth ≤ slice.start)
      (beforeCompare : slice.start + width ≤
        (OracleWorkLayout.canonical p).compareWork.start)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
      persistent wire = input wire := by
    simpa [persistent] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_middleOracleSlice p (columnKeyWires p)
        (columnKeyWires_disjoint_diagonalOracleWorkWires p) false input slice
          candidateBefore beforeCompare wire member
  have preserveCandidate
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth))) :
      persistent wire = input wire := by
    simpa [persistent] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_candidateSlice p (columnKeyWires p)
        (columnKeyWires_candidateInputLayout p) false input wire member
  have inputSliceZero {width : Nat}
      (slice : RegisterSlice p.oracleWorkWidth width)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) : input wire = false :=
    specification.work_zero wire
      (diagonalOracleSlice_subset_work p slice member)
  refine {
    selector_bits := ?_
    column_key_bits := ?_
    present := ?_
    active_word := ?_
    degree := ?_
    legal := persistentOutput.legal
    degree_condition := by simpa using persistentOutput.degreeCondition
    selected_zero := ?_
    moved_zero := ?_
    membership_zero := ?_
    branch_zero := ?_
    candidate_zero := ?_
    event_clean := ?_ }
  · calc
      readWires (columnSelectorWires p) persistent =
          readWires (columnSelectorWires p) input := by
        exact readWires_runBasis_of_usesOnly_disjoint
          (columnKeyWires p ++ diagonalOracleWorkWires p)
          (columnSelectorWires p)
          (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false) input
          persistentUses
          (columnSelectorWires_disjoint_columnKeyAndOracleWork p).symm
      _ = constantBits selector.val (columnSelectorWires p).length :=
        specification.selector_bits
  · simpa [persistent] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_input_preserved_of_clean p (columnKeyWires p)
        (columnKeyWires_oraclePersistentInputLayout p) configuration input
          persistentClean false
  · intro slot
    simpa [persistent] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_present_value_of_clean p (columnKeyWires p)
        (columnKeyWires_oraclePersistentInputLayout p) configuration input
          persistentClean false slot
  · intro slot active
    simpa [persistent, siteWordBits] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_activeWord_of_clean p (columnKeyWires p)
        (columnKeyWires_oraclePersistentInputLayout p) configuration input
          persistentClean false slot active
  · intro slot
    have point := congrArg (fun values : List Bool =>
      values[slot.val]?.getD false) persistentOutput.degree
    change persistent (oracleDegreeWireAt p slot) = _
    simpa [persistent, readWires, oracleDegreeWires, oracleDegreeWireAt,
      QParameters.degreeWidth, slot.isLt,
      degreeOneHotFrom_getD_of_lt p.K configuration.1.card 0 slot.val slot.isLt]
      using point
  · change persistent (oracleSelectedWire p) = false
    rw [preservePre (OracleWorkLayout.canonical p).selected]
    · exact inputSliceZero (OracleWorkLayout.canonical p).selected _
        (by simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList])
    · simp [OracleWorkLayout.canonical]
      omega
    · simp [oraclePersistentSpecialSlice, OracleWorkLayout.canonical]
    · simp [OracleWorkLayout.canonical]
    · simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
  · intro wire member
    change persistent wire = false
    rw [preservePre (OracleWorkLayout.canonical p).moved]
    · exact inputSliceZero (OracleWorkLayout.canonical p).moved wire
        (by simpa [oracleMovedWires, RegisterSlice.wireList] using member)
    · simp [OracleWorkLayout.canonical]
      omega
    · simp [oraclePersistentSpecialSlice, OracleWorkLayout.canonical]
    · simp [OracleWorkLayout.canonical]
    · simpa [oracleMovedWires, RegisterSlice.wireList] using member
  · refine {
      equal_zero := ?_
      good_zero := ?_
      present_other_zero := ?_
      absent_zero := ?_ }
    · intro slot
      change persistent (membershipEqualWireAt p slot) = false
      rw [preserveMiddle (OracleWorkLayout.canonical p).membershipEqual]
      · exact inputSliceZero (OracleWorkLayout.canonical p).membershipEqual _
          (membershipEqualWireAt_mem_slice p slot)
      · simp [OracleWorkLayout.canonical]
      · simp [OracleWorkLayout.canonical]
        omega
      · exact membershipEqualWireAt_mem_slice p slot
    · intro slot
      change persistent (membershipGoodWireAt p slot) = false
      rw [preserveMiddle (OracleWorkLayout.canonical p).membershipGood]
      · exact inputSliceZero (OracleWorkLayout.canonical p).membershipGood _
          (membershipGoodWireAt_mem_slice p slot)
      · simp [OracleWorkLayout.canonical]
        omega
      · simp [OracleWorkLayout.canonical]
        omega
      · exact membershipGoodWireAt_mem_slice p slot
    · change persistent (oraclePresentOtherWire p) = false
      rw [preserveMiddle (OracleWorkLayout.canonical p).presentOther]
      · exact inputSliceZero (OracleWorkLayout.canonical p).presentOther _
          (oraclePresentOtherWire_mem_slice p)
      · simp [OracleWorkLayout.canonical]
        omega
      · simp [OracleWorkLayout.canonical]
        omega
      · exact oraclePresentOtherWire_mem_slice p
    · change persistent (oracleAbsentWire p) = false
      rw [preserveMiddle (OracleWorkLayout.canonical p).absent]
      · exact inputSliceZero (OracleWorkLayout.canonical p).absent _
          (oracleAbsentWire_mem_slice p)
      · simp [OracleWorkLayout.canonical]
        omega
      · simp [OracleWorkLayout.canonical]
        omega
      · exact oracleAbsentWire_mem_slice p
  · change persistent (oracleBranchWire p) = false
    rw [preserveMiddle (OracleWorkLayout.canonical p).branch]
    · exact inputSliceZero (OracleWorkLayout.canonical p).branch _
        (by simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList])
    · simp [OracleWorkLayout.canonical]
      omega
    · simp [OracleWorkLayout.canonical]
      omega
    · simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
  · refine {
      data_zero := ?_
      marker_zero := ?_ }
    · intro word
      change readWires ((candidateWordAt p word).take p.wordWidth) persistent = _
      have pointwise : ∀ wire ∈ (candidateWordAt p word).take p.wordWidth,
          persistent wire = false := by
        intro wire member
        rw [preserveCandidate wire
          (candidateWordAt_mem_candidateSlice p word
            (List.mem_of_mem_take member))]
        exact inputSliceZero (OracleWorkLayout.canonical p).candidate wire
          (candidateWordAt_mem_candidateSlice p word
            (List.mem_of_mem_take member))
      simpa using readWires_eq_replicate_false_of_forall
        ((candidateWordAt p word).take p.wordWidth) persistent pointwise
    · intro word
      change persistent (candidateMarkerWire p word) = false
      rw [preserveCandidate (candidateMarkerWire p word)
        (candidateWordAt_mem_candidateSlice p word (by
          simp [candidateMarkerWire, candidateWordAt]))]
      exact inputSliceZero (OracleWorkLayout.canonical p).candidate _
        (candidateWordAt_mem_candidateSlice p word (by
          simp [candidateMarkerWire, candidateWordAt]))
  · simpa [persistent] using
      columnOraclePersistentOutput_eventSortClean p configuration input
        persistentClean specification.eventSortClean

/-- 固定幅に収まる二つの自然数では、little-endian 定数 bit 列の一致と数値の一致は同値である。 -/
theorem columnConstantBits_eq_constantBits_iff_of_lt
    {left right width : Nat} (leftLt : left < 2 ^ width)
    (rightLt : right < 2 ^ width) :
    constantBits left width = constantBits right width ↔ left = right := by
  constructor
  · intro bitsEqual
    apply Nat.eq_of_testBit_eq
    intro index
    by_cases inRange : index < width
    · have point := congrArg (fun bits : List Bool => bits[index]?) bitsEqual
      rw [constantBits_getElem? left width index inRange,
        constantBits_getElem? right width index inRange] at point
      exact Option.some.inj point
    · have widthLe : width ≤ index := Nat.le_of_not_gt inRange
      have leftIndexLt : left < 2 ^ index :=
        lt_of_lt_of_le leftLt (Nat.pow_le_pow_right (by decide) widthLe)
      have rightIndexLt : right < 2 ^ index :=
        lt_of_lt_of_le rightLt (Nat.pow_le_pow_right (by decide) widthLe)
      rw [Nat.testBit_lt_two_pow leftIndexLt,
        Nat.testBit_lt_two_pow rightIndexLt]
  · rintro rfl
    rfl

/--
Persistent selector と異なる event branch は、内部 compute を実行しても selected=false のため、
compute--use--uncompute 全体で入力基底を厳密に固定する。
-/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_selector_ne
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentConditionsSpec p configuration selector input)
    (different : selector ≠ selectorOfSlotOffset slot offset) :
    (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorConstantDifferent : selector.val ≠ 6 * slot.val + offset.val := by
    intro equal
    apply different
    apply Fin.ext
    simpa [selectorOfSlotOffset] using equal
  have selectorMatches : columnEventSelectorMatches p slot offset input = false := by
    unfold columnEventSelectorMatches diagonalSelectorMatches
    rw [specification.selector_bits]
    apply decide_eq_false
    intro bitsEqual
    apply selectorConstantDifferent
    exact (columnConstantBits_eq_constantBits_iff_of_lt
      (qSelector_lt_capacity p selector)
      (qSelector_lt_capacity p (selectorOfSlotOffset slot offset))).mp
        (by simpa [selectorOfSlotOffset, columnSelectorWires] using bitsEqual)
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_columnEventSelectorCompute p slot offset input
      specification.event_clean
  have movedClean : EventSortCleanInput p states.afterMoveForward := by
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.movedCopy_eq]
      exact EventSortCleanInput.of_columnEventMovedCopy p slot _ selectorClean
    rw [states.moveForward_eq]
    exact EventSortCleanInput.of_columnEventMoveForward p offset _ copiedClean
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    rw [states.membership_eq]
    exact EventSortCleanInput.of_columnEventMembership p slot _ movedClean
  have membershipSlotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) states.afterMoveForward := {
    equalWork_zero := movedClean.moved_selector.compare_zero
    scratch_zero := movedClean.moved_selector.scratch_zero }
  have selectedAfterSelector : states.afterSelector (oracleSelectedWire p) =
      false := by
    rw [states.selector_eq, runBasis_columnEventSelectorCompute p slot offset input
      specification.event_clean.moved_selector.scratch_zero, selectorMatches]
    exact specification.selected_zero
  have selectedAfterMembership : states.afterMembership (oracleSelectedWire p) =
      false := by
    have selectedOutside : oracleSelectedWire p ∉ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).moved).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      intro movedMember
      have selectedMember : oracleSelectedWire p ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).selected).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
      have disjoint :
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).selected).wireList :
              List (Wire p.ancillaWidth p.systemWidth)).Disjoint
            ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).moved).wireList :
                List (Wire p.ancillaWidth p.systemWidth)) := by
        apply RegisterSlice.wireList_disjoint_of_end_le_start
        simp [QLayout.oracleSlice, RegisterSlice.compose,
          OracleWorkLayout.canonical]
      exact (List.disjoint_left.mp disjoint) selectedMember movedMember
    have selectedAfterMove : states.afterMoveForward (oracleSelectedWire p) =
        false := by
      rw [states.moveForward_eq, states.movedCopy_eq]
      exact (runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
        states.afterSelector selectorClean _ selectedOutside).trans
          selectedAfterSelector
    rw [states.membership_eq]
    exact (runBasis_columnEventMembership_preserves_branch_inputs p slot
      states.afterMoveForward membershipSlotClean).2.1.trans
          selectedAfterMove
  have branchZeroAfterMembership : states.afterMembership
      (oracleBranchWire p) = false := by
    have branchOutside : oracleBranchWire p ∉ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).moved).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      intro movedMember
      have branchMember : oracleBranchWire p ∈ ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).branch).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
      exact (List.disjoint_left.mp
        (RegisterSlice.wireList_disjoint_of_end_le_start
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).branch)
          (by simp [QLayout.oracleSlice, RegisterSlice.compose,
            OracleWorkLayout.canonical]; omega))) movedMember branchMember
    have branchDifferent : oracleBranchWire p ≠ oracleSelectedWire p := by
      intro equal
      have branchMember : oracleBranchWire p ∈ ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).branch).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
      have selectedMember : oracleSelectedWire p ∈ ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).selected).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
      exact (oracleSliceMembers_ne_of_end_le_start p
        (OracleWorkLayout.canonical p).selected
        (OracleWorkLayout.canonical p).branch
        (by
          simp [OracleWorkLayout.canonical]
          omega)
        selectedMember branchMember) equal.symm
    have branchAfterSelector : states.afterSelector (oracleBranchWire p) =
        input (oracleBranchWire p) := by
      rw [states.selector_eq]
      exact runBasis_columnEventSelectorCompute_other p slot offset input
        specification.event_clean _ branchDifferent
    have afterMoveZero : states.afterMoveForward (oracleBranchWire p) = false := by
      rw [states.moveForward_eq, states.movedCopy_eq]
      exact (runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
        states.afterSelector selectorClean _ branchOutside).trans
          (branchAfterSelector.trans specification.branch_zero)
    rw [states.membership_eq]
    exact (runBasis_columnEventMembership_preserves_branch_inputs p slot
      states.afterMoveForward membershipSlotClean).2.2.2.2.trans
          afterMoveZero
  have branchFalse : states.afterBranch (oracleBranchWire p) = false := by
    rw [states.branch_eq]
    exact runBasis_columnEventBranchCompute_false_of_selected_canonical p slot
      offset states.afterMembership membershipClean.moved_selector.scratch_zero
        branchZeroAfterMembership selectedAfterMembership
  apply applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_afterBranch p slot offset input
  · exact columnEventCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input
      specification.event_clean
  · exact branchFalse

/--
Selector は一致するが configuration の粒子数以上にある padding event slot は、present=false
によって branch が不活性となり、入力基底を厳密に固定する。
-/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_padding
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (padding : configuration.1.card ≤ slot.val)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentConditionsSpec p configuration
      (selectorOfSlotOffset slot offset) input) :
    (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_columnEventSelectorCompute p slot offset input
      specification.event_clean
  have movedClean : EventSortCleanInput p states.afterMoveForward := by
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.movedCopy_eq]
      exact EventSortCleanInput.of_columnEventMovedCopy p slot _ selectorClean
    rw [states.moveForward_eq]
    exact EventSortCleanInput.of_columnEventMoveForward p offset _ copiedClean
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    rw [states.membership_eq]
    exact EventSortCleanInput.of_columnEventMembership p slot _ movedClean
  have membershipSlotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) states.afterMoveForward := {
    equalWork_zero := movedClean.moved_selector.compare_zero
    scratch_zero := movedClean.moved_selector.scratch_zero }
  have presentOutside : oraclePresentWireAt p slot ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
    intro movedMember
    have presentMember : oraclePresentWireAt p slot ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).present).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oraclePresentWireAt, RegisterSlice.wireList]
    exact (List.disjoint_left.mp
      (RegisterSlice.wireList_disjoint_of_end_le_start
        (QLayout.oracleSlice (OracleWorkLayout.canonical p).present)
        (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
        (by simp [QLayout.oracleSlice, RegisterSlice.compose,
          OracleWorkLayout.canonical]; omega))) presentMember movedMember
  have presentDifferent : oraclePresentWireAt p slot ≠ oracleSelectedWire p := by
    have presentMember : oraclePresentWireAt p slot ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).present).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oraclePresentWireAt, RegisterSlice.wireList]
    have selectedMember : oracleSelectedWire p ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).selected).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
    exact oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).present
      (OracleWorkLayout.canonical p).selected
      (by
        simp [OracleWorkLayout.canonical]
        omega) presentMember selectedMember
  have presentAfterSelector : states.afterSelector
      (oraclePresentWireAt p slot) = input (oraclePresentWireAt p slot) := by
    rw [states.selector_eq]
    exact runBasis_columnEventSelectorCompute_other p slot offset input
      specification.event_clean _ presentDifferent
  have presentInputFalse : input (oraclePresentWireAt p slot) = false := by
    rw [specification.present slot]
    simp [Nat.not_lt.mpr padding]
  have presentAfterMove : states.afterMoveForward (oraclePresentWireAt p slot) =
      false := by
    rw [states.moveForward_eq, states.movedCopy_eq]
    exact (runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
      states.afterSelector selectorClean _ presentOutside).trans
        (presentAfterSelector.trans presentInputFalse)
  have branchZeroAfterMove : states.afterMoveForward (oracleBranchWire p) =
      false := by
    have branchOutside : oracleBranchWire p ∉ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).moved).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      intro movedMember
      have branchMember : oracleBranchWire p ∈ ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).branch).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
      exact (List.disjoint_left.mp
        (RegisterSlice.wireList_disjoint_of_end_le_start
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).branch)
          (by simp [QLayout.oracleSlice, RegisterSlice.compose,
            OracleWorkLayout.canonical]; omega))) movedMember branchMember
    have branchDifferent : oracleBranchWire p ≠ oracleSelectedWire p := by
      intro equal
      have branchMember : oracleBranchWire p ∈ ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).branch).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
      have selectedMember : oracleSelectedWire p ∈ ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).selected).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
      exact (oracleSliceMembers_ne_of_end_le_start p
        (OracleWorkLayout.canonical p).selected
        (OracleWorkLayout.canonical p).branch
        (by
          simp [OracleWorkLayout.canonical]
          omega)
        selectedMember branchMember) equal.symm
    have branchAfterSelector : states.afterSelector (oracleBranchWire p) =
        input (oracleBranchWire p) := by
      rw [states.selector_eq]
      exact runBasis_columnEventSelectorCompute_other p slot offset input
        specification.event_clean _ branchDifferent
    rw [states.moveForward_eq, states.movedCopy_eq]
    exact (runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
      states.afterSelector selectorClean _ branchOutside).trans
        (branchAfterSelector.trans specification.branch_zero)
  have preserved := runBasis_columnEventMembership_preserves_branch_inputs p slot
    states.afterMoveForward membershipSlotClean
  have presentAfterMembership : states.afterMembership
      (oraclePresentWireAt p slot) = false := by
    rw [states.membership_eq]
    exact preserved.2.2.1.trans presentAfterMove
  have branchZeroAfterMembership : states.afterMembership
      (oracleBranchWire p) = false := by
    rw [states.membership_eq]
    exact preserved.2.2.2.2.trans branchZeroAfterMove
  have branchFalse : states.afterBranch (oracleBranchWire p) = false := by
    rw [states.branch_eq]
    exact runBasis_columnEventBranchCompute_false_of_present_canonical p slot
      offset states.afterMembership membershipClean.moved_selector.scratch_zero
        branchZeroAfterMembership presentAfterMembership
  apply applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_afterBranch p slot offset input
  · exact columnEventCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input
      specification.event_clean
  · exact branchFalse

/--
Column event compute support 上で入力と一致する状態は、同じ configuration と selector の
persistent 入力仕様を満たす。外部 accumulator の XOR 後状態へ仕様を移すために使う。
-/
theorem ColumnOraclePersistentConditionsSpec.of_supportAgreement
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOraclePersistentConditionsSpec p configuration selector input)
    (agreement : BasisAgreeOn (columnEventCandidateUpdateAndSortSupport p) output input) :
    ColumnOraclePersistentConditionsSpec p configuration selector output := by
  have selectorAgree : readWires (columnSelectorWires p) output =
      readWires (columnSelectorWires p) input := by
    apply List.map_congr_left
    intro wire member
    exact agreement wire (by simp [columnEventCandidateUpdateAndSortSupport, member])
  have keyAgree : readWires (columnKeyWires p) output =
      readWires (columnKeyWires p) input := by
    apply List.map_congr_left
    intro wire member
    exact agreement wire (by simp [columnEventCandidateUpdateAndSortSupport, member])
  have workAgree : ∀ wire ∈ diagonalOracleWorkWires p,
      output wire = input wire := by
    intro wire member
    exact agreement wire (List.mem_append_right _ member)
  have sliceAgree {width : Nat} (slice : RegisterSlice p.oracleWorkWidth width)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
      output wire = input wire :=
    workAgree wire (diagonalOracleSlice_subset_work p slice member)
  refine {
    selector_bits := selectorAgree.trans specification.selector_bits
    column_key_bits := keyAgree.trans specification.column_key_bits
    present := ?_
    active_word := ?_
    degree := ?_
    legal := ?_
    degree_condition := ?_
    selected_zero := ?_
    moved_zero := ?_
    membership_zero := ?_
    branch_zero := ?_
    candidate_zero := ?_
    event_clean := ?_ }
  · intro slot
    rw [sliceAgree (OracleWorkLayout.canonical p).present]
    · exact specification.present slot
    · change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).present).ancillaWire slot ∈ _
      simp [RegisterSlice.wireList]
  · intro slot active
    calc
      readWires (registerWordAt p (columnKeyWires p) slot) output =
          readWires (registerWordAt p (columnKeyWires p) slot) input := by
        apply List.map_congr_left
        intro wire member
        apply agreement wire
        have keyMember : wire ∈ columnKeyWires p :=
          List.mem_of_mem_drop (List.mem_of_mem_take member)
        simp [columnEventCandidateUpdateAndSortSupport, keyMember]
      _ = siteWordBits p (configuration.siteAt ⟨slot.val, active⟩) :=
        specification.active_word slot active
  · intro slot
    rw [sliceAgree (OracleWorkLayout.canonical p).degree]
    · exact specification.degree slot
    · change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).degree).ancillaWire slot ∈ _
      simp [RegisterSlice.wireList]
  · rw [sliceAgree (OracleWorkLayout.canonical p).legal]
    · exact specification.legal
    · simp [oracleLegalWire, RegisterSlice.wireList]
  · rw [sliceAgree (OracleWorkLayout.canonical p).degreeCondition]
    · exact specification.degree_condition
    · simp [oracleDegreeConditionWire, oracleSingletonWire,
        RegisterSlice.wireList]
  · rw [sliceAgree (OracleWorkLayout.canonical p).selected]
    · exact specification.selected_zero
    · simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
  · intro wire member
    rw [workAgree wire]
    · exact specification.moved_zero wire member
    · exact oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).moved
          (by simpa [oracleMovedWires, RegisterSlice.wireList] using member)
  · refine {
      equal_zero := ?_
      good_zero := ?_
      present_other_zero := ?_
      absent_zero := ?_ }
    · intro slot
      rw [sliceAgree (OracleWorkLayout.canonical p).membershipEqual]
      · exact specification.membership_zero.equal_zero slot
      · exact membershipEqualWireAt_mem_slice p slot
    · intro slot
      rw [sliceAgree (OracleWorkLayout.canonical p).membershipGood]
      · exact specification.membership_zero.good_zero slot
      · exact membershipGoodWireAt_mem_slice p slot
    · rw [sliceAgree (OracleWorkLayout.canonical p).presentOther]
      · exact specification.membership_zero.present_other_zero
      · exact oraclePresentOtherWire_mem_slice p
    · rw [sliceAgree (OracleWorkLayout.canonical p).absent]
      · exact specification.membership_zero.absent_zero
      · exact oracleAbsentWire_mem_slice p
  · rw [sliceAgree (OracleWorkLayout.canonical p).branch]
    · exact specification.branch_zero
    · simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
  · refine {
      data_zero := ?_
      marker_zero := ?_ }
    · intro word
      calc
        readWires ((candidateWordAt p word).take p.wordWidth) output =
            readWires ((candidateWordAt p word).take p.wordWidth) input := by
          apply List.map_congr_left
          intro wire member
          exact workAgree wire (oracleSliceWire_mem_oracleWork p
            (OracleWorkLayout.canonical p).candidate
              (candidateWordAt_mem_candidateSlice p word
                (List.mem_of_mem_take member)))
        _ = List.replicate p.wordWidth false :=
          specification.candidate_zero.data_zero word
    · intro word
      rw [workAgree (candidateMarkerWire p word)]
      · exact specification.candidate_zero.marker_zero word
      · exact oracleSliceWire_mem_oracleWork p
          (OracleWorkLayout.canonical p).candidate
            (candidateWordAt_mem_candidateSlice p word (by
              simp [candidateMarkerWire, candidateWordAt]))
  · apply EventSortCleanInput.of_agree p input output specification.event_clean
    · apply List.map_congr_left
      intro wire member
      exact workAgree wire (oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).compareWork
          (by simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member))
    · intro wire member
      exact workAgree wire
        (decoderAndScratchWire_mem_diagonalOracleWorkWires p member)
    · exact workAgree (oraclePositionWire p) (by
        apply oracleSliceWire_mem_oracleWork p
          (OracleWorkLayout.canonical p).positionMatch
        change (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).positionMatch).ancillaWire _ ∈ _
        simp [RegisterSlice.wireList])
    · exact workAgree (oraclePairWire p) (by
        apply oracleSliceWire_mem_oracleWork p
          (OracleWorkLayout.canonical p).pair
        change (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).pair).ancillaWire _ ∈ _
        simp [RegisterSlice.wireList])
    · apply List.map_congr_left
      intro wire member
      simp only [sortCompareWorkWires, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with compareMember | extraEqual
      · exact workAgree wire (oracleSliceWire_mem_oracleWork p
          (OracleWorkLayout.canonical p).compareWork
            (by simpa [oracleCompareWorkWires, RegisterSlice.wireList] using
              compareMember))
      · subst wire
        apply workAgree
        apply oracleSliceWire_mem_oracleWork p
          (OracleWorkLayout.canonical p).andWork
        simp [RegisterSlice.wireList]
    · intro wire member
      exact workAgree wire (oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).andWork
          (sortAndScratchWires_mem_andSlice p member))
    · intro instruction instructionMember
      apply workAgree
      apply oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).sortFlags
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr
        ⟨instruction.history, List.mem_finRange instruction.history, rfl⟩

/--
合法な active event slot で rep/coll bit が物理 membership と一致するとき、actual branch は
`columnReference` が返す configuration・row selector・符号を任意 accumulator へ厳密に XOR する。
-/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_active_reference
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (_eventRange : 2 ≤ offset.val)
    (branchCorrect :
      (decide (moveSite (configuration.siteAt ⟨slot.val, active⟩)
          (selectorDirection (selectorOfSlotOffset slot offset)) ∈
        configuration.1.erase
          (configuration.siteAt ⟨slot.val, active⟩)) : Bool) =
        selectorRequestsCollision (selectorOfSlotOffset slot offset))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentConditionsSpec p configuration
      (selectorOfSlotOffset slot offset) input) :
    let source := configuration.siteAt ⟨slot.val, active⟩
    let direction := selectorDirection (selectorOfSlotOffset slot offset)
    let outputConfiguration := updateConfiguration configuration (source, direction)
    let moved := moveSite source direction
    let movedMember : moved ∈ outputConfiguration.1 :=
      moveSite_mem_updateConfiguration configuration (source, direction)
        ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
    let reference : ColumnReferenceResult p :=
      ⟨outputConfiguration,
        selectorOfSlotOffset
          (slotOfMember outputConfiguration moved movedMember) offset, false⟩
    ColumnReferenceBranchResult p reference input
      ((applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  dsimp only
  let source := configuration.siteAt ⟨slot.val, active⟩
  let direction := selectorDirection (selectorOfSlotOffset slot offset)
  let outputConfiguration := updateConfiguration configuration (source, direction)
  let moved := moveSite source direction
  have sourceMember : source ∈ configuration.1 :=
    ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
  have movedMember : moved ∈ outputConfiguration.1 :=
    moveSite_mem_updateConfiguration configuration (source, direction) sourceMember
  have conditionTrue : columnEventMembershipCondition configuration source slot
      offset = true := by
    rw [columnEventMembershipCondition_correct configuration source sourceMember]
    exact decide_eq_true branchCorrect
  have activeResult : ColumnEventActiveBranchResult p outputConfiguration moved
      movedMember offset input
        ((applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
          reversibleGatePermutation input) := by
    simpa [source, direction, outputConfiguration, moved] using
      applyColumnEventReferenceAndRestoreWorkCircuit_active_of_prefix configuration slot offset active input
        (columnEventPrefix_correct configuration slot offset active input
          specification) (by simpa [source] using conditionTrue)
  exact activeResult.toColumnReference
    ⟨outputConfiguration,
      selectorOfSlotOffset (slotOfMember outputConfiguration moved movedMember)
        offset, false⟩ rfl rfl rfl

/--
合法な active event slot でも rep/coll bit が物理 membership と異なれば、actual branch は
branch=false となり、`columnReference = none` と同じく入力基底を厳密に固定する。
-/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_wrongBranch
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (wrongBranch :
      (decide (moveSite (configuration.siteAt ⟨slot.val, active⟩)
          (selectorDirection (selectorOfSlotOffset slot offset)) ∈
        configuration.1.erase
          (configuration.siteAt ⟨slot.val, active⟩)) : Bool) ≠
        selectorRequestsCollision (selectorOfSlotOffset slot offset))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentConditionsSpec p configuration
      (selectorOfSlotOffset slot offset) input) :
    (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  let source := configuration.siteAt ⟨slot.val, active⟩
  have sourceMember : source ∈ configuration.1 :=
    ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
  have conditionFalse : columnEventMembershipCondition configuration source slot
      offset = false := by
    rw [columnEventMembershipCondition_correct configuration source sourceMember]
    exact decide_eq_false wrongBranch
  exact applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_prefix configuration slot offset active
    input (columnEventPrefix_correct configuration slot offset active input
      specification) (by simpa [source] using conditionFalse)

/-- Persistent column 入力から同じ slot の対角 branch が要求する clean 仕様を取り出す。 -/
theorem ColumnOraclePersistentConditionsSpec.diagonalClean
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOraclePersistentConditionsSpec p configuration selector input)
    (slot : Fin p.K) :
    DiagonalBranchCleanInput p slot true
      (decide (slot.val < configuration.1.card)) input := by
  refine {
    scratch_zero := specification.event_clean.moved_selector.scratch_zero
    selected_zero := specification.selected_zero
    branch_zero := specification.branch_zero
    legal_value := specification.legal
    present_value := specification.present slot }

/--
Column 対角 branch は、row-output、selector-output、negative、active 以外の任意 wire を
compute--use--uncompute 後に入力値へ厳密に戻す。
-/
theorem columnDiagonalResultComputeUseUncomputeCircuit_outside_outputs_restored
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideRow : wire ∉ rowOutputWires p)
    (outsideSelector : wire ∉ selectorOutputWires p)
    (outsideNegative : wire ≠ negativeWire p)
    (outsideActive : wire ≠ activeWire p) :
    (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input wire = input wire := by
  let compute := xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
    (6 * slot.val + copy.val)
  let computed := compute.runBasis reversibleGatePermutation input
  let used := (controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy).runBasis
    reversibleGatePermutation computed
  have outputEq :
      (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
          reversibleGatePermutation input =
        restoreSupport (columnDiagonalComputeSupport p) input used := by
    simpa [computed, used, compute] using
      runBasis_columnDiagonalResultComputeUseUncomputeCircuit_restoreSupport p slot copy input
  by_cases supportMember : wire ∈ columnDiagonalComputeSupport p
  · rw [outputEq]
    exact restoreSupport_agrees_input (columnDiagonalComputeSupport p) input used
      wire supportMember
  · have useOutside : used wire = computed wire := by
      dsimp [used]
      simp only [controlledXorColumnDiagonalResultIntoOutputsCircuit, runBasis_seq]
      rw [runBasis_safeCnot_outside (oracleBranchWire p) (activeWire p) wire
        (oracleBranchWire_ne_activeWire p) outsideActive]
      rw [runBasis_safeCnot_outside (oracleBranchWire p) (negativeWire p) wire
        (oracleBranchWire_ne_negativeWire p) outsideNegative]
      rw [runBasis_controlledXorConstant_outside (oracleBranchWire p)
        (selectorOutputWires p) (6 * slot.val + copy.val) _
        (oracleBranchWire_not_mem_selectorOutputWires p) wire outsideSelector]
      exact runBasis_validatedControlledXorCopyLists_outside (oracleBranchWire p)
        (columnKeyWires p) (rowOutputWires p) computed
        (columnKeyWires_nodup p) (rowOutputWires_nodup p)
        (by simp) (columnKeyWires_disjoint_rowOutputWires p)
        (oracleBranchWire_not_mem_columnKeyWires p)
        (oracleBranchWire_not_mem_rowOutputWires p) wire outsideRow
    have computedOutside : computed wire = input wire := by
      dsimp [computed, compute]
      exact Circuit.runBasis_outside_of_usesOnly
        (columnDiagonalComputeSupport p)
        (xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
          (6 * slot.val + copy.val))
        (columnDiagonalCompute_usesOnly p slot copy) input wire supportMember
    rw [outputEq]
    exact (restoreSupport_outside (columnDiagonalComputeSupport p) input used wire
      supportMember).trans (useOutside.trans computedOutside)

/--
合法な active 対角 selector では、actual diagonal branch は `columnReference` の
同一 configuration・同一 selector・negative=true を任意 accumulator へ厳密に XOR する。
-/
theorem columnDiagonalResultComputeUseUncomputeCircuit_active_reference
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (copy : Fin 2)
    (active : slot.val < configuration.1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentConditionsSpec p configuration
      (selectorOfSlotOffset slot
        ⟨copy.val, lt_trans copy.isLt (by decide)⟩) input) :
    let selector := selectorOfSlotOffset slot
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
    ColumnReferenceBranchResult p reference input
      ((columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input) := by
  dsimp only
  let selector := selectorOfSlotOffset slot
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  have selectorMatch : diagonalSelectorMatches (columnSelectorWires p)
      (6 * slot.val + copy.val) input = true := by
    simp [diagonalSelectorMatches, specification.selector_bits,
      selectorOfSlotOffset]
  have diagonalResult := columnDiagonalResultComputeUseUncomputeCircuit_active p slot copy input
    (by simpa [decide_eq_true active] using specification.diagonalClean slot)
    selectorMatch
  have supportRestored : BasisAgreeOn (columnEventCandidateUpdateAndSortSupport p)
      ((columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input) input := by
    intro wire supportMember
    apply columnDiagonalResultComputeUseUncomputeCircuit_outside_outputs_restored p slot copy input wire
    · intro rowMember
      exact (List.disjoint_left.mp
        (columnEventCandidateUpdateAndSortSupport_disjoint_rowOutput p)) supportMember rowMember
    · intro selectorMember
      exact (List.disjoint_left.mp
        (columnEventCandidateUpdateAndSortSupport_disjoint_selectorOutput p)) supportMember
          selectorMember
    · intro equal
      subst wire
      exact negativeWire_not_mem_columnEventCandidateUpdateAndSortSupport p supportMember
    · intro equal
      subst wire
      exact activeWire_not_mem_columnEventCandidateUpdateAndSortSupport p supportMember
  refine {
    row_output := ?_
    selector_output := ?_
    negative := ?_
    active := ?_
    support_restored := supportRestored
    outside_restored := ?_ }
  · simpa [specification.column_key_bits] using diagonalResult.row_output
  · simpa [selector, selectorOfSlotOffset] using diagonalResult.selector_output
  · simpa using diagonalResult.negative
  · simpa using diagonalResult.active
  · intro wire outsideRow outsideSelector outsideNegative outsideActive
    exact columnDiagonalResultComputeUseUncomputeCircuit_outside_outputs_restored p slot copy input wire
      outsideRow outsideSelector outsideNegative outsideActive

/--
Persistent selector と異なる任意 selector の column branch は、対角・event のどちらでも
入力基底を厳密に固定する。
-/
theorem dispatchColumnSelectorToDiagonalOrEventCircuit_inactive_of_selector_ne
    {p : QParameters} (configuration : QConfiguration p)
    (active branch : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentConditionsSpec p configuration active input)
    (different : branch ≠ active) :
    (dispatchColumnSelectorToDiagonalOrEventCircuit p branch).runBasis
        reversibleGatePermutation input = input := by
  let slot := selectorSlot branch
  let offset := selectorOffset branch
  have activeDifferent : active ≠ selectorOfSlotOffset slot offset := by
    simpa [slot, offset] using Ne.symm different
  unfold dispatchColumnSelectorToDiagonalOrEventCircuit
  by_cases diagonal : offset.val < 2
  · rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal p slot offset diagonal]
    let copy : Fin 2 := ⟨offset.val, diagonal⟩
    change (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input
    apply columnDiagonalResultComputeUseUncomputeCircuit_padding_identity p slot copy true
      (decide (slot.val < configuration.1.card)) input
      (specification.diagonalClean slot)
    unfold diagonalSelectorMatches
    rw [specification.selector_bits]
    apply decide_eq_false
    intro bitsEqual
    apply activeDifferent
    apply Fin.ext
    have valueEqual := (columnConstantBits_eq_constantBits_iff_of_lt
      (qSelector_lt_capacity p active)
      (qSelector_lt_capacity p (selectorOfSlotOffset slot offset))).mp
        (by simpa [columnSelectorWires, copy, selectorOfSlotOffset] using bitsEqual)
    simpa [selectorOfSlotOffset] using valueEqual
  · rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset diagonal]
    exact applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_selector_ne configuration active slot
      offset input specification activeDifferent

/--
`columnReference` が `some reference` を返す合法 selector では、対応する唯一の actual
column branch がその reference の全 XOR 仕様を厳密に満たす。
-/
theorem dispatchColumnSelectorToDiagonalOrEventCircuit_reference_some
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p) (reference : ColumnReferenceResult p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentConditionsSpec p configuration selector input)
    (referenceSome : columnReference configuration selector = some reference) :
    ColumnReferenceBranchResult p reference input
      ((dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis
        reversibleGatePermutation input) := by
  let slot := selectorSlot selector
  let offset := selectorOffset selector
  have selectorRebuild : selectorOfSlotOffset slot offset = selector := by
    simp [slot, offset]
  have specificationAt : ColumnOraclePersistentConditionsSpec p configuration
      (selectorOfSlotOffset slot offset) input := by
    simpa [selectorRebuild] using specification
  by_cases active : slot.val < configuration.1.card
  · by_cases diagonal : offset.val < 2
    · let copy : Fin 2 := ⟨offset.val, diagonal⟩
      obtain ⟨member, selected⟩ :=
        configurationSlot_eq_some_siteAt configuration slot active
      let source := configuration.siteAt ⟨slot.val, active⟩
      have slotEq : slot = slotOfMember configuration source member := by
        exact physicalSlot_eq_slotOfMember_of_siteAt_eq configuration slot active
          source member rfl
      have referenceExact : columnReference configuration selector =
          some ⟨configuration, selector, true⟩ := by
        rw [← selectorRebuild, slotEq]
        simpa [copy] using
          columnReference_diagonal configuration source member copy
      have referenceEq : reference =
          (⟨configuration, selector, true⟩ : ColumnReferenceResult p) := by
        exact Option.some.inj (referenceSome.symm.trans referenceExact)
      subst reference
      unfold dispatchColumnSelectorToDiagonalOrEventCircuit
      rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal p slot offset diagonal]
      change ColumnReferenceBranchResult p ⟨configuration, selector, true⟩ input
        ((columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
          reversibleGatePermutation input)
      simpa [selectorRebuild, copy] using
        columnDiagonalResultComputeUseUncomputeCircuit_active_reference configuration slot copy active
          input specificationAt
    · have eventRange : 2 ≤ offset.val := by omega
      by_cases branchCorrect :
          (decide (moveSite (configuration.siteAt ⟨slot.val, active⟩)
              (selectorDirection (selectorOfSlotOffset slot offset)) ∈
            configuration.1.erase
              (configuration.siteAt ⟨slot.val, active⟩)) : Bool) =
            selectorRequestsCollision (selectorOfSlotOffset slot offset)
      · let source := configuration.siteAt ⟨slot.val, active⟩
        let direction := selectorDirection (selectorOfSlotOffset slot offset)
        let outputConfiguration :=
          updateConfiguration configuration (source, direction)
        let moved := moveSite source direction
        have sourceMember : source ∈ configuration.1 :=
          ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
        have movedMember : moved ∈ outputConfiguration.1 :=
          moveSite_mem_updateConfiguration configuration (source, direction)
            sourceMember
        let expected : ColumnReferenceResult p :=
          ⟨outputConfiguration,
            selectorOfSlotOffset
              (slotOfMember outputConfiguration moved movedMember) offset, false⟩
        have referenceExact : columnReference configuration selector =
            some expected := by
          rw [← selectorRebuild]
          simpa [expected, source, direction, outputConfiguration, moved] using
            columnReference_eventSlot_active_exact configuration slot offset active
              eventRange branchCorrect
        have referenceEq : reference = expected :=
          Option.some.inj (referenceSome.symm.trans referenceExact)
        subst reference
        unfold dispatchColumnSelectorToDiagonalOrEventCircuit
        rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset diagonal]
        simpa [expected, source, direction, outputConfiguration, moved] using
          applyColumnEventReferenceAndRestoreWorkCircuit_active_reference configuration slot offset active
            eventRange branchCorrect input specificationAt
      · have none := columnReference_eventSlot_wrongBranch configuration slot
          offset active eventRange branchCorrect
        rw [selectorRebuild, referenceSome] at none
        simp at none
  · have padding : configuration.1.card ≤ slot.val := Nat.le_of_not_gt active
    have none := columnReference_paddingSlot configuration slot offset padding
    rw [selectorRebuild, referenceSome] at none
    simp at none

/--
`columnReference = none` の selector では、padding または誤った rep/coll event のいずれでも、
対応する actual column branch は入力基底を厳密に固定する。
-/
theorem dispatchColumnSelectorToDiagonalOrEventCircuit_reference_none
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentConditionsSpec p configuration selector input)
    (referenceNone : columnReference configuration selector = none) :
    (dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis
        reversibleGatePermutation input = input := by
  let slot := selectorSlot selector
  let offset := selectorOffset selector
  have selectorRebuild : selectorOfSlotOffset slot offset = selector := by
    simp [slot, offset]
  have specificationAt : ColumnOraclePersistentConditionsSpec p configuration
      (selectorOfSlotOffset slot offset) input := by
    simpa [selectorRebuild] using specification
  by_cases active : slot.val < configuration.1.card
  · by_cases diagonal : offset.val < 2
    · let copy : Fin 2 := ⟨offset.val, diagonal⟩
      obtain ⟨member, _selected⟩ :=
        configurationSlot_eq_some_siteAt configuration slot active
      let source := configuration.siteAt ⟨slot.val, active⟩
      have slotEq : slot = slotOfMember configuration source member := by
        exact physicalSlot_eq_slotOfMember_of_siteAt_eq configuration slot active
          source member rfl
      have someValue : columnReference configuration selector =
          some ⟨configuration, selector, true⟩ := by
        rw [← selectorRebuild, slotEq]
        simpa [copy] using
          columnReference_diagonal configuration source member copy
      rw [referenceNone] at someValue
      simp at someValue
    · have eventRange : 2 ≤ offset.val := by omega
      by_cases branchCorrect :
          (decide (moveSite (configuration.siteAt ⟨slot.val, active⟩)
              (selectorDirection (selectorOfSlotOffset slot offset)) ∈
            configuration.1.erase
              (configuration.siteAt ⟨slot.val, active⟩)) : Bool) =
            selectorRequestsCollision (selectorOfSlotOffset slot offset)
      · have someValue := columnReference_eventSlot_active_exact configuration
          slot offset active eventRange branchCorrect
        rw [selectorRebuild, referenceNone] at someValue
        simp at someValue
      · unfold dispatchColumnSelectorToDiagonalOrEventCircuit
        rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset diagonal]
        exact applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_wrongBranch configuration slot
          offset active branchCorrect input specificationAt
  · have padding : configuration.1.card ≤ slot.val := Nat.le_of_not_gt active
    unfold dispatchColumnSelectorToDiagonalOrEventCircuit
    by_cases diagonal : offset.val < 2
    · rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal p slot offset diagonal]
      let copy : Fin 2 := ⟨offset.val, diagonal⟩
      change (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
          reversibleGatePermutation input = input
      apply columnDiagonalResultComputeUseUncomputeCircuit_absent_identity p slot copy true input
      simpa [decide_eq_false (Nat.not_lt.mpr padding)] using
        specification.diagonalClean slot
    · rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset diagonal]
      exact applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_padding configuration slot offset
        padding input specificationAt

/--
一般 accumulator 入力で `columnReference = some reference` なら、全 `6K` branch 列と
persistent compute--uncompute を含む actual column oracle 全体が reference の XOR 仕様を満たす。
-/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p) (reference : ColumnReferenceResult p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOracleInputSpec p configuration selector input)
    (referenceSome : columnReference configuration selector = some reference) :
    ColumnReferenceBranchResult p reference input
      ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input) := by
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
    reversibleGatePermutation input
  let branchOutput := (dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis
    reversibleGatePermutation persistent
  have persistentSpec : ColumnOraclePersistentConditionsSpec p configuration selector
      persistent := by
    simpa [persistent] using specification.afterPersistent
  have branchResult : ColumnReferenceBranchResult p reference persistent
      branchOutput := by
    simpa [branchOutput] using dispatchColumnSelectorToDiagonalOrEventCircuit_reference_some configuration
      selector reference persistent persistentSpec referenceSome
  have outputSpec : ColumnOraclePersistentConditionsSpec p configuration selector
      branchOutput :=
    persistentSpec.of_supportAgreement branchResult.support_restored
  have inactiveInput : ∀ branch : QSelector p, branch ≠ selector →
      (dispatchColumnSelectorToDiagonalOrEventCircuit p branch).runBasis reversibleGatePermutation
        persistent = persistent := by
    intro branch different
    exact dispatchColumnSelectorToDiagonalOrEventCircuit_inactive_of_selector_ne configuration selector
      branch persistent persistentSpec different
  have activeResult : (dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis
      reversibleGatePermutation persistent = branchOutput := rfl
  have inactiveOutput : ∀ branch : QSelector p, branch ≠ selector →
      (dispatchColumnSelectorToDiagonalOrEventCircuit p branch).runBasis reversibleGatePermutation
        branchOutput = branchOutput := by
    intro branch different
    exact dispatchColumnSelectorToDiagonalOrEventCircuit_inactive_of_selector_ne configuration selector
      branch branchOutput outputSpec different
  simpa [persistent, branchOutput] using
    applyColumnOracleReferenceAndRestoreWorkCircuit_correct_of_unique_active p reference selector
      input branchOutput inactiveInput activeResult inactiveOutput branchResult

/--
一般 accumulator 入力で `columnReference = none` なら、全 `6K` branch が恒等であり、
persistent compute--uncompute も消去されるため actual column oracle 全体は厳密な恒等写像である。
-/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_reference_none
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOracleInputSpec p configuration selector input)
    (referenceNone : columnReference configuration selector = none) :
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input = input := by
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
    reversibleGatePermutation input
  have persistentSpec : ColumnOraclePersistentConditionsSpec p configuration selector
      persistent := by
    simpa [persistent] using specification.afterPersistent
  apply applyColumnOracleReferenceAndRestoreWorkCircuit_eq_input_of_eachBranch p input
  intro branch
  change (dispatchColumnSelectorToDiagonalOrEventCircuit p branch).runBasis reversibleGatePermutation
      persistent = persistent
  by_cases equal : branch = selector
  · subst branch
    exact dispatchColumnSelectorToDiagonalOrEventCircuit_reference_none configuration selector persistent
      persistentSpec referenceNone
  · exact dispatchColumnSelectorToDiagonalOrEventCircuit_inactive_of_selector_ne configuration selector
      branch persistent persistentSpec equal

/--
非合法 delimiter の persistent compute 後に必要な最小仕様。合法 configuration は仮定せず、
legal=false と event/diagonal branch の一時 work clean 性だけを保持する。
-/
structure ColumnOraclePersistentIllegalSpec (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- compact decoder の legal flag は false である。 -/
  legal_false : input (oracleLegalWire p) = false
  /-- selector 一致 flag は各 branch の開始時に 0 である。 -/
  selected_zero : input (oracleSelectedWire p) = false
  /-- branch flag は各 branch の開始時に 0 である。 -/
  branch_zero : input (oracleBranchWire p) = false
  /-- event・sort・writer の transient work は clean である。 -/
  event_clean : EventSortCleanInput p input

/-- legal=false の persistent 状態では、任意 event branch が入力基底を厳密に固定する。 -/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_illegal
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentIllegalSpec p input) :
    (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_columnEventSelectorCompute p slot offset input
      specification.event_clean
  have movedClean : EventSortCleanInput p states.afterMoveForward := by
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.movedCopy_eq]
      exact EventSortCleanInput.of_columnEventMovedCopy p slot _ selectorClean
    rw [states.moveForward_eq]
    exact EventSortCleanInput.of_columnEventMoveForward p offset _ copiedClean
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    rw [states.membership_eq]
    exact EventSortCleanInput.of_columnEventMembership p slot _ movedClean
  have membershipSlotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) states.afterMoveForward := {
    equalWork_zero := movedClean.moved_selector.compare_zero
    scratch_zero := movedClean.moved_selector.scratch_zero }
  have legalOutside : oracleLegalWire p ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
    intro movedMember
    have legalMember : oracleLegalWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).legal).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleLegalWire, RegisterSlice.wireList]
    exact (List.disjoint_left.mp
      (RegisterSlice.wireList_disjoint_of_end_le_start
        (QLayout.oracleSlice (OracleWorkLayout.canonical p).legal)
        (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
        (by simp [QLayout.oracleSlice, RegisterSlice.compose,
          OracleWorkLayout.canonical]; omega))) legalMember movedMember
  have legalDifferent : oracleLegalWire p ≠ oracleSelectedWire p := by
    intro equal
    have legalMember : oracleLegalWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).legal).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleLegalWire, RegisterSlice.wireList]
    have selectedMember : oracleSelectedWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).selected).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
    exact (oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).legal
      (OracleWorkLayout.canonical p).selected
      (by simp [OracleWorkLayout.canonical]; omega)
      legalMember selectedMember) equal
  have legalAfterSelector : states.afterSelector (oracleLegalWire p) =
      input (oracleLegalWire p) := by
    rw [states.selector_eq]
    exact runBasis_columnEventSelectorCompute_other p slot offset input
      specification.event_clean _ legalDifferent
  have legalAfterMove : states.afterMoveForward (oracleLegalWire p) = false := by
    rw [states.moveForward_eq, states.movedCopy_eq]
    exact (runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
      states.afterSelector selectorClean _ legalOutside).trans
        (legalAfterSelector.trans specification.legal_false)
  have branchOutside : oracleBranchWire p ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
    intro movedMember
    have branchMember : oracleBranchWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).branch).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
    exact (List.disjoint_left.mp
      (RegisterSlice.wireList_disjoint_of_end_le_start
        (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
        (QLayout.oracleSlice (OracleWorkLayout.canonical p).branch)
        (by simp [QLayout.oracleSlice, RegisterSlice.compose,
          OracleWorkLayout.canonical]; omega))) movedMember branchMember
  have branchDifferent : oracleBranchWire p ≠ oracleSelectedWire p := by
    intro equal
    have branchMember : oracleBranchWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).branch).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
    have selectedMember : oracleSelectedWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).selected).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
    exact (oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).selected
      (OracleWorkLayout.canonical p).branch
      (by simp [OracleWorkLayout.canonical]; omega)
      selectedMember branchMember) equal.symm
  have branchAfterSelector : states.afterSelector (oracleBranchWire p) =
      input (oracleBranchWire p) := by
    rw [states.selector_eq]
    exact runBasis_columnEventSelectorCompute_other p slot offset input
      specification.event_clean _ branchDifferent
  have branchAfterMove : states.afterMoveForward (oracleBranchWire p) = false := by
    rw [states.moveForward_eq, states.movedCopy_eq]
    exact (runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
      states.afterSelector selectorClean _ branchOutside).trans
        (branchAfterSelector.trans specification.branch_zero)
  have preserved := runBasis_columnEventMembership_preserves_branch_inputs p slot
    states.afterMoveForward membershipSlotClean
  have legalAfterMembership : states.afterMembership (oracleLegalWire p) = false := by
    rw [states.membership_eq]
    exact preserved.1.trans legalAfterMove
  have branchAfterMembership : states.afterMembership
      (oracleBranchWire p) = false := by
    rw [states.membership_eq]
    exact preserved.2.2.2.2.trans branchAfterMove
  have branchFalse : states.afterBranch (oracleBranchWire p) = false := by
    rw [states.branch_eq]
    exact runBasis_columnEventBranchCompute_false_of_legal_canonical p slot offset
      states.afterMembership membershipClean.moved_selector.scratch_zero
        branchAfterMembership legalAfterMembership
  apply applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_afterBranch p slot offset input
  · exact columnEventCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input
      specification.event_clean
  · exact branchFalse

/-- legal=false の persistent 状態では、任意の対角・event branch が入力を固定する。 -/
theorem dispatchColumnSelectorToDiagonalOrEventCircuit_inactive_of_illegal
    (p : QParameters) (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentIllegalSpec p input) :
    (dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis
        reversibleGatePermutation input = input := by
  let slot := selectorSlot selector
  let offset := selectorOffset selector
  unfold dispatchColumnSelectorToDiagonalOrEventCircuit
  by_cases diagonal : offset.val < 2
  · rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal p slot offset diagonal]
    let copy : Fin 2 := ⟨offset.val, diagonal⟩
    change (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input
    apply columnDiagonalResultComputeUseUncomputeCircuit_illegal_identity p slot copy
      (input (oraclePresentWireAt p slot)) input
    exact {
      scratch_zero := specification.event_clean.moved_selector.scratch_zero
      selected_zero := specification.selected_zero
      branch_zero := specification.branch_zero
      legal_value := specification.legal_false
      present_value := rfl }
  · rw [dispatchColumnSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset diagonal]
    exact applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_illegal p slot offset input specification

/--
Persistent compute 後に legal=false と clean 性が得られれば、全 `6K` branch と outer
uncompute を含む column oracle 全体は入力基底を厳密に固定する。
-/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_identity_of_persistentIllegal
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentIllegalSpec p
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input)) :
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input = input := by
  apply applyColumnOracleReferenceAndRestoreWorkCircuit_eq_input_of_eachBranch p input
  intro selector
  exact dispatchColumnSelectorToDiagonalOrEventCircuit_inactive_of_illegal p selector _ specification

end ReversibleCircuit

end ProbabilityGeneratorQProof
