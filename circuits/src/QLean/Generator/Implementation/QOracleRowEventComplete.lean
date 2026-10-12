import QLean.Generator.Implementation.QOracleEventComputeLocality
import QLean.Generator.Implementation.QOracleBranchIndexing
import QLean.Generator.Implementation.QOraclePersistentLocality
import QLean.Generator.Implementation.QWriteSortedConfigurationBridge
import QLean.Generator.Implementation.QOracleEventComputedClean
import QLean.Generator.Implementation.QWriteSortedBitlistBridge
import QLean.Generator.Implementation.QWriteMovedSelectorConfigurationBridge
import QLean.Generator.Implementation.QOracleColumnEventComplete

/-!
# Q row event 分岐と row oracle の完全な基底作用

このファイルでは、row event 正本回路の疎な局所性を分岐正しさへ差し込み、
巨大行列や全基底列挙を使わず、外部出力と内部 work 復元の厳密な状態等式を組み立てる。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- row event offset が出力次数へ加える変化量で、collision のときだけ `+1` である。 -/
def rowEventDegreeChange (offset : Fin 6) : Int :=
  if offset.val % 2 = 1 then 1 else 0

/-- event offsetをrow側で読むと元の物理方向へ戻る。 -/
@[simp] theorem rowEventDirection_eventOffset
    (direction : QDirection) (collision : Bool) :
    rowEventDirection (eventOffset direction collision) = direction := by
  cases direction <;> cases collision <;>
    simp [rowEventDirection, eventOffset]

/-- event offsetの奇偶はcollision Boolそのものである。 -/
@[simp] theorem eventOffset_mod_two_eq_one
    (direction : QDirection) (collision : Bool) :
    ((eventOffset direction collision).val % 2 = 1) = (collision = true) := by
  cases direction <;> cases collision <;> decide

/--
row oracle の物理入力を、system配置・row selector・全oracle workの0初期化だけで
指定する。column-key・column-selector・key-signalは任意のXOR accumulatorでよい。
-/
structure RowOracleInputSpec (p : QParameters)
    (configuration : QConfiguration p) (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- system registerは対象configurationのdelimiter符号である。 -/
  system_bits : readWires (systemWires p) input =
    registerBitList (delimiterEncoding configuration)
  /-- row selectorは指定selectorのlittle-endian定数bit列である。 -/
  selector_bits : readWires (rowSelectorWires p) input =
    constantBits selector.val (rowSelectorWires p).length
  /-- oracle内部work sliceの全wireは0で初期化されている。 -/
  work_zero : ∀ wire ∈ diagonalOracleWorkWires p, input wire = false

/--
row event の各分岐へ入る persistent 状態について、後続の基底作用証明に必要な
値不変条件をまとめる。これは最終定理の外部仮定ではなく、persistent 正本から生成する。
-/
structure RowOraclePersistentConditionsSpec (p : QParameters)
    (configuration : QConfiguration p) (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- selector register は指定した row selector の固定幅 bit 列である。 -/
  selector_bits : readWires (rowSelectorWires p) input =
    constantBits selector.val (rowSelectorWires p).length
  /-- system register は合法配置の delimiter 符号である。 -/
  system_bits : readWires (systemWires p) input =
    registerBitList (delimiterEncoding configuration)
  /-- present bit は合法配置の有効 slot と一致する。 -/
  present : ∀ slot : Fin p.K,
    input (oraclePresentWireAt p slot) =
      decide (slot.val < configuration.1.card)
  /-- 有効 system word は対応する配置 site を保持する。 -/
  active_word : ∀ (slot : Fin p.K)
    (active : slot.val < configuration.1.card),
    readWires (registerWordAt p (systemWires p) slot) input =
      siteWordBits p (configuration.siteAt ⟨slot.val, active⟩)
  /-- degree one-hot は粒子数に一致する。 -/
  degree : ∀ slot : Fin p.K,
    input (oracleDegreeWireAt p slot) =
      decide (slot.val + 1 = configuration.1.card)
  /-- delimiter 合法性 flag は真である。 -/
  legal : input (oracleLegalWire p) = true
  /-- row-mode degree 条件は配置に空きがあることと一致する。 -/
  degree_condition : input (oracleDegreeConditionWire p) =
    decide (configuration.1.card < p.K)
  /-- selector 一致 flag は各分岐の開始時に 0 である。 -/
  selected_zero : input (oracleSelectedWire p) = false
  /-- moved register は各分岐の開始時に全て 0 である。 -/
  moved_zero : ∀ wire ∈ oracleMovedWires p, input wire = false
  /-- membership の全出力 flag は各分岐の開始時に 0 である。 -/
  membership_zero : MembershipFlagsClean p input
  /-- branch flag は各分岐の開始時に 0 である。 -/
  branch_zero : input (oracleBranchWire p) = false
  /-- candidate 領域は各分岐の開始時に全て 0 である。 -/
  candidate_zero : CandidateRegionClean p input
  /-- event の比較・sort・writer work は canonical clean 条件を満たす。 -/
  event_clean : EventSortCleanInput p input

/-- canonical oracle slice内のwireは、row oracle入力仕様の下で全て0である。 -/
theorem RowOracleInputSpec.slice_zero
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleInputSpec p configuration selector input)
    {width : Nat} (slice : RegisterSlice p.oracleWorkWidth width) :
    ∀ wire ∈ ((QLayout.oracleSlice slice).wireList :
      List (Wire p.ancillaWidth p.systemWidth)), input wire = false := by
  intro wire member
  exact specification.work_zero wire (by
    simpa [diagonalOracleWorkWires] using
      oracleSliceWire_mem_oracleWork p slice member)

/-- row oracle入力仕様はpersistent decoderが要求する全clean条件を満たす。 -/
theorem RowOracleInputSpec.persistentClean
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleInputSpec p configuration selector input) :
    OraclePersistentCleanInput p (systemWires p) configuration input := by
  refine {
    decoder := {
      input_bits := specification.system_bits
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

/-- row oracle入力仕様からpersistent computeの数学的出力仕様を無仮定で得る。 -/
theorem RowOracleInputSpec.persistentOutput
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleInputSpec p configuration selector input) :
    OraclePersistentOutputSpec p configuration true
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input) := by
  exact computeSharedDecoderPresenceParityAndOneFlagsCircuit_correct_of_clean p (systemWires p)
    (systemWires_oraclePersistentInputLayout p) configuration input
    specification.persistentClean true

/-- row oracle入力仕様はevent candidate/sort開始前の全tracked clean条件も満たす。 -/
theorem RowOracleInputSpec.eventSortClean
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleInputSpec p configuration selector input) :
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

/-- row-selector registerはsystem registerとcanonical oracle-work全体の双方に交わらない。 -/
theorem rowSelectorWires_disjoint_systemAndOracleWork (p : QParameters) :
    (rowSelectorWires p).Disjoint
      (systemWires p ++ diagonalOracleWorkWires p) := by
  rw [List.disjoint_append_right]
  constructor
  · let selector := (QLayout.canonical p).rowSelector
    simpa [rowSelectorWires, rowSelectorWire, systemWires, QLayout.systemWire,
      selector, RegisterSlice.wireList] using
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) selector).symm
  · let selector := (QLayout.canonical p).rowSelector
    let work := (QLayout.canonical p).oracleWork
    have separated : selector.start + p.selectorWidth ≤ work.start := by
      simp [selector, work, QLayout.canonical]
      omega
    simpa [rowSelectorWires, rowSelectorWire, diagonalOracleWorkWires,
      selector, work, RegisterSlice.wireList] using
      (selector.wireList_disjoint_of_end_le_start work separated :
        (selector.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (work.wireList : List (Wire p.ancillaWidth p.systemWidth)))

/-- degree one-hot参照列の任意添字を、範囲判定と等式判定へ簡約する。 -/
theorem degreeOneHotFrom_getD :
    ∀ (count particleCount start index : Nat),
      (degreeOneHotFrom count particleCount start)[index]?.getD false =
        if index < count then decide (start + index + 1 = particleCount)
        else false
  | 0, _, _, _ => by simp [degreeOneHotFrom]
  | count + 1, particleCount, start, 0 => by simp [degreeOneHotFrom]
  | count + 1, particleCount, start, index + 1 => by
      simp only [degreeOneHotFrom, List.getElem?_cons_succ]
      rw [degreeOneHotFrom_getD count particleCount (start + 1) index]
      by_cases inRange : index < count
      · simp [inRange]
        omega
      · have outside : ¬index + 1 < count + 1 := by omega
        simp [inRange, outside]

/--
合法delimiter・selector・全0 oracle-workからpersistent computeを実行すると、全row event
分岐が要求するpersistent入力仕様を外部契約なしで満たす。
-/
theorem RowOracleInputSpec.afterPersistent
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleInputSpec p configuration selector input) :
    RowOraclePersistentConditionsSpec p configuration selector
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input) := by
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
    reversibleGatePermutation input
  have persistentClean := specification.persistentClean
  have persistentOutput := specification.persistentOutput
  have persistentUses : circuitUsesOnly
      (systemWires p ++ diagonalOracleWorkWires p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true) := by
    simpa using rowOraclePersistentCompute_usesOnly p
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
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_preCandidateSlice p (systemWires p)
        (systemWires_disjoint_diagonalOracleWorkWires p) true input slice
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
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_middleOracleSlice p (systemWires p)
        (systemWires_disjoint_diagonalOracleWorkWires p) true input slice
          candidateBefore beforeCompare wire member
  have preserveCandidate
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth))) :
      persistent wire = input wire := by
    simpa [persistent] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_candidateSlice p (systemWires p)
        (systemWires_candidateInputLayout p) true input wire member
  have inputSliceZero {width : Nat}
      (slice : RegisterSlice p.oracleWorkWidth width)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) : input wire = false :=
    specification.work_zero wire
      (diagonalOracleSlice_subset_work p slice member)
  refine {
    selector_bits := ?_
    system_bits := ?_
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
      readWires (rowSelectorWires p) persistent =
          readWires (rowSelectorWires p) input := by
        exact readWires_runBasis_of_usesOnly_disjoint
          (systemWires p ++ diagonalOracleWorkWires p) (rowSelectorWires p)
          (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true) input persistentUses
          (rowSelectorWires_disjoint_systemAndOracleWork p).symm
      _ = constantBits selector.val (rowSelectorWires p).length :=
        specification.selector_bits
  · simpa [persistent] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_input_preserved_of_clean p (systemWires p)
        (systemWires_oraclePersistentInputLayout p) configuration input
          persistentClean true
  · intro slot
    simpa [persistent] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_present_value_of_clean p (systemWires p)
        (systemWires_oraclePersistentInputLayout p) configuration input
          persistentClean true slot
  · intro slot active
    simpa [persistent, siteWordBits] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_activeWord_of_clean p (systemWires p)
        (systemWires_oraclePersistentInputLayout p) configuration input
          persistentClean true slot active
  · intro slot
    have point := congrArg (fun values : List Bool =>
      values[slot.val]?.getD false) persistentOutput.degree
    simpa [persistent, readWires, oracleDegreeWires, oracleDegreeWireAt,
      QParameters.degreeWidth, degreeOneHotFrom_getD, slot.isLt] using point
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
      rowOraclePersistentOutput_eventSortClean p configuration input
        persistentClean specification.eventSortClean

/-- membership出力領域より前にあるoracle sliceのwireは全membership出力と異なる。 -/
theorem MembershipOutputsSeparated.of_earlierSlice
    (p : QParameters) {width : Nat}
    (earlier : RegisterSlice p.oracleWorkWidth width)
    (beforeEqual : earlier.start + width ≤
      (OracleWorkLayout.canonical p).membershipEqual.start)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ ((QLayout.oracleSlice earlier).wireList :
      List (Wire p.ancillaWidth p.systemWidth))) :
    MembershipOutputsSeparated p wire := by
  refine {
    ne_equal := ?_
    ne_good := ?_
    ne_other := ?_
    ne_absent := ?_ }
  · intro slot
    exact oracleSliceMembers_ne_of_end_le_start p earlier
      (OracleWorkLayout.canonical p).membershipEqual beforeEqual member
      (membershipEqualWireAt_mem_slice p slot)
  · intro slot
    exact oracleSliceMembers_ne_of_end_le_start p earlier
      (OracleWorkLayout.canonical p).membershipGood (by
        have := beforeEqual
        simp [OracleWorkLayout.canonical] at this ⊢
        omega) member (membershipGoodWireAt_mem_slice p slot)
  · exact oracleSliceMembers_ne_of_end_le_start p earlier
      (OracleWorkLayout.canonical p).presentOther (by
        have := beforeEqual
        simp [OracleWorkLayout.canonical] at this ⊢
        omega) member (oraclePresentOtherWire_mem_slice p)
  · exact oracleSliceMembers_ne_of_end_le_start p earlier
      (OracleWorkLayout.canonical p).absent (by
        have := beforeEqual
        simp [OracleWorkLayout.canonical] at this ⊢
        omega) member (oracleAbsentWire_mem_slice p)

/-- system wireはancilla上のmembership出力wireのいずれとも異なる。 -/
theorem MembershipOutputsSeparated.of_systemWire
    (p : QParameters) (index : Fin p.systemWidth) :
    MembershipOutputsSeparated p (QLayout.systemWire p index) := by
  refine {
    ne_equal := ?_
    ne_good := ?_
    ne_other := ?_
    ne_absent := ?_ }
  · intro slot
    simp [QLayout.systemWire, membershipEqualWireAt,
      QLayout.oracleSlice, RegisterSlice.compose, RegisterSlice.ancillaWire]
  · intro slot
    simp [QLayout.systemWire, membershipGoodWireAt,
      QLayout.oracleSlice, RegisterSlice.compose, RegisterSlice.ancillaWire]
  · simp [QLayout.systemWire, oraclePresentOtherWire, oracleSingletonWire,
      QLayout.oracleSlice, RegisterSlice.compose, RegisterSlice.ancillaWire]
  · simp [QLayout.systemWire, oracleAbsentWire, oracleSingletonWire,
      QLayout.oracleSlice, RegisterSlice.compose, RegisterSlice.ancillaWire]

/-- row membership正本はsystem register全体を厳密に保存する。 -/
theorem runBasis_rowEventMembership_system
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    readWires (systemWires p)
        ((rowEventMembership p slot).runBasis reversibleGatePermutation input) =
      readWires (systemWires p) input := by
  apply List.map_congr_left
  intro wire member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  exact runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other p (systemWires p)
    (systemWires_membershipInputLayout p) slot false input
      {
        equalWork_zero := clean.moved_selector.compare_zero
        scratch_zero := clean.moved_selector.scratch_zero }
      (QLayout.systemWire p index)
      (MembershipOutputsSeparated.of_systemWire p index)

/-- row membership正本はmembership出力より前のoracle sliceを厳密に保存する。 -/
theorem runBasis_rowEventMembership_earlierSlice
    (p : QParameters) (slot : Fin p.K) {width : Nat}
    (earlier : RegisterSlice p.oracleWorkWidth width)
    (beforeEqual : earlier.start + width ≤
      (OracleWorkLayout.canonical p).membershipEqual.start)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    readWires ((QLayout.oracleSlice earlier).wireList :
        List (Wire p.ancillaWidth p.systemWidth))
        ((rowEventMembership p slot).runBasis reversibleGatePermutation input) =
      readWires ((QLayout.oracleSlice earlier).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) input := by
  apply List.map_congr_left
  intro wire member
  exact runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other p (systemWires p)
    (systemWires_membershipInputLayout p) slot false input
      {
        equalWork_zero := clean.moved_selector.compare_zero
        scratch_zero := clean.moved_selector.scratch_zero }
      wire (MembershipOutputsSeparated.of_earlierSlice p earlier beforeEqual
        wire member)

/-- selector比較はselected flag以外の任意wireを保存する。 -/
theorem runBasis_rowEventSelectorCompute_other
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (different : wire ≠ oracleSelectedWire p) :
    (rowEventSelectorCompute p slot offset).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [runBasis_rowEventSelectorCompute p slot offset input
    clean.moved_selector.scratch_zero]
  split
  · exact xBasisAction_other (oracleSelectedWire p) wire different input
  · rfl

/-- system registerはselected flagを含まない。 -/
theorem oracleSelectedWire_not_mem_systemWires (p : QParameters) :
    oracleSelectedWire p ∉ systemWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have impossible : QLayout.systemWire p index ≠ oracleSelectedWire p := by
    simp [QLayout.systemWire, oracleSelectedWire, oracleSingletonWire,
      QLayout.oracleSlice, RegisterSlice.compose, RegisterSlice.ancillaWire]
  exact impossible equal

/-- selector比較はsystem register全体を保存する。 -/
theorem runBasis_rowEventSelectorCompute_system
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    readWires (systemWires p)
        ((rowEventSelectorCompute p slot offset).runBasis
          reversibleGatePermutation input) =
      readWires (systemWires p) input := by
  apply List.map_congr_left
  intro wire member
  exact runBasis_rowEventSelectorCompute_other p slot offset input clean wire
    (fun equal => oracleSelectedWire_not_mem_systemWires p (equal ▸ member))

/-- moved複写と逆移動の二段はmoved slice外の任意wireを保存する。 -/
theorem runBasis_rowEventMovedComputation_outside_movedSlice
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (rowEventMovedComputation p slot offset).runBasis
        reversibleGatePermutation input wire = input wire := by
  let copied := (rowEventMovedCopy p slot).runBasis
    reversibleGatePermutation input
  have copiedClean : EventSortCleanInput p copied :=
    EventSortCleanInput.of_rowEventMovedCopy p slot input clean
  rw [rowEventMovedComputation, runBasis_seq]
  calc
    (rowEventMoveBackward p offset).runBasis
        reversibleGatePermutation copied wire = copied wire :=
      runBasis_rowEventMoveBackward_outside_movedSlice p offset copied
        copiedClean.moved_selector.scratch_zero wire outside
    _ = input wire :=
      runBasis_rowEventMovedCopy_outside_movedSlice p slot input wire outside

/-- system registerはmoved sliceと交わらない。 -/
theorem systemWires_disjoint_oracleMovedSlice (p : QParameters) :
    (systemWires p).Disjoint
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).moved).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  rw [List.disjoint_left]
  intro wire systemMember movedMember
  rcases List.mem_map.mp systemMember with ⟨index, _, equal⟩
  subst wire
  rcases List.mem_map.mp movedMember with ⟨movedIndex, _, movedEqual⟩
  simp [QLayout.systemWire, QLayout.oracleSlice, RegisterSlice.compose,
    RegisterSlice.ancillaWire] at movedEqual

/-- moved複写と逆移動はsystem register全体を保存する。 -/
theorem runBasis_rowEventMovedComputation_system
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    readWires (systemWires p)
        ((rowEventMovedComputation p slot offset).runBasis
          reversibleGatePermutation input) =
      readWires (systemWires p) input := by
  apply List.map_congr_left
  intro wire member
  exact runBasis_rowEventMovedComputation_outside_movedSlice p slot offset input
    clean wire ((List.disjoint_left.mp
      (systemWires_disjoint_oracleMovedSlice p)) member)

/-- selector比較・moved複写・逆移動はmovedより後方の任意oracle sliceを保存する。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMoveBackward_laterSlice
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) {width : Nat}
    (later : RegisterSlice p.oracleWorkWidth width)
    (afterMoved : (OracleWorkLayout.canonical p).moved.start + p.movedWidth ≤
      later.start) :
    readWires ((QLayout.oracleSlice later).wireList :
        List (Wire p.ancillaWidth p.systemWidth))
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMoveBackward =
      readWires ((QLayout.oracleSlice later).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) input := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input clean
  apply List.map_congr_left
  intro wire member
  have outsideMoved : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) :=
    laterOracleListWire_not_mem_earlierSlice p
      (OracleWorkLayout.canonical p).moved later afterMoved wire member
  have differentSelected : wire ≠ oracleSelectedWire p := by
    have selectedMember : oracleSelectedWire p ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).selected).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
    exact (oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).selected later (by
        have := afterMoved
        simp [OracleWorkLayout.canonical] at this ⊢
        omega) selectedMember member).symm
  calc
    states.afterMoveBackward wire = states.afterSelector wire := by
      rw [states.moveBackward_eq, states.moved_eq]
      exact runBasis_rowEventMovedComputation_outside_movedSlice p slot offset
        states.afterSelector selectorClean wire outsideMoved
    _ = input wire := by
      rw [states.selector_eq]
      exact runBasis_rowEventSelectorCompute_other p slot offset input clean wire
        differentSelected

/-- persistent入力のmembership flag clean性はmembership直前まで保存される。 -/
theorem RowOraclePersistentConditionsSpec.afterMoveBackward_membershipZero
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOraclePersistentConditionsSpec p configuration selector input)
    (slot : Fin p.K) (offset : Fin 6) :
    MembershipFlagsClean p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMoveBackward := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have preserve {width : Nat}
      (later : RegisterSlice p.oracleWorkWidth width)
      (afterMoved : (OracleWorkLayout.canonical p).moved.start + p.movedWidth ≤
        later.start) :
      readWires ((QLayout.oracleSlice later).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) states.afterMoveBackward =
        readWires ((QLayout.oracleSlice later).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) input :=
    rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMoveBackward_laterSlice p slot offset input
      specification.event_clean later afterMoved
  refine {
    equal_zero := ?_
    good_zero := ?_
    present_other_zero := ?_
    absent_zero := ?_ }
  · intro current
    have values := preserve
      (OracleWorkLayout.canonical p).membershipEqual (by
        simp [OracleWorkLayout.canonical]
        omega)
    exact (readWires_eq_at_of_eq _ _ _ values
      (membershipEqualWireAt_mem_slice p current)).trans
        (specification.membership_zero.equal_zero current)
  · intro current
    have values := preserve
      (OracleWorkLayout.canonical p).membershipGood (by
        simp [OracleWorkLayout.canonical]
        omega)
    exact (readWires_eq_at_of_eq _ _ _ values
      (membershipGoodWireAt_mem_slice p current)).trans
        (specification.membership_zero.good_zero current)
  · have values := preserve
      (OracleWorkLayout.canonical p).presentOther (by
        simp [OracleWorkLayout.canonical]
        omega)
    exact (readWires_eq_at_of_eq _ _ _ values
      (oraclePresentOtherWire_mem_slice p)).trans
        specification.membership_zero.present_other_zero
  · have values := preserve
      (OracleWorkLayout.canonical p).absent (by
        simp [OracleWorkLayout.canonical]
        omega)
    exact (readWires_eq_at_of_eq _ _ _ values
      (oracleAbsentWire_mem_slice p)).trans
        specification.membership_zero.absent_zero

/-- row event 状態記録のmembership段はsystem register全体を保存する。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMembership_system
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    readWires (systemWires p)
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMembership =
      readWires (systemWires p)
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMoveBackward := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have moveClean : EventSortCleanInput p states.afterMoveBackward := by
    have selectorClean : EventSortCleanInput p states.afterSelector := by
      rw [states.selector_eq]
      exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input clean
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.moved_eq]
      exact EventSortCleanInput.of_rowEventMovedCopy p slot _ selectorClean
    rw [states.moveBackward_eq]
    exact EventSortCleanInput.of_rowEventMoveBackward p offset _ copiedClean
  rw [states.membership_eq]
  exact runBasis_rowEventMembership_system p slot states.afterMoveBackward moveClean

/-- row event 状態記録のmembership段はmembership出力より前のsliceを保存する。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMembership_earlierSlice
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) {width : Nat}
    (earlier : RegisterSlice p.oracleWorkWidth width)
    (beforeEqual : earlier.start + width ≤
      (OracleWorkLayout.canonical p).membershipEqual.start) :
    readWires ((QLayout.oracleSlice earlier).wireList :
        List (Wire p.ancillaWidth p.systemWidth))
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMembership =
      readWires ((QLayout.oracleSlice earlier).wireList :
        List (Wire p.ancillaWidth p.systemWidth))
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMoveBackward := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have moveClean : EventSortCleanInput p states.afterMoveBackward := by
    have selectorClean : EventSortCleanInput p states.afterSelector := by
      rw [states.selector_eq]
      exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input clean
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.moved_eq]
      exact EventSortCleanInput.of_rowEventMovedCopy p slot _ selectorClean
    rw [states.moveBackward_eq]
    exact EventSortCleanInput.of_rowEventMoveBackward p offset _ copiedClean
  rw [states.membership_eq]
  exact runBasis_rowEventMembership_earlierSlice p slot earlier beforeEqual
    states.afterMoveBackward moveClean

/-- branch計算はbranch target以外の任意wireを保存する。 -/
theorem runBasis_rowEventBranchCompute_other
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (different : wire ≠ oracleBranchWire p) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [runBasis_rowEventBranchCompute_canonical p slot offset input
    clean.moved_selector.scratch_zero]
  split
  · exact xBasisAction_other (oracleBranchWire p) wire different input
  · rfl

/--
候補生成回路はsystem・present・movedの参照領域を保存するため、合法配置のmembership
読出し仕様をそのまま候補生成後へ持ち上げられる。
-/
theorem ConfigurationMembershipInput.of_prepareCandidatesSystem
    {p : QParameters} {configuration : QConfiguration p} {moved : QSite p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ConfigurationMembershipInput p (systemWires p)
      configuration moved input) :
    ConfigurationMembershipInput p (systemWires p) configuration moved
      ((xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
        reversibleGatePermutation input) := by
  let output := (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
    reversibleGatePermutation input
  have preserve (wire : Wire p.ancillaWidth p.systemWidth)
      (outside : wire ∉ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth))) :
      output wire = input wire :=
    runBasis_xorConfigurationIntoCandidateRegisterCircuit_outside_candidateSlice p (systemWires p)
      (systemWires_candidateInputLayout p) input wire outside
  refine {
    present := ?_
    active_word := ?_
    moved_word := ?_ }
  · intro slot
    change output (oraclePresentWireAt p slot) = _
    rw [preserve (oraclePresentWireAt p slot)]
    · exact specification.present slot
    · intro candidateMember
      have presentMember : oraclePresentWireAt p slot ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).present).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        change (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).present).ancillaWire slot ∈ _
        rw [RegisterSlice.wireList]
        exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩
      have disjoint :
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).present).wireList :
              List (Wire p.ancillaWidth p.systemWidth)).Disjoint
            ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).candidate).wireList :
                List (Wire p.ancillaWidth p.systemWidth)) := by
        apply RegisterSlice.wireList_disjoint_of_end_le_start
        simp [QLayout.oracleSlice, RegisterSlice.compose,
          OracleWorkLayout.canonical]
        omega
      exact (List.disjoint_left.mp disjoint) presentMember candidateMember
  · intro slot active
    calc
      readWires (registerWordAt p (systemWires p) slot) output =
          readWires (registerWordAt p (systemWires p) slot) input := by
        apply List.map_congr_left
        intro wire member
        apply preserve wire
        exact (List.disjoint_left.mp
          (systemWires_candidateInputLayout p).disjoint_candidate)
            (mem_register_of_mem_registerWordAt p (systemWires p) slot member)
      _ = siteWordBits p (configuration.siteAt ⟨slot.val, active⟩) :=
        specification.active_word slot active
  · calc
      readWires (oracleMovedWires p) output =
          readWires (oracleMovedWires p) input := by
        apply List.map_congr_left
        intro wire member
        apply preserve wire
        intro candidateMember
        have movedMember : wire ∈ ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).moved).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
          simpa [oracleMovedWires, RegisterSlice.wireList] using member
        have disjoint :
            ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).moved).wireList :
                List (Wire p.ancillaWidth p.systemWidth)).Disjoint
              ((QLayout.oracleSlice
                (OracleWorkLayout.canonical p).candidate).wireList :
                  List (Wire p.ancillaWidth p.systemWidth)) := by
          apply RegisterSlice.wireList_disjoint_of_end_le_start
          simp [QLayout.oracleSlice, RegisterSlice.compose,
            OracleWorkLayout.canonical]
          omega
        exact (List.disjoint_left.mp disjoint) movedMember candidateMember
      _ = siteWordBits p moved := specification.moved_word

/--
persistent状態の合法配置仕様から、selector・moved copy・逆移動後にmembershipが読む
system/present/moved三領域の数学的仕様を得る。
-/
theorem RowOraclePersistentConditionsSpec.afterMoveBackward_membership
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOraclePersistentConditionsSpec p configuration selector input)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card) :
    ConfigurationMembershipInput p (systemWires p) configuration
      (moveSiteBackward (configuration.siteAt ⟨slot.val, active⟩)
        (rowEventDirection offset))
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMoveBackward := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input
      specification.event_clean
  have systemAfterSelector : readWires (systemWires p) states.afterSelector =
      readWires (systemWires p) input := by
    rw [states.selector_eq]
    exact runBasis_rowEventSelectorCompute_system p slot offset input
      specification.event_clean
  have movedResult : readWires (oracleMovedWires p) states.afterMoveBackward =
      siteWordBits p
        (moveSiteBackward (configuration.siteAt ⟨slot.val, active⟩)
          (rowEventDirection offset)) := by
    rw [states.moveBackward_eq, states.moved_eq]
    change readWires (oracleMovedWires p)
        ((rowEventMovedComputation p slot offset).runBasis
          reversibleGatePermutation states.afterSelector) = _
    apply runBasis_rowEventMovedComputation_site p slot offset
      (configuration.siteAt ⟨slot.val, active⟩) states.afterSelector
    · calc
        readWires (registerWordAt p (systemWires p) slot)
            states.afterSelector =
            readWires (registerWordAt p (systemWires p) slot) input := by
          apply List.map_congr_left
          intro wire member
          rw [states.selector_eq]
          exact runBasis_rowEventSelectorCompute_other p slot offset input
            specification.event_clean wire (fun equal =>
              oracleSelectedWire_not_mem_systemWires p (equal ▸
                mem_register_of_mem_registerWordAt p (systemWires p) slot
                  member))
        _ = siteWordBits p
            (configuration.siteAt ⟨slot.val, active⟩) :=
          specification.active_word slot active
    · intro wire member
      rw [states.selector_eq]
      rw [runBasis_rowEventSelectorCompute_other p slot offset input
        specification.event_clean wire]
      · exact specification.moved_zero wire member
      · intro equal
        subst wire
        have selectedMember : oracleSelectedWire p ∈
            ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).selected).wireList :
                List (Wire p.ancillaWidth p.systemWidth)) := by
          simp [oracleSelectedWire, oracleSingletonWire,
            RegisterSlice.wireList]
        have movedMember : oracleSelectedWire p ∈
            ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).moved).wireList :
                List (Wire p.ancillaWidth p.systemWidth)) := by
          simpa [oracleMovedWires, RegisterSlice.wireList] using member
        exact (List.disjoint_left.mp
          (RegisterSlice.wireList_disjoint_of_end_le_start
            (QLayout.oracleSlice (OracleWorkLayout.canonical p).selected)
            (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
            (by simp [QLayout.oracleSlice, RegisterSlice.compose,
              OracleWorkLayout.canonical]))) selectedMember movedMember
    · exact selectorClean.moved_selector.scratch_zero
  refine {
    present := ?_
    active_word := ?_
    moved_word := movedResult }
  · intro current
    have presentOutside : oraclePresentWireAt p current ∉
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).moved).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      intro movedMember
      have presentMember : oraclePresentWireAt p current ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).present).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        change (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).present).ancillaWire current ∈ _
        rw [RegisterSlice.wireList]
        exact List.mem_map.mpr ⟨current, List.mem_finRange current, rfl⟩
      have disjoint :
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).present).wireList :
              List (Wire p.ancillaWidth p.systemWidth)).Disjoint
            ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).moved).wireList :
                List (Wire p.ancillaWidth p.systemWidth)) := by
        apply RegisterSlice.wireList_disjoint_of_end_le_start
        simp [QLayout.oracleSlice, RegisterSlice.compose,
          OracleWorkLayout.canonical]
        omega
      exact (List.disjoint_left.mp disjoint) presentMember movedMember
    calc
      states.afterMoveBackward (oraclePresentWireAt p current) =
          states.afterSelector (oraclePresentWireAt p current) := by
        rw [states.moveBackward_eq, states.moved_eq]
        exact runBasis_rowEventMovedComputation_outside_movedSlice p slot offset
          states.afterSelector selectorClean _ presentOutside
      _ = input (oraclePresentWireAt p current) := by
        rw [states.selector_eq]
        exact runBasis_rowEventSelectorCompute_other p slot offset input
          specification.event_clean _ (by
            simpa [oraclePresentWireAt, oracleSelectedWire,
              oracleSingletonWire] using
              oracleSlice_ancillaWire_ne_of_localIndex_ne p
                (OracleWorkLayout.canonical p).present
                (OracleWorkLayout.canonical p).selected current 0 (by
                  simp [OracleWorkLayout.canonical]
                  omega))
      _ = decide (current.val < configuration.1.card) :=
        specification.present current
  · intro current currentActive
    calc
      readWires (registerWordAt p (systemWires p) current)
          states.afterMoveBackward =
          readWires (registerWordAt p (systemWires p) current)
            states.afterSelector := by
        rw [states.moveBackward_eq, states.moved_eq]
        apply List.map_congr_left
        intro wire member
        exact runBasis_rowEventMovedComputation_outside_movedSlice p slot offset
          states.afterSelector selectorClean wire
            ((List.disjoint_left.mp (systemWires_disjoint_oracleMovedSlice p))
              (mem_register_of_mem_registerWordAt p (systemWires p) current
                member))
      _ = readWires (registerWordAt p (systemWires p) current) input := by
        rw [states.selector_eq]
        apply List.map_congr_left
        intro wire member
        exact runBasis_rowEventSelectorCompute_other p slot offset input
          specification.event_clean wire (fun equal =>
            oracleSelectedWire_not_mem_systemWires p (equal ▸
              mem_register_of_mem_registerWordAt p (systemWires p) current
                member))
      _ = siteWordBits p
          (configuration.siteAt ⟨current.val, currentActive⟩) :=
        specification.active_word current currentActive

/-- persistent入力のcandidate全0条件はrow branch計算直後まで保存される。 -/
theorem RowOraclePersistentConditionsSpec.afterBranch_candidateZero
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOraclePersistentConditionsSpec p configuration selector input)
    (slot : Fin p.K) (offset : Fin 6) :
    CandidateRegionClean p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have afterBranchClean : EventSortCleanInput p states.afterBranch :=
    rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input
      specification.event_clean
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    have selectorClean : EventSortCleanInput p states.afterSelector := by
      rw [states.selector_eq]
      exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input
        specification.event_clean
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.moved_eq]
      exact EventSortCleanInput.of_rowEventMovedCopy p slot _ selectorClean
    have movedClean : EventSortCleanInput p states.afterMoveBackward := by
      rw [states.moveBackward_eq]
      exact EventSortCleanInput.of_rowEventMoveBackward p offset _ copiedClean
    rw [states.membership_eq]
    exact EventSortCleanInput.of_rowEventMembership p slot _ movedClean
  have candidateAfterMove :
      readWires ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) states.afterMoveBackward =
        readWires ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).candidate).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) input :=
    rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMoveBackward_laterSlice p slot offset input
      specification.event_clean (OracleWorkLayout.canonical p).candidate (by
        simp [OracleWorkLayout.canonical])
  have candidateAfterMembership :
      readWires ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) states.afterMembership =
        readWires ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).candidate).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) states.afterMoveBackward :=
    rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMembership_earlierSlice p slot offset input
      specification.event_clean (OracleWorkLayout.canonical p).candidate (by
        simp [OracleWorkLayout.canonical])
  have candidateAfterBranch :
      readWires ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) states.afterBranch =
        readWires ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).candidate).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) states.afterMembership := by
    apply List.map_congr_left
    intro wire member
    rw [states.branch_eq]
    exact runBasis_rowEventBranchCompute_other p slot offset
      states.afterMembership membershipClean wire (by
        have branchMember : oracleBranchWire p ∈
            ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).branch).wireList :
                List (Wire p.ancillaWidth p.systemWidth)) := by
          simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
        exact oracleSliceMembers_ne_of_end_le_start p
          (OracleWorkLayout.canonical p).candidate
          (OracleWorkLayout.canonical p).branch (by
            simp [OracleWorkLayout.canonical]
            omega) member branchMember)
  have candidateEqual :
      readWires ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) states.afterBranch =
        readWires ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).candidate).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) input :=
    candidateAfterBranch.trans (candidateAfterMembership.trans candidateAfterMove)
  refine {
    data_zero := ?_
    marker_zero := ?_ }
  · intro word
    calc
      readWires ((candidateWordAt p word).take p.wordWidth)
          states.afterBranch =
          readWires ((candidateWordAt p word).take p.wordWidth) input := by
        apply List.map_congr_left
        intro wire member
        exact readWires_eq_at_of_eq _ _ _ candidateEqual
          (candidateWordAt_mem_candidateSlice p word
            (List.mem_of_mem_take member))
      _ = List.replicate p.wordWidth false :=
        specification.candidate_zero.data_zero word
  · intro word
    exact (readWires_eq_at_of_eq _ _ _ candidateEqual
      (candidateMarkerWire_mem_candidateSlice p word)).trans
        (specification.candidate_zero.marker_zero word)

/-- active row event のprefix計算がcandidate変更前に満たす完全な値仕様。 -/
structure RowEventActivePrefixSpec (p : QParameters)
    (configuration : QConfiguration p) (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- branch計算直後もevent/sort workはcleanである。 -/
  after_branch_clean : EventSortCleanInput p
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
  /-- 全受理条件が成立し、branch flagは真である。 -/
  branch_true : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
    (oracleBranchWire p) = true
  /-- persistent degree one-hotはbranch計算後も保存される。 -/
  degree_oneHot : ∀ current : Fin p.K,
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleDegreeWireAt p current) =
        decide (current.val + 1 = configuration.1.card)
  /-- 逆移動したsource wordはbranch計算後も保存される。 -/
  moved_word : readWires (oracleMovedWires p)
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch =
    siteWordBits p
      (moveSiteBackward (configuration.siteAt ⟨slot.val, active⟩)
        (rowEventDirection offset))
  /-- candidate生成後も合法配置・sourceのmembership入力仕様を満たす。 -/
  candidates_membership : ConfigurationMembershipInput p (systemWires p)
    configuration
      (moveSiteBackward (configuration.siteAt ⟨slot.val, active⟩)
        (rowEventDirection offset))
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates
  /-- candidate生成後の値関数は入力配置のcanonical列に一致する。 -/
  candidates_values : qCandidateValue p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates =
    configurationCandidateValue p configuration

/--
合法persistent状態で選択slotが存在し、逆移動sourceが不在で、collision時に次数の空きが
あれば、selector・membership・branch・candidate準備のactual正本を完全に合成できる。
-/
theorem rowEventActivePrefix_correct
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOraclePersistentConditionsSpec p configuration
      (selectorOfSlotOffset slot offset) input)
    (sourceAbsent : moveSiteBackward
      (configuration.siteAt ⟨slot.val, active⟩) (rowEventDirection offset) ∉
        configuration.1)
    (collisionRoom : offset.val % 2 = 1 → configuration.1.card < p.K) :
    RowEventActivePrefixSpec p configuration slot offset active input := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  let source := moveSiteBackward (configuration.siteAt ⟨slot.val, active⟩)
    (rowEventDirection offset)
  have selectorMatches : rowEventSelectorMatches p slot offset input = true := by
    simp [rowEventSelectorMatches, diagonalSelectorMatches,
      specification.selector_bits, selectorOfSlotOffset]
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input
      specification.event_clean
  have movedClean : EventSortCleanInput p states.afterMoveBackward := by
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.moved_eq]
      exact EventSortCleanInput.of_rowEventMovedCopy p slot _ selectorClean
    rw [states.moveBackward_eq]
    exact EventSortCleanInput.of_rowEventMoveBackward p offset _ copiedClean
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    rw [states.membership_eq]
    exact EventSortCleanInput.of_rowEventMembership p slot _ movedClean
  have afterBranchClean : EventSortCleanInput p states.afterBranch :=
    rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input
      specification.event_clean
  have movedMembership :=
    specification.afterMoveBackward_membership slot offset active
  have flagsZero := specification.afterMoveBackward_membershipZero slot offset
  have membershipAbsent : states.afterMembership (oracleAbsentWire p) = true := by
    rw [states.membership_eq]
    exact runBasis_rowEventMembership_accepts_absent p configuration source slot
      states.afterMoveBackward (by simpa [source] using movedMembership)
      {
        equalWork_zero := movedClean.moved_selector.compare_zero
        scratch_zero := movedClean.moved_selector.scratch_zero }
      flagsZero (by simpa [source] using sourceAbsent)
  have earlierValue {width : Nat}
      (earlier : RegisterSlice p.oracleWorkWidth width)
      (beforeSelected : earlier.start + width ≤
        (OracleWorkLayout.canonical p).selected.start)
      (beforeMoved : earlier.start + width ≤
        (OracleWorkLayout.canonical p).moved.start)
      (beforeEqual : earlier.start + width ≤
        (OracleWorkLayout.canonical p).membershipEqual.start)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice earlier).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
      states.afterMembership wire = input wire := by
    have selectorDifferent : wire ≠ oracleSelectedWire p := by
      have selectedMember : oracleSelectedWire p ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).selected).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
      exact oracleSliceMembers_ne_of_end_le_start p earlier
        (OracleWorkLayout.canonical p).selected beforeSelected member
        selectedMember
    have movedOutside : wire ∉ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).moved).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      intro movedMember
      have disjoint :
          ((QLayout.oracleSlice earlier).wireList :
            List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).moved).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        apply RegisterSlice.wireList_disjoint_of_end_le_start
        simp [QLayout.oracleSlice, RegisterSlice.compose]
        omega
      exact (List.disjoint_left.mp disjoint) member movedMember
    calc
      states.afterMembership wire = states.afterMoveBackward wire := by
        exact readWires_eq_at_of_eq _ _ _
          (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMembership_earlierSlice p slot offset
            input specification.event_clean earlier beforeEqual) member
      _ = states.afterSelector wire := by
        rw [states.moveBackward_eq, states.moved_eq]
        exact runBasis_rowEventMovedComputation_outside_movedSlice p slot offset
          states.afterSelector selectorClean wire movedOutside
      _ = input wire := by
        rw [states.selector_eq]
        exact runBasis_rowEventSelectorCompute_other p slot offset input
          specification.event_clean wire selectorDifferent
  have selectedAfterSelector : states.afterSelector (oracleSelectedWire p) =
      true := by
    rw [states.selector_eq, runBasis_rowEventSelectorCompute p slot offset input
      specification.event_clean.moved_selector.scratch_zero, selectorMatches]
    simp [xBasisAction, specification.selected_zero]
  have selectedAfterMembership : states.afterMembership (oracleSelectedWire p) =
      true := by
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
    have selectedAfterMove : states.afterMoveBackward (oracleSelectedWire p) =
        true := by
      rw [states.moveBackward_eq, states.moved_eq]
      exact (runBasis_rowEventMovedComputation_outside_movedSlice p slot offset
        states.afterSelector selectorClean _ selectedOutside).trans
          selectedAfterSelector
    have selectedValues := rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMembership_earlierSlice p
      slot offset input specification.event_clean
        (OracleWorkLayout.canonical p).selected (by
          simp [OracleWorkLayout.canonical]
          omega)
    exact (readWires_eq_at_of_eq _ _ _ selectedValues (by
      simp [oracleSelectedWire, oracleSingletonWire,
        RegisterSlice.wireList])).trans selectedAfterMove
  have presentAfterMembership : states.afterMembership
      (oraclePresentWireAt p slot) = true := by
    have value := earlierValue (OracleWorkLayout.canonical p).present
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (oraclePresentWireAt p slot) (by
        change (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).present).ancillaWire slot ∈ _
        rw [RegisterSlice.wireList]
        exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩)
    rw [value, specification.present slot]
    exact decide_eq_true active
  have legalAfterMembership : states.afterMembership (oracleLegalWire p) = true := by
    exact (earlierValue (OracleWorkLayout.canonical p).legal
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (oracleLegalWire p) (by
        simp [oracleLegalWire, RegisterSlice.wireList])).trans
          specification.legal
  have degreeConditionAfterMembership : states.afterMembership
      (oracleDegreeConditionWire p) = decide (configuration.1.card < p.K) := by
    exact (earlierValue (OracleWorkLayout.canonical p).degreeCondition
      (by simp [OracleWorkLayout.canonical])
      (by simp [OracleWorkLayout.canonical])
      (by simp [OracleWorkLayout.canonical]; omega)
      (oracleDegreeConditionWire p) (by
        simp [oracleDegreeConditionWire, oracleSingletonWire,
          RegisterSlice.wireList])).trans specification.degree_condition
  have branchZeroAfterMembership : states.afterMembership
      (oracleBranchWire p) = false := by
    have afterMoveValues :=
      rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMoveBackward_laterSlice p slot offset input
        specification.event_clean (OracleWorkLayout.canonical p).branch (by
          simp [OracleWorkLayout.canonical]
          omega)
    have afterMoveZero : states.afterMoveBackward (oracleBranchWire p) = false :=
      (readWires_eq_at_of_eq _ _ _ afterMoveValues (by
        simp [oracleBranchWire, oracleSingletonWire,
          RegisterSlice.wireList])).trans specification.branch_zero
    rw [states.membership_eq]
    exact (runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other p (systemWires p)
      (systemWires_membershipInputLayout p) slot false states.afterMoveBackward
      {
        equalWork_zero := movedClean.moved_selector.compare_zero
        scratch_zero := movedClean.moved_selector.scratch_zero }
      (oracleBranchWire p)
      (MembershipOutputsSeparated.of_laterSlice p
        (OracleWorkLayout.canonical p).branch (by
          simp [OracleWorkLayout.canonical]) (oracleBranchWire p) (by
            simp [oracleBranchWire, oracleSingletonWire,
              RegisterSlice.wireList]))).trans afterMoveZero
  have branchTrue : states.afterBranch (oracleBranchWire p) = true := by
    rw [states.branch_eq]
    rw [runBasis_rowEventBranchCompute_branch_canonical p slot offset
      states.afterMembership membershipClean.moved_selector.scratch_zero
      branchZeroAfterMembership]
    by_cases collision : offset.val % 2 = 1
    · have roomTrue : states.afterMembership
          (oracleDegreeConditionWire p) = true := by
        rw [degreeConditionAfterMembership]
        exact decide_eq_true (collisionRoom collision)
      simp [rowEventBranchControls, collision, allWiresTrue, readWires,
        legalAfterMembership, selectedAfterMembership, presentAfterMembership,
        membershipAbsent, roomTrue]
    · simp [rowEventBranchControls, collision, allWiresTrue, readWires,
        legalAfterMembership, selectedAfterMembership, presentAfterMembership,
        membershipAbsent]
  have degreeAfterBranch : ∀ current : Fin p.K,
      states.afterBranch (oracleDegreeWireAt p current) =
        decide (current.val + 1 = configuration.1.card) := by
    intro current
    have degreeBefore := earlierValue (OracleWorkLayout.canonical p).degree
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (oracleDegreeWireAt p current) (by
        change (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).degree).ancillaWire current ∈ _
        rw [RegisterSlice.wireList]
        exact List.mem_map.mpr ⟨current, List.mem_finRange current, rfl⟩)
    rw [states.branch_eq]
    exact (runBasis_rowEventBranchCompute_other p slot offset
      states.afterMembership membershipClean (oracleDegreeWireAt p current) (by
        simpa [oracleDegreeWireAt, oracleBranchWire, oracleSingletonWire] using
          oracleSlice_ancillaWire_ne_of_localIndex_ne p
            (OracleWorkLayout.canonical p).degree
            (OracleWorkLayout.canonical p).branch current 0 (by
              simp [OracleWorkLayout.canonical]
              omega))).trans (degreeBefore.trans (specification.degree current))
  have afterBranchMembership : ConfigurationMembershipInput p (systemWires p)
      configuration source states.afterBranch := by
    have systemAfterMembership := rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMembership_system p
      slot offset input specification.event_clean
    have systemAfterMove := movedMembership
    refine {
      present := ?_
      active_word := ?_
      moved_word := ?_ }
    · intro current
      have presentBefore := earlierValue (OracleWorkLayout.canonical p).present
        (by simp [OracleWorkLayout.canonical]; omega)
        (by simp [OracleWorkLayout.canonical]; omega)
        (by simp [OracleWorkLayout.canonical]; omega)
        (oraclePresentWireAt p current) (by
          change (QLayout.oracleSlice
            (OracleWorkLayout.canonical p).present).ancillaWire current ∈ _
          rw [RegisterSlice.wireList]
          exact List.mem_map.mpr ⟨current, List.mem_finRange current, rfl⟩)
      rw [states.branch_eq]
      exact (runBasis_rowEventBranchCompute_other p slot offset
        states.afterMembership membershipClean (oraclePresentWireAt p current) (by
          simpa [oraclePresentWireAt, oracleBranchWire, oracleSingletonWire] using
            oracleSlice_ancillaWire_ne_of_localIndex_ne p
              (OracleWorkLayout.canonical p).present
              (OracleWorkLayout.canonical p).branch current 0 (by
                simp [OracleWorkLayout.canonical]
                omega))).trans (presentBefore.trans (specification.present current))
    · intro current currentActive
      rw [states.branch_eq]
      calc
        readWires (registerWordAt p (systemWires p) current)
            ((rowEventBranchCompute p slot offset).runBasis
              reversibleGatePermutation states.afterMembership) =
            readWires (registerWordAt p (systemWires p) current)
              states.afterMembership := by
          apply List.map_congr_left
          intro wire member
          exact runBasis_rowEventBranchCompute_other p slot offset
            states.afterMembership membershipClean wire (by
              intro equal
              subst wire
              exact oracleBranchWire_not_mem_systemWires p
                (mem_register_of_mem_registerWordAt p (systemWires p)
                  current member))
        _ = readWires (registerWordAt p (systemWires p) current)
            states.afterMoveBackward := by
          apply List.map_congr_left
          intro wire member
          exact readWires_eq_at_of_eq _ _ _ systemAfterMembership
            (mem_register_of_mem_registerWordAt p (systemWires p) current member)
        _ = siteWordBits p
            (configuration.siteAt ⟨current.val, currentActive⟩) :=
          movedMembership.active_word current currentActive
    · rw [states.branch_eq]
      calc
        readWires (oracleMovedWires p)
            ((rowEventBranchCompute p slot offset).runBasis
              reversibleGatePermutation states.afterMembership) =
            readWires (oracleMovedWires p) states.afterMembership := by
          apply List.map_congr_left
          intro wire member
          exact runBasis_rowEventBranchCompute_other p slot offset
            states.afterMembership membershipClean wire (by
              have movedMember : wire ∈ ((QLayout.oracleSlice
                  (OracleWorkLayout.canonical p).moved).wireList :
                    List (Wire p.ancillaWidth p.systemWidth)) := by
                simpa [oracleMovedWires, RegisterSlice.wireList] using member
              have branchMember : oracleBranchWire p ∈
                  ((QLayout.oracleSlice
                    (OracleWorkLayout.canonical p).branch).wireList :
                      List (Wire p.ancillaWidth p.systemWidth)) := by
                simp [oracleBranchWire, oracleSingletonWire,
                  RegisterSlice.wireList]
              exact oracleSliceMembers_ne_of_end_le_start p
                (OracleWorkLayout.canonical p).moved
                (OracleWorkLayout.canonical p).branch (by
                  simp [OracleWorkLayout.canonical]
                  omega) movedMember branchMember)
        _ = siteWordBits p source := by
          rw [states.membership_eq]
          calc
            readWires (oracleMovedWires p)
                ((rowEventMembership p slot).runBasis
                  reversibleGatePermutation states.afterMoveBackward) =
                readWires (oracleMovedWires p) states.afterMoveBackward := by
              apply List.map_congr_left
              intro wire member
              exact runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other p (systemWires p)
                (systemWires_membershipInputLayout p) slot false
                states.afterMoveBackward
                {
                  equalWork_zero := movedClean.moved_selector.compare_zero
                  scratch_zero := movedClean.moved_selector.scratch_zero }
                wire (MembershipOutputsSeparated.of_earlierSlice p
                  (OracleWorkLayout.canonical p).moved (by
                    simp [OracleWorkLayout.canonical]
                    omega) wire (by
                      simpa [oracleMovedWires, RegisterSlice.wireList] using
                        member))
            _ = siteWordBits p source := by
              simpa [source] using movedMembership.moved_word
  have candidatesMembership : ConfigurationMembershipInput p (systemWires p)
      configuration source states.afterCandidates := by
    rw [states.candidates_eq]
    exact afterBranchMembership.of_prepareCandidatesSystem
  have candidatesValues : qCandidateValue p states.afterCandidates =
      configurationCandidateValue p configuration := by
    rw [states.candidates_eq]
    exact qCandidateValue_runBasis_prepareCandidates_configuration p
      configuration source states.afterBranch afterBranchMembership
        (specification.afterBranch_candidateZero slot offset)
  refine {
    after_branch_clean := afterBranchClean
    branch_true := branchTrue
    degree_oneHot := degreeAfterBranch
    moved_word := ?_
    candidates_membership := by simpa [source] using candidatesMembership
    candidates_values := candidatesValues }
  exact afterBranchMembership.moved_word

/-- branch wireはcandidate slice全体の外にある。 -/
theorem oracleBranchWire_not_mem_candidateSlice (p : QParameters) :
    oracleBranchWire p ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  simpa [oracleBranchWire, oracleSingletonWire] using
    laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).candidate
      (OracleWorkLayout.canonical p).branch (by
        simp [OracleWorkLayout.canonical]
        omega)
      ⟨0, by simp⟩

/-- row collision変更列はclean性とともにbranch wireを保存する。 -/
theorem runBasis_rowEventCollisionSequence_oracleBranch
    (p : QParameters) :
    ∀ (slots : List (Fin (p.K - 1)))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      EventSortCleanInput p input →
      (Circuit.sequence (slots.map fun degreeSlot =>
        controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot)).runBasis
          reversibleGatePermutation input (oracleBranchWire p) =
        input (oracleBranchWire p)
  | [], input, _ => rfl
  | degreeSlot :: slots, input, clean => by
      simp only [List.map_cons, Circuit.sequence]
      let next := (controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot).runBasis
        reversibleGatePermutation input
      have nextClean : EventSortCleanInput p next :=
        EventSortCleanInput.of_rowEventCollisionModifyAt p degreeSlot input clean
      calc
        (Circuit.sequence
            (slots.map fun nextSlot => controlledUpdateRowCollisionCandidateAtDegreeCircuit p nextSlot)).runBasis
              reversibleGatePermutation next (oracleBranchWire p) =
            next (oracleBranchWire p) :=
          runBasis_rowEventCollisionSequence_oracleBranch p slots next nextClean
        _ = input (oracleBranchWire p) := by
          exact runBasis_rowEventCollisionModifyAt_outside_candidateSlice p
            degreeSlot input clean (oracleBranchWire p)
              (oracleBranchWire_not_mem_candidateSlice p)

/-- row collision変更列はcandidate slice外の任意wireを保存する。 -/
theorem runBasis_rowEventCollisionSequence_outside_candidateSlice
    (p : QParameters) :
    ∀ (slots : List (Fin (p.K - 1)))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      EventSortCleanInput p input →
      ∀ (wire : Wire p.ancillaWidth p.systemWidth),
      wire ∉ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) →
      (Circuit.sequence (slots.map fun degreeSlot =>
        controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot)).runBasis
          reversibleGatePermutation input wire = input wire
  | [], input, _, wire, _ => rfl
  | degreeSlot :: slots, input, clean, wire, outside => by
      simp only [List.map_cons, Circuit.sequence]
      let next := (controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot).runBasis
        reversibleGatePermutation input
      have nextClean : EventSortCleanInput p next :=
        EventSortCleanInput.of_rowEventCollisionModifyAt p degreeSlot input clean
      calc
        (Circuit.sequence
            (slots.map fun nextSlot => controlledUpdateRowCollisionCandidateAtDegreeCircuit p nextSlot)).runBasis
              reversibleGatePermutation next wire = next wire :=
          runBasis_rowEventCollisionSequence_outside_candidateSlice p slots next
            nextClean wire outside
        _ = input wire :=
          runBasis_rowEventCollisionModifyAt_outside_candidateSlice p degreeSlot
            input clean wire outside

/-- row replacement/collision変更段はcandidate slice外の任意wireを保存する。 -/
theorem runBasis_rowEventModify_outside_candidateSlice
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation input wire =
      input wire := by
  by_cases collision : offset.val % 2 = 1
  · rw [controlledUpdateSelectedRowCandidateWordCircuit, if_pos collision, controlledUpdateSelectedRowCollisionCandidateWordCircuit]
    exact runBasis_rowEventCollisionSequence_outside_candidateSlice p
      (List.finRange (p.K - 1)) input clean wire outside
  · rw [controlledUpdateSelectedRowCandidateWordCircuit, if_neg collision]
    exact runBasis_rowEventReplacementModify_outside_candidateSlice p slot input
      wire outside

/-- row replacement/collisionのどちらでもcandidate変更段はbranch wireを保存する。 -/
theorem runBasis_rowEventModify_oracleBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation input
        (oracleBranchWire p) = input (oracleBranchWire p) := by
  by_cases collision : offset.val % 2 = 1
  · rw [controlledUpdateSelectedRowCandidateWordCircuit, if_pos collision, controlledUpdateSelectedRowCollisionCandidateWordCircuit]
    exact runBasis_rowEventCollisionSequence_oracleBranch p
      (List.finRange (p.K - 1)) input clean
  · rw [controlledUpdateSelectedRowCandidateWordCircuit, if_neg collision]
    exact runBasis_rowEventReplacementModify_outside_candidateSlice p slot input
      (oracleBranchWire p) (oracleBranchWire_not_mem_candidateSlice p)

/--
branch計算後がtracked cleanなら、candidate生成・変更・bitonic sortを通っても
compute最終状態のbranch bitはbranch計算直後の値に一致する。
-/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_branch_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output (oracleBranchWire p) =
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
        (oracleBranchWire p) := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have candidatesClean : EventSortCleanInput p states.afterCandidates := by
    rw [states.candidates_eq]
    exact EventSortCleanInput.of_xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)
      (systemWires_candidateInputLayout p) _ clean
  have modifyClean : EventSortCleanInput p states.afterModify := by
    rw [states.modify_eq]
    exact EventSortCleanInput.of_rowEventModify p slot offset _ candidatesClean
  calc
    states.output (oracleBranchWire p) =
        states.afterModify (oracleBranchWire p) := by
      rw [states.sort_eq]
      exact qBitonicSort_preserves_oracleBranch p states.afterModify
        modifyClean.sort_compare_zero modifyClean.sort_scratch_zero
        modifyClean.sort_history_zero
    _ = states.afterCandidates (oracleBranchWire p) := by
      rw [states.modify_eq]
      exact runBasis_rowEventModify_oracleBranch p slot offset
        states.afterCandidates candidatesClean
    _ = states.afterBranch (oracleBranchWire p) := by
      rw [states.candidates_eq]
      exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_oracleBranch p (systemWires p)
        (systemWires_candidateInputLayout p) states.afterBranch

/--
candidate sliceにもsort historyにも属さないwireは、tracked cleanなbranch後状態から
candidate生成・変更・bitonic sortを通っても保存される。
-/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_preserves_outsideCandidateHistories
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideCandidate : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)))
    (outsideHistories : ∀ instruction ∈ qTypedBitonicSchedule p,
      wire ≠ (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) :
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output wire =
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch wire := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have candidatesClean : EventSortCleanInput p states.afterCandidates := by
    rw [states.candidates_eq]
    exact EventSortCleanInput.of_xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)
      (systemWires_candidateInputLayout p) _ clean
  have modifyClean : EventSortCleanInput p states.afterModify := by
    rw [states.modify_eq]
    exact EventSortCleanInput.of_rowEventModify p slot offset _ candidatesClean
  calc
    states.output wire = states.afterModify wire := by
      rw [states.sort_eq]
      rw [runBasis_reversiblySortCandidateWordsAndRestoreHistoryCircuit_eq_reference p
        states.afterModify modifyClean.sort_compare_zero
        modifyClean.sort_scratch_zero modifyClean.sort_history_zero]
      exact canonicalCandidateSortWithHistoryRestorationSpec_preserves_other p
        (qTypedBitonicSchedule p) states.afterModify wire
          (fun word member => outsideCandidate
            (candidateWordAt_mem_candidateSlice p word member))
          outsideHistories
    _ = states.afterCandidates wire := by
      rw [states.modify_eq]
      exact runBasis_rowEventModify_outside_candidateSlice p slot offset
        states.afterCandidates candidatesClean wire outsideCandidate
    _ = states.afterBranch wire := by
      rw [states.candidates_eq]
      exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_outside_candidateSlice p
        (systemWires p) (systemWires_candidateInputLayout p) states.afterBranch
          wire outsideCandidate

/--
candidate sliceとsort-history sliceより前に配置された任意oracle sliceは、
row eventのcandidate生成以降でpointwiseに保存される。
-/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_preserves_earlyOracleSlice
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch)
    {width : Nat} (slice : RegisterSlice p.oracleWorkWidth width)
    (beforeCandidate : slice.start + width ≤
      (OracleWorkLayout.canonical p).candidate.start)
    (beforeHistories : slice.start + width ≤
      (OracleWorkLayout.canonical p).sortFlags.start)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ ((QLayout.oracleSlice slice).wireList :
      List (Wire p.ancillaWidth p.systemWidth))) :
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output wire =
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch wire := by
  have candidateDisjoint :
      ((QLayout.oracleSlice slice).wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).candidate).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [QLayout.oracleSlice, RegisterSlice.compose]
    omega
  have historyDisjoint :
      ((QLayout.oracleSlice slice).wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [QLayout.oracleSlice, RegisterSlice.compose]
    omega
  apply rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_preserves_outsideCandidateHistories p
    slot offset input clean wire
  · intro candidateMember
    exact (List.disjoint_left.mp candidateDisjoint) member candidateMember
  · intro instruction instructionMember equal
    apply (List.disjoint_left.mp historyDisjoint) member
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history, equal.symm⟩

/-- candidate生成以降はpredecessor sourceを保持するmoved registerを保存する。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_movedWires_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    readWires (oracleMovedWires p)
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output =
      readWires (oracleMovedWires p)
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch := by
  apply List.map_congr_left
  intro wire member
  apply rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_preserves_earlyOracleSlice p slot offset
    input clean (OracleWorkLayout.canonical p).moved
  · simp [OracleWorkLayout.canonical]
  · simp [OracleWorkLayout.canonical]
  · simpa [oracleMovedWires, RegisterSlice.wireList] using member

/-- candidate生成以降はpersistent degree one-hot列の各wireを保存する。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_degree_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch)
    (degreeSlot : Fin p.K) :
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
        (oracleDegreeWireAt p degreeSlot) =
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
        (oracleDegreeWireAt p degreeSlot) := by
  apply rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_preserves_earlyOracleSlice p slot offset
    input clean (OracleWorkLayout.canonical p).degree
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [oracleDegreeWireAt, RegisterSlice.wireList]

/-- sorted writer は column-key と key-signal 以外の oracle work をすべて保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_diagonalOracleWork
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    BasisAgreeOn (diagonalOracleWorkWires p)
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p) degreeChange input)
      input := by
  intro wire workMember
  apply xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_columnKey
  · intro keyMember
    exact (List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnKey p))
      (List.mem_append_right _ workMember) keyMember
  · intro equal
    subst wire
    exact keySignalWire_not_mem_rowEventBroadSupport p
      (List.mem_append_right _ workMember)

/-- sorted writer は全candidate wordの自然数値関数を保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_qCandidateValue
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    qCandidateValue p
        (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
          (by simp [columnKeyWires]) (keySignalWire p) degreeChange input) =
      qCandidateValue p input := by
  funext word
  unfold qCandidateValue
  apply congrArg littleEndianNat
  apply List.map_congr_left
  intro wire member
  apply xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_diagonalOracleWork p degreeChange
    input wire
  apply oracleSliceWire_mem_oracleWork p
    (OracleWorkLayout.canonical p).candidate
  exact candidateWordAt_mem_candidateSlice p word member

/-- sorted writer はpredecessor sourceを保持するmoved registerを保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_movedWires
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (oracleMovedWires p)
        (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
          (by simp [columnKeyWires]) (keySignalWire p) degreeChange input) =
      readWires (oracleMovedWires p) input := by
  apply List.map_congr_left
  intro wire member
  apply xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_diagonalOracleWork p degreeChange
    input wire
  apply oracleSliceWire_mem_oracleWork p
    (OracleWorkLayout.canonical p).moved
  simpa [oracleMovedWires, RegisterSlice.wireList] using member

/-- sorted writer はevent useを制御するbranch bitを保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_branch
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p) degreeChange input
        (oracleBranchWire p) =
      input (oracleBranchWire p) := by
  exact xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_diagonalOracleWork p degreeChange
    input (oracleBranchWire p)
      (oracleBranchWire_mem_diagonalOracleWorkWires p)

/--
sorted writer は column-key と key-signal 以外の wire を保存するため、
moved-selector が後段で要求する比較・AND・position・pair の clean 条件も保存する。
-/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_movedSelectorClean
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : WriteMovedSelectorSlotClean p input) :
    WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p) degreeChange input) := by
  let output := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
    (by simp [columnKeyWires]) (keySignalWire p) degreeChange input
  have preserveWork : ∀ wire ∈ diagonalOracleWorkWires p,
      output wire = input wire := by
    exact xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_diagonalOracleWork p degreeChange
      input
  refine {
    compare_zero := ?_
    scratch_zero := ?_
    position_zero := ?_
    pair_zero := ?_ }
  · calc
      readWires (oracleCompareWorkWires p) output =
          readWires (oracleCompareWorkWires p) input := by
        apply List.map_congr_left
        intro wire member
        apply preserveWork wire
        apply oracleSliceWire_mem_oracleWork p
          (OracleWorkLayout.canonical p).compareWork
        simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member
      _ = List.replicate (oracleCompareWorkWires p).length false :=
        clean.compare_zero
  · intro wire member
    change output wire = false
    rw [preserveWork wire (decoderAndScratchWire_mem_diagonalOracleWorkWires p
      member)]
    exact clean.scratch_zero wire member
  · change output (oraclePositionWire p) = false
    rw [preserveWork (oraclePositionWire p)]
    · exact clean.position_zero
    · apply oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).positionMatch
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).positionMatch).ancillaWire _ ∈ _
      simp [RegisterSlice.wireList]
  · change output (oraclePairWire p) = false
    rw [preserveWork (oraclePairWire p)]
    · exact clean.pair_zero
    · apply oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).pair
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).pair).ancillaWire _ ∈ _
      simp [RegisterSlice.wireList]

/--
active row event の actual compute 末尾について writer 接続に必要な数学的事実をまとめる。
これは回路仕様を仮定する契約ではなく、各正本 subcircuit の証明から内部生成する中間記録である。
-/
structure RowEventActiveComputedSpec (p : QParameters)
    (configuration : QConfiguration p) (source : QSite p)
    (member : source ∈ configuration.1) (offset : Fin 6)
    (degreeSlot : Fin p.K)
    (computed : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 選択 degree と rep/coll 変化量は predecessor 配置の次数に一致する。 -/
  output_degree : Int.ofNat (degreeSlot.val + 1) + rowEventDegreeChange offset =
    Int.ofNat configuration.1.card
  /-- active compute 末尾の branch bit は真である。 -/
  branch_true : computed (oracleBranchWire p) = true
  /-- compute 末尾でも persistent degree 列は同じ one-hot を保持する。 -/
  degree_oneHot : ∀ slot : Fin p.K,
    computed (oracleDegreeWireAt p slot) = decide (slot = degreeSlot)
  /-- sort 後の全 candidate 値は predecessor 配置の canonical 昇順関数である。 -/
  candidate_values : qCandidateValue p computed =
    configurationCandidateValue p configuration
  /-- moved register は predecessor で選ばれる source site を保持する。 -/
  moved_word : readWires (oracleMovedWires p) computed = siteWordBits p source
  /-- sorted writer が使う AND scratch は全て 0 に戻っている。 -/
  scratch_zero : ∀ wire ∈ decoderAndScratchWires p, computed wire = false
  /-- sorted writer の一時 pair bit は 0 に戻っている。 -/
  pair_zero : computed (oraclePairWire p) = false
  /-- sorted writer 後の moved-selector 一時領域も canonical clean 条件を満たす。 -/
  moved_clean : WriteMovedSelectorSlotClean p
    (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
      (by simp [columnKeyWires]) (keySignalWire p)
      (rowEventDegreeChange offset) computed)

/--
compute 最終状態そのものが moved-selector 用に clean なら、sorted writer による
clean 保存を用いて active compute 仕様を一括して構成できる。
-/
theorem RowEventActiveComputedSpec.of_outputClean
    {p : QParameters} {configuration : QConfiguration p}
    {source : QSite p} {member : source ∈ configuration.1}
    {offset : Fin 6} {degreeSlot : Fin p.K}
    {computed : JointBasis p.ancillaWidth p.systemWidth}
    (outputDegree : Int.ofNat (degreeSlot.val + 1) +
      rowEventDegreeChange offset = Int.ofNat configuration.1.card)
    (branchTrue : computed (oracleBranchWire p) = true)
    (degreeOneHot : ∀ slot : Fin p.K,
      computed (oracleDegreeWireAt p slot) = decide (slot = degreeSlot))
    (candidateValues : qCandidateValue p computed =
      configurationCandidateValue p configuration)
    (movedWord : readWires (oracleMovedWires p) computed =
      siteWordBits p source)
    (clean : WriteMovedSelectorSlotClean p computed) :
    RowEventActiveComputedSpec p configuration source member offset degreeSlot
      computed := by
  refine {
    output_degree := outputDegree
    branch_true := branchTrue
    degree_oneHot := degreeOneHot
    candidate_values := candidateValues
    moved_word := movedWord
    scratch_zero := clean.scratch_zero
    pair_zero := clean.pair_zero
    moved_clean := ?_ }
  exact xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_movedSelectorClean p
    (rowEventDegreeChange offset) computed clean

/--
branch計算直後のclean・branch・degree・moved仕様と、sort後candidate仕様から、
active compute最終仕様を一括構成する。suffixの保存は正本回路定理から内部導出する。
-/
theorem RowEventActiveComputedSpec.of_afterBranch
    {p : QParameters} {configuration : QConfiguration p}
    {source : QSite p} {member : source ∈ configuration.1}
    {offset : Fin 6} {degreeSlot : Fin p.K}
    {slot : Fin p.K}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (outputDegree : Int.ofNat (degreeSlot.val + 1) +
      rowEventDegreeChange offset = Int.ofNat configuration.1.card)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch)
    (branchTrue : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleBranchWire p) = true)
    (degreeOneHot : ∀ current : Fin p.K,
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
        (oracleDegreeWireAt p current) = decide (current = degreeSlot))
    (candidateValues : qCandidateValue p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output =
        configurationCandidateValue p configuration)
    (movedWord : readWires (oracleMovedWires p)
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch =
        siteWordBits p source) :
    RowEventActiveComputedSpec p configuration source member offset degreeSlot
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output := by
  apply RowEventActiveComputedSpec.of_outputClean outputDegree
  · exact (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_branch_of_afterBranch p slot offset input
      clean).trans branchTrue
  · intro current
    exact (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_degree_of_afterBranch p slot offset input
      clean current).trans (degreeOneHot current)
  · exact candidateValues
  · exact (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_movedWires_of_afterBranch p slot offset
      input clean).trans movedWord
  · exact rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_clean_of_afterBranch p slot offset input
      clean

/--
replacement offsetのactual candidate生成・置換・bitonic sortを合成すると、sort後の
candidate値はpredecessor configurationのcanonical列に一致する。
-/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_replacement_candidateValues
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (noCollision : moveSite source direction ∉ configuration.1.erase source)
    (slot : Fin p.K) (offset : Fin 6)
    (replacement : offset.val % 2 ≠ 1)
    (active : slot.val < (eventOutput configuration source direction).1.card)
    (arrivalAt :
      (eventOutput configuration source direction).siteAt ⟨slot.val, active⟩ =
        moveSite source direction)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (systemWires p)
      (eventOutput configuration source direction) source
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates)
    (valuesBefore : qCandidateValue p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates =
        configurationCandidateValue p
          (eventOutput configuration source direction))
    (branchTrue : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleBranchWire p) = true)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    qCandidateValue p (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output =
      configurationCandidateValue p configuration := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have candidatesBranch : states.afterCandidates (oracleBranchWire p) = true := by
    calc
      states.afterCandidates (oracleBranchWire p) =
          states.afterBranch (oracleBranchWire p) := by
        rw [states.candidates_eq]
        exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_oracleBranch p (systemWires p)
          (systemWires_candidateInputLayout p) states.afterBranch
      _ = true := branchTrue
  have modifyClean : EventSortCleanInput p states.afterModify :=
    rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterModify_clean_of_afterBranch p slot offset input
      clean
  have modifyEq : states.afterModify =
      (controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis reversibleGatePermutation
        states.afterCandidates := by
    rw [states.modify_eq, controlledUpdateSelectedRowCandidateWordCircuit, if_neg replacement]
  rw [states.sort_eq, modifyEq]
  apply rowEventReplacementModify_sort_correct configuration source member
    direction noCollision slot active arrivalAt states.afterCandidates
      specification valuesBefore candidatesBranch
  · simpa [modifyEq] using modifyClean.sort_compare_zero
  · intro wire wireMember
    simpa [modifyEq] using modifyClean.sort_scratch_zero wire wireMember
  · intro instruction instructionMember
    simpa [modifyEq] using modifyClean.sort_history_zero instruction
      instructionMember

/-- candidate sliceはpersistent degree sliceと交わらない。 -/
theorem oracleDegreeWireAt_not_mem_candidateSlice
    (p : QParameters) (degreeSlot : Fin p.K) :
    oracleDegreeWireAt p degreeSlot ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  have disjoint :
      ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).degree).wireList :
            List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).candidate).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  intro candidateMember
  apply (List.disjoint_left.mp disjoint) _ candidateMember
  simp [oracleDegreeWireAt, RegisterSlice.wireList]

/-- candidate生成回路はpersistent degree wireを保存する。 -/
theorem runBasis_xorConfigurationIntoCandidateRegisterCircuit_degree
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (degreeSlot : Fin p.K) :
    (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
        reversibleGatePermutation input (oracleDegreeWireAt p degreeSlot) =
      input (oracleDegreeWireAt p degreeSlot) := by
  exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_outside_candidateSlice p
    (systemWires p) (systemWires_candidateInputLayout p) input
      (oracleDegreeWireAt p degreeSlot)
      (oracleDegreeWireAt_not_mem_candidateSlice p degreeSlot)

/--
collision offsetのactual candidate生成・追加・bitonic sortを合成すると、sort後の
candidate値はpredecessor configurationのcanonical列に一致する。
-/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_collision_candidateValues
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (collision : moveSite source direction ∈ configuration.1.erase source)
    (slot : Fin p.K) (offset : Fin 6)
    (collisionOffset : offset.val % 2 = 1)
    (activeSlot : Fin (p.K - 1))
    (slotAtBoundary : activeSlot.val + 1 =
      (eventOutput configuration source direction).1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (systemWires p)
      (eventOutput configuration source direction) source
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates)
    (valuesBefore : qCandidateValue p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates =
        configurationCandidateValue p
          (eventOutput configuration source direction))
    (branchTrue : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleBranchWire p) = true)
    (activeDegree : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleDegreeWireAt p
        (rowEventCollisionDegreeIndex p activeSlot)) = true)
    (otherDegree : ∀ degreeSlot : Fin (p.K - 1),
      degreeSlot ≠ activeSlot →
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
        (oracleDegreeWireAt p
          (rowEventCollisionDegreeIndex p degreeSlot)) = false)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    qCandidateValue p (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output =
      configurationCandidateValue p configuration := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have candidatesClean : EventSortCleanInput p states.afterCandidates := by
    rw [states.candidates_eq]
    exact EventSortCleanInput.of_xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)
      (systemWires_candidateInputLayout p) _ clean
  have candidatesBranch : states.afterCandidates (oracleBranchWire p) = true := by
    calc
      states.afterCandidates (oracleBranchWire p) =
          states.afterBranch (oracleBranchWire p) := by
        rw [states.candidates_eq]
        exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_oracleBranch p (systemWires p)
          (systemWires_candidateInputLayout p) states.afterBranch
      _ = true := branchTrue
  have candidatesActiveDegree : states.afterCandidates
      (oracleDegreeWireAt p
        (rowEventCollisionDegreeIndex p activeSlot)) = true := by
    calc
      states.afterCandidates
          (oracleDegreeWireAt p
            (rowEventCollisionDegreeIndex p activeSlot)) =
        states.afterBranch
          (oracleDegreeWireAt p
            (rowEventCollisionDegreeIndex p activeSlot)) := by
          rw [states.candidates_eq]
          exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_degree p states.afterBranch _
      _ = true := activeDegree
  have candidatesOtherDegree : ∀ degreeSlot : Fin (p.K - 1),
      degreeSlot ≠ activeSlot →
      states.afterCandidates
        (oracleDegreeWireAt p
          (rowEventCollisionDegreeIndex p degreeSlot)) = false := by
    intro degreeSlot different
    calc
      states.afterCandidates
          (oracleDegreeWireAt p
            (rowEventCollisionDegreeIndex p degreeSlot)) =
        states.afterBranch
          (oracleDegreeWireAt p
            (rowEventCollisionDegreeIndex p degreeSlot)) := by
          rw [states.candidates_eq]
          exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_degree p states.afterBranch _
      _ = false := otherDegree degreeSlot different
  have modifyClean : EventSortCleanInput p states.afterModify :=
    rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterModify_clean_of_afterBranch p slot offset input
      clean
  have modifyEq : states.afterModify =
      (controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis reversibleGatePermutation
        states.afterCandidates := by
    rw [states.modify_eq, controlledUpdateSelectedRowCandidateWordCircuit, if_pos collisionOffset]
  rw [states.sort_eq, modifyEq]
  apply rowEventCollisionModify_sort_correct_of_values configuration source member
    direction collision activeSlot slotAtBoundary states.afterCandidates
      valuesBefore specification.moved_word
      candidatesClean.moved_selector.scratch_zero
      candidatesClean.moved_selector.pair_zero candidatesBranch
      candidatesActiveDegree candidatesOtherDegree
  · simpa [modifyEq] using modifyClean.sort_compare_zero
  · intro wire wireMember
    simpa [modifyEq] using modifyClean.sort_scratch_zero wire wireMember
  · intro instruction instructionMember
    simpa [modifyEq] using modifyClean.sort_history_zero instruction
      instructionMember

/-- 配置に属するsiteのcanonical slotは配置粒子数未満である。 -/
theorem slotOfMember_lt_configurationCard
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) :
    (slotOfMember configuration site member).val < configuration.1.card := by
  unfold slotOfMember
  exact ((configuration.1.orderIsoOfFin rfl).symm ⟨site, member⟩).isLt

/--
物理eventの出力配置とcanonical row selectorを保持するpersistent状態では、actual row
event compute末尾がpredecessor配置のactive writer仕様を満たす。
-/
theorem rowEventActiveComputedSpec_physicalEvent
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOraclePersistentConditionsSpec p
      (eventOutput configuration source direction)
      (rowSelectorForEvent configuration source member direction) input) :
    let outputConfiguration := eventOutput configuration source direction
    let moved := moveSite source direction
    let movedMember : moved ∈ outputConfiguration.1 :=
      moveSite_mem_updateConfiguration configuration (source, direction) member
    let slot := slotOfMember outputConfiguration moved movedMember
    let offset := eventOffset direction (eventCollision configuration source direction)
    ∃ degreeSlot : Fin p.K,
      RowEventActiveComputedSpec p configuration source member offset degreeSlot
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output := by
  dsimp only
  let outputConfiguration := eventOutput configuration source direction
  let moved := moveSite source direction
  have movedMember : moved ∈ outputConfiguration.1 := by
    exact moveSite_mem_updateConfiguration configuration (source, direction) member
  let slot := slotOfMember outputConfiguration moved movedMember
  let collision := eventCollision configuration source direction
  let offset := eventOffset direction collision
  have slotActive : slot.val < outputConfiguration.1.card :=
    slotOfMember_lt_configurationCard outputConfiguration moved movedMember
  have movedAt : outputConfiguration.siteAt ⟨slot.val, slotActive⟩ = moved :=
    configuration_siteAt_slotOfMember outputConfiguration moved movedMember
      slotActive
  have sourceRecovered : moveSiteBackward
      (outputConfiguration.siteAt ⟨slot.val, slotActive⟩)
        (rowEventDirection offset) = source := by
    rw [movedAt]
    simp [moved, offset, collision]
  have sourceAbsentOutput : source ∉ outputConfiguration.1 := by
    exact source_not_mem_updateConfiguration configuration (source, direction)
      member
  have collisionRoom : offset.val % 2 = 1 →
      outputConfiguration.1.card < p.K := by
    intro collisionOffset
    by_cases collisionProperty : moved ∈ configuration.1.erase source
    · have cardDrop := updateConfiguration_card_add_one_of_collision
        configuration (source, direction) member collisionProperty
      change outputConfiguration.1.card + 1 = configuration.1.card at cardDrop
      omega
    · have collisionFalse : collision = false := by
        simp [collision, eventCollision, moved, collisionProperty]
      change (eventOffset direction collision).val % 2 = 1 at collisionOffset
      rw [collisionFalse] at collisionOffset
      exfalso
      cases direction <;> simp [eventOffset] at collisionOffset
  have selectorEq :
      rowSelectorForEvent configuration source member direction =
        selectorOfSlotOffset slot offset := by
    unfold rowSelectorForEvent
    change selectorOfSlotOffset
        (slotOfMember outputConfiguration moved _) offset =
      selectorOfSlotOffset slot offset
    congr 1
  have prefixSpecification : RowOraclePersistentConditionsSpec p outputConfiguration
      (selectorOfSlotOffset slot offset) input := by
    rw [← selectorEq]
    exact specification
  have prefixSourceAbsent : moveSiteBackward
      (outputConfiguration.siteAt ⟨slot.val, slotActive⟩)
        (rowEventDirection offset) ∉ outputConfiguration.1 := by
    simpa [sourceRecovered] using sourceAbsentOutput
  have activePrefix :=
    rowEventActivePrefix_correct outputConfiguration slot offset
      slotActive input prefixSpecification prefixSourceAbsent collisionRoom
  have outputCardPositive : 0 < outputConfiguration.1.card :=
    outputConfiguration.2.1
  let degreeSlot : Fin p.K :=
    ⟨outputConfiguration.1.card - 1, by omega⟩
  have degreeBoundary : degreeSlot.val + 1 = outputConfiguration.1.card := by
    simp [degreeSlot]
    omega
  have degreeOneHot : ∀ current : Fin p.K,
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
        (oracleDegreeWireAt p current) = decide (current = degreeSlot) := by
    intro current
    rw [activePrefix.degree_oneHot current]
    congr 1
    apply propext
    constructor
    · intro equal
      apply Fin.ext
      simp [degreeSlot]
      omega
    · intro equal
      have values := congrArg Fin.val equal
      simp [degreeSlot] at values
      omega
  have candidateValues : qCandidateValue p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output =
        configurationCandidateValue p configuration := by
    by_cases collisionProperty : moved ∈ configuration.1.erase source
    · have collisionTrue : collision = true := by
        simp [collision, eventCollision, moved, collisionProperty]
      have outputBelow : outputConfiguration.1.card < p.K :=
        collisionRoom (by
          cases direction <;> simp [offset, collisionTrue, eventOffset])
      let activeSlot : Fin (p.K - 1) :=
        ⟨outputConfiguration.1.card - 1, by omega⟩
      have slotAtBoundary : activeSlot.val + 1 =
          outputConfiguration.1.card := by
        simp [activeSlot]
        omega
      apply rowEventPredecessorCandidateUpdateAndSortExecutionTrace_collision_candidateValues configuration source
        member direction collisionProperty slot offset
          (by cases direction <;> simp [offset, collisionTrue, eventOffset])
          activeSlot (by simpa [outputConfiguration] using slotAtBoundary) input
      · simpa [outputConfiguration, sourceRecovered] using
          activePrefix.candidates_membership
      · exact activePrefix.candidates_values
      · exact activePrefix.branch_true
      · rw [activePrefix.degree_oneHot]
        simp [rowEventCollisionDegreeIndex, activeSlot]
        omega
      · intro other different
        rw [activePrefix.degree_oneHot]
        simp [rowEventCollisionDegreeIndex]
        omega
      · exact activePrefix.after_branch_clean
    · have collisionFalse : collision = false := by
        simp [collision, eventCollision, moved, collisionProperty]
      apply rowEventPredecessorCandidateUpdateAndSortExecutionTrace_replacement_candidateValues configuration
        source member direction collisionProperty slot offset
          (by cases direction <;> simp [offset, collisionFalse, eventOffset])
          slotActive (by simpa [outputConfiguration] using movedAt) input
      · simpa [outputConfiguration, sourceRecovered] using
          activePrefix.candidates_membership
      · exact activePrefix.candidates_values
      · exact activePrefix.branch_true
      · exact activePrefix.after_branch_clean
  have outputDegree : Int.ofNat (degreeSlot.val + 1) +
      rowEventDegreeChange offset = Int.ofNat configuration.1.card := by
    by_cases collisionProperty : moved ∈ configuration.1.erase source
    · have collisionTrue : collision = true := by
        simp [collision, eventCollision, moved, collisionProperty]
      have cardDrop := updateConfiguration_card_add_one_of_collision
        configuration (source, direction) member collisionProperty
      change outputConfiguration.1.card + 1 = configuration.1.card at cardDrop
      cases direction <;>
        simp [rowEventDegreeChange, offset, collisionTrue, eventOffset,
          degreeBoundary] <;> omega
    · have collisionFalse : collision = false := by
        simp [collision, eventCollision, moved, collisionProperty]
      have cardSame := updateConfiguration_card_of_noCollision
        configuration (source, direction) member collisionProperty
      change outputConfiguration.1.card = configuration.1.card at cardSame
      cases direction <;>
        simp [rowEventDegreeChange, offset, collisionFalse, eventOffset,
          degreeBoundary] <;> omega
  refine ⟨degreeSlot, RowEventActiveComputedSpec.of_afterBranch outputDegree
    activePrefix.after_branch_clean activePrefix.branch_true degreeOneHot candidateValues ?_⟩
  simpa [sourceRecovered] using activePrefix.moved_word

/--
branch計算直後がtracked cleanかつbranch=falseなら、suffixのclean・branch保存から
actual row event C-U-U全体が厳密な恒等作用になる。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch)
    (branchFalse : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleBranchWire p) = false) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  apply applyRowEventReferenceAndRestoreWorkCircuit_inactive_canonical p slot offset input
  · exact rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_clean_of_afterBranch p slot offset input
      clean
  · exact (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_branch_of_afterBranch p slot offset input
      clean).trans branchFalse

/-- 容量内の自然数では固定幅little-endian bit列の一致と自然数の一致が同値である。 -/
theorem constantBits_eq_constantBits_iff_of_lt
    {width left right : Nat} (leftLt : left < 2 ^ width)
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
persistent selectorと異なるslot/offsetのactual row event分岐は、内部computeを実行しても
branch flagが偽のため、compute--use--uncompute全体で厳密な恒等作用になる。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_selector_ne
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOraclePersistentConditionsSpec p configuration selector input)
    (different : selector ≠ selectorOfSlotOffset slot offset) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorConstantDifferent : selector.val ≠ 6 * slot.val + offset.val := by
    intro equal
    apply different
    apply Fin.ext
    simpa [selectorOfSlotOffset] using equal
  have selectorMatches : rowEventSelectorMatches p slot offset input = false := by
    unfold rowEventSelectorMatches diagonalSelectorMatches
    rw [specification.selector_bits]
    apply decide_eq_false
    intro bitsEqual
    apply selectorConstantDifferent
    exact (constantBits_eq_constantBits_iff_of_lt
      (qSelector_lt_capacity p selector)
      (qSelector_lt_capacity p (selectorOfSlotOffset slot offset))).mp
        (by simpa [selectorOfSlotOffset, rowSelectorWires] using bitsEqual)
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input
      specification.event_clean
  have movedClean : EventSortCleanInput p states.afterMoveBackward := by
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.moved_eq]
      exact EventSortCleanInput.of_rowEventMovedCopy p slot _ selectorClean
    rw [states.moveBackward_eq]
    exact EventSortCleanInput.of_rowEventMoveBackward p offset _ copiedClean
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    rw [states.membership_eq]
    exact EventSortCleanInput.of_rowEventMembership p slot _ movedClean
  have selectedAfterSelector : states.afterSelector (oracleSelectedWire p) =
      false := by
    rw [states.selector_eq, runBasis_rowEventSelectorCompute p slot offset input
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
    have selectedAfterMove : states.afterMoveBackward (oracleSelectedWire p) =
        false := by
      rw [states.moveBackward_eq, states.moved_eq]
      exact (runBasis_rowEventMovedComputation_outside_movedSlice p slot offset
        states.afterSelector selectorClean _ selectedOutside).trans
          selectedAfterSelector
    have selectedValues := rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMembership_earlierSlice p
      slot offset input specification.event_clean
        (OracleWorkLayout.canonical p).selected (by
          simp [OracleWorkLayout.canonical]
          omega)
    exact (readWires_eq_at_of_eq _ _ _ selectedValues (by
      simp [oracleSelectedWire, oracleSingletonWire,
        RegisterSlice.wireList])).trans selectedAfterMove
  have branchZeroAfterMembership : states.afterMembership
      (oracleBranchWire p) = false := by
    have afterMoveValues :=
      rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMoveBackward_laterSlice p slot offset input
        specification.event_clean (OracleWorkLayout.canonical p).branch (by
          simp [OracleWorkLayout.canonical]
          omega)
    have afterMoveZero : states.afterMoveBackward (oracleBranchWire p) = false :=
      (readWires_eq_at_of_eq _ _ _ afterMoveValues (by
        simp [oracleBranchWire, oracleSingletonWire,
          RegisterSlice.wireList])).trans specification.branch_zero
    rw [states.membership_eq]
    exact (runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other p (systemWires p)
      (systemWires_membershipInputLayout p) slot false states.afterMoveBackward
      {
        equalWork_zero := movedClean.moved_selector.compare_zero
        scratch_zero := movedClean.moved_selector.scratch_zero }
      (oracleBranchWire p)
      (MembershipOutputsSeparated.of_laterSlice p
        (OracleWorkLayout.canonical p).branch (by
          simp [OracleWorkLayout.canonical]) (oracleBranchWire p) (by
            simp [oracleBranchWire, oracleSingletonWire,
              RegisterSlice.wireList]))).trans afterMoveZero
  have branchFalse : states.afterBranch (oracleBranchWire p) = false := by
    rw [states.branch_eq]
    rw [runBasis_rowEventBranchCompute_branch_canonical p slot offset
      states.afterMembership membershipClean.moved_selector.scratch_zero
      branchZeroAfterMembership]
    simp [rowEventBranchControls, allWiresTrue, readWires,
      selectedAfterMembership]
  apply applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_afterBranch p slot offset input
  · exact rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input
      specification.event_clean
  · exact branchFalse

/--
row event broad support上で入力仕様を満たす状態と一致する状態も、同じconfigurationと
selectorのpersistent入力仕様を満たす。外部accumulatorのXOR後状態へ仕様を移すために使う。
-/
theorem RowOraclePersistentConditionsSpec.of_broadAgreement
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOraclePersistentConditionsSpec p configuration selector input)
    (agreement : BasisAgreeOn (rowEventBroadSupport p) output input) :
    RowOraclePersistentConditionsSpec p configuration selector output := by
  have selectorAgree : readWires (rowSelectorWires p) output =
      readWires (rowSelectorWires p) input := by
    apply List.map_congr_left
    intro wire member
    exact agreement wire (by simp [rowEventBroadSupport, member])
  have systemAgree : readWires (systemWires p) output =
      readWires (systemWires p) input := by
    apply List.map_congr_left
    intro wire member
    exact agreement wire (by simp [rowEventBroadSupport, member])
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
    system_bits := systemAgree.trans specification.system_bits
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
      readWires (registerWordAt p (systemWires p) slot) output =
          readWires (registerWordAt p (systemWires p) slot) input := by
        apply List.map_congr_left
        intro wire member
        apply agreement wire
        have systemMember : wire ∈ systemWires p :=
          List.mem_of_mem_drop (List.mem_of_mem_take member)
        simp [rowEventBroadSupport, systemMember]
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
    exact specification.moved_zero wire member
    exact oracleSliceWire_mem_oracleWork p
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

/-- row event persistent仕様から、同じslotの対角分岐が要求するclean入力仕様を得る。 -/
theorem RowOraclePersistentConditionsSpec.diagonalClean
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOraclePersistentConditionsSpec p configuration selector input)
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
persistent selectorと異なる任意selectorのrow分岐は、対角・eventのどちらでも厳密な恒等作用である。
-/
theorem dispatchRowSelectorToDiagonalOrEventCircuit_inactive_of_selector_ne
    {p : QParameters} (configuration : QConfiguration p)
    (active branch : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOraclePersistentConditionsSpec p configuration active input)
    (different : branch ≠ active) :
    (dispatchRowSelectorToDiagonalOrEventCircuit p branch).runBasis reversibleGatePermutation input = input := by
  let slot := selectorSlot branch
  let offset := selectorOffset branch
  have activeDifferent : active ≠ selectorOfSlotOffset slot offset := by
    simpa [slot, offset] using Ne.symm different
  unfold dispatchRowSelectorToDiagonalOrEventCircuit
  by_cases diagonal : offset.val < 2
  · rw [dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal p slot offset diagonal]
    let copy : Fin 2 := ⟨offset.val, diagonal⟩
    change (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input
    apply rowDiagonalResultComputeUseUncomputeCircuit_padding_identity p slot copy true
      (decide (slot.val < configuration.1.card)) input
      (specification.diagonalClean slot)
    unfold diagonalSelectorMatches
    rw [specification.selector_bits]
    apply decide_eq_false
    intro bitsEqual
    apply activeDifferent
    apply Fin.ext
    have valueEqual := (constantBits_eq_constantBits_iff_of_lt
      (qSelector_lt_capacity p active)
      (qSelector_lt_capacity p (selectorOfSlotOffset slot offset))).mp
        (by simpa [rowSelectorWires, copy, selectorOfSlotOffset] using bitsEqual)
    simpa [selectorOfSlotOffset] using valueEqual
  · rw [dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset diagonal]
    exact applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_selector_ne configuration active slot
      offset input specification activeDifferent

/--
selector・moved・membershipより前のpersistent sliceは、row event membership後も入力値を
厳密に保持する。
-/
theorem RowOraclePersistentConditionsSpec.afterMembership_earlierValue
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOraclePersistentConditionsSpec p configuration selector input)
    (slot : Fin p.K) (offset : Fin 6)
    {width : Nat} (earlier : RegisterSlice p.oracleWorkWidth width)
    (beforeSelected : earlier.start + width ≤
      (OracleWorkLayout.canonical p).selected.start)
    (beforeMoved : earlier.start + width ≤
      (OracleWorkLayout.canonical p).moved.start)
    (beforeEqual : earlier.start + width ≤
      (OracleWorkLayout.canonical p).membershipEqual.start)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ ((QLayout.oracleSlice earlier).wireList :
      List (Wire p.ancillaWidth p.systemWidth))) :
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMembership wire =
      input wire := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input
      specification.event_clean
  have selectorDifferent : wire ≠ oracleSelectedWire p := by
    have selectedMember : oracleSelectedWire p ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).selected).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
    exact oracleSliceMembers_ne_of_end_le_start p earlier
      (OracleWorkLayout.canonical p).selected beforeSelected member selectedMember
  have movedOutside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
    intro movedMember
    have disjoint :
        ((QLayout.oracleSlice earlier).wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).moved).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      apply RegisterSlice.wireList_disjoint_of_end_le_start
      simp [QLayout.oracleSlice, RegisterSlice.compose]
      omega
    exact (List.disjoint_left.mp disjoint) member movedMember
  calc
    states.afterMembership wire = states.afterMoveBackward wire := by
      exact readWires_eq_at_of_eq _ _ _
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMembership_earlierSlice p slot offset input
          specification.event_clean earlier beforeEqual) member
    _ = states.afterSelector wire := by
      rw [states.moveBackward_eq, states.moved_eq]
      exact runBasis_rowEventMovedComputation_outside_movedSlice p slot offset
        states.afterSelector selectorClean wire movedOutside
    _ = input wire := by
      rw [states.selector_eq]
      exact runBasis_rowEventSelectorCompute_other p slot offset input
        specification.event_clean wire selectorDifferent

/--
canonical event selectorに対して`rowReference`がpredecessorを返さないなら、偽predecessor・
collision満杯・paddingの全場合でactual row event分岐は厳密な恒等作用になる。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_reference_none
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6) (eventRange : 2 ≤ offset.val)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOraclePersistentConditionsSpec p configuration
      (selectorOfSlotOffset slot offset) input)
    (referenceNone : rowReference configuration
      (selectorOfSlotOffset slot offset) = none) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorMatches : rowEventSelectorMatches p slot offset input = true := by
    simp [rowEventSelectorMatches, diagonalSelectorMatches,
      specification.selector_bits, selectorOfSlotOffset]
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input
      specification.event_clean
  have movedClean : EventSortCleanInput p states.afterMoveBackward := by
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.moved_eq]
      exact EventSortCleanInput.of_rowEventMovedCopy p slot _ selectorClean
    rw [states.moveBackward_eq]
    exact EventSortCleanInput.of_rowEventMoveBackward p offset _ copiedClean
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    rw [states.membership_eq]
    exact EventSortCleanInput.of_rowEventMembership p slot _ movedClean
  have selectedAfterSelector : states.afterSelector (oracleSelectedWire p) =
      true := by
    rw [states.selector_eq, runBasis_rowEventSelectorCompute p slot offset input
      specification.event_clean.moved_selector.scratch_zero, selectorMatches]
    simp [xBasisAction, specification.selected_zero]
  have selectedAfterMembership : states.afterMembership (oracleSelectedWire p) =
      true := by
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
    have selectedAfterMove : states.afterMoveBackward (oracleSelectedWire p) =
        true := by
      rw [states.moveBackward_eq, states.moved_eq]
      exact (runBasis_rowEventMovedComputation_outside_movedSlice p slot offset
        states.afterSelector selectorClean _ selectedOutside).trans
          selectedAfterSelector
    have selectedValues := rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMembership_earlierSlice p
      slot offset input specification.event_clean
        (OracleWorkLayout.canonical p).selected (by
          simp [OracleWorkLayout.canonical]
          omega)
    exact (readWires_eq_at_of_eq _ _ _ selectedValues (by
      simp [oracleSelectedWire, oracleSingletonWire,
        RegisterSlice.wireList])).trans selectedAfterMove
  have branchZeroAfterMembership : states.afterMembership
      (oracleBranchWire p) = false := by
    have afterMoveValues :=
      rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMoveBackward_laterSlice p slot offset input
        specification.event_clean (OracleWorkLayout.canonical p).branch (by
          simp [OracleWorkLayout.canonical]
          omega)
    have afterMoveZero : states.afterMoveBackward (oracleBranchWire p) = false :=
      (readWires_eq_at_of_eq _ _ _ afterMoveValues (by
        simp [oracleBranchWire, oracleSingletonWire,
          RegisterSlice.wireList])).trans specification.branch_zero
    rw [states.membership_eq]
    exact (runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other p (systemWires p)
      (systemWires_membershipInputLayout p) slot false states.afterMoveBackward
      {
        equalWork_zero := movedClean.moved_selector.compare_zero
        scratch_zero := movedClean.moved_selector.scratch_zero }
      (oracleBranchWire p)
      (MembershipOutputsSeparated.of_laterSlice p
        (OracleWorkLayout.canonical p).branch (by
          simp [OracleWorkLayout.canonical]) (oracleBranchWire p) (by
            simp [oracleBranchWire, oracleSingletonWire,
              RegisterSlice.wireList]))).trans afterMoveZero
  have legalAfterMembership : states.afterMembership (oracleLegalWire p) = true :=
    (specification.afterMembership_earlierValue slot offset
      (OracleWorkLayout.canonical p).legal
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (oracleLegalWire p) (by simp [oracleLegalWire, RegisterSlice.wireList])).trans
        specification.legal
  have presentAfterMembership : states.afterMembership
      (oraclePresentWireAt p slot) =
        decide (slot.val < configuration.1.card) :=
    (specification.afterMembership_earlierValue slot offset
      (OracleWorkLayout.canonical p).present
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (oraclePresentWireAt p slot) (by
        change (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).present).ancillaWire slot ∈ _
        simp [RegisterSlice.wireList])).trans (specification.present slot)
  have degreeAfterMembership : states.afterMembership
      (oracleDegreeConditionWire p) = decide (configuration.1.card < p.K) :=
    (specification.afterMembership_earlierValue slot offset
      (OracleWorkLayout.canonical p).degreeCondition
      (by simp [OracleWorkLayout.canonical])
      (by simp [OracleWorkLayout.canonical])
      (by simp [OracleWorkLayout.canonical]; omega)
      (oracleDegreeConditionWire p) (by
        simp [oracleDegreeConditionWire, oracleSingletonWire,
          RegisterSlice.wireList])).trans specification.degree_condition
  have branchFalse : states.afterBranch (oracleBranchWire p) = false := by
    rw [states.branch_eq]
    rw [runBasis_rowEventBranchCompute_branch_canonical p slot offset
      states.afterMembership membershipClean.moved_selector.scratch_zero
      branchZeroAfterMembership]
    by_cases active : slot.val < configuration.1.card
    · let arrival := configuration.siteAt ⟨slot.val, active⟩
      let source := moveSiteBackward arrival (rowEventDirection offset)
      have arrivalMember : arrival ∈ configuration.1 := by
        exact ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
      have slotEq : slot = slotOfMember configuration arrival arrivalMember := by
        exact physicalSlot_eq_slotOfMember_of_siteAt_eq configuration slot active
          arrival arrivalMember rfl
      have movedMembership :=
        specification.afterMoveBackward_membership slot offset active
      have flagsZero := specification.afterMoveBackward_membershipZero slot offset
      have absentAfterMembership : states.afterMembership (oracleAbsentWire p) =
          decide (source ∉ configuration.1) := by
        rw [states.membership_eq]
        exact runBasis_rowEventMembership_absent_configuration p configuration
          source slot states.afterMoveBackward
            (by simpa [source] using movedMembership)
            {
              equalWork_zero := movedClean.moved_selector.compare_zero
              scratch_zero := movedClean.moved_selector.scratch_zero }
            flagsZero
      have rejectCondition : ¬(source ∉ configuration.1 ∧
          (rowEventCollision offset = false ∨ configuration.1.card < p.K)) := by
        intro accepted
        have someValue := (rowReference_eventSelector_isSome_iff configuration
          arrival arrivalMember offset eventRange).2
            (by simpa [arrival, source] using accepted)
        have sameReference : rowReference configuration
            (selectorOfSlotOffset
              (slotOfMember configuration arrival arrivalMember) offset) = none := by
          rw [← slotEq]
          exact referenceNone
        rw [sameReference] at someValue
        simp at someValue
      by_cases collisionOffset : offset.val % 2 = 1
      · have collisionTrue : rowEventCollision offset = true := by
          simp [rowEventCollision, collisionOffset]
        have rejectCollision : ¬(source ∉ configuration.1 ∧
            configuration.1.card < p.K) := by
          simpa [collisionTrue] using rejectCondition
        by_cases sourceAbsent : source ∉ configuration.1
        · have degreeFull : ¬ configuration.1.card < p.K := by
            intro degreeRoom
            exact rejectCollision ⟨sourceAbsent, degreeRoom⟩
          simp [rowEventBranchControls, collisionOffset, allWiresTrue, readWires,
            legalAfterMembership, selectedAfterMembership,
            presentAfterMembership, active, absentAfterMembership,
            sourceAbsent, degreeAfterMembership, degreeFull]
        · simp [rowEventBranchControls, collisionOffset, allWiresTrue, readWires,
            legalAfterMembership, selectedAfterMembership,
            presentAfterMembership, active, absentAfterMembership, sourceAbsent]
      · have collisionFalse : rowEventCollision offset = false := by
          simp [rowEventCollision, collisionOffset]
        have sourcePresent : ¬source ∉ configuration.1 := by
          simpa [collisionFalse] using rejectCondition
        simp [rowEventBranchControls, collisionOffset, allWiresTrue, readWires,
          legalAfterMembership, selectedAfterMembership, presentAfterMembership,
          active, absentAfterMembership, sourcePresent]
    · simp [rowEventBranchControls, allWiresTrue, readWires,
        legalAfterMembership, selectedAfterMembership, presentAfterMembership,
        active]
  apply applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_afterBranch p slot offset input
  · exact rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input
      specification.event_clean
  · exact branchFalse

/--
合法な配置と canonical row selector に対して参照関数が値を返さないなら、選択された
対角または event 分岐そのものも基底状態上の恒等作用になる。
-/
theorem dispatchRowSelectorToDiagonalOrEventCircuit_inactive_of_reference_none
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOraclePersistentConditionsSpec p configuration selector input)
    (referenceNone : rowReference configuration selector = none) :
    (dispatchRowSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation input =
      input := by
  let slot := selectorSlot selector
  let offset := selectorOffset selector
  unfold dispatchRowSelectorToDiagonalOrEventCircuit
  by_cases diagonal : offset.val < 2
  · rw [dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal p slot offset diagonal]
    let copy : Fin 2 := ⟨offset.val, diagonal⟩
    change (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input = input
    have padding : ¬ slot.val < configuration.1.card := by
      intro active
      let arrival : {site : QSite p // site ∈ configuration.1} :=
        (configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩
      have selected : configurationSlot? configuration slot = some arrival := by
        unfold configurationSlot?
        rw [dif_pos active]
      have referenceSome : rowReference configuration selector =
          some ⟨configuration, selector⟩ := by
        unfold rowReference
        have selectedAtSelector : configurationSlot? configuration
            (selectorSlot selector) = some arrival := by
          simpa [slot] using selected
        rw [selectedAtSelector]
        have diagonalAtSelector : (selectorOffset selector).val < 2 := by
          simpa [offset] using diagonal
        simp [diagonalAtSelector]
      rw [referenceNone] at referenceSome
      contradiction
    apply rowDiagonalResultComputeUseUncomputeCircuit_absent_identity p slot copy true input
    simpa [padding] using specification.diagonalClean slot
  · rw [dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset diagonal]
    have eventRange : 2 ≤ offset.val := by omega
    have canonicalSpecification : RowOraclePersistentConditionsSpec p configuration
        (selectorOfSlotOffset slot offset) input := by
      simpa [slot, offset] using specification
    have canonicalNone : rowReference configuration
        (selectorOfSlotOffset slot offset) = none := by
      simpa [slot, offset] using referenceNone
    exact applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_reference_none configuration slot
      offset eventRange input canonicalSpecification canonicalNone

/--
active row event 分岐の desired XOR 出力と全内部 wire 復元をまとめた最終基底仕様。
-/
structure RowEventActiveBranchResult (p : QParameters)
    (configuration : QConfiguration p) (source : QSite p)
    (member : source ∈ configuration.1) (offset : Fin 6)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- column-key は predecessor の delimiter 符号を既存 accumulator へ XOR する。 -/
  column_key : readWires (columnKeyWires p) output =
    List.zipWith
      (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
      (registerBitList (delimiterEncoding configuration))
      (readWires (columnKeyWires p) input)
  /-- column-selector は predecessor source の selector 定数を既存 accumulator へ XOR する。 -/
  column_selector : readWires (columnSelectorWires p) output =
    controlledXorConstantBits true
      (6 * (slotOfMember configuration source member).val + offset.val) 0
      (readWires (columnSelectorWires p) input)
  /-- key-signal は active 分岐で一回反転する。 -/
  key_signal : output (keySignalWire p) = !(input (keySignalWire p))
  /-- row-selector・system・oracle-work の全 broad support は入力へ戻る。 -/
  support_restored : BasisAgreeOn (rowEventBroadSupport p) output input
  /-- 三外部出力以外の任意 wire も入力へ戻る。 -/
  outside_restored : ∀ wire,
    wire ∉ columnKeyWires p → wire ∉ columnSelectorWires p →
      wire ≠ keySignalWire p → output wire = input wire

/-- rowReference が返した predecessor 配置と column selector を直接使う外部 XOR 仕様。 -/
structure RowReferenceBranchResult (p : QParameters)
    (predecessor : QConfiguration p) (columnSelector : QSelector p)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- column-key は predecessor delimiter 符号を accumulator へ XOR する。 -/
  column_key : readWires (columnKeyWires p) output =
    List.zipWith
      (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
      (registerBitList (delimiterEncoding predecessor))
      (readWires (columnKeyWires p) input)
  /-- column-selector は rowReference が返した selector を accumulator へ XOR する。 -/
  column_selector : readWires (columnSelectorWires p) output =
    controlledXorConstantBits true columnSelector.val 0
      (readWires (columnSelectorWires p) input)
  /-- key-signal は受理時に一回反転する。 -/
  key_signal : output (keySignalWire p) = !(input (keySignalWire p))
  /-- row-selector・system・oracle-work は入力へ戻る。 -/
  support_restored : BasisAgreeOn (rowEventBroadSupport p) output input
  /-- 三外部出力以外の任意 wire も入力へ戻る。 -/
  outside_restored : ∀ wire,
    wire ∉ columnKeyWires p → wire ∉ columnSelectorWires p →
      wire ≠ keySignalWire p → output wire = input wire

/--
source の canonical slot と offset が rowReference の column selector を与えるなら、
active event 仕様を rowReference 直結仕様へ変換できる。
-/
theorem RowEventActiveBranchResult.toRowReference
    {p : QParameters} {configuration : QConfiguration p} {source : QSite p}
    {member : source ∈ configuration.1} {offset : Fin 6}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (result : RowEventActiveBranchResult p configuration source member offset
      input output)
    (columnSelector : QSelector p)
    (selectorEq : columnSelector =
      selectorOfSlotOffset (slotOfMember configuration source member) offset) :
    RowReferenceBranchResult p configuration columnSelector input output := by
  subst columnSelector
  refine {
    column_key := result.column_key
    column_selector := ?_
    key_signal := result.key_signal
    support_restored := result.support_restored
    outside_restored := result.outside_restored }
  simpa [selectorOfSlotOffset] using result.column_selector

/--
canonical row event compute の局所性を内部適用した、分岐全体の broad-support 復元等式。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_eq_restoreBroadSupport_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false)
    (pairZero : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (if offset.val % 2 = 1 then 1 else 0)
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input =
      restoreSupport (rowEventBroadSupport p) input
        ((xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
          (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output) := by
  apply applyRowEventReferenceAndRestoreWorkCircuit_eq_restoreBroadSupport p slot offset input
  · rw [← rowEventPredecessorCandidateUpdateAndSortSupport_eq_broadSupport p]
    exact computeRowEventPredecessorCandidateUpdateAndSortCircuit_usesOnly p slot offset
  · exact scratchZero
  · exact pairZero
  · exact movedClean

/--
canonical row event compute の局所性を内部適用すると、actual 分岐の三外部出力は
純粋 writer 参照に一致し、row-selector・system・oracle-work はすべて入力へ戻る。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_reference_correct_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false)
    (pairZero : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (if offset.val % 2 = 1 then 1 else 0)
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)) :
    RowEventBranchReferenceResult p offset input
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      ((applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  apply applyRowEventReferenceAndRestoreWorkCircuit_reference_correct p slot offset input
  · rw [← rowEventPredecessorCandidateUpdateAndSortSupport_eq_broadSupport p]
    exact computeRowEventPredecessorCandidateUpdateAndSortCircuit_usesOnly p slot offset
  · exact scratchZero
  · exact pairZero
  · exact movedClean

/--
三つの外部出力 register・bit のいずれにも属さない任意 wire は、canonical row event
分岐の前後で入力値に厳密に戻る。内部 support とその外側の双方を一つの定理で覆う。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_outside_outputs_restored_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ work ∈ decoderAndScratchWires p,
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output work = false)
    (pairZero : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (if offset.val % 2 = 1 then 1 else 0)
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output))
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideKey : wire ∉ columnKeyWires p)
    (outsideSelector : wire ∉ columnSelectorWires p)
    (outsideSignal : wire ≠ keySignalWire p) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input wire = input wire := by
  let computed := (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
    (by simp [columnKeyWires]) (keySignalWire p)
    (if offset.val % 2 = 1 then 1 else 0) computed
  let used := (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation computed
  let output := (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
    reversibleGatePermutation input
  have computeUses : circuitUsesOnly (rowEventBroadSupport p)
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) := by
    rw [← rowEventPredecessorCandidateUpdateAndSortSupport_eq_broadSupport p]
    exact computeRowEventPredecessorCandidateUpdateAndSortCircuit_usesOnly p slot offset
  have outputEq : output = restoreSupport (rowEventBroadSupport p) input used := by
    dsimp [output, used, computed]
    exact applyRowEventReferenceAndRestoreWorkCircuit_eq_restoreBroadSupport p slot offset input
      computeUses scratchZero pairZero movedClean
  by_cases supportMember : wire ∈ rowEventBroadSupport p
  · change output wire = input wire
    rw [outputEq]
    exact restoreSupport_agrees_input (rowEventBroadSupport p) input used wire
      supportMember
  · have useOutside : used wire = sorted wire := by
      have useSpec := runBasis_xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_reference p offset computed
        scratchZero pairZero movedClean
      exact useSpec.2 wire outsideSelector
    have sortedOutside : sorted wire = computed wire := by
      exact xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_columnKey p
        (if offset.val % 2 = 1 then 1 else 0) computed wire outsideKey
        outsideSignal
    have computedOutside : computed wire = input wire := by
      dsimp [computed]
      rw [rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output]
      exact Circuit.runBasis_outside_of_usesOnly (rowEventBroadSupport p)
        (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) computeUses input wire supportMember
    change output wire = input wire
    rw [outputEq]
    exact (restoreSupport_outside (rowEventBroadSupport p) input used wire
      supportMember).trans (useOutside.trans (sortedOutside.trans computedOutside))

/--
canonical writer と moved-selector の純粋 XOR 式が得られれば、actual row event 分岐の
全外部出力と全 wire 復元を最終 active 仕様へ一括して持ち上げる。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_active_of_writer_references
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (configuration : QConfiguration p) (source : QSite p)
    (member : source ∈ configuration.1)
    (degreeSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (computedSpec : RowEventActiveComputedSpec p configuration source member offset
      degreeSlot (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)
    (writerKey :
      let computed := (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (rowEventDegreeChange offset) computed
      readWires (columnKeyWires p) sorted =
        List.zipWith
          (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
          (registerBitList (delimiterEncoding configuration))
          (readWires (columnKeyWires p) computed))
    (writerSignal :
      let computed := (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (rowEventDegreeChange offset) computed
      sorted (keySignalWire p) = !(computed (keySignalWire p)))
    (movedSelector :
      let computed := (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (rowEventDegreeChange offset) computed
      movedMemberPositionSelectorOutputXorReference p offset.val (columnSelectorWires p) sorted =
        controlledXorConstantBits true
          (6 * (slotOfMember configuration source member).val + offset.val) 0
          (readWires (columnSelectorWires p) sorted)) :
    RowEventActiveBranchResult p configuration source member offset input
      ((applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  let computed := (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
    (by simp [columnKeyWires]) (keySignalWire p)
    (rowEventDegreeChange offset) computed
  let output := (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
    reversibleGatePermutation input
  have computeUses : circuitUsesOnly (rowEventBroadSupport p)
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) := by
    rw [← rowEventPredecessorCandidateUpdateAndSortSupport_eq_broadSupport p]
    exact computeRowEventPredecessorCandidateUpdateAndSortCircuit_usesOnly p slot offset
  have referenceSpec : RowEventBranchReferenceResult p offset input computed output := by
    change RowEventBranchReferenceResult p offset input
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output _
    apply applyRowEventReferenceAndRestoreWorkCircuit_reference_correct_canonical p slot offset input
    · exact computedSpec.scratch_zero
    · exact computedSpec.pair_zero
    · simpa [rowEventDegreeChange] using computedSpec.moved_clean
  have computedKey : readWires (columnKeyWires p) computed =
      readWires (columnKeyWires p) input := by
    dsimp [computed]
    rw [rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output]
    exact readWires_runBasis_of_usesOnly_disjoint
      (rowEventBroadSupport p) (columnKeyWires p)
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) input computeUses
      (rowEventBroadSupport_disjoint_columnKey p)
  have computedSelector : readWires (columnSelectorWires p) computed =
      readWires (columnSelectorWires p) input := by
    dsimp [computed]
    rw [rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output]
    exact readWires_runBasis_of_usesOnly_disjoint
      (rowEventBroadSupport p) (columnSelectorWires p)
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) input computeUses
      (rowEventBroadSupport_disjoint_columnSelector p)
  have computedSignal : computed (keySignalWire p) = input (keySignalWire p) := by
    dsimp [computed]
    rw [rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output]
    exact Circuit.runBasis_outside_of_usesOnly (rowEventBroadSupport p)
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) computeUses input (keySignalWire p)
      (keySignalWire_not_mem_rowEventBroadSupport p)
  have sortedSelector : readWires (columnSelectorWires p) sorted =
      readWires (columnSelectorWires p) computed := by
    apply List.map_congr_left
    intro wire selectorMember
    apply xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_columnKey
    · exact (List.disjoint_left.mp
        (columnKeyWires_disjoint_columnSelectorWires p).symm) selectorMember
    · intro equal
      subst wire
      exact keySignalWire_not_mem_columnSelectorWires p selectorMember
  have writerKey' : readWires (columnKeyWires p) sorted =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (registerBitList (delimiterEncoding configuration))
        (readWires (columnKeyWires p) computed) := by
    simpa [sorted, computed] using writerKey
  have writerSignal' : sorted (keySignalWire p) =
      !(computed (keySignalWire p)) := by
    simpa [sorted, computed] using writerSignal
  have movedSelector' :
      movedMemberPositionSelectorOutputXorReference p offset.val (columnSelectorWires p) sorted =
        controlledXorConstantBits true
          (6 * (slotOfMember configuration source member).val + offset.val) 0
          (readWires (columnSelectorWires p) sorted) := by
    simpa [sorted, computed] using movedSelector
  change RowEventActiveBranchResult p configuration source member offset input output
  refine ⟨?_, ?_, ?_, referenceSpec.support_restored, ?_⟩
  · rw [referenceSpec.column_key]
    change readWires (columnKeyWires p) sorted = _
    rw [writerKey', computedKey]
  · rw [referenceSpec.column_selector]
    change movedMemberPositionSelectorOutputXorReference p offset.val
      (columnSelectorWires p) sorted = _
    rw [movedSelector', sortedSelector, computedSelector]
  · rw [referenceSpec.key_signal]
    change sorted (keySignalWire p) = _
    rw [writerSignal', computedSignal]
  · intro wire outsideKey outsideSelector outsideSignal
    exact applyRowEventReferenceAndRestoreWorkCircuit_outside_outputs_restored_canonical p slot offset
      input computedSpec.scratch_zero computedSpec.pair_zero
      (by simpa [rowEventDegreeChange] using computedSpec.moved_clean)
      wire outsideKey outsideSelector outsideSignal

/--
candidate・degree・branch のcompute仕様から sorted writer のdelimiter XORと
key-signal反転を内部導出し、残る moved-selector の純粋式だけでactive分岐を閉じる。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_active_of_computedSpec
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (configuration : QConfiguration p) (source : QSite p)
    (member : source ∈ configuration.1)
    (degreeSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (computedSpec : RowEventActiveComputedSpec p configuration source member offset
      degreeSlot (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)
    (movedSelector :
      let computed := (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (rowEventDegreeChange offset) computed
      movedMemberPositionSelectorOutputXorReference p offset.val (columnSelectorWires p) sorted =
        controlledXorConstantBits true
          (6 * (slotOfMember configuration source member).val + offset.val) 0
          (readWires (columnSelectorWires p) sorted)) :
    RowEventActiveBranchResult p configuration source member offset input
      ((applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  let computed := (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
  have writerEq :
      SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
          (by simp [columnKeyWires]) (keySignalWire p)
          (rowEventDegreeChange offset) computed =
        writeSortedUseReference p
          (canonicalSortedOutputWires p .columnKey)
          (canonicalSortedOutputWires_length p .columnKey)
          (canonicalSortedOutputActive p .columnKey)
          configuration.1.card configuration.2.2 true computed := by
    simpa [canonicalSortedOutputWires, canonicalSortedOutputActive] using
      xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_eq_configuration_use p .columnKey configuration
        degreeSlot (rowEventDegreeChange offset) computed
          computedSpec.output_degree computedSpec.branch_true
          computedSpec.degree_oneHot
  apply applyRowEventReferenceAndRestoreWorkCircuit_active_of_writer_references p slot offset
    configuration source member degreeSlot input computedSpec
  · dsimp only
    rw [writerEq]
    simpa [canonicalSortedOutputWires] using
      writeSortedUseReference_configuration_bits_canonical p .columnKey
        configuration computed computedSpec.candidate_values
  · dsimp only
    rw [writerEq]
    simpa [canonicalSortedOutputActive] using
      writeSortedUseReference_configuration_active_canonical p .columnKey
        configuration computed
  · exact movedSelector

/--
active compute仕様だけからmoved-selectorの唯一slot作用も内部導出し、actual row event
分岐のdelimiter・selector・signal XORと全work復元を仮定なしで得る。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_active
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (configuration : QConfiguration p) (source : QSite p)
    (member : source ∈ configuration.1)
    (degreeSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (computedSpec : RowEventActiveComputedSpec p configuration source member offset
      degreeSlot (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output) :
    RowEventActiveBranchResult p configuration source member offset input
      ((applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  let computed := (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
    (by simp [columnKeyWires]) (keySignalWire p)
    (rowEventDegreeChange offset) computed
  apply applyRowEventReferenceAndRestoreWorkCircuit_active_of_computedSpec p slot offset configuration
    source member degreeSlot input computedSpec
  dsimp only
  apply xorMovedMemberPositionIntoSelectorOutputCircuitBitsReference_configuration p configuration source
    member offset.val (columnSelectorWires p) sorted
  · exact (xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_branch p
      (rowEventDegreeChange offset) computed).trans computedSpec.branch_true
  · exact (xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_qCandidateValue p
      (rowEventDegreeChange offset) computed).trans
        computedSpec.candidate_values
  · exact (xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_movedWires p
      (rowEventDegreeChange offset) computed).trans computedSpec.moved_word

/--
物理eventの出力配置とcanonical row selectorを保持するpersistent状態では、対応する
actual row分岐がpredecessor delimiter・column selector・signalを厳密にXORする。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_physicalEvent
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOraclePersistentConditionsSpec p
      (eventOutput configuration source direction)
      (rowSelectorForEvent configuration source member direction) input) :
    let outputConfiguration := eventOutput configuration source direction
    let moved := moveSite source direction
    let movedMember : moved ∈ outputConfiguration.1 :=
      moveSite_mem_updateConfiguration configuration (source, direction) member
    let slot := slotOfMember outputConfiguration moved movedMember
    let offset := eventOffset direction (eventCollision configuration source direction)
    RowEventActiveBranchResult p configuration source member offset input
      ((applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  dsimp only
  obtain ⟨degreeSlot, computedSpec⟩ :=
    rowEventActiveComputedSpec_physicalEvent configuration source member direction
      input specification
  exact applyRowEventReferenceAndRestoreWorkCircuit_active p _ _ configuration source member degreeSlot
    input computedSpec

/-- row oracle 分岐列は、selector 全域の型安全な分岐関数を `finRange` 順に写した列である。 -/
theorem rowOracleBranchList_eq_finRange_map (p : QParameters) :
    rowOracleBranchList p =
      (List.finRange p.selectorCount).map (dispatchRowSelectorToDiagonalOrEventCircuit p) := by
  rw [rowOracleBranchList_eq_ofFn]
  apply List.ext_get
  · simp
  · intro index leftBound rightBound
    simp

/--
唯一の active selector 分岐だけが出力を作り、他の全分岐が active 前後の状態を固定するなら、
`6K` 本の row 分岐列全体の作用はその active 分岐の作用へ厳密に簡約される。
-/
theorem runBasis_rowOracleBranchSequence_eq_active
    (p : QParameters) (active : QSelector p)
    (input output : JointBasis p.ancillaWidth p.systemWidth)
    (inactiveInput : ∀ selector : QSelector p, selector ≠ active →
      (dispatchRowSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation input = input)
    (activeResult : (dispatchRowSelectorToDiagonalOrEventCircuit p active).runBasis
      reversibleGatePermutation input = output)
    (inactiveOutput : ∀ selector : QSelector p, selector ≠ active →
      (dispatchRowSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation output = output) :
    (Circuit.sequence (rowOracleBranchList p)).runBasis
        reversibleGatePermutation input = output := by
  rw [rowOracleBranchList_eq_finRange_map]
  apply runBasis_sequence_map_eq_of_unique_active reversibleGatePermutation
    (List.finRange p.selectorCount) (dispatchRowSelectorToDiagonalOrEventCircuit p) active input output
  · exact List.nodup_finRange p.selectorCount
  · exact List.mem_finRange active
  · intro selector _ different
    exact inactiveInput selector different
  · exact activeResult
  · intro selector _ different
    exact inactiveOutput selector different

/-- 全 selector 分岐が同じ状態を固定するなら、row 分岐列全体もその状態を固定する。 -/
theorem runBasis_rowOracleBranchSequence_eq_input
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (eachIdentity : ∀ selector : QSelector p,
      (dispatchRowSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation input = input) :
    (Circuit.sequence (rowOracleBranchList p)).runBasis
        reversibleGatePermutation input = input := by
  apply Circuit.runBasis_sequence_eq_input_of_each
  intro circuit member
  rw [rowOracleBranchList_eq_finRange_map] at member
  obtain ⟨selector, _, rfl⟩ := List.mem_map.mp member
  exact eachIdentity selector

/-- row oracle の最外側 persistent compute が参照する canonical support。 -/
def rowOraclePersistentSupport (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  systemWires p ++ diagonalOracleWorkWires p

/-- row oracle persistent support は row event broad support に含まれる。 -/
theorem rowOraclePersistentSupport_subset_rowEventBroadSupport (p : QParameters) :
    ∀ wire ∈ rowOraclePersistentSupport p, wire ∈ rowEventBroadSupport p := by
  intro wire member
  rcases List.mem_append.mp member with systemMember | workMember
  · exact List.mem_append_left _ (List.mem_append_right _ systemMember)
  · exact List.mem_append_right _ workMember

/-- row oracle persistent support は column-key 出力 register と交わらない。 -/
theorem rowOraclePersistentSupport_disjoint_columnKey (p : QParameters) :
    (rowOraclePersistentSupport p).Disjoint (columnKeyWires p) := by
  rw [List.disjoint_left]
  intro wire supportMember keyMember
  exact (List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnKey p))
    (rowOraclePersistentSupport_subset_rowEventBroadSupport p wire supportMember)
    keyMember

/-- row oracle persistent support は column-selector 出力 register と交わらない。 -/
theorem rowOraclePersistentSupport_disjoint_columnSelector (p : QParameters) :
    (rowOraclePersistentSupport p).Disjoint (columnSelectorWires p) := by
  rw [List.disjoint_left]
  intro wire supportMember selectorMember
  exact (List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnSelector p))
    (rowOraclePersistentSupport_subset_rowEventBroadSupport p wire supportMember)
    selectorMember

/-- key-signal 出力 bit は row oracle persistent support に含まれない。 -/
theorem keySignalWire_not_mem_rowOraclePersistentSupport (p : QParameters) :
    keySignalWire p ∉ rowOraclePersistentSupport p := by
  intro member
  exact keySignalWire_not_mem_rowEventBroadSupport p
    (rowOraclePersistentSupport_subset_rowEventBroadSupport p _ member)

/--
全 row 分岐列が persistent support を保存するなら、最外側の
persistent compute--branches--uncompute はその support を入力へ厳密に復元する。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_eq_restorePersistentSupport
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchesPreserve : BasisAgreeOn (rowOraclePersistentSupport p)
      ((Circuit.sequence (rowOracleBranchList p)).runBasis
        reversibleGatePermutation
        ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
          reversibleGatePermutation input))
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input)) :
    (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input =
      restoreSupport (rowOraclePersistentSupport p) input
        ((Circuit.sequence (rowOracleBranchList p)).runBasis
          reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
            reversibleGatePermutation input)) := by
  rw [applyRowOracleReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
  exact Circuit.computeUseUncompute_local_clean
    (rowOraclePersistentSupport p)
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true)
    (Circuit.sequence (rowOracleBranchList p)) input
    (by simpa [rowOraclePersistentSupport] using
      rowOraclePersistentCompute_usesOnly p)
    branchesPreserve

/--
分岐列の厳密な出力等式と、その出力による persistent support 保存を与えると、
row oracle 全体の最終基底を一段の `restoreSupport` 式へ簡約できる。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_eq_restore_of_branchResult
    (p : QParameters) (input branchOutput :
      JointBasis p.ancillaWidth p.systemWidth)
    (sequenceResult :
      (Circuit.sequence (rowOracleBranchList p)).runBasis
          reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
            reversibleGatePermutation input) = branchOutput)
    (persistentPreserved : BasisAgreeOn (rowOraclePersistentSupport p)
      branchOutput
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input)) :
    (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input =
      restoreSupport (rowOraclePersistentSupport p) input branchOutput := by
  have branchesPreserve : BasisAgreeOn (rowOraclePersistentSupport p)
      ((Circuit.sequence (rowOracleBranchList p)).runBasis
        reversibleGatePermutation
        ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
          reversibleGatePermutation input))
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input) := by
    rw [sequenceResult]
    exact persistentPreserved
  rw [applyRowOracleReferenceAndRestoreWorkCircuit_eq_restorePersistentSupport p input
    branchesPreserve, sequenceResult]

/--
分岐列が rowReference 仕様を満たす一状態を返すなら、最外側 persistent uncompute 後も
同じ XOR 出力を保持し、全 broad support とその他の全 wire を入力へ厳密に戻す。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_correct_of_branchResult
    (p : QParameters) (predecessor : QConfiguration p)
    (columnSelector : QSelector p)
    (input branchOutput : JointBasis p.ancillaWidth p.systemWidth)
    (sequenceResult :
      (Circuit.sequence (rowOracleBranchList p)).runBasis
          reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
            reversibleGatePermutation input) = branchOutput)
    (branchResult : RowReferenceBranchResult p predecessor columnSelector
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input) branchOutput) :
    RowReferenceBranchResult p predecessor columnSelector input
      ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input) := by
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
    reversibleGatePermutation input
  let output := (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
    reversibleGatePermutation input
  have persistentUses : circuitUsesOnly (rowOraclePersistentSupport p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true) := by
    simpa [rowOraclePersistentSupport] using rowOraclePersistentCompute_usesOnly p
  have persistentKey : readWires (columnKeyWires p) persistent =
      readWires (columnKeyWires p) input := by
    exact readWires_runBasis_of_usesOnly_disjoint
      (rowOraclePersistentSupport p) (columnKeyWires p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true) input persistentUses
      (rowOraclePersistentSupport_disjoint_columnKey p)
  have persistentSelector : readWires (columnSelectorWires p) persistent =
      readWires (columnSelectorWires p) input := by
    exact readWires_runBasis_of_usesOnly_disjoint
      (rowOraclePersistentSupport p) (columnSelectorWires p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true) input persistentUses
      (rowOraclePersistentSupport_disjoint_columnSelector p)
  have persistentSignal : persistent (keySignalWire p) =
      input (keySignalWire p) := by
    exact Circuit.runBasis_outside_of_usesOnly (rowOraclePersistentSupport p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true) persistentUses input
      (keySignalWire p) (keySignalWire_not_mem_rowOraclePersistentSupport p)
  have persistentPreserved : BasisAgreeOn (rowOraclePersistentSupport p)
      branchOutput persistent := by
    intro wire member
    exact branchResult.support_restored wire
      (rowOraclePersistentSupport_subset_rowEventBroadSupport p wire member)
  have outputEq : output =
      restoreSupport (rowOraclePersistentSupport p) input branchOutput := by
    dsimp [output, persistent] at sequenceResult ⊢
    exact applyRowOracleReferenceAndRestoreWorkCircuit_eq_restore_of_branchResult p input
      branchOutput sequenceResult persistentPreserved
  have keyFinal : readWires (columnKeyWires p) output =
      readWires (columnKeyWires p) branchOutput := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (rowOraclePersistentSupport p) input branchOutput
      wire (fun supportMember =>
        (List.disjoint_left.mp (rowOraclePersistentSupport_disjoint_columnKey p))
          supportMember member)
  have selectorFinal : readWires (columnSelectorWires p) output =
      readWires (columnSelectorWires p) branchOutput := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (rowOraclePersistentSupport p) input branchOutput
      wire (fun supportMember =>
        (List.disjoint_left.mp
          (rowOraclePersistentSupport_disjoint_columnSelector p))
            supportMember member)
  have signalFinal : output (keySignalWire p) =
      branchOutput (keySignalWire p) := by
    rw [outputEq]
    exact restoreSupport_outside (rowOraclePersistentSupport p) input branchOutput
      (keySignalWire p) (keySignalWire_not_mem_rowOraclePersistentSupport p)
  change RowReferenceBranchResult p predecessor columnSelector input output
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [keyFinal, branchResult.column_key, persistentKey]
  · rw [selectorFinal, branchResult.column_selector, persistentSelector]
  · rw [signalFinal, branchResult.key_signal]
    exact congrArg (fun bit => !bit) (by
      simpa [persistent] using persistentSignal)
  · intro wire broadMember
    by_cases persistentMember : wire ∈ rowOraclePersistentSupport p
    · rw [outputEq]
      exact restoreSupport_agrees_input (rowOraclePersistentSupport p) input
        branchOutput wire persistentMember
    · rw [outputEq, restoreSupport_outside (rowOraclePersistentSupport p) input
        branchOutput wire persistentMember]
      rw [branchResult.support_restored wire broadMember]
      exact Circuit.runBasis_outside_of_usesOnly (rowOraclePersistentSupport p)
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true) persistentUses input wire
        persistentMember
  · intro wire outsideKey outsideSelector outsideSignal
    by_cases persistentMember : wire ∈ rowOraclePersistentSupport p
    · rw [outputEq]
      exact restoreSupport_agrees_input (rowOraclePersistentSupport p) input
        branchOutput wire persistentMember
    · rw [outputEq, restoreSupport_outside (rowOraclePersistentSupport p) input
        branchOutput wire persistentMember]
      rw [branchResult.outside_restored wire outsideKey outsideSelector outsideSignal]
      exact Circuit.runBasis_outside_of_usesOnly (rowOraclePersistentSupport p)
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true) persistentUses input wire
        persistentMember

/--
唯一のactive selector分岐の前後で全不一致分岐が恒等なら、その一分岐の
`rowReference` 厳密仕様を row oracle 全体へ持ち上げられる。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_correct_of_unique_active
    (p : QParameters) (predecessor : QConfiguration p)
    (columnSelector active : QSelector p)
    (input branchOutput : JointBasis p.ancillaWidth p.systemWidth)
    (inactiveInput : ∀ selector : QSelector p, selector ≠ active →
      (dispatchRowSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
            reversibleGatePermutation input) =
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
          reversibleGatePermutation input)
    (activeResult : (dispatchRowSelectorToDiagonalOrEventCircuit p active).runBasis
        reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
            reversibleGatePermutation input) = branchOutput)
    (inactiveOutput : ∀ selector : QSelector p, selector ≠ active →
      (dispatchRowSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation
          branchOutput = branchOutput)
    (branchResult : RowReferenceBranchResult p predecessor columnSelector
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input) branchOutput) :
    RowReferenceBranchResult p predecessor columnSelector input
      ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input) := by
  have sequenceResult :
      (Circuit.sequence (rowOracleBranchList p)).runBasis
          reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
            reversibleGatePermutation input) = branchOutput := by
    exact runBasis_rowOracleBranchSequence_eq_active p active _ branchOutput
      inactiveInput activeResult inactiveOutput
  exact applyRowOracleReferenceAndRestoreWorkCircuit_correct_of_branchResult p predecessor
    columnSelector input branchOutput sequenceResult branchResult

/--
persistent compute 後の状態を全 `6K` 分岐が固定するなら、row oracle 全体は入力基底上の
厳密な恒等作用である。padding・illegal・偽 predecessor の拒否を共通に合成できる。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_eq_input_of_eachBranch
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (eachIdentity : ∀ selector : QSelector p,
      (dispatchRowSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
            reversibleGatePermutation input) =
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
          reversibleGatePermutation input) :
    (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input = input := by
  rw [applyRowOracleReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
  apply Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl)
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true)
    (Circuit.sequence (rowOracleBranchList p)) input input
  exact runBasis_rowOracleBranchSequence_eq_input p _ eachIdentity

/--
合法 delimiter・canonical row selector・clean oracle work を持つ入力で `rowReference` が
`none` を返すなら、全 `6K` 分岐と persistent compute--uncompute を含む row oracle
全体は基底状態を厳密に保存する。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_reference_none
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOracleInputSpec p configuration selector input)
    (referenceNone : rowReference configuration selector = none) :
    (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input =
      input := by
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
    reversibleGatePermutation input
  have persistentSpecification : RowOraclePersistentConditionsSpec p configuration
      selector persistent := by
    simpa [persistent] using specification.afterPersistent
  apply applyRowOracleReferenceAndRestoreWorkCircuit_eq_input_of_eachBranch p input
  intro branch
  by_cases active : branch = selector
  · subst branch
    exact dispatchRowSelectorToDiagonalOrEventCircuit_inactive_of_reference_none configuration selector
      persistent persistentSpecification referenceNone
  · exact dispatchRowSelectorToDiagonalOrEventCircuit_inactive_of_selector_ne configuration selector
      branch persistent persistentSpecification active

/--
物理eventで得られた出力配置とcanonical row selectorの合法基底では、全`6K`分岐列と
最外persistent uncomputeを含むactual row oracleが、`rowReference`のpredecessor・
column selectorを任意accumulatorへ厳密にXORし、全workを入力へ戻す。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_physicalEvent_correct
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOracleInputSpec p
      (eventOutput configuration source direction)
      (rowSelectorForEvent configuration source member direction) input) :
    RowReferenceBranchResult p configuration
      (selectorForEvent configuration source member direction) input
      ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input) := by
  let outputConfiguration := eventOutput configuration source direction
  let active := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
    reversibleGatePermutation input
  let moved := moveSite source direction
  have movedMember : moved ∈ outputConfiguration.1 := by
    exact moveSite_mem_updateConfiguration configuration (source, direction) member
  let slot := slotOfMember outputConfiguration moved movedMember
  let collision := eventCollision configuration source direction
  let offset := eventOffset direction collision
  let branchOutput := (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
    reversibleGatePermutation persistent
  have persistentSpec : RowOraclePersistentConditionsSpec p outputConfiguration active
      persistent := by
    simpa [persistent, outputConfiguration, active] using specification.afterPersistent
  have eventResult : RowEventActiveBranchResult p configuration source member offset
      persistent branchOutput := by
    dsimp [branchOutput]
    simpa [outputConfiguration, active, moved, slot, collision, offset] using
      applyRowEventReferenceAndRestoreWorkCircuit_physicalEvent configuration source member direction
        persistent persistentSpec
  have activeCircuit : dispatchRowSelectorToDiagonalOrEventCircuit p active =
      applyRowEventReferenceAndRestoreWorkCircuit p slot offset := by
    unfold dispatchRowSelectorToDiagonalOrEventCircuit
    have activeSlot : selectorSlot active = slot := by
      simp [active, rowSelectorForEvent, slot, outputConfiguration, moved]
    have activeOffset : selectorOffset active = offset := by
      simp [active, rowSelectorForEvent, offset, collision]
    rw [activeSlot, activeOffset]
    exact dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset
      (by
        simpa [offset, collision] using
          eventOffset_not_diagonal direction collision)
  have activeResult : (dispatchRowSelectorToDiagonalOrEventCircuit p active).runBasis
      reversibleGatePermutation persistent = branchOutput := by
    rw [activeCircuit]
  have branchOutputSpec : RowOraclePersistentConditionsSpec p outputConfiguration active
      branchOutput :=
    persistentSpec.of_broadAgreement eventResult.support_restored
  have inactiveInput : ∀ branch : QSelector p, branch ≠ active →
      (dispatchRowSelectorToDiagonalOrEventCircuit p branch).runBasis reversibleGatePermutation persistent =
        persistent := by
    intro branch different
    exact dispatchRowSelectorToDiagonalOrEventCircuit_inactive_of_selector_ne outputConfiguration active
      branch persistent persistentSpec different
  have inactiveOutput : ∀ branch : QSelector p, branch ≠ active →
      (dispatchRowSelectorToDiagonalOrEventCircuit p branch).runBasis reversibleGatePermutation branchOutput =
        branchOutput := by
    intro branch different
    exact dispatchRowSelectorToDiagonalOrEventCircuit_inactive_of_selector_ne outputConfiguration active
      branch branchOutput branchOutputSpec different
  have selectorEq : columnSelector =
      selectorOfSlotOffset (slotOfMember configuration source member) offset := by
    rfl
  have branchResult : RowReferenceBranchResult p configuration columnSelector
      persistent branchOutput :=
    eventResult.toRowReference columnSelector selectorEq
  simpa [columnSelector] using
    applyRowOracleReferenceAndRestoreWorkCircuit_correct_of_unique_active p configuration
      columnSelector active input branchOutput inactiveInput activeResult
        inactiveOutput branchResult

end ReversibleCircuit

end ProbabilityGeneratorQProof
