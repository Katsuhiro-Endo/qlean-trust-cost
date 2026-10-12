import QLean.Generator.Implementation.QOracleEventComputeLocality
import QLean.Generator.Implementation.QOracleEventComputedClean
import QLean.Generator.Implementation.QOracleBranchIndexing
import QLean.Generator.Implementation.QOraclePersistentLocality
import QLean.Generator.Implementation.QWriteMovedSelectorConfigurationBridge
import QLean.Generator.Implementation.ReversibleLogicSharedCoreReadoutAdapter

/-!
# Q column event 分岐の完全な基底作用

column event の実回路について、sorted writer と moved-selector の純粋参照式を結び、
局所的な compute--use--uncompute 復元へ持ち上げる。すべての証明は wire support と
有限 fold の一般補題を合成し、巨大行列や全基底の列挙を行わない。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- column event が出力配置の次数へ加える変化量。 -/
def columnEventDegreeChange (offset : Fin 6) : Int :=
  if offset.val % 2 = 1 then -1 else 0

/--
column persistent compute 後に各 event branch が利用する数学的状態仕様。
この構造は最終 API の仮定ではなく、canonical COPY 入力から内部で構成する中間補題用である。
-/
structure ColumnOraclePersistentConditionsSpec (p : QParameters)
    (configuration : QConfiguration p) (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- column selector register は指定 selector の little-endian bit 列である。 -/
  selector_bits : readWires (columnSelectorWires p) input =
    constantBits selector.val (columnSelectorWires p).length
  /-- column-key register は configuration の delimiter 符号である。 -/
  column_key_bits : readWires (columnKeyWires p) input =
    registerBitList (delimiterEncoding configuration)
  /-- persistent present bit は有効な物理 slot だけで真である。 -/
  present : ∀ slot : Fin p.K,
    input (oraclePresentWireAt p slot) =
      decide (slot.val < configuration.1.card)
  /-- 有効な column-key word は configuration の昇順 site を保持する。 -/
  active_word : ∀ (slot : Fin p.K)
    (active : slot.val < configuration.1.card),
    readWires (registerWordAt p (columnKeyWires p) slot) input =
      siteWordBits p (configuration.siteAt ⟨slot.val, active⟩)
  /-- persistent degree register は粒子数の one-hot 符号である。 -/
  degree : ∀ slot : Fin p.K,
    input (oracleDegreeWireAt p slot) =
      decide (slot.val + 1 = configuration.1.card)
  /-- 合法 delimiter flag は真である。 -/
  legal : input (oracleLegalWire p) = true
  /-- column-mode degree 条件は衝突 branch が可能な場合だけ真である。 -/
  degree_condition : input (oracleDegreeConditionWire p) =
    decide (1 < configuration.1.card)
  /-- branch 開始時の selector 一致 flag は 0 である。 -/
  selected_zero : input (oracleSelectedWire p) = false
  /-- branch 開始時の moved register は全 0 である。 -/
  moved_zero : ∀ wire ∈ oracleMovedWires p, input wire = false
  /-- branch 開始時の membership 出力 flag は全 0 である。 -/
  membership_zero : MembershipFlagsClean p input
  /-- branch 開始時の branch flag は 0 である。 -/
  branch_zero : input (oracleBranchWire p) = false
  /-- branch 開始時の candidate region は全 0 である。 -/
  candidate_zero : CandidateRegionClean p input
  /-- event compare・sort・writer の transient work は canonical clean である。 -/
  event_clean : EventSortCleanInput p input

/--
selector 外が全0の canonical 基底では、system→column-key COPY 後も
event sort が使う transient work は全て clean である。
-/
theorem xorSystemIntoColumnKey_eventSortClean
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    EventSortCleanInput p
      ((xorSystemIntoColumnKeyReversibleCircuit p).runBasis
        reversibleGatePermutation basis) := by
  let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
    reversibleGatePermutation basis
  have sliceZero {width : Nat}
      (slice : RegisterSlice p.oracleWorkWidth width) :
      ∀ wire ∈ ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth)), copied wire = false := by
    simpa [copied] using
      oracleSlice_zero_after_copy p configuration basis outside slice
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
    apply sliceZero (OracleWorkLayout.canonical p).compareWork wire
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member
  · intro wire member
    apply sliceZero (OracleWorkLayout.canonical p).andWork wire
    simpa [decoderAndScratchWires, oracleAndWorkWires,
      RegisterSlice.wireList] using List.mem_of_mem_drop member
  · apply sliceZero (OracleWorkLayout.canonical p).positionMatch
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).positionMatch).ancillaWire _ ∈ _
    simp [RegisterSlice.wireList]
  · apply sliceZero (OracleWorkLayout.canonical p).pair
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).pair).ancillaWire _ ∈ _
    simp [RegisterSlice.wireList]
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    simp only [sortCompareWorkWires, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with compareMember | extraMember
    · apply sliceZero (OracleWorkLayout.canonical p).compareWork wire
      simpa [oracleCompareWorkWires, RegisterSlice.wireList] using compareMember
    · subst wire
      apply sliceZero (OracleWorkLayout.canonical p).andWork
      simp [RegisterSlice.wireList]
  · intro wire member
    apply sliceZero (OracleWorkLayout.canonical p).andWork wire
    exact sortAndScratchWires_mem_andSlice p member
  · intro instruction instructionMember
    apply sliceZero (OracleWorkLayout.canonical p).sortFlags
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history, rfl⟩

/--
canonical COPY 後のpersistent compute出力は、全 event branch の sort 前 clean 条件を
外部契約なしで満たす。
-/
theorem columnOraclePersistent_after_copy_eventSortClean
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    EventSortCleanInput p
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation copied) := by
  dsimp only
  apply columnOraclePersistentOutput_eventSortClean p configuration
  · exact xorSystemIntoColumnKey_persistentCleanInput p configuration basis outside
  · exact xorSystemIntoColumnKey_eventSortClean p configuration basis outside

/--
degree・legal より後、candidate より前の oracle slice は compact decoder の厳密 support
外にあるため、persistent compute がその値を保存する。
-/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_preCandidateSlice
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (inputDisjointWork : inputWires.Disjoint (diagonalOracleWorkWires p))
    (rowMode : Bool) (input : JointBasis p.ancillaWidth p.systemWidth)
    {width : Nat} (middle : RegisterSlice p.oracleWorkWidth width)
    (degreeBefore :
      (OracleWorkLayout.canonical p).degree.start + p.degreeWidth ≤ middle.start)
    (specialBefore : (oraclePersistentSpecialSlice p).start + 2 ≤ middle.start)
    (middleBeforeCandidate : middle.start + width ≤
      (OracleWorkLayout.canonical p).candidate.start)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ ((QLayout.oracleSlice middle).wireList :
      List (Wire p.ancillaWidth p.systemWidth))) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input wire = input wire := by
  have outsideExact : wire ∉ compactDecoderExactSupport p inputWires := by
    intro supportMember
    have cases : wire ∈ inputWires ∨ wire ∈ decoderSuffixWires p ∨
        wire ∈ oracleDegreeWires p ∨ wire ∈ oracleCompareWorkWires p ∨
        wire ∈ oracleAndWorkWires p ∨ wire = oracleLegalWire p := by
      simpa only [compactDecoderExactSupport, decoderLegalitySupportFor,
        List.mem_append, List.mem_singleton, or_assoc] using supportMember
    rcases cases with inputMember | suffixMember | degreeMember | compareMember |
      andMember | legalEqual
    · exact (List.disjoint_left.mp inputDisjointWork inputMember)
        (diagonalOracleSlice_subset_work p middle member)
    · have candidateMember : wire ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).candidate).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) :=
        List.mem_of_mem_take suffixMember
      exact (List.disjoint_left.mp
        (RegisterSlice.wireList_disjoint_of_end_le_start
          (QLayout.oracleSlice middle)
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate)
          (by
            simp only [QLayout.oracleSlice, RegisterSlice.compose]
            omega))) member candidateMember
    · have degreeFull : wire ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).degree).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        simpa [oracleDegreeWires, RegisterSlice.wireList] using degreeMember
      exact (List.disjoint_left.mp
        (RegisterSlice.wireList_disjoint_of_end_le_start
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).degree)
          (QLayout.oracleSlice middle)
          (by
            simp only [QLayout.oracleSlice, RegisterSlice.compose]
            omega))) degreeFull member
    · have compareFull : wire ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).compareWork).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        simpa [oracleCompareWorkWires, RegisterSlice.wireList] using compareMember
      have middleBeforeCompare : middle.start + width ≤
          (OracleWorkLayout.canonical p).compareWork.start := by
        have candidateBeforeCompare :
            (OracleWorkLayout.canonical p).candidate.start ≤
              (OracleWorkLayout.canonical p).compareWork.start := by
          simp [OracleWorkLayout.canonical]
          omega
        exact le_trans middleBeforeCandidate candidateBeforeCompare
      exact (List.disjoint_left.mp
        (RegisterSlice.wireList_disjoint_of_end_le_start
          (QLayout.oracleSlice middle)
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork)
          (by
            simp only [QLayout.oracleSlice, RegisterSlice.compose]
            omega))) member compareFull
    · have andFull : wire ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).andWork).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        simpa [oracleAndWorkWires, RegisterSlice.wireList] using andMember
      have middleBeforeAnd : middle.start + width ≤
          (OracleWorkLayout.canonical p).andWork.start := by
        have candidateBeforeAnd :
            (OracleWorkLayout.canonical p).candidate.start ≤
              (OracleWorkLayout.canonical p).andWork.start := by
          simp [OracleWorkLayout.canonical]
          omega
        exact le_trans middleBeforeCandidate candidateBeforeAnd
      exact (List.disjoint_left.mp
        (RegisterSlice.wireList_disjoint_of_end_le_start
          (QLayout.oracleSlice middle)
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork)
          (by
            simp only [QLayout.oracleSlice, RegisterSlice.compose]
            omega))) member andFull
    · subst wire
      have legalMember : oracleLegalWire p ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).legal).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleLegalWire, RegisterSlice.wireList]
      have legalBefore : (OracleWorkLayout.canonical p).legal.start + 1 ≤
          middle.start := by
        have specialStarts :
            (OracleWorkLayout.canonical p).legal.start + 1 ≤
              (oraclePersistentSpecialSlice p).start := by
          simp [oraclePersistentSpecialSlice, OracleWorkLayout.canonical]
        exact le_trans specialStarts (le_trans (Nat.le_add_right _ _) specialBefore)
      exact (List.disjoint_left.mp
        (RegisterSlice.wireList_disjoint_of_end_le_start
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).legal)
          (QLayout.oracleSlice middle)
          (by simpa [QLayout.oracleSlice, RegisterSlice.compose] using legalBefore)))
            legalMember member
  have compactPreserves :
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
          reversibleGatePermutation input wire = input wire :=
    Circuit.runBasis_outside_of_usesOnly
      (compactDecoderExactSupport p inputWires)
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires)
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_usesOnly_exact p inputWires)
      input wire outsideExact
  have outsidePresent : wire ∉ oraclePresentWires p := by
    have presentBefore :
        (OracleWorkLayout.canonical p).present.start + p.presentWidth ≤
          middle.start := by
      have presentBeforeSpecial :
          (OracleWorkLayout.canonical p).present.start + p.presentWidth ≤
            (oraclePersistentSpecialSlice p).start := by
        simp [oraclePersistentSpecialSlice, OracleWorkLayout.canonical]
      exact le_trans presentBeforeSpecial
        (le_trans (Nat.le_add_right _ _) specialBefore)
    intro presentMember
    have presentFull : wire ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).present).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oraclePresentWires, RegisterSlice.wireList] using presentMember
    exact (List.disjoint_left.mp
      (RegisterSlice.wireList_disjoint_of_end_le_start
        (QLayout.oracleSlice (OracleWorkLayout.canonical p).present)
        (QLayout.oracleSlice middle)
        (by
          simp only [QLayout.oracleSlice, RegisterSlice.compose]
          omega))) presentFull member
  have outsideSpecial : wire ∉ oraclePersistentSpecialWires p := by
    intro specialMember
    have specialFull : wire ∈
        ((QLayout.oracleSlice (oraclePersistentSpecialSlice p)).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oraclePersistentSpecialWires] using specialMember
    exact (List.disjoint_left.mp
      (RegisterSlice.wireList_disjoint_of_end_le_start
        (QLayout.oracleSlice (oraclePersistentSpecialSlice p))
        (QLayout.oracleSlice middle)
        (by
          simp only [QLayout.oracleSlice, RegisterSlice.compose]
          omega))) specialFull member
  calc
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input wire =
        (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
          reversibleGatePermutation input wire :=
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_eq_compactDecoder_outside p inputWires rowMode
        input wire outsidePresent
        (fun equal => outsideSpecial (by
          rw [equal]
          exact oracleDegreeConditionWire_mem_special p))
        (fun equal => outsideSpecial (by
          rw [equal]
          exact oracleOneWire_mem_special p))
    _ = input wire := compactPreserves

/--
candidate より後かつ compare work より前の任意の oracle slice は、canonical COPY 後の
persistent compute でも全0のまま保存される。
-/
theorem columnOraclePersistent_after_copy_middleSlice_zero
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis)
    {width : Nat} (middle : RegisterSlice p.oracleWorkWidth width)
    (candidateBefore :
      (OracleWorkLayout.canonical p).candidate.start + p.candidateWidth ≤
        middle.start)
    (beforeCompare : middle.start + width ≤
      (OracleWorkLayout.canonical p).compareWork.start) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
      reversibleGatePermutation copied
    ∀ wire ∈ ((QLayout.oracleSlice middle).wireList :
      List (Wire p.ancillaWidth p.systemWidth)), persistent wire = false := by
  dsimp only
  intro wire member
  rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_middleOracleSlice p
    (columnKeyWires p) (columnKeyWires_disjoint_diagonalOracleWorkWires p)
    false
    ((xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis)
    middle candidateBefore beforeCompare wire member]
  exact oracleSlice_zero_after_copy p configuration basis outside middle wire member

/-- canonical persistent 出力では selector 一致 flag は0である。 -/
theorem columnOraclePersistent_after_copy_selected_zero
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
      reversibleGatePermutation copied
    persistent (oracleSelectedWire p) = false := by
  dsimp only
  rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_preCandidateSlice p
    (columnKeyWires p) (columnKeyWires_disjoint_diagonalOracleWorkWires p)
    false
    ((xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis)
    (OracleWorkLayout.canonical p).selected]
  · exact oracleSlice_zero_after_copy p configuration basis outside
      (OracleWorkLayout.canonical p).selected _ (by
        simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList])
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [oraclePersistentSpecialSlice, OracleWorkLayout.canonical]
  · simp [OracleWorkLayout.canonical]
  · simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]

/-- canonical persistent 出力では moved register は全0である。 -/
theorem columnOraclePersistent_after_copy_moved_zero
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
      reversibleGatePermutation copied
    ∀ wire ∈ oracleMovedWires p, persistent wire = false := by
  dsimp only
  intro wire member
  rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_preCandidateSlice p
    (columnKeyWires p) (columnKeyWires_disjoint_diagonalOracleWorkWires p)
    false
    ((xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis)
    (OracleWorkLayout.canonical p).moved]
  · exact oracleSlice_zero_after_copy p configuration basis outside
      (OracleWorkLayout.canonical p).moved wire
        (by simpa [oracleMovedWires, RegisterSlice.wireList] using member)
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [oraclePersistentSpecialSlice, OracleWorkLayout.canonical]
  · simp [OracleWorkLayout.canonical]
  · simpa [oracleMovedWires, RegisterSlice.wireList] using member

/-- canonical persistent 出力では membership 出力 flag は全0である。 -/
theorem columnOraclePersistent_after_copy_membership_zero
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
      reversibleGatePermutation copied
    MembershipFlagsClean p persistent := by
  dsimp only
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
    reversibleGatePermutation
      ((xorSystemIntoColumnKeyReversibleCircuit p).runBasis
        reversibleGatePermutation basis)
  have sliceZero {width : Nat}
      (middle : RegisterSlice p.oracleWorkWidth width)
      (candidateBefore :
        (OracleWorkLayout.canonical p).candidate.start + p.candidateWidth ≤
          middle.start)
      (beforeCompare : middle.start + width ≤
        (OracleWorkLayout.canonical p).compareWork.start) :
      ∀ wire ∈ ((QLayout.oracleSlice middle).wireList :
        List (Wire p.ancillaWidth p.systemWidth)), persistent wire = false := by
    simpa [persistent] using
      columnOraclePersistent_after_copy_middleSlice_zero p configuration basis
        outside middle candidateBefore beforeCompare
  refine {
    equal_zero := ?_
    good_zero := ?_
    present_other_zero := ?_
    absent_zero := ?_ }
  · intro slot
    exact sliceZero (OracleWorkLayout.canonical p).membershipEqual
      (by simp [OracleWorkLayout.canonical])
      (by simp [OracleWorkLayout.canonical]; omega)
      _ (membershipEqualWireAt_mem_slice p slot)
  · intro slot
    exact sliceZero (OracleWorkLayout.canonical p).membershipGood
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      _ (membershipGoodWireAt_mem_slice p slot)
  · exact sliceZero (OracleWorkLayout.canonical p).presentOther
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      _ (oraclePresentOtherWire_mem_slice p)
  · exact sliceZero (OracleWorkLayout.canonical p).absent
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      _ (oracleAbsentWire_mem_slice p)

/-- canonical persistent 出力では event branch flag は0である。 -/
theorem columnOraclePersistent_after_copy_branch_zero
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
      reversibleGatePermutation copied
    persistent (oracleBranchWire p) = false := by
  dsimp only
  apply columnOraclePersistent_after_copy_middleSlice_zero p configuration basis
    outside (OracleWorkLayout.canonical p).branch
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]

/--
一般入力register用のcompact decoderは、candidate sliceをscratchとして利用しても
compute--uncomputeの終了時にはその全wireを入力値へ厳密に戻す。
-/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_preserves_candidateSlice
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p inputWires)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input wire = input wire := by
  by_cases suffixMember : wire ∈ decoderSuffixWires p
  · let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input
    have agree : BasisAgreeOn (decoderLegalitySupportFor p inputWires)
        ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
          reversibleGatePermutation input) decoded := by
      simpa [decoded] using
        xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_support_restored_of_input p inputWires
          layout.membership.decoder input
    calc
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
          reversibleGatePermutation input wire = decoded wire :=
        agree wire (by simp [decoderLegalitySupportFor, suffixMember])
      _ = input wire := by
        change (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires
          (decoderSuffixWires p) (oracleDegreeWires p)).runBasis
            reversibleGatePermutation input wire = input wire
        rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_local_clean p.wordWidth inputWires
          (decoderSuffixWires p) (oracleDegreeWires p) input
          layout.membership.decoder.disjoint_suffix
          layout.membership.decoder.disjoint_degree
          (oracleDegreeWires_disjoint_decoderSuffixWires p).symm]
        simp [restoreSupport, suffixMember]
  · apply Circuit.runBasis_outside_of_usesOnly
      (compactDecoderExactSupport p inputWires)
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires)
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_usesOnly_exact p inputWires)
      input wire
    intro supportMember
    have cases : wire ∈ inputWires ∨ wire ∈ decoderSuffixWires p ∨
        wire ∈ oracleDegreeWires p ∨ wire ∈ oracleCompareWorkWires p ∨
        wire ∈ oracleAndWorkWires p ∨ wire = oracleLegalWire p := by
      simpa only [compactDecoderExactSupport, decoderLegalitySupportFor,
        List.mem_append, List.mem_singleton, or_assoc] using supportMember
    rcases cases with inputMember | suffixMember' | degreeMember |
      compareMember | andMember | legalEqual
    · exact (List.disjoint_left.mp layout.disjoint_candidate inputMember) member
    · exact suffixMember suffixMember'
    · have outside := laterOracleListWire_not_mem_earlierSlice p
        (OracleWorkLayout.canonical p).degree
        (OracleWorkLayout.canonical p).candidate
        (by simp [OracleWorkLayout.canonical]; omega) wire member
      exact outside (by
        simpa [oracleDegreeWires, RegisterSlice.wireList] using degreeMember)
    · exact (List.disjoint_left.mp
        (sortCandidateSlice_disjoint_compareSlice p) member) compareMember
    · exact (List.disjoint_left.mp
        (sortCandidateSlice_disjoint_andSlice p) member) andMember
    · have outside := laterOracleListWire_not_mem_earlierSlice p
        (OracleWorkLayout.canonical p).legal
        (OracleWorkLayout.canonical p).candidate
        (by simp [OracleWorkLayout.canonical]; omega) wire member
      apply outside
      rw [legalEqual]
      simp [oracleLegalWire, RegisterSlice.wireList]

/--
persistent decoder全体もcandidate sliceを一時scratchとしてしか用いず、全wireを復元する。
-/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_candidateSlice
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p inputWires)
    (rowMode : Bool) (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input wire = input wire := by
  have outsidePresent : wire ∉ oraclePresentWires p := by
    intro presentMember
    exact (List.disjoint_left.mp
      (oraclePresentWires_disjoint_candidateSlice p) presentMember) member
  have outsideSpecial : wire ∉ oraclePersistentSpecialWires p := by
    have outside := laterOracleListWire_not_mem_earlierSlice p
      (oraclePersistentSpecialSlice p)
      (OracleWorkLayout.canonical p).candidate
      (by simp [oraclePersistentSpecialSlice, OracleWorkLayout.canonical]; omega)
      wire member
    intro specialMember
    apply outside
    simpa [oraclePersistentSpecialWires] using specialMember
  calc
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input wire =
        (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
          reversibleGatePermutation input wire :=
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_eq_compactDecoder_outside p inputWires rowMode
        input wire outsidePresent
        (fun equal => outsideSpecial (by
          rw [equal]
          exact oracleDegreeConditionWire_mem_special p))
        (fun equal => outsideSpecial (by
          rw [equal]
          exact oracleOneWire_mem_special p))
    _ = input wire :=
      xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_preserves_candidateSlice p inputWires
        layout input wire member

/-- canonical COPY後のpersistent出力ではcandidate data・markerが全て0である。 -/
theorem columnOraclePersistent_after_copy_candidate_zero
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
      reversibleGatePermutation copied
    CandidateRegionClean p persistent := by
  dsimp only
  let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
    reversibleGatePermutation basis
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
    reversibleGatePermutation copied
  have preserve (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth))) :
      persistent wire = copied wire := by
    simpa [persistent] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_candidateSlice p (columnKeyWires p)
        (columnKeyWires_candidateInputLayout p) false copied wire member
  have copiedZero (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth))) :
      copied wire = false := by
    simpa [copied] using oracleSlice_zero_after_copy p configuration basis outside
      (OracleWorkLayout.canonical p).candidate wire member
  refine {
    data_zero := ?_
    marker_zero := ?_ }
  · intro word
    change readWires ((candidateWordAt p word).take p.wordWidth) persistent = _
    have pointwise : ∀ wire ∈ (candidateWordAt p word).take p.wordWidth,
        persistent wire = false := by
      intro wire wordMember
      rw [preserve wire (candidateWordAt_mem_candidateSlice p word
        (List.mem_of_mem_take wordMember))]
      exact copiedZero wire (candidateWordAt_mem_candidateSlice p word
        (List.mem_of_mem_take wordMember))
    simpa using readWires_eq_replicate_false_of_forall
      ((candidateWordAt p word).take p.wordWidth) persistent pointwise
  · intro word
    change persistent (candidateMarkerWire p word) = false
    rw [preserve (candidateMarkerWire p word)
      (candidateWordAt_mem_candidateSlice p word (by
        simp [candidateMarkerWire, candidateWordAt]))]
    exact copiedZero (candidateMarkerWire p word)
      (candidateWordAt_mem_candidateSlice p word (by
        simp [candidateMarkerWire, candidateWordAt]))

/-- column selector registerとoracle work全体は、canonical layout上で互いに素である。 -/
theorem columnSelectorWires_disjoint_diagonalOracleWork (p : QParameters) :
    (columnSelectorWires p).Disjoint (diagonalOracleWorkWires p) := by
  let selector := (QLayout.canonical p).columnSelector
  let work := (QLayout.canonical p).oracleWork
  have full :
      (selector.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (work.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    selector.wireList_disjoint_of_end_le_start work
      (by simp [selector, work, QLayout.canonical]; omega)
  simpa [columnSelectorWires, columnSelectorWire, diagonalOracleWorkWires,
    selector, work, RegisterSlice.wireList] using full

/-- persistent computeはcolumn selector registerをbitごとに厳密保存する。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_columnSelector
    (p : QParameters) (rowMode : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (columnSelectorWires p)
        ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) rowMode).runBasis
          reversibleGatePermutation input) =
      readWires (columnSelectorWires p) input := by
  apply List.map_congr_left
  intro wire selectorMember
  apply Circuit.runBasis_outside_of_usesOnly
    (oraclePersistentSupport p (columnKeyWires p))
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) rowMode)
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit_usesOnly p (columnKeyWires p) rowMode)
    input wire
  intro supportMember
  rcases List.mem_append.mp supportMember with keyMember | workMember
  · exact (List.disjoint_left.mp
      (columnKeyWires_disjoint_columnSelectorWires p) keyMember) selectorMember
  · exact (List.disjoint_left.mp
      (columnSelectorWires_disjoint_diagonalOracleWork p)
        selectorMember) workMember

/-- one-hot次数列の有効添字は、対応する粒子数等式を厳密に表す。 -/
theorem degreeOneHotFrom_getD_of_lt
    (count particleCount degree index : Nat) (indexLt : index < count) :
    (degreeOneHotFrom count particleCount degree)[index]?.getD false =
      decide (degree + index + 1 = particleCount) := by
  have dropped := degreeOneHotFrom_drop count particleCount degree index
    (Nat.le_of_lt indexLt)
  have head := congrArg (fun bits : List Bool => bits.head?.getD false) dropped
  have remaining : count - index = (count - index - 1) + 1 := by omega
  rw [remaining] at head
  simpa [degreeOneHotFrom, indexLt, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using head

/--
selector値を持つcanonical COPY入力から、column event全分岐が要求するpersistent仕様を
外部oracle契約なしで構成する。
-/
theorem columnOraclePersistent_after_copy_inputSpec
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis)
    (selectorBits : readWires (columnSelectorWires p) basis =
      constantBits selector.val (columnSelectorWires p).length) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
      reversibleGatePermutation copied
    ColumnOraclePersistentConditionsSpec p configuration selector persistent := by
  dsimp only
  let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
    reversibleGatePermutation basis
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
    reversibleGatePermutation copied
  have clean := xorSystemIntoColumnKey_persistentCleanInput p configuration basis outside
  have outputSpec := computeSharedDecoderPresenceParityAndOneFlagsCircuit_column_after_copy_correct p
    configuration basis outside
  have copiedSelector : readWires (columnSelectorWires p) copied =
      readWires (columnSelectorWires p) basis := by
    apply List.map_congr_left
    intro wire selectorMember
    rw [show copied = (xorCopy (topSystemWires p) (topColumnKeyWires p)).runBasis
        reversibleGatePermutation basis by
      rfl]
    apply runBasis_validatedXorCopyLists_outside
      (topSystemWires p) (topColumnKeyWires p) basis
      (topSystemWires_nodup p) (topColumnKeyWires_nodup p) (by simp)
      (topSystemWires_disjoint_topColumnKeyWires p)
    intro keyMember
    have keyMember' : wire ∈ columnKeyWires p := by
      simpa [columnKeyWires_eq_topColumnKeyWires] using keyMember
    exact (List.disjoint_left.mp
      (columnKeyWires_disjoint_columnSelectorWires p) keyMember')
        selectorMember
  refine {
    selector_bits := ?_
    column_key_bits := ?_
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
  · calc
      readWires (columnSelectorWires p) persistent =
          readWires (columnSelectorWires p) copied := by
        simpa [persistent] using
          computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_columnSelector p false copied
      _ = readWires (columnSelectorWires p) basis := copiedSelector
      _ = constantBits selector.val (columnSelectorWires p).length := selectorBits
  · simpa [persistent] using computeSharedDecoderPresenceParityAndOneFlagsCircuit_input_preserved_of_clean p
      (columnKeyWires p) (columnKeyWires_oraclePersistentInputLayout p)
      configuration copied clean false
  · intro slot
    simpa [persistent] using computeSharedDecoderPresenceParityAndOneFlagsCircuit_present_value_of_clean p
      (columnKeyWires p) (columnKeyWires_oraclePersistentInputLayout p)
      configuration copied clean false slot
  · intro slot active
    simpa [persistent, siteWordBits] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_activeWord_of_clean p (columnKeyWires p)
        (columnKeyWires_oraclePersistentInputLayout p) configuration copied
        clean false slot active
  · intro slot
    have point := congrArg (fun values : List Bool =>
      values[slot.val]?.getD false) outputSpec.degree
    change persistent (oracleDegreeWireAt p slot) = _
    simpa [persistent, readWires, oracleDegreeWires, oracleDegreeWireAt,
      QParameters.degreeWidth, slot.isLt,
      degreeOneHotFrom_getD_of_lt p.K configuration.1.card 0 slot.val slot.isLt]
      using point
  · simpa [persistent] using outputSpec.legal
  · simpa [persistent] using outputSpec.degreeCondition
  · simpa [persistent] using
      columnOraclePersistent_after_copy_selected_zero p configuration basis outside
  · simpa [persistent] using
      columnOraclePersistent_after_copy_moved_zero p configuration basis outside
  · simpa [persistent] using
      columnOraclePersistent_after_copy_membership_zero p configuration basis outside
  · simpa [persistent] using
      columnOraclePersistent_after_copy_branch_zero p configuration basis outside
  · simpa [persistent] using
      columnOraclePersistent_after_copy_candidate_zero p configuration basis outside
  · simpa [persistent] using
      columnOraclePersistent_after_copy_eventSortClean p configuration basis outside

/-- membership出力より前のoracle sliceにあるwireは、全membership出力と異なる。 -/
theorem columnMembershipOutputsSeparated_of_earlierSlice
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
        simp [OracleWorkLayout.canonical] at beforeEqual ⊢
        omega) member (membershipGoodWireAt_mem_slice p slot)
  · exact oracleSliceMembers_ne_of_end_le_start p earlier
      (OracleWorkLayout.canonical p).presentOther (by
        simp [OracleWorkLayout.canonical] at beforeEqual ⊢
        omega) member (oraclePresentOtherWire_mem_slice p)
  · exact oracleSliceMembers_ne_of_end_le_start p earlier
      (OracleWorkLayout.canonical p).absent (by
        simp [OracleWorkLayout.canonical] at beforeEqual ⊢
        omega) member (oracleAbsentWire_mem_slice p)

/-- column selector比較はselected flag以外の任意wireを保存する。 -/
theorem runBasis_columnEventSelectorCompute_other
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (different : wire ≠ oracleSelectedWire p) :
    (columnEventSelectorCompute p slot offset).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [runBasis_columnEventSelectorCompute p slot offset input
    clean.moved_selector.scratch_zero]
  split
  · exact xBasisAction_other (oracleSelectedWire p) wire different input
  · rfl

/-- moved copyとforward moveの合成はmoved slice外のwireを保存する。 -/
theorem runBasis_columnEventMovedCircuit_outside_movedSlice
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (columnEventMovedCircuit p slot offset).runBasis
        reversibleGatePermutation input wire = input wire := by
  let copied := (columnEventMovedCopy p slot).runBasis
    reversibleGatePermutation input
  have copiedClean : EventSortCleanInput p copied :=
    EventSortCleanInput.of_columnEventMovedCopy p slot input clean
  rw [columnEventMovedCircuit, runBasis_seq]
  calc
    (columnEventMoveForward p offset).runBasis reversibleGatePermutation copied wire =
        copied wire :=
      runBasis_columnEventMoveForward_outside_movedSlice p offset copied
        copiedClean.moved_selector.scratch_zero wire outside
    _ = input wire :=
      runBasis_columnEventMovedCopy_outside_movedSlice p slot input wire outside

/-- selector比較とmoved計算は、movedより後方の任意oracle sliceを保存する。 -/
theorem columnEventCandidateUpdateAndSortExecutionTrace_afterMoveForward_laterSlice
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) {width : Nat}
    (later : RegisterSlice p.oracleWorkWidth width)
    (afterMoved : (OracleWorkLayout.canonical p).moved.start + p.movedWidth ≤
      later.start) :
    readWires ((QLayout.oracleSlice later).wireList :
        List (Wire p.ancillaWidth p.systemWidth))
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterMoveForward =
      readWires ((QLayout.oracleSlice later).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) input := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_columnEventSelectorCompute p slot offset input clean
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
        simp [OracleWorkLayout.canonical] at afterMoved ⊢
        omega) selectedMember member).symm
  calc
    states.afterMoveForward wire = states.afterSelector wire := by
      rw [states.moveForward_eq, states.movedCopy_eq]
      exact runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
        states.afterSelector selectorClean wire outsideMoved
    _ = input wire := by
      rw [states.selector_eq]
      exact runBasis_columnEventSelectorCompute_other p slot offset input clean
        wire differentSelected

/-- column membership正本はmembership出力より前のsliceを厳密に保存する。 -/
theorem runBasis_columnEventMembership_earlierSlice
    (p : QParameters) (slot : Fin p.K) {width : Nat}
    (earlier : RegisterSlice p.oracleWorkWidth width)
    (beforeEqual : earlier.start + width ≤
      (OracleWorkLayout.canonical p).membershipEqual.start)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    readWires ((QLayout.oracleSlice earlier).wireList :
        List (Wire p.ancillaWidth p.systemWidth))
        ((columnEventMembership p slot).runBasis reversibleGatePermutation input) =
      readWires ((QLayout.oracleSlice earlier).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) input := by
  apply List.map_congr_left
  intro wire member
  exact runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other p (columnKeyWires p)
    (columnKeyWires_membershipInputLayout p) slot true input
      {
        equalWork_zero := clean.moved_selector.compare_zero
        scratch_zero := clean.moved_selector.scratch_zero }
      wire (columnMembershipOutputsSeparated_of_earlierSlice p earlier beforeEqual
        wire member)

/-- persistent入力のmembership flag clean性はforward move直後まで保存される。 -/
theorem ColumnOraclePersistentConditionsSpec.afterMoveForward_membershipZero
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOraclePersistentConditionsSpec p configuration selector input)
    (slot : Fin p.K) (offset : Fin 6) :
    MembershipFlagsClean p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterMoveForward := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have preserve {width : Nat}
      (later : RegisterSlice p.oracleWorkWidth width)
      (afterMoved : (OracleWorkLayout.canonical p).moved.start + p.movedWidth ≤
        later.start) :
      readWires ((QLayout.oracleSlice later).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) states.afterMoveForward =
        readWires ((QLayout.oracleSlice later).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) input :=
    columnEventCandidateUpdateAndSortExecutionTrace_afterMoveForward_laterSlice p slot offset input
      specification.event_clean later afterMoved
  refine {
    equal_zero := ?_
    good_zero := ?_
    present_other_zero := ?_
    absent_zero := ?_ }
  · intro current
    have values := preserve
      (OracleWorkLayout.canonical p).membershipEqual (by
        simp [OracleWorkLayout.canonical]; omega)
    exact (readWires_eq_at_of_eq _ _ _ values
      (membershipEqualWireAt_mem_slice p current)).trans
        (specification.membership_zero.equal_zero current)
  · intro current
    have values := preserve
      (OracleWorkLayout.canonical p).membershipGood (by
        simp [OracleWorkLayout.canonical]; omega)
    exact (readWires_eq_at_of_eq _ _ _ values
      (membershipGoodWireAt_mem_slice p current)).trans
        (specification.membership_zero.good_zero current)
  · have values := preserve
      (OracleWorkLayout.canonical p).presentOther (by
        simp [OracleWorkLayout.canonical]; omega)
    exact (readWires_eq_at_of_eq _ _ _ values
      (oraclePresentOtherWire_mem_slice p)).trans
        specification.membership_zero.present_other_zero
  · have values := preserve
      (OracleWorkLayout.canonical p).absent (by
        simp [OracleWorkLayout.canonical]; omega)
    exact (readWires_eq_at_of_eq _ _ _ values
      (oracleAbsentWire_mem_slice p)).trans
        specification.membership_zero.absent_zero

/-- branch計算はbranch target以外の任意wireを保存する。 -/
theorem runBasis_columnEventBranchCompute_other
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (different : wire ≠ oracleBranchWire p) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [runBasis_columnEventBranchCompute_canonical p slot offset input
    clean.moved_selector.scratch_zero]
  split
  · exact xBasisAction_other (oracleBranchWire p) wire different input
  · rfl

/--
persistent合法配置から、selector比較とforward move後にmembershipが読む
column-key・present・moved三領域の仕様を得る。
-/
theorem ColumnOraclePersistentConditionsSpec.afterMoveForward_membership
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOraclePersistentConditionsSpec p configuration selector input)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card) :
    ConfigurationMembershipInput p (columnKeyWires p) configuration
      (moveSite (configuration.siteAt ⟨slot.val, active⟩)
        (selectorDirection (selectorOfSlotOffset slot offset)))
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterMoveForward := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_columnEventSelectorCompute p slot offset input
      specification.event_clean
  have movedResult : readWires (oracleMovedWires p) states.afterMoveForward =
      siteWordBits p
        (moveSite (configuration.siteAt ⟨slot.val, active⟩)
          (selectorDirection (selectorOfSlotOffset slot offset))) := by
    rw [states.moveForward_eq, states.movedCopy_eq]
    change readWires (oracleMovedWires p)
        ((columnEventMovedCircuit p slot offset).runBasis
          reversibleGatePermutation states.afterSelector) = _
    apply runBasis_columnEventMovedCircuit_read p slot offset
      (configuration.siteAt ⟨slot.val, active⟩) states.afterSelector
    refine {
      source_word := ?_
      moved_zero := ?_
      scratch_zero := ?_ }
    · calc
        readWires (registerWordAt p (columnKeyWires p) slot)
            states.afterSelector =
            readWires (registerWordAt p (columnKeyWires p) slot) input := by
          apply List.map_congr_left
          intro wire member
          rw [states.selector_eq]
          exact runBasis_columnEventSelectorCompute_other p slot offset input
            specification.event_clean wire (by
              intro equal
              subst wire
              exact (List.disjoint_left.mp
                (columnKeyWires_disjoint_oracleSlice p
                  (OracleWorkLayout.canonical p).selected)
                (mem_register_of_mem_registerWordAt p (columnKeyWires p) slot
                  member)) (by
                    simp [oracleSelectedWire, oracleSingletonWire,
                      RegisterSlice.wireList]))
        _ = siteWordBits p
            (configuration.siteAt ⟨slot.val, active⟩) :=
          specification.active_word slot active
    · apply readWires_eq_replicate_false_of_forall
      intro wire member
      rw [states.selector_eq]
      rw [runBasis_columnEventSelectorCompute_other p slot offset input
        specification.event_clean wire]
      · exact specification.moved_zero wire member
      · intro equal
        subst wire
        have selectedMember : oracleSelectedWire p ∈
            ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).selected).wireList :
                List (Wire p.ancillaWidth p.systemWidth)) := by
          simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
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
        simp [oraclePresentWireAt, RegisterSlice.wireList]
      exact (List.disjoint_left.mp
        (RegisterSlice.wireList_disjoint_of_end_le_start
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).present)
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
          (by simp [QLayout.oracleSlice, RegisterSlice.compose,
            OracleWorkLayout.canonical]; omega)) presentMember) movedMember
    calc
      states.afterMoveForward (oraclePresentWireAt p current) =
          states.afterSelector (oraclePresentWireAt p current) := by
        rw [states.moveForward_eq, states.movedCopy_eq]
        exact runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
          states.afterSelector selectorClean _ presentOutside
      _ = input (oraclePresentWireAt p current) := by
        rw [states.selector_eq]
        exact runBasis_columnEventSelectorCompute_other p slot offset input
          specification.event_clean _ (by
            simpa [oraclePresentWireAt, oracleSelectedWire,
              oracleSingletonWire] using
              oracleSlice_ancillaWire_ne_of_localIndex_ne p
                (OracleWorkLayout.canonical p).present
                (OracleWorkLayout.canonical p).selected current 0 (by
                  simp [OracleWorkLayout.canonical]; omega))
      _ = decide (current.val < configuration.1.card) :=
        specification.present current
  · intro current currentActive
    calc
      readWires (registerWordAt p (columnKeyWires p) current)
          states.afterMoveForward =
          readWires (registerWordAt p (columnKeyWires p) current)
            states.afterSelector := by
        rw [states.moveForward_eq, states.movedCopy_eq]
        apply List.map_congr_left
        intro wire member
        exact runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
          states.afterSelector selectorClean wire (by
            intro movedMember
            exact (List.disjoint_left.mp
              (columnKeyWires_disjoint_oracleSlice p
                (OracleWorkLayout.canonical p).moved)
              (mem_register_of_mem_registerWordAt p (columnKeyWires p) current
                member)) movedMember)
      _ = readWires (registerWordAt p (columnKeyWires p) current) input := by
        apply List.map_congr_left
        intro wire member
        rw [states.selector_eq]
        exact runBasis_columnEventSelectorCompute_other p slot offset input
          specification.event_clean wire (by
            intro equal
            subst wire
            exact (List.disjoint_left.mp
              (columnKeyWires_disjoint_oracleSlice p
                (OracleWorkLayout.canonical p).selected)
              (mem_register_of_mem_registerWordAt p (columnKeyWires p) current
                member)) (by
                  simp [oracleSelectedWire, oracleSingletonWire,
                    RegisterSlice.wireList]))
      _ = siteWordBits p
          (configuration.siteAt ⟨current.val, currentActive⟩) :=
        specification.active_word current currentActive

/-- persistent入力のcandidate全0条件はcolumn branch計算直後まで保存される。 -/
theorem ColumnOraclePersistentConditionsSpec.afterBranch_candidateZero
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOraclePersistentConditionsSpec p configuration selector input)
    (slot : Fin p.K) (offset : Fin 6) :
    CandidateRegionClean p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    have selectorClean : EventSortCleanInput p states.afterSelector := by
      rw [states.selector_eq]
      exact EventSortCleanInput.of_columnEventSelectorCompute p slot offset input
        specification.event_clean
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.movedCopy_eq]
      exact EventSortCleanInput.of_columnEventMovedCopy p slot _ selectorClean
    have movedClean : EventSortCleanInput p states.afterMoveForward := by
      rw [states.moveForward_eq]
      exact EventSortCleanInput.of_columnEventMoveForward p offset _ copiedClean
    rw [states.membership_eq]
    exact EventSortCleanInput.of_columnEventMembership p slot _ movedClean
  have candidateAfterMove :=
    columnEventCandidateUpdateAndSortExecutionTrace_afterMoveForward_laterSlice p slot offset input
      specification.event_clean (OracleWorkLayout.canonical p).candidate (by
        simp [OracleWorkLayout.canonical])
  have candidateAfterMembership :
      readWires ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) states.afterMembership =
        readWires ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).candidate).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) states.afterMoveForward := by
    rw [states.membership_eq]
    exact runBasis_columnEventMembership_earlierSlice p slot
      (OracleWorkLayout.canonical p).candidate (by
        simp [OracleWorkLayout.canonical]) states.afterMoveForward
          (by
            have selectorClean : EventSortCleanInput p states.afterSelector := by
              rw [states.selector_eq]
              exact EventSortCleanInput.of_columnEventSelectorCompute p slot offset
                input specification.event_clean
            have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
              rw [states.movedCopy_eq]
              exact EventSortCleanInput.of_columnEventMovedCopy p slot _ selectorClean
            rw [states.moveForward_eq]
            exact EventSortCleanInput.of_columnEventMoveForward p offset _ copiedClean)
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
    exact runBasis_columnEventBranchCompute_other p slot offset
      states.afterMembership membershipClean wire (by
        have branchMember : oracleBranchWire p ∈
            ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).branch).wireList :
                List (Wire p.ancillaWidth p.systemWidth)) := by
          simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
        exact oracleSliceMembers_ne_of_end_le_start p
          (OracleWorkLayout.canonical p).candidate
          (OracleWorkLayout.canonical p).branch (by
            simp [OracleWorkLayout.canonical]; omega) member branchMember)
  have candidateEqual :=
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

/--
column event use の実回路は、canonical sorted writer の後に moved-selector の純粋 fold を
適用した参照作用と一致する。
-/
theorem runBasis_xorColumnEventDelimiterAndSelectorIntoOutputsCircuit_reference
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset) input)) :
    let sorted := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
      (by simp [rowOutputWires]) (activeWire p)
      (columnEventDegreeChange offset) input
    let output := (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input
    readWires (selectorOutputWires p) output =
        movedMemberPositionSelectorOutputXorReference p offset.val (selectorOutputWires p) sorted ∧
      BasisAgreeOutside (selectorOutputWires p) output sorted := by
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
    (by simp [rowOutputWires]) (activeWire p)
    (columnEventDegreeChange offset) input
  let output := (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input
  have sortedEq :
      (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (rowOutputWires p) (by simp [rowOutputWires])
        (activeWire p) (columnEventDegreeChange offset)).runBasis
          reversibleGatePermutation input = sorted := by
    simpa [sorted, columnEventDegreeChange, canonicalSortedOutputWires,
      canonicalSortedOutputActive] using
      runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical p .rowOutput
        (columnEventDegreeChange offset) input scratchZero pairZero
  have outputEq : output =
      (xorMovedMemberPositionIntoSelectorOutputCircuit p offset.val (selectorOutputWires p)).runBasis
        reversibleGatePermutation sorted := by
    change (xorMovedMemberPositionIntoSelectorOutputCircuit p offset.val (selectorOutputWires p)).runBasis
      reversibleGatePermutation
        ((xorSortedCandidatesAsDelimiterIntoOutputCircuit p (rowOutputWires p) (by simp [rowOutputWires])
          (activeWire p) (columnEventDegreeChange offset)).runBasis
            reversibleGatePermutation input) = _
    rw [sortedEq]
  change readWires (selectorOutputWires p) output =
      movedMemberPositionSelectorOutputXorReference p offset.val (selectorOutputWires p) sorted ∧
    BasisAgreeOutside (selectorOutputWires p) output sorted
  rw [outputEq, runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_slotFold]
  exact runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitSlotList_correct p offset.val
    (selectorOutputWires p) sorted
    (MovedMemberPositionSelectorOutputLayout_selectorOutput_canonical p) movedClean
    (List.finRange p.K) sorted (by
      intro wire outside
      rfl)

/-- 一つの次数に対する sorted writer は row-output と active 以外を保存する。 -/
theorem writeSortedDegreeReference_outside_rowOutput
    (p : QParameters) (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideOutput : wire ∉ rowOutputWires p)
    (outsideActive : wire ≠ activeWire p) :
    writeSortedDegreeReference p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p) degreeSlot degreeChange input wire =
      input wire := by
  unfold writeSortedDegreeReference
  split
  · apply writeSortedUseReference_outside p (rowOutputWires p)
      (by simp [rowOutputWires]) (activeWire p) _ _ _ input wire
      outsideOutput outsideActive
  · rfl

/-- sorted writer の全次数 fold は row-output と active 以外を保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_rowOutput
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideOutput : wire ∉ rowOutputWires p)
    (outsideActive : wire ≠ activeWire p) :
    SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p) degreeChange input wire =
      input wire := by
  unfold SortedCandidatesDelimiterOutputXorSpec
  let slots := List.finRange p.K
  change slots.foldl (fun state degreeSlot =>
      writeSortedDegreeReference p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p) degreeSlot degreeChange state)
      input wire = input wire
  induction slots generalizing input with
  | nil => rfl
  | cons degreeSlot slots inductionHypothesis =>
      simp only [List.foldl_cons]
      calc
        slots.foldl (fun state nextSlot =>
            writeSortedDegreeReference p (rowOutputWires p)
              (by simp [rowOutputWires]) (activeWire p) nextSlot degreeChange state)
            (writeSortedDegreeReference p (rowOutputWires p)
              (by simp [rowOutputWires]) (activeWire p) degreeSlot degreeChange input)
            wire =
          writeSortedDegreeReference p (rowOutputWires p)
            (by simp [rowOutputWires]) (activeWire p) degreeSlot degreeChange input
            wire := inductionHypothesis _
        _ = input wire := writeSortedDegreeReference_outside_rowOutput p
          degreeSlot degreeChange input wire outsideOutput outsideActive

/-- column event compute support は row-output register と交わらない。 -/
theorem columnEventCandidateUpdateAndSortSupport_disjoint_rowOutput (p : QParameters) :
    (columnEventCandidateUpdateAndSortSupport p).Disjoint (rowOutputWires p) := by
  rw [List.disjoint_left]
  intro wire supportMember outputMember
  rcases List.mem_append.mp supportMember with prefixMember | workMember
  · rcases List.mem_append.mp prefixMember with selectorMember | keyMember
    · exact (List.disjoint_left.mp (columnDiagonalSupport_disjoint_rowOutput p))
        (List.mem_append_left _ selectorMember) outputMember
    · exact (List.disjoint_left.mp (columnKeyWires_disjoint_rowOutputWires p))
        keyMember outputMember
  · exact (List.disjoint_left.mp (columnDiagonalSupport_disjoint_rowOutput p))
      (List.mem_append_right _ workMember) outputMember

/-- column-key register は selector-output register と交わらない。 -/
theorem columnKeyWires_disjoint_selectorOutputWires (p : QParameters) :
    (columnKeyWires p).Disjoint (selectorOutputWires p) := by
  let key := (QLayout.canonical p).columnKey
  let output := (QLayout.canonical p).selectorOutput
  have separated :
      (key.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (output.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    key.wireList_disjoint_of_end_le_start output
      (by simp [key, output, QLayout.canonical]; omega)
  simpa [columnKeyWires, columnKeyWire, selectorOutputWires,
    selectorOutputWire, key, output, RegisterSlice.wireList] using separated

/-- column event compute support は selector-output register と交わらない。 -/
theorem columnEventCandidateUpdateAndSortSupport_disjoint_selectorOutput (p : QParameters) :
    (columnEventCandidateUpdateAndSortSupport p).Disjoint (selectorOutputWires p) := by
  rw [List.disjoint_left]
  intro wire supportMember outputMember
  rcases List.mem_append.mp supportMember with prefixMember | workMember
  · rcases List.mem_append.mp prefixMember with selectorMember | keyMember
    · exact
        (List.disjoint_left.mp (columnDiagonalSupport_disjoint_selectorOutput p))
          (List.mem_append_left _ selectorMember) outputMember
    · exact
        (List.disjoint_left.mp (columnKeyWires_disjoint_selectorOutputWires p))
          keyMember outputMember
  · exact
      (List.disjoint_left.mp (columnDiagonalSupport_disjoint_selectorOutput p))
        (List.mem_append_right _ workMember) outputMember

/-- active 出力 bit は column event compute support に含まれない。 -/
theorem activeWire_not_mem_columnEventCandidateUpdateAndSortSupport (p : QParameters) :
    activeWire p ∉ columnEventCandidateUpdateAndSortSupport p := by
  intro supportMember
  rcases List.mem_append.mp supportMember with prefixMember | workMember
  · rcases List.mem_append.mp prefixMember with selectorMember | keyMember
    · exact activeWire_not_mem_columnDiagonalSupport p
        (List.mem_append_left _ selectorMember)
    · let key := (QLayout.canonical p).columnKey
      let active := (QLayout.canonical p).active
      have separated :
          (key.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
            (active.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
        key.wireList_disjoint_of_end_le_start active
          (by simp [key, active, QLayout.canonical]; omega)
      have activeMember : activeWire p ∈
          (active.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
        change active.ancillaWire 0 ∈
          (active.wireList : List (Wire p.ancillaWidth p.systemWidth))
        rw [RegisterSlice.wireList]
        exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
      exact (List.disjoint_left.mp separated)
        (by simpa [columnKeyWires, columnKeyWire, key,
          RegisterSlice.wireList] using keyMember) activeMember
  · exact activeWire_not_mem_columnDiagonalSupport p
      (List.mem_append_right _ workMember)

/--
sorted writer と moved-selector の出力が support 外にあるなら、column event use は support
上の全 bit を保存する。
-/
theorem xorColumnEventDelimiterAndSelectorIntoOutputsCircuit_preserves_support
    (p : QParameters) (offset : Fin 6)
    (support : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset) input))
    (supportDisjointOutput : support.Disjoint (rowOutputWires p))
    (supportDisjointSelector : support.Disjoint (selectorOutputWires p))
    (activeOutside : activeWire p ∉ support) :
    BasisAgreeOn support
      ((xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input) input := by
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
    (by simp [rowOutputWires]) (activeWire p)
    (columnEventDegreeChange offset) input
  have useResult := runBasis_xorColumnEventDelimiterAndSelectorIntoOutputsCircuit_reference p offset input scratchZero
    pairZero movedClean
  intro wire supportMember
  have outsideSelector : wire ∉ selectorOutputWires p := by
    intro selectorMember
    exact (List.disjoint_left.mp supportDisjointSelector) supportMember selectorMember
  have outsideOutput : wire ∉ rowOutputWires p := by
    intro outputMember
    exact (List.disjoint_left.mp supportDisjointOutput) supportMember outputMember
  have outsideActive : wire ≠ activeWire p := by
    intro equal
    subst wire
    exact activeOutside supportMember
  calc
    (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input wire =
        sorted wire := useResult.2 wire outsideSelector
    _ = input wire := xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_rowOutput p
      (columnEventDegreeChange offset) input wire outsideOutput outsideActive

/-- canonical column event compute support 上で use は全 bit を保存する。 -/
theorem xorColumnEventDelimiterAndSelectorIntoOutputsCircuit_preserves_computeSupport
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset) input)) :
    BasisAgreeOn (columnEventCandidateUpdateAndSortSupport p)
      ((xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input) input := by
  exact xorColumnEventDelimiterAndSelectorIntoOutputsCircuit_preserves_support p offset (columnEventCandidateUpdateAndSortSupport p)
    input scratchZero pairZero movedClean
      (columnEventCandidateUpdateAndSortSupport_disjoint_rowOutput p)
      (columnEventCandidateUpdateAndSortSupport_disjoint_selectorOutput p)
      (activeWire_not_mem_columnEventCandidateUpdateAndSortSupport p)

/--
column event compute の局所性と use の support 保存から、分岐全体を support 復元式へ
厳密に変換する。
-/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_eq_restoreComputeSupport
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false)
    (pairZero : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset)
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output)) :
    (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input =
      restoreSupport (columnEventCandidateUpdateAndSortSupport p) input
        ((xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
          (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output) := by
  rw [applyColumnEventReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
  apply Circuit.computeUseUncompute_local_clean (columnEventCandidateUpdateAndSortSupport p)
    (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset) input
      (computeColumnEventCandidateUpdateAndSortCircuit_usesOnly p slot offset)
  rw [← columnEventCandidateUpdateAndSortExecutionTrace_output]
  exact xorColumnEventDelimiterAndSelectorIntoOutputsCircuit_preserves_computeSupport p offset
    (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output scratchZero pairZero
      movedClean

/-- column event 分岐の純粋 writer 出力と support 復元をまとめた仕様。 -/
structure ColumnEventBranchReferenceResult (p : QParameters) (offset : Fin 6)
    (input computed output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- row-output は canonical sorted writer の参照出力に一致する。 -/
  row_output : readWires (rowOutputWires p) output =
    readWires (rowOutputWires p)
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset) computed)
  /-- selector-output は sorted writer 後の moved-selector 参照 fold に一致する。 -/
  selector_output : readWires (selectorOutputWires p) output =
    movedMemberPositionSelectorOutputXorReference p offset.val (selectorOutputWires p)
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset) computed)
  /-- active bit は sorted writer の参照出力に一致する。 -/
  active : output (activeWire p) =
    SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
      (by simp [rowOutputWires]) (activeWire p)
      (columnEventDegreeChange offset) computed (activeWire p)
  /-- compute support は入力値へ完全に復元される。 -/
  support_restored : BasisAgreeOn (columnEventCandidateUpdateAndSortSupport p) output input

/--
clean な actual compute 出力では、column event 分岐全体が純粋 writer 参照仕様を満たす。
-/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_reference_correct
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false)
    (pairZero : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset)
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output)) :
    ColumnEventBranchReferenceResult p offset input
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      ((applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  let computed := (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
    (by simp [rowOutputWires]) (activeWire p)
    (columnEventDegreeChange offset) computed
  let used := (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation computed
  let output := (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
    reversibleGatePermutation input
  have outputEq : output =
      restoreSupport (columnEventCandidateUpdateAndSortSupport p) input used := by
    dsimp [output, used, computed]
    exact applyColumnEventReferenceAndRestoreWorkCircuit_eq_restoreComputeSupport p slot offset input
      scratchZero pairZero movedClean
  have useSpec :
      readWires (selectorOutputWires p) used =
          movedMemberPositionSelectorOutputXorReference p offset.val (selectorOutputWires p)
            sorted ∧
        BasisAgreeOutside (selectorOutputWires p) used sorted := by
    dsimp [used, sorted, computed]
    exact runBasis_xorColumnEventDelimiterAndSelectorIntoOutputsCircuit_reference p offset _ scratchZero pairZero movedClean
  have rowUsed : readWires (rowOutputWires p) used =
      readWires (rowOutputWires p) sorted := by
    apply List.map_congr_left
    intro wire member
    exact useSpec.2 wire
      ((List.disjoint_left.mp (rowOutputWires_disjoint_selectorOutputWires p))
        member)
  have activeUsed : used (activeWire p) = sorted (activeWire p) :=
    useSpec.2 (activeWire p) (activeWire_not_mem_selectorOutputWires p)
  have rowFinal : readWires (rowOutputWires p) output =
      readWires (rowOutputWires p) used := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (columnEventCandidateUpdateAndSortSupport p) input used wire
      (fun supportMember =>
        (List.disjoint_left.mp (columnEventCandidateUpdateAndSortSupport_disjoint_rowOutput p))
          supportMember member)
  have selectorFinal : readWires (selectorOutputWires p) output =
      readWires (selectorOutputWires p) used := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (columnEventCandidateUpdateAndSortSupport p) input used wire
      (fun supportMember =>
        (List.disjoint_left.mp
          (columnEventCandidateUpdateAndSortSupport_disjoint_selectorOutput p))
            supportMember member)
  have activeFinal : output (activeWire p) = used (activeWire p) := by
    rw [outputEq]
    exact restoreSupport_outside (columnEventCandidateUpdateAndSortSupport p) input used
      (activeWire p) (activeWire_not_mem_columnEventCandidateUpdateAndSortSupport p)
  change ColumnEventBranchReferenceResult p offset input computed output
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [sorted] using rowFinal.trans rowUsed
  · simpa [sorted] using selectorFinal.trans useSpec.1
  · simpa [sorted] using activeFinal.trans activeUsed
  · intro wire member
    rw [outputEq]
    exact restoreSupport_agrees_input (columnEventCandidateUpdateAndSortSupport p) input used
      wire member

/-- active column event の compute 末尾で writer 接続に必要な事実をまとめた仕様。 -/
structure ColumnEventActiveComputedSpec (p : QParameters)
    (configuration : QConfiguration p) (moved : QSite p)
    (member : moved ∈ configuration.1) (offset : Fin 6)
    (degreeSlot : Fin p.K)
    (computed : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 選択次数と event の次数変化は出力配置の粒子数に一致する。 -/
  output_degree : Int.ofNat (degreeSlot.val + 1) +
    columnEventDegreeChange offset = Int.ofNat configuration.1.card
  /-- active compute 末尾の branch bit は真である。 -/
  branch_true : computed (oracleBranchWire p) = true
  /-- persistent degree register は選択次数の one-hot を保持する。 -/
  degree_oneHot : ∀ slot : Fin p.K,
    computed (oracleDegreeWireAt p slot) = decide (slot = degreeSlot)
  /-- sort 後 candidate 値は出力配置の canonical 候補に一致する。 -/
  candidate_values : qCandidateValue p computed =
    configurationCandidateValue p configuration
  /-- moved register は出力配置中の移動後 site を保持する。 -/
  moved_word : readWires (oracleMovedWires p) computed = siteWordBits p moved
  /-- sorted writer 用 AND scratch は全て 0 である。 -/
  scratch_zero : ∀ wire ∈ decoderAndScratchWires p, computed wire = false
  /-- sorted writer 用 pair bit は 0 である。 -/
  pair_zero : computed (oraclePairWire p) = false
  /-- sorted writer 後も moved-selector の一時 work は clean である。 -/
  moved_clean : WriteMovedSelectorSlotClean p
    (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
      (by simp [rowOutputWires]) (activeWire p)
      (columnEventDegreeChange offset) computed)

/-- active column event の外部 XOR 出力と内部復元をまとめた最終分岐仕様。 -/
structure ColumnEventActiveBranchResult (p : QParameters)
    (configuration : QConfiguration p) (moved : QSite p)
    (member : moved ∈ configuration.1) (offset : Fin 6)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- row-output は出力配置の delimiter 符号を accumulator へ XOR する。 -/
  row_output : readWires (rowOutputWires p) output =
    List.zipWith
      (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
      (registerBitList (delimiterEncoding configuration))
      (readWires (rowOutputWires p) input)
  /-- selector-output は moved site の canonical slot と offset を XOR する。 -/
  selector_output : readWires (selectorOutputWires p) output =
    controlledXorConstantBits true
      (6 * (slotOfMember configuration moved member).val + offset.val) 0
      (readWires (selectorOutputWires p) input)
  /-- active 出力 bit は一回反転する。 -/
  active : output (activeWire p) = !(input (activeWire p))
  /-- column selector・column key・oracle work は全て入力へ復元される。 -/
  support_restored : BasisAgreeOn (columnEventCandidateUpdateAndSortSupport p) output input
  /-- 三つの外部出力領域以外の任意 wire も入力へ復元される。 -/
  outside_restored : ∀ wire,
    wire ∉ rowOutputWires p → wire ∉ selectorOutputWires p →
      wire ≠ activeWire p → output wire = input wire

/--
三つの外部出力領域に属さない wire は、clean な column event 分岐の前後で入力値へ戻る。
-/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_outside_outputs_restored
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false)
    (pairZero : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset)
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output))
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideOutput : wire ∉ rowOutputWires p)
    (outsideSelector : wire ∉ selectorOutputWires p)
    (outsideActive : wire ≠ activeWire p) :
    (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input wire = input wire := by
  let computed := (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
    (by simp [rowOutputWires]) (activeWire p)
    (columnEventDegreeChange offset) computed
  let used := (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation computed
  let output := (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
    reversibleGatePermutation input
  have outputEq : output =
      restoreSupport (columnEventCandidateUpdateAndSortSupport p) input used := by
    dsimp [output, used, computed]
    exact applyColumnEventReferenceAndRestoreWorkCircuit_eq_restoreComputeSupport p slot offset input
      scratchZero pairZero movedClean
  by_cases supportMember : wire ∈ columnEventCandidateUpdateAndSortSupport p
  · change output wire = input wire
    rw [outputEq]
    exact restoreSupport_agrees_input (columnEventCandidateUpdateAndSortSupport p) input used
      wire supportMember
  · have useOutside : used wire = sorted wire := by
      have useSpec := runBasis_xorColumnEventDelimiterAndSelectorIntoOutputsCircuit_reference p offset computed
        scratchZero pairZero movedClean
      exact useSpec.2 wire outsideSelector
    have sortedOutside : sorted wire = computed wire :=
      xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_rowOutput p
        (columnEventDegreeChange offset) computed wire outsideOutput outsideActive
    have computedOutside : computed wire = input wire := by
      dsimp [computed]
      rw [columnEventCandidateUpdateAndSortExecutionTrace_output]
      exact Circuit.runBasis_outside_of_usesOnly (columnEventCandidateUpdateAndSortSupport p)
        (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) (computeColumnEventCandidateUpdateAndSortCircuit_usesOnly p slot offset)
        input wire supportMember
    change output wire = input wire
    rw [outputEq]
    exact (restoreSupport_outside (columnEventCandidateUpdateAndSortSupport p) input used wire
      supportMember).trans (useOutside.trans (sortedOutside.trans computedOutside))

/--
writer の delimiter/active と moved-selector の純粋 XOR 式が得られれば、actual column
event 分岐の全出力と内部復元を一括して得る。
-/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_active_of_writer_references
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (configuration : QConfiguration p) (moved : QSite p)
    (member : moved ∈ configuration.1) (degreeSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (computedSpec : ColumnEventActiveComputedSpec p configuration moved member
      offset degreeSlot (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output)
    (writerOutput :
      let computed := (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      let sorted := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset) computed
      readWires (rowOutputWires p) sorted =
        List.zipWith
          (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
          (registerBitList (delimiterEncoding configuration))
          (readWires (rowOutputWires p) computed))
    (writerActive :
      let computed := (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      let sorted := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset) computed
      sorted (activeWire p) = !(computed (activeWire p)))
    (movedSelector :
      let computed := (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      let sorted := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset) computed
      movedMemberPositionSelectorOutputXorReference p offset.val (selectorOutputWires p) sorted =
        controlledXorConstantBits true
          (6 * (slotOfMember configuration moved member).val + offset.val) 0
          (readWires (selectorOutputWires p) sorted)) :
    ColumnEventActiveBranchResult p configuration moved member offset input
      ((applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  let computed := (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
    (by simp [rowOutputWires]) (activeWire p)
    (columnEventDegreeChange offset) computed
  let output := (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
    reversibleGatePermutation input
  have referenceSpec : ColumnEventBranchReferenceResult p offset input computed
      output := by
    change ColumnEventBranchReferenceResult p offset input
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output _
    exact applyColumnEventReferenceAndRestoreWorkCircuit_reference_correct p slot offset input
      computedSpec.scratch_zero computedSpec.pair_zero computedSpec.moved_clean
  have computedOutput : readWires (rowOutputWires p) computed =
      readWires (rowOutputWires p) input := by
    dsimp [computed]
    rw [columnEventCandidateUpdateAndSortExecutionTrace_output]
    exact readWires_runBasis_of_usesOnly_disjoint
      (columnEventCandidateUpdateAndSortSupport p) (rowOutputWires p)
      (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) input
      (computeColumnEventCandidateUpdateAndSortCircuit_usesOnly p slot offset)
      (columnEventCandidateUpdateAndSortSupport_disjoint_rowOutput p)
  have computedSelector : readWires (selectorOutputWires p) computed =
      readWires (selectorOutputWires p) input := by
    dsimp [computed]
    rw [columnEventCandidateUpdateAndSortExecutionTrace_output]
    exact readWires_runBasis_of_usesOnly_disjoint
      (columnEventCandidateUpdateAndSortSupport p) (selectorOutputWires p)
      (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) input
      (computeColumnEventCandidateUpdateAndSortCircuit_usesOnly p slot offset)
      (columnEventCandidateUpdateAndSortSupport_disjoint_selectorOutput p)
  have computedActive : computed (activeWire p) = input (activeWire p) := by
    dsimp [computed]
    rw [columnEventCandidateUpdateAndSortExecutionTrace_output]
    exact Circuit.runBasis_outside_of_usesOnly (columnEventCandidateUpdateAndSortSupport p)
      (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) (computeColumnEventCandidateUpdateAndSortCircuit_usesOnly p slot offset)
      input (activeWire p) (activeWire_not_mem_columnEventCandidateUpdateAndSortSupport p)
  have sortedSelector : readWires (selectorOutputWires p) sorted =
      readWires (selectorOutputWires p) computed := by
    apply List.map_congr_left
    intro wire selectorMember
    apply xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_rowOutput
    · exact (List.disjoint_left.mp
        (rowOutputWires_disjoint_selectorOutputWires p).symm) selectorMember
    · intro equal
      subst wire
      exact activeWire_not_mem_selectorOutputWires p selectorMember
  have writerOutput' : readWires (rowOutputWires p) sorted =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (registerBitList (delimiterEncoding configuration))
        (readWires (rowOutputWires p) computed) := by
    simpa [sorted, computed] using writerOutput
  have writerActive' : sorted (activeWire p) = !(computed (activeWire p)) := by
    simpa [sorted, computed] using writerActive
  have movedSelector' :
      movedMemberPositionSelectorOutputXorReference p offset.val (selectorOutputWires p) sorted =
        controlledXorConstantBits true
          (6 * (slotOfMember configuration moved member).val + offset.val) 0
          (readWires (selectorOutputWires p) sorted) := by
    simpa [sorted, computed] using movedSelector
  change ColumnEventActiveBranchResult p configuration moved member offset input
    output
  refine ⟨?_, ?_, ?_, referenceSpec.support_restored, ?_⟩
  · rw [referenceSpec.row_output]
    change readWires (rowOutputWires p) sorted = _
    rw [writerOutput', computedOutput]
  · rw [referenceSpec.selector_output]
    change movedMemberPositionSelectorOutputXorReference p offset.val
      (selectorOutputWires p) sorted = _
    rw [movedSelector', sortedSelector, computedSelector]
  · rw [referenceSpec.active]
    change sorted (activeWire p) = _
    rw [writerActive', computedActive]
  · intro wire outsideOutput outsideSelector outsideActive
    exact applyColumnEventReferenceAndRestoreWorkCircuit_outside_outputs_restored p slot offset input
      computedSpec.scratch_zero computedSpec.pair_zero computedSpec.moved_clean
      wire outsideOutput outsideSelector outsideActive

/-- sorted writer は全 oracle-work wire を保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_diagonalOracleWork_column
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    BasisAgreeOn (diagonalOracleWorkWires p)
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p) degreeChange input)
      input := by
  intro wire workMember
  apply xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_rowOutput
  · intro outputMember
    exact (List.disjoint_left.mp (columnDiagonalSupport_disjoint_rowOutput p))
      (List.mem_append_right _ workMember) outputMember
  · intro equal
    subst wire
    exact activeWire_not_mem_columnDiagonalSupport p
      (List.mem_append_right _ workMember)

/-- sorted writer は candidate の自然数値関数を保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_qCandidateValue_column
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    qCandidateValue p
        (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
          (by simp [rowOutputWires]) (activeWire p) degreeChange input) =
      qCandidateValue p input := by
  funext word
  unfold qCandidateValue
  apply congrArg littleEndianNat
  apply List.map_congr_left
  intro wire member
  apply xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_diagonalOracleWork_column p
    degreeChange input wire
  apply oracleSliceWire_mem_oracleWork p
    (OracleWorkLayout.canonical p).candidate
  exact candidateWordAt_mem_candidateSlice p word member

/-- sorted writer は moved register を保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_movedWires_column
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (oracleMovedWires p)
        (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
          (by simp [rowOutputWires]) (activeWire p) degreeChange input) =
      readWires (oracleMovedWires p) input := by
  apply List.map_congr_left
  intro wire member
  apply xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_diagonalOracleWork_column p
    degreeChange input wire
  apply oracleSliceWire_mem_oracleWork p
    (OracleWorkLayout.canonical p).moved
  simpa [oracleMovedWires, RegisterSlice.wireList] using member

/-- sorted writer は event branch bit を保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_branch_column
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p) degreeChange input
        (oracleBranchWire p) = input (oracleBranchWire p) := by
  exact xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_diagonalOracleWork_column p
    degreeChange input (oracleBranchWire p)
      (oracleBranchWire_mem_diagonalOracleWorkWires p)

/-- sorted writer は moved-selector が使う一時 work の clean 性を保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_movedSelectorClean_column
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : WriteMovedSelectorSlotClean p input) :
    WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p) degreeChange input) := by
  let output := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
    (by simp [rowOutputWires]) (activeWire p) degreeChange input
  have preserve : ∀ wire ∈ diagonalOracleWorkWires p,
      output wire = input wire :=
    xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_diagonalOracleWork_column p
      degreeChange input
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
        apply preserve wire
        apply oracleSliceWire_mem_oracleWork p
          (OracleWorkLayout.canonical p).compareWork
        simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member
      _ = List.replicate (oracleCompareWorkWires p).length false :=
        clean.compare_zero
  · intro wire member
    change output wire = false
    rw [preserve wire (decoderAndScratchWire_mem_diagonalOracleWorkWires p member)]
    exact clean.scratch_zero wire member
  · change output (oraclePositionWire p) = false
    rw [preserve (oraclePositionWire p)]
    · exact clean.position_zero
    · apply oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).positionMatch
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).positionMatch).ancillaWire _ ∈ _
      simp [RegisterSlice.wireList]
  · change output (oraclePairWire p) = false
    rw [preserve (oraclePairWire p)]
    · exact clean.pair_zero
    · apply oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).pair
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).pair).ancillaWire _ ∈ _
      simp [RegisterSlice.wireList]

/-- clean な output 仕様から active compute 仕様を構成する。 -/
theorem ColumnEventActiveComputedSpec.of_outputClean
    {p : QParameters} {configuration : QConfiguration p}
    {moved : QSite p} {member : moved ∈ configuration.1}
    {offset : Fin 6} {degreeSlot : Fin p.K}
    {computed : JointBasis p.ancillaWidth p.systemWidth}
    (outputDegree : Int.ofNat (degreeSlot.val + 1) +
      columnEventDegreeChange offset = Int.ofNat configuration.1.card)
    (branchTrue : computed (oracleBranchWire p) = true)
    (degreeOneHot : ∀ slot : Fin p.K,
      computed (oracleDegreeWireAt p slot) = decide (slot = degreeSlot))
    (candidateValues : qCandidateValue p computed =
      configurationCandidateValue p configuration)
    (movedWord : readWires (oracleMovedWires p) computed =
      siteWordBits p moved)
    (clean : WriteMovedSelectorSlotClean p computed) :
    ColumnEventActiveComputedSpec p configuration moved member offset degreeSlot
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
  exact xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_movedSelectorClean_column p
    (columnEventDegreeChange offset) computed clean

/-- branch wire は candidate slice 全体の外にある。 -/
theorem columnOracleBranchWire_not_mem_candidateSlice (p : QParameters) :
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

/--
branch 後が tracked clean なら、candidate 生成・変更・sort は branch bit を保存する。
-/
theorem columnEventCandidateUpdateAndSortExecutionTrace_output_branch_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output (oracleBranchWire p) =
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
        (oracleBranchWire p) := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have candidatesClean : EventSortCleanInput p states.afterCandidates := by
    rw [states.candidates_eq]
    exact EventSortCleanInput.of_xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)
      (columnKeyWires_candidateInputLayout p) _ clean
  have modifyClean : EventSortCleanInput p states.afterModify := by
    rw [states.modify_eq]
    exact EventSortCleanInput.of_columnEventModify p slot offset _ candidatesClean
  calc
    states.output (oracleBranchWire p) =
        states.afterModify (oracleBranchWire p) := by
      rw [states.sort_eq]
      exact qBitonicSort_preserves_oracleBranch p states.afterModify
        modifyClean.sort_compare_zero modifyClean.sort_scratch_zero
        modifyClean.sort_history_zero
    _ = states.afterCandidates (oracleBranchWire p) := by
      rw [states.modify_eq]
      exact runBasis_columnEventModify_outside_candidateSlice p slot offset
        states.afterCandidates (oracleBranchWire p)
          (columnOracleBranchWire_not_mem_candidateSlice p)
    _ = states.afterBranch (oracleBranchWire p) := by
      rw [states.candidates_eq]
      exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_oracleBranch p (columnKeyWires p)
        (columnKeyWires_candidateInputLayout p) states.afterBranch

/--
candidate と sort-history の外側にある wire は、column event の suffix 全体で保存される。
-/
theorem columnEventCandidateUpdateAndSortExecutionTrace_output_preserves_outsideCandidateHistories
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideCandidate : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)))
    (outsideHistories : ∀ instruction ∈ qTypedBitonicSchedule p,
      wire ≠ (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) :
    (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output wire =
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch wire := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have candidatesClean : EventSortCleanInput p states.afterCandidates := by
    rw [states.candidates_eq]
    exact EventSortCleanInput.of_xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)
      (columnKeyWires_candidateInputLayout p) _ clean
  have modifyClean : EventSortCleanInput p states.afterModify := by
    rw [states.modify_eq]
    exact EventSortCleanInput.of_columnEventModify p slot offset _ candidatesClean
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
      exact runBasis_columnEventModify_outside_candidateSlice p slot offset
        states.afterCandidates wire outsideCandidate
    _ = states.afterBranch wire := by
      rw [states.candidates_eq]
      exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_outside_candidateSlice p
        (columnKeyWires p) (columnKeyWires_candidateInputLayout p)
        states.afterBranch wire outsideCandidate

/-- candidate より前の oracle slice は column event suffix 全体で保存される。 -/
theorem columnEventCandidateUpdateAndSortExecutionTrace_output_preserves_earlyOracleSlice
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch)
    {width : Nat} (slice : RegisterSlice p.oracleWorkWidth width)
    (beforeCandidate : slice.start + width ≤
      (OracleWorkLayout.canonical p).candidate.start)
    (beforeHistories : slice.start + width ≤
      (OracleWorkLayout.canonical p).sortFlags.start)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ ((QLayout.oracleSlice slice).wireList :
      List (Wire p.ancillaWidth p.systemWidth))) :
    (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output wire =
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch wire := by
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
  apply columnEventCandidateUpdateAndSortExecutionTrace_output_preserves_outsideCandidateHistories p
    slot offset input clean wire
  · intro candidateMember
    exact (List.disjoint_left.mp candidateDisjoint) member candidateMember
  · intro instruction instructionMember equal
    apply (List.disjoint_left.mp historyDisjoint) member
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history, equal.symm⟩

/-- column event suffix は moved register を保存する。 -/
theorem columnEventCandidateUpdateAndSortExecutionTrace_output_movedWires_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    readWires (oracleMovedWires p)
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output =
      readWires (oracleMovedWires p)
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch := by
  apply List.map_congr_left
  intro wire member
  apply columnEventCandidateUpdateAndSortExecutionTrace_output_preserves_earlyOracleSlice p slot offset
    input clean (OracleWorkLayout.canonical p).moved
  · simp [OracleWorkLayout.canonical]
  · simp [OracleWorkLayout.canonical]
  · simpa [oracleMovedWires, RegisterSlice.wireList] using member

/-- column event suffix は persistent degree one-hot register を保存する。 -/
theorem columnEventCandidateUpdateAndSortExecutionTrace_output_degree_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch)
    (degreeSlot : Fin p.K) :
    (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
        (oracleDegreeWireAt p degreeSlot) =
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
        (oracleDegreeWireAt p degreeSlot) := by
  apply columnEventCandidateUpdateAndSortExecutionTrace_output_preserves_earlyOracleSlice p slot offset
    input clean (OracleWorkLayout.canonical p).degree
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [oracleDegreeWireAt, RegisterSlice.wireList]

/-- branch 後の事実と sort 後 candidate 仕様から active compute 仕様を構成する。 -/
theorem ColumnEventActiveComputedSpec.of_afterBranch
    {p : QParameters} {configuration : QConfiguration p}
    {moved : QSite p} {member : moved ∈ configuration.1}
    {offset : Fin 6} {degreeSlot slot : Fin p.K}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (outputDegree : Int.ofNat (degreeSlot.val + 1) +
      columnEventDegreeChange offset = Int.ofNat configuration.1.card)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch)
    (branchTrue : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleBranchWire p) = true)
    (degreeOneHot : ∀ current : Fin p.K,
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
        (oracleDegreeWireAt p current) = decide (current = degreeSlot))
    (candidateValues : qCandidateValue p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output =
        configurationCandidateValue p configuration)
    (movedWord : readWires (oracleMovedWires p)
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch =
        siteWordBits p moved) :
    ColumnEventActiveComputedSpec p configuration moved member offset degreeSlot
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output := by
  apply ColumnEventActiveComputedSpec.of_outputClean outputDegree
  · exact (columnEventCandidateUpdateAndSortExecutionTrace_output_branch_of_afterBranch p slot offset
      input clean).trans branchTrue
  · intro current
    exact (columnEventCandidateUpdateAndSortExecutionTrace_output_degree_of_afterBranch p slot offset input
      clean current).trans (degreeOneHot current)
  · exact candidateValues
  · exact (columnEventCandidateUpdateAndSortExecutionTrace_output_movedWires_of_afterBranch p slot
      offset input clean).trans movedWord
  · exact columnEventCandidateUpdateAndSortExecutionTrace_output_clean_of_afterBranch p slot offset
      input clean

/--
replacement event の candidate 生成・置換・bitonic sort を合成すると、sort 後の候補値は
更新配置の canonical 値関数に一致する。
-/
theorem columnEventCandidateUpdateAndSortExecutionTrace_replacement_candidateValues
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (noCollision : moveSite source direction ∉ configuration.1.erase source)
    (slot : Fin p.K) (offset : Fin 6)
    (replacement : offset.val % 2 ≠ 1)
    (active : slot.val < configuration.1.card)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration (moveSite source direction)
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates)
    (valuesBefore : qCandidateValue p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates =
        configurationCandidateValue p configuration)
    (branchTrue : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleBranchWire p) = true)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    qCandidateValue p (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output =
      configurationCandidateValue p
        (updateConfiguration configuration (source, direction)) := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have candidatesBranch : states.afterCandidates (oracleBranchWire p) = true := by
    calc
      states.afterCandidates (oracleBranchWire p) =
          states.afterBranch (oracleBranchWire p) := by
        rw [states.candidates_eq]
        exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_oracleBranch p (columnKeyWires p)
          (columnKeyWires_candidateInputLayout p) states.afterBranch
      _ = true := branchTrue
  have modifyClean : EventSortCleanInput p states.afterModify :=
    columnEventCandidateUpdateAndSortExecutionTrace_afterModify_clean_of_afterBranch p slot offset
      input clean
  rw [states.sort_eq, states.modify_eq]
  apply columnEventModify_replacement_sort_correct configuration source member
    direction noCollision slot active sourceAt offset replacement
      states.afterCandidates specification valuesBefore candidatesBranch
  · simpa [states.modify_eq] using modifyClean.sort_compare_zero
  · intro wire wireMember
    simpa [states.modify_eq] using modifyClean.sort_scratch_zero wire wireMember
  · intro instruction instructionMember
    simpa [states.modify_eq] using modifyClean.sort_history_zero instruction
      instructionMember

/--
collision event の candidate 生成・削除・bitonic sort を合成すると、sort 後の候補値は
更新配置の canonical 値関数に一致する。
-/
theorem columnEventCandidateUpdateAndSortExecutionTrace_collision_candidateValues
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (physicalCollision : moveSite source direction ∈
      configuration.1.erase source)
    (slot : Fin p.K) (offset : Fin 6)
    (collision : offset.val % 2 = 1)
    (directionAt : selectorDirection (selectorOfSlotOffset slot offset) = direction)
    (active : slot.val < configuration.1.card)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration (moveSite source direction)
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates)
    (valuesBefore : qCandidateValue p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates =
        configurationCandidateValue p configuration)
    (branchTrue : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleBranchWire p) = true)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    qCandidateValue p (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output =
      configurationCandidateValue p
        (updateConfiguration configuration (source, direction)) := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  have candidatesBranch : states.afterCandidates (oracleBranchWire p) = true := by
    calc
      states.afterCandidates (oracleBranchWire p) =
          states.afterBranch (oracleBranchWire p) := by
        rw [states.candidates_eq]
        exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_oracleBranch p (columnKeyWires p)
          (columnKeyWires_candidateInputLayout p) states.afterBranch
      _ = true := branchTrue
  have modifyClean : EventSortCleanInput p states.afterModify :=
    columnEventCandidateUpdateAndSortExecutionTrace_afterModify_clean_of_afterBranch p slot offset
      input clean
  rw [states.sort_eq, states.modify_eq]
  apply columnEventModify_collision_sort_correct configuration source member
    direction physicalCollision slot active sourceAt offset collision directionAt
      states.afterCandidates specification valuesBefore candidatesBranch
  · simpa [states.modify_eq] using modifyClean.sort_compare_zero
  · intro wire wireMember
    simpa [states.modify_eq] using modifyClean.sort_scratch_zero wire wireMember
  · intro instruction instructionMember
    simpa [states.modify_eq] using modifyClean.sort_history_zero instruction
      instructionMember

/--
branch 計算後が tracked clean かつ branch=false なら、column event C-U-U 全体は厳密な恒等
作用である。selector 不一致・padding・illegal・rep/coll 不一致をこの API へ帰着できる。
-/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch)
    (branchFalse : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleBranchWire p) = false) :
    (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  have outputClean := columnEventCandidateUpdateAndSortExecutionTrace_output_clean_of_afterBranch p
    slot offset input clean
  apply runBasis_applyColumnEventReferenceAndRestoreWorkCircuit_identity_of_computed_branch_false p slot
    offset input outputClean.scratch_zero outputClean.pair_zero outputClean
  rw [← columnEventCandidateUpdateAndSortExecutionTrace_output]
  exact (columnEventCandidateUpdateAndSortExecutionTrace_output_branch_of_afterBranch p slot offset input
    clean).trans branchFalse

/--
合法な event selector に対する columnReference の row selector を、更新配置中の moved site
の canonical slot として明示する。
-/
theorem columnReference_eventSlot_active_exact
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (eventRange : 2 ≤ offset.val)
    (branchCorrect :
      (decide (moveSite (configuration.siteAt ⟨slot.val, active⟩)
          (selectorDirection (selectorOfSlotOffset slot offset)) ∈
        configuration.1.erase
          (configuration.siteAt ⟨slot.val, active⟩)) : Bool) =
        selectorRequestsCollision (selectorOfSlotOffset slot offset)) :
    let source := configuration.siteAt ⟨slot.val, active⟩
    let direction := selectorDirection (selectorOfSlotOffset slot offset)
    let output := updateConfiguration configuration (source, direction)
    let moved := moveSite source direction
    let movedMember : moved ∈ output.1 :=
      moveSite_mem_updateConfiguration configuration (source, direction)
        ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
    columnReference configuration (selectorOfSlotOffset slot offset) =
      some ⟨output,
        selectorOfSlotOffset (slotOfMember output moved movedMember) offset,
        false⟩ := by
  dsimp only
  let source := configuration.siteAt ⟨slot.val, active⟩
  let sourceMember : source ∈ configuration.1 :=
    ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
  have selected : configurationSlot? configuration
      (selectorSlot (selectorOfSlotOffset slot offset)) =
        some ⟨source, sourceMember⟩ := by
    rcases configurationSlot_eq_some_siteAt configuration slot active with
      ⟨member, selectedAt⟩
    have proofEqual : member = sourceMember := Subsingleton.elim _ _
    subst member
    simpa [source] using selectedAt
  unfold columnReference
  rw [selected]
  have notDiagonal : ¬(selectorOffset
      (selectorOfSlotOffset slot offset)).val < 2 := by
    simp
    omega
  simp only [notDiagonal, dite_false]
  rw [dif_pos branchCorrect]
  dsimp [source]
  simp

/-- columnReference の外部 XOR と内部復元を直接表す分岐仕様。 -/
structure ColumnReferenceBranchResult (p : QParameters)
    (reference : ColumnReferenceResult p)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- row-output は参照結果の配置を delimiter 符号化して XOR する。 -/
  row_output : readWires (rowOutputWires p) output =
    List.zipWith
      (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
      (registerBitList (delimiterEncoding reference.output))
      (readWires (rowOutputWires p) input)
  /-- selector-output は参照結果の row selector を XOR する。 -/
  selector_output : readWires (selectorOutputWires p) output =
    controlledXorConstantBits true reference.rowSelector.val 0
      (readWires (selectorOutputWires p) input)
  /-- negative bit は参照結果の符号 bit を XOR する。 -/
  negative : output (negativeWire p) =
    if reference.negative then !(input (negativeWire p))
    else input (negativeWire p)
  /-- active bit は受理時に一回反転する。 -/
  active : output (activeWire p) = !(input (activeWire p))
  /-- column event compute support は入力へ復元される。 -/
  support_restored : BasisAgreeOn (columnEventCandidateUpdateAndSortSupport p) output input
  /-- 四つの外部出力以外の wire も入力へ復元される。 -/
  outside_restored : ∀ wire,
    wire ∉ rowOutputWires p → wire ∉ selectorOutputWires p →
      wire ≠ negativeWire p → wire ≠ activeWire p →
      output wire = input wire

/-- active event 分岐仕様を、その columnReference 結果の直接仕様へ変換する。 -/
theorem ColumnEventActiveBranchResult.toColumnReference
    {p : QParameters} {configuration : QConfiguration p}
    {moved : QSite p} {member : moved ∈ configuration.1}
    {offset : Fin 6}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (result : ColumnEventActiveBranchResult p configuration moved member offset
      input output)
    (reference : ColumnReferenceResult p)
    (outputEq : reference.output = configuration)
    (selectorEq : reference.rowSelector =
      selectorOfSlotOffset (slotOfMember configuration moved member) offset)
    (negativeFalse : reference.negative = false) :
    ColumnReferenceBranchResult p reference input output := by
  refine {
    row_output := ?_
    selector_output := ?_
    negative := ?_
    active := result.active
    support_restored := result.support_restored
    outside_restored := ?_ }
  · simpa [outputEq] using result.row_output
  · rw [selectorEq]
    simpa [selectorOfSlotOffset] using result.selector_output
  · rw [negativeFalse]
    simp only [Bool.false_eq_true, if_false]
    exact result.outside_restored (negativeWire p)
      (negativeWire_not_mem_rowOutputWires p)
      (negativeWire_not_mem_selectorOutputWires p)
      (negativeWire_ne_activeWire p)
  · intro wire outsideOutput outsideSelector outsideNegative outsideActive
    exact result.outside_restored wire outsideOutput outsideSelector outsideActive

/--
active compute 仕様だけから writer の delimiter/active と moved-selector の selector XOR を
すべて導出し、actual column event 分岐の完全な外部仕様を得る。
-/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_active_of_computedSpec
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (configuration : QConfiguration p) (moved : QSite p)
    (member : moved ∈ configuration.1) (degreeSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (computedSpec : ColumnEventActiveComputedSpec p configuration moved member
      offset degreeSlot (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output) :
    ColumnEventActiveBranchResult p configuration moved member offset input
      ((applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  let computed := (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
    (by simp [rowOutputWires]) (activeWire p)
    (columnEventDegreeChange offset) computed
  have writerEq :
      sorted =
        writeSortedUseReference p
          (canonicalSortedOutputWires p .rowOutput)
          (canonicalSortedOutputWires_length p .rowOutput)
          (canonicalSortedOutputActive p .rowOutput)
          configuration.1.card configuration.2.2 true computed := by
    dsimp [sorted]
    simpa [canonicalSortedOutputWires, canonicalSortedOutputActive] using
      xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_eq_configuration_use p .rowOutput configuration
        degreeSlot (columnEventDegreeChange offset) computed
          computedSpec.output_degree computedSpec.branch_true
          computedSpec.degree_oneHot
  have sortedCandidates : qCandidateValue p sorted =
      configurationCandidateValue p configuration := by
    rw [xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_qCandidateValue_column]
    exact computedSpec.candidate_values
  have sortedMoved : readWires (oracleMovedWires p) sorted =
      siteWordBits p moved := by
    rw [xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_movedWires_column]
    exact computedSpec.moved_word
  have sortedBranch : sorted (oracleBranchWire p) = true := by
    dsimp [sorted]
    rw [xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_preserves_branch_column]
    exact computedSpec.branch_true
  have writerOutputRef : readWires (rowOutputWires p) sorted =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (registerBitList (delimiterEncoding configuration))
        (readWires (rowOutputWires p) computed) := by
    rw [writerEq]
    simpa [canonicalSortedOutputWires] using
      writeSortedUseReference_configuration_bits_canonical p .rowOutput
        configuration computed computedSpec.candidate_values
  have writerActiveRef : sorted (activeWire p) = !(computed (activeWire p)) := by
    rw [writerEq]
    simpa [canonicalSortedOutputActive] using
      writeSortedUseReference_configuration_active_canonical p .rowOutput
        configuration computed
  have movedSelector :
      movedMemberPositionSelectorOutputXorReference p offset.val (selectorOutputWires p) sorted =
        controlledXorConstantBits true
          (6 * (slotOfMember configuration moved member).val + offset.val) 0
          (readWires (selectorOutputWires p) sorted) :=
    xorMovedMemberPositionIntoSelectorOutputCircuitBitsReference_configuration p configuration moved member
      offset.val (selectorOutputWires p) sorted sortedBranch sortedCandidates
        sortedMoved
  apply applyColumnEventReferenceAndRestoreWorkCircuit_active_of_writer_references p slot offset
    configuration moved member degreeSlot input computedSpec
  · simpa [sorted, computed] using writerOutputRef
  · simpa [sorted, computed] using writerActiveRef
  · simpa [sorted, computed] using movedSelector

/-- column oracle の分岐列を selector 全域の型安全な写像として書き直す。 -/
theorem columnOracleBranchList_eq_finRange_map (p : QParameters) :
    columnOracleBranchList p =
      (List.finRange p.selectorCount).map (dispatchColumnSelectorToDiagonalOrEventCircuit p) := by
  rw [columnOracleBranchList_eq_ofFn]
  apply List.ext_get
  · simp
  · intro index leftBound rightBound
    simp

/--
唯一の active selector 分岐だけが作用し、その前後の分岐が恒等なら、全 column 分岐列は
active 分岐と厳密に同じ基底状態を返す。
-/
theorem runBasis_columnOracleBranchSequence_eq_active
    (p : QParameters) (active : QSelector p)
    (input output : JointBasis p.ancillaWidth p.systemWidth)
    (inactiveInput : ∀ selector : QSelector p, selector ≠ active →
      (dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation input = input)
    (activeResult : (dispatchColumnSelectorToDiagonalOrEventCircuit p active).runBasis
      reversibleGatePermutation input = output)
    (inactiveOutput : ∀ selector : QSelector p, selector ≠ active →
      (dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation output = output) :
    (Circuit.sequence (columnOracleBranchList p)).runBasis
        reversibleGatePermutation input = output := by
  rw [columnOracleBranchList_eq_finRange_map]
  apply runBasis_sequence_map_eq_of_unique_active reversibleGatePermutation
    (List.finRange p.selectorCount) (dispatchColumnSelectorToDiagonalOrEventCircuit p) active input output
  · exact List.nodup_finRange p.selectorCount
  · exact List.mem_finRange active
  · intro selector _ different
    exact inactiveInput selector different
  · exact activeResult
  · intro selector _ different
    exact inactiveOutput selector different

/-- 全 selector 分岐が同じ状態を固定するなら、column 分岐列全体もその状態を固定する。 -/
theorem runBasis_columnOracleBranchSequence_eq_input
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (eachIdentity : ∀ selector : QSelector p,
      (dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation input = input) :
    (Circuit.sequence (columnOracleBranchList p)).runBasis
        reversibleGatePermutation input = input := by
  apply Circuit.runBasis_sequence_eq_input_of_each
  intro circuit member
  rw [columnOracleBranchList_eq_finRange_map] at member
  obtain ⟨selector, _, rfl⟩ := List.mem_map.mp member
  exact eachIdentity selector

/-- column oracle の最外 persistent compute が触れる canonical support。 -/
def columnOraclePersistentSupport (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  columnKeyWires p ++ diagonalOracleWorkWires p

/-- column persistent support は column event compute support に含まれる。 -/
theorem columnOraclePersistentSupport_subset_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) :
    ∀ wire ∈ columnOraclePersistentSupport p,
      wire ∈ columnEventCandidateUpdateAndSortSupport p := by
  intro wire member
  rcases List.mem_append.mp member with keyMember | workMember
  · exact List.mem_append_left _ (List.mem_append_right _ keyMember)
  · exact List.mem_append_right _ workMember

/-- column persistent support は row-output register と交わらない。 -/
theorem columnOraclePersistentSupport_disjoint_rowOutput (p : QParameters) :
    (columnOraclePersistentSupport p).Disjoint (rowOutputWires p) := by
  rw [List.disjoint_left]
  intro wire supportMember outputMember
  exact (List.disjoint_left.mp (columnEventCandidateUpdateAndSortSupport_disjoint_rowOutput p))
    (columnOraclePersistentSupport_subset_columnEventCandidateUpdateAndSortSupport p wire
      supportMember) outputMember

/-- column persistent support は selector-output register と交わらない。 -/
theorem columnOraclePersistentSupport_disjoint_selectorOutput (p : QParameters) :
    (columnOraclePersistentSupport p).Disjoint (selectorOutputWires p) := by
  rw [List.disjoint_left]
  intro wire supportMember outputMember
  exact (List.disjoint_left.mp
    (columnEventCandidateUpdateAndSortSupport_disjoint_selectorOutput p))
      (columnOraclePersistentSupport_subset_columnEventCandidateUpdateAndSortSupport p wire
        supportMember) outputMember

/-- negative 出力 bit は column event compute support に含まれない。 -/
theorem negativeWire_not_mem_columnEventCandidateUpdateAndSortSupport (p : QParameters) :
    negativeWire p ∉ columnEventCandidateUpdateAndSortSupport p := by
  intro supportMember
  rcases List.mem_append.mp supportMember with prefixMember | workMember
  · rcases List.mem_append.mp prefixMember with selectorMember | keyMember
    · exact negativeWire_not_mem_columnDiagonalSupport p
        (List.mem_append_left _ selectorMember)
    · let key := (QLayout.canonical p).columnKey
      let negative := (QLayout.canonical p).negative
      have separated :
          (key.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
            (negative.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
        key.wireList_disjoint_of_end_le_start negative
          (by simp [key, negative, QLayout.canonical]; omega)
      have negativeMember : negativeWire p ∈
          (negative.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
        change negative.ancillaWire 0 ∈
          (negative.wireList : List (Wire p.ancillaWidth p.systemWidth))
        rw [RegisterSlice.wireList]
        exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
      exact (List.disjoint_left.mp separated)
        (by simpa [columnKeyWires, columnKeyWire, key,
          RegisterSlice.wireList] using keyMember) negativeMember
  · exact negativeWire_not_mem_columnDiagonalSupport p
      (List.mem_append_right _ workMember)

/-- negative 出力 bit は column persistent support に含まれない。 -/
theorem negativeWire_not_mem_columnOraclePersistentSupport (p : QParameters) :
    negativeWire p ∉ columnOraclePersistentSupport p := by
  intro member
  exact negativeWire_not_mem_columnEventCandidateUpdateAndSortSupport p
    (columnOraclePersistentSupport_subset_columnEventCandidateUpdateAndSortSupport p _ member)

/-- active 出力 bit は column persistent support に含まれない。 -/
theorem activeWire_not_mem_columnOraclePersistentSupport (p : QParameters) :
    activeWire p ∉ columnOraclePersistentSupport p := by
  intro member
  exact activeWire_not_mem_columnEventCandidateUpdateAndSortSupport p
    (columnOraclePersistentSupport_subset_columnEventCandidateUpdateAndSortSupport p _ member)

/--
全 column 分岐列が persistent support を保存するなら、最外 compute--use--uncompute は
その support を入力へ復元する。
-/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_eq_restorePersistentSupport
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchesPreserve : BasisAgreeOn (columnOraclePersistentSupport p)
      ((Circuit.sequence (columnOracleBranchList p)).runBasis
        reversibleGatePermutation
        ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
          reversibleGatePermutation input))
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input)) :
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input =
      restoreSupport (columnOraclePersistentSupport p) input
        ((Circuit.sequence (columnOracleBranchList p)).runBasis
          reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
            reversibleGatePermutation input)) := by
  rw [applyColumnOracleReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
  exact Circuit.computeUseUncompute_local_clean
    (columnOraclePersistentSupport p)
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false)
    (Circuit.sequence (columnOracleBranchList p)) input
    (by simpa [columnOraclePersistentSupport] using
      columnOraclePersistentCompute_usesOnly p)
    branchesPreserve

/-- 分岐列の厳密な出力と support 保存から、column oracle 全体の復元式を得る。 -/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_eq_restore_of_branchResult
    (p : QParameters) (input branchOutput :
      JointBasis p.ancillaWidth p.systemWidth)
    (sequenceResult :
      (Circuit.sequence (columnOracleBranchList p)).runBasis
          reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
            reversibleGatePermutation input) = branchOutput)
    (persistentPreserved : BasisAgreeOn (columnOraclePersistentSupport p)
      branchOutput
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input)) :
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input =
      restoreSupport (columnOraclePersistentSupport p) input branchOutput := by
  have branchesPreserve : BasisAgreeOn (columnOraclePersistentSupport p)
      ((Circuit.sequence (columnOracleBranchList p)).runBasis
        reversibleGatePermutation
        ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
          reversibleGatePermutation input))
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input) := by
    rw [sequenceResult]
    exact persistentPreserved
  rw [applyColumnOracleReferenceAndRestoreWorkCircuit_eq_restorePersistentSupport p input
    branchesPreserve, sequenceResult]

/--
分岐列が `columnReference` の XOR 仕様を満たすなら、最外 persistent uncompute 後も
同じ外部仕様を満たし、全 work を入力へ戻す。
-/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_correct_of_branchResult
    (p : QParameters) (reference : ColumnReferenceResult p)
    (input branchOutput : JointBasis p.ancillaWidth p.systemWidth)
    (sequenceResult :
      (Circuit.sequence (columnOracleBranchList p)).runBasis
          reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
            reversibleGatePermutation input) = branchOutput)
    (branchResult : ColumnReferenceBranchResult p reference
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input) branchOutput) :
    ColumnReferenceBranchResult p reference input
      ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input) := by
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
    reversibleGatePermutation input
  let output := (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
    reversibleGatePermutation input
  have persistentUses : circuitUsesOnly (columnOraclePersistentSupport p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false) := by
    simpa [columnOraclePersistentSupport] using
      columnOraclePersistentCompute_usesOnly p
  have persistentRowOutput : readWires (rowOutputWires p) persistent =
      readWires (rowOutputWires p) input := by
    exact readWires_runBasis_of_usesOnly_disjoint
      (columnOraclePersistentSupport p) (rowOutputWires p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false) input persistentUses
      (columnOraclePersistentSupport_disjoint_rowOutput p)
  have persistentSelectorOutput : readWires (selectorOutputWires p) persistent =
      readWires (selectorOutputWires p) input := by
    exact readWires_runBasis_of_usesOnly_disjoint
      (columnOraclePersistentSupport p) (selectorOutputWires p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false) input persistentUses
      (columnOraclePersistentSupport_disjoint_selectorOutput p)
  have persistentNegative : persistent (negativeWire p) = input (negativeWire p) := by
    exact Circuit.runBasis_outside_of_usesOnly (columnOraclePersistentSupport p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false) persistentUses input
      (negativeWire p) (negativeWire_not_mem_columnOraclePersistentSupport p)
  have persistentActive : persistent (activeWire p) = input (activeWire p) := by
    exact Circuit.runBasis_outside_of_usesOnly (columnOraclePersistentSupport p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false) persistentUses input
      (activeWire p) (activeWire_not_mem_columnOraclePersistentSupport p)
  have persistentPreserved : BasisAgreeOn (columnOraclePersistentSupport p)
      branchOutput persistent := by
    intro wire member
    exact branchResult.support_restored wire
      (columnOraclePersistentSupport_subset_columnEventCandidateUpdateAndSortSupport p wire member)
  have outputEq : output =
      restoreSupport (columnOraclePersistentSupport p) input branchOutput := by
    dsimp [output, persistent] at sequenceResult ⊢
    exact applyColumnOracleReferenceAndRestoreWorkCircuit_eq_restore_of_branchResult p input
      branchOutput sequenceResult persistentPreserved
  have rowOutputFinal : readWires (rowOutputWires p) output =
      readWires (rowOutputWires p) branchOutput := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (columnOraclePersistentSupport p) input branchOutput
      wire (fun supportMember =>
        (List.disjoint_left.mp (columnOraclePersistentSupport_disjoint_rowOutput p))
          supportMember member)
  have selectorOutputFinal : readWires (selectorOutputWires p) output =
      readWires (selectorOutputWires p) branchOutput := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (columnOraclePersistentSupport p) input branchOutput
      wire (fun supportMember =>
        (List.disjoint_left.mp
          (columnOraclePersistentSupport_disjoint_selectorOutput p))
            supportMember member)
  have negativeFinal : output (negativeWire p) = branchOutput (negativeWire p) := by
    rw [outputEq]
    exact restoreSupport_outside (columnOraclePersistentSupport p) input branchOutput
      (negativeWire p) (negativeWire_not_mem_columnOraclePersistentSupport p)
  have activeFinal : output (activeWire p) = branchOutput (activeWire p) := by
    rw [outputEq]
    exact restoreSupport_outside (columnOraclePersistentSupport p) input branchOutput
      (activeWire p) (activeWire_not_mem_columnOraclePersistentSupport p)
  change ColumnReferenceBranchResult p reference input output
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rowOutputFinal, branchResult.row_output, persistentRowOutput]
  · rw [selectorOutputFinal, branchResult.selector_output,
      persistentSelectorOutput]
  · rw [negativeFinal, branchResult.negative]
    split
    · exact congrArg (fun bit => !bit) persistentNegative
    · exact persistentNegative
  · rw [activeFinal, branchResult.active]
    exact congrArg (fun bit => !bit) persistentActive
  · intro wire supportMember
    by_cases persistentMember : wire ∈ columnOraclePersistentSupport p
    · rw [outputEq]
      exact restoreSupport_agrees_input (columnOraclePersistentSupport p) input
        branchOutput wire persistentMember
    · rw [outputEq, restoreSupport_outside (columnOraclePersistentSupport p) input
        branchOutput wire persistentMember]
      rw [branchResult.support_restored wire supportMember]
      exact Circuit.runBasis_outside_of_usesOnly (columnOraclePersistentSupport p)
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false) persistentUses input wire
        persistentMember
  · intro wire outsideOutput outsideSelector outsideNegative outsideActive
    by_cases persistentMember : wire ∈ columnOraclePersistentSupport p
    · rw [outputEq]
      exact restoreSupport_agrees_input (columnOraclePersistentSupport p) input
        branchOutput wire persistentMember
    · rw [outputEq, restoreSupport_outside (columnOraclePersistentSupport p) input
        branchOutput wire persistentMember]
      rw [branchResult.outside_restored wire outsideOutput outsideSelector
        outsideNegative outsideActive]
      exact Circuit.runBasis_outside_of_usesOnly (columnOraclePersistentSupport p)
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false) persistentUses input wire
        persistentMember

/-- 唯一の active branch の仕様を column oracle 全体へ持ち上げる。 -/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_correct_of_unique_active
    (p : QParameters) (reference : ColumnReferenceResult p)
    (active : QSelector p)
    (input branchOutput : JointBasis p.ancillaWidth p.systemWidth)
    (inactiveInput : ∀ selector : QSelector p, selector ≠ active →
      (dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
            reversibleGatePermutation input) =
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
          reversibleGatePermutation input)
    (activeResult : (dispatchColumnSelectorToDiagonalOrEventCircuit p active).runBasis
        reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
            reversibleGatePermutation input) = branchOutput)
    (inactiveOutput : ∀ selector : QSelector p, selector ≠ active →
      (dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation
          branchOutput = branchOutput)
    (branchResult : ColumnReferenceBranchResult p reference
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input) branchOutput) :
    ColumnReferenceBranchResult p reference input
      ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input) := by
  have sequenceResult :
      (Circuit.sequence (columnOracleBranchList p)).runBasis
          reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
            reversibleGatePermutation input) = branchOutput := by
    exact runBasis_columnOracleBranchSequence_eq_active p active _ branchOutput
      inactiveInput activeResult inactiveOutput
  exact applyColumnOracleReferenceAndRestoreWorkCircuit_correct_of_branchResult p reference input
    branchOutput sequenceResult branchResult

/-- 全分岐が persistent 状態を固定する場合、column oracle 全体は入力を固定する。 -/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_eq_input_of_eachBranch
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (eachIdentity : ∀ selector : QSelector p,
      (dispatchColumnSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation
          ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
            reversibleGatePermutation input) =
        (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
          reversibleGatePermutation input) :
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input = input := by
  rw [applyColumnOracleReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
  apply Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl)
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false)
    (Circuit.sequence (columnOracleBranchList p)) input input
  exact runBasis_columnOracleBranchSequence_eq_input p _ eachIdentity

end ReversibleCircuit

end ProbabilityGeneratorQProof
