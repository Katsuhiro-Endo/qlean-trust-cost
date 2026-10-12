import QLean.Generator.Implementation.QOracleDiagonalBranchCorrectness
import QLean.Generator.Implementation.QOracleEventReferenceBridge
import QLean.Generator.Implementation.QBitonicCircuitCorrectness
import QLean.Generator.Implementation.ReversibleLocality
import QLean.Generator.Implementation.QSortedCandidateBridge
import QLean.Generator.Implementation.QEventMembershipBridge
import QLean.Generator.Implementation.QEventLayoutBridge
import QLean.Generator.Implementation.QConfigurationCandidateCount
import QLean.Generator.Implementation.FiniteValueCountUpdate
import QLean.Generator.Implementation.QWriteMovedSelectorLayoutCanonical
import QLean.Generator.Implementation.ReversibleLogicSharedCoreReadoutAdapter

/-!
# Q oracle の column event 分岐

column oracle の `6i+2` から `6i+5` までの event 分岐を、任意の正の
`q,K` について計算基底作用だけで検証する。候補列の整列では巨大行列も全基底列挙も
用いず、有限列の昇順性と各値の出現個数だけを使う。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 一degreeの純粋sorted出力作用はcanonical外部出力以外を保存する。 -/
theorem writeSortedDegreeReference_outside_canonical_local
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideOutput : wire ∉ canonicalSortedOutputWires p kind)
    (outsideActive : wire ≠ canonicalSortedOutputActive p kind) :
    writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeSlot degreeChange input wire =
      input wire := by
  unfold writeSortedDegreeReference
  split
  · apply writeSortedUseReference_outside p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) _ _ _ input wire
      outsideOutput outsideActive
  · rfl

/-- decoder AND scratchはsorted pair計算supportに含まれる。 -/
theorem decoderAndScratchWire_mem_writeSortedPairSupport_local
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ decoderAndScratchWires p) :
    wire ∈ writeSortedPairSupport p := by
  have andMember : wire ∈
      ((QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [decoderAndScratchWires, oracleAndWorkWires,
      QParameters.andWorkWidth, RegisterSlice.wireList] using
        List.mem_of_mem_drop member
  simp [writeSortedPairSupport, andMember]

/--
任意のdegree slot部分列について、canonical sorted出力の実回路foldは純粋参照foldに
一致し、帰納に必要なpair・AND scratchのclean性を保持する。
-/
theorem runBasis_writeSortedDegreeList_canonical_local
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeChange : Int) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      (∀ wire ∈ decoderAndScratchWires p, input wire = false) →
      input (oraclePairWire p) = false →
      slots.foldl (fun state degreeSlot =>
          (writeSortedDegreeCircuit p (canonicalSortedOutputWires p kind)
            (canonicalSortedOutputWires_length p kind)
            (canonicalSortedOutputActive p kind) degreeChange degreeSlot).runBasis
              reversibleGatePermutation state) input =
        slots.foldl (fun state degreeSlot =>
          writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
            (canonicalSortedOutputWires_length p kind)
            (canonicalSortedOutputActive p kind) degreeSlot degreeChange state) input
  | [], _, _, _ => rfl
  | degreeSlot :: slots, input, scratchZero, pairZero => by
      simp only [List.foldl_cons]
      rw [runBasis_writeSortedDegreeCircuit_canonical p kind degreeSlot
        degreeChange input scratchZero pairZero]
      let next := writeSortedDegreeReference p
        (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeSlot degreeChange input
      apply runBasis_writeSortedDegreeList_canonical_local p kind degreeChange
        slots next
      · intro wire member
        dsimp only [next]
        rw [writeSortedDegreeReference_outside_canonical_local p kind degreeSlot
          degreeChange input wire]
        · exact scratchZero wire member
        · intro outputMember
          exact (List.disjoint_left.mp
            (canonicalSortedOutputWires_disjoint_writeSortedPairSupport p kind))
              outputMember
              (decoderAndScratchWire_mem_writeSortedPairSupport_local p member)
        · intro equal
          subst wire
          exact (canonicalSortedOutputActive_not_mem_writeSortedPairSupport p kind)
            (decoderAndScratchWire_mem_writeSortedPairSupport_local p member)
      ·
        dsimp only [next]
        rw [writeSortedDegreeReference_outside_canonical_local p kind degreeSlot
          degreeChange input (oraclePairWire p)]
        · exact pairZero
        · intro outputMember
          exact (List.disjoint_left.mp
            (canonicalSortedOutputWires_disjoint_writeSortedPairSupport p kind))
              outputMember (oraclePairWire_mem_writeSortedPairSupport p)
        · intro equal
          exact (canonicalSortedOutputActive_not_mem_writeSortedPairSupport p kind)
            (equal ▸ oraclePairWire_mem_writeSortedPairSupport p)

/-- canonical sorted出力正本全体は、全degree有限foldの純粋参照作用に一致する。 -/
theorem runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical_local
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false) :
    (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) degreeChange).runBasis
        reversibleGatePermutation input =
      SortedCandidatesDelimiterOutputXorSpec p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeChange input := by
  rw [runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_degreeFold]
  exact runBasis_writeSortedDegreeList_canonical_local p kind degreeChange
    (List.finRange p.K) input scratchZero pairZero

/-- column eventでincrementする`q` bit座標slice。offset 2,3は下位、4,5は上位である。 -/
def columnEventCoordinate (p : QParameters) (offset : Fin 6) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  if 4 ≤ offset.val then
    (oracleMovedWires p).drop p.q |>.take p.q
  else
    (oracleMovedWires p).take p.q

/-- source wordのXOR copyと座標incrementを合成したcolumn eventの移動先計算部。 -/
def columnEventMovedCircuit (p : QParameters) (slot : Fin p.K)
    (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .seq (xorCopy (registerWordAt p (columnKeyWires p) slot)
      (oracleMovedWires p))
    (incrementWordMod2PowInPlaceCircuit (columnEventCoordinate p offset)
      (decoderAndScratchWires p))

/-- column event移動先計算に必要な静的配置条件。 -/
structure ColumnEventMoveLayout (p : QParameters) (slot : Fin p.K)
    (offset : Fin 6) : Prop where
  /-- sourceとmovedは同じ`2q` bit幅である。 -/
  same_length :
    (registerWordAt p (columnKeyWires p) slot).length =
      (oracleMovedWires p).length
  /-- source registerとmoved workは交わらない。 -/
  source_disjoint_moved :
    (registerWordAt p (columnKeyWires p) slot).Disjoint
      (oracleMovedWires p)
  /-- source registerには重複がない。 -/
  source_nodup : (registerWordAt p (columnKeyWires p) slot).Nodup
  /-- moved registerには重複がない。 -/
  moved_nodup : (oracleMovedWires p).Nodup
  /-- increment座標とAND scratchには重複がない。 -/
  coordinate_scratch_nodup :
    (columnEventCoordinate p offset ++ decoderAndScratchWires p).Nodup
  /-- increment回路に十分なscratchがある。 -/
  enough_scratch :
    (columnEventCoordinate p offset).length ≤
      (decoderAndScratchWires p).length + 2
  /-- moved全体とAND scratchは交わらない。 -/
  moved_disjoint_scratch :
    (oracleMovedWires p).Disjoint (decoderAndScratchWires p)

/-- canonical `QLayout`は任意slot・event offsetの移動先計算配置条件を満たす。 -/
theorem columnEventMoveLayout_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    ColumnEventMoveLayout p slot offset := by
  let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have movedNodup : (oracleMovedWires p).Nodup := by
    simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using
      (RegisterSlice.wireList_nodup (systemWidth := p.systemWidth) movedSlice)
  have scratchNodup : (decoderAndScratchWires p).Nodup :=
    List.Nodup.sublist (by simp) (decoderAndScratchFlags_nodup p)
  have movedAnd :
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [movedSlice, andSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have movedScratch :
      (oracleMovedWires p).Disjoint (decoderAndScratchWires p) := by
    rw [List.disjoint_left]
    intro wire movedMember scratchMember
    have movedFull : wire ∈
        (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using movedMember
    have scratchFull : wire ∈
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [decoderAndScratchWires, oracleAndWorkWires, andSlice,
        RegisterSlice.wireList] using List.mem_of_mem_drop scratchMember
    exact (List.disjoint_left.mp movedAnd movedFull) scratchFull
  have coordinateSub : ∀ wire ∈ columnEventCoordinate p offset,
      wire ∈ oracleMovedWires p := by
    intro wire member
    unfold columnEventCoordinate at member
    split at member
    · exact List.mem_of_mem_drop (List.mem_of_mem_take member)
    · exact List.mem_of_mem_take member
  have coordinateNodup : (columnEventCoordinate p offset).Nodup := by
    unfold columnEventCoordinate
    split
    · exact (List.Pairwise.drop movedNodup).take
    · exact List.Pairwise.take movedNodup
  have coordinateScratch :
      (columnEventCoordinate p offset).Disjoint (decoderAndScratchWires p) := by
    rw [List.disjoint_left]
    intro wire coordinateMember scratchMember
    exact (List.disjoint_left.mp movedScratch)
      (coordinateSub wire coordinateMember) scratchMember
  refine {
    same_length := ?_
    source_disjoint_moved := ?_
    source_nodup := by
      unfold registerWordAt
      exact (columnKeyWires_nodup p).drop.take
    moved_nodup := movedNodup
    coordinate_scratch_nodup :=
      List.nodup_append.mpr ⟨coordinateNodup, scratchNodup, by
        intro left leftMember right rightMember equal
        exact (List.disjoint_left.mp coordinateScratch) leftMember
          (equal ▸ rightMember)⟩
    enough_scratch := ?_
    moved_disjoint_scratch := movedScratch }
  · rw [registerWordAt_length p (columnKeyWires p)
      (columnKeyWires_length p) slot]
    simp [oracleMovedWires, QParameters.movedWidth]
  · rw [List.disjoint_left]
    intro wire sourceMember movedMember
    exact (List.disjoint_left.mp
      (columnKeyWires_disjoint_oracleSlice p
        (OracleWorkLayout.canonical p).moved))
      (mem_register_of_mem_registerWordAt p (columnKeyWires p) slot sourceMember)
      (by simpa [oracleMovedWires, RegisterSlice.wireList] using movedMember)
  · have coordinateLength : (columnEventCoordinate p offset).length = p.q := by
      unfold columnEventCoordinate
      split
      · simp [oracleMovedWires, QParameters.movedWidth, QParameters.wordWidth]
        omega
      · simp [oracleMovedWires, QParameters.movedWidth, QParameters.wordWidth]
        omega
    rw [coordinateLength]
    have wordEnough := decoderAndScratchWires_wordWidth_le p
    simp [QParameters.wordWidth] at wordEnough
    omega

/-- column event移動先計算を開始する際の値条件。 -/
structure ColumnEventMoveInput (p : QParameters) (slot : Fin p.K)
    (source : QSite p)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 選択source wordは対応siteのbit列である。 -/
  source_word :
    readWires (registerWordAt p (columnKeyWires p) slot) input =
      siteWordBits p source
  /-- moved workは全0である。 -/
  moved_zero : readWires (oracleMovedWires p) input =
    List.replicate (oracleMovedWires p).length false
  /-- increment用AND scratchは全0である。 -/
  scratch_zero : ∀ wire ∈ decoderAndScratchWires p, input wire = false

/--
source copyと周期incrementから成る実回路は、offsetが表す右・上移動site wordを返す。
証明は二つの`q` bit半分の作用を合成し、`2^(2q)`個のwordを列挙しない。
-/
theorem runBasis_columnEventMovedCircuit_read
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (source : QSite p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnEventMoveInput p slot source input) :
    readWires (oracleMovedWires p)
        ((columnEventMovedCircuit p slot offset).runBasis
          reversibleGatePermutation input) =
      siteWordBits p
        (moveSite source
          (selectorDirection (selectorOfSlotOffset slot offset))) := by
  let sourceWord := registerWordAt p (columnKeyWires p) slot
  let moved := oracleMovedWires p
  let scratch := decoderAndScratchWires p
  let coordinate := columnEventCoordinate p offset
  let copied := (xorCopy sourceWord moved).runBasis
    reversibleGatePermutation input
  let output := (incrementWordMod2PowInPlaceCircuit coordinate scratch).runBasis
    reversibleGatePermutation copied
  have layout := columnEventMoveLayout_canonical p slot offset
  have copiedMoved : readWires moved copied = siteWordBits p source := by
    rw [show copied = (xorCopy sourceWord moved).runBasis
      reversibleGatePermutation input by rfl]
    rw [readWires_validatedXorCopyLists_target sourceWord moved input
      layout.source_nodup layout.moved_nodup layout.same_length
      layout.source_disjoint_moved]
    rw [show readWires sourceWord input = siteWordBits p source by
      exact clean.source_word]
    rw [show readWires moved input = List.replicate moved.length false by
      exact clean.moved_zero]
    simpa [moved, oracleMovedWires, QParameters.movedWidth] using
      candidateZipWithXorFalse (siteWordBits p source)
  have copiedScratch : ∀ wire ∈ scratch, copied wire = false := by
    intro wire member
    rw [show copied wire = input wire by
      exact runBasis_validatedXorCopyLists_outside sourceWord moved input
        layout.source_nodup layout.moved_nodup layout.same_length
        layout.source_disjoint_moved wire (by
        intro movedMember
        exact (List.disjoint_left.mp layout.moved_disjoint_scratch)
          movedMember member)]
    exact clean.scratch_zero wire member
  have outputEq : output = incrementWordCarrySequenceReference [] coordinate copied := by
    exact runBasis_incrementWordMod2PowInPlaceCircuit coordinate scratch copied
      layout.enough_scratch layout.coordinate_scratch_nodup copiedScratch
  have circuitOutput :
      (columnEventMovedCircuit p slot offset).runBasis
          reversibleGatePermutation input = output := by
    rfl
  rw [circuitOutput]
  have movedLength : moved.length = p.wordWidth := by
    simp [moved, oracleMovedWires, QParameters.movedWidth]
  have splitMoved : moved.take p.q ++ moved.drop p.q = moved :=
    List.take_append_drop p.q moved
  have splitNodup : (moved.take p.q ++ moved.drop p.q).Nodup := by
    rw [splitMoved]
    exact layout.moved_nodup
  have lowHighDisjoint : (moved.take p.q).Disjoint (moved.drop p.q) := by
    rw [List.disjoint_left]
    intro wire lowMember highMember
    exact (List.nodup_append.mp splitNodup).2.2 wire lowMember wire
      highMember rfl
  have copiedLow : readWires (moved.take p.q) copied =
      (siteWordBits p source).take p.q := by
    have point := congrArg (List.take p.q) copiedMoved
    simpa [readWires] using point
  have copiedHigh : readWires (moved.drop p.q) copied =
      (siteWordBits p source).drop p.q := by
    have point := congrArg (List.drop p.q) copiedMoved
    simpa [readWires] using point
  by_cases vertical : 4 ≤ offset.val
  · have dropLength : (moved.drop p.q).length = p.q := by
      simp [movedLength, QParameters.wordWidth]
      omega
    have coordinateEq : coordinate = moved.drop p.q := by
      dsimp [coordinate, columnEventCoordinate]
      rw [if_pos vertical]
      change (moved.drop p.q).take p.q = moved.drop p.q
      exact List.take_of_length_le (le_of_eq dropLength)
    have highIncrement : readWires (moved.drop p.q) output =
        incrementBits (readWires (moved.drop p.q) copied) := by
      rw [outputEq, coordinateEq]
      have coordinateNodup : coordinate.Nodup :=
        (List.nodup_append.mp layout.coordinate_scratch_nodup).1
      rw [coordinateEq] at coordinateNodup
      simpa [incrementBits, allWiresTrue, readWires] using
        readWires_incrementWordCarrySequenceReference [] (moved.drop p.q) copied
          coordinateNodup
    have lowPreserved : readWires (moved.take p.q) output =
        readWires (moved.take p.q) copied := by
      rw [outputEq]
      apply List.map_congr_left
      intro wire member
      exact incrementWordCarrySequenceReference_outside [] coordinate wire copied (by
        rw [coordinateEq]
        exact fun highMember =>
          (List.disjoint_left.mp lowHighDisjoint) member highMember)
    calc
      readWires moved output =
          readWires (moved.take p.q) output ++
            readWires (moved.drop p.q) output := by
              rw [← splitMoved]
              simp [readWires]
      _ = (siteWordBits p source).take p.q ++
          incrementBits ((siteWordBits p source).drop p.q) := by
            rw [lowPreserved, highIncrement, copiedLow, copiedHigh]
      _ = siteWordBits p
          (moveSite source
            (selectorDirection (selectorOfSlotOffset slot offset))) := by
            rw [show selectorDirection (selectorOfSlotOffset slot offset) = .up by
              simp [selectorDirection, vertical]]
            exact (siteWordBits_moveSite_up p source).symm
  · have coordinateEq : coordinate = moved.take p.q := by
      dsimp [coordinate, columnEventCoordinate, moved]
      rw [if_neg vertical]
    have lowIncrement : readWires (moved.take p.q) output =
        incrementBits (readWires (moved.take p.q) copied) := by
      rw [outputEq, coordinateEq]
      have coordinateNodup : coordinate.Nodup :=
        (List.nodup_append.mp layout.coordinate_scratch_nodup).1
      rw [coordinateEq] at coordinateNodup
      simpa [incrementBits, allWiresTrue, readWires] using
        readWires_incrementWordCarrySequenceReference [] (moved.take p.q) copied
          coordinateNodup
    have highPreserved : readWires (moved.drop p.q) output =
        readWires (moved.drop p.q) copied := by
      rw [outputEq]
      apply List.map_congr_left
      intro wire member
      exact incrementWordCarrySequenceReference_outside [] coordinate wire copied (by
        rw [coordinateEq]
        exact fun lowMember =>
          (List.disjoint_left.mp lowHighDisjoint) lowMember member)
    have belowFour : offset.val < 4 := by omega
    calc
      readWires moved output =
          readWires (moved.take p.q) output ++
            readWires (moved.drop p.q) output := by
              rw [← splitMoved]
              simp [readWires]
      _ = incrementBits ((siteWordBits p source).take p.q) ++
          (siteWordBits p source).drop p.q := by
            rw [lowIncrement, highPreserved, copiedLow, copiedHigh]
      _ = siteWordBits p
          (moveSite source
            (selectorDirection (selectorOfSlotOffset slot offset))) := by
            rw [show selectorDirection (selectorOfSlotOffset slot offset) =
                .right by simp [selectorDirection, belowFour]]
            exact (siteWordBits_moveSite_right p source).symm

/-- 衝突移動ではsource以外にも移動先が占有されるため、入力粒子数は1より大きい。 -/
theorem one_lt_configuration_card_of_collision
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (sourceMember : source ∈ configuration.1)
    (direction : QDirection)
    (collision : moveSite source direction ∈ configuration.1.erase source) :
    1 < configuration.1.card := by
  have erasePositive : 0 < (configuration.1.erase source).card :=
    Finset.card_pos.mpr ⟨moveSite source direction, collision⟩
  have erasedCard := Finset.card_erase_of_mem sourceMember
  omega

/-- actual event branchがmembership・degree flagから読む純粋なBool条件。 -/
def columnEventMembershipCondition
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (slot : Fin p.K) (offset : Fin 6) : Bool :=
  let moved := moveSite source
    (selectorDirection (selectorOfSlotOffset slot offset))
  if offset.val % 2 = 1 then
    decide (moved ∈ configuration.1.erase source) &&
      decide (1 < configuration.1.card)
  else
    decide (moved ∉ configuration.1)

/--
sourceが実在する合法配置では、実回路のreplacement/collision条件は
`columnReference`の「要求衝突bitと実衝突が一致する」条件と同値である。
-/
theorem columnEventMembershipCondition_correct
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (sourceMember : source ∈ configuration.1)
    (slot : Fin p.K) (offset : Fin 6) :
    columnEventMembershipCondition configuration source slot offset =
      decide ((decide
        (moveSite source
          (selectorDirection (selectorOfSlotOffset slot offset)) ∈
            configuration.1.erase source) : Bool) =
        selectorRequestsCollision (selectorOfSlotOffset slot offset)) := by
  let moved := moveSite source
    (selectorDirection (selectorOfSlotOffset slot offset))
  have movedNeSource : moved ≠ source := by
    exact moveSite_ne_self source
      (selectorDirection (selectorOfSlotOffset slot offset))
  by_cases requested : offset.val % 2 = 1
  · by_cases collision : moved ∈ configuration.1.erase source
    · have degreeLarge : 1 < configuration.1.card :=
        one_lt_configuration_card_of_collision configuration source sourceMember
          (selectorDirection (selectorOfSlotOffset slot offset)) collision
      simp [columnEventMembershipCondition, moved, requested,
        collision, degreeLarge, selectorRequestsCollision]
    · simp [columnEventMembershipCondition, moved, requested,
        collision, selectorRequestsCollision]
  · by_cases collision : moved ∈ configuration.1.erase source
    · have movedMember : moved ∈ configuration.1 :=
        (Finset.mem_erase.mp collision).2
      simp [columnEventMembershipCondition, moved, requested,
        collision, movedMember, selectorRequestsCollision]
    · have movedAbsent : moved ∉ configuration.1 := by
        intro movedMember
        exact collision (Finset.mem_erase.mpr ⟨movedNeSource, movedMember⟩)
      simp [columnEventMembershipCondition, moved, requested,
        collision, movedAbsent, selectorRequestsCollision]

/-- 粒子数未満の物理 slot は `configurationSlot?` で対応 site を返す。 -/
theorem configurationSlot_eq_some_siteAt
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (active : slot.val < configuration.1.card) :
    ∃ member : configuration.siteAt ⟨slot.val, active⟩ ∈ configuration.1,
      configurationSlot? configuration slot =
        some ⟨configuration.siteAt ⟨slot.val, active⟩, member⟩ := by
  let entry := (configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩
  refine ⟨entry.2, ?_⟩
  unfold configurationSlot?
  rw [dif_pos active]
  rfl

/--
実在 slot、event offset、正しい rep/coll 条件では純粋 column 参照関数が更新配置を返す。
-/
theorem columnReference_eventSlot_active
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
    ∃ rowSelector,
      columnReference configuration (selectorOfSlotOffset slot offset) =
        some ⟨updateConfiguration configuration
          (configuration.siteAt ⟨slot.val, active⟩,
            selectorDirection (selectorOfSlotOffset slot offset)),
          rowSelector, false⟩ := by
  rcases configurationSlot_eq_some_siteAt configuration slot active with
    ⟨member, selected⟩
  apply columnReference_event_active configuration
    (selectorOfSlotOffset slot offset)
    (configuration.siteAt ⟨slot.val, active⟩) member (by simpa using selected)
  · simp
    omega
  · exact branchCorrect

/-- rep/coll 条件が逆なら、実在 event slot も純粋 column 参照関数で拒否される。 -/
theorem columnReference_eventSlot_wrongBranch
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (eventRange : 2 ≤ offset.val)
    (wrongBranch :
      (decide (moveSite (configuration.siteAt ⟨slot.val, active⟩)
          (selectorDirection (selectorOfSlotOffset slot offset)) ∈
        configuration.1.erase
          (configuration.siteAt ⟨slot.val, active⟩)) : Bool) ≠
        selectorRequestsCollision (selectorOfSlotOffset slot offset)) :
    columnReference configuration (selectorOfSlotOffset slot offset) = none := by
  rcases configurationSlot_eq_some_siteAt configuration slot active with
    ⟨member, selected⟩
  have selectedAtSelector :
      configurationSlot? configuration
          (selectorSlot (selectorOfSlotOffset slot offset)) =
        some ⟨configuration.siteAt ⟨slot.val, active⟩, member⟩ := by
    simpa using selected
  unfold columnReference
  rw [selectedAtSelector]
  have notDiagonal : ¬offset.val < 2 := by omega
  have notDiagonalSelector :
      ¬(selectorOffset (selectorOfSlotOffset slot offset)).val < 2 := by
    simpa using notDiagonal
  simp only
  rw [dif_neg notDiagonalSelector]
  rw [dif_neg wrongBranch]

/-- 粒子数以上の padding slot は純粋 column 参照関数で常に拒否される。 -/
theorem columnReference_paddingSlot
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (padding : configuration.1.card ≤ slot.val) :
    columnReference configuration (selectorOfSlotOffset slot offset) = none := by
  have missing : configurationSlot? configuration slot = none := by
    unfold configurationSlot?
    rw [dif_neg (Nat.not_lt.mpr padding)]
  have missingAtSelector :
      configurationSlot? configuration
          (selectorSlot (selectorOfSlotOffset slot offset)) = none := by
    simpa using missing
  unfold columnReference
  rw [missingAtSelector]

/-- column event 分岐の selector 比較回路。 -/
def columnEventSelectorCompute (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  selectorEqualsConstant (columnSelectorWires p) (decoderAndScratchWires p)
    (6 * slot.val + offset.val) (oracleSelectedWire p)

/-- column event の selector 定数との一致を表す純粋な Bool 条件。 -/
def columnEventSelectorMatches (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Bool :=
  diagonalSelectorMatches (columnSelectorWires p)
    (6 * slot.val + offset.val) input

/-- clean scratch 上で column event selector 比較正本は純粋一致条件に一致する。 -/
theorem runBasis_columnEventSelectorCompute
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false) :
    (columnEventSelectorCompute p slot offset).runBasis
        reversibleGatePermutation input =
      if columnEventSelectorMatches p slot offset input then
        xBasisAction (oracleSelectedWire p) input
      else input := by
  have result := runBasis_selectorEqualsConstant_bits (columnSelectorWires p)
    (decoderAndScratchWires p) (6 * slot.val + offset.val)
    (oracleSelectedWire p) input
    (by simpa [columnSelectorWires] using
      selectorWidth_le_decoderAndScratch_add_one p)
    (columnSelector_decoderScratch_selected_nodup p) scratchZero
  simpa [columnEventSelectorCompute, columnEventSelectorMatches,
    diagonalSelectorMatches] using result

/-- selected bit が clean なら、selector 比較後の値は純粋一致条件そのものである。 -/
theorem runBasis_columnEventSelectorCompute_selected
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (selectedZero : input (oracleSelectedWire p) = false) :
    (columnEventSelectorCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleSelectedWire p) =
      columnEventSelectorMatches p slot offset input := by
  rw [runBasis_columnEventSelectorCompute p slot offset input scratchZero]
  by_cases isMatch : columnEventSelectorMatches p slot offset input = true
  · simp [isMatch, xBasisAction, selectedZero]
  · have mismatch := Bool.eq_false_of_not_eq_true isMatch
    simp [mismatch, selectedZero]

/-- column event 分岐の membership 判定回路。 -/
def columnEventMembership (p : QParameters) (slot : Fin p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  xorMembershipMatchGoodAndAbsentFlagsCircuit p (columnKeyWires p) slot true

/--
合法配置の moved site に対する実 membership 回路は、absent と present-other を
集合 membership と厳密に一致させ、局所比較 work を clean に保つ。
-/
theorem runBasis_columnEventMembership_configuration
    (p : QParameters) (configuration : QConfiguration p)
    (source moved : QSite p) (slot : Fin p.K)
    (active : slot.val < configuration.1.card)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration moved input)
    (slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input)
    (flagsClean : MembershipFlagsClean p input) :
    let output := (columnEventMembership p slot).runBasis
      reversibleGatePermutation input
    output (oracleAbsentWire p) = decide (moved ∉ configuration.1) ∧
      output (oraclePresentOtherWire p) =
        decide (moved ∈ configuration.1.erase source) ∧
      MembershipSlotClean (oracleCompareWorkWires p)
        (decoderAndScratchWires p) output := by
  dsimp only
  let output := (columnEventMembership p slot).runBasis
    reversibleGatePermutation input
  have run := runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit p (columnKeyWires p)
    (columnKeyWires_membershipInputLayout p) slot true input slotClean
  have absentActual : output (oracleAbsentWire p) =
      noMembershipMatch p (columnKeyWires p) input := by
    simpa [output, columnEventMembership] using
      runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_absent p (columnKeyWires p)
        (columnKeyWires_membershipInputLayout p) slot true input slotClean
          flagsClean
  have otherActual : output (oraclePresentOtherWire p) =
      hasMatchingOther p (columnKeyWires p) slot true input := by
    simpa [output, columnEventMembership] using
      runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_presentOther p (columnKeyWires p)
        (columnKeyWires_membershipInputLayout p) slot true input slotClean
          flagsClean (specification.distinctPresentWords p (columnKeyWires p)
            configuration moved input)
  have absentReference := noMembershipMatch_configuration p (columnKeyWires p)
    configuration moved input specification
  have otherReference := hasMatchingOther_configuration_erase p
    (columnKeyWires p) configuration source moved slot active sourceAt input
      specification
  refine ⟨absentActual.trans absentReference,
    otherActual.trans otherReference, ?_⟩
  simpa [output, columnEventMembership] using run.2

/--
membership の equal・good・present-other・absent 以外の wire は、実 membership 回路で
点ごとに保存される。
-/
theorem runBasis_columnEventMembership_other
    (p : QParameters) (selectedSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (neEqual : ∀ slot : Fin p.K, wire ≠ membershipEqualWireAt p slot)
    (neGood : ∀ slot : Fin p.K, wire ≠ membershipGoodWireAt p slot)
    (neOther : wire ≠ oraclePresentOtherWire p)
    (neAbsent : wire ≠ oracleAbsentWire p) :
    (columnEventMembership p selectedSlot).runBasis
        reversibleGatePermutation input wire = input wire := by
  have run := runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit p (columnKeyWires p)
    (columnKeyWires_membershipInputLayout p) selectedSlot true input slotClean
  have slotsPreserve : ∀ (slots : List (Fin p.K))
      (state : JointBasis p.ancillaWidth p.systemWidth),
      FoldedSiteSlotMatchAndGoodFlagsReference p (columnKeyWires p) selectedSlot true slots state
          wire = state wire := by
    intro slots
    induction slots with
    | nil => intro state; rfl
    | cons slot slots inductionHypothesis =>
        intro state
        change FoldedSiteSlotMatchAndGoodFlagsReference p (columnKeyWires p) selectedSlot true
          slots (SiteSlotMatchAndGoodFlagAtIndexXorSpec p (columnKeyWires p) selectedSlot slot
            true state) wire = state wire
        rw [inductionHypothesis]
        exact membershipSlotReference_other p (columnKeyWires p) selectedSlot slot
          true state wire (neEqual slot) (neGood slot) neOther
  rw [show (columnEventMembership p selectedSlot).runBasis
      reversibleGatePermutation input =
        MembershipMatchGoodAndAbsentFlagsXorSpec p (columnKeyWires p) selectedSlot true input by
    simpa [columnEventMembership] using run.1]
  unfold MembershipMatchGoodAndAbsentFlagsXorSpec
  split
  · rw [xBasisAction_other (oracleAbsentWire p) wire neAbsent]
    exact slotsPreserve (List.finRange p.K) input
  · exact slotsPreserve (List.finRange p.K) input

/--
実 membership 回路は event branch が読む legal・selected・present・degree・branch を
すべて点ごとに保存する。
-/
theorem runBasis_columnEventMembership_preserves_branch_inputs
    (p : QParameters) (selectedSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input) :
    let output := (columnEventMembership p selectedSlot).runBasis
      reversibleGatePermutation input
    output (oracleLegalWire p) = input (oracleLegalWire p) ∧
      output (oracleSelectedWire p) = input (oracleSelectedWire p) ∧
      output (oraclePresentWireAt p selectedSlot) =
        input (oraclePresentWireAt p selectedSlot) ∧
      output (oracleDegreeConditionWire p) =
        input (oracleDegreeConditionWire p) ∧
      output (oracleBranchWire p) = input (oracleBranchWire p) := by
  dsimp only
  let preserve := runBasis_columnEventMembership_other p selectedSlot input
    slotClean
  have legal :
      (columnEventMembership p selectedSlot).runBasis
        reversibleGatePermutation input (oracleLegalWire p) =
          input (oracleLegalWire p) := by
    apply preserve (oracleLegalWire p)
    · intro slot equal
      have numbers := congrArg wireNumber equal
      simp [oracleLegalWire, membershipEqualWireAt, QLayout.oracleSlice,
        RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth] at numbers
      omega
    · intro slot equal
      have numbers := congrArg wireNumber equal
      simp [oracleLegalWire, membershipGoodWireAt, QLayout.oracleSlice,
        RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
      omega
    · intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleLegalWire, oraclePresentOtherWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
      omega
    · intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleLegalWire, oracleAbsentWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
      omega
  have selected :
      (columnEventMembership p selectedSlot).runBasis
        reversibleGatePermutation input (oracleSelectedWire p) =
          input (oracleSelectedWire p) := by
    apply preserve (oracleSelectedWire p)
    · intro slot equal
      have numbers := congrArg wireNumber equal
      simp [oracleSelectedWire, oracleSingletonWire, membershipEqualWireAt,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth] at numbers
      omega
    · intro slot equal
      have numbers := congrArg wireNumber equal
      simp [oracleSelectedWire, oracleSingletonWire, membershipGoodWireAt,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
      omega
    · intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleSelectedWire, oraclePresentOtherWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
      omega
    · intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleSelectedWire, oracleAbsentWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
      omega
  have present :
      (columnEventMembership p selectedSlot).runBasis
        reversibleGatePermutation input (oraclePresentWireAt p selectedSlot) =
          input (oraclePresentWireAt p selectedSlot) := by
    apply preserve (oraclePresentWireAt p selectedSlot)
    · exact fun slot => oraclePresentWireAt_ne_membershipEqual p selectedSlot slot
    · exact fun slot => oraclePresentWireAt_ne_membershipGood p selectedSlot slot
    · exact oraclePresentWireAt_ne_presentOther p selectedSlot
    · intro equal
      have numbers := congrArg wireNumber equal
      simp [oraclePresentWireAt, oracleAbsentWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
      omega
  have degree :
      (columnEventMembership p selectedSlot).runBasis
        reversibleGatePermutation input (oracleDegreeConditionWire p) =
          input (oracleDegreeConditionWire p) := by
    apply preserve (oracleDegreeConditionWire p)
    · intro slot equal
      have numbers := congrArg wireNumber equal
      simp [oracleDegreeConditionWire, oracleSingletonWire,
        membershipEqualWireAt, QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical, QParameters.membershipEqWidth] at numbers
      omega
    · intro slot equal
      have numbers := congrArg wireNumber equal
      simp [oracleDegreeConditionWire, oracleSingletonWire,
        membershipGoodWireAt, QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical, QParameters.membershipEqWidth,
        QParameters.membershipGoodWidth] at numbers
      omega
    · intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleDegreeConditionWire, oraclePresentOtherWire,
        oracleSingletonWire, QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical, QParameters.membershipEqWidth,
        QParameters.membershipGoodWidth] at numbers
      omega
    · intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleDegreeConditionWire, oracleAbsentWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
      omega
  have branch :
      (columnEventMembership p selectedSlot).runBasis
        reversibleGatePermutation input (oracleBranchWire p) =
          input (oracleBranchWire p) := by
    apply preserve (oracleBranchWire p)
    · intro slot equal
      have numbers := congrArg wireNumber equal
      simp [oracleBranchWire, oracleSingletonWire, membershipEqualWireAt,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth] at numbers
      omega
    · intro slot equal
      have numbers := congrArg wireNumber equal
      simp [oracleBranchWire, oracleSingletonWire, membershipGoodWireAt,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
      omega
    · intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleBranchWire, oraclePresentOtherWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
    · intro equal
      have numbers := congrArg wireNumber equal
      simp [oracleBranchWire, oracleAbsentWire, oracleSingletonWire,
        QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
        QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
      omega
  exact ⟨legal, selected, present, degree, branch⟩

/-- column event 分岐で source word を moved work へ複写する回路。 -/
def columnEventMovedCopy (p : QParameters) (slot : Fin p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  xorCopy (registerWordAt p (columnKeyWires p) slot) (oracleMovedWires p)

/-- The canonical column moved-copy execution is the independent pure reference. -/
theorem runBasis_columnEventMovedCopy_eq_controlledCopyReference
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (columnEventMovedCopy p slot).runBasis reversibleGatePermutation input =
      controlledCopyBasisReference true
        (registerWordAt p (columnKeyWires p) slot) (oracleMovedWires p) input := by
  have layout := columnEventMoveLayout_canonical p slot (0 : Fin 6)
  rw [columnEventMovedCopy]
  exact runBasis_validatedXorCopyLists_eq_controlledCopyBasisReference_true
    (registerWordAt p (columnKeyWires p) slot) (oracleMovedWires p) input
    layout.source_nodup layout.moved_nodup layout.same_length
    layout.source_disjoint_moved

/-- column event 分岐で moved site の指定座標を一歩進める回路。 -/
def columnEventMoveForward (p : QParameters) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  incrementWordMod2PowInPlaceCircuit (columnEventCoordinate p offset)
    (decoderAndScratchWires p)

/-- column event 分岐の多重制御に渡す wire 列。 -/
def columnEventBranchControls (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  [oracleLegalWire p, oracleSelectedWire p, oraclePresentWireAt p slot,
    if offset.val % 2 = 1 then
      oraclePresentOtherWire p else oracleAbsentWire p] ++
    if offset.val % 2 = 1 then [oracleDegreeConditionWire p] else []

/-- canonical oracle layout は column event branch の全制御・scratch・target 非重複条件を満たす。 -/
theorem columnEventBranchControls_layout_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    (columnEventBranchControls p slot offset ++ decoderAndScratchWires p ++
      [oracleBranchWire p]).Nodup := by
  let base : List (Wire p.ancillaWidth p.systemWidth) :=
    [oracleLegalWire p, oracleSelectedWire p, oraclePresentWireAt p slot]
  let scratch := decoderAndScratchWires p
  let branch := oracleBranchWire p
  let absent := oracleAbsentWire p
  let presentOther := oraclePresentOtherWire p
  let degree := oracleDegreeConditionWire p
  let legalSlice := (OracleWorkLayout.canonical p).legal
  let selectedSlice := (OracleWorkLayout.canonical p).selected
  let presentSlice := (OracleWorkLayout.canonical p).present
  let absentSlice := (OracleWorkLayout.canonical p).absent
  let presentOtherSlice := (OracleWorkLayout.canonical p).presentOther
  let degreeSlice := (OracleWorkLayout.canonical p).degreeCondition
  let branchSlice := (OracleWorkLayout.canonical p).branch
  have baseLayout : (base ++ scratch ++ [branch]).Nodup := by
    simpa [base, scratch, branch] using
      (diagonalBranch_controls_scratch_branch_nodup p slot)
  have absentNeLegal : absent ≠ oracleLegalWire p := by
    simpa [absent, absentSlice, legalSlice, oracleAbsentWire,
      oracleSingletonWire, oracleLegalWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p absentSlice legalSlice 0 0
        (by simp [absentSlice, legalSlice, OracleWorkLayout.canonical]; omega)
  have absentNeSelected : absent ≠ oracleSelectedWire p := by
    simpa [absent, absentSlice, selectedSlice, oracleAbsentWire,
      oracleSingletonWire, oracleSelectedWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p absentSlice selectedSlice 0 0
        (by simp [absentSlice, selectedSlice, OracleWorkLayout.canonical]; omega)
  have absentNePresent : absent ≠ oraclePresentWireAt p slot := by
    simpa [absent, absentSlice, presentSlice, oracleAbsentWire,
      oracleSingletonWire, oraclePresentWireAt] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p absentSlice presentSlice 0 slot
        (by simp [absentSlice, presentSlice, OracleWorkLayout.canonical]; omega)
  have absentNotBase : absent ∉ base := by
    intro member
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with equal | equal | equal
    · exact absentNeLegal equal
    · exact absentNeSelected equal
    · exact absentNePresent equal
  have absentNotScratch : absent ∉ scratch := by
    simpa [absent, scratch, absentSlice, oracleAbsentWire] using
      oracleSingletonWire_not_mem_decoderAndScratch p absentSlice
        (by simp [absentSlice, OracleWorkLayout.canonical]; omega)
  have absentNeBranch : absent ≠ branch := by
    simpa [absent, branch, absentSlice, branchSlice, oracleAbsentWire,
      oracleBranchWire, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p absentSlice branchSlice 0 0
        (by simp [absentSlice, branchSlice, OracleWorkLayout.canonical]; omega)
  have withAbsent :
      (base ++ [absent] ++ scratch ++ [branch]).Nodup :=
    eventControls_nodup_insert_before_scratch base scratch branch absent
      baseLayout absentNotBase absentNotScratch absentNeBranch
  have otherNeLegal : presentOther ≠ oracleLegalWire p := by
    simpa [presentOther, presentOtherSlice, legalSlice,
      oraclePresentOtherWire, oracleSingletonWire, oracleLegalWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p presentOtherSlice legalSlice 0 0
        (by simp [presentOtherSlice, legalSlice, OracleWorkLayout.canonical]; omega)
  have otherNeSelected : presentOther ≠ oracleSelectedWire p := by
    simpa [presentOther, presentOtherSlice, selectedSlice,
      oraclePresentOtherWire, oracleSingletonWire, oracleSelectedWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p presentOtherSlice
        selectedSlice 0 0
        (by simp [presentOtherSlice, selectedSlice,
          OracleWorkLayout.canonical]; omega)
  have otherNePresent : presentOther ≠ oraclePresentWireAt p slot := by
    simpa [presentOther, presentOtherSlice, presentSlice,
      oraclePresentOtherWire, oracleSingletonWire, oraclePresentWireAt] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p presentOtherSlice
        presentSlice 0 slot
        (by simp [presentOtherSlice, presentSlice,
          OracleWorkLayout.canonical]; omega)
  have otherNotBase : presentOther ∉ base := by
    intro member
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with equal | equal | equal
    · exact otherNeLegal equal
    · exact otherNeSelected equal
    · exact otherNePresent equal
  have otherNotScratch : presentOther ∉ scratch := by
    simpa [presentOther, scratch, presentOtherSlice,
      oraclePresentOtherWire] using
      oracleSingletonWire_not_mem_decoderAndScratch p presentOtherSlice
        (by simp [presentOtherSlice, OracleWorkLayout.canonical]; omega)
  have otherNeBranch : presentOther ≠ branch := by
    simpa [presentOther, branch, presentOtherSlice, branchSlice,
      oraclePresentOtherWire, oracleBranchWire, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p presentOtherSlice branchSlice
        0 0
        (by simp [presentOtherSlice, branchSlice,
          OracleWorkLayout.canonical])
  have withOther :
      (base ++ [presentOther] ++ scratch ++ [branch]).Nodup :=
    eventControls_nodup_insert_before_scratch base scratch branch presentOther
      baseLayout otherNotBase otherNotScratch otherNeBranch
  have degreeNeLegal : degree ≠ oracleLegalWire p := by
    simpa [degree, degreeSlice, legalSlice, oracleDegreeConditionWire,
      oracleSingletonWire, oracleLegalWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p degreeSlice legalSlice 0 0
        (by simp [degreeSlice, legalSlice, OracleWorkLayout.canonical]; omega)
  have degreeNeSelected : degree ≠ oracleSelectedWire p := by
    simpa [degree, degreeSlice, selectedSlice, oracleDegreeConditionWire,
      oracleSingletonWire, oracleSelectedWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p degreeSlice selectedSlice 0 0
        (by simp [degreeSlice, selectedSlice, OracleWorkLayout.canonical]; omega)
  have degreeNePresent : degree ≠ oraclePresentWireAt p slot := by
    simpa [degree, degreeSlice, presentSlice, oracleDegreeConditionWire,
      oracleSingletonWire, oraclePresentWireAt] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p degreeSlice presentSlice 0 slot
        (by simp [degreeSlice, presentSlice, OracleWorkLayout.canonical]; omega)
  have degreeNotBase : degree ∉ base := by
    intro member
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with equal | equal | equal
    · exact degreeNeLegal equal
    · exact degreeNeSelected equal
    · exact degreeNePresent equal
  have degreeNeOther : degree ≠ presentOther := by
    simpa [degree, presentOther, degreeSlice, presentOtherSlice,
      oracleDegreeConditionWire, oraclePresentOtherWire, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p degreeSlice
        presentOtherSlice 0 0
        (by simp [degreeSlice, presentOtherSlice,
          OracleWorkLayout.canonical]; omega)
  have degreeNotBaseOther : degree ∉ base ++ [presentOther] := by
    intro member
    rcases List.mem_append.mp member with baseMember | otherMember
    · exact degreeNotBase baseMember
    · have equal : degree = presentOther := by simpa using otherMember
      exact degreeNeOther equal
  have degreeNotScratch : degree ∉ scratch := by
    simpa [degree, scratch, degreeSlice, oracleDegreeConditionWire] using
      oracleSingletonWire_not_mem_decoderAndScratch p degreeSlice
        (by simp [degreeSlice, OracleWorkLayout.canonical]; omega)
  have degreeNeBranch : degree ≠ branch := by
    simpa [degree, branch, degreeSlice, branchSlice,
      oracleDegreeConditionWire, oracleBranchWire, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p degreeSlice branchSlice 0 0
        (by simp [degreeSlice, branchSlice, OracleWorkLayout.canonical]; omega)
  have withOtherDegree :
      (base ++ [presentOther] ++ [degree] ++ scratch ++ [branch]).Nodup := by
    simpa [List.append_assoc] using
      eventControls_nodup_insert_before_scratch (base ++ [presentOther]) scratch
        branch degree (by simpa [List.append_assoc] using withOther)
        degreeNotBaseOther degreeNotScratch degreeNeBranch
  by_cases collision : offset.val % 2 = 1
  · simpa [columnEventBranchControls, collision, base, scratch, branch,
      presentOther, degree, List.append_assoc] using withOtherDegree
  · simpa [columnEventBranchControls, collision, base, scratch, branch,
      absent, List.append_assoc] using withAbsent

/-- column event branch の制御本数には canonical AND scratch が十分である。 -/
theorem columnEventBranchControls_enoughScratch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    (columnEventBranchControls p slot offset).length ≤
      (decoderAndScratchWires p).length + 1 := by
  by_cases collision : offset.val % 2 = 1 <;>
    simp [columnEventBranchControls, collision, decoderAndScratchWires,
      oracleAndWorkWires, QParameters.andWorkWidth, QParameters.wordWidth] <;>
    omega

/-- column event 分岐の受理 bit を計算する回路。 -/
def columnEventBranchCompute (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  positiveMultiControlledX (columnEventBranchControls p slot offset)
    (decoderAndScratchWires p)
    (oracleBranchWire p)

/--
静的な非重複配置と clean scratch の下で、column event branch 正本は
全制御の論理積を branch bit へ XOR する。
-/
theorem runBasis_columnEventBranchCompute
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (columnEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input =
      if allWiresTrue (columnEventBranchControls p slot offset) input then
        xBasisAction (oracleBranchWire p) input
      else input := by
  have result := runBasis_positiveMultiControlledX
    (columnEventBranchControls p slot offset) (decoderAndScratchWires p)
    (oracleBranchWire p) input
    (columnEventBranchControls_enoughScratch p slot offset)
    layoutNodup scratchZero
  simpa [columnEventBranchCompute] using result

/-- canonical 配置では、column event branch の制御論理積仕様は配置仮定を要しない。 -/
theorem runBasis_columnEventBranchCompute_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input =
      if allWiresTrue (columnEventBranchControls p slot offset) input then
        xBasisAction (oracleBranchWire p) input
      else input := by
  exact runBasis_columnEventBranchCompute p slot offset input
    (columnEventBranchControls_layout_canonical p slot offset) scratchZero

/-- branch bit が clean なら、branch 計算後の値は全制御の論理積そのものである。 -/
theorem runBasis_columnEventBranchCompute_branch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (columnEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) =
      allWiresTrue (columnEventBranchControls p slot offset) input := by
  rw [runBasis_columnEventBranchCompute p slot offset input layoutNodup
    scratchZero]
  by_cases enabled : allWiresTrue (columnEventBranchControls p slot offset) input
  · simp [enabled, xBasisAction, branchZero]
  · have disabled := Bool.eq_false_of_not_eq_true enabled
    simp [disabled, branchZero]

/-- canonical 配置で branch bit が clean なら、計算後の値は全制御の論理積である。 -/
theorem runBasis_columnEventBranchCompute_branch_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) =
      allWiresTrue (columnEventBranchControls p slot offset) input := by
  exact runBasis_columnEventBranchCompute_branch p slot offset input
    (columnEventBranchControls_layout_canonical p slot offset) scratchZero
      branchZero

/--
合法配置の membership 入力では、実 membership と実 branch 回路の合成結果が
純粋な replacement/collision 受理条件に厳密一致する。
-/
theorem runBasis_columnEventMembership_branch_configuration
    (p : QParameters) (configuration : QConfiguration p)
    (source : QSite p) (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration
        (moveSite source
          (selectorDirection (selectorOfSlotOffset slot offset))) input)
    (slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input)
    (flagsClean : MembershipFlagsClean p input)
    (legalTrue : input (oracleLegalWire p) = true)
    (selectedTrue : input (oracleSelectedWire p) = true)
    (degreeValue : input (oracleDegreeConditionWire p) =
      decide (1 < configuration.1.card))
    (branchZero : input (oracleBranchWire p) = false) :
    let afterMembership := (columnEventMembership p slot).runBasis
      reversibleGatePermutation input
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation afterMembership (oracleBranchWire p) =
      columnEventMembershipCondition configuration source slot offset := by
  dsimp only
  let afterMembership := (columnEventMembership p slot).runBasis
    reversibleGatePermutation input
  let moved := moveSite source
    (selectorDirection (selectorOfSlotOffset slot offset))
  have membership := runBasis_columnEventMembership_configuration p configuration
    source moved slot active sourceAt input specification slotClean flagsClean
  have persistent := runBasis_columnEventMembership_preserves_branch_inputs p
    slot input slotClean
  have presentTrue : input (oraclePresentWireAt p slot) = true := by
    rw [specification.present slot]
    exact decide_eq_true active
  have afterLegal : afterMembership (oracleLegalWire p) = true :=
    persistent.1.trans legalTrue
  have afterSelected : afterMembership (oracleSelectedWire p) = true :=
    persistent.2.1.trans selectedTrue
  have afterPresent : afterMembership (oraclePresentWireAt p slot) = true :=
    persistent.2.2.1.trans presentTrue
  have afterDegree : afterMembership (oracleDegreeConditionWire p) =
      decide (1 < configuration.1.card) :=
    persistent.2.2.2.1.trans degreeValue
  have afterBranchZero : afterMembership (oracleBranchWire p) = false :=
    persistent.2.2.2.2.trans branchZero
  have afterAbsent : afterMembership (oracleAbsentWire p) =
      decide (moved ∉ configuration.1) := membership.1
  have afterOther : afterMembership (oraclePresentOtherWire p) =
      decide (moved ∈ configuration.1.erase source) := membership.2.1
  have branchValue := runBasis_columnEventBranchCompute_branch_canonical p slot
    offset afterMembership membership.2.2.scratch_zero afterBranchZero
  rw [branchValue]
  by_cases collision : offset.val % 2 = 1
  · simp [columnEventBranchControls, allWiresTrue, readWires, collision,
      afterLegal, afterSelected, afterPresent, afterDegree]
    rw [show afterMembership (oraclePresentOtherWire p) =
        decide (moveSite source
          (selectorDirection (selectorOfSlotOffset slot offset)) ∈
            configuration.1.erase source) by simpa [moved] using afterOther]
    simp [columnEventMembershipCondition, collision, Finset.mem_erase,
      moveSite_ne_self]
  · simp [columnEventBranchControls, allWiresTrue, readWires, collision,
      afterLegal, afterSelected, afterPresent]
    rw [show afterMembership (oracleAbsentWire p) =
        decide (moveSite source
          (selectorDirection (selectorOfSlotOffset slot offset)) ∉
            configuration.1) by simpa [moved] using afterAbsent]
    simp [columnEventMembershipCondition, collision]

/-- legal 制御が偽なら column event branch は受理されない。 -/
theorem runBasis_columnEventBranchCompute_false_of_legal
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (columnEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (legalFalse : input (oracleLegalWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_columnEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [columnEventBranchControls, allWiresTrue, readWires, legalFalse]

/-- selected 制御が偽なら selector 不一致・padding branch は受理されない。 -/
theorem runBasis_columnEventBranchCompute_false_of_selected
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (columnEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (selectedFalse : input (oracleSelectedWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_columnEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [columnEventBranchControls, allWiresTrue, readWires, selectedFalse]

/-- present 制御が偽なら範囲外 slot branch は受理されない。 -/
theorem runBasis_columnEventBranchCompute_false_of_present
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (columnEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (presentFalse : input (oraclePresentWireAt p slot) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_columnEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [columnEventBranchControls, allWiresTrue, readWires, presentFalse]

/-- replacement で absent 制御が偽なら偽 successor branch は受理されない。 -/
theorem runBasis_columnEventBranchCompute_false_of_absent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (columnEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (replacement : offset.val % 2 ≠ 1)
    (absentFalse : input (oracleAbsentWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_columnEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [columnEventBranchControls, replacement, allWiresTrue, readWires,
    absentFalse]

/-- collision で present-other 制御が偽なら偽 successor branch は受理されない。 -/
theorem runBasis_columnEventBranchCompute_false_of_presentOther
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (columnEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (collision : offset.val % 2 = 1)
    (presentOtherFalse : input (oraclePresentOtherWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_columnEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [columnEventBranchControls, collision, allWiresTrue, readWires,
    presentOtherFalse]

/-- collision で degree 条件が偽なら境界外 branch は受理されない。 -/
theorem runBasis_columnEventBranchCompute_false_of_degree
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (columnEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (collision : offset.val % 2 = 1)
    (degreeFalse : input (oracleDegreeConditionWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_columnEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [columnEventBranchControls, collision, allWiresTrue, readWires,
    degreeFalse]

/-- canonical 配置では legal 制御が偽なら branch bit も偽である。 -/
theorem runBasis_columnEventBranchCompute_false_of_legal_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (legalFalse : input (oracleLegalWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_columnEventBranchCompute_false_of_legal p slot offset input
    (columnEventBranchControls_layout_canonical p slot offset) scratchZero
      branchZero legalFalse

/-- canonical 配置では selected 制御が偽なら branch bit も偽である。 -/
theorem runBasis_columnEventBranchCompute_false_of_selected_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (selectedFalse : input (oracleSelectedWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_columnEventBranchCompute_false_of_selected p slot offset input
    (columnEventBranchControls_layout_canonical p slot offset) scratchZero
      branchZero selectedFalse

/-- canonical 配置では present 制御が偽なら branch bit も偽である。 -/
theorem runBasis_columnEventBranchCompute_false_of_present_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (presentFalse : input (oraclePresentWireAt p slot) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_columnEventBranchCompute_false_of_present p slot offset input
    (columnEventBranchControls_layout_canonical p slot offset) scratchZero
      branchZero presentFalse

/-- canonical replacement では absent 制御が偽なら branch bit も偽である。 -/
theorem runBasis_columnEventBranchCompute_false_of_absent_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (replacement : offset.val % 2 ≠ 1)
    (absentFalse : input (oracleAbsentWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_columnEventBranchCompute_false_of_absent p slot offset input
    (columnEventBranchControls_layout_canonical p slot offset) scratchZero
      branchZero replacement absentFalse

/-- canonical collision では present-other 制御が偽なら branch bit も偽である。 -/
theorem runBasis_columnEventBranchCompute_false_of_presentOther_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (collision : offset.val % 2 = 1)
    (presentOtherFalse : input (oraclePresentOtherWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_columnEventBranchCompute_false_of_presentOther p slot offset
    input (columnEventBranchControls_layout_canonical p slot offset)
      scratchZero branchZero collision presentOtherFalse

/-- canonical collision では degree 条件が偽なら branch bit も偽である。 -/
theorem runBasis_columnEventBranchCompute_false_of_degree_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (collision : offset.val % 2 = 1)
    (degreeFalse : input (oracleDegreeConditionWire p) = false) :
    (columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_columnEventBranchCompute_false_of_degree p slot offset input
    (columnEventBranchControls_layout_canonical p slot offset) scratchZero
      branchZero collision degreeFalse

/-- 選択 source candidate を削除する制御 XOR 回路。 -/
def columnEventRemoveSource (p : QParameters) (slot : Fin p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  controlledXorCopy (oracleBranchWire p)
    (registerWordAt p (columnKeyWires p) slot)
    ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth)

/-- branch wire は任意 candidate data word の外にある。 -/
theorem columnOracleBranchWire_not_mem_candidateData
    (p : QParameters) (word : Fin p.sortWordCount) :
    oracleBranchWire p ∉ (candidateWordAt p word).take p.wordWidth := by
  let candidateSlice :=
    QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  let branchSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).branch
  have separated :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [candidateSlice, branchSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  intro candidateMember
  have candidateFull : oracleBranchWire p ∈
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    candidateWordAt_mem_candidateSlice p word
      (List.mem_of_mem_take candidateMember)
  have branchMember : oracleBranchWire p ∈
      (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change branchSlice.ancillaWire 0 ∈ _
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  exact (List.disjoint_left.mp separated) candidateFull branchMember

/-- branch wire は moved word の外にある。 -/
theorem columnOracleBranchWire_not_mem_moved (p : QParameters) :
    oracleBranchWire p ∉ oracleMovedWires p := by
  let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
  let branchSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).branch
  have separated :
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [movedSlice, branchSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  intro movedMember
  have movedFull : oracleBranchWire p ∈
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using movedMember
  have branchMember : oracleBranchWire p ∈
      (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change branchSlice.ancillaWire 0 ∈ _
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  exact (List.disjoint_left.mp separated) movedFull branchMember

/-- moved word と任意 candidate data word は交わらない。 -/
theorem columnOracleMoved_disjoint_candidateData
    (p : QParameters) (word : Fin p.sortWordCount) :
    (oracleMovedWires p).Disjoint
      ((candidateWordAt p word).take p.wordWidth) := by
  let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
  let candidateSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  have separated :
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [movedSlice, candidateSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  rw [List.disjoint_left]
  intro wire movedMember candidateMember
  have movedFull : wire ∈
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using movedMember
  have candidateFull : wire ∈
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    candidateWordAt_mem_candidateSlice p word
      (List.mem_of_mem_take candidateMember)
  exact (List.disjoint_left.mp separated) movedFull candidateFull

/-- column-key slot word と任意 candidate data word は交わらない。 -/
theorem columnKeyRegisterWord_disjoint_candidateData
    (p : QParameters) (slot : Fin p.K) (word : Fin p.sortWordCount) :
    (registerWordAt p (columnKeyWires p) slot).Disjoint
      ((candidateWordAt p word).take p.wordWidth) := by
  rw [List.disjoint_left]
  intro wire keyMember candidateMember
  have keyFull : wire ∈ columnKeyWires p :=
    mem_register_of_mem_registerWordAt p (columnKeyWires p) slot keyMember
  have candidateFull : wire ∈
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
    candidateWordAt_mem_candidateSlice p word
      (List.mem_of_mem_take candidateMember)
  exact (List.disjoint_left.mp
    (columnKeyWires_candidateInputLayout p).disjoint_candidate)
      keyFull candidateFull

/-- 同一 bit 列どうしの bitwise XOR は同じ長さの全 0 列である。 -/
theorem columnCandidateZipWithXorSelf (bits : List Bool) :
    List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        bits bits = List.replicate bits.length false := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      change (if bit then !bit else bit) ::
          List.zipWith
            (fun sourceBit targetBit =>
              if sourceBit then !targetBit else targetBit) bits bits =
        false :: List.replicate bits.length false
      rw [inductionHypothesis]
      cases bit <;> rfl

/-- replacement または collision に応じて選択 candidate を変更する回路。 -/
def controlledUpdateSelectedColumnCandidateWordCircuit (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  if offset.val % 2 = 1 then
    .seq (columnEventRemoveSource p slot) <|
      safeCnot (oracleBranchWire p)
        (candidateMarkerWire p (slotToSortWord p slot))
  else
    .seq (columnEventRemoveSource p slot) <|
      controlledXorCopy (oracleBranchWire p) (oracleMovedWires p)
        ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth)

/--
有効な replacement 変更回路は、選択 candidate data を source から moved site へ
厳密に置き換える。
-/
theorem runBasis_columnEventModify_replacement_target
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (replacement : offset.val % 2 ≠ 1)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (source moved : QSite p)
    (branchTrue : input (oracleBranchWire p) = true)
    (keyRead : readWires (registerWordAt p (columnKeyWires p) slot) input =
      siteWordBits p source)
    (candidateRead : readWires
      ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth) input =
        siteWordBits p source)
    (movedRead : readWires (oracleMovedWires p) input =
      siteWordBits p moved) :
    readWires ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth)
        ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
          reversibleGatePermutation input) = siteWordBits p moved := by
  let keyWord := registerWordAt p (columnKeyWires p) slot
  let candidateData :=
    (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let branch := oracleBranchWire p
  let afterRemove := (controlledXorCopy branch keyWord candidateData).runBasis
    reversibleGatePermutation input
  have keyLength : keyWord.length = candidateData.length := by
    rw [show keyWord.length = p.wordWidth by
      exact registerWordAt_length p (columnKeyWires p)
        (by simp [columnKeyWires]) slot]
    simp [candidateData]
  have movedLength : (oracleMovedWires p).length = candidateData.length := by
    simp [oracleMovedWires, QParameters.movedWidth, candidateData]
  have keyDisjoint : keyWord.Disjoint candidateData :=
    columnKeyRegisterWord_disjoint_candidateData p slot (slotToSortWord p slot)
  have movedDisjoint : (oracleMovedWires p).Disjoint candidateData :=
    columnOracleMoved_disjoint_candidateData p (slotToSortWord p slot)
  have branchAbsentKey : branch ∉ keyWord := by
    intro member
    exact oracleBranchWire_not_mem_columnKeyWires p
      (mem_register_of_mem_registerWordAt p (columnKeyWires p) slot member)
  have branchAbsentCandidate : branch ∉ candidateData :=
    columnOracleBranchWire_not_mem_candidateData p (slotToSortWord p slot)
  have branchAbsentMoved : branch ∉ oracleMovedWires p :=
    columnOracleBranchWire_not_mem_moved p
  have candidateNodup : candidateData.Nodup :=
    (candidateWordAt_nodup p (slotToSortWord p slot)).take
  have keyNodup : keyWord.Nodup := by
    dsimp [keyWord, registerWordAt]
    exact (columnKeyWires_nodup p).drop.take
  have movedNodup : (oracleMovedWires p).Nodup :=
    (columnEventMoveLayout_canonical p slot offset).moved_nodup
  have removedRead : readWires candidateData afterRemove =
      List.replicate p.wordWidth false := by
    have result := readWires_validatedControlledXorCopyLists_target branch
      keyWord candidateData input keyNodup candidateNodup keyLength keyDisjoint
      branchAbsentKey branchAbsentCandidate
    rw [branchTrue, keyRead, candidateRead] at result
    simpa [keyWord, candidateData] using
      result.trans (columnCandidateZipWithXorSelf (siteWordBits p source))
  have branchAfter : afterRemove branch = true := by
    dsimp only [afterRemove]
    rw [runBasis_validatedControlledXorCopyLists_outside branch keyWord
      candidateData input keyNodup candidateNodup keyLength keyDisjoint
      branchAbsentKey branchAbsentCandidate branch branchAbsentCandidate]
    exact branchTrue
  have movedAfter : readWires (oracleMovedWires p) afterRemove =
      siteWordBits p moved := by
    rw [readWires_validatedControlledXorCopyLists_outside branch keyWord
      candidateData (oracleMovedWires p) input keyNodup candidateNodup keyLength
      keyDisjoint branchAbsentKey branchAbsentCandidate movedDisjoint]
    exact movedRead
  rw [controlledUpdateSelectedColumnCandidateWordCircuit, if_neg replacement, runBasis_seq]
  change readWires candidateData
    ((controlledXorCopy branch (oracleMovedWires p) candidateData).runBasis
      reversibleGatePermutation afterRemove) = _
  rw [readWires_validatedControlledXorCopyLists_target branch
    (oracleMovedWires p) candidateData afterRemove movedNodup candidateNodup
    movedLength movedDisjoint branchAbsentMoved branchAbsentCandidate]
  rw [branchAfter, movedAfter, removedRead]
  simpa using candidateZipWithXorFalse (siteWordBits p moved)

/-- replacement 変更回路は選択 candidate data 外の任意 wire を保存する。 -/
theorem runBasis_columnEventModify_replacement_outside
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (replacement : offset.val % 2 ≠ 1)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉
      (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth) :
    (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
        reversibleGatePermutation input wire = input wire := by
  let keyWord := registerWordAt p (columnKeyWires p) slot
  let candidateData :=
    (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let branch := oracleBranchWire p
  let afterRemove := (controlledXorCopy branch keyWord candidateData).runBasis
    reversibleGatePermutation input
  have keyLength : keyWord.length = candidateData.length := by
    rw [show keyWord.length = p.wordWidth by
      exact registerWordAt_length p (columnKeyWires p)
        (by simp [columnKeyWires]) slot]
    simp [candidateData]
  have movedLength : (oracleMovedWires p).length = candidateData.length := by
    simp [oracleMovedWires, QParameters.movedWidth, candidateData]
  have keyDisjoint : keyWord.Disjoint candidateData :=
    columnKeyRegisterWord_disjoint_candidateData p slot (slotToSortWord p slot)
  have movedDisjoint : (oracleMovedWires p).Disjoint candidateData :=
    columnOracleMoved_disjoint_candidateData p (slotToSortWord p slot)
  have branchAbsentKey : branch ∉ keyWord := by
    intro member
    exact oracleBranchWire_not_mem_columnKeyWires p
      (mem_register_of_mem_registerWordAt p (columnKeyWires p) slot member)
  have branchAbsentCandidate : branch ∉ candidateData :=
    columnOracleBranchWire_not_mem_candidateData p (slotToSortWord p slot)
  have branchAbsentMoved : branch ∉ oracleMovedWires p :=
    columnOracleBranchWire_not_mem_moved p
  have candidateNodup : candidateData.Nodup :=
    (candidateWordAt_nodup p (slotToSortWord p slot)).take
  have keyNodup : keyWord.Nodup := by
    dsimp [keyWord, registerWordAt]
    exact (columnKeyWires_nodup p).drop.take
  have movedNodup : (oracleMovedWires p).Nodup :=
    (columnEventMoveLayout_canonical p slot offset).moved_nodup
  rw [controlledUpdateSelectedColumnCandidateWordCircuit, if_neg replacement, runBasis_seq]
  change (controlledXorCopy branch (oracleMovedWires p) candidateData).runBasis
      reversibleGatePermutation afterRemove wire = input wire
  rw [runBasis_validatedControlledXorCopyLists_outside branch
    (oracleMovedWires p) candidateData afterRemove movedNodup candidateNodup
    movedLength movedDisjoint branchAbsentMoved branchAbsentCandidate wire outside]
  exact runBasis_validatedControlledXorCopyLists_outside branch keyWord
    candidateData input keyNodup candidateNodup keyLength keyDisjoint
    branchAbsentKey branchAbsentCandidate wire outside

/--
有効 replacement branch では、変更後 candidate 値は選択 slot だけ moved 値となり、
他の全 word は入力配置の canonical 値を保つ。
-/
theorem qCandidateValue_runBasis_columnEventModify_replacement
    (p : QParameters) (configuration : QConfiguration p)
    (source moved : QSite p) (slot : Fin p.K)
    (active : slot.val < configuration.1.card)
    (offset : Fin 6) (replacement : offset.val % 2 ≠ 1)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration moved input)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (branchTrue : input (oracleBranchWire p) = true)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source) :
    qCandidateValue p
        ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
          reversibleGatePermutation input) =
      fun word => if word = slotToSortWord p slot then moved.val
        else configurationCandidateValue p configuration word := by
  let selectedWord := slotToSortWord p slot
  let output := (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
    reversibleGatePermutation input
  have keyRead : readWires (registerWordAt p (columnKeyWires p) slot) input =
      siteWordBits p source := by
    rw [← sourceAt]
    exact specification.active_word slot active
  have selectedActive : selectedWord.val < configuration.1.card := active
  have candidateRead : readWires
      ((candidateWordAt p selectedWord).take p.wordWidth) input =
        siteWordBits p source := by
    rw [← sourceAt]
    exact candidateData_eq_siteWordBits_of_value_eq p configuration input
      valuesBefore selectedWord selectedActive
  have targetRead : readWires
      ((candidateWordAt p selectedWord).take p.wordWidth) output =
        siteWordBits p moved := by
    exact runBasis_columnEventModify_replacement_target p slot offset replacement
      input source moved branchTrue keyRead candidateRead specification.moved_word
  have markerBefore : input (candidateMarkerWire p selectedWord) = false :=
    candidateMarker_false_of_value_eq p configuration input valuesBefore
      selectedWord selectedActive
  have markerAfter : output (candidateMarkerWire p selectedWord) = false := by
    exact (runBasis_columnEventModify_replacement_outside p slot offset
      replacement input (candidateMarkerWire p selectedWord)
      (candidateMarkerWire_not_mem_data p selectedWord)).trans markerBefore
  funext word
  by_cases selected : word = selectedWord
  · subst word
    rw [if_pos rfl]
    rw [qCandidateValue_eq_of_data_marker p output selectedWord
      (siteWordBits p moved) false targetRead markerAfter]
    simp [littleEndianNat_append, littleEndianNat_siteWordBits, littleEndianNat]
  · rw [if_neg selected]
    have wordDisjointTarget : (candidateWordAt p word).Disjoint
        ((candidateWordAt p selectedWord).take p.wordWidth) := by
      rw [List.disjoint_left]
      intro wire wordMember targetMember
      exact (List.disjoint_left.mp
        (candidateWordAt_disjoint_of_ne p word selectedWord selected))
          wordMember (List.mem_of_mem_take targetMember)
    have wordRead : readWires (candidateWordAt p word) output =
        readWires (candidateWordAt p word) input := by
      apply List.map_congr_left
      intro wire wordMember
      exact runBasis_columnEventModify_replacement_outside p slot offset
        replacement input wire (fun targetMember =>
          (List.disjoint_left.mp wordDisjointTarget) wordMember targetMember)
    unfold qCandidateValue
    rw [wordRead]
    exact congrFun valuesBefore word

/--
非衝突 replacement では、実変更回路後の candidate 多重集合が更新配置の
canonical candidate 多重集合に一致する。
-/
theorem columnEventModify_replacement_valueCount
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (sourceMember : source ∈ configuration.1)
    (direction : QDirection)
    (noCollision : moveSite source direction ∉ configuration.1.erase source)
    (slot : Fin p.K) (active : slot.val < configuration.1.card)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source)
    (offset : Fin 6) (replacement : offset.val % 2 ≠ 1)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration (moveSite source direction) input)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (branchTrue : input (oracleBranchWire p) = true)
    (target : Nat) :
    finiteValueCount target
        (qCandidateValue p
          ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
            reversibleGatePermutation input)) =
      finiteValueCount target
        (configurationCandidateValue p
          (updateConfiguration configuration (source, direction))) := by
  let selectedWord := slotToSortWord p slot
  let moved := moveSite source direction
  have actualValues := qCandidateValue_runBasis_columnEventModify_replacement p
    configuration source moved slot active offset replacement input specification
      valuesBefore branchTrue sourceAt
  rw [actualValues]
  have oldAt : configurationCandidateValue p configuration selectedWord =
      source.val := by
    rw [configurationCandidateValue_active p configuration selectedWord active]
    exact congrArg Fin.val sourceAt
  have updateBalance := finiteValueCount_update_one_balance_general target
    (configurationCandidateValue p configuration) selectedWord moved.val
  rw [oldAt] at updateBalance
  by_cases below : target < 2 ^ p.wordWidth
  · let targetSite : QSite p := ⟨target, by
      have capacity : p.G * p.G = 2 ^ p.wordWidth := by
        simp [QParameters.G, QParameters.wordWidth, two_mul, pow_add]
      simpa [capacity] using below⟩
    have physicalBalance :=
      finiteValueCount_configurationCandidateValue_noCollision_balance
        configuration (source, direction) sourceMember noCollision targetSite
    have targetEqSource : targetSite = source ↔ target = source.val := by
      constructor
      · intro equal
        exact congrArg Fin.val equal
      · intro equal
        exact Fin.ext equal
    have targetEqMoved : targetSite = moved ↔ target = moved.val := by
      constructor
      · intro equal
        exact congrArg Fin.val equal
      · intro equal
        exact Fin.ext equal
    change finiteValueCount target
          (configurationCandidateValue p
            (updateConfiguration configuration (source, direction))) +
          (if targetSite = source then 1 else 0) =
        finiteValueCount target (configurationCandidateValue p configuration) +
          (if targetSite = moved then 1 else 0) at physicalBalance
    simp only [targetEqSource, targetEqMoved] at physicalBalance
    have sourceIndicator :
        (if source.val = target then 1 else 0) =
          (if target = source.val then 1 else 0) := by
      by_cases equal : target = source.val <;> simp [equal, eq_comm]
    have movedIndicator :
        (if moved.val = target then 1 else 0) =
          (if target = moved.val then 1 else 0) := by
      by_cases equal : target = moved.val <;> simp [equal, eq_comm]
    rw [sourceIndicator, movedIndicator] at updateBalance
    exact Nat.add_right_cancel (updateBalance.trans physicalBalance.symm)
  · have markerOrAbove : 2 ^ p.wordWidth ≤ target := Nat.le_of_not_gt below
    by_cases marker : target = 2 ^ p.wordWidth
    · subst target
      have sourceBelow := qSite_val_lt_marker p source
      have movedBelow := qSite_val_lt_marker p moved
      simp [sourceBelow.ne, movedBelow.ne] at updateBalance
      rw [updateBalance]
      exact (finiteValueCount_configurationCandidateValue_noCollision_marker
        configuration (source, direction) sourceMember noCollision).symm
    · have above : 2 ^ p.wordWidth < target := by omega
      have sourceDifferent : source.val ≠ target :=
        Nat.ne_of_lt (lt_trans (qSite_val_lt_marker p source) above)
      have movedDifferent : moved.val ≠ target :=
        Nat.ne_of_lt (lt_trans (qSite_val_lt_marker p moved) above)
      simp [sourceDifferent, movedDifferent] at updateBalance
      rw [updateBalance,
        finiteValueCount_configurationCandidateValue_gt_marker p
          configuration target above,
        finiteValueCount_configurationCandidateValue_gt_marker p
          (updateConfiguration configuration (source, direction)) target above]

/--
非衝突 replacement の実変更回路と実 bitonic sort を合成すると、全 candidate 値は
更新配置の canonical 昇順関数に厳密一致する。
-/
theorem columnEventModify_replacement_sort_correct
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (sourceMember : source ∈ configuration.1)
    (direction : QDirection)
    (noCollision : moveSite source direction ∉ configuration.1.erase source)
    (slot : Fin p.K) (active : slot.val < configuration.1.card)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source)
    (offset : Fin 6) (replacement : offset.val % 2 ≠ 1)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration (moveSite source direction) input)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (branchTrue : input (oracleBranchWire p) = true)
    (flagsZero : readWires (sortCompareWorkWires p)
        ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
          reversibleGatePermutation input) =
      List.replicate (sortCompareWorkWires p).length false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p,
      ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
        reversibleGatePermutation input) wire = false)
    (historiesZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
        reversibleGatePermutation input)
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).sortFlags).ancillaWire
              instruction.history) = false) :
    qCandidateValue p
        ((reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
          ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
            reversibleGatePermutation input)) =
      configurationCandidateValue p
        (updateConfiguration configuration (source, direction)) := by
  let modified := (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
    reversibleGatePermutation input
  apply qBitonicSort_candidateValue_eq_configurationCandidateValue p
    (updateConfiguration configuration (source, direction)) modified flagsZero
      scratchZero historiesZero
  intro target
  exact columnEventModify_replacement_valueCount configuration source sourceMember
    direction noCollision slot active sourceAt offset replacement input
      specification valuesBefore branchTrue target

/-- branch wire と任意 candidate marker wire は異なる。 -/
theorem columnOracleBranchWire_ne_candidateMarker
    (p : QParameters) (word : Fin p.sortWordCount) :
    oracleBranchWire p ≠ candidateMarkerWire p word := by
  let candidateSlice :=
    QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  let branchSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).branch
  have separated :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [candidateSlice, branchSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  intro equal
  have markerMember : candidateMarkerWire p word ∈
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    candidateMarkerWire_mem_candidateSlice p word
  have branchMember : oracleBranchWire p ∈
      (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change branchSlice.ancillaWire 0 ∈ _
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  rw [← equal] at markerMember
  exact (List.disjoint_left.mp separated) markerMember branchMember

/--
有効 collision 変更回路は、選択 candidate data を全 0 にし marker を真にする。
-/
theorem runBasis_columnEventModify_collision_target
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (collision : offset.val % 2 = 1)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (source : QSite p)
    (branchTrue : input (oracleBranchWire p) = true)
    (keyRead : readWires (registerWordAt p (columnKeyWires p) slot) input =
      siteWordBits p source)
    (candidateRead : readWires
      ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth) input =
        siteWordBits p source)
    (markerFalse : input
      (candidateMarkerWire p (slotToSortWord p slot)) = false) :
    let output := (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
      reversibleGatePermutation input
    readWires ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth)
        output = List.replicate p.wordWidth false ∧
      output (candidateMarkerWire p (slotToSortWord p slot)) = true := by
  dsimp only
  let keyWord := registerWordAt p (columnKeyWires p) slot
  let selectedWord := slotToSortWord p slot
  let candidateData := (candidateWordAt p selectedWord).take p.wordWidth
  let marker := candidateMarkerWire p selectedWord
  let branch := oracleBranchWire p
  let afterRemove := (controlledXorCopy branch keyWord candidateData).runBasis
    reversibleGatePermutation input
  have keyLength : keyWord.length = candidateData.length := by
    rw [show keyWord.length = p.wordWidth by
      exact registerWordAt_length p (columnKeyWires p)
        (by simp [columnKeyWires]) slot]
    simp [candidateData]
  have keyDisjoint : keyWord.Disjoint candidateData :=
    columnKeyRegisterWord_disjoint_candidateData p slot selectedWord
  have branchAbsentKey : branch ∉ keyWord := by
    intro member
    exact oracleBranchWire_not_mem_columnKeyWires p
      (mem_register_of_mem_registerWordAt p (columnKeyWires p) slot member)
  have branchAbsentCandidate : branch ∉ candidateData :=
    columnOracleBranchWire_not_mem_candidateData p selectedWord
  have candidateNodup : candidateData.Nodup :=
    (candidateWordAt_nodup p selectedWord).take
  have keyNodup : keyWord.Nodup := by
    dsimp [keyWord, registerWordAt]
    exact (columnKeyWires_nodup p).drop.take
  have removedRead : readWires candidateData afterRemove =
      List.replicate p.wordWidth false := by
    have result := readWires_validatedControlledXorCopyLists_target branch
      keyWord candidateData input keyNodup candidateNodup keyLength keyDisjoint
      branchAbsentKey branchAbsentCandidate
    rw [branchTrue, keyRead, candidateRead] at result
    simpa [keyWord, candidateData, selectedWord] using
      result.trans (columnCandidateZipWithXorSelf (siteWordBits p source))
  have branchAfter : afterRemove branch = true := by
    dsimp only [afterRemove]
    rw [runBasis_validatedControlledXorCopyLists_outside branch keyWord
      candidateData input keyNodup candidateNodup keyLength keyDisjoint
      branchAbsentKey branchAbsentCandidate branch branchAbsentCandidate]
    exact branchTrue
  have markerAfterRemove : afterRemove marker = false := by
    dsimp only [afterRemove]
    rw [runBasis_validatedControlledXorCopyLists_outside branch keyWord
      candidateData input keyNodup candidateNodup keyLength keyDisjoint
      branchAbsentKey branchAbsentCandidate marker
      (candidateMarkerWire_not_mem_data p selectedWord)]
    exact markerFalse
  rw [controlledUpdateSelectedColumnCandidateWordCircuit, if_pos collision, runBasis_seq]
  change readWires candidateData
      ((safeCnot branch marker).runBasis reversibleGatePermutation afterRemove) = _ ∧
    (safeCnot branch marker).runBasis reversibleGatePermutation afterRemove marker = true
  constructor
  · rw [readWires_safeCnot_of_target_not_mem branch marker candidateData
      afterRemove (by
        simpa [branch, marker, selectedWord] using
          columnOracleBranchWire_ne_candidateMarker p selectedWord)
      (candidateMarkerWire_not_mem_data p selectedWord)]
    exact removedRead
  · rw [runBasis_safeCnot branch marker (by
      simpa [branch, marker, selectedWord] using
        columnOracleBranchWire_ne_candidateMarker p selectedWord)]
    rw [cnotBasisAction_target, branchAfter, markerAfterRemove]
    rfl

/-- collision 変更回路は選択 candidate word 外の任意 wire を保存する。 -/
theorem runBasis_columnEventModify_collision_outside
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (collision : offset.val % 2 = 1)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideData : wire ∉
      (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth)
    (outsideMarker : wire ≠
      candidateMarkerWire p (slotToSortWord p slot)) :
    (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
        reversibleGatePermutation input wire = input wire := by
  let keyWord := registerWordAt p (columnKeyWires p) slot
  let selectedWord := slotToSortWord p slot
  let candidateData := (candidateWordAt p selectedWord).take p.wordWidth
  let marker := candidateMarkerWire p selectedWord
  let branch := oracleBranchWire p
  let afterRemove := (controlledXorCopy branch keyWord candidateData).runBasis
    reversibleGatePermutation input
  have keyLength : keyWord.length = candidateData.length := by
    rw [show keyWord.length = p.wordWidth by
      exact registerWordAt_length p (columnKeyWires p)
        (by simp [columnKeyWires]) slot]
    simp [candidateData]
  have keyDisjoint : keyWord.Disjoint candidateData :=
    columnKeyRegisterWord_disjoint_candidateData p slot selectedWord
  have branchAbsentKey : branch ∉ keyWord := by
    intro member
    exact oracleBranchWire_not_mem_columnKeyWires p
      (mem_register_of_mem_registerWordAt p (columnKeyWires p) slot member)
  have branchAbsentCandidate : branch ∉ candidateData :=
    columnOracleBranchWire_not_mem_candidateData p selectedWord
  have candidateNodup : candidateData.Nodup :=
    (candidateWordAt_nodup p selectedWord).take
  have keyNodup : keyWord.Nodup := by
    dsimp [keyWord, registerWordAt]
    exact (columnKeyWires_nodup p).drop.take
  rw [controlledUpdateSelectedColumnCandidateWordCircuit, if_pos collision, runBasis_seq]
  change (safeCnot branch marker).runBasis reversibleGatePermutation afterRemove
      wire = input wire
  rw [runBasis_safeCnot_outside branch marker wire (by
      simpa [branch, marker, selectedWord] using
        columnOracleBranchWire_ne_candidateMarker p selectedWord)
    (by simpa [marker, selectedWord] using outsideMarker) afterRemove]
  exact runBasis_validatedControlledXorCopyLists_outside branch keyWord
    candidateData input keyNodup candidateNodup keyLength keyDisjoint
    branchAbsentKey branchAbsentCandidate wire
      (by simpa [candidateData, selectedWord] using outsideData)

/--
有効 collision branch では、変更後 candidate 値は選択 slot だけ marker 値となり、
他の全 word は入力配置の canonical 値を保つ。
-/
theorem qCandidateValue_runBasis_columnEventModify_collision
    (p : QParameters) (configuration : QConfiguration p)
    (source : QSite p) (slot : Fin p.K)
    (active : slot.val < configuration.1.card)
    (offset : Fin 6) (collision : offset.val % 2 = 1)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration (moveSite source
        (selectorDirection (selectorOfSlotOffset slot offset))) input)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (branchTrue : input (oracleBranchWire p) = true)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source) :
    qCandidateValue p
        ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
          reversibleGatePermutation input) =
      fun word => if word = slotToSortWord p slot then 2 ^ p.wordWidth
        else configurationCandidateValue p configuration word := by
  let selectedWord := slotToSortWord p slot
  let output := (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
    reversibleGatePermutation input
  have keyRead : readWires (registerWordAt p (columnKeyWires p) slot) input =
      siteWordBits p source := by
    rw [← sourceAt]
    exact specification.active_word slot active
  have selectedActive : selectedWord.val < configuration.1.card := active
  have candidateRead : readWires
      ((candidateWordAt p selectedWord).take p.wordWidth) input =
        siteWordBits p source := by
    rw [← sourceAt]
    exact candidateData_eq_siteWordBits_of_value_eq p configuration input
      valuesBefore selectedWord selectedActive
  have markerBefore : input (candidateMarkerWire p selectedWord) = false :=
    candidateMarker_false_of_value_eq p configuration input valuesBefore
      selectedWord selectedActive
  have target := runBasis_columnEventModify_collision_target p slot offset collision
    input source branchTrue keyRead candidateRead markerBefore
  have targetData : readWires
      ((candidateWordAt p selectedWord).take p.wordWidth) output =
        List.replicate p.wordWidth false := target.1
  have targetMarker : output (candidateMarkerWire p selectedWord) = true := target.2
  funext word
  by_cases selected : word = selectedWord
  · subst word
    rw [if_pos rfl]
    rw [qCandidateValue_eq_of_data_marker p output selectedWord
      (List.replicate p.wordWidth false) true targetData targetMarker]
    simp [littleEndianNat_append, littleEndianNat]
  · rw [if_neg selected]
    have wordDisjoint : (candidateWordAt p word).Disjoint
        (candidateWordAt p selectedWord) :=
      candidateWordAt_disjoint_of_ne p word selectedWord selected
    have wordRead : readWires (candidateWordAt p word) output =
        readWires (candidateWordAt p word) input := by
      apply List.map_congr_left
      intro wire wordMember
      apply runBasis_columnEventModify_collision_outside p slot offset collision
        input wire
      · intro dataMember
        exact (List.disjoint_left.mp wordDisjoint) wordMember
          (List.mem_of_mem_take dataMember)
      · intro equal
        have markerMember : candidateMarkerWire p selectedWord ∈
            candidateWordAt p selectedWord := by
          simp [candidateMarkerWire, candidateWordAt]
        rw [equal] at wordMember
        exact (List.disjoint_left.mp wordDisjoint) wordMember markerMember
    unfold qCandidateValue
    rw [wordRead]
    exact congrFun valuesBefore word

/--
衝突 branch では、実変更回路後の candidate 多重集合が一粒子減った更新配置の
canonical candidate 多重集合に一致する。
-/
theorem columnEventModify_collision_valueCount
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (sourceMember : source ∈ configuration.1)
    (direction : QDirection)
    (physicalCollision : moveSite source direction ∈
      configuration.1.erase source)
    (slot : Fin p.K) (active : slot.val < configuration.1.card)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source)
    (offset : Fin 6) (collision : offset.val % 2 = 1)
    (directionAt : selectorDirection (selectorOfSlotOffset slot offset) = direction)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration (moveSite source direction) input)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (branchTrue : input (oracleBranchWire p) = true)
    (target : Nat) :
    finiteValueCount target
        (qCandidateValue p
          ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
            reversibleGatePermutation input)) =
      finiteValueCount target
        (configurationCandidateValue p
          (updateConfiguration configuration (source, direction))) := by
  let selectedWord := slotToSortWord p slot
  have specificationAtSelector : ConfigurationMembershipInput p
      (columnKeyWires p) configuration
      (moveSite source
        (selectorDirection (selectorOfSlotOffset slot offset))) input := by
    simpa [directionAt] using specification
  have actualValues := qCandidateValue_runBasis_columnEventModify_collision p
    configuration source slot active offset collision input specificationAtSelector
      valuesBefore branchTrue sourceAt
  rw [actualValues]
  have oldAt : configurationCandidateValue p configuration selectedWord =
      source.val := by
    rw [configurationCandidateValue_active p configuration selectedWord active]
    exact congrArg Fin.val sourceAt
  have updateBalance := finiteValueCount_update_one_balance_general target
    (configurationCandidateValue p configuration) selectedWord
      (2 ^ p.wordWidth)
  rw [oldAt] at updateBalance
  by_cases below : target < 2 ^ p.wordWidth
  · let targetSite : QSite p := ⟨target, by
      have capacity : p.G * p.G = 2 ^ p.wordWidth := by
        simp [QParameters.G, QParameters.wordWidth, two_mul, pow_add]
      simpa [capacity] using below⟩
    have physicalBalance :=
      finiteValueCount_configurationCandidateValue_collision_balance
        configuration (source, direction) sourceMember physicalCollision targetSite
    have targetEqSource : targetSite = source ↔ target = source.val := by
      constructor
      · intro equal
        exact congrArg Fin.val equal
      · intro equal
        exact Fin.ext equal
    change finiteValueCount target
          (configurationCandidateValue p
            (updateConfiguration configuration (source, direction))) +
          (if targetSite = source then 1 else 0) =
        finiteValueCount target (configurationCandidateValue p configuration)
        at physicalBalance
    simp only [targetEqSource] at physicalBalance
    have sourceIndicator :
        (if source.val = target then 1 else 0) =
          (if target = source.val then 1 else 0) := by
      by_cases equal : target = source.val <;> simp [equal, eq_comm]
    have markerDifferent : 2 ^ p.wordWidth ≠ target := by omega
    rw [sourceIndicator, if_neg markerDifferent] at updateBalance
    simp only [Nat.add_zero] at updateBalance
    exact Nat.add_right_cancel (updateBalance.trans physicalBalance.symm)
  · have markerOrAbove : 2 ^ p.wordWidth ≤ target := Nat.le_of_not_gt below
    by_cases marker : target = 2 ^ p.wordWidth
    · subst target
      have sourceBelow := qSite_val_lt_marker p source
      simp [sourceBelow.ne] at updateBalance
      rw [updateBalance]
      exact (finiteValueCount_configurationCandidateValue_collision_marker
        configuration (source, direction) sourceMember physicalCollision).symm
    · have above : 2 ^ p.wordWidth < target := by omega
      have sourceDifferent : source.val ≠ target :=
        Nat.ne_of_lt (lt_trans (qSite_val_lt_marker p source) above)
      have markerDifferent : 2 ^ p.wordWidth ≠ target := by omega
      simp [sourceDifferent, markerDifferent] at updateBalance
      rw [updateBalance,
        finiteValueCount_configurationCandidateValue_gt_marker p
          configuration target above,
        finiteValueCount_configurationCandidateValue_gt_marker p
          (updateConfiguration configuration (source, direction)) target above]

/--
衝突変更回路と実 bitonic sort を合成すると、全 candidate 値は更新配置の
canonical 昇順関数に厳密一致する。
-/
theorem columnEventModify_collision_sort_correct
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (sourceMember : source ∈ configuration.1)
    (direction : QDirection)
    (physicalCollision : moveSite source direction ∈
      configuration.1.erase source)
    (slot : Fin p.K) (active : slot.val < configuration.1.card)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source)
    (offset : Fin 6) (collision : offset.val % 2 = 1)
    (directionAt : selectorDirection (selectorOfSlotOffset slot offset) = direction)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration (moveSite source direction) input)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (branchTrue : input (oracleBranchWire p) = true)
    (flagsZero : readWires (sortCompareWorkWires p)
        ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
          reversibleGatePermutation input) =
      List.replicate (sortCompareWorkWires p).length false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p,
      ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
        reversibleGatePermutation input) wire = false)
    (historiesZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
        reversibleGatePermutation input)
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).sortFlags).ancillaWire
              instruction.history) = false) :
    qCandidateValue p
        ((reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
          ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
            reversibleGatePermutation input)) =
      configurationCandidateValue p
        (updateConfiguration configuration (source, direction)) := by
  let modified := (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
    reversibleGatePermutation input
  apply qBitonicSort_candidateValue_eq_configurationCandidateValue p
    (updateConfiguration configuration (source, direction)) modified flagsZero
      scratchZero historiesZero
  intro target
  exact columnEventModify_collision_valueCount configuration source sourceMember
    direction physicalCollision slot active sourceAt offset collision directionAt
      input specification valuesBefore branchTrue target

/-- column event 分岐の compute 部分全体。 -/
def computeColumnEventCandidateUpdateAndSortCircuit (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .seq (columnEventSelectorCompute p slot offset) <|
    .seq (columnEventMovedCopy p slot) <|
    .seq (columnEventMoveForward p offset) <|
    .seq (columnEventMembership p slot) <|
    .seq (columnEventBranchCompute p slot offset) <|
    .seq (xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)) <|
    .seq (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset) (reversiblySortCandidateWordsAndRestoreHistoryCircuit p)

/-- column event 分岐の use 部分全体。 -/
def xorColumnEventDelimiterAndSelectorIntoOutputsCircuit (p : QParameters) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .seq (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (rowOutputWires p)
      (by simp [rowOutputWires]) (activeWire p)
      (if offset.val % 2 = 1 then -1 else 0)) <|
    xorMovedMemberPositionIntoSelectorOutputCircuit p offset.val (selectorOutputWires p)

/-- 正本 column event AST は、明示した compute と use の C-U-U 合成である。 -/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_eq_computeUseUncompute
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    applyColumnEventReferenceAndRestoreWorkCircuit p slot offset =
      Circuit.computeUseUncompute id (computeColumnEventCandidateUpdateAndSortCircuit p slot offset)
        (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset) := by
  rfl

/-- column event compute の各段階を保持する、行列非展開な状態記録。 -/
structure ColumnEventComputedStates (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) where
  /-- selector 比較直後の状態。 -/
  afterSelector : JointBasis p.ancillaWidth p.systemWidth
  /-- source 複写と一歩移動の直後の状態。 -/
  afterMovedCopy : JointBasis p.ancillaWidth p.systemWidth
  /-- moved site を一歩進めた直後の状態。 -/
  afterMoveForward : JointBasis p.ancillaWidth p.systemWidth
  /-- membership 判定直後の状態。 -/
  afterMembership : JointBasis p.ancillaWidth p.systemWidth
  /-- branch bit 計算直後の状態。 -/
  afterBranch : JointBasis p.ancillaWidth p.systemWidth
  /-- candidate 準備直後の状態。 -/
  afterCandidates : JointBasis p.ancillaWidth p.systemWidth
  /-- candidate 変更直後の状態。 -/
  afterModify : JointBasis p.ancillaWidth p.systemWidth
  /-- bitonic sort 直後、すなわち compute 完了時の状態。 -/
  output : JointBasis p.ancillaWidth p.systemWidth
  /-- selector 段階は正本回路の基底作用である。 -/
  selector_eq : afterSelector =
    (columnEventSelectorCompute p slot offset).runBasis
      reversibleGatePermutation input
  /-- moved copy 段階は正本回路の基底作用である。 -/
  movedCopy_eq : afterMovedCopy =
    (columnEventMovedCopy p slot).runBasis
      reversibleGatePermutation afterSelector
  /-- forward move 段階は正本回路の基底作用である。 -/
  moveForward_eq : afterMoveForward =
    (columnEventMoveForward p offset).runBasis
      reversibleGatePermutation afterMovedCopy
  /-- membership 段階は正本回路の基底作用である。 -/
  membership_eq : afterMembership =
    (columnEventMembership p slot).runBasis
      reversibleGatePermutation afterMoveForward
  /-- branch 段階は正本回路の基底作用である。 -/
  branch_eq : afterBranch =
    (columnEventBranchCompute p slot offset).runBasis
      reversibleGatePermutation afterMembership
  /-- candidate 準備段階は正本回路の基底作用である。 -/
  candidates_eq : afterCandidates =
    (xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
      reversibleGatePermutation afterBranch
  /-- candidate 変更段階は正本回路の基底作用である。 -/
  modify_eq : afterModify =
    (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
      reversibleGatePermutation afterCandidates
  /-- sort 段階は正本回路の基底作用である。 -/
  sort_eq : output =
    (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
      reversibleGatePermutation afterModify

/-- 任意の基底入力に対する column event compute の正本状態記録。 -/
def columnEventCandidateUpdateAndSortExecutionTrace (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    ColumnEventComputedStates p slot offset input := by
  let afterSelector := (columnEventSelectorCompute p slot offset).runBasis
    reversibleGatePermutation input
  let afterMovedCopy := (columnEventMovedCopy p slot).runBasis
    reversibleGatePermutation afterSelector
  let afterMoveForward := (columnEventMoveForward p offset).runBasis
    reversibleGatePermutation afterMovedCopy
  let afterMembership := (columnEventMembership p slot).runBasis
    reversibleGatePermutation afterMoveForward
  let afterBranch := (columnEventBranchCompute p slot offset).runBasis
    reversibleGatePermutation afterMembership
  let afterCandidates :=
    (xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
      reversibleGatePermutation afterBranch
  let afterModify := (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
    reversibleGatePermutation afterCandidates
  let output := (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
    reversibleGatePermutation afterModify
  exact {
    afterSelector := afterSelector
    afterMovedCopy := afterMovedCopy
    afterMoveForward := afterMoveForward
    afterMembership := afterMembership
    afterBranch := afterBranch
    afterCandidates := afterCandidates
    afterModify := afterModify
    output := output
    selector_eq := rfl
    movedCopy_eq := rfl
    moveForward_eq := rfl
    membership_eq := rfl
    branch_eq := rfl
    candidates_eq := rfl
    modify_eq := rfl
    sort_eq := rfl }

/-- 状態記録の最終状態は column event compute 正本回路の実行結果に等しい。 -/
theorem columnEventCandidateUpdateAndSortExecutionTrace_output
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output =
      (computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis
        reversibleGatePermutation input := by
  rfl

/-- 制御が偽の sorted-data 有限 fold は入力状態を変更しない。 -/
theorem writeSortedCopyReference_fold_false
    (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K) :
    ∀ (slots : List (Fin outputDegree))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      slots.foldl (fun state candidateSlot =>
        writeSortedCopyReference p output outputDegree outputDegreeLe false
          candidateSlot state) input = input
  | [], _ => rfl
  | candidateSlot :: slots, input => by
      simp only [List.foldl_cons]
      rw [show writeSortedCopyReference p output outputDegree outputDegreeLe
          false candidateSlot input = input by
        simp [writeSortedCopyReference]]
      exact writeSortedCopyReference_fold_false p output outputDegree
        outputDegreeLe slots input

/-- 制御が偽の sorted-use 純粋参照作用は恒等作用である。 -/
theorem writeSortedUseReference_false
    (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    writeSortedUseReference p output outputLength outputActive outputDegree
      outputDegreeLe false input = input := by
  unfold writeSortedUseReference writeSortedDataReference
  rw [writeSortedCopyReference_fold_false p output outputDegree outputDegreeLe
    (List.finRange outputDegree) input]
  unfold toggleOutputIndexReference
  split <;> rfl

/-- branch flag が偽なら、一つの sorted degree 参照作用は恒等作用である。 -/
theorem writeSortedDegreeReference_branch_false
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchFalse : input (oracleBranchWire p) = false) :
    writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) degreeSlot degreeChange input = input := by
  unfold writeSortedDegreeReference
  by_cases valid : (1 : Int) ≤ Int.ofNat (degreeSlot.val + 1) + degreeChange ∧
      Int.ofNat (degreeSlot.val + 1) + degreeChange ≤ Int.ofNat p.K
  · rw [dif_pos valid]
    dsimp only
    rw [branchFalse, Bool.false_and]
    exact writeSortedUseReference_false p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) _ _ input
  · rw [dif_neg valid]

/-- branch flag が偽なら、全 degree の sorted 参照 fold は恒等作用である。 -/
theorem writeSortedDegreeReference_fold_branch_false
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeChange : Int) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      input (oracleBranchWire p) = false →
      slots.foldl (fun state degreeSlot =>
        writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
          (canonicalSortedOutputWires_length p kind)
          (canonicalSortedOutputActive p kind) degreeSlot degreeChange state) input =
        input
  | [], _, _ => rfl
  | degreeSlot :: slots, input, branchFalse => by
      simp only [List.foldl_cons]
      rw [writeSortedDegreeReference_branch_false p kind degreeSlot degreeChange
        input branchFalse]
      exact writeSortedDegreeReference_fold_branch_false p kind degreeChange
        slots input branchFalse

/-- clean work と偽 branch では、canonical sorted 出力の実回路は恒等作用である。 -/
theorem runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_identity_of_branch_false
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (branchFalse : input (oracleBranchWire p) = false) :
    (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) degreeChange).runBasis
        reversibleGatePermutation input = input := by
  rw [runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical p kind degreeChange input scratchZero
    pairZero]
  exact writeSortedDegreeReference_fold_branch_false p kind degreeChange
    (List.finRange p.K) input branchFalse

/-- branch flag が偽なら、moved-selector の純粋有限 fold は恒等作用である。 -/
theorem xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_branch_false
    (p : QParameters) (offset : Nat)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchFalse : input (oracleBranchWire p) = false) :
    ∀ (slots : List (Fin p.K)) (bits : List Bool),
      xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset slots input bits = bits
  | [], _ => rfl
  | slot :: slots, bits => by
      rw [xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_cons]
      rw [show movedSelectorSlotEnabled p slot input = false by
        simp [movedSelectorSlotEnabled, branchFalse]]
      simp
      exact xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_branch_false p offset input
        branchFalse slots bits

/-- 読出し列とその外側をともに保存する二状態は同一である。 -/
theorem basis_eq_of_readWires_eq_of_agreesOutside
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (left right : JointBasis ancillaQubits systemQubits)
    (readEqual : readWires wires left = readWires wires right)
    (outsideEqual : BasisAgreeOutside wires left right) :
    left = right := by
  funext wire
  by_cases member : wire ∈ wires
  · rcases List.mem_iff_getElem?.mp member with ⟨index, atIndex⟩
    have mapped := congrArg (fun bits => bits[index]?) readEqual
    simpa [readWires, List.getElem?_map, atIndex] using mapped
  · exact outsideEqual wire member

/-- clean work と偽 branch では、moved-selector 実回路全体は恒等作用である。 -/
theorem runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_identity_of_branch_false
    (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layouts : ∀ slot : Fin p.K,
      WriteMovedSelectorSlotLayout p slot outputSelector)
    (clean : WriteMovedSelectorSlotClean p input)
    (branchFalse : input (oracleBranchWire p) = false) :
    (xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector).runBasis
      reversibleGatePermutation input = input := by
  let result := runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitSlotList_correct p offset
    outputSelector input layouts clean (List.finRange p.K) input (by
      intro wire outside
      rfl)
  apply basis_eq_of_readWires_eq_of_agreesOutside outputSelector
  · rw [runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_slotFold]
    rw [result.1]
    exact xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_branch_false p offset input
      branchFalse (List.finRange p.K) (readWires outputSelector input)
  · rw [runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_slotFold]
    exact result.2

/--
偽 branch と clean な内部 work では、column event の use 部分全体が恒等作用である。
-/
theorem runBasis_xorColumnEventDelimiterAndSelectorIntoOutputsCircuit_identity_of_branch_false
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p input)
    (branchFalse : input (oracleBranchWire p) = false) :
    (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input = input := by
  rw [xorColumnEventDelimiterAndSelectorIntoOutputsCircuit, runBasis_seq]
  rw [show xorSortedCandidatesAsDelimiterIntoOutputCircuit p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (if offset.val % 2 = 1 then -1 else 0) =
      xorSortedCandidatesAsDelimiterIntoOutputCircuit p (canonicalSortedOutputWires p .rowOutput)
        (canonicalSortedOutputWires_length p .rowOutput)
        (canonicalSortedOutputActive p .rowOutput)
        (if offset.val % 2 = 1 then -1 else 0) by rfl]
  rw [runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_identity_of_branch_false p .rowOutput
    (if offset.val % 2 = 1 then -1 else 0) input scratchZero pairZero
    branchFalse]
  exact runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_identity_of_branch_false p offset.val
    (selectorOutputWires p) input
      (MovedMemberPositionSelectorOutputLayout_selectorOutput_canonical p)
      movedClean branchFalse

/--
compute 後の branch が偽なら、正本 column event C-U-U 全体は入力を厳密に復元する。
selector 不一致、padding、illegal、present 不一致、rep/coll 条件不一致は、各々
compute 後 branch が偽であることを示せばこの一つの API へ帰着できる。
-/
theorem runBasis_applyColumnEventReferenceAndRestoreWorkCircuit_identity_of_computed_branch_false
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis
        reversibleGatePermutation input wire = false)
    (pairZero :
      (computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input
        (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      ((computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis
        reversibleGatePermutation input))
    (branchFalse :
      (computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input
        (oracleBranchWire p) = false) :
    (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
      reversibleGatePermutation input = input := by
  rw [applyColumnEventReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
  apply Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl)
      (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset) input input
  change
    VerifiedCircuitCore.Circuit.runBasis reversibleGatePermutation
        (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset)
        (VerifiedCircuitCore.Circuit.runBasis reversibleGatePermutation
          (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) input) =
      VerifiedCircuitCore.Circuit.runBasis reversibleGatePermutation
        (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) input
  exact
    runBasis_xorColumnEventDelimiterAndSelectorIntoOutputsCircuit_identity_of_branch_false p offset
      ((computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis
        reversibleGatePermutation input) scratchZero pairZero movedClean branchFalse

end ReversibleCircuit

end ProbabilityGeneratorQProof
