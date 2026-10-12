import QLean.Generator.Implementation.QOracleEndToEnd

/-!
# column・row oracleの永続decoder部分

compact decoder、slot presence、degree条件、定数1の順に実行する
`computeSharedDecoderPresenceParityAndOneFlagsCircuit`を、system・column-keyの両入力配置で共通に検証する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- oracle present wire列の長さは`K`である。 -/
@[simp] theorem oraclePresentWires_length (p : QParameters) :
    (oraclePresentWires p).length = p.K := by
  simp [oraclePresentWires, QParameters.presentWidth]

/-- oracle present wire列には重複がない。 -/
theorem oraclePresentWires_nodup (p : QParameters) :
    (oraclePresentWires p).Nodup := by
  change (((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).present).wireList :
        List (Wire p.ancillaWidth p.systemWidth))).Nodup
  exact RegisterSlice.wireList_nodup _

/-- degree列とpresent列は互いに素である。 -/
theorem oracleDegreeWires_disjoint_presentWires (p : QParameters) :
    (oracleDegreeWires p).Disjoint (oraclePresentWires p) := by
  let degree := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
  let present := QLayout.oracleSlice (OracleWorkLayout.canonical p).present
  have separated : degree.start + p.degreeWidth ≤ present.start := by
    simp [degree, present, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
  have full :
      (degree.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (present.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    degree.wireList_disjoint_of_end_le_start present separated
  simpa [oracleDegreeWires, oraclePresentWires, RegisterSlice.wireList,
    degree, present] using full

/-- degree条件wireと定数1 wireをまとめた連続2-wire oracle slice。 -/
def oraclePersistentSpecialSlice (p : QParameters) :
    RegisterSlice p.oracleWorkWidth 2 :=
  ⟨p.degreeWidth + 1 + p.presentWidth, by
    simp [QParameters.oracleWorkWidth]
    omega⟩

/-- degree条件wireと定数1 wireの二要素列。 -/
def oraclePersistentSpecialWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  ((QLayout.oracleSlice (oraclePersistentSpecialSlice p)).wireList :
    List (Wire p.ancillaWidth p.systemWidth))

/-- degree条件wireは連続2-wire sliceの先頭に属する。 -/
theorem oracleDegreeConditionWire_mem_special (p : QParameters) :
    oracleDegreeConditionWire p ∈ oraclePersistentSpecialWires p := by
  apply List.mem_map.mpr
  refine ⟨(0 : Fin 2), List.mem_finRange _, ?_⟩
  rfl

/-- 定数1 wireは連続2-wire sliceの二番目に属する。 -/
theorem oracleOneWire_mem_special (p : QParameters) :
    oracleOneWire p ∈ oraclePersistentSpecialWires p := by
  apply List.mem_map.mpr
  refine ⟨(1 : Fin 2), List.mem_finRange _, ?_⟩
  rfl

/-- compact decoder入力に加え、永続出力wireとの非交差を持つ配置条件。 -/
structure OraclePersistentInputLayout (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth)) : Prop where
  /-- compact decoder自体の配置条件。 -/
  decoder : CompactDecoderInputLayout p inputWires
  /-- 入力registerとpresent列は互いに素である。 -/
  disjoint_present : inputWires.Disjoint (oraclePresentWires p)
  /-- 入力registerとdegree条件・定数1の二wireは互いに素である。 -/
  disjoint_special : inputWires.Disjoint (oraclePersistentSpecialWires p)

/-- 物理system registerは永続decoderの適正入力配置である。 -/
theorem systemWires_oraclePersistentInputLayout (p : QParameters) :
    OraclePersistentInputLayout p (systemWires p) where
  decoder := systemWires_compactDecoderInputLayout p
  disjoint_present := by
    change ((List.finRange p.systemWidth).map Wire.system).Disjoint
      (((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).present).wireList :
          List (Wire p.ancillaWidth p.systemWidth)))
    exact RegisterSlice.systemWires_disjoint_wireList _
  disjoint_special := by
    change ((List.finRange p.systemWidth).map Wire.system).Disjoint
      (((QLayout.oracleSlice (oraclePersistentSpecialSlice p)).wireList :
        List (Wire p.ancillaWidth p.systemWidth)))
    exact RegisterSlice.systemWires_disjoint_wireList _

/-- column-key registerも永続decoderの適正入力配置である。 -/
theorem columnKeyWires_oraclePersistentInputLayout (p : QParameters) :
    OraclePersistentInputLayout p (columnKeyWires p) where
  decoder := columnKeyWires_compactDecoderInputLayout p
  disjoint_present := by
    let present := (OracleWorkLayout.canonical p).present
    simpa [oraclePresentWires, RegisterSlice.wireList, present] using
      columnKeyWires_disjoint_oracleSlice p present
  disjoint_special := by
    simpa [oraclePersistentSpecialWires] using
      columnKeyWires_disjoint_oracleSlice p (oraclePersistentSpecialSlice p)

/-- 永続decoderへ渡す全補助wireが0であるという値条件。 -/
structure OraclePersistentCleanInput (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- compact decoderのclean条件。 -/
  decoder : CompactDecoderCleanInput p inputWires configuration input
  /-- present列は全0である。 -/
  present_zero : readWires (oraclePresentWires p) input =
    List.replicate (oraclePresentWires p).length false
  /-- degree条件・定数1の二wireは全0である。 -/
  special_zero : readWires (oraclePersistentSpecialWires p) input =
    List.replicate (oraclePersistentSpecialWires p).length false

/--
column selector外が全0背景と一致する基底では、COPY後も任意oracle sliceは全0である。
-/
theorem oracleSlice_zero_after_copy
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis)
    {width : Nat} (slice : RegisterSlice p.oracleWorkWidth width) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    ∀ wire ∈ ((QLayout.oracleSlice slice).wireList :
      List (Wire p.ancillaWidth p.systemWidth)), copied wire = false := by
  dsimp only
  let wires := ((QLayout.oracleSlice slice).wireList :
    List (Wire p.ancillaWidth p.systemWidth))
  have inputZero : ∀ wire ∈ wires, basis wire = false := by
    apply outsideColumnSelector_zero_on_disjoint p
      (delimiterEncoding configuration) basis outside wires
      (columnSelectorSlice_disjoint_oracleSlice p slice)
    intro wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl
  intro wire member
  rw [xorSystemIntoColumnKeyReversibleCircuit]
  rw [runBasis_validatedXorCopyLists_outside
    (topSystemWires p) (topColumnKeyWires p) basis
    (topSystemWires_nodup p) (topColumnKeyWires_nodup p) (by simp)
    (topSystemWires_disjoint_topColumnKeyWires p) wire]
  · exact inputZero wire member
  · intro keyMember
    have keyMember' : wire ∈ columnKeyWires p := by
      simpa [columnKeyWires_eq_topColumnKeyWires] using keyMember
    exact (List.disjoint_left.mp (columnKeyWires_disjoint_oracleSlice p slice)
      keyMember') (by simpa [wires] using member)

/-- COPY後のcolumn-key状態はoracle永続部の全clean条件を満たす。 -/
theorem xorSystemIntoColumnKey_persistentCleanInput
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    OraclePersistentCleanInput p (columnKeyWires p) configuration copied := by
  dsimp only
  let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
    reversibleGatePermutation basis
  refine {
    decoder := xorSystemIntoColumnKey_cleanInput p configuration basis outside
    present_zero := ?_
    special_zero := ?_ }
  · apply readWires_eq_replicate_false_of_forall
    let present := (OracleWorkLayout.canonical p).present
    simpa [oraclePresentWires, present, RegisterSlice.wireList, copied] using
      oracleSlice_zero_after_copy p configuration basis outside present
  · apply readWires_eq_replicate_false_of_forall
    simpa [oraclePersistentSpecialWires, copied] using
      oracleSlice_zero_after_copy p configuration basis outside
        (oraclePersistentSpecialSlice p)

/-- present列とdecoder suffixは互いに素である。 -/
theorem oraclePresentWires_disjoint_decoderSuffix (p : QParameters) :
    (oraclePresentWires p).Disjoint (decoderSuffixWires p) := by
  let present := QLayout.oracleSlice (OracleWorkLayout.canonical p).present
  let candidate := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  have separated : present.start + p.presentWidth ≤ candidate.start := by
    simp [present, candidate, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have full :
      (present.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (candidate.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    present.wireList_disjoint_of_end_le_start candidate separated
  rw [List.disjoint_left]
  intro wire presentMember suffixMember
  apply (List.disjoint_left.mp full)
  · simpa [oraclePresentWires, present, RegisterSlice.wireList] using presentMember
  · exact List.mem_of_mem_take suffixMember

/-- present列と比較work列は互いに素である。 -/
theorem oraclePresentWires_disjoint_compareWork (p : QParameters) :
    (oraclePresentWires p).Disjoint (oracleCompareWorkWires p) := by
  let present := QLayout.oracleSlice (OracleWorkLayout.canonical p).present
  let compare := QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork
  have separated : present.start + p.presentWidth ≤ compare.start := by
    simp [present, compare, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have full :
      (present.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compare.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    present.wireList_disjoint_of_end_le_start compare separated
  simpa [oraclePresentWires, oracleCompareWorkWires, present, compare,
    RegisterSlice.wireList] using
      full

/-- present列とAND work列は互いに素である。 -/
theorem oraclePresentWires_disjoint_andWork (p : QParameters) :
    (oraclePresentWires p).Disjoint (oracleAndWorkWires p) := by
  let present := QLayout.oracleSlice (OracleWorkLayout.canonical p).present
  let andWork := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have separated : present.start + p.presentWidth ≤ andWork.start := by
    simp [present, andWork, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have full :
      (present.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andWork.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    present.wireList_disjoint_of_end_le_start andWork separated
  simpa [oraclePresentWires, oracleAndWorkWires, present, andWork,
    RegisterSlice.wireList] using
      full

/-- present列の各wireはcompact decoderの局所support外にある。 -/
theorem oraclePresent_not_mem_decoderLegalitySupportFor
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires) :
    ∀ wire ∈ oraclePresentWires p,
      wire ∉ decoderLegalitySupportFor p inputWires := by
  intro wire presentMember supportMember
  have cases : wire ∈ inputWires ∨ wire ∈ decoderSuffixWires p ∨
      wire ∈ oracleDegreeWires p ∨ wire ∈ oracleCompareWorkWires p ∨
      wire ∈ oracleAndWorkWires p := by
    simpa only [decoderLegalitySupportFor, List.mem_append, or_assoc] using
      supportMember
  rcases cases with inputMember | suffixMember | degreeMember | compareMember |
    andMember
  · exact (List.disjoint_left.mp layout.disjoint_present inputMember) presentMember
  · exact (List.disjoint_left.mp (oraclePresentWires_disjoint_decoderSuffix p)
      presentMember) suffixMember
  · exact (List.disjoint_left.mp (oracleDegreeWires_disjoint_presentWires p)
      degreeMember) presentMember
  · exact (List.disjoint_left.mp (oraclePresentWires_disjoint_compareWork p)
      presentMember) compareMember
  · exact (List.disjoint_left.mp (oraclePresentWires_disjoint_andWork p)
      presentMember) andMember

/-- present列は保持用legal wireを含まない。 -/
theorem oraclePresentWire_ne_legal
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ oraclePresentWires p) :
    wire ≠ oracleLegalWire p := by
  let legal := QLayout.oracleSlice (OracleWorkLayout.canonical p).legal
  let present := QLayout.oracleSlice (OracleWorkLayout.canonical p).present
  have separated : legal.start + 1 ≤ present.start := by
    simp [legal, present, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
  have disjoint :
      (legal.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (present.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    legal.wireList_disjoint_of_end_le_start present separated
  have presentMember : wire ∈
      (present.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [oraclePresentWires, present, RegisterSlice.wireList] using member
  have legalMember : oracleLegalWire p ∈
      (legal.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [oracleLegalWire, legal, RegisterSlice.wireList]
  intro equal
  subst wire
  exact (List.disjoint_left.mp disjoint legalMember) presentMember

/-- compact decoder実行後も、cleanなpresent列は全0のまま保存される。 -/
theorem compactDecoder_present_zero
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input) :
    let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    readWires (oraclePresentWires p) decoded =
      List.replicate (oraclePresentWires p).length false := by
  dsimp only
  apply readWires_eq_replicate_false_of_forall
  intro wire member
  rw [xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_outside_of_input p inputWires
    layout.decoder input wire
    (oraclePresent_not_mem_decoderLegalitySupportFor p inputWires layout wire member)
    (oraclePresentWire_ne_legal p member)]
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
    (decoderSuffixWires p) (oracleDegreeWires p) wire input
    (by simp [layout.decoder.length_eq]) layout.decoder.disjoint_suffix
    layout.decoder.disjoint_degree
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p)]
  · exact pointwise_false_of_readWires_eq_replicate
      (oraclePresentWires p) input clean.present_zero wire member
  · exact (List.disjoint_left.mp layout.disjoint_present.symm member)
  · exact (List.disjoint_left.mp
      (oraclePresentWires_disjoint_decoderSuffix p) member)
  · exact (List.disjoint_left.mp
      (oracleDegreeWires_disjoint_presentWires p).symm member)

/-- 永続特殊2-wire sliceとdecoder suffixは互いに素である。 -/
theorem oraclePersistentSpecialWires_disjoint_decoderSuffix (p : QParameters) :
    (oraclePersistentSpecialWires p).Disjoint (decoderSuffixWires p) := by
  let special := QLayout.oracleSlice (oraclePersistentSpecialSlice p)
  let candidate := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  have separated : special.start + 2 ≤ candidate.start := by
    simp [special, candidate, oraclePersistentSpecialSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have full :
      (special.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (candidate.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    special.wireList_disjoint_of_end_le_start candidate separated
  rw [List.disjoint_left]
  intro wire specialMember suffixMember
  exact (List.disjoint_left.mp full
    (by simpa [oraclePersistentSpecialWires, special] using specialMember))
    (List.mem_of_mem_take suffixMember)

/-- 永続特殊2-wire sliceとdegree列は互いに素である。 -/
theorem oracleDegreeWires_disjoint_persistentSpecialWires (p : QParameters) :
    (oracleDegreeWires p).Disjoint (oraclePersistentSpecialWires p) := by
  let degree := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
  let special := QLayout.oracleSlice (oraclePersistentSpecialSlice p)
  have separated : degree.start + p.degreeWidth ≤ special.start := by
    simp [degree, special, oraclePersistentSpecialSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have full :
      (degree.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (special.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    degree.wireList_disjoint_of_end_le_start special separated
  simpa [oracleDegreeWires, oraclePersistentSpecialWires, degree, special,
    RegisterSlice.wireList] using full

/-- 永続特殊2-wire sliceと比較work列は互いに素である。 -/
theorem oraclePersistentSpecialWires_disjoint_compareWork (p : QParameters) :
    (oraclePersistentSpecialWires p).Disjoint (oracleCompareWorkWires p) := by
  let special := QLayout.oracleSlice (oraclePersistentSpecialSlice p)
  let compare := QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork
  have separated : special.start + 2 ≤ compare.start := by
    simp [special, compare, oraclePersistentSpecialSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have full :
      (special.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compare.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    special.wireList_disjoint_of_end_le_start compare separated
  simpa [oraclePersistentSpecialWires, oracleCompareWorkWires, special, compare,
    RegisterSlice.wireList] using full

/-- 永続特殊2-wire sliceとAND work列は互いに素である。 -/
theorem oraclePersistentSpecialWires_disjoint_andWork (p : QParameters) :
    (oraclePersistentSpecialWires p).Disjoint (oracleAndWorkWires p) := by
  let special := QLayout.oracleSlice (oraclePersistentSpecialSlice p)
  let andWork := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have separated : special.start + 2 ≤ andWork.start := by
    simp [special, andWork, oraclePersistentSpecialSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have full :
      (special.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andWork.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    special.wireList_disjoint_of_end_le_start andWork separated
  simpa [oraclePersistentSpecialWires, oracleAndWorkWires, special, andWork,
    RegisterSlice.wireList] using full

/-- 永続特殊2-wire sliceの各wireはcompact decoderの局所support外にある。 -/
theorem oraclePersistentSpecial_not_mem_decoderLegalitySupportFor
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires) :
    ∀ wire ∈ oraclePersistentSpecialWires p,
      wire ∉ decoderLegalitySupportFor p inputWires := by
  intro wire specialMember supportMember
  have cases : wire ∈ inputWires ∨ wire ∈ decoderSuffixWires p ∨
      wire ∈ oracleDegreeWires p ∨ wire ∈ oracleCompareWorkWires p ∨
      wire ∈ oracleAndWorkWires p := by
    simpa only [decoderLegalitySupportFor, List.mem_append, or_assoc] using
      supportMember
  rcases cases with inputMember | suffixMember | degreeMember | compareMember |
    andMember
  · exact (List.disjoint_left.mp layout.disjoint_special inputMember) specialMember
  · exact (List.disjoint_left.mp
      (oraclePersistentSpecialWires_disjoint_decoderSuffix p) specialMember)
      suffixMember
  · exact (List.disjoint_left.mp
      (oracleDegreeWires_disjoint_persistentSpecialWires p) degreeMember)
      specialMember
  · exact (List.disjoint_left.mp
      (oraclePersistentSpecialWires_disjoint_compareWork p) specialMember)
      compareMember
  · exact (List.disjoint_left.mp
      (oraclePersistentSpecialWires_disjoint_andWork p) specialMember) andMember

/-- 永続特殊2-wire sliceは保持用legal wireを含まない。 -/
theorem oraclePersistentSpecialWire_ne_legal
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ oraclePersistentSpecialWires p) :
    wire ≠ oracleLegalWire p := by
  let legal := QLayout.oracleSlice (OracleWorkLayout.canonical p).legal
  let special := QLayout.oracleSlice (oraclePersistentSpecialSlice p)
  have separated : legal.start + 1 ≤ special.start := by
    simp [legal, special, oraclePersistentSpecialSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have disjoint :
      (legal.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (special.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    legal.wireList_disjoint_of_end_le_start special separated
  have specialMember : wire ∈
      (special.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [oraclePersistentSpecialWires, special] using member
  have legalMember : oracleLegalWire p ∈
      (legal.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [oracleLegalWire, legal, RegisterSlice.wireList]
  intro equal
  subst wire
  exact (List.disjoint_left.mp disjoint legalMember) specialMember

/-- compact decoder実行後も永続特殊2-wire sliceは全0である。 -/
theorem compactDecoder_persistentSpecial_zero
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input) :
    let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    readWires (oraclePersistentSpecialWires p) decoded =
      List.replicate (oraclePersistentSpecialWires p).length false := by
  dsimp only
  apply readWires_eq_replicate_false_of_forall
  intro wire member
  rw [xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_outside_of_input p inputWires
    layout.decoder input wire
    (oraclePersistentSpecial_not_mem_decoderLegalitySupportFor p inputWires
      layout wire member)
    (oraclePersistentSpecialWire_ne_legal p member)]
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
    (decoderSuffixWires p) (oracleDegreeWires p) wire input
    (by simp [layout.decoder.length_eq]) layout.decoder.disjoint_suffix
    layout.decoder.disjoint_degree
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p)]
  · exact pointwise_false_of_readWires_eq_replicate
      (oraclePersistentSpecialWires p) input clean.special_zero wire member
  · exact (List.disjoint_left.mp layout.disjoint_special.symm member)
  · exact (List.disjoint_left.mp
      (oraclePersistentSpecialWires_disjoint_decoderSuffix p) member)
  · exact (List.disjoint_left.mp
      (oracleDegreeWires_disjoint_persistentSpecialWires p).symm member)

/-- slot presence実行後も永続特殊2-wire sliceは全0である。 -/
theorem oraclePersistentSpecial_zero_after_slot
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input) :
    let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    let presented := (slotPresenceCircuit (oracleDegreeWires p)
      (oraclePresentWires p)).runBasis reversibleGatePermutation decoded
    readWires (oraclePersistentSpecialWires p) presented =
      List.replicate (oraclePersistentSpecialWires p).length false := by
  dsimp only
  let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
    reversibleGatePermutation input
  calc
    readWires (oraclePersistentSpecialWires p)
        ((slotPresenceCircuit (oracleDegreeWires p)
          (oraclePresentWires p)).runBasis reversibleGatePermutation decoded) =
        readWires (oraclePersistentSpecialWires p) decoded := by
      apply List.map_congr_left
      intro wire member
      apply runBasis_xorDegreeSuffixParityIntoSlotPresenceCircuit_outside
        (oracleDegreeWires p) (oraclePresentWires p) 0 wire decoded
        (oracleDegreeWires_disjoint_presentWires p)
      intro presentMember
      have disjoint : (oraclePresentWires p).Disjoint
          (oraclePersistentSpecialWires p) := by
        let present := QLayout.oracleSlice (OracleWorkLayout.canonical p).present
        let special := QLayout.oracleSlice (oraclePersistentSpecialSlice p)
        have separated : present.start + p.presentWidth ≤ special.start := by
          simp [present, special, oraclePersistentSpecialSlice,
            QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical]
          omega
        simpa [oraclePresentWires, oraclePersistentSpecialWires, present, special,
          RegisterSlice.wireList] using
          (present.wireList_disjoint_of_end_le_start special separated :
            (present.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
              (special.wireList : List (Wire p.ancillaWidth p.systemWidth)))
      exact (List.disjoint_left.mp disjoint presentMember) member
    _ = List.replicate (oraclePersistentSpecialWires p).length false := by
      simpa [decoded] using compactDecoder_persistentSpecial_zero p inputWires
        layout configuration input clean

/-- degree条件wireと定数1 wireは異なる。 -/
theorem oracleDegreeConditionWire_ne_oneWire (p : QParameters) :
    oracleDegreeConditionWire p ≠ oracleOneWire p := by
  intro equal
  have values := congrArg wireNumber equal
  simp [oracleDegreeConditionWire, oracleOneWire, oracleSingletonWire,
    OracleWorkLayout.canonical, QLayout.oracleSlice, RegisterSlice.compose,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at values

/-- slot presence後のdegree条件wireは0である。 -/
theorem oracleDegreeCondition_zero_after_slot
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input) :
    let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    let presented := (slotPresenceCircuit (oracleDegreeWires p)
      (oraclePresentWires p)).runBasis reversibleGatePermutation decoded
    presented (oracleDegreeConditionWire p) = false := by
  dsimp only
  exact pointwise_false_of_readWires_eq_replicate
    (oraclePersistentSpecialWires p)
    ((slotPresenceCircuit (oracleDegreeWires p) (oraclePresentWires p)).runBasis
      reversibleGatePermutation
      ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input))
    (oraclePersistentSpecial_zero_after_slot p inputWires layout configuration
      input clean)
    (oracleDegreeConditionWire p) (oracleDegreeConditionWire_mem_special p)

/-- slot presence後の定数1 wireも0である。 -/
theorem oracleOne_zero_after_slot
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input) :
    let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    let presented := (slotPresenceCircuit (oracleDegreeWires p)
      (oraclePresentWires p)).runBasis reversibleGatePermutation decoded
    presented (oracleOneWire p) = false := by
  dsimp only
  exact pointwise_false_of_readWires_eq_replicate
    (oraclePersistentSpecialWires p)
    ((slotPresenceCircuit (oracleDegreeWires p) (oraclePresentWires p)).runBasis
      reversibleGatePermutation
      ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input))
    (oraclePersistentSpecial_zero_after_slot p inputWires layout configuration
      input clean)
    (oracleOneWire p) (oracleOneWire_mem_special p)

/-- 永続部のdegree条件CNOT列はone-hot degreeの指定部分のparityを書き込む。 -/
theorem oraclePersistent_degreeCondition_value
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input)
    (rowMode : Bool) :
    let degree := oracleDegreeWires p
    let sources := if rowMode then degree.take (p.K - 1) else degree.drop 1
    let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    let presented := (slotPresenceCircuit degree (oraclePresentWires p)).runBasis
      reversibleGatePermutation decoded
    let conditioned := (xorSourceParityIntoTargetCircuit sources
      (oracleDegreeConditionWire p)).runBasis reversibleGatePermutation presented
    conditioned (oracleDegreeConditionWire p) =
      boolParity (if rowMode then
        (degreeOneHotFrom p.K configuration.1.card 0).take (p.K - 1)
      else (degreeOneHotFrom p.K configuration.1.card 0).drop 1) := by
  dsimp only
  let degree := oracleDegreeWires p
  let sources := if rowMode then degree.take (p.K - 1) else degree.drop 1
  let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
    reversibleGatePermutation input
  let presented := (slotPresenceCircuit degree (oraclePresentWires p)).runBasis
    reversibleGatePermutation decoded
  have targetAbsentDegree : oracleDegreeConditionWire p ∉ degree := by
    intro degreeMember
    exact (List.disjoint_left.mp
      (oracleDegreeWires_disjoint_persistentSpecialWires p) degreeMember)
      (oracleDegreeConditionWire_mem_special p)
  have targetAbsentSources : oracleDegreeConditionWire p ∉ sources := by
    simp only [sources]
    split
    · intro member
      exact targetAbsentDegree (List.mem_of_mem_take member)
    · intro member
      exact targetAbsentDegree (List.mem_of_mem_drop member)
  rw [xorSourceParityIntoTargetCircuit_target_value sources (oracleDegreeConditionWire p)
    presented targetAbsentSources]
  · have degreeValues : readWires degree presented =
        degreeOneHotFrom p.K configuration.1.card 0 := by
      calc
        readWires degree presented = readWires degree decoded := by
          apply List.map_congr_left
          intro wire member
          apply runBasis_xorDegreeSuffixParityIntoSlotPresenceCircuit_outside degree (oraclePresentWires p) 0
            wire decoded (by simpa [degree] using
              oracleDegreeWires_disjoint_presentWires p)
          intro presentMember
          exact (List.disjoint_left.mp
            (oracleDegreeWires_disjoint_presentWires p)
            (by simpa [degree] using member)) presentMember
        _ = degreeOneHotFrom p.K configuration.1.card 0 := by
          simpa [degree, decoded] using
            xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_degree_of_clean p inputWires
              layout.decoder configuration input clean.decoder
    simp only [sources]
    split
    · rw [show readWires (degree.take (p.K - 1)) presented =
          (readWires degree presented).take (p.K - 1) by
        simp [readWires]]
      rw [degreeValues]
    · rw [show readWires (degree.drop 1) presented =
          (readWires degree presented).drop 1 by
        simp [readWires]]
      rw [degreeValues]
  · simpa [presented, decoded] using
      oracleDegreeCondition_zero_after_slot p inputWires layout configuration input clean

/-- degree条件CNOT列は定数1 wireを0のまま保存する。 -/
theorem oraclePersistent_one_zero_after_condition
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input)
    (rowMode : Bool) :
    let degree := oracleDegreeWires p
    let sources := if rowMode then degree.take (p.K - 1) else degree.drop 1
    let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    let presented := (slotPresenceCircuit degree (oraclePresentWires p)).runBasis
      reversibleGatePermutation decoded
    let conditioned := (xorSourceParityIntoTargetCircuit sources
      (oracleDegreeConditionWire p)).runBasis reversibleGatePermutation presented
    conditioned (oracleOneWire p) = false := by
  dsimp only
  let degree := oracleDegreeWires p
  let sources := if rowMode then degree.take (p.K - 1) else degree.drop 1
  let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
    reversibleGatePermutation input
  let presented := (slotPresenceCircuit degree (oraclePresentWires p)).runBasis
    reversibleGatePermutation decoded
  have targetAbsentDegree : oracleDegreeConditionWire p ∉ degree := by
    intro degreeMember
    exact (List.disjoint_left.mp
      (oracleDegreeWires_disjoint_persistentSpecialWires p) degreeMember)
      (oracleDegreeConditionWire_mem_special p)
  have targetAbsentSources : oracleDegreeConditionWire p ∉ sources := by
    simp only [sources]
    split
    · intro member
      exact targetAbsentDegree (List.mem_of_mem_take member)
    · intro member
      exact targetAbsentDegree (List.mem_of_mem_drop member)
  rw [runBasis_xorSourceParityIntoTargetCircuit_other sources (oracleDegreeConditionWire p)
    (oracleOneWire p) presented targetAbsentSources
    (oracleDegreeConditionWire_ne_oneWire p).symm]
  simpa [presented, decoded] using
    oracleOne_zero_after_slot p inputWires layout configuration input clean

/-- one-hot degree列の先頭`takeCount`要素は同じ開始degreeの短いone-hot列である。 -/
theorem degreeOneHotFrom_take_of_le
    (count particleCount degree takeCount : Nat) (takeLe : takeCount ≤ count) :
    (degreeOneHotFrom count particleCount degree).take takeCount =
      degreeOneHotFrom takeCount particleCount degree := by
  induction takeCount generalizing count degree with
  | zero => rfl
  | succ takeCount inductionHypothesis =>
      cases count with
      | zero => omega
      | succ count =>
          simp only [degreeOneHotFrom, List.take_succ_cons]
          rw [inductionHypothesis count (degree + 1) (by omega)]

/-- row modeのdegree条件parityは、粒子を一個追加できる`card < K`と一致する。 -/
theorem boolParity_degreeCondition_row
    (p : QParameters) (configuration : QConfiguration p) :
    boolParity ((degreeOneHotFrom p.K configuration.1.card 0).take (p.K - 1)) =
      decide (configuration.1.card < p.K) := by
  rw [degreeOneHotFrom_take_of_le p.K configuration.1.card 0 (p.K - 1)
    (Nat.sub_le _ _)]
  rw [boolParity_degreeOneHotFrom]
  by_cases room : configuration.1.card < p.K
  · have bound : configuration.1.card ≤ p.K - 1 := by omega
    have nonempty : configuration.1.Nonempty :=
      Finset.card_pos.mp configuration.2.1
    simp [room, bound, nonempty]
  · have notBound : ¬configuration.1.card ≤ p.K - 1 := by omega
    simp [room, notBound]

/-- column modeのdegree条件parityは、合体可能な`1 < card`と一致する。 -/
theorem boolParity_degreeCondition_column
    (p : QParameters) (configuration : QConfiguration p) :
    boolParity ((degreeOneHotFrom p.K configuration.1.card 0).drop 1) =
      decide (1 < configuration.1.card) := by
  rw [boolParity_degreeOneHotFrom_drop p.K configuration.1.card 0 1
    (by omega : 1 ≤ p.K)]
  by_cases collisionRoom : 1 < configuration.1.card
  · simp [collisionRoom, configuration.2.2]
  · simp [collisionRoom]

/-- slot presence実行後は、粒子数未満のslotだけが1になる。 -/
theorem oraclePersistent_present_after_slot
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input) :
    let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    let presented := (slotPresenceCircuit (oracleDegreeWires p)
      (oraclePresentWires p)).runBasis reversibleGatePermutation decoded
    readWires (oraclePresentWires p) presented =
      presenceBitsFrom p.K configuration.1.card 0 := by
  dsimp only
  let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
    reversibleGatePermutation input
  have degreeValues : readWires (oracleDegreeWires p) decoded =
      degreeOneHotFrom p.K configuration.1.card 0 := by
    simpa [decoded] using
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_degree_of_clean p inputWires
        layout.decoder configuration input clean.decoder)
  have degreeValuesLength : readWires (oracleDegreeWires p) decoded =
      degreeOneHotFrom (oracleDegreeWires p).length configuration.1.card 0 := by
    simpa using degreeValues
  have presentZero : readWires (oraclePresentWires p) decoded =
      List.replicate (oraclePresentWires p).length false := by
    simpa [decoded] using
      (compactDecoder_present_zero p inputWires layout configuration input clean)
  have result := readWires_slotPresenceCircuit_degreeOneHot
    (oracleDegreeWires p) (oraclePresentWires p) configuration.1.card decoded
    (oracleDegreeWires_disjoint_presentWires p)
    (oraclePresentWires_nodup p)
    degreeValuesLength presentZero
    (by simp)
    (by simpa [QParameters.degreeWidth] using configuration.2.2)
  simpa [decoded] using result

/-- slot presence回路はdegree one-hot列を変更しない。 -/
theorem oraclePersistent_degree_after_slot
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input) :
    let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    let presented := (slotPresenceCircuit (oracleDegreeWires p)
      (oraclePresentWires p)).runBasis reversibleGatePermutation decoded
    readWires (oracleDegreeWires p) presented =
      degreeOneHotFrom p.K configuration.1.card 0 := by
  dsimp only
  let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
    reversibleGatePermutation input
  calc
    readWires (oracleDegreeWires p)
        ((slotPresenceCircuit (oracleDegreeWires p)
          (oraclePresentWires p)).runBasis reversibleGatePermutation decoded) =
        readWires (oracleDegreeWires p) decoded := by
      apply List.map_congr_left
      intro wire member
      apply runBasis_xorDegreeSuffixParityIntoSlotPresenceCircuit_outside
        (oracleDegreeWires p) (oraclePresentWires p) 0 wire decoded
        (oracleDegreeWires_disjoint_presentWires p)
      intro presentMember
      exact (List.disjoint_left.mp (oracleDegreeWires_disjoint_presentWires p)
        member) presentMember
    _ = degreeOneHotFrom p.K configuration.1.card 0 := by
      simpa [decoded] using
        xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_degree_of_clean p inputWires
          layout.decoder configuration input clean.decoder

/-- XOR source回路は、標的を含まないwire列の読み出しを保存する。 -/
theorem readWires_xorSourceParityIntoTargetCircuit_other
    {ancillaQubits systemQubits : Nat}
    (sources : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (targetAbsentSources : target ∉ sources)
    (targetAbsentWires : target ∉ wires) :
    readWires wires
        ((xorSourceParityIntoTargetCircuit sources target).runBasis
          reversibleGatePermutation input) =
      readWires wires input := by
  apply List.map_congr_left
  intro wire member
  exact runBasis_xorSourceParityIntoTargetCircuit_other sources target wire input
    targetAbsentSources (by
      intro equal
      subst wire
      exact targetAbsentWires member)

/-- X作用は、標的を含まないwire列の読み出しを保存する。 -/
theorem readWires_xBasisAction_other
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (targetAbsent : target ∉ wires) :
    readWires wires (xBasisAction target input) = readWires wires input := by
  apply List.map_congr_left
  intro wire member
  exact xBasisAction_other target wire (by
    intro equal
    subst wire
    exact targetAbsent member) input

/-- 永続計算部が基底入力上で満たす、後続oracle用の完全な出力仕様。 -/
structure OraclePersistentOutputSpec (p : QParameters)
    (configuration : QConfiguration p) (rowMode : Bool)
    (output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- present列は占有slotだけを表す。 -/
  present : readWires (oraclePresentWires p) output =
    presenceBitsFrom p.K configuration.1.card 0
  /-- degree列は粒子数のone-hot符号である。 -/
  degree : readWires (oracleDegreeWires p) output =
    degreeOneHotFrom p.K configuration.1.card 0
  /-- delimiter合法性flagは真である。 -/
  legal : output (oracleLegalWire p) = true
  /-- degree条件はrow/column modeに応じた遷移可能性を表す。 -/
  degreeCondition : output (oracleDegreeConditionWire p) =
    if rowMode then decide (configuration.1.card < p.K)
    else decide (1 < configuration.1.card)
  /-- 定数1として使うwireは真である。 -/
  one : output (oracleOneWire p) = true

/-- degree条件用source列にdegree条件wire自身は含まれない。 -/
theorem oracleDegreeConditionWire_not_mem_degreeConditionSources
    (p : QParameters) (rowMode : Bool) :
    oracleDegreeConditionWire p ∉
      (if rowMode then (oracleDegreeWires p).take (p.K - 1)
      else (oracleDegreeWires p).drop 1) := by
  have absentDegree : oracleDegreeConditionWire p ∉ oracleDegreeWires p := by
    intro member
    exact (List.disjoint_left.mp
      (oracleDegreeWires_disjoint_persistentSpecialWires p) member)
      (oracleDegreeConditionWire_mem_special p)
  split
  · intro member
    exact absentDegree (List.mem_of_mem_take member)
  · intro member
    exact absentDegree (List.mem_of_mem_drop member)

/-- `computeSharedDecoderPresenceParityAndOneFlagsCircuit`は、cleanな合法delimiter入力から永続出力仕様を満たす。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_correct_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input)
    (rowMode : Bool) :
    OraclePersistentOutputSpec p configuration rowMode
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input) := by
  let degree := oracleDegreeWires p
  let present := oraclePresentWires p
  let condition := oracleDegreeConditionWire p
  let one := oracleOneWire p
  let sources := if rowMode then degree.take (p.K - 1) else degree.drop 1
  let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
    reversibleGatePermutation input
  let presented := (slotPresenceCircuit degree present).runBasis
    reversibleGatePermutation decoded
  let conditioned := (xorSourceParityIntoTargetCircuit sources condition).runBasis
    reversibleGatePermutation presented
  have outputEq :
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
          reversibleGatePermutation input =
        xBasisAction one conditioned := by
    simp only [computeSharedDecoderPresenceParityAndOneFlagsCircuit, runBasis_seq, runBasis_x]
    rfl
  have conditionAbsentSources : condition ∉ sources := by
    simpa [condition, sources, degree] using
      oracleDegreeConditionWire_not_mem_degreeConditionSources p rowMode
  have oneNeCondition : one ≠ condition := by
    simpa [one, condition] using (oracleDegreeConditionWire_ne_oneWire p).symm
  refine {
    present := ?_
    degree := ?_
    legal := ?_
    degreeCondition := ?_
    one := ?_ }
  · rw [outputEq]
    rw [readWires_xBasisAction_other one present conditioned]
    · rw [show readWires present conditioned = readWires present presented by
          exact readWires_xorSourceParityIntoTargetCircuit_other sources condition present presented
            conditionAbsentSources (by
              intro member
              have disjoint : (oraclePresentWires p).Disjoint
                  (oraclePersistentSpecialWires p) := by
                let presentSlice := QLayout.oracleSlice
                  (OracleWorkLayout.canonical p).present
                let specialSlice := QLayout.oracleSlice
                  (oraclePersistentSpecialSlice p)
                have separated : presentSlice.start + p.presentWidth ≤
                    specialSlice.start := by
                  simp [presentSlice, specialSlice, oraclePersistentSpecialSlice,
                    QLayout.oracleSlice, RegisterSlice.compose,
                    OracleWorkLayout.canonical]
                  omega
                simpa [oraclePresentWires, oraclePersistentSpecialWires,
                  presentSlice, specialSlice, RegisterSlice.wireList] using
                  (presentSlice.wireList_disjoint_of_end_le_start specialSlice separated :
                    (presentSlice.wireList :
                      List (Wire p.ancillaWidth p.systemWidth)).Disjoint
                      (specialSlice.wireList :
                        List (Wire p.ancillaWidth p.systemWidth)))
              exact (List.disjoint_left.mp disjoint member)
                (oracleDegreeConditionWire_mem_special p))]
      simpa [presented, decoded, present, degree] using
        oraclePersistent_present_after_slot p inputWires layout configuration
          input clean
    · intro member
      have disjoint : (oraclePresentWires p).Disjoint
          (oraclePersistentSpecialWires p) := by
        let presentSlice := QLayout.oracleSlice
          (OracleWorkLayout.canonical p).present
        let specialSlice := QLayout.oracleSlice (oraclePersistentSpecialSlice p)
        have separated : presentSlice.start + p.presentWidth ≤ specialSlice.start := by
          simp [presentSlice, specialSlice, oraclePersistentSpecialSlice,
            QLayout.oracleSlice, RegisterSlice.compose,
            OracleWorkLayout.canonical]
          omega
        simpa [oraclePresentWires, oraclePersistentSpecialWires,
          presentSlice, specialSlice, RegisterSlice.wireList] using
          (presentSlice.wireList_disjoint_of_end_le_start specialSlice separated :
            (presentSlice.wireList :
              List (Wire p.ancillaWidth p.systemWidth)).Disjoint
              (specialSlice.wireList :
                List (Wire p.ancillaWidth p.systemWidth)))
      exact (List.disjoint_left.mp disjoint member) (oracleOneWire_mem_special p)
  · rw [outputEq]
    rw [readWires_xBasisAction_other one degree conditioned]
    · rw [show readWires degree conditioned = readWires degree presented by
          exact readWires_xorSourceParityIntoTargetCircuit_other sources condition degree presented
            conditionAbsentSources (by
              intro member
              exact (List.disjoint_left.mp
                (oracleDegreeWires_disjoint_persistentSpecialWires p) member)
                (oracleDegreeConditionWire_mem_special p))]
      simpa [presented, decoded, degree, present] using
        oraclePersistent_degree_after_slot p inputWires layout configuration input clean
    · intro member
      exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_persistentSpecialWires p) member)
        (oracleOneWire_mem_special p)
  · rw [outputEq, xBasisAction_other one (oracleLegalWire p)]
    · change (xorSourceParityIntoTargetCircuit sources condition).runBasis
          reversibleGatePermutation presented (oracleLegalWire p) = true
      rw [runBasis_xorSourceParityIntoTargetCircuit_other sources condition
          (oracleLegalWire p) presented conditionAbsentSources]
      · change (xorDegreeSuffixParityIntoSlotPresenceCircuit degree 0 present).runBasis
            reversibleGatePermutation decoded (oracleLegalWire p) = true
        rw [runBasis_xorDegreeSuffixParityIntoSlotPresenceCircuit_outside degree present 0
            (oracleLegalWire p) decoded]
        · simpa [decoded] using
            xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_true_of_clean p inputWires
              layout.decoder configuration input clean.decoder
        · simpa [degree, present] using oracleDegreeWires_disjoint_presentWires p
        · intro member
          exact (oraclePresentWire_ne_legal p member) rfl
      · exact (oraclePersistentSpecialWire_ne_legal p
          (oracleDegreeConditionWire_mem_special p)).symm
    · exact (oraclePersistentSpecialWire_ne_legal p
        (oracleOneWire_mem_special p)).symm
  · rw [outputEq, xBasisAction_other one condition oneNeCondition.symm]
    have value := oraclePersistent_degreeCondition_value p inputWires layout
      configuration input clean rowMode
    change conditioned condition = _
    have value' : conditioned condition =
        boolParity (if rowMode then
          (degreeOneHotFrom p.K configuration.1.card 0).take (p.K - 1)
        else (degreeOneHotFrom p.K configuration.1.card 0).drop 1) := by
      simpa [conditioned, presented, decoded, sources, condition, degree, present]
        using value
    rw [value']
    split
    · exact boolParity_degreeCondition_row p configuration
    · exact boolParity_degreeCondition_column p configuration
  · rw [outputEq, xBasisAction_target]
    have zero := oraclePersistent_one_zero_after_condition p inputWires layout
      configuration input clean rowMode
    simpa [zero]

/-- 一様化後の各column-selector基底では、COPYに続くcolumn永続計算が仕様を満たす。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_column_after_copy_correct
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    OraclePersistentOutputSpec p configuration false
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation copied) := by
  dsimp only
  exact computeSharedDecoderPresenceParityAndOneFlagsCircuit_correct_of_clean p (columnKeyWires p)
    (columnKeyWires_oraclePersistentInputLayout p) configuration _
    (xorSystemIntoColumnKey_persistentCleanInput p configuration basis outside) false

/-- 全0 ancillaと合法system delimiterは、row永続計算のclean入力である。 -/
theorem zeroAncilla_system_oraclePersistentCleanInput
    (p : QParameters) (configuration : QConfiguration p) :
    OraclePersistentCleanInput p (systemWires p) configuration
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) := by
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  refine {
    decoder := {
      input_bits := ?_
      suffix_zero := ?_
      degree_zero := ?_
      compare_zero := ?_
      and_zero := ?_
      legal_zero := ?_ }
    present_zero := ?_
    special_zero := ?_ }
  · simpa [input] using readWires_systemWires_zeroAncilla p
      (delimiterEncoding configuration)
  · simpa [input] using readWires_decoderSuffix_zeroAncilla p
      (delimiterEncoding configuration)
  · simpa [input] using readWires_oracleDegree_zeroAncilla p
      (delimiterEncoding configuration)
  · simpa [input] using readWires_oracleCompare_zeroAncilla p
      (delimiterEncoding configuration)
  · intro wire member
    simpa [input] using zeroAncilla_oracleAndWork_member p
      (delimiterEncoding configuration) member
  · rfl
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl

/-- 全0 ancilla上の合法system delimiterでは、row永続計算が仕様を満たす。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_system_correct
    (p : QParameters) (configuration : QConfiguration p) :
    OraclePersistentOutputSpec p configuration true
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation
        (zeroAncillaJointBasis p (delimiterEncoding configuration))) := by
  exact computeSharedDecoderPresenceParityAndOneFlagsCircuit_correct_of_clean p (systemWires p)
    (systemWires_oraclePersistentInputLayout p) configuration _
    (zeroAncilla_system_oraclePersistentCleanInput p configuration) true

end ReversibleCircuit

end ProbabilityGeneratorQProof
