import QLean.Generator.Implementation.QWriteSortedOutputCorrectness
import QLean.Generator.Implementation.QEventLayoutBridge

/-!
# moved-selector の canonical 配置

row/column event が共有する moved-selector 回路について、正本 `QLayout` の slice 境界だけ
から静的配置条件を構成する。値に関する oracle 契約は仮定しない。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- oracle 内部 slice の任意の wire は、最上位 oracle-work slice 全体に属する。 -/
theorem oracleSliceWire_mem_oracleWork
    (p : QParameters) {width : Nat}
    (slice : RegisterSlice p.oracleWorkWidth width)
    {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ ((QLayout.oracleSlice slice).wireList :
      List (Wire p.ancillaWidth p.systemWidth))) :
    wire ∈ (((QLayout.canonical p).oracleWork.wireList) :
      List (Wire p.ancillaWidth p.systemWidth)) := by
  rcases List.mem_map.mp member with ⟨index, _indexMember, rfl⟩
  let outerIndex : Fin p.oracleWorkWidth :=
    ⟨slice.start + index.val, by
      have fits := slice.fits
      omega⟩
  apply List.mem_map.mpr
  refine ⟨outerIndex, List.mem_finRange _, ?_⟩
  apply congrArg Wire.ancilla
  apply Fin.ext
  simp [outerIndex, QLayout.oracleSlice, RegisterSlice.compose,
    RegisterSlice.index]
  omega

/-- moved-selector compute support は最上位 oracle-work slice 全体に含まれる。 -/
theorem xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport_subset_oracleWork
    (p : QParameters) (slot : Fin p.K)
    {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport p slot) :
    wire ∈ (((QLayout.canonical p).oracleWork.wireList) :
      List (Wire p.ancillaWidth p.systemWidth)) := by
  simp only [xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, List.mem_append] at member
  rcases member with
      (((movedMember | wordMember) | compareMember) | scratchMember) | lastMember
  · apply oracleSliceWire_mem_oracleWork p
      (OracleWorkLayout.canonical p).moved
    simpa [oracleMovedWires, RegisterSlice.wireList] using movedMember
  ·
    apply oracleSliceWire_mem_oracleWork p
      (OracleWorkLayout.canonical p).candidate
    exact candidateWordAt_mem_candidateSlice p (slotToSortWord p slot)
      (List.mem_of_mem_take wordMember)
  ·
    apply oracleSliceWire_mem_oracleWork p
      (OracleWorkLayout.canonical p).compareWork
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using compareMember
  ·
    apply oracleSliceWire_mem_oracleWork p
      (OracleWorkLayout.canonical p).andWork
    have andMember : wire ∈ oracleAndWorkWires p :=
      List.mem_of_mem_drop scratchMember
    simpa [oracleAndWorkWires, RegisterSlice.wireList] using andMember
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at lastMember
    rcases lastMember with branchMember | positionMember | markerMember | pairMember
    · subst wire
      apply oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).branch
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).branch).ancillaWire 0 ∈ _
      simp [RegisterSlice.wireList]
    · subst wire
      apply oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).positionMatch
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).positionMatch).ancillaWire _ ∈ _
      simp [RegisterSlice.wireList]
    · subst wire
      apply oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).candidate
      exact candidateMarkerWire_mem_candidateSlice p (slotToSortWord p slot)
    · subst wire
      apply oracleSliceWire_mem_oracleWork p
        (OracleWorkLayout.canonical p).pair
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).pair).ancillaWire _ ∈ _
      simp [RegisterSlice.wireList]

/--
oracle-work より前の canonical 出力 slice に対し、moved-selector の全静的配置条件は
外部仮定なしに成立する。
-/
theorem MovedMemberPositionSelectorOutputLayout_of_outputSlice
    (p : QParameters) (slot : Fin p.K)
    (outputSlice : RegisterSlice p.ancillaWidth p.selectorWidth)
    (beforeOracle : outputSlice.start + p.selectorWidth ≤
      (QLayout.canonical p).oracleWork.start) :
    WriteMovedSelectorSlotLayout p slot
      (outputSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
  let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
  let candidateSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).candidate
  let branchSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).branch
  let positionSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).positionMatch
  let pairSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).pair
  let compareSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).compareWork
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  let oracleSlice := (QLayout.canonical p).oracleWork
  let word := (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let marker := candidateMarkerWire p (slotToSortWord p slot)
  let branch := oracleBranchWire p
  let position := oraclePositionWire p
  let pair := oraclePairWire p
  let compare := oracleCompareWorkWires p
  let scratch := decoderAndScratchWires p
  have movedCompareFull :
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [movedSlice, compareSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have candidateCompareFull :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [candidateSlice, compareSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have compareAndFull :
      (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [compareSlice, andSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have candidateBranchFull :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [candidateSlice, branchSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have candidatePositionFull :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (positionSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [candidateSlice, positionSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have movedPositionFull :
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (positionSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [movedSlice, positionSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have candidatePairFull :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [candidateSlice, pairSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have branchPositionFull :
      (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (positionSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [branchSlice, positionSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
  have branchPairFull :
      (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [branchSlice, pairSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have positionPairFull :
      (positionSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [positionSlice, pairSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical, QParameters.positionMatchWidth]
    omega
  have branchCompareFull :
      (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [branchSlice, compareSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have positionCompareFull :
      (positionSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [positionSlice, compareSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical,
      QParameters.positionMatchWidth, QParameters.pairWidth]
    omega
  have pairCompareFull :
      (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [pairSlice, compareSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical, QParameters.pairWidth]
    omega
  have branchScratchFull := oracleSlice_disjoint_decoderAndScratch p
    (OracleWorkLayout.canonical p).branch
    (by simp [OracleWorkLayout.canonical]; omega)
  have positionScratchFull := oracleSlice_disjoint_decoderAndScratch p
    (OracleWorkLayout.canonical p).positionMatch
    (by simp [OracleWorkLayout.canonical, QParameters.positionMatchWidth]; omega)
  have pairScratchFull := oracleSlice_disjoint_decoderAndScratch p
    (OracleWorkLayout.canonical p).pair
    (by simp [OracleWorkLayout.canonical, QParameters.pairWidth])
  have candidateScratchFull := oracleSlice_disjoint_decoderAndScratch p
    (OracleWorkLayout.canonical p).candidate
    (by simp [OracleWorkLayout.canonical]; omega)
  have branchMember : branch ∈
      (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [branch, branchSlice, oracleBranchWire, oracleSingletonWire,
      RegisterSlice.wireList]
  have positionMember : position ∈
      (positionSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [position, positionSlice, oraclePositionWire, RegisterSlice.wireList]
  have pairMember : pair ∈
      (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [pair, pairSlice, oraclePairWire, RegisterSlice.wireList]
  have markerMember : marker ∈
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [marker, candidateSlice] using
      candidateMarkerWire_mem_candidateSlice p (slotToSortWord p slot)
  have compareNodup : compare.Nodup := by
    simpa [compare, compareSlice, oracleCompareWorkWires,
      RegisterSlice.wireList] using
      (RegisterSlice.wireList_nodup
        (systemWidth := p.systemWidth) compareSlice)
  have scratchNodup : scratch.Nodup := by
    simpa [scratch] using
      (List.Nodup.sublist (by simp) (decoderAndScratchFlags_nodup p))
  have compareScratch : compare.Disjoint scratch := by
    rw [List.disjoint_left]
    intro wire compareMember scratchMember
    change wire ∈ decoderAndScratchWires p at scratchMember
    exact (List.disjoint_left.mp (oracleCompareWorkWires_disjoint_andWork p))
      (by simpa [compare] using compareMember)
      (List.mem_of_mem_drop scratchMember)
  have branchNePosition : branch ≠ position := fun equal =>
    (List.disjoint_left.mp branchPositionFull branchMember)
      (equal ▸ positionMember)
  have branchNeMarker : branch ≠ marker := fun equal =>
    (List.disjoint_left.mp candidateBranchFull markerMember)
      (equal.symm ▸ branchMember)
  have positionNeMarker : position ≠ marker := fun equal =>
    (List.disjoint_left.mp candidatePositionFull markerMember)
      (equal.symm ▸ positionMember)
  have pairNePosition : pair ≠ position := fun equal =>
    (List.disjoint_left.mp positionPairFull positionMember)
      (equal.symm ▸ pairMember)
  have pairNeMarker : pair ≠ marker := fun equal =>
    (List.disjoint_left.mp candidatePairFull markerMember)
      (equal.symm ▸ pairMember)
  have branchAbsentCompare : branch ∉ compare := fun member =>
    (List.disjoint_left.mp branchCompareFull branchMember)
      (by simpa [compare, compareSlice, oracleCompareWorkWires,
        RegisterSlice.wireList] using member)
  have positionAbsentCompare : position ∉ compare := fun member =>
    (List.disjoint_left.mp positionCompareFull positionMember)
      (by simpa [compare, compareSlice, oracleCompareWorkWires,
        RegisterSlice.wireList] using member)
  have pairAbsentCompare : pair ∉ compare := fun member =>
    (List.disjoint_left.mp pairCompareFull pairMember)
      (by simpa [compare, compareSlice, oracleCompareWorkWires,
        RegisterSlice.wireList] using member)
  have markerAbsentCompare : marker ∉ compare := fun member =>
    (List.disjoint_left.mp candidateCompareFull markerMember)
      (by simpa [compare, compareSlice, oracleCompareWorkWires,
        RegisterSlice.wireList] using member)
  have branchAbsentScratch : branch ∉ scratch := fun member =>
    (List.disjoint_left.mp branchScratchFull branchMember)
      (by simpa [scratch] using member)
  have positionAbsentScratch : position ∉ scratch := fun member =>
    (List.disjoint_left.mp positionScratchFull positionMember)
      (by simpa [scratch] using member)
  have pairAbsentScratch : pair ∉ scratch := fun member =>
    (List.disjoint_left.mp pairScratchFull pairMember)
      (by simpa [scratch] using member)
  have markerAbsentScratch : marker ∉ scratch := fun member =>
    (List.disjoint_left.mp candidateScratchFull markerMember)
      (by simpa [scratch] using member)
  have equalityLayout : (compare ++ scratch ++ [position]).Nodup := by
    have comparisonPrefix : (compare ++ scratch).Nodup :=
      List.nodup_append.mpr ⟨compareNodup, scratchNodup, by
        intro left leftMember right rightMember equal
        exact (List.disjoint_left.mp compareScratch) leftMember
          (equal ▸ rightMember)⟩
    apply List.nodup_append.mpr
    refine ⟨comparisonPrefix, by simp, ?_⟩
    intro left leftMember right rightMember equal
    have rightEq : right = position := by simpa using rightMember
    have leftEq : left = position := equal.trans rightEq
    rcases List.mem_append.mp leftMember with compareMember | scratchMember
    · exact positionAbsentCompare (leftEq ▸ compareMember)
    · exact positionAbsentScratch (leftEq ▸ scratchMember)
  have pairLayout : ([branch, position, marker] ++ scratch ++ [pair]).Nodup := by
    have controls : [branch, position, marker].Nodup := by
      simp [branchNePosition, branchNeMarker, positionNeMarker]
    have controlsScratch : ([branch, position, marker] ++ scratch).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨controls, scratchNodup, ?_⟩
      intro left leftMember right rightMember equal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember
      rcases leftMember with rfl | rfl | rfl
      · exact branchAbsentScratch (equal ▸ rightMember)
      · exact positionAbsentScratch (equal ▸ rightMember)
      · exact markerAbsentScratch (equal ▸ rightMember)
    apply List.nodup_append.mpr
    refine ⟨controlsScratch, by simp, ?_⟩
    intro left leftMember right rightMember equal
    have rightEq : right = pair := by simpa using rightMember
    have leftEq : left = pair := equal.trans rightEq
    rcases List.mem_append.mp leftMember with controlMember | scratchMember
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at controlMember
      rcases controlMember with branchEq | positionEq | markerEq
      · have branchEqPair : branch = pair := branchEq.symm.trans leftEq
        exact (List.disjoint_left.mp branchPairFull branchMember)
          (branchEqPair ▸ pairMember)
      · exact pairNePosition (leftEq.symm.trans positionEq)
      · exact pairNeMarker (leftEq.symm.trans markerEq)
    · exact pairAbsentScratch (leftEq ▸ scratchMember)
  have outputOracleDisjoint :
      (outputSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (oracleSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simpa [oracleSlice] using beforeOracle
  refine {
    moved_length := by simp [oracleMovedWires, QParameters.movedWidth]
    word_length := by simp
    moved_disjoint_compare := by
      simpa [oracleMovedWires, compare, movedSlice, compareSlice,
        oracleCompareWorkWires, RegisterSlice.wireList] using movedCompareFull
    word_disjoint_compare := by
      rw [List.disjoint_left]
      intro wire wordMember compareMember
      exact (List.disjoint_left.mp candidateCompareFull)
        (candidateWordAt_mem_candidateSlice p (slotToSortWord p slot)
          (List.mem_of_mem_take (by simpa [word] using wordMember)))
        (by simpa [compare, compareSlice, oracleCompareWorkWires,
          RegisterSlice.wireList] using compareMember)
    compare_disjoint_scratch := compareScratch
    compare_nodup := compareNodup
    equality_layout := equalityLayout
    position_absent_moved := by
      intro movedMember
      exact (List.disjoint_left.mp movedPositionFull)
        (by simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using
          movedMember)
        positionMember
    position_absent_word := by
      intro wordMember
      exact (List.disjoint_left.mp candidatePositionFull)
        (candidateWordAt_mem_candidateSlice p (slotToSortWord p slot)
          (List.mem_of_mem_take wordMember)) positionMember
    equality_scratch_enough := by
      have enough := decoderAndScratchWires_wordWidth_le p
      simpa [compare] using Nat.le_trans enough
        (Nat.le_add_right (decoderAndScratchWires p).length 1)
    pair_layout := pairLayout
    pair_scratch_enough := by
      have enough := decoderAndScratchWires_wordWidth_le p
      have qPositive := p.q_pos
      have wordLower : 2 ≤ p.wordWidth := by
        simp [QParameters.wordWidth]
        omega
      omega
    branch_ne_position := branchNePosition
    branch_ne_marker := branchNeMarker
    position_ne_marker := positionNeMarker
    pair_ne_position := pairNePosition
    pair_ne_marker := pairNeMarker
    branch_absent_compare := branchAbsentCompare
    marker_absent_compare := markerAbsentCompare
    pair_absent_compare := pairAbsentCompare
    branch_absent_scratch := branchAbsentScratch
    position_absent_scratch := positionAbsentScratch
    marker_absent_scratch := markerAbsentScratch
    pair_absent_scratch := pairAbsentScratch
    output_nodup := RegisterSlice.wireList_nodup outputSlice
    output_disjoint_support := by
      rw [List.disjoint_left]
      intro wire outputMember supportMember
      exact (List.disjoint_left.mp outputOracleDisjoint) outputMember
        (xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport_subset_oracleWork p slot supportMember) }

/-- selector-output registerは canonical moved-selector 配置条件を満たす。 -/
theorem MovedMemberPositionSelectorOutputLayout_selectorOutput_canonical
    (p : QParameters) (slot : Fin p.K) :
    WriteMovedSelectorSlotLayout p slot (selectorOutputWires p) := by
  simpa [selectorOutputWires, selectorOutputWire, RegisterSlice.wireList] using
    MovedMemberPositionSelectorOutputLayout_of_outputSlice p slot
      (QLayout.canonical p).selectorOutput (by
        simp [QLayout.canonical]
        omega)

/-- column-selector registerは canonical moved-selector 配置条件を満たす。 -/
theorem MovedMemberPositionSelectorOutputLayout_columnSelector_canonical
    (p : QParameters) (slot : Fin p.K) :
    WriteMovedSelectorSlotLayout p slot (columnSelectorWires p) := by
  simpa [columnSelectorWires, columnSelectorWire, RegisterSlice.wireList] using
    MovedMemberPositionSelectorOutputLayout_of_outputSlice p slot
      (QLayout.canonical p).columnSelector (by
        simp [QLayout.canonical]
        omega)

end ReversibleCircuit

end ProbabilityGeneratorQProof
