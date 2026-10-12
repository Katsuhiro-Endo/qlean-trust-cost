import QLean.Generator.Implementation.QOraclePersistentLocality
import QLean.Generator.Implementation.ReversibleLogicSharedCoreReadoutAdapter

/-!
# Q oracle event compute の use 用 work clean 性

event compute の最終 bitonic sort が、moved-selector と sorted writer に必要な比較・
AND・position・pair work を clean に保つことを、純粋 schedule の有限帰納で証明する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 前側 oracle slice と後側 oracle slice の配置順から、後側 wire の非所属を得る。 -/
theorem laterOracleSliceWire_not_mem_earlier
    (p : QParameters) {earlyWidth laterWidth : Nat}
    (early : RegisterSlice p.oracleWorkWidth earlyWidth)
    (later : RegisterSlice p.oracleWorkWidth laterWidth)
    (separated : early.start + earlyWidth ≤ later.start)
    (index : Fin laterWidth) :
    (QLayout.oracleSlice later).ancillaWire index ∉
      ((QLayout.oracleSlice early).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  have disjoint :
      ((QLayout.oracleSlice early).wireList :
        List (Wire p.ancillaWidth p.systemWidth)).Disjoint
      ((QLayout.oracleSlice later).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [QLayout.oracleSlice, RegisterSlice.compose]
    omega
  intro earlyMember
  apply (List.disjoint_left.mp disjoint) earlyMember
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩

/-- 前方sliceと後方sliceの配置順序から、後方sliceのwireの非所属を得る。 -/
theorem laterOracleListWire_not_mem_earlierSlice
    (p : QParameters) {earlyWidth laterWidth : Nat}
    (early : RegisterSlice p.oracleWorkWidth earlyWidth)
    (later : RegisterSlice p.oracleWorkWidth laterWidth)
    (separated : early.start + earlyWidth ≤ later.start)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈
      ((QLayout.oracleSlice later).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    wire ∉ ((QLayout.oracleSlice early).wireList :
      List (Wire p.ancillaWidth p.systemWidth)) := by
  rw [RegisterSlice.wireList] at member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  exact laterOracleSliceWire_not_mem_earlier p early later separated index

/-- candidate slice より後方のsliceに属するwireはcandidate sliceに属さない。 -/
theorem laterOracleListWire_not_mem_candidateSlice
    (p : QParameters) {laterWidth : Nat}
    (later : RegisterSlice p.oracleWorkWidth laterWidth)
    (separated :
      (OracleWorkLayout.canonical p).candidate.start + p.candidateWidth ≤
        later.start)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈
      ((QLayout.oracleSlice later).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    wire ∉
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  exact laterOracleListWire_not_mem_earlierSlice p
    (OracleWorkLayout.canonical p).candidate later separated wire member

/-- 純粋 bitonic schedule は、全candidateと全使用historyの外のwireを保存する。 -/
theorem canonicalCandidateSortWithHistoryRestorationSpec_preserves_other
    (p : QParameters) :
    ∀ (schedule :
        List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (wire : Wire p.ancillaWidth p.systemWidth),
      (∀ word : Fin p.sortWordCount, wire ∉ candidateWordAt p word) →
      (∀ instruction ∈ schedule,
        wire ≠ (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire
            instruction.history) →
      CanonicalCandidateSortWithHistoryRestorationSpec p schedule input wire = input wire
  | [], _, _, _, _ => rfl
  | instruction :: schedule, input, wire, outsideCandidates, outsideHistories => by
      change CanonicalCandidateSortWithHistoryRestorationSpec p schedule
        (qBitonicStepReference p instruction input) wire = input wire
      rw [canonicalCandidateSortWithHistoryRestorationSpec_preserves_other p schedule
        (qBitonicStepReference p instruction input) wire outsideCandidates]
      · apply qBitonicStepReference_other p instruction input wire
        · exact outsideCandidates instruction.left
        · exact outsideCandidates instruction.right
        · exact outsideHistories instruction (by simp)
      · intro next nextMember
        exact outsideHistories next (by simp [nextMember])

/-- bitonic schedule は oracle compare work の読出し値を保存する。 -/
theorem canonicalCandidateSortWithHistoryRestorationSpec_preserves_oracleCompare
    (p : QParameters)
    (schedule :
      List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (oracleCompareWorkWires p)
        (CanonicalCandidateSortWithHistoryRestorationSpec p schedule input) =
      readWires (oracleCompareWorkWires p) input := by
  apply List.map_congr_left
  intro wire member
  apply canonicalCandidateSortWithHistoryRestorationSpec_preserves_other p schedule input wire
  · intro word candidateMember
    have compareMember : wire ∈ sortCompareWorkWires p := by
      apply List.mem_append_left
      simpa [sortCompareWorkWires, oracleCompareWorkWires] using member
    exact (List.disjoint_left.mp (sortCandidateWordAt_disjoint_compare p word))
      candidateMember compareMember
  · intro instruction instructionMember equal
    subst wire
    apply sortHistoryWire_not_mem_compare p instruction.history
    apply List.mem_append_left
    simpa [sortCompareWorkWires, oracleCompareWorkWires] using member

/-- bitonic schedule は decoder AND scratch を点ごとに保存する。 -/
theorem canonicalCandidateSortWithHistoryRestorationSpec_preserves_decoderScratch
    (p : QParameters)
    (schedule :
      List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ decoderAndScratchWires p) :
    CanonicalCandidateSortWithHistoryRestorationSpec p schedule input wire = input wire := by
  apply canonicalCandidateSortWithHistoryRestorationSpec_preserves_other p schedule input wire
  · intro word candidateMember
    have candidateFull := candidateWordAt_mem_candidateSlice p word candidateMember
    have scratchFull : wire ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).andWork).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [decoderAndScratchWires, oracleAndWorkWires,
        RegisterSlice.wireList] using List.mem_of_mem_drop member
    have disjoint :
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).candidate).wireList :
            List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).andWork).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      apply RegisterSlice.wireList_disjoint_of_end_le_start
      simp [QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical]
      omega
    exact (List.disjoint_left.mp disjoint) candidateFull scratchFull
  · intro instruction instructionMember equal
    subst wire
    have sortMember :
        (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire
            instruction.history ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).sortFlags).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr
        ⟨instruction.history, List.mem_finRange instruction.history, rfl⟩
    have scratchFull :
        (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire
            instruction.history ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).andWork).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [decoderAndScratchWires, oracleAndWorkWires,
        RegisterSlice.wireList] using List.mem_of_mem_drop member
    have disjoint :
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).wireList :
            List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).andWork).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      apply RegisterSlice.wireList_disjoint_of_end_le_start
      simp [QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical]
      omega
    exact (List.disjoint_left.mp disjoint) sortMember scratchFull

/-- bitonic schedule は position flag を保存する。 -/
theorem canonicalCandidateSortWithHistoryRestorationSpec_preserves_position
    (p : QParameters)
    (schedule :
      List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    CanonicalCandidateSortWithHistoryRestorationSpec p schedule input (oraclePositionWire p) =
      input (oraclePositionWire p) := by
  apply canonicalCandidateSortWithHistoryRestorationSpec_preserves_other p schedule input
  · intro word member
    have candidateFull := candidateWordAt_mem_candidateSlice p word member
    have positionAbsent := laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).candidate
      (OracleWorkLayout.canonical p).positionMatch (by
        simp [OracleWorkLayout.canonical]
        omega) ⟨0, by simpa [QParameters.positionMatchWidth] using p.K_pos⟩
    exact positionAbsent candidateFull
  · intro instruction instructionMember equal
    have positionAbsent := laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).sortFlags
      (OracleWorkLayout.canonical p).positionMatch (by
        simp [OracleWorkLayout.canonical]
        omega) ⟨0, by simpa [QParameters.positionMatchWidth] using p.K_pos⟩
    apply positionAbsent
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history,
        by simpa [oraclePositionWire] using equal.symm⟩

/-- bitonic schedule は pair flag を保存する。 -/
theorem canonicalCandidateSortWithHistoryRestorationSpec_preserves_pair
    (p : QParameters)
    (schedule :
      List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    CanonicalCandidateSortWithHistoryRestorationSpec p schedule input (oraclePairWire p) =
      input (oraclePairWire p) := by
  apply canonicalCandidateSortWithHistoryRestorationSpec_preserves_other p schedule input
  · intro word member
    exact oraclePairWire_not_mem_candidateSlice p
      (candidateWordAt_mem_candidateSlice p word member)
  · intro instruction instructionMember equal
    have pairAbsent := laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).sortFlags
      (OracleWorkLayout.canonical p).pair (by
        simp [OracleWorkLayout.canonical]
        omega) ⟨0, by simpa [QParameters.pairWidth] using p.K_pos⟩
    apply pairAbsent
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history,
        by simpa [oraclePairWire] using equal.symm⟩

/-- candidate slot 参照作用は、全 slot のcandidate word 外にある wire を保存する。 -/
theorem prepareCandidateSlotsReference_other
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (wire : Wire p.ancillaWidth p.systemWidth),
      (∀ slot : Fin p.K, wire ∉
        (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth) →
      (∀ slot : Fin p.K, wire ≠
        candidateMarkerWire p (slotToSortWord p slot)) →
      prepareCandidateSlotsReference p register slots input wire = input wire
  | [], _, _, _, _ => rfl
  | slot :: slots, input, wire, outsideData, outsideMarker => by
      change prepareCandidateSlotsReference p register slots
          (prepareCandidateSlotReference p register slot input) wire = input wire
      rw [prepareCandidateSlotsReference_other p register slots _ wire
        outsideData outsideMarker]
      exact prepareCandidateSlotReference_other p register slot input wire
        (outsideData slot) (outsideMarker slot)

/-- candidate 生成参照作用は、candidate slice 外の wire を保存する。 -/
theorem configurationToCandidateRegisterXorSpec_other
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideData : ∀ word : Fin p.sortWordCount,
      wire ∉ (candidateWordAt p word).take p.wordWidth)
    (outsideMarker : ∀ word : Fin p.sortWordCount,
      wire ≠ candidateMarkerWire p word) :
    ConfigurationToCandidateRegisterXorSpec p register input wire = input wire := by
  rw [ConfigurationToCandidateRegisterXorSpec]
  rw [prepareCandidateSlotsReference_other p register (List.finRange p.K) _ wire
    (fun slot => outsideData (slotToSortWord p slot))
    (fun slot => outsideMarker (slotToSortWord p slot))]
  apply initializeCandidateMarkersReference_other
  intro word member
  exact outsideMarker word

/-- branch wire は任意のcandidate wordの外にある。 -/
theorem oracleBranchWire_not_mem_candidateWordAt
    (p : QParameters) (word : Fin p.sortWordCount) :
    oracleBranchWire p ∉ candidateWordAt p word := by
  have absent := laterOracleSliceWire_not_mem_earlier p
    (OracleWorkLayout.canonical p).candidate
    (OracleWorkLayout.canonical p).branch (by
      simp [OracleWorkLayout.canonical]
      omega)
    (0 : Fin 1)
  intro member
  apply absent
  simpa [oracleBranchWire, oracleSingletonWire] using
    candidateWordAt_mem_candidateSlice p word member

/-- 正本 candidate 生成回路は branch wire を保存する。 -/
theorem runBasis_xorConfigurationIntoCandidateRegisterCircuit_oracleBranch
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (xorConfigurationIntoCandidateRegisterCircuit p register).runBasis reversibleGatePermutation input
        (oracleBranchWire p) = input (oracleBranchWire p) := by
  rw [runBasis_xorConfigurationIntoCandidateRegisterCircuit p register layout input]
  apply configurationToCandidateRegisterXorSpec_other
  · intro word member
    exact oracleBranchWire_not_mem_candidateWordAt p word
      (List.mem_of_mem_take member)
  · intro word equal
    apply oracleBranchWire_not_mem_candidateWordAt p word
    rw [equal]
    simp [candidateMarkerWire, candidateWordAt]

/-- 正本 candidate 生成回路はcandidate slice外の任意wireを保存する。 -/
theorem runBasis_xorConfigurationIntoCandidateRegisterCircuit_outside_candidateSlice
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth))) :
    (xorConfigurationIntoCandidateRegisterCircuit p register).runBasis reversibleGatePermutation input
        wire = input wire := by
  rw [runBasis_xorConfigurationIntoCandidateRegisterCircuit p register layout input]
  apply configurationToCandidateRegisterXorSpec_other
  · intro word member
    exact outside (candidateWordAt_mem_candidateSlice p word
      (List.mem_of_mem_take member))
  · intro word equal
    apply outside
    rw [equal]
    exact candidateMarkerWire_mem_candidateSlice p word

/-- oracle compare work の各wireはcandidate sliceの外にある。 -/
theorem oracleCompareWorkWire_not_mem_candidateSlice
    (p : QParameters) (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ oracleCompareWorkWires p) :
    wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  apply laterOracleListWire_not_mem_candidateSlice p
    (OracleWorkLayout.canonical p).compareWork (by
      simp [OracleWorkLayout.canonical]
      omega) wire
  simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member

/-- decoder AND scratch の各wireはcandidate sliceの外にある。 -/
theorem decoderScratchWire_not_mem_candidateSlice
    (p : QParameters) (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ decoderAndScratchWires p) :
    wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  apply laterOracleListWire_not_mem_candidateSlice p
    (OracleWorkLayout.canonical p).andWork (by
      simp [OracleWorkLayout.canonical]
      omega) wire
  simpa [decoderAndScratchWires, oracleAndWorkWires,
    RegisterSlice.wireList] using List.mem_of_mem_drop member

/-- position wire はcandidate sliceの外にある。 -/
theorem oraclePositionWire_not_mem_candidateSlice (p : QParameters) :
    oraclePositionWire p ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  simpa [oraclePositionWire] using laterOracleSliceWire_not_mem_earlier p
    (OracleWorkLayout.canonical p).candidate
    (OracleWorkLayout.canonical p).positionMatch (by
      simp [OracleWorkLayout.canonical]
      omega)
    ⟨0, by simpa [QParameters.positionMatchWidth] using p.K_pos⟩

/-- pair wire はcandidate sliceの外にある。 -/
theorem oraclePairWire_not_mem_candidateRegion (p : QParameters) :
    oraclePairWire p ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  simpa [oraclePairWire] using laterOracleSliceWire_not_mem_earlier p
    (OracleWorkLayout.canonical p).candidate
    (OracleWorkLayout.canonical p).pair (by
      simp [OracleWorkLayout.canonical]
      omega)
    ⟨0, by simp [QParameters.pairWidth, p.K_pos]⟩

/-- sort compare work の各wireはcandidate sliceの外にある。 -/
theorem sortCompareWire_not_mem_candidateSlice
    (p : QParameters) (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ sortCompareWorkWires p) :
    wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  change wire ∈ oracleCompareWorkWires p ++ [_] at member
  rcases List.mem_append.mp member with compareMember | extraMember
  · exact oracleCompareWorkWire_not_mem_candidateSlice p wire compareMember
  · simp only [List.mem_singleton] at extraMember
    subst wire
    exact laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).candidate
      (OracleWorkLayout.canonical p).andWork (by
        simp [OracleWorkLayout.canonical]
        omega)
      ⟨0, by simp [QParameters.andWorkWidth]⟩

/-- sort AND scratch の各wireはcandidate sliceの外にある。 -/
theorem sortScratchWire_not_mem_candidateSlice
    (p : QParameters) (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ sortAndScratchWires p) :
    wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
  exact laterOracleSliceWire_not_mem_earlier p
    (OracleWorkLayout.canonical p).candidate
    (OracleWorkLayout.canonical p).andWork (by
      simp [OracleWorkLayout.canonical]
      omega)
    ⟨index.val + 1, by
      simp [QParameters.andWorkWidth] at index ⊢
      omega⟩

/-- sort history wire はcandidate sliceの外にある。 -/
theorem sortHistoryWire_not_mem_candidateSlice
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange
      p.sortWordCount p.sortFlagWidth) :
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire
        instruction.history ∉
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
  laterOracleSliceWire_not_mem_earlier p
    (OracleWorkLayout.canonical p).candidate
    (OracleWorkLayout.canonical p).sortFlags (by
      simp [OracleWorkLayout.canonical]) instruction.history

/-- bitonic sort は branch wire を保存する。 -/
theorem qBitonicSort_preserves_oracleBranch
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (sortCompareZero : readWires (sortCompareWorkWires p) input =
      List.replicate (sortCompareWorkWires p).length false)
    (sortScratchZero : ∀ wire ∈ sortAndScratchWires p,
      input wire = false)
    (sortHistoryZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      input ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) = false) :
    (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation input
        (oracleBranchWire p) = input (oracleBranchWire p) := by
  rw [runBasis_reversiblySortCandidateWordsAndRestoreHistoryCircuit_eq_reference p input
    sortCompareZero sortScratchZero sortHistoryZero]
  apply canonicalCandidateSortWithHistoryRestorationSpec_preserves_other
  · intro word member
    exact oracleBranchWire_not_mem_candidateWordAt p word member
  · intro instruction instructionMember equal
    have absent := laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).sortFlags
      (OracleWorkLayout.canonical p).branch (by
        simp [OracleWorkLayout.canonical]
        omega)
      (0 : Fin 1)
    apply absent
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history,
        by simpa [oracleBranchWire, oracleSingletonWire] using equal.symm⟩

/-- event sort 直前に必要な transient work の clean 条件。 -/
structure EventSortCleanInput (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- moved-selector writer の比較・position・pair work が clean である。 -/
  moved_selector : WriteMovedSelectorSlotClean p input
  /-- bitonic sort の比較workが全0である。 -/
  sort_compare_zero : readWires (sortCompareWorkWires p) input =
    List.replicate (sortCompareWorkWires p).length false
  /-- bitonic sort のAND scratchが全0である。 -/
  sort_scratch_zero : ∀ wire ∈ sortAndScratchWires p, input wire = false
  /-- bitonic sort の各履歴wireが全0である。 -/
  sort_history_zero : ∀ instruction ∈ qTypedBitonicSchedule p,
    input ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire
        instruction.history) = false

/-- tracked work 上で clean 入力と一致する状態も event sort の clean 条件を満たす。 -/
theorem EventSortCleanInput.of_agree
    (p : QParameters)
    (original state : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p original)
    (compareAgree : readWires (oracleCompareWorkWires p) state =
      readWires (oracleCompareWorkWires p) original)
    (decoderScratchAgree : ∀ wire ∈ decoderAndScratchWires p,
      state wire = original wire)
    (positionAgree : state (oraclePositionWire p) =
      original (oraclePositionWire p))
    (pairAgree : state (oraclePairWire p) = original (oraclePairWire p))
    (sortCompareAgree : readWires (sortCompareWorkWires p) state =
      readWires (sortCompareWorkWires p) original)
    (sortScratchAgree : ∀ wire ∈ sortAndScratchWires p,
      state wire = original wire)
    (historyAgree : ∀ instruction ∈ qTypedBitonicSchedule p,
      state ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) =
      original ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history)) :
    EventSortCleanInput p state := by
  refine {
    moved_selector := {
      compare_zero := compareAgree.trans clean.moved_selector.compare_zero
      scratch_zero := ?_
      position_zero := positionAgree.trans clean.moved_selector.position_zero
      pair_zero := pairAgree.trans clean.moved_selector.pair_zero }
    sort_compare_zero := sortCompareAgree.trans clean.sort_compare_zero
    sort_scratch_zero := ?_
    sort_history_zero := ?_ }
  · intro wire member
    rw [decoderScratchAgree wire member]
    exact clean.moved_selector.scratch_zero wire member
  · intro wire member
    rw [sortScratchAgree wire member]
    exact clean.sort_scratch_zero wire member
  · intro instruction member
    rw [historyAgree instruction member]
    exact clean.sort_history_zero instruction member

/-- candidate slice外の全tracked wireを保存する状態変換は、event sort clean性を保存する。 -/
theorem EventSortCleanInput.of_candidateSlice_preserved
    (p : QParameters)
    (original state : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p original)
    (preserve : ∀ (wire : Wire p.ancillaWidth p.systemWidth),
      wire ∉ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) →
      state wire = original wire) :
    EventSortCleanInput p state := by
  apply EventSortCleanInput.of_agree p original state clean
  · apply List.map_congr_left
    intro wire member
    exact preserve wire
      (oracleCompareWorkWire_not_mem_candidateSlice p wire member)
  · intro wire member
    exact preserve wire
      (decoderScratchWire_not_mem_candidateSlice p wire member)
  · exact preserve (oraclePositionWire p)
      (oraclePositionWire_not_mem_candidateSlice p)
  · exact preserve (oraclePairWire p)
      (oraclePairWire_not_mem_candidateRegion p)
  · apply List.map_congr_left
    intro wire member
    exact preserve wire
      (sortCompareWire_not_mem_candidateSlice p wire member)
  · intro wire member
    exact preserve wire
      (sortScratchWire_not_mem_candidateSlice p wire member)
  · intro instruction instructionMember
    exact preserve _ (sortHistoryWire_not_mem_candidateSlice p instruction)

/-- sortFlagsより前方の一slice外を保存する状態変換は、event sort clean性を保存する。 -/
theorem EventSortCleanInput.of_earlySlice_preserved
    (p : QParameters) {earlyWidth : Nat}
    (early : RegisterSlice p.oracleWorkWidth earlyWidth)
    (earlyBeforeSort : early.start + earlyWidth ≤
      (OracleWorkLayout.canonical p).sortFlags.start)
    (original state : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p original)
    (preserve : ∀ (wire : Wire p.ancillaWidth p.systemWidth),
      wire ∉ ((QLayout.oracleSlice early).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) →
      state wire = original wire) :
    EventSortCleanInput p state := by
  have outsideLater {width : Nat}
      (later : RegisterSlice p.oracleWorkWidth width)
      (sortBeforeLater :
        (OracleWorkLayout.canonical p).sortFlags.start ≤ later.start)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice later).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
      wire ∉ ((QLayout.oracleSlice early).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) :=
    laterOracleListWire_not_mem_earlierSlice p early later
      (le_trans earlyBeforeSort sortBeforeLater) wire member
  apply EventSortCleanInput.of_agree p original state clean
  · apply List.map_congr_left
    intro wire member
    apply preserve wire
    apply outsideLater (OracleWorkLayout.canonical p).compareWork (by
      simp [OracleWorkLayout.canonical]
      omega) wire
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member
  · intro wire member
    apply preserve wire
    apply outsideLater (OracleWorkLayout.canonical p).andWork (by
      simp [OracleWorkLayout.canonical]
      omega) wire
    simpa [decoderAndScratchWires, oracleAndWorkWires,
      RegisterSlice.wireList] using List.mem_of_mem_drop member
  · apply preserve (oraclePositionWire p)
    apply laterOracleSliceWire_not_mem_earlier p early
      (OracleWorkLayout.canonical p).positionMatch
      (le_trans earlyBeforeSort (by
        simp [OracleWorkLayout.canonical]
        omega))
      ⟨0, by simpa [QParameters.positionMatchWidth] using p.K_pos⟩
  · apply preserve (oraclePairWire p)
    apply laterOracleSliceWire_not_mem_earlier p early
      (OracleWorkLayout.canonical p).pair
      (le_trans earlyBeforeSort (by
        simp [OracleWorkLayout.canonical]
        omega))
      ⟨0, by simpa [QParameters.pairWidth] using p.K_pos⟩
  · apply List.map_congr_left
    intro wire member
    change wire ∈ oracleCompareWorkWires p ++ [_] at member
    rcases List.mem_append.mp member with compareMember | extraMember
    · apply preserve wire
      apply outsideLater (OracleWorkLayout.canonical p).compareWork (by
        simp [OracleWorkLayout.canonical]
        omega) wire
      simpa [oracleCompareWorkWires, RegisterSlice.wireList] using compareMember
    · simp only [List.mem_singleton] at extraMember
      subst wire
      apply preserve
      apply laterOracleSliceWire_not_mem_earlier p early
        (OracleWorkLayout.canonical p).andWork
        (le_trans earlyBeforeSort (by
          simp [OracleWorkLayout.canonical]
          omega))
        ⟨0, by simp [QParameters.andWorkWidth]⟩
  · intro wire member
    rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
    apply preserve
    apply laterOracleSliceWire_not_mem_earlier p early
      (OracleWorkLayout.canonical p).andWork
      (le_trans earlyBeforeSort (by
        simp [OracleWorkLayout.canonical]
        omega))
      ⟨index.val + 1, by
        simp [QParameters.andWorkWidth] at index ⊢
        omega⟩
  · intro instruction instructionMember
    apply preserve
    exact laterOracleSliceWire_not_mem_earlier p early
      (OracleWorkLayout.canonical p).sortFlags earlyBeforeSort
      instruction.history

/-- selected bitのX作用はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_x_selected
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p (xBasisAction (oracleSelectedWire p) input) := by
  apply EventSortCleanInput.of_earlySlice_preserved p
    (OracleWorkLayout.canonical p).selected (by
      simp [OracleWorkLayout.canonical]
      omega) input _ clean
  intro wire outside
  apply xBasisAction_other
  intro equal
  apply outside
  rw [equal]
  change (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).selected).ancillaWire 0 ∈ _
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩

/-- column selector比較回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_columnEventSelectorCompute
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((columnEventSelectorCompute p slot offset).runBasis
        reversibleGatePermutation input) := by
  rw [runBasis_columnEventSelectorCompute p slot offset input
    clean.moved_selector.scratch_zero]
  split
  · exact EventSortCleanInput.of_x_selected p input clean
  · exact clean

/-- row selector比較回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_rowEventSelectorCompute
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((rowEventSelectorCompute p slot offset).runBasis
        reversibleGatePermutation input) := by
  rw [runBasis_rowEventSelectorCompute p slot offset input
    clean.moved_selector.scratch_zero]
  split
  · exact EventSortCleanInput.of_x_selected p input clean
  · exact clean

/-- column moved copy回路はmoved slice外の任意wireを保存する。 -/
theorem runBasis_columnEventMovedCopy_outside_movedSlice
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (columnEventMovedCopy p slot).runBasis reversibleGatePermutation input wire =
      input wire := by
  have layout := columnEventMoveLayout_canonical p slot (0 : Fin 6)
  rw [columnEventMovedCopy]
  apply runBasis_validatedXorCopyLists_outside
    (registerWordAt p (columnKeyWires p) slot) (oracleMovedWires p) input
    (registerWordAt_nodup_of_nodup p (columnKeyWires p) slot
      (columnKeyWires_nodup p)) layout.moved_nodup layout.same_length
    layout.source_disjoint_moved
  intro member
  apply outside
  simpa [oracleMovedWires, RegisterSlice.wireList] using member

/-- row moved copy回路はmoved slice外の任意wireを保存する。 -/
theorem runBasis_rowEventMovedCopy_outside_movedSlice
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (rowEventMovedCopy p slot).runBasis reversibleGatePermutation input wire =
      input wire := by
  have sameLength :
      (registerWordAt p (systemWires p) slot).length =
        (oracleMovedWires p).length := by
    rw [registerWordAt_length p (systemWires p) (systemWires_length p) slot]
    simp [oracleMovedWires, QParameters.movedWidth, QParameters.wordWidth]
  have sourceDisjoint :
      (registerWordAt p (systemWires p) slot).Disjoint
        (oracleMovedWires p) := by
    rw [List.disjoint_left]
    intro observed sourceMember targetMember
    exact (List.disjoint_left.mp (systemWires_disjoint_oracleMovedWires p))
      (mem_register_of_mem_registerWordAt p (systemWires p) slot sourceMember)
      targetMember
  rw [rowEventMovedCopy]
  apply runBasis_validatedXorCopyLists_outside
    (registerWordAt p (systemWires p) slot) (oracleMovedWires p) input
    (registerWordAt_nodup_of_nodup p (systemWires p) slot
      (systemWires_nodup p)) (oracleMovedWires_nodup p) sameLength
    sourceDisjoint
  intro member
  apply outside
  simpa [oracleMovedWires, RegisterSlice.wireList] using member

/-- event移動座標の各wireはmoved sliceに属する。 -/
theorem columnEventCoordinate_mem_movedSlice
    (p : QParameters) (offset : Fin 6)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ columnEventCoordinate p offset) :
    wire ∈ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  have movedMember : wire ∈ oracleMovedWires p := by
    unfold columnEventCoordinate at member
    split at member
    · exact List.mem_of_mem_drop (List.mem_of_mem_take member)
    · exact List.mem_of_mem_take member
  simpa [oracleMovedWires, RegisterSlice.wireList] using movedMember

/-- column周期incrementはmoved slice外の任意wireを保存する。 -/
theorem runBasis_columnEventMoveForward_outside_movedSlice
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (columnEventMoveForward p offset).runBasis reversibleGatePermutation input
        wire = input wire := by
  let slot : Fin p.K := ⟨0, p.K_pos⟩
  let layout := columnEventMoveLayout_canonical p slot offset
  rw [columnEventMoveForward]
  rw [runBasis_incrementWordMod2PowInPlaceCircuit (columnEventCoordinate p offset)
    (decoderAndScratchWires p) input layout.enough_scratch
    layout.coordinate_scratch_nodup scratchZero]
  apply incrementWordCarrySequenceReference_outside
  intro member
  exact outside (columnEventCoordinate_mem_movedSlice p offset wire member)

/-- row周期decrementはmoved slice外の任意wireを保存する。 -/
theorem runBasis_rowEventMoveBackward_outside_movedSlice
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).moved).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (rowEventMoveBackward p offset).runBasis reversibleGatePermutation input
        wire = input wire := by
  let slot : Fin p.K := ⟨0, p.K_pos⟩
  let layout := columnEventMoveLayout_canonical p slot offset
  change (decrementWordMod2PowInPlaceCircuit (columnEventCoordinate p offset)
    (decoderAndScratchWires p)).runBasis reversibleGatePermutation input wire = _
  rw [runBasis_decrementWordMod2PowInPlaceCircuit (columnEventCoordinate p offset)
    (decoderAndScratchWires p) input layout.enough_scratch
    layout.coordinate_scratch_nodup scratchZero]
  apply decrementWordBorrowSequenceReference_outside
  intro member
  exact outside (columnEventCoordinate_mem_movedSlice p offset wire member)

/-- moved slice外を保存する変換はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_movedSlice_preserved
    (p : QParameters)
    (original state : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p original)
    (preserve : ∀ (wire : Wire p.ancillaWidth p.systemWidth),
      wire ∉ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).moved).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) →
      state wire = original wire) :
    EventSortCleanInput p state := by
  exact EventSortCleanInput.of_earlySlice_preserved p
    (OracleWorkLayout.canonical p).moved (by
      simp [OracleWorkLayout.canonical]) original state clean preserve

/-- column moved copy回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_columnEventMovedCopy
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((columnEventMovedCopy p slot).runBasis reversibleGatePermutation input) := by
  apply EventSortCleanInput.of_movedSlice_preserved p input _ clean
  exact runBasis_columnEventMovedCopy_outside_movedSlice p slot input

/-- row moved copy回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_rowEventMovedCopy
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((rowEventMovedCopy p slot).runBasis reversibleGatePermutation input) := by
  apply EventSortCleanInput.of_movedSlice_preserved p input _ clean
  exact runBasis_rowEventMovedCopy_outside_movedSlice p slot input

/-- column移動回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_columnEventMoveForward
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((columnEventMoveForward p offset).runBasis
        reversibleGatePermutation input) := by
  apply EventSortCleanInput.of_movedSlice_preserved p input _ clean
  intro wire outside
  exact runBasis_columnEventMoveForward_outside_movedSlice p offset input
    clean.moved_selector.scratch_zero wire outside

/-- row逆移動回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_rowEventMoveBackward
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((rowEventMoveBackward p offset).runBasis
        reversibleGatePermutation input) := by
  apply EventSortCleanInput.of_movedSlice_preserved p input _ clean
  intro wire outside
  exact runBasis_rowEventMoveBackward_outside_movedSlice p offset input
    clean.moved_selector.scratch_zero wire outside

/-- 非重複なoracle sliceに属する二wireは異なる。 -/
theorem oracleSliceMembers_ne_of_end_le_start
    (p : QParameters) {leftWidth rightWidth : Nat}
    (left : RegisterSlice p.oracleWorkWidth leftWidth)
    (right : RegisterSlice p.oracleWorkWidth rightWidth)
    (separated : left.start + leftWidth ≤ right.start)
    {leftWire rightWire : Wire p.ancillaWidth p.systemWidth}
    (leftMember : leftWire ∈ ((QLayout.oracleSlice left).wireList :
      List (Wire p.ancillaWidth p.systemWidth)))
    (rightMember : rightWire ∈ ((QLayout.oracleSlice right).wireList :
      List (Wire p.ancillaWidth p.systemWidth))) :
    leftWire ≠ rightWire := by
  intro equal
  subst rightWire
  exact (laterOracleListWire_not_mem_earlierSlice p left right separated
    leftWire rightMember) leftMember

/-- membership参照作用が書き込む4種類のwireとの非一致条件。 -/
structure MembershipOutputsSeparated (p : QParameters)
    (wire : Wire p.ancillaWidth p.systemWidth) : Prop where
  /-- 各membership equal flagと異なる。 -/
  ne_equal : ∀ slot : Fin p.K, wire ≠ membershipEqualWireAt p slot
  /-- 各membership good flagと異なる。 -/
  ne_good : ∀ slot : Fin p.K, wire ≠ membershipGoodWireAt p slot
  /-- present-other flagと異なる。 -/
  ne_other : wire ≠ oraclePresentOtherWire p
  /-- absent flagと異なる。 -/
  ne_absent : wire ≠ oracleAbsentWire p

/-- membership equal flagは対応sliceに属する。 -/
theorem membershipEqualWireAt_mem_slice
    (p : QParameters) (slot : Fin p.K) :
    membershipEqualWireAt p slot ∈
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).membershipEqual).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩

/-- membership good flagは対応sliceに属する。 -/
theorem membershipGoodWireAt_mem_slice
    (p : QParameters) (slot : Fin p.K) :
    membershipGoodWireAt p slot ∈
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).membershipGood).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩

/-- absent flagは対応sliceに属する。 -/
theorem oracleAbsentWire_mem_slice (p : QParameters) :
    oracleAbsentWire p ∈ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).absent).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  simp [oracleAbsentWire, oracleSingletonWire, RegisterSlice.wireList]

/-- present-other flagは対応sliceに属する。 -/
theorem oraclePresentOtherWire_mem_slice (p : QParameters) :
    oraclePresentOtherWire p ∈ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).presentOther).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  simp [oraclePresentOtherWire, oracleSingletonWire, RegisterSlice.wireList]

/-- sort history sliceのwireはmembership出力wireのいずれとも異なる。 -/
theorem MembershipOutputsSeparated.of_sortFlags
    (p : QParameters) (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    MembershipOutputsSeparated p wire := by
  refine {
    ne_equal := ?_
    ne_good := ?_
    ne_other := ?_
    ne_absent := ?_ }
  · intro slot
    exact oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).sortFlags
      (OracleWorkLayout.canonical p).membershipEqual (by
        simp [OracleWorkLayout.canonical]) member
      (membershipEqualWireAt_mem_slice p slot)
  · intro slot
    exact oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).sortFlags
      (OracleWorkLayout.canonical p).membershipGood (by
        simp [OracleWorkLayout.canonical]) member
      (membershipGoodWireAt_mem_slice p slot)
  · exact oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).sortFlags
      (OracleWorkLayout.canonical p).presentOther (by
        simp [OracleWorkLayout.canonical]
        omega) member
      (oraclePresentOtherWire_mem_slice p)
  · exact oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).sortFlags
      (OracleWorkLayout.canonical p).absent (by
        simp [OracleWorkLayout.canonical]
        omega) member (oracleAbsentWire_mem_slice p)

/-- present-otherより後方のsliceのwireはmembership出力wireのいずれとも異なる。 -/
theorem MembershipOutputsSeparated.of_laterSlice
    (p : QParameters) {width : Nat}
    (later : RegisterSlice p.oracleWorkWidth width)
    (afterOther :
      (OracleWorkLayout.canonical p).presentOther.start + 1 ≤ later.start)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ ((QLayout.oracleSlice later).wireList :
      List (Wire p.ancillaWidth p.systemWidth))) :
    MembershipOutputsSeparated p wire := by
  refine {
    ne_equal := ?_
    ne_good := ?_
    ne_other := ?_
    ne_absent := ?_ }
  · intro slot
    exact (oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).membershipEqual later (by
        have := afterOther
        simp [OracleWorkLayout.canonical] at this ⊢
        omega) (membershipEqualWireAt_mem_slice p slot) member).symm
  · intro slot
    exact (oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).membershipGood later (by
        have := afterOther
        simp [OracleWorkLayout.canonical] at this ⊢
        omega) (membershipGoodWireAt_mem_slice p slot) member).symm
  · exact (oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).presentOther later afterOther
      (oraclePresentOtherWire_mem_slice p) member).symm
  · exact (oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).absent later (by
        have := afterOther
        simp [OracleWorkLayout.canonical] at this ⊢
        omega) (oracleAbsentWire_mem_slice p) member).symm

/-- membership正本回路は4種類の出力wire外の任意wireを保存する。 -/
theorem runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (matchRow : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (separated : MembershipOutputsSeparated p wire) :
    (xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot matchRow).runBasis
        reversibleGatePermutation input wire = input wire := by
  have run := runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit p register layout selectedSlot
    matchRow input slotClean
  have slotsPreserve : ∀ (slots : List (Fin p.K))
      (state : JointBasis p.ancillaWidth p.systemWidth),
      FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot matchRow slots state wire =
        state wire := by
    intro slots
    induction slots with
    | nil => intro state; rfl
    | cons slot slots inductionHypothesis =>
        intro state
        change FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot matchRow slots
          (SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot matchRow state)
            wire = state wire
        rw [inductionHypothesis]
        exact membershipSlotReference_other p register selectedSlot slot matchRow
          state wire (separated.ne_equal slot) (separated.ne_good slot)
          separated.ne_other
  rw [run.1]
  unfold MembershipMatchGoodAndAbsentFlagsXorSpec
  split
  · rw [xBasisAction_other (oracleAbsentWire p) wire separated.ne_absent]
    exact slotsPreserve (List.finRange p.K) input
  · exact slotsPreserve (List.finRange p.K) input

/-- membership正本回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_xorMembershipMatchGoodAndAbsentFlagsCircuit
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (matchRow : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot matchRow).runBasis
        reversibleGatePermutation input) := by
  let output := (xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot matchRow).runBasis
    reversibleGatePermutation input
  let slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input := {
    equalWork_zero := clean.moved_selector.compare_zero
    scratch_zero := clean.moved_selector.scratch_zero }
  have preserve (wire : Wire p.ancillaWidth p.systemWidth)
      (separated : MembershipOutputsSeparated p wire) :
      output wire = input wire :=
    runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other p register layout selectedSlot
      matchRow input slotClean wire separated
  apply EventSortCleanInput.of_agree p input output clean
  · apply List.map_congr_left
    intro wire member
    apply preserve wire
    apply MembershipOutputsSeparated.of_laterSlice p
      (OracleWorkLayout.canonical p).compareWork (by
        simp [OracleWorkLayout.canonical]
        omega) wire
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member
  · intro wire member
    apply preserve wire
    apply MembershipOutputsSeparated.of_laterSlice p
      (OracleWorkLayout.canonical p).andWork (by
        simp [OracleWorkLayout.canonical]
        omega) wire
    simpa [decoderAndScratchWires, oracleAndWorkWires,
      RegisterSlice.wireList] using List.mem_of_mem_drop member
  · apply preserve (oraclePositionWire p)
    apply MembershipOutputsSeparated.of_laterSlice p
      (OracleWorkLayout.canonical p).positionMatch (by
        simp [OracleWorkLayout.canonical])
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨⟨0, by simpa [QParameters.positionMatchWidth] using p.K_pos⟩,
        List.mem_finRange _, rfl⟩
  · apply preserve (oraclePairWire p)
    apply MembershipOutputsSeparated.of_laterSlice p
      (OracleWorkLayout.canonical p).pair (by
        have positionPos : 0 < p.positionMatchWidth := by
          simpa [QParameters.positionMatchWidth] using p.K_pos
        simp [OracleWorkLayout.canonical]
        omega)
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨⟨0, by simpa [QParameters.pairWidth] using p.K_pos⟩,
        List.mem_finRange _, rfl⟩
  · apply List.map_congr_left
    intro wire member
    change wire ∈ oracleCompareWorkWires p ++ [_] at member
    rcases List.mem_append.mp member with compareMember | extraMember
    · apply preserve wire
      apply MembershipOutputsSeparated.of_laterSlice p
        (OracleWorkLayout.canonical p).compareWork (by
          have positionPos : 0 < p.positionMatchWidth := by
            simpa [QParameters.positionMatchWidth] using p.K_pos
          have pairPos : 0 < p.pairWidth := by
            simpa [QParameters.pairWidth] using p.K_pos
          simp [OracleWorkLayout.canonical]
          omega) wire
      simpa [oracleCompareWorkWires, RegisterSlice.wireList] using compareMember
    · simp only [List.mem_singleton] at extraMember
      subst wire
      apply preserve
      apply MembershipOutputsSeparated.of_laterSlice p
        (OracleWorkLayout.canonical p).andWork (by
          simp [OracleWorkLayout.canonical]
          omega)
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
  · intro wire member
    rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
    apply preserve
    apply MembershipOutputsSeparated.of_laterSlice p
      (OracleWorkLayout.canonical p).andWork (by
        simp [OracleWorkLayout.canonical]
        omega)
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
  · intro instruction instructionMember
    apply preserve
    apply MembershipOutputsSeparated.of_sortFlags p
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history, rfl⟩

/-- column membership回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_columnEventMembership
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((columnEventMembership p slot).runBasis reversibleGatePermutation input) :=
  EventSortCleanInput.of_xorMembershipMatchGoodAndAbsentFlagsCircuit p (columnKeyWires p)
    (columnKeyWires_membershipInputLayout p) slot true input clean

/-- row membership回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_rowEventMembership
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((rowEventMembership p slot).runBasis reversibleGatePermutation input) :=
  EventSortCleanInput.of_xorMembershipMatchGoodAndAbsentFlagsCircuit p (systemWires p)
    (systemWires_membershipInputLayout p) slot false input clean

/-- branch bitのX作用はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_x_branch
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p (xBasisAction (oracleBranchWire p) input) := by
  have branchMember : oracleBranchWire p ∈
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).branch).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
  have branchNeLater {width : Nat}
      (later : RegisterSlice p.oracleWorkWidth width)
      (separated :
        (OracleWorkLayout.canonical p).branch.start + 1 ≤ later.start)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice later).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
      wire ≠ oracleBranchWire p :=
    (oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).branch later separated branchMember
      member).symm
  have historyNeBranch
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).wireList :
          List (Wire p.ancillaWidth p.systemWidth))) :
      wire ≠ oracleBranchWire p :=
    oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).sortFlags
      (OracleWorkLayout.canonical p).branch (by
        simp [OracleWorkLayout.canonical]
        omega) member branchMember
  have preserve (wire : Wire p.ancillaWidth p.systemWidth)
      (different : wire ≠ oracleBranchWire p) :
      xBasisAction (oracleBranchWire p) input wire = input wire :=
    xBasisAction_other (oracleBranchWire p) wire different input
  apply EventSortCleanInput.of_agree p input
    (xBasisAction (oracleBranchWire p) input) clean
  · apply List.map_congr_left
    intro wire member
    apply preserve wire
    apply branchNeLater (OracleWorkLayout.canonical p).compareWork (by
      simp [OracleWorkLayout.canonical]
      omega) wire
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member
  · intro wire member
    apply preserve wire
    apply branchNeLater (OracleWorkLayout.canonical p).andWork (by
      simp [OracleWorkLayout.canonical]
      omega) wire
    simpa [decoderAndScratchWires, oracleAndWorkWires,
      RegisterSlice.wireList] using List.mem_of_mem_drop member
  · apply preserve (oraclePositionWire p)
    apply branchNeLater (OracleWorkLayout.canonical p).positionMatch (by
      simp [OracleWorkLayout.canonical])
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨⟨0, by simpa [QParameters.positionMatchWidth] using p.K_pos⟩,
        List.mem_finRange _, rfl⟩
  · apply preserve (oraclePairWire p)
    apply branchNeLater (OracleWorkLayout.canonical p).pair (by
      simp [OracleWorkLayout.canonical])
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨⟨0, by simpa [QParameters.pairWidth] using p.K_pos⟩,
        List.mem_finRange _, rfl⟩
  · apply List.map_congr_left
    intro wire member
    change wire ∈ oracleCompareWorkWires p ++ [_] at member
    rcases List.mem_append.mp member with compareMember | extraMember
    · apply preserve wire
      apply branchNeLater (OracleWorkLayout.canonical p).compareWork (by
        simp [OracleWorkLayout.canonical]
        omega) wire
      simpa [oracleCompareWorkWires, RegisterSlice.wireList] using compareMember
    · simp only [List.mem_singleton] at extraMember
      subst wire
      apply preserve
      apply branchNeLater (OracleWorkLayout.canonical p).andWork (by
        simp [OracleWorkLayout.canonical]
        omega)
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
  · intro wire member
    rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
    apply preserve
    apply branchNeLater (OracleWorkLayout.canonical p).andWork (by
      simp [OracleWorkLayout.canonical]
      omega)
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
  · intro instruction instructionMember
    apply preserve
    apply historyNeBranch
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history, rfl⟩

/-- column branch計算回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_columnEventBranchCompute
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((columnEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input) := by
  rw [runBasis_columnEventBranchCompute_canonical p slot offset input
    clean.moved_selector.scratch_zero]
  split
  · exact EventSortCleanInput.of_x_branch p input clean
  · exact clean

/-- row branch計算回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_rowEventBranchCompute
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input) := by
  rw [runBasis_rowEventBranchCompute_canonical p slot offset input
    clean.moved_selector.scratch_zero]
  split
  · exact EventSortCleanInput.of_x_branch p input clean
  · exact clean

/-- column eventの初期clean性はselectorからbranchまでの全段階を通じて保たれる。 -/
theorem columnEventCandidateUpdateAndSortExecutionTrace_afterBranch_clean
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch := by
  have selectorClean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterSelector := by
    rw [(columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).selector_eq]
    exact EventSortCleanInput.of_columnEventSelectorCompute p slot offset input
      clean
  have movedCopyClean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterMovedCopy := by
    rw [(columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).movedCopy_eq]
    exact EventSortCleanInput.of_columnEventMovedCopy p slot _ selectorClean
  have moveClean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterMoveForward := by
    rw [(columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).moveForward_eq]
    exact EventSortCleanInput.of_columnEventMoveForward p offset _ movedCopyClean
  have membershipClean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterMembership := by
    rw [(columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).membership_eq]
    exact EventSortCleanInput.of_columnEventMembership p slot _ moveClean
  rw [(columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).branch_eq]
  exact EventSortCleanInput.of_columnEventBranchCompute p slot offset _
    membershipClean

/-- row eventの初期clean性はselectorからbranchまでの全段階を通じて保たれる。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterBranch_clean
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch := by
  have selectorClean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterSelector := by
    rw [(rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).selector_eq]
    exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input clean
  have movedCopyClean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMovedCopy := by
    rw [(rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).moved_eq]
    exact EventSortCleanInput.of_rowEventMovedCopy p slot _ selectorClean
  have moveClean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMoveBackward := by
    rw [(rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).moveBackward_eq]
    exact EventSortCleanInput.of_rowEventMoveBackward p offset _ movedCopyClean
  have membershipClean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterMembership := by
    rw [(rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).membership_eq]
    exact EventSortCleanInput.of_rowEventMembership p slot _ moveClean
  rw [(rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).branch_eq]
  exact EventSortCleanInput.of_rowEventBranchCompute p slot offset _
    membershipClean

/-- clean なcandidate前状態でcandidateを生成しても、event sort用workはcleanに保たれる。 -/
theorem EventSortCleanInput.of_xorConfigurationIntoCandidateRegisterCircuit
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((xorConfigurationIntoCandidateRegisterCircuit p register).runBasis
        reversibleGatePermutation input) := by
  let output := (xorConfigurationIntoCandidateRegisterCircuit p register).runBasis
    reversibleGatePermutation input
  have preserve (wire : Wire p.ancillaWidth p.systemWidth)
      (outside : wire ∉
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).candidate).wireList :
            List (Wire p.ancillaWidth p.systemWidth))) :
      output wire = input wire := by
    exact runBasis_xorConfigurationIntoCandidateRegisterCircuit_outside_candidateSlice p register layout
      input wire outside
  apply EventSortCleanInput.of_agree p input output clean
  · apply List.map_congr_left
    intro wire member
    exact preserve wire
      (oracleCompareWorkWire_not_mem_candidateSlice p wire member)
  · intro wire member
    exact preserve wire
      (decoderScratchWire_not_mem_candidateSlice p wire member)
  · exact preserve (oraclePositionWire p)
      (oraclePositionWire_not_mem_candidateSlice p)
  · exact preserve (oraclePairWire p)
      (oraclePairWire_not_mem_candidateRegion p)
  · apply List.map_congr_left
    intro wire member
    exact preserve wire
      (sortCompareWire_not_mem_candidateSlice p wire member)
  · intro wire member
    exact preserve wire
      (sortScratchWire_not_mem_candidateSlice p wire member)
  · intro instruction instructionMember
    exact preserve _ (sortHistoryWire_not_mem_candidateSlice p instruction)

/-- column candidate変更回路はcandidate slice外の任意wireを保存する。 -/
theorem runBasis_columnEventModify_outside_candidateSlice
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation input wire =
      input wire := by
  by_cases collision : offset.val % 2 = 1
  · apply runBasis_columnEventModify_collision_outside p slot offset collision
    · intro member
      exact outside (candidateWordAt_mem_candidateSlice p
        (slotToSortWord p slot) (List.mem_of_mem_take member))
    · intro equal
      apply outside
      rw [equal]
      exact candidateMarkerWire_mem_candidateSlice p (slotToSortWord p slot)
  · apply runBasis_columnEventModify_replacement_outside p slot offset collision
    intro member
    exact outside (candidateWordAt_mem_candidateSlice p
      (slotToSortWord p slot) (List.mem_of_mem_take member))

/-- column candidate変更はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_columnEventModify
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  apply EventSortCleanInput.of_candidateSlice_preserved p input _ clean
  intro wire outside
  exact runBasis_columnEventModify_outside_candidateSlice p slot offset input
    wire outside

/-- row collision のcandidate追加参照作用は、対象candidate word外の任意wireを保存する。 -/
theorem rowEventCollisionAppendReference_other
    (p : QParameters) (degreeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideData : wire ∉
      (candidateWordAt p
        (rowEventCollisionCandidateIndex p degreeSlot)).take p.wordWidth)
    (outsideMarker : wire ≠ candidateMarkerWire p
      (rowEventCollisionCandidateIndex p degreeSlot)) :
    rowEventCollisionAppendReference p degreeSlot input wire = input wire := by
  unfold rowEventCollisionAppendReference
  rw [xBasisAction_other _ wire outsideMarker]
  exact controlledCopyBasisReference_outside_target true (oracleMovedWires p)
    ((candidateWordAt p
      (rowEventCollisionCandidateIndex p degreeSlot)).take p.wordWidth)
    input wire outsideData

/-- cleanな一つのrow collision回路はcandidate slice外の任意wireを保存する。 -/
theorem runBasis_rowEventCollisionModifyAt_outside_candidateSlice
    (p : QParameters) (degreeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot).runBasis
        reversibleGatePermutation input wire = input wire := by
  have outsideData : wire ∉
      (candidateWordAt p
        (rowEventCollisionCandidateIndex p degreeSlot)).take p.wordWidth := by
    intro member
    exact outside (candidateWordAt_mem_candidateSlice p
      (rowEventCollisionCandidateIndex p degreeSlot)
      (List.mem_of_mem_take member))
  have outsideMarker : wire ≠ candidateMarkerWire p
      (rowEventCollisionCandidateIndex p degreeSlot) := by
    intro equal
    apply outside
    rw [equal]
    exact candidateMarkerWire_mem_candidateSlice p
      (rowEventCollisionCandidateIndex p degreeSlot)
  by_cases branchTrue : input (oracleBranchWire p) = true
  · by_cases degreeTrue : input
        (oracleDegreeWireAt p
          (rowEventCollisionDegreeIndex p degreeSlot)) = true
    · rw [runBasis_rowEventCollisionModifyAt_active p degreeSlot input
        clean.moved_selector.scratch_zero clean.moved_selector.pair_zero
        branchTrue degreeTrue]
      exact rowEventCollisionAppendReference_other p degreeSlot input wire
        outsideData outsideMarker
    · rw [runBasis_rowEventCollisionModifyAt_inactive p degreeSlot input
        clean.moved_selector.scratch_zero clean.moved_selector.pair_zero
        (Or.inr (Bool.eq_false_of_not_eq_true degreeTrue))]
  · rw [runBasis_rowEventCollisionModifyAt_inactive p degreeSlot input
      clean.moved_selector.scratch_zero clean.moved_selector.pair_zero
      (Or.inl (Bool.eq_false_of_not_eq_true branchTrue))]

/-- cleanな一つのrow collision回路はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_rowEventCollisionModifyAt
    (p : QParameters) (degreeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot).runBasis
        reversibleGatePermutation input) := by
  apply EventSortCleanInput.of_candidateSlice_preserved p input _ clean
  intro wire outside
  exact runBasis_rowEventCollisionModifyAt_outside_candidateSlice p degreeSlot
    input clean wire outside

/-- row collision回路列はevent sort clean性を帰納的に保存する。 -/
theorem EventSortCleanInput.of_rowEventCollisionSequence
    (p : QParameters) :
    ∀ (slots : List (Fin (p.K - 1)))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      EventSortCleanInput p input →
      EventSortCleanInput p
        ((Circuit.sequence (slots.map fun degreeSlot =>
          controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot)).runBasis
            reversibleGatePermutation input)
  | [], input, clean => by
      rw [Circuit.runBasis_sequence]
      exact clean
  | degreeSlot :: slots, input, clean => by
      simp only [List.map_cons, Circuit.sequence]
      exact EventSortCleanInput.of_rowEventCollisionSequence p slots _
        (EventSortCleanInput.of_rowEventCollisionModifyAt p degreeSlot input clean)

/-- row replacement回路はcandidate slice外の任意wireを保存する。 -/
theorem runBasis_rowEventReplacementModify_outside_candidateSlice
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis reversibleGatePermutation input
        wire = input wire := by
  apply runBasis_rowEventReplacementModify_outside p slot input wire
  intro member
  exact outside (candidateWordAt_mem_candidateSlice p (slotToSortWord p slot)
    (List.mem_of_mem_take member))

/-- row candidate変更はevent sort clean性を保存する。 -/
theorem EventSortCleanInput.of_rowEventModify
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  by_cases collision : offset.val % 2 = 1
  · rw [controlledUpdateSelectedRowCandidateWordCircuit, if_pos collision, controlledUpdateSelectedRowCollisionCandidateWordCircuit]
    exact EventSortCleanInput.of_rowEventCollisionSequence p
      (List.finRange (p.K - 1)) input clean
  · rw [controlledUpdateSelectedRowCandidateWordCircuit, if_neg collision]
    apply EventSortCleanInput.of_candidateSlice_preserved p input _ clean
    intro wire outside
    exact runBasis_rowEventReplacementModify_outside_candidateSlice p slot input
      wire outside

/-- column eventでbranch計算後がcleanなら、sort直前までclean性が保たれる。 -/
theorem columnEventCandidateUpdateAndSortExecutionTrace_afterModify_clean_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterModify := by
  have candidatesClean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates := by
    rw [(columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).candidates_eq]
    exact EventSortCleanInput.of_xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)
      (columnKeyWires_candidateInputLayout p) _ clean
  rw [(columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).modify_eq]
  exact EventSortCleanInput.of_columnEventModify p slot offset _ candidatesClean

/-- row eventでbranch計算後がcleanなら、sort直前までclean性が保たれる。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterModify_clean_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterModify := by
  have candidatesClean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates := by
    rw [(rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).candidates_eq]
    exact EventSortCleanInput.of_xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)
      (systemWires_candidateInputLayout p) _ clean
  rw [(rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).modify_eq]
  exact EventSortCleanInput.of_rowEventModify p slot offset _ candidatesClean

/-- clean 入力から bitonic sort 後も moved-selector writer 用workは clean である。 -/
theorem qBitonicSort_preserves_xorMovedMemberPositionIntoSelectorOutputCircuitClean
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    WriteMovedSelectorSlotClean p
      ((reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
        reversibleGatePermutation input) := by
  let output := (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
    reversibleGatePermutation input
  let reference := CanonicalCandidateSortWithHistoryRestorationSpec p (qTypedBitonicSchedule p) input
  have outputEq : output = reference := by
    simpa [output, reference] using
      runBasis_reversiblySortCandidateWordsAndRestoreHistoryCircuit_eq_reference p input
        clean.sort_compare_zero clean.sort_scratch_zero clean.sort_history_zero
  refine {
    compare_zero := ?_
    scratch_zero := ?_
    position_zero := ?_
    pair_zero := ?_ }
  · change readWires (oracleCompareWorkWires p) output = _
    rw [outputEq]
    rw [canonicalCandidateSortWithHistoryRestorationSpec_preserves_oracleCompare]
    exact clean.moved_selector.compare_zero
  · intro wire member
    change output wire = false
    rw [outputEq]
    dsimp [reference]
    rw [canonicalCandidateSortWithHistoryRestorationSpec_preserves_decoderScratch p
      (qTypedBitonicSchedule p) input wire member]
    exact clean.moved_selector.scratch_zero wire member
  · change output (oraclePositionWire p) = false
    rw [outputEq]
    dsimp [reference]
    rw [canonicalCandidateSortWithHistoryRestorationSpec_preserves_position]
    exact clean.moved_selector.position_zero
  · change output (oraclePairWire p) = false
    rw [outputEq]
    dsimp [reference]
    rw [canonicalCandidateSortWithHistoryRestorationSpec_preserves_pair]
    exact clean.moved_selector.pair_zero

/-- column event 状態記録の sort 前clean性から compute 最終clean性を得る。 -/
theorem columnEventCandidateUpdateAndSortExecutionTrace_output_clean_of_afterModify
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterModify) :
    WriteMovedSelectorSlotClean p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output := by
  rw [(columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).sort_eq]
  exact qBitonicSort_preserves_xorMovedMemberPositionIntoSelectorOutputCircuitClean p _ clean

/-- row event 状態記録の sort 前clean性から compute 最終clean性を得る。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_clean_of_afterModify
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterModify) :
    WriteMovedSelectorSlotClean p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output := by
  rw [(rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).sort_eq]
  exact qBitonicSort_preserves_xorMovedMemberPositionIntoSelectorOutputCircuitClean p _ clean

/-- column eventでbranch計算後がcleanなら、compute最終状態のmoved-selector workもcleanである。 -/
theorem columnEventCandidateUpdateAndSortExecutionTrace_output_clean_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    WriteMovedSelectorSlotClean p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output :=
  columnEventCandidateUpdateAndSortExecutionTrace_output_clean_of_afterModify p slot offset input
    (columnEventCandidateUpdateAndSortExecutionTrace_afterModify_clean_of_afterBranch p slot offset
      input clean)

/-- row eventでbranch計算後がcleanなら、compute最終状態のmoved-selector workもcleanである。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_clean_of_afterBranch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch) :
    WriteMovedSelectorSlotClean p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output :=
  rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_clean_of_afterModify p slot offset input
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterModify_clean_of_afterBranch p slot offset
      input clean)

/-- cleanな入力から開始したcolumn event計算は、末尾でもwriter用workをcleanに戻す。 -/
theorem columnEventCandidateUpdateAndSortExecutionTrace_output_clean
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    WriteMovedSelectorSlotClean p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output :=
  columnEventCandidateUpdateAndSortExecutionTrace_output_clean_of_afterBranch p slot offset input
    (columnEventCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input clean)

/-- cleanな入力から開始したrow event計算は、末尾でもwriter用workをcleanに戻す。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_clean
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    WriteMovedSelectorSlotClean p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output :=
  rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output_clean_of_afterBranch p slot offset input
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input clean)

/-- compact decoderが実際に参照・変更するwireだけを集めた狭いsupport。 -/
def compactDecoderExactSupport (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth)) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  decoderLegalitySupportFor p inputWires ++ [oracleLegalWire p]

/-- compact decoderの全AST葉は狭いsupportの中だけを使用する。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_usesOnly_exact
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth)) :
    circuitUsesOnly (compactDecoderExactSupport p inputWires)
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires) := by
  let support := compactDecoderExactSupport p inputWires
  have supportContains : ∀ wire ∈ decoderLegalitySupportFor p inputWires,
      wire ∈ support := by
    intro wire member
    exact List.mem_append_left _ member
  have inputMembers : ∀ wire ∈ inputWires, wire ∈ support := by
    intro wire member
    apply supportContains
    simp [decoderLegalitySupportFor, member]
  have suffixMembers : ∀ wire ∈ decoderSuffixWires p, wire ∈ support := by
    intro wire member
    apply supportContains
    simp [decoderLegalitySupportFor, member]
  have degreeMembers : ∀ wire ∈ oracleDegreeWires p, wire ∈ support := by
    intro wire member
    apply supportContains
    simp [decoderLegalitySupportFor, member]
  have computeUses : circuitUsesOnly support
      (decoderLegalityCompute
        (splitSystemWords p.wordWidth p.K inputWires)
        (oracleDegreeWires p) (decoderLessWires p) (decoderNeedWires p)
        (decoderGoodWires p) (oracleCompareWorkWires p)
        (decoderAndScratchWires p) (decoderDegreeValidWire p)
        (decoderLegalTemporaryWire p)) := by
    apply circuitUsesOnly_mono supportContains
    exact decoderLegalityCompute_usesOnly_input p inputWires
  have temporaryMember : decoderLegalTemporaryWire p ∈ support := by
    apply supportContains
    simp [decoderLegalitySupportFor, decoderLegalTemporary_mem_andWork]
  have legalMember : oracleLegalWire p ∈ support := by
    simp [support, compactDecoderExactSupport]
  change circuitUsesOnly support
    (.seq
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        (oracleDegreeWires p))
      (Circuit.computeUseUncompute id
        (decoderLegalityCompute
          (splitSystemWords p.wordWidth p.K inputWires)
          (oracleDegreeWires p) (decoderLessWires p) (decoderNeedWires p)
          (decoderGoodWires p) (oracleCompareWorkWires p)
          (decoderAndScratchWires p) (decoderDegreeValidWire p)
          (decoderLegalTemporaryWire p))
        (safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p))))
  exact ⟨
    circuitUsesOnly_xorDelimiterDegreeOneHotIntoTargetsCircuit support p.wordWidth inputWires
      (decoderSuffixWires p) (oracleDegreeWires p) inputMembers suffixMembers
      degreeMembers,
    circuitUsesOnly_computeUseUncompute support _ _ computeUses
      (circuitUsesOnly_safeCnot support _ _ temporaryMember legalMember)⟩

/-- persistent computeのdecoder後段は、三つの出力領域外のwireを保存する。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_eq_compactDecoder_outside
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (rowMode : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsidePresent : wire ∉ oraclePresentWires p)
    (differentCondition : wire ≠ oracleDegreeConditionWire p)
    (differentOne : wire ≠ oracleOneWire p) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input wire =
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input wire := by
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
          reversibleGatePermutation input = xBasisAction one conditioned := by
    simp only [computeSharedDecoderPresenceParityAndOneFlagsCircuit, runBasis_seq, runBasis_x]
    rfl
  have conditionAbsentSources : condition ∉ sources := by
    simpa [condition, sources, degree] using
      oracleDegreeConditionWire_not_mem_degreeConditionSources p rowMode
  rw [outputEq]
  rw [xBasisAction_other one wire (by simpa [one] using differentOne)]
  dsimp only [conditioned]
  rw [runBasis_xorSourceParityIntoTargetCircuit_other sources condition wire presented
    conditionAbsentSources (by simpa [condition] using differentCondition)]
  dsimp only [presented]
  change (xorDegreeSuffixParityIntoSlotPresenceCircuit degree 0 present).runBasis
      reversibleGatePermutation decoded wire = decoded wire
  rw [runBasis_xorDegreeSuffixParityIntoSlotPresenceCircuit_outside degree present 0 wire decoded]
  · simpa [degree, present] using oracleDegreeWires_disjoint_presentWires p
  · simpa [present] using outsidePresent

/-- compare/AND workはpersistent compute後にもcompact decoder直後の値を保つ。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_work_eq_compactDecoder
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (rowMode : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (workMember : wire ∈ oracleCompareWorkWires p ∨
      wire ∈ oracleAndWorkWires p) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input wire =
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input wire := by
  apply computeSharedDecoderPresenceParityAndOneFlagsCircuit_eq_compactDecoder_outside p inputWires rowMode
    input wire
  · rcases workMember with compareMember | andMember
    · exact fun presentMember =>
        (List.disjoint_left.mp (oraclePresentWires_disjoint_compareWork p)
          presentMember) compareMember
    · exact fun presentMember =>
        (List.disjoint_left.mp (oraclePresentWires_disjoint_andWork p)
          presentMember) andMember
  · intro equal
    subst wire
    rcases workMember with compareMember | andMember
    · exact (List.disjoint_left.mp
        (oraclePersistentSpecialWires_disjoint_compareWork p)
        (oracleDegreeConditionWire_mem_special p)) compareMember
    · exact (List.disjoint_left.mp
        (oraclePersistentSpecialWires_disjoint_andWork p)
        (oracleDegreeConditionWire_mem_special p)) andMember
  · intro equal
    subst wire
    rcases workMember with compareMember | andMember
    · exact (List.disjoint_left.mp
        (oraclePersistentSpecialWires_disjoint_compareWork p)
        (oracleOneWire_mem_special p)) compareMember
    · exact (List.disjoint_left.mp
        (oraclePersistentSpecialWires_disjoint_andWork p)
        (oracleOneWire_mem_special p)) andMember

/-- candidate以後かつcompare以前のsliceは、compact decoderの狭いsupportの外にある。 -/
theorem middleOracleSlice_not_mem_compactDecoderExactSupport
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (inputDisjointWork : inputWires.Disjoint (diagonalOracleWorkWires p))
    {width : Nat} (middle : RegisterSlice p.oracleWorkWidth width)
    (candidateBefore :
      (OracleWorkLayout.canonical p).candidate.start + p.candidateWidth ≤
        middle.start)
    (beforeCompare : middle.start + width ≤
      (OracleWorkLayout.canonical p).compareWork.start)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (middleMember : wire ∈
      ((QLayout.oracleSlice middle).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    wire ∉ compactDecoderExactSupport p inputWires := by
  intro supportMember
  have cases : wire ∈ inputWires ∨ wire ∈ decoderSuffixWires p ∨
      wire ∈ oracleDegreeWires p ∨ wire ∈ oracleCompareWorkWires p ∨
      wire ∈ oracleAndWorkWires p ∨ wire = oracleLegalWire p := by
    simpa only [compactDecoderExactSupport, decoderLegalitySupportFor,
      List.mem_append, List.mem_singleton, or_assoc] using supportMember
  rcases cases with inputMember | suffixMember | degreeMember | compareMember |
    andMember | legalEqual
  · exact (List.disjoint_left.mp inputDisjointWork inputMember)
      (diagonalOracleSlice_subset_work p middle middleMember)
  · have outside := laterOracleListWire_not_mem_earlierSlice p
      (OracleWorkLayout.canonical p).candidate middle candidateBefore wire
      middleMember
    apply outside
    simpa [decoderSuffixWires, RegisterSlice.wireList] using
      List.mem_of_mem_take suffixMember
  · have outside := laterOracleListWire_not_mem_earlierSlice p
      (OracleWorkLayout.canonical p).degree middle (by
        simp [OracleWorkLayout.canonical] at candidateBefore ⊢
        omega) wire middleMember
    apply outside
    simpa [oracleDegreeWires, RegisterSlice.wireList] using degreeMember
  · have outside := laterOracleListWire_not_mem_earlierSlice p middle
      (OracleWorkLayout.canonical p).compareWork beforeCompare wire (by
        simpa [oracleCompareWorkWires, RegisterSlice.wireList] using
          compareMember)
    exact outside middleMember
  · have outside := laterOracleListWire_not_mem_earlierSlice p middle
      (OracleWorkLayout.canonical p).andWork (by
        simp [OracleWorkLayout.canonical] at beforeCompare ⊢
        omega) wire (by
          simpa [oracleAndWorkWires, RegisterSlice.wireList] using andMember)
    exact outside middleMember
  · subst wire
    have outside := laterOracleListWire_not_mem_earlierSlice p
      (OracleWorkLayout.canonical p).legal middle (by
        simp [OracleWorkLayout.canonical] at candidateBefore ⊢
        omega) (oracleLegalWire p) middleMember
    apply outside
    simp [oracleLegalWire, RegisterSlice.wireList]

/-- candidate以後かつcompare以前のsliceはpersistent compute全体で保存される。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_middleOracleSlice
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (inputDisjointWork : inputWires.Disjoint (diagonalOracleWorkWires p))
    (rowMode : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    {width : Nat} (middle : RegisterSlice p.oracleWorkWidth width)
    (candidateBefore :
      (OracleWorkLayout.canonical p).candidate.start + p.candidateWidth ≤
        middle.start)
    (beforeCompare : middle.start + width ≤
      (OracleWorkLayout.canonical p).compareWork.start)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (middleMember : wire ∈
      ((QLayout.oracleSlice middle).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input wire = input wire := by
  have compactPreserves :
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
          reversibleGatePermutation input wire = input wire :=
    Circuit.runBasis_outside_of_usesOnly
      (compactDecoderExactSupport p inputWires)
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires)
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_usesOnly_exact p inputWires)
      input wire
      (middleOracleSlice_not_mem_compactDecoderExactSupport p inputWires
        inputDisjointWork middle candidateBefore beforeCompare wire middleMember)
  have outsidePresent : wire ∉ oraclePresentWires p := by
    have outside := laterOracleListWire_not_mem_earlierSlice p
      (OracleWorkLayout.canonical p).present middle (by
        simp [OracleWorkLayout.canonical] at candidateBefore ⊢
        omega) wire middleMember
    simpa [oraclePresentWires, RegisterSlice.wireList] using outside
  have outsideSpecial : wire ∉ oraclePersistentSpecialWires p := by
    have outside := laterOracleListWire_not_mem_earlierSlice p
      (oraclePersistentSpecialSlice p) middle (by
        simp [oraclePersistentSpecialSlice, OracleWorkLayout.canonical]
          at candidateBefore ⊢
        omega) wire middleMember
    simpa [oraclePersistentSpecialWires] using outside
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

/-- persistent computeはclean入力からevent用tracked workをcleanのまま出力する。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_output_eventSortClean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (persistentClean : OraclePersistentCleanInput p inputWires configuration input)
    (eventClean : EventSortCleanInput p input)
    (inputDisjointWork : inputWires.Disjoint (diagonalOracleWorkWires p))
    (rowMode : Bool) :
    EventSortCleanInput p
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input) := by
  let output := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
    reversibleGatePermutation input
  let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
    reversibleGatePermutation input
  have decodedWork := xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_work_clean_of_clean p
    inputWires layout.decoder configuration input persistentClean.decoder
  have workPreserved (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ oracleCompareWorkWires p ∨
        wire ∈ oracleAndWorkWires p) : output wire = decoded wire := by
    simpa [output, decoded] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_work_eq_compactDecoder p inputWires rowMode input
        wire member
  have compareZero : readWires (oracleCompareWorkWires p) output =
      List.replicate (oracleCompareWorkWires p).length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    rw [workPreserved wire (Or.inl member)]
    exact decodedWork.1 wire member
  have andZero : ∀ wire ∈ oracleAndWorkWires p, output wire = false := by
    intro wire member
    rw [workPreserved wire (Or.inr member)]
    exact decodedWork.2 wire member
  have preserveMiddle {width : Nat}
      (middle : RegisterSlice p.oracleWorkWidth width)
      (candidateBefore :
        (OracleWorkLayout.canonical p).candidate.start + p.candidateWidth ≤
          middle.start)
      (beforeCompare : middle.start + width ≤
        (OracleWorkLayout.canonical p).compareWork.start)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈
        ((QLayout.oracleSlice middle).wireList :
          List (Wire p.ancillaWidth p.systemWidth))) :
      output wire = input wire := by
    simpa [output] using computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_middleOracleSlice p
      inputWires inputDisjointWork rowMode input middle candidateBefore
      beforeCompare wire member
  refine {
    moved_selector := {
      compare_zero := compareZero
      scratch_zero := ?_
      position_zero := ?_
      pair_zero := ?_ }
    sort_compare_zero := ?_
    sort_scratch_zero := ?_
    sort_history_zero := ?_ }
  · intro wire member
    exact andZero wire (List.mem_of_mem_drop member)
  · change output (oraclePositionWire p) = false
    have positionMember : oraclePositionWire p ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).positionMatch).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr
        ⟨⟨0, by simpa [QParameters.positionMatchWidth] using p.K_pos⟩,
          List.mem_finRange _, rfl⟩
    rw [preserveMiddle (OracleWorkLayout.canonical p).positionMatch (by
      simp [OracleWorkLayout.canonical]
      omega) (by simp [OracleWorkLayout.canonical])
      (oraclePositionWire p) positionMember]
    exact eventClean.moved_selector.position_zero
  · change output (oraclePairWire p) = false
    have pairMember : oraclePairWire p ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).pair).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr
        ⟨⟨0, by simp [QParameters.pairWidth, p.K_pos]⟩,
          List.mem_finRange _, rfl⟩
    rw [preserveMiddle (OracleWorkLayout.canonical p).pair (by
      simp [OracleWorkLayout.canonical]
      omega) (by simp [OracleWorkLayout.canonical])
      (oraclePairWire p) pairMember]
    exact eventClean.moved_selector.pair_zero
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    rcases List.mem_append.mp member with compareMember | extraMember
    · exact pointwise_false_of_readWires_eq_replicate _ output compareZero wire
        compareMember
    · simp only [List.mem_singleton] at extraMember
      subst wire
      exact andZero _ (by simp [oracleAndWorkWires])
  · intro wire member
    have fullMember := sortAndScratchWires_mem_andSlice p member
    apply andZero wire
    simpa [oracleAndWorkWires, RegisterSlice.wireList] using fullMember
  · intro instruction instructionMember
    change output ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire
        instruction.history) = false
    rw [preserveMiddle (OracleWorkLayout.canonical p).sortFlags (by
      simp [OracleWorkLayout.canonical]) (by
        simp [OracleWorkLayout.canonical]
        omega) _ (by
          rw [RegisterSlice.wireList]
          exact List.mem_map.mpr
            ⟨instruction.history, List.mem_finRange _, rfl⟩)]
    exact eventClean.sort_history_zero instruction instructionMember

/-- system registerとoracle work registerは型と配置の双方で交わらない。 -/
theorem systemWires_disjoint_diagonalOracleWorkWires (p : QParameters) :
    (systemWires p).Disjoint (diagonalOracleWorkWires p) := by
  let work := (QLayout.canonical p).oracleWork
  simpa [systemWires, QLayout.systemWire, diagonalOracleWorkWires, work] using
    (RegisterSlice.systemWires_disjoint_wireList
      (systemWidth := p.systemWidth) work)

/-- column-key registerとoracle work registerは正本layout上で交わらない。 -/
theorem columnKeyWires_disjoint_diagonalOracleWorkWires (p : QParameters) :
    (columnKeyWires p).Disjoint (diagonalOracleWorkWires p) := by
  let key := (QLayout.canonical p).columnKey
  let work := (QLayout.canonical p).oracleWork
  have separated : key.start + p.systemWidth ≤ work.start := by
    simp [key, work, QLayout.canonical]
    omega
  have disjoint :
      (key.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (work.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    key.wireList_disjoint_of_end_le_start work separated
  simpa [columnKeyWires, columnKeyWire, diagonalOracleWorkWires, key, work,
    RegisterSlice.wireList] using disjoint

/-- canonical row persistent computeはevent計算開始時のtracked workをcleanに保つ。 -/
theorem rowOraclePersistentOutput_eventSortClean
    (p : QParameters) (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (persistentClean : OraclePersistentCleanInput p (systemWires p)
      configuration input)
    (eventClean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input) :=
  computeSharedDecoderPresenceParityAndOneFlagsCircuit_output_eventSortClean p (systemWires p)
    (systemWires_oraclePersistentInputLayout p) configuration input
    persistentClean eventClean (systemWires_disjoint_diagonalOracleWorkWires p)
    true

/-- canonical column persistent computeはevent計算開始時のtracked workをcleanに保つ。 -/
theorem columnOraclePersistentOutput_eventSortClean
    (p : QParameters) (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (persistentClean : OraclePersistentCleanInput p (columnKeyWires p)
      configuration input)
    (eventClean : EventSortCleanInput p input) :
    EventSortCleanInput p
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input) :=
  computeSharedDecoderPresenceParityAndOneFlagsCircuit_output_eventSortClean p (columnKeyWires p)
    (columnKeyWires_oraclePersistentInputLayout p) configuration input
    persistentClean eventClean
    (columnKeyWires_disjoint_diagonalOracleWorkWires p) false

end ReversibleCircuit

end ProbabilityGeneratorQProof
