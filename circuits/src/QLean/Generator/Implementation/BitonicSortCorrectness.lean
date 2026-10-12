import QLean.Generator.Implementation.QDecoderCorrectness
import QLean.Generator.Implementation.BitonicNetworkCorrectness
import QLean.Circuits.Foundation.BitonicScheduleCorrectnessAnalytic
import QLean.Circuits.Foundation.BitonicPermutationCorrectnessAnalytic
import QLean.Generator.Analysis.BitonicTotalStage

/-!
# 可逆bitonic sort回路の基底作用証明

一個のcompare--exchangeから始め、履歴flagを保持するschedule全体の作用を証明する。
比較対象wordの全値や全計算基底は列挙せず、既証明の一般比較器とcontrolled swapを合成する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- Q正本のbitonic scheduleも、一般の`K>0`について履歴wireを共有しない。 -/
theorem qTypedBitonicSchedule_history_nodup (p : QParameters) :
    ((qTypedBitonicSchedule p).map
      (fun instruction => instruction.history)).Nodup := by
  let positiveHistory : 0 < p.sortFlagWidth := by
    simp [QParameters.sortFlagWidth, QParameters.sortWordCount]
  have fits : (BitonicTotalProgram.qBareSchedule p).length ≤ p.sortFlagWidth := by
    unfold BitonicTotalProgram.qBareSchedule
    rw [List.length_map]
    simpa [BitonicTotalProgram.recursiveSort, QParameters.sortFlagWidth,
      QParameters.sortWordCount, recursiveBitonicWidth_eq_pow, pow_two,
      Nat.mul_assoc] using
      VerifiedCircuitCore.bitonicSortSchedule_length_le_historyCapacity
        (Nat.clog 2 p.K) true
  change ((BitonicTotalProgram.qSchedule p).map
    (fun instruction => instruction.history)).Nodup
  unfold BitonicTotalProgram.qSchedule BitonicTotalProgram.attachHistory
  exact VerifiedCircuitCore.attachBitonicHistory_history_nodup
    positiveHistory (BitonicTotalProgram.qBareSchedule p) fits

/-- Q正本scheduleの全命令は異なる二candidate wordを比較する。 -/
theorem qTypedBitonicSchedule_left_ne_right
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    instruction.left ≠ instruction.right := by
  change instruction ∈ BitonicTotalProgram.qSchedule p at member
  unfold BitonicTotalProgram.qSchedule BitonicTotalProgram.attachHistory at member
  apply VerifiedCircuitCore.attachBitonicHistoryFrom_all_distinct
      (by simp [QParameters.sortFlagWidth, QParameters.sortWordCount]) 0
      (BitonicTotalProgram.qBareSchedule p) _ instruction member
  intro source sourceMember
  unfold BitonicTotalProgram.qBareSchedule at sourceMember
  rcases List.mem_map.mp sourceMember with ⟨original, originalMember, rfl⟩
  intro equal
  apply (VerifiedCircuitCore.bitonicSortSchedule_all_distinct
    (Nat.clog 2 p.K) true original originalMember)
  apply Fin.ext
  simpa [BitonicTotalProgram.cast,
    VerifiedCircuitCore.BitonicCompareExchange.cast] using
    congrArg Fin.val equal

/-- sort証明で使うcandidate wordの長さはmarker込みで`wordWidth+1`である。 -/
@[simp] theorem sortCandidateWordAt_length (p : QParameters)
    (word : Fin p.sortWordCount) :
    (candidateWordAt p word).length = p.wordWidth + 1 := by
  simp [candidateWordAt]

/-- sort証明用に、candidate内の`(word,bit)`物理wire写像が単射であることを示す。 -/
theorem sortCandidateWordWire_pair_injective (p : QParameters) :
    Function.Injective (fun pair :
      Fin p.sortWordCount × Fin (p.wordWidth + 1) =>
        candidateWordWire p pair.1 pair.2) := by
  intro left right equal
  let slice := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  have localEqual :
      left.1.val * (p.wordWidth + 1) + left.2.val =
        right.1.val * (p.wordWidth + 1) + right.2.val := by
    have wireNumbers := congrArg wireNumber equal
    simpa [candidateWordWire, slice, Nat.add_assoc] using
      Nat.add_left_cancel wireNumbers
  have radixPos : 0 < p.wordWidth + 1 := Nat.zero_lt_succ _
  have wordValues : left.1.val = right.1.val := by
    have divided := congrArg (fun value => value / (p.wordWidth + 1)) localEqual
    have leftDivision :
        (left.1.val * (p.wordWidth + 1) + left.2.val) /
            (p.wordWidth + 1) = left.1.val := by
      rw [Nat.mul_comm left.1.val (p.wordWidth + 1)]
      rw [Nat.mul_add_div radixPos]
      simp [Nat.div_eq_of_lt left.2.isLt]
    have rightDivision :
        (right.1.val * (p.wordWidth + 1) + right.2.val) /
            (p.wordWidth + 1) = right.1.val := by
      rw [Nat.mul_comm right.1.val (p.wordWidth + 1)]
      rw [Nat.mul_add_div radixPos]
      simp [Nat.div_eq_of_lt right.2.isLt]
    exact leftDivision.symm.trans (divided.trans rightDivision)
  have wordEqual : left.1 = right.1 := Fin.ext wordValues
  have bitValues : left.2.val = right.2.val := by
    rw [wordValues] at localEqual
    exact Nat.add_left_cancel localEqual
  have bitEqual : left.2 = right.2 := Fin.ext bitValues
  exact Prod.ext wordEqual bitEqual

/-- sort証明で使う一個のcandidate wordにはwire重複がない。 -/
theorem sortCandidateWordAt_nodup (p : QParameters)
    (word : Fin p.sortWordCount) : (candidateWordAt p word).Nodup := by
  apply List.Nodup.map _ (List.nodup_finRange (p.wordWidth + 1))
  intro left right equal
  have pairEqual : (word, left) = (word, right) :=
    sortCandidateWordWire_pair_injective p
      (show candidateWordWire p word left =
        candidateWordWire p word right from equal)
  exact congrArg Prod.snd pairEqual

/-- sort証明で使う異なるcandidate wordのwire列は互いに素である。 -/
theorem sortCandidateWordAt_disjoint_of_ne (p : QParameters)
    (left right : Fin p.sortWordCount) (different : left ≠ right) :
    (candidateWordAt p left).Disjoint (candidateWordAt p right) := by
  rw [List.disjoint_left]
  intro wire leftMember rightMember
  rcases List.mem_map.mp leftMember with ⟨leftBit, _, leftWire⟩
  rcases List.mem_map.mp rightMember with ⟨rightBit, _, rightWire⟩
  have pairEqual : (left, leftBit) = (right, rightBit) :=
    sortCandidateWordWire_pair_injective p (leftWire.trans rightWire.symm)
  exact different (congrArg Prod.fst pairEqual)

/-- candidate wordの任意wireはcandidate slice全体に属する。 -/
theorem sortCandidateWordAt_mem_candidateSlice
    (p : QParameters) (word : Fin p.sortWordCount)
    {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ candidateWordAt p word) :
    wire ∈ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  rcases List.mem_map.mp member with ⟨bit, _, rfl⟩
  apply List.mem_map.mpr
  let localIndex : Fin p.candidateWidth :=
    ⟨word.val * (p.wordWidth + 1) + bit.val, by
      simp only [QParameters.candidateWidth]
      nlinarith [word.isLt, bit.isLt]⟩
  exact ⟨localIndex, List.mem_finRange _, rfl⟩

/-- sort比較flagの任意wireはcompare sliceまたはAND sliceに属する。 -/
theorem sortCompareWorkWires_mem_compare_or_and
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ sortCompareWorkWires p) :
    wire ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).compareWork).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) ∨
      wire ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).andWork).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  rw [sortCompareWorkWires, List.mem_append] at member
  rcases member with comparisonMember | extraMember
  · left
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using comparisonMember
  · right
    simp only [List.mem_singleton] at extraMember
    subst wire
    simp [RegisterSlice.wireList]

/-- sort用AND scratchの任意wireはAND slice全体に属する。 -/
theorem sortAndScratchWires_mem_andSlice
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ sortAndScratchWires p) :
    wire ∈ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).andWork).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
  simp [RegisterSlice.wireList]

/-- 型安全なhistory添字のwireはsort flag slice全体に属する。 -/
theorem sortHistoryWire_mem_sortSlice (p : QParameters)
    (history : Fin p.sortFlagWidth) :
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire history ∈
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  simp [RegisterSlice.wireList]

/-- candidate sliceとsort flag sliceは互いに素である。 -/
theorem sortCandidateSlice_disjoint_historySlice (p : QParameters) :
    ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)).Disjoint
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical]
  omega

/-- candidate sliceとcompare work sliceは互いに素である。 -/
theorem sortCandidateSlice_disjoint_compareSlice (p : QParameters) :
    ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)).Disjoint
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).compareWork).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical]
  omega

/-- candidate sliceとAND work sliceは互いに素である。 -/
theorem sortCandidateSlice_disjoint_andSlice (p : QParameters) :
    ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)).Disjoint
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).andWork).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical]
  omega

/-- sort flag sliceとcompare work sliceは互いに素である。 -/
theorem sortHistorySlice_disjoint_compareSlice (p : QParameters) :
    ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).wireList :
        List (Wire p.ancillaWidth p.systemWidth)).Disjoint
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).compareWork).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical]
  omega

/-- sort flag sliceとAND work sliceは互いに素である。 -/
theorem sortHistorySlice_disjoint_andSlice (p : QParameters) :
    ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).wireList :
        List (Wire p.ancillaWidth p.systemWidth)).Disjoint
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).andWork).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical]
  omega

/-- sort比較flag列の長さはcandidate word長と一致する。 -/
@[simp] theorem sortCompareWorkWires_length (p : QParameters) :
    (sortCompareWorkWires p).length = p.wordWidth + 1 := by
  simp [sortCompareWorkWires]

/-- sort用AND scratchは比較flag本数以上確保されている。 -/
theorem sortCompareWorkWires_length_le_scratch (p : QParameters) :
    (sortCompareWorkWires p).length ≤ (sortAndScratchWires p).length := by
  simp [sortCompareWorkWires, sortAndScratchWires,
    QParameters.andWorkWidth, QParameters.wordWidth]
  omega

/-- sort用AND scratch列にはwire重複がない。 -/
theorem sortAndScratchWires_nodup (p : QParameters) :
    (sortAndScratchWires p).Nodup := by
  let slice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  apply List.Nodup.map _ (List.nodup_finRange (p.andWorkWidth - 1))
  intro left right equal
  have shiftedEqual :
      (⟨left.val + 1, by
          simp [QParameters.andWorkWidth] at left ⊢
          omega⟩ : Fin p.andWorkWidth) =
        ⟨right.val + 1, by
          simp [QParameters.andWorkWidth] at right ⊢
          omega⟩ := by
    apply slice.ancillaWire_injective
    simpa [sortAndScratchWires, slice] using equal
  apply Fin.ext
  have values := congrArg Fin.val shiftedEqual
  exact Nat.add_right_cancel values

/-- AND slice先頭の追加比較flagは、先頭を除いたsort scratch列に含まれない。 -/
theorem sortCompareExtra_not_mem_scratch (p : QParameters) :
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).andWork).ancillaWire
        ⟨0, by simp [QParameters.andWorkWidth]⟩ ∉ sortAndScratchWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  let slice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have indexEqual :
      (⟨0, by simp [QParameters.andWorkWidth]⟩ : Fin p.andWorkWidth) =
        ⟨index.val + 1, by
          simp [QParameters.andWorkWidth] at index ⊢
          omega⟩ := by
    apply slice.ancillaWire_injective
    simpa [sortAndScratchWires, slice] using equal.symm
  have values := congrArg Fin.val indexEqual
  simp at values

/-- sort比較flag列にはwire重複がない。 -/
theorem sortCompareWorkWires_nodup (p : QParameters) :
    (sortCompareWorkWires p).Nodup := by
  let comparison := oracleCompareWorkWires p
  let extra : Wire p.ancillaWidth p.systemWidth :=
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).ancillaWire
      ⟨0, by simp [QParameters.andWorkWidth]⟩
  have comparisonNodup : comparison.Nodup := by
    let slice := QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork
    simpa [comparison, oracleCompareWorkWires, RegisterSlice.wireList, slice] using
      (RegisterSlice.wireList_nodup (systemWidth := p.systemWidth) slice)
  have extraAbsent : extra ∉ comparison := by
    intro member
    have extraMember : extra ∈ oracleAndWorkWires p := by
      simp [extra, oracleAndWorkWires]
    exact (List.disjoint_left.mp
      (oracleCompareWorkWires_disjoint_andWork p) member) extraMember
  simpa [sortCompareWorkWires, comparison, extra, oracleCompareWorkWires] using
    (List.nodup_append.mpr ⟨comparisonNodup, by simp, by
      intro wire member target targetMember
      simp only [List.mem_singleton] at targetMember
      subst target
      intro equal
      subst wire
      exact extraAbsent member⟩)

/-- sort比較flag列とsort AND scratch列は互いに素である。 -/
theorem sortCompareWorkWires_disjoint_scratch (p : QParameters) :
    (sortCompareWorkWires p).Disjoint (sortAndScratchWires p) := by
  rw [List.disjoint_left]
  intro wire flagMember scratchMember
  rcases sortCompareWorkWires_mem_compare_or_and p flagMember with
    compareMember | andMember
  · have scratchFull := sortAndScratchWires_mem_andSlice p scratchMember
    have fullDisjoint :
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).compareWork).wireList :
            List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).andWork).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oracleCompareWorkWires, oracleAndWorkWires,
        RegisterSlice.wireList] using
          oracleCompareWorkWires_disjoint_andWork p
    exact (List.disjoint_left.mp fullDisjoint compareMember) scratchFull
  · rw [sortCompareWorkWires] at flagMember
    rcases List.mem_append.mp flagMember with comparisonMember | extraMember
    · have comparisonFull : wire ∈ oracleCompareWorkWires p := by
        simpa [oracleCompareWorkWires] using comparisonMember
      have scratchFull : wire ∈ oracleAndWorkWires p := by
        simpa [oracleAndWorkWires, RegisterSlice.wireList] using
          sortAndScratchWires_mem_andSlice p scratchMember
      exact (List.disjoint_left.mp
        (oracleCompareWorkWires_disjoint_andWork p) comparisonFull) scratchFull
    · simp only [List.mem_singleton] at extraMember
      subst wire
      exact sortCompareExtra_not_mem_scratch p scratchMember

/-- 任意candidate wordとsort比較flag列は互いに素である。 -/
theorem sortCandidateWordAt_disjoint_compare
    (p : QParameters) (word : Fin p.sortWordCount) :
    (candidateWordAt p word).Disjoint (sortCompareWorkWires p) := by
  rw [List.disjoint_left]
  intro wire candidateMember compareMember
  have candidateFull := sortCandidateWordAt_mem_candidateSlice p word candidateMember
  rcases sortCompareWorkWires_mem_compare_or_and p compareMember with
    compareFull | andFull
  · exact (List.disjoint_left.mp
      (sortCandidateSlice_disjoint_compareSlice p) candidateFull) compareFull
  · exact (List.disjoint_left.mp
      (sortCandidateSlice_disjoint_andSlice p) candidateFull) andFull

/-- 任意candidate wordとsort AND scratch列は互いに素である。 -/
theorem sortCandidateWordAt_disjoint_scratch
    (p : QParameters) (word : Fin p.sortWordCount) :
    (candidateWordAt p word).Disjoint (sortAndScratchWires p) := by
  rw [List.disjoint_left]
  intro wire candidateMember scratchMember
  exact (List.disjoint_left.mp (sortCandidateSlice_disjoint_andSlice p)
    (sortCandidateWordAt_mem_candidateSlice p word candidateMember))
      (sortAndScratchWires_mem_andSlice p scratchMember)

/-- 指定history wireは任意candidate wordに含まれない。 -/
theorem sortHistoryWire_not_mem_candidate
    (p : QParameters) (history : Fin p.sortFlagWidth)
    (word : Fin p.sortWordCount) :
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire history ∉
      candidateWordAt p word := by
  intro member
  exact (List.disjoint_left.mp (sortCandidateSlice_disjoint_historySlice p)
    (sortCandidateWordAt_mem_candidateSlice p word member))
      (sortHistoryWire_mem_sortSlice p history)

/-- 指定history wireはsort比較flag列に含まれない。 -/
theorem sortHistoryWire_not_mem_compare
    (p : QParameters) (history : Fin p.sortFlagWidth) :
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire history ∉
      sortCompareWorkWires p := by
  intro member
  have historyFull := sortHistoryWire_mem_sortSlice p history
  rcases sortCompareWorkWires_mem_compare_or_and p member with
    compareFull | andFull
  · exact (List.disjoint_left.mp (sortHistorySlice_disjoint_compareSlice p)
      historyFull) compareFull
  · exact (List.disjoint_left.mp (sortHistorySlice_disjoint_andSlice p)
      historyFull) andFull

/-- 指定history wireはsort AND scratch列に含まれない。 -/
theorem sortHistoryWire_not_mem_scratch
    (p : QParameters) (history : Fin p.sortFlagWidth) :
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire history ∉
      sortAndScratchWires p := by
  intro member
  exact (List.disjoint_left.mp (sortHistorySlice_disjoint_andSlice p)
    (sortHistoryWire_mem_sortSlice p history))
      (sortAndScratchWires_mem_andSlice p member)

/-- Q scheduleの一命令が使うcandidate・比較・scratch・history全配置はNodupである。 -/
theorem qTypedBitonicInstruction_layout
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p) :
    let historyWire := (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history
    (candidateWordAt p instruction.left ++
      candidateWordAt p instruction.right ++ sortCompareWorkWires p ++
      sortAndScratchWires p ++ [historyWire]).Nodup := by
  dsimp only
  let left := candidateWordAt p instruction.left
  let right := candidateWordAt p instruction.right
  let flags := sortCompareWorkWires p
  let scratches := sortAndScratchWires p
  let historyWire : Wire p.ancillaWidth p.systemWidth := (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history
  have instructionDifferent := qTypedBitonicSchedule_left_ne_right p instruction member
  have candidatePairNodup : (left ++ right).Nodup :=
    List.nodup_append.mpr ⟨sortCandidateWordAt_nodup p instruction.left,
      sortCandidateWordAt_nodup p instruction.right, by
        intro leftWire leftMember rightWire rightMember equal
        subst rightWire
        exact (List.disjoint_left.mp
          (sortCandidateWordAt_disjoint_of_ne p instruction.left
            instruction.right instructionDifferent) leftMember) rightMember⟩
  have workNodup : (flags ++ scratches).Nodup :=
    List.nodup_append.mpr ⟨sortCompareWorkWires_nodup p,
      sortAndScratchWires_nodup p, by
        intro flag flagMember scratch scratchMember equal
        subst scratch
        exact (List.disjoint_left.mp
          (sortCompareWorkWires_disjoint_scratch p) flagMember) scratchMember⟩
  have candidatesDisjointWork : (left ++ right).Disjoint (flags ++ scratches) := by
    rw [List.disjoint_left]
    intro wire candidateMember workMember
    rcases List.mem_append.mp candidateMember with leftMember | rightMember
    · rcases List.mem_append.mp workMember with flagMember | scratchMember
      · exact (List.disjoint_left.mp
          (sortCandidateWordAt_disjoint_compare p instruction.left)
            leftMember) flagMember
      · exact (List.disjoint_left.mp
          (sortCandidateWordAt_disjoint_scratch p instruction.left)
            leftMember) scratchMember
    · rcases List.mem_append.mp workMember with flagMember | scratchMember
      · exact (List.disjoint_left.mp
          (sortCandidateWordAt_disjoint_compare p instruction.right)
            rightMember) flagMember
      · exact (List.disjoint_left.mp
          (sortCandidateWordAt_disjoint_scratch p instruction.right)
            rightMember) scratchMember
  have prefixNodup : ((left ++ right) ++ (flags ++ scratches)).Nodup :=
    List.nodup_append.mpr ⟨candidatePairNodup, workNodup, by
      intro candidate candidateMember work workMember equal
      subst work
      exact (List.disjoint_left.mp candidatesDisjointWork candidateMember) workMember⟩
  have historyAbsent : historyWire ∉ (left ++ right) ++ (flags ++ scratches) := by
    simp only [List.mem_append, not_or]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact sortHistoryWire_not_mem_candidate p instruction.history instruction.left
    · exact sortHistoryWire_not_mem_candidate p instruction.history instruction.right
    · exact sortHistoryWire_not_mem_compare p instruction.history
    · exact sortHistoryWire_not_mem_scratch p instruction.history
  have complete : (((left ++ right) ++ (flags ++ scratches)) ++
      [historyWire]).Nodup :=
    List.nodup_append.mpr ⟨prefixNodup, by simp, by
      intro wire wireMember target targetMember equal
      simp only [List.mem_singleton] at targetMember
      subst target
      subst wire
      exact historyAbsent wireMember⟩
  simpa [left, right, flags, scratches, historyWire, List.append_assoc] using complete

/--
clean history上でunsigned比較とcontrolled swapを連結すると、`compareRight < compareLeft`
のときだけswap word対を交換し、historyへ比較結果を保持する。
-/
theorem runBasis_compareThenControlledSwap
    {ancillaQubits systemQubits : Nat}
    (compareLeft compareRight swapLeft swapRight equalFlags scratches :
      List (Wire ancillaQubits systemQubits))
    (history : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : compareLeft.length = equalFlags.length)
    (rightLength : compareRight.length = equalFlags.length)
    (leftDisjointFlags : compareLeft.Disjoint equalFlags)
    (rightDisjointFlags : compareRight.Disjoint equalFlags)
    (flagsDisjointScratch : equalFlags.Disjoint scratches)
    (flagsNodup : equalFlags.Nodup)
    (historyAbsentLeft : history ∉ compareLeft)
    (historyAbsentRight : history ∉ compareRight)
    (historyAbsentFlags : history ∉ equalFlags)
    (flagsZero : readWires equalFlags input =
      List.replicate equalFlags.length false)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (historyZero : input history = false)
    (programEnough : ∀ controls ∈
        lessThanControlProgram compareLeft compareRight equalFlags,
      controls.length ≤ scratches.length + 1)
    (programLayout : ∀ controls ∈
        lessThanControlProgram compareLeft compareRight equalFlags,
      (controls.map Prod.fst ++ scratches ++ [history]).Nodup)
    (pairLayout : ∀ pair ∈ swapLeft.zip swapRight,
      history ≠ pair.1 ∧ history ≠ pair.2 ∧ pair.1 ≠ pair.2) :
    (.seq (xorLessThanIntoTargetCircuit compareLeft compareRight equalFlags scratches history)
        (controlledSwapWord history swapLeft swapRight) :
      Circuit (ReversibleGate ancillaQubits systemQubits)).runBasis
        reversibleGatePermutation input =
      if decide (littleEndianNat (readWires compareLeft input) <
          littleEndianNat (readWires compareRight input)) then
        swapPairsAction (swapLeft.zip swapRight)
          (xBasisAction history input)
      else input := by
  rw [runBasis_core_seq]
  simp only [runBasis_core_eq_local]
  rw [runBasis_xorLessThanIntoTargetCircuit_nat compareLeft compareRight equalFlags scratches history input
    leftLength rightLength leftDisjointFlags rightDisjointFlags flagsDisjointScratch
    flagsNodup historyAbsentLeft historyAbsentRight historyAbsentFlags flagsZero
    scratchZero programEnough programLayout]
  by_cases shouldSwap : littleEndianNat (readWires compareLeft input) <
      littleEndianNat (readWires compareRight input)
  · simp only [decide_eq_true_eq, shouldSwap, if_true]
    rw [runBasis_controlledSwapWord history swapLeft swapRight
      (xBasisAction history input) pairLayout]
    simp [historyZero]
  · have comparisonFalse : decide
        (littleEndianNat (readWires compareLeft input) <
          littleEndianNat (readWires compareRight input)) = false := by
      exact decide_eq_false shouldSwap
    simp only [comparisonFalse, Bool.false_eq_true, if_false]
    rw [runBasis_controlledSwapWord history swapLeft swapRight input pairLayout]
    simp [historyZero]

/-- zipに含まれるpairの左成分は元の左リストに属する。 -/
theorem fst_mem_of_mem_zip {α β : Type} :
    ∀ (left : List α) (right : List β) (pair : α × β),
      pair ∈ left.zip right → pair.1 ∈ left
  | [], _, _, member => by simp at member
  | _ :: _, [], _, member => by simp at member
  | leftHead :: left, rightHead :: right, pair, member => by
      simp only [List.zip_cons_cons, List.mem_cons] at member ⊢
      rcases member with rfl | tailMember
      · exact Or.inl rfl
      · exact Or.inr (fst_mem_of_mem_zip left right pair tailMember)

/-- zipに含まれるpairの右成分は元の右リストに属する。 -/
theorem snd_mem_of_mem_zip {α β : Type} :
    ∀ (left : List α) (right : List β) (pair : α × β),
      pair ∈ left.zip right → pair.2 ∈ right
  | [], _, _, member => by simp at member
  | _ :: _, [], _, member => by simp at member
  | leftHead :: left, rightHead :: right, pair, member => by
      simp only [List.zip_cons_cons, List.mem_cons] at member ⊢
      rcases member with rfl | tailMember
      · exact Or.inl rfl
      · exact Or.inr (snd_mem_of_mem_zip left right pair tailMember)

/--
二word・中間work・historyをまとめた`Nodup`から、controlled word swapが要求する
各bit pairの型安全性を取り出す。
-/
theorem swapPairLayout_of_fullLayout
    {ancillaQubits systemQubits : Nat}
    (left right middle : List (Wire ancillaQubits systemQubits))
    (history : Wire ancillaQubits systemQubits)
    (fullLayout : (left ++ right ++ middle ++ [history]).Nodup) :
    ∀ pair ∈ left.zip right,
      history ≠ pair.1 ∧ history ≠ pair.2 ∧ pair.1 ≠ pair.2 := by
  have normalized :
      (left ++ (right ++ (middle ++ [history]))).Nodup := by
    simpa [List.append_assoc] using fullLayout
  have leftSplit := List.nodup_append.mp normalized
  have rightSplit := List.nodup_append.mp leftSplit.2.1
  intro pair member
  have leftMember := fst_mem_of_mem_zip left right pair member
  have rightMember := snd_mem_of_mem_zip left right pair member
  have historyRest : history ∈ right ++ (middle ++ [history]) := by simp
  have historyAfterRight : history ∈ middle ++ [history] := by simp
  exact ⟨
    (leftSplit.2.2 pair.1 leftMember history historyRest).symm,
    (rightSplit.2.2 pair.2 rightMember history historyAfterRight).symm,
    leftSplit.2.2 pair.1 leftMember pair.2 (by simp [rightMember])⟩

/--
比較wordとswap wordの左右順が異なっても、一括比較layoutとswap pairの型安全性から
比較結果をhistoryへ保存するcompare--exchangeの基底作用を得る。
-/
theorem runBasis_compareThenControlledSwap_of_separate_layout
    {ancillaQubits systemQubits : Nat}
    (compareLeft compareRight swapLeft swapRight equalFlags scratches :
      List (Wire ancillaQubits systemQubits))
    (history : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : compareLeft.length = equalFlags.length)
    (rightLength : compareRight.length = equalFlags.length)
    (compareLayout :
      (compareLeft ++ compareRight ++ equalFlags ++ scratches ++ [history]).Nodup)
    (flagsZero : readWires equalFlags input =
      List.replicate equalFlags.length false)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (historyZero : input history = false)
    (scratchEnough : equalFlags.length ≤ scratches.length)
    (pairLayout : ∀ pair ∈ swapLeft.zip swapRight,
      history ≠ pair.1 ∧ history ≠ pair.2 ∧ pair.1 ≠ pair.2) :
    (.seq (xorLessThanIntoTargetCircuit compareLeft compareRight equalFlags scratches history)
        (controlledSwapWord history swapLeft swapRight) :
      Circuit (ReversibleGate ancillaQubits systemQubits)).runBasis
        reversibleGatePermutation input =
      if decide (littleEndianNat (readWires compareLeft input) <
          littleEndianNat (readWires compareRight input)) then
        swapPairsAction (swapLeft.zip swapRight)
          (xBasisAction history input)
      else input := by
  rw [runBasis_core_seq]
  simp only [runBasis_core_eq_local]
  rw [runBasis_xorLessThanIntoTargetCircuit_nat_of_layout compareLeft compareRight equalFlags
    scratches history input leftLength rightLength compareLayout flagsZero
    scratchZero scratchEnough]
  by_cases shouldSwap : littleEndianNat (readWires compareLeft input) <
      littleEndianNat (readWires compareRight input)
  · simp only [decide_eq_true_eq, shouldSwap, if_true]
    rw [runBasis_controlledSwapWord history swapLeft swapRight
      (xBasisAction history input) pairLayout]
    simp [historyZero]
  · have comparisonFalse : decide
        (littleEndianNat (readWires compareLeft input) <
          littleEndianNat (readWires compareRight input)) = false :=
      decide_eq_false shouldSwap
    simp only [comparisonFalse, Bool.false_eq_true, if_false]
    rw [runBasis_controlledSwapWord history swapLeft swapRight input pairLayout]
    simp [historyZero]

/-- 一括Nodup配置から、一個の比較・交換回路の自然数比較仕様を得る。 -/
theorem runBasis_compareThenControlledSwap_of_layout
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratches :
      List (Wire ancillaQubits systemQubits))
    (history : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = equalFlags.length)
    (rightLength : right.length = equalFlags.length)
    (fullLayout :
      (left ++ right ++ equalFlags ++ scratches ++ [history]).Nodup)
    (flagsZero : readWires equalFlags input =
      List.replicate equalFlags.length false)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (historyZero : input history = false)
    (scratchEnough : equalFlags.length ≤ scratches.length) :
    (.seq (xorLessThanIntoTargetCircuit left right equalFlags scratches history)
        (controlledSwapWord history left right) :
      Circuit (ReversibleGate ancillaQubits systemQubits)).runBasis
        reversibleGatePermutation input =
      if decide (littleEndianNat (readWires left input) <
          littleEndianNat (readWires right input)) then
        swapPairsAction (left.zip right) (xBasisAction history input)
      else input := by
  have normalized :
      (left ++ (right ++ (equalFlags ++ (scratches ++ [history])))).Nodup := by
    simpa [List.append_assoc] using fullLayout
  have leftSplit := List.nodup_append.mp normalized
  have rightSplit := List.nodup_append.mp leftSplit.2.1
  have pairLayout : ∀ pair ∈ left.zip right,
      history ≠ pair.1 ∧ history ≠ pair.2 ∧ pair.1 ≠ pair.2 := by
    intro pair member
    have leftMember := fst_mem_of_mem_zip left right pair member
    have rightMember := snd_mem_of_mem_zip left right pair member
    have historyRest :
        history ∈ right ++ (equalFlags ++ (scratches ++ [history])) := by
      simp
    have historyAfterRight : history ∈ equalFlags ++ (scratches ++ [history]) := by
      simp
    exact ⟨
      (leftSplit.2.2 pair.1 leftMember history historyRest).symm,
      (rightSplit.2.2 pair.2 rightMember history historyAfterRight).symm,
      leftSplit.2.2 pair.1 leftMember pair.2 (by simp [rightMember])⟩
  rw [runBasis_core_seq]
  simp only [runBasis_core_eq_local]
  rw [runBasis_xorLessThanIntoTargetCircuit_nat_of_layout left right equalFlags scratches history
    input leftLength rightLength fullLayout flagsZero scratchZero scratchEnough]
  by_cases shouldSwap : littleEndianNat (readWires left input) <
      littleEndianNat (readWires right input)
  · simp only [decide_eq_true_eq, shouldSwap, if_true]
    rw [runBasis_controlledSwapWord history left right
      (xBasisAction history input) pairLayout]
    simp [historyZero]
  · have comparisonFalse : decide
        (littleEndianNat (readWires left input) <
          littleEndianNat (readWires right input)) = false :=
      decide_eq_false shouldSwap
    simp only [comparisonFalse, Bool.false_eq_true, if_false]
    rw [runBasis_controlledSwapWord history left right input pairLayout]
    simp [historyZero]

/--
Q正本scheduleの一命令は、昇順なら`right < left`、降順なら`left < right`のときだけ
二candidate wordを交換し、その比較結果を固有history wireへ保存する。
-/
theorem runBasis_emitTypedBitonicCompareExchange
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (flagsZero : readWires (sortCompareWorkWires p) input =
      List.replicate (sortCompareWorkWires p).length false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p, input wire = false)
    (historyZero : input ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire
        instruction.history) = false) :
    (emitTypedBitonicCompareExchange (candidateWordAt p)
      (sortCompareWorkWires p) (sortAndScratchWires p)
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) instruction).runBasis
        reversibleGatePermutation input =
      if instruction.ascending then
        if decide (littleEndianNat
            (readWires (candidateWordAt p instruction.right) input) <
          littleEndianNat
            (readWires (candidateWordAt p instruction.left) input)) then
          swapPairsAction
            ((candidateWordAt p instruction.left).zip
              (candidateWordAt p instruction.right))
            (xBasisAction ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).sortFlags).ancillaWire
                instruction.history) input)
        else input
      else
        if decide (littleEndianNat
            (readWires (candidateWordAt p instruction.left) input) <
          littleEndianNat
            (readWires (candidateWordAt p instruction.right) input)) then
          swapPairsAction
            ((candidateWordAt p instruction.left).zip
              (candidateWordAt p instruction.right))
            (xBasisAction ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).sortFlags).ancillaWire
                instruction.history) input)
        else input := by
  let left := candidateWordAt p instruction.left
  let right := candidateWordAt p instruction.right
  let flags := sortCompareWorkWires p
  let scratches := sortAndScratchWires p
  let history : Wire p.ancillaWidth p.systemWidth :=
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history
  have originalLayout :
      (left ++ right ++ flags ++ scratches ++ [history]).Nodup := by
    simpa [left, right, flags, scratches, history] using
      qTypedBitonicInstruction_layout p instruction member
  have reversedLayout :
      (right ++ left ++ flags ++ scratches ++ [history]).Nodup := by
    let rest := flags ++ scratches ++ [history]
    have normalized : (left ++ right ++ rest).Nodup := by
      simpa [rest, List.append_assoc] using originalLayout
    have permutation : (right ++ left ++ rest).Perm (left ++ right ++ rest) :=
      List.perm_append_comm.append_right rest
    simpa [rest, List.append_assoc] using permutation.nodup_iff.mpr normalized
  have pairLayout : ∀ pair ∈ left.zip right,
      history ≠ pair.1 ∧ history ≠ pair.2 ∧ pair.1 ≠ pair.2 :=
    swapPairLayout_of_fullLayout left right (flags ++ scratches) history (by
      simpa [List.append_assoc] using originalLayout)
  have leftLength : left.length = flags.length := by
    simp [left, flags, sortCompareWorkWires]
  have rightLength : right.length = flags.length := by
    simp [right, flags, sortCompareWorkWires]
  have enough : flags.length ≤ scratches.length := by
    simpa [flags, scratches] using sortCompareWorkWires_length_le_scratch p
  cases ascendingValue : instruction.ascending with
  | false =>
      simp only [emitTypedBitonicCompareExchange, ascendingValue]
      simpa [left, right, flags, scratches, history] using
        runBasis_compareThenControlledSwap_of_separate_layout
          left right left right flags scratches history input leftLength
          rightLength originalLayout (by simpa [flags] using flagsZero)
          (by simpa [scratches] using scratchZero)
          (by simpa [history] using historyZero) enough pairLayout
  | true =>
      simp only [emitTypedBitonicCompareExchange, ascendingValue, if_true]
      simpa [left, right, flags, scratches, history] using
        runBasis_compareThenControlledSwap_of_separate_layout
          right left left right flags scratches history input rightLength
          leftLength reversedLayout (by simpa [flags] using flagsZero)
          (by simpa [scratches] using scratchZero)
          (by simpa [history] using historyZero) enough pairLayout

/-- Q用compare--exchange一命令の純粋な基底作用。 -/
def qBitonicStepReference (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let left := candidateWordAt p instruction.left
  let right := candidateWordAt p instruction.right
  let history := (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history
  let shouldSwap := if instruction.ascending then
    littleEndianNat (readWires right input) < littleEndianNat (readWires left input)
  else
    littleEndianNat (readWires left input) < littleEndianNat (readWires right input)
  if decide shouldSwap then
    swapPairsAction (left.zip right) (xBasisAction history input)
  else input

/-- 正本の一命令は、clean work上で純粋なcompare--exchange作用に一致する。 -/
theorem runBasis_emitTypedBitonicCompareExchange_eq_reference
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (flagsZero : readWires (sortCompareWorkWires p) input =
      List.replicate (sortCompareWorkWires p).length false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p, input wire = false)
    (historyZero : input ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire
        instruction.history) = false) :
    (emitTypedBitonicCompareExchange (candidateWordAt p)
      (sortCompareWorkWires p) (sortAndScratchWires p)
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) instruction).runBasis
        reversibleGatePermutation input =
      qBitonicStepReference p instruction input := by
  rw [runBasis_emitTypedBitonicCompareExchange p instruction member input
    flagsZero scratchZero historyZero]
  simp only [qBitonicStepReference]
  cases instruction.ascending <;> rfl

/--
互いに素な同長word列をpairwise swapすると、左wordの読出しは交換前の右wordになる。
-/
theorem readWires_swapPairsAction_zip_left
    {ancillaQubits systemQubits : Nat} :
    ∀ (left right : List (Wire ancillaQubits systemQubits))
      (input : JointBasis ancillaQubits systemQubits),
      left.length = right.length → (left ++ right).Nodup →
      readWires left (swapPairsAction (left.zip right) input) =
        readWires right input
  | [], right, input, lengthEqual, _ => by
      cases right with
      | nil => rfl
      | cons head tail => simp at lengthEqual
  | leftHead :: left, [], input, lengthEqual, _ => by
      simp at lengthEqual
  | leftHead :: left, rightHead :: right, input, lengthEqual, layout => by
      have tailLength : left.length = right.length := by simpa using lengthEqual
      have split := List.nodup_append.mp layout
      have leftSplit := List.nodup_cons.mp split.1
      have rightSplit := List.nodup_cons.mp split.2.1
      have tailLayout : (left ++ right).Nodup :=
        List.nodup_append.mpr ⟨leftSplit.2, rightSplit.2, by
          intro leftWire leftMember rightWire rightMember
          exact split.2.2 leftWire (by simp [leftMember]) rightWire
            (by simp [rightMember])⟩
      have headOutside : ∀ pair ∈ left.zip right,
          leftHead ≠ pair.1 ∧ leftHead ≠ pair.2 := by
        intro pair member
        have pairLeft := fst_mem_of_mem_zip left right pair member
        have pairRight := snd_mem_of_mem_zip left right pair member
        exact ⟨fun equal => leftSplit.1 (by simpa [equal] using pairLeft),
          fun equal => split.2.2 leftHead (by simp) pair.2
            (by simp [pairRight]) equal⟩
      have headValue :
          swapPairsAction (left.zip right)
              (swapBasisAction leftHead rightHead input) leftHead =
            input rightHead := by
        rw [swapPairsAction_other _ leftHead _ headOutside]
        simp [swapBasisAction]
      have tailRead := readWires_swapPairsAction_zip_left left right
        (swapBasisAction leftHead rightHead input) tailLength tailLayout
      have rightUnaffected :
          readWires right (swapBasisAction leftHead rightHead input) =
            readWires right input := by
        apply List.map_congr_left
        intro wire member
        apply swapBasisAction_other
        · intro equal
          subst wire
          exact (split.2.2 leftHead (by simp) leftHead
            (by simp [member])) rfl
        · intro equal
          subst wire
          exact rightSplit.1 member
      simp only [readWires, List.map_cons, List.zip_cons_cons,
        swapPairsAction]
      rw [headValue]
      rw [rightUnaffected] at tailRead
      exact congrArg (List.cons (input rightHead)) tailRead

/--
互いに素な同長word列をpairwise swapすると、右wordの読出しは交換前の左wordになる。
-/
theorem readWires_swapPairsAction_zip_right
    {ancillaQubits systemQubits : Nat} :
    ∀ (left right : List (Wire ancillaQubits systemQubits))
      (input : JointBasis ancillaQubits systemQubits),
      left.length = right.length → (left ++ right).Nodup →
      readWires right (swapPairsAction (left.zip right) input) =
        readWires left input
  | [], right, input, lengthEqual, _ => by
      cases right with
      | nil => rfl
      | cons head tail => simp at lengthEqual
  | leftHead :: left, [], input, lengthEqual, _ => by
      simp at lengthEqual
  | leftHead :: left, rightHead :: right, input, lengthEqual, layout => by
      have tailLength : left.length = right.length := by simpa using lengthEqual
      have split := List.nodup_append.mp layout
      have leftSplit := List.nodup_cons.mp split.1
      have rightSplit := List.nodup_cons.mp split.2.1
      have headDifferent : leftHead ≠ rightHead :=
        split.2.2 leftHead (by simp) rightHead (by simp)
      have tailLayout : (left ++ right).Nodup :=
        List.nodup_append.mpr ⟨leftSplit.2, rightSplit.2, by
          intro leftWire leftMember rightWire rightMember
          exact split.2.2 leftWire (by simp [leftMember]) rightWire
            (by simp [rightMember])⟩
      have headOutside : ∀ pair ∈ left.zip right,
          rightHead ≠ pair.1 ∧ rightHead ≠ pair.2 := by
        intro pair member
        have pairLeft := fst_mem_of_mem_zip left right pair member
        have pairRight := snd_mem_of_mem_zip left right pair member
        exact ⟨fun equal => split.2.2 pair.1 (by simp [pairLeft]) rightHead
            (by simp) equal.symm,
          fun equal => rightSplit.1 (by simpa [equal] using pairRight)⟩
      have headValue :
          swapPairsAction (left.zip right)
              (swapBasisAction leftHead rightHead input) rightHead =
            input leftHead := by
        rw [swapPairsAction_other _ rightHead _ headOutside]
        simp [swapBasisAction, headDifferent.symm]
      have tailRead := readWires_swapPairsAction_zip_right left right
        (swapBasisAction leftHead rightHead input) tailLength tailLayout
      have leftUnaffected :
          readWires left (swapBasisAction leftHead rightHead input) =
            readWires left input := by
        apply List.map_congr_left
        intro wire member
        apply swapBasisAction_other
        · exact fun equal => leftSplit.1 (by simpa [equal] using member)
        · intro equal
          subst wire
          exact (split.2.2 rightHead (by simp [member]) rightHead
            (by simp)) rfl
      simp only [readWires, List.map_cons, List.zip_cons_cons,
        swapPairsAction]
      rw [headValue]
      rw [leftUnaffected] at tailRead
      exact congrArg (List.cons (input leftHead)) tailRead

/-- 全swap pair外のwire列はpairwise swapで変化しない。 -/
theorem readWires_swapPairsAction_other
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (pairs : List
      (Wire ancillaQubits systemQubits × Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (outside : ∀ wire ∈ wires, ∀ pair ∈ pairs,
      wire ≠ pair.1 ∧ wire ≠ pair.2) :
    readWires wires (swapPairsAction pairs input) = readWires wires input := by
  apply List.map_congr_left
  intro wire member
  exact swapPairsAction_other pairs wire input (outside wire member)

/-- 一個のcandidate wordをmarker込みlittle-endian自然数として読む。 -/
def qCandidateValue (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (word : Fin p.sortWordCount) : Nat :=
  littleEndianNat (readWires (candidateWordAt p word) input)

/-- 純粋な自然数word状態上の一個のbitonic compare--exchange。 -/
def qBitonicValueStep (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (values : Fin p.sortWordCount → Nat) : Fin p.sortWordCount → Nat :=
  let shouldSwap := if instruction.ascending then
    values instruction.right < values instruction.left
  else values instruction.left < values instruction.right
  if decide shouldSwap then
    Function.update
      (Function.update values instruction.left (values instruction.right))
      instruction.right (values instruction.left)
  else values

/-- history Xは任意candidate wordの読出しを変化させない。 -/
theorem readWires_candidateWordAt_xHistory
    (p : QParameters) (history : Fin p.sortFlagWidth)
    (word : Fin p.sortWordCount)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (candidateWordAt p word)
        (xBasisAction ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire history) input) =
      readWires (candidateWordAt p word) input := by
  exact readWires_xBasisAction_of_not_mem _ _ input
    (sortHistoryWire_not_mem_candidate p history word)

/--
Q正本の一命令をcandidate自然数状態へ射影すると、純粋なcompare--exchangeに一致する。
-/
theorem qCandidateValue_qBitonicStepReference
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qTypedBitonicSchedule p)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    qCandidateValue p (qBitonicStepReference p instruction input) =
      qBitonicValueStep p instruction (qCandidateValue p input) := by
  funext word
  let left := candidateWordAt p instruction.left
  let right := candidateWordAt p instruction.right
  let flags := sortCompareWorkWires p
  let scratches := sortAndScratchWires p
  let history : Wire p.ancillaWidth p.systemWidth :=
    (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history
  have fullLayout :
      (left ++ right ++ flags ++ scratches ++ [history]).Nodup := by
    simpa [left, right, flags, scratches, history] using
      qTypedBitonicInstruction_layout p instruction member
  have pairLayout : (left ++ right).Nodup := by
    have normalized :
        ((left ++ right) ++ (flags ++ scratches ++ [history])).Nodup := by
      simpa [List.append_assoc] using fullLayout
    exact (List.nodup_append.mp normalized).1
  have lengthEqual : left.length = right.length := by
    simp [left, right]
  have instructionDifferent : instruction.left ≠ instruction.right :=
    qTypedBitonicSchedule_left_ne_right p instruction member
  have leftAfterSwap :
      readWires left
          (swapPairsAction (left.zip right) (xBasisAction history input)) =
        readWires right input := by
    rw [readWires_swapPairsAction_zip_left left right
      (xBasisAction history input) lengthEqual pairLayout]
    simpa [right, history] using
      readWires_candidateWordAt_xHistory p instruction.history
        instruction.right input
  have rightAfterSwap :
      readWires right
          (swapPairsAction (left.zip right) (xBasisAction history input)) =
        readWires left input := by
    rw [readWires_swapPairsAction_zip_right left right
      (xBasisAction history input) lengthEqual pairLayout]
    simpa [left, history] using
      readWires_candidateWordAt_xHistory p instruction.history
        instruction.left input
  have otherAfterSwap : ∀ other : Fin p.sortWordCount,
      other ≠ instruction.left → other ≠ instruction.right →
      readWires (candidateWordAt p other)
          (swapPairsAction (left.zip right) (xBasisAction history input)) =
        readWires (candidateWordAt p other) input := by
    intro other differentLeft differentRight
    rw [readWires_swapPairsAction_other]
    · simpa [history] using
        readWires_candidateWordAt_xHistory p instruction.history other input
    · intro wire wireMember pair pairMember
      have pairLeft := fst_mem_of_mem_zip left right pair pairMember
      have pairRight := snd_mem_of_mem_zip left right pair pairMember
      constructor
      · intro equal
        subst wire
        exact (List.disjoint_left.mp
          (sortCandidateWordAt_disjoint_of_ne p other instruction.left
            differentLeft) wireMember) (by simpa [left] using pairLeft)
      · intro equal
        subst wire
        exact (List.disjoint_left.mp
          (sortCandidateWordAt_disjoint_of_ne p other instruction.right
            differentRight) wireMember) (by simpa [right] using pairRight)
  unfold qBitonicStepReference qBitonicValueStep qCandidateValue
  dsimp only
  cases ascendingValue : instruction.ascending <;>
    simp only [Bool.false_eq_true, if_false, if_true]
  all_goals
    split
    · by_cases isLeft : word = instruction.left
      · subst word
        simp [Function.update, instructionDifferent, left, right, history,
          leftAfterSwap]
      · by_cases isRight : word = instruction.right
        · subst word
          simp [Function.update, left, right, history, rightAfterSwap]
        · simp [Function.update, isLeft, isRight,
            left, right, history, otherAfterSwap word isLeft isRight]
    · rfl

/-- 純粋な自然数word状態上でQ bitonic命令列を実行する。 -/
def qBitonicValuesReference (p : QParameters) :
    List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) →
      (Fin p.sortWordCount → Nat) → Fin p.sortWordCount → Nat
  | [], values => values
  | instruction :: schedule, values =>
      qBitonicValuesReference p schedule
        (qBitonicValueStep p instruction values)

/-- Q用一命令の純粋意味論は、一般の型付き比較交換意味論の自然数特殊化である。 -/
theorem qBitonicValueStep_eq_typed
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (values : Fin p.sortWordCount → Nat) :
    qBitonicValueStep p instruction values =
      typedBitonicValueStep instruction values := by
  rfl

/-- Q用命令列の純粋意味論は、一般の型付き比較ネットワーク意味論に一致する。 -/
theorem qBitonicValuesReference_eq_typed
    (p : QParameters)
    (schedule :
      List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
    (values : Fin p.sortWordCount → Nat) :
    qBitonicValuesReference p schedule values =
      runTypedBitonicValues schedule values := by
  induction schedule generalizing values with
  | nil => rfl
  | cons instruction schedule inductionHypothesis =>
      simp only [qBitonicValuesReference, runTypedBitonicValues]
      rw [qBitonicValueStep_eq_typed]
      exact inductionHypothesis _

/-- history添字から物理history wireへの写像は単射である。 -/
theorem sortHistoryWire_injective (p : QParameters) :
    Function.Injective (fun history : Fin p.sortFlagWidth =>
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire history :
          Wire p.ancillaWidth p.systemWidth)) := by
  exact (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).sortFlags).ancillaWire_injective

/--
swap pair外かつ固有history以外のwireは、一命令の純粋作用で変化しない。
-/
theorem qBitonicStepReference_other
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideLeft : wire ∉ candidateWordAt p instruction.left)
    (outsideRight : wire ∉ candidateWordAt p instruction.right)
    (differentHistory : wire ≠ (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire
        instruction.history) :
    qBitonicStepReference p instruction input wire = input wire := by
  unfold qBitonicStepReference
  cases ascendingValue : instruction.ascending <;>
    simp only [Bool.false_eq_true, if_false, if_true]
  all_goals
    split
    · rw [swapPairsAction_other]
      · exact xBasisAction_other _ wire differentHistory input
      · intro pair pairMember
        constructor
        · intro equal
          apply outsideLeft
          rw [equal]
          exact fst_mem_of_mem_zip _ _ pair pairMember
        · intro equal
          apply outsideRight
          rw [equal]
          exact snd_mem_of_mem_zip _ _ pair pairMember
    · rfl

/-- 一命令の純粋作用は比較flag列を変更しない。 -/
theorem qBitonicStepReference_preserves_compare
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (sortCompareWorkWires p)
        (qBitonicStepReference p instruction input) =
      readWires (sortCompareWorkWires p) input := by
  apply List.map_congr_left
  intro wire member
  apply qBitonicStepReference_other p instruction input wire
  · intro candidateMember
    exact (List.disjoint_left.mp
      (sortCandidateWordAt_disjoint_compare p instruction.left)
        candidateMember) member
  · intro candidateMember
    exact (List.disjoint_left.mp
      (sortCandidateWordAt_disjoint_compare p instruction.right)
        candidateMember) member
  · intro equal
    subst wire
    exact sortHistoryWire_not_mem_compare p instruction.history member

/-- 一命令の純粋作用はAND scratch列を変更しない。 -/
theorem qBitonicStepReference_preserves_scratch
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ sortAndScratchWires p) :
    qBitonicStepReference p instruction input wire = input wire := by
  apply qBitonicStepReference_other p instruction input wire
  · intro candidateMember
    exact (List.disjoint_left.mp
      (sortCandidateWordAt_disjoint_scratch p instruction.left)
        candidateMember) member
  · intro candidateMember
    exact (List.disjoint_left.mp
      (sortCandidateWordAt_disjoint_scratch p instruction.right)
        candidateMember) member
  · intro equal
    subst wire
    exact sortHistoryWire_not_mem_scratch p instruction.history member

/-- 現命令と異なるhistory wireは、一命令の純粋作用で変化しない。 -/
theorem qBitonicStepReference_preserves_other_history
    (p : QParameters)
    (instruction other :
      TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (different : other.history ≠ instruction.history)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    qBitonicStepReference p instruction input
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire other.history) =
      input ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire other.history) := by
  apply qBitonicStepReference_other p instruction input
  · exact sortHistoryWire_not_mem_candidate p other.history instruction.left
  · exact sortHistoryWire_not_mem_candidate p other.history instruction.right
  · intro equal
    exact different (sortHistoryWire_injective p equal)

/-- Q用compare--exchange列の純粋な実行意味論。 -/
def CanonicalCandidateSortWithHistoryRestorationSpec (p : QParameters) :
    List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) →
      JointBasis p.ancillaWidth p.systemWidth →
      JointBasis p.ancillaWidth p.systemWidth
  | [], input => input
  | instruction :: schedule, input =>
      CanonicalCandidateSortWithHistoryRestorationSpec p schedule
        (qBitonicStepReference p instruction input)

/--
任意のQ schedule部分列について、比較work・scratch・未使用historyがcleanなら、
正本回路列の基底作用は純粋schedule作用に一致する。
-/
theorem runBasis_emitTypedBitonicSort_eq_reference
    (p : QParameters) :
    ∀ (schedule :
        List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      (∀ instruction ∈ schedule, instruction ∈ qTypedBitonicSchedule p) →
      (schedule.map (fun instruction => instruction.history)).Nodup →
      readWires (sortCompareWorkWires p) input =
        List.replicate (sortCompareWorkWires p).length false →
      (∀ wire ∈ sortAndScratchWires p, input wire = false) →
      (∀ instruction ∈ schedule,
        input ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire
            instruction.history) = false) →
      (emitTypedBitonicSort (candidateWordAt p) (sortCompareWorkWires p)
        (sortAndScratchWires p)
        (QLayout.oracleSlice
          (OracleWorkLayout.canonical p).sortFlags).ancillaWire
        schedule).runBasis reversibleGatePermutation input =
          CanonicalCandidateSortWithHistoryRestorationSpec p schedule input := by
  intro schedule
  induction schedule with
  | nil =>
      intro input _ _ _ _ _
      rfl
  | cons instruction schedule inductionHypothesis =>
      intro input allMembers historyNodup flagsZero scratchZero historiesZero
      have instructionMember : instruction ∈ qTypedBitonicSchedule p :=
        allMembers instruction (by simp)
      have scheduleMembers : ∀ next ∈ schedule,
          next ∈ qTypedBitonicSchedule p := by
        intro next member
        exact allMembers next (by simp [member])
      have historySplit := List.nodup_cons.mp historyNodup
      have currentHistoryZero := historiesZero instruction (by simp)
      have stepCorrect :=
        runBasis_emitTypedBitonicCompareExchange_eq_reference p instruction
          instructionMember input flagsZero scratchZero currentHistoryZero
      change
        (emitTypedBitonicSort (candidateWordAt p) (sortCompareWorkWires p)
          (sortAndScratchWires p)
          (QLayout.oracleSlice
            (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          schedule).runBasis reversibleGatePermutation
            ((emitTypedBitonicCompareExchange (candidateWordAt p)
              (sortCompareWorkWires p) (sortAndScratchWires p)
              ((QLayout.oracleSlice
                (OracleWorkLayout.canonical p).sortFlags).ancillaWire
                  instruction.history) instruction).runBasis
                    reversibleGatePermutation input) =
          CanonicalCandidateSortWithHistoryRestorationSpec p schedule
            (qBitonicStepReference p instruction input)
      rw [stepCorrect]
      apply inductionHypothesis (qBitonicStepReference p instruction input)
        scheduleMembers historySplit.2
      · rw [qBitonicStepReference_preserves_compare]
        exact flagsZero
      · intro wire member
        rw [qBitonicStepReference_preserves_scratch p instruction input wire member]
        exact scratchZero wire member
      · intro next nextMember
        have different : next.history ≠ instruction.history := by
          intro equal
          apply historySplit.1
          exact List.mem_map.mpr ⟨next, nextMember, equal⟩
        rw [qBitonicStepReference_preserves_other_history p instruction next
          different input]
        exact historiesZero next (by simp [nextMember])

/--
全Q bitonic正本回路は、全0の比較・scratch・historyから純粋schedule作用を実行する。
-/
theorem runBasis_reversiblySortCandidateWordsAndRestoreHistoryCircuit_eq_reference
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (flagsZero : readWires (sortCompareWorkWires p) input =
      List.replicate (sortCompareWorkWires p).length false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p, input wire = false)
    (historiesZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      input ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) = false) :
    (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
        reversibleGatePermutation input =
      CanonicalCandidateSortWithHistoryRestorationSpec p (qTypedBitonicSchedule p) input := by
  apply runBasis_emitTypedBitonicSort_eq_reference p
  · intro instruction member
    exact member
  · exact qTypedBitonicSchedule_history_nodup p
  · exact flagsZero
  · exact scratchZero
  · exact historiesZero

/--
基底上の純粋schedule作用を全candidate自然数へ射影すると、純粋word scheduleに一致する。
-/
theorem qCandidateValue_canonicalCandidateSortWithHistoryRestorationSpec
    (p : QParameters) :
    ∀ (schedule :
        List (TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      (∀ instruction ∈ schedule, instruction ∈ qTypedBitonicSchedule p) →
      qCandidateValue p (CanonicalCandidateSortWithHistoryRestorationSpec p schedule input) =
        qBitonicValuesReference p schedule (qCandidateValue p input) := by
  intro schedule
  induction schedule with
  | nil =>
      intro input _
      rfl
  | cons instruction schedule inductionHypothesis =>
      intro input allMembers
      have instructionMember : instruction ∈ qTypedBitonicSchedule p :=
        allMembers instruction (by simp)
      have scheduleMembers : ∀ next ∈ schedule,
          next ∈ qTypedBitonicSchedule p := by
        intro next member
        exact allMembers next (by simp [member])
      simp only [CanonicalCandidateSortWithHistoryRestorationSpec, qBitonicValuesReference]
      rw [inductionHypothesis (qBitonicStepReference p instruction input)
        scheduleMembers]
      rw [qCandidateValue_qBitonicStepReference p instruction
        instructionMember input]

/--
Q bitonic正本回路の全candidate自然数作用は、純粋な型付きnetworkの実行と一致する。
-/
theorem qCandidateValue_runBasis_reversiblySortCandidateWordsAndRestoreHistoryCircuit
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (flagsZero : readWires (sortCompareWorkWires p) input =
      List.replicate (sortCompareWorkWires p).length false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p, input wire = false)
    (historiesZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      input ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) = false) :
    qCandidateValue p
        ((reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
          reversibleGatePermutation input) =
      qBitonicValuesReference p (qTypedBitonicSchedule p)
        (qCandidateValue p input) := by
  rw [runBasis_reversiblySortCandidateWordsAndRestoreHistoryCircuit_eq_reference p input
    flagsZero scratchZero historiesZero]
  apply qCandidateValue_canonicalCandidateSortWithHistoryRestorationSpec p
  intro instruction member
  exact member

end ReversibleCircuit

end ProbabilityGeneratorQProof
