import QLean.Generator.Implementation.QOracleMembershipCorrectness
import QLean.Generator.Implementation.ReversibleLogicSharedCoreReadoutAdapter

/-!
# candidate生成回路の一般基底作用

candidate wordの型安全な配置、marker初期化、present制御付きword copyを、
行列や全基底を列挙せずに証明する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- candidate生成へ渡すregisterの型安全な配置条件。 -/
structure CandidateInputLayout (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) : Prop where
  /-- membershipまでに必要な入力配置条件。 -/
  membership : MembershipInputLayout p register
  /-- registerとpresent flag sliceは交わらない。 -/
  disjoint_present : register.Disjoint (oraclePresentWires p)
  /-- registerとcandidate sliceは交わらない。 -/
  disjoint_candidate : register.Disjoint
    ((QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate).wireList :
      List (Wire p.ancillaWidth p.systemWidth))

/-- 物理system registerはcandidate生成の正しい入力配置である。 -/
theorem systemWires_candidateInputLayout (p : QParameters) :
    CandidateInputLayout p (systemWires p) where
  membership := systemWires_membershipInputLayout p
  disjoint_present := by
    let presentSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).present
    simpa [systemWires, QLayout.systemWire, oraclePresentWires,
      RegisterSlice.wireList, presentSlice] using
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) presentSlice)
  disjoint_candidate := by
    let candidateSlice := QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate
    simpa [systemWires, QLayout.systemWire, candidateSlice] using
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) candidateSlice)

/-- column-key registerはcandidate生成の正しい入力配置である。 -/
theorem columnKeyWires_candidateInputLayout (p : QParameters) :
    CandidateInputLayout p (columnKeyWires p) where
  membership := columnKeyWires_membershipInputLayout p
  disjoint_present := by
    simpa [oraclePresentWires, RegisterSlice.wireList] using
      columnKeyWires_disjoint_oracleSlice p
        (OracleWorkLayout.canonical p).present
  disjoint_candidate := by
    simpa using columnKeyWires_disjoint_oracleSlice p
      (OracleWorkLayout.canonical p).candidate

/-- 1 candidate wordはmarkerを含めて常に`wordWidth+1` bitである。 -/
@[simp] theorem candidateWordAt_length (p : QParameters)
    (word : Fin p.sortWordCount) :
    (candidateWordAt p word).length = p.wordWidth + 1 := by
  simp [candidateWordAt]

/-- 1 candidate wordのdata部分は常に`wordWidth` bitである。 -/
@[simp] theorem candidateWordAt_data_length (p : QParameters)
    (word : Fin p.sortWordCount) :
    ((candidateWordAt p word).take p.wordWidth).length = p.wordWidth := by
  simp [candidateWordAt]

/-- 同じcandidate word内ではbit添字から物理wireへの写像が単射である。 -/
theorem candidateWordWire_bit_injective (p : QParameters)
    (word : Fin p.sortWordCount) :
    Function.Injective (candidateWordWire p word) := by
  intro left right equal
  let slice := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  have indices :
      (⟨word.val * (p.wordWidth + 1) + left.val, by
          simp only [QParameters.candidateWidth]
          nlinarith [word.isLt, left.isLt]⟩ : Fin p.candidateWidth) =
        ⟨word.val * (p.wordWidth + 1) + right.val, by
          simp only [QParameters.candidateWidth]
          nlinarith [word.isLt, right.isLt]⟩ := by
    apply slice.ancillaWire_injective
    simpa [candidateWordWire, slice] using equal
  apply Fin.ext
  have values := congrArg Fin.val indices
  change word.val * (p.wordWidth + 1) + left.val =
    word.val * (p.wordWidth + 1) + right.val at values
  exact Nat.add_left_cancel values

/-- candidateの`(word, bit)`から物理wireへの二重添字写像は大域的に単射である。 -/
theorem candidateWordWire_pair_injective (p : QParameters) :
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

/-- 異なるcandidate wordのwire列は互いに素である。 -/
theorem candidateWordAt_disjoint_of_ne (p : QParameters)
    (left right : Fin p.sortWordCount) (different : left ≠ right) :
    (candidateWordAt p left).Disjoint (candidateWordAt p right) := by
  rw [List.disjoint_left]
  intro wire leftMember rightMember
  rcases List.mem_map.mp leftMember with ⟨leftBit, _, leftWire⟩
  rcases List.mem_map.mp rightMember with ⟨rightBit, _, rightWire⟩
  have pairEqual : (left, leftBit) = (right, rightBit) :=
    candidateWordWire_pair_injective p (leftWire.trans rightWire.symm)
  exact different (congrArg Prod.fst pairEqual)

/-- candidate marker wireはword添字について単射である。 -/
theorem candidateMarkerWire_injective (p : QParameters) :
    Function.Injective (candidateMarkerWire p) := by
  intro left right equal
  have pairWireEqual :
      candidateWordWire p left ⟨p.wordWidth, by omega⟩ =
        candidateWordWire p right ⟨p.wordWidth, by omega⟩ := by
    simpa [candidateMarkerWire] using equal
  have pairEqual :
      ((left, ⟨p.wordWidth, by omega⟩) :
        Fin p.sortWordCount × Fin (p.wordWidth + 1)) =
        ((right, ⟨p.wordWidth, by omega⟩) :
          Fin p.sortWordCount × Fin (p.wordWidth + 1)) :=
    candidateWordWire_pair_injective p pairWireEqual
  exact congrArg Prod.fst pairEqual

/-- 1 candidate wordのwire列には重複がない。 -/
theorem candidateWordAt_nodup (p : QParameters)
    (word : Fin p.sortWordCount) : (candidateWordAt p word).Nodup := by
  exact List.Nodup.map (candidateWordWire_bit_injective p word)
    (List.nodup_finRange (p.wordWidth + 1))

/-- candidate wordの任意のwireはcandidate全体sliceに属する。 -/
theorem candidateWordAt_mem_candidateSlice
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
  refine ⟨localIndex, List.mem_finRange _, ?_⟩
  rfl

/-- candidateのdata部分と末尾marker wireは異なる。 -/
theorem candidateMarkerWire_not_mem_data (p : QParameters)
    (word : Fin p.sortWordCount) :
    candidateMarkerWire p word ∉ (candidateWordAt p word).take p.wordWidth := by
  intro member
  rcases List.mem_take_iff_getElem.mp member with ⟨index, indexLt, equal⟩
  have indexWordLt : index < p.wordWidth := by
    exact lt_of_lt_of_le indexLt (Nat.min_le_left _ _)
  have wireEqual :
      candidateWordWire p word ⟨index, by omega⟩ =
        candidateWordWire p word ⟨p.wordWidth, by omega⟩ := by
    simpa [candidateWordAt, candidateMarkerWire] using equal
  have bitEqual := candidateWordWire_bit_injective p word wireEqual
  have values := congrArg Fin.val bitEqual
  change index = p.wordWidth at values
  omega

/-- 任意wordのmarkerは、同じwordか別wordかを問わず全data領域の外側にある。 -/
theorem candidateMarkerWire_not_mem_data_any (p : QParameters)
    (markerWord dataWord : Fin p.sortWordCount) :
    candidateMarkerWire p markerWord ∉
      (candidateWordAt p dataWord).take p.wordWidth := by
  intro member
  have fullMember := List.mem_of_mem_take member
  rcases List.mem_map.mp fullMember with ⟨dataBit, _, wireEqual⟩
  have dataBitLt : dataBit.val < p.wordWidth := by
    rcases List.mem_take_iff_getElem.mp member with ⟨index, indexLt, getEqual⟩
    have indexWordLt : index < p.wordWidth :=
      lt_of_lt_of_le indexLt (Nat.min_le_left _ _)
    have dataIndex : dataBit.val = index := by
      have mapped := congrArg wireNumber (wireEqual.trans getEqual.symm)
      simp [candidateWordAt, candidateWordWire, QLayout.oracleSlice,
        RegisterSlice.compose, OracleWorkLayout.canonical] at mapped
      omega
    omega
  have markerEqual :
      candidateWordWire p markerWord ⟨p.wordWidth, by omega⟩ =
        candidateWordWire p dataWord dataBit := by
    simpa [candidateMarkerWire] using wireEqual.symm
  have pairEqual :
      ((markerWord, ⟨p.wordWidth, by omega⟩) :
        Fin p.sortWordCount × Fin (p.wordWidth + 1)) =
        (dataWord, dataBit) :=
    candidateWordWire_pair_injective p markerEqual
  have bitEqual := congrArg (fun pair => pair.2.val) pairEqual
  change p.wordWidth = dataBit.val at bitEqual
  omega

/-- active slotからpadding込みsort wordへの埋込みは単射である。 -/
theorem slotToSortWord_injective (p : QParameters) :
    Function.Injective (slotToSortWord p) := by
  intro left right equal
  apply Fin.ext
  simpa [slotToSortWord] using congrArg Fin.val equal

/-- candidate sliceとpresent sliceは互いに素である。 -/
theorem oraclePresentWires_disjoint_candidateSlice (p : QParameters) :
    (oraclePresentWires p).Disjoint
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  let presentSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).present
  let candidateSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).candidate
  have separated : presentSlice.start + p.presentWidth ≤ candidateSlice.start := by
    simp [presentSlice, candidateSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  simpa [oraclePresentWires, RegisterSlice.wireList, presentSlice,
    candidateSlice] using
      (presentSlice.wireList_disjoint_of_end_le_start candidateSlice separated :
        (presentSlice.wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (candidateSlice.wireList :
            List (Wire p.ancillaWidth p.systemWidth)))

/-- 1 slotのcandidate copyが要求する全配置条件を正本layoutから導く。 -/
theorem prepareCandidateSlot_layout
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) (slot : Fin p.K) :
    let source := registerWordAt p register slot
    let target := (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
    let control := oraclePresentWireAt p slot
    source.length = target.length ∧ source.Disjoint target ∧
      control ∉ source ∧ control ∉ target ∧ target.Nodup ∧
      control ≠ candidateMarkerWire p (slotToSortWord p slot) := by
  dsimp only
  let word := slotToSortWord p slot
  let candidateSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).candidate
  constructor
  · rw [registerWordAt_length p register layout.membership.decoder.length_eq]
    exact (candidateWordAt_data_length p word).symm
  constructor
  · rw [List.disjoint_left]
    intro wire sourceMember targetMember
    exact (List.disjoint_left.mp layout.disjoint_candidate
      (mem_register_of_mem_registerWordAt p register slot sourceMember))
      (candidateWordAt_mem_candidateSlice p word
        (List.mem_of_mem_take targetMember))
  constructor
  · intro member
    have registerMember := mem_register_of_mem_registerWordAt p register slot member
    have presentMember : oraclePresentWireAt p slot ∈ oraclePresentWires p := by
      simp [oraclePresentWireAt, oraclePresentWires, QParameters.presentWidth]
    exact (List.disjoint_left.mp layout.disjoint_present registerMember) presentMember
  constructor
  · intro member
    have presentMember : oraclePresentWireAt p slot ∈ oraclePresentWires p := by
      simp [oraclePresentWireAt, oraclePresentWires, QParameters.presentWidth]
    exact (List.disjoint_left.mp
      (oraclePresentWires_disjoint_candidateSlice p) presentMember)
      (candidateWordAt_mem_candidateSlice p word
        (List.mem_of_mem_take member))
  constructor
  · exact (candidateWordAt_nodup p word).take
  · intro equal
    have presentMember : oraclePresentWireAt p slot ∈ oraclePresentWires p := by
      simp [oraclePresentWireAt, oraclePresentWires, QParameters.presentWidth]
    have markerMember : candidateMarkerWire p word ∈
        (candidateWordAt p word) := by
      simp [candidateMarkerWire, candidateWordAt]
    rw [equal] at presentMember
    exact (List.disjoint_left.mp
      (oraclePresentWires_disjoint_candidateSlice p) presentMember)
      (candidateWordAt_mem_candidateSlice p word markerMember)

/-- 1 slot candidate回路の、行列を展開しない基底作用参照関数。 -/
def prepareCandidateSlotReference
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let source := registerWordAt p register slot
  let target := (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let control := oraclePresentWireAt p slot
  let afterData := if input control then
    (TotalReversibleStage.xorCopy source target).reference input
  else input
  cnotBasisAction control (candidateMarkerWire p (slotToSortWord p slot))
    afterData

/-- 1 slotのcandidate生成後、markerはpresent flagをXORした値になる。 -/
theorem prepareCandidateSlotReference_marker
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    prepareCandidateSlotReference p register slot input
        (candidateMarkerWire p (slotToSortWord p slot)) =
      if input (oraclePresentWireAt p slot) then
        !(input (candidateMarkerWire p (slotToSortWord p slot)))
      else input (candidateMarkerWire p (slotToSortWord p slot)) := by
  let source := registerWordAt p register slot
  let target := (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let control := oraclePresentWireAt p slot
  let marker := candidateMarkerWire p (slotToSortWord p slot)
  have slotLayout := prepareCandidateSlot_layout p register layout slot
  rcases slotLayout with
    ⟨_, _, _, controlTarget, _, _⟩
  have markerTarget : marker ∉ target := by
    exact candidateMarkerWire_not_mem_data p (slotToSortWord p slot)
  by_cases enabled : input (oraclePresentWireAt p slot) = true
  · have controlAfter :
        (TotalReversibleStage.xorCopy source target).reference input control =
          input control :=
      TotalReversibleStage.xorCopy_reference_apply_outside_target
        source target input control controlTarget
    have markerAfter :
        (TotalReversibleStage.xorCopy source target).reference input marker =
          input marker :=
      TotalReversibleStage.xorCopy_reference_apply_outside_target
        source target input marker markerTarget
    rw [prepareCandidateSlotReference, if_pos enabled, cnotBasisAction_target]
    rw [controlAfter, markerAfter, enabled]
  · have disabled : input (oraclePresentWireAt p slot) = false :=
      Bool.eq_false_of_not_eq_true enabled
    simp [prepareCandidateSlotReference, disabled]

/-- 1 slotのcandidate生成後、data wordはpresent時だけsource wordをXORする。 -/
theorem prepareCandidateSlotReference_data
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    let source := registerWordAt p register slot
    let target := (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
    readWires target (prepareCandidateSlotReference p register slot input) =
      if input (oraclePresentWireAt p slot) then
        List.zipWith
          (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
          (readWires source input) (readWires target input)
      else readWires target input := by
  dsimp only
  let source := registerWordAt p register slot
  let target := (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let control := oraclePresentWireAt p slot
  let marker := candidateMarkerWire p (slotToSortWord p slot)
  have slotLayout := prepareCandidateSlot_layout p register layout slot
  rcases slotLayout with
    ⟨sameLength, sourceTarget, _, _, targetNodup, _⟩
  have markerTarget : marker ∉ target := by
    exact candidateMarkerWire_not_mem_data p (slotToSortWord p slot)
  by_cases enabled : input (oraclePresentWireAt p slot) = true
  · rw [prepareCandidateSlotReference]
    rw [if_pos enabled]
    rw [readWires_cnotBasisAction_of_not_mem target control marker _ markerTarget]
    have sourceNodup : source.Nodup := by
      exact layout.membership.decoder.nodup.drop.take
    let copyLayout := ValidatedRegisterXorCopyLayout.ofLists source target
      sourceNodup targetNodup sameLength sourceTarget
    rw [show (TotalReversibleStage.xorCopy source target).reference input =
        copyLayout.basisAction input by
      simpa [copyLayout] using copyLayout.xorCopyStage_reference_eq_basisAction input]
    rw [show readWires target (copyLayout.basisAction input) =
        List.zipWith
          (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
          (readWires source input) (readWires target input) by
      simpa [copyLayout] using
        readWires_validatedRegisterXorCopyBasisAction_target copyLayout input]
    simp only [enabled, if_true, source, target]
  · have disabled : input (oraclePresentWireAt p slot) = false :=
      Bool.eq_false_of_not_eq_true enabled
    rw [prepareCandidateSlotReference]
    rw [if_neg enabled]
    simpa only [disabled, Bool.false_eq_true, if_false] using
      readWires_cnotBasisAction_of_not_mem target control marker input markerTarget

/-- 1 slotのcandidate参照作用は、そのslotのdataとmarker以外を変更しない。 -/
theorem prepareCandidateSlotReference_other
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideData : wire ∉
      (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth)
    (outsideMarker : wire ≠
      candidateMarkerWire p (slotToSortWord p slot)) :
    prepareCandidateSlotReference p register slot input wire = input wire := by
  let source := registerWordAt p register slot
  let target := (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let control := oraclePresentWireAt p slot
  let marker := candidateMarkerWire p (slotToSortWord p slot)
  by_cases enabled : input (oraclePresentWireAt p slot) = true
  · rw [prepareCandidateSlotReference, if_pos enabled]
    rw [cnotBasisAction_other control marker wire outsideMarker]
    exact TotalReversibleStage.xorCopy_reference_apply_outside_target
      source target input wire outsideData
  · rw [prepareCandidateSlotReference, if_neg enabled]
    exact cnotBasisAction_other control marker wire outsideMarker input

/-- 任意candidate markerはcandidate全体sliceに属する。 -/
theorem candidateMarkerWire_mem_candidateSlice
    (p : QParameters) (word : Fin p.sortWordCount) :
    candidateMarkerWire p word ∈
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
  apply candidateWordAt_mem_candidateSlice p word
  simp [candidateMarkerWire, candidateWordAt]

/-- 1 slotのcandidate参照作用はsource registerの任意wireを保存する。 -/
theorem prepareCandidateSlotReference_register
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth) (member : wire ∈ register) :
    prepareCandidateSlotReference p register slot input wire = input wire := by
  apply prepareCandidateSlotReference_other
  · intro targetMember
    exact (List.disjoint_left.mp layout.disjoint_candidate member)
      (candidateWordAt_mem_candidateSlice p _
        (List.mem_of_mem_take targetMember))
  · intro equal
    rw [equal] at member
    exact (List.disjoint_left.mp layout.disjoint_candidate member)
      (candidateMarkerWire_mem_candidateSlice p _)

/-- 1 slotのcandidate参照作用は全present flagを保存する。 -/
theorem prepareCandidateSlotReference_present
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot presentSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    prepareCandidateSlotReference p register slot input
        (oraclePresentWireAt p presentSlot) =
      input (oraclePresentWireAt p presentSlot) := by
  have presentMember : oraclePresentWireAt p presentSlot ∈ oraclePresentWires p := by
    simp [oraclePresentWireAt, oraclePresentWires, QParameters.presentWidth]
  apply prepareCandidateSlotReference_other
  · intro targetMember
    exact (List.disjoint_left.mp
      (oraclePresentWires_disjoint_candidateSlice p) presentMember)
      (candidateWordAt_mem_candidateSlice p _
        (List.mem_of_mem_take targetMember))
  · intro equal
    rw [equal] at presentMember
    exact (List.disjoint_left.mp
      (oraclePresentWires_disjoint_candidateSlice p) presentMember)
      (candidateMarkerWire_mem_candidateSlice p _)

/-- 異なるwordを担当するslot作用は指定candidate data wordを保存する。 -/
theorem prepareCandidateSlotReference_data_other_word
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (word : Fin p.sortWordCount)
    (different : word ≠ slotToSortWord p slot)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires ((candidateWordAt p word).take p.wordWidth)
        (prepareCandidateSlotReference p register slot input) =
      readWires ((candidateWordAt p word).take p.wordWidth) input := by
  apply List.map_congr_left
  intro wire member
  apply prepareCandidateSlotReference_other
  · intro targetMember
    exact (List.disjoint_left.mp
      (candidateWordAt_disjoint_of_ne p word (slotToSortWord p slot) different)
      (List.mem_of_mem_take member)) (List.mem_of_mem_take targetMember)
  · intro equal
    have markerMember : candidateMarkerWire p (slotToSortWord p slot) ∈
        candidateWordAt p (slotToSortWord p slot) := by
      simp [candidateMarkerWire, candidateWordAt]
    rw [equal] at member
    exact (List.disjoint_left.mp
      (candidateWordAt_disjoint_of_ne p word (slotToSortWord p slot) different)
      (List.mem_of_mem_take member)) markerMember

/-- 異なるwordを担当するslot作用は指定candidate markerを保存する。 -/
theorem prepareCandidateSlotReference_marker_other_word
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (word : Fin p.sortWordCount)
    (different : word ≠ slotToSortWord p slot)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    prepareCandidateSlotReference p register slot input
        (candidateMarkerWire p word) =
      input (candidateMarkerWire p word) := by
  apply prepareCandidateSlotReference_other
  · intro targetMember
    have markerMember : candidateMarkerWire p word ∈ candidateWordAt p word := by
      simp [candidateMarkerWire, candidateWordAt]
    exact (List.disjoint_left.mp
      (candidateWordAt_disjoint_of_ne p word (slotToSortWord p slot) different)
      markerMember) (List.mem_of_mem_take targetMember)
  · intro equal
    exact different (candidateMarkerWire_injective p equal)

/-- 1 slot作用はsource register全体の読出し値を保存する。 -/
theorem prepareCandidateSlotReference_read_register
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires register (prepareCandidateSlotReference p register slot input) =
      readWires register input := by
  apply List.map_congr_left
  intro wire member
  exact prepareCandidateSlotReference_register p register layout slot input wire member

/-- 正本の1 slot candidate回路は基底作用参照関数と厳密に一致する。 -/
theorem runBasis_prepareCandidateSlotTyped
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (prepareCandidateSlotTyped p register slot).runBasis
        reversibleGatePermutation input =
      prepareCandidateSlotReference p register slot input := by
  let source := registerWordAt p register slot
  let target := (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let control := oraclePresentWireAt p slot
  let marker := candidateMarkerWire p (slotToSortWord p slot)
  have slotLayout := prepareCandidateSlot_layout p register layout slot
  rcases slotLayout with
    ⟨sameLength, sourceTarget, controlSource, controlTarget, _, controlMarker⟩
  rw [prepareCandidateSlotTyped, runBasis_seq]
  rw [runBasis_controlledXorCopy control source target input sameLength
    sourceTarget controlSource controlTarget]
  by_cases enabled : input control = true
  · simp only [enabled, if_true]
    rw [runBasis_rawXorCopy_eq_reference]
    rw [runBasis_safeCnot control marker controlMarker]
    have enabledConcrete : input (oraclePresentWireAt p slot) = true := by
      simpa [control] using enabled
    dsimp only [source, target, control, marker]
    simp [prepareCandidateSlotReference, enabledConcrete]
  · have disabled : input control = false := Bool.eq_false_of_not_eq_true enabled
    simp only [disabled, Bool.false_eq_true, if_false]
    rw [runBasis_safeCnot control marker controlMarker]
    have disabledConcrete : input (oraclePresentWireAt p slot) = false := by
      simpa [control] using disabled
    dsimp only [source, target, control, marker]
    simp [prepareCandidateSlotReference, disabledConcrete]

/-- candidate marker列を左から初期化する純粋な基底作用。 -/
def initializeCandidateMarkersReference
    (p : QParameters) (words : List (Fin p.sortWordCount))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  words.foldl (fun state word =>
    xBasisAction (candidateMarkerWire p word) state) input

/-- 指定word列に属するmarker以外のwireは、marker初期化列で変化しない。 -/
theorem initializeCandidateMarkersReference_other (p : QParameters) :
    ∀ (words : List (Fin p.sortWordCount))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (wire : Wire p.ancillaWidth p.systemWidth),
      (∀ word ∈ words, wire ≠ candidateMarkerWire p word) →
      initializeCandidateMarkersReference p words input wire = input wire
  | [], _, _, _ => rfl
  | word :: words, input, wire, outside => by
      have headDifferent : wire ≠ candidateMarkerWire p word :=
        outside word (by simp)
      have tailOutside : ∀ tailWord ∈ words,
          wire ≠ candidateMarkerWire p tailWord := by
        intro tailWord member
        exact outside tailWord (by simp [member])
      change initializeCandidateMarkersReference p words
          (xBasisAction (candidateMarkerWire p word) input) wire = input wire
      rw [initializeCandidateMarkersReference_other p words _ wire tailOutside]
      exact xBasisAction_other _ _ headDifferent input

/-- Nodupなword列では、列に属するmarkerは初期値をちょうど一回反転する。 -/
theorem initializeCandidateMarkersReference_marker (p : QParameters) :
    ∀ (words : List (Fin p.sortWordCount))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (target : Fin p.sortWordCount),
      words.Nodup → target ∈ words →
      initializeCandidateMarkersReference p words input
          (candidateMarkerWire p target) =
        !(input (candidateMarkerWire p target))
  | [], _, _, _, member => by simp at member
  | word :: words, input, target, nodup, member => by
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rcases List.mem_cons.mp member with targetHead | targetTail
      · subst target
        have tailOutside : ∀ tailWord ∈ words,
            candidateMarkerWire p word ≠ candidateMarkerWire p tailWord := by
          intro tailWord tailMember equal
          exact headAbsent ((candidateMarkerWire_injective p equal).symm ▸ tailMember)
        change initializeCandidateMarkersReference p words
            (xBasisAction (candidateMarkerWire p word) input)
              (candidateMarkerWire p word) = _
        rw [initializeCandidateMarkersReference_other p words _ _ tailOutside]
        exact xBasisAction_target _ input
      · have headDifferent :
            candidateMarkerWire p target ≠ candidateMarkerWire p word := by
          intro equal
          have targetWord := candidateMarkerWire_injective p equal
          subst target
          exact headAbsent targetTail
        change initializeCandidateMarkersReference p words
            (xBasisAction (candidateMarkerWire p word) input)
              (candidateMarkerWire p target) = _
        rw [initializeCandidateMarkersReference_marker p words _ target tailNodup
          targetTail]
        rw [xBasisAction_other _ _ headDifferent]

/-- 全padding wordを含むmarker初期化後は、任意wordのmarkerが一度だけ反転する。 -/
theorem initializeAllCandidateMarkersReference_marker
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (target : Fin p.sortWordCount) :
    initializeCandidateMarkersReference p (List.finRange p.sortWordCount) input
        (candidateMarkerWire p target) =
      !(input (candidateMarkerWire p target)) := by
  exact initializeCandidateMarkersReference_marker p _ input target
    (List.nodup_finRange _) (List.mem_finRange _)

/-- candidate生成開始時に要求する、全data bitと全markerが0である条件。 -/
structure CandidateRegionClean (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 全candidate data wordが0である。 -/
  data_zero : ∀ word : Fin p.sortWordCount,
    readWires ((candidateWordAt p word).take p.wordWidth) input =
      List.replicate p.wordWidth false
  /-- 全candidate markerが0である。 -/
  marker_zero : ∀ word : Fin p.sortWordCount,
    input (candidateMarkerWire p word) = false

/-- 全0アンシラ標準入力ではcandidate領域全体がcleanである。 -/
theorem zeroAncillaJointBasis_candidateRegionClean
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    CandidateRegionClean p (zeroAncillaJointBasis p system) where
  data_zero := by
    intro word
    let data := (candidateWordAt p word).take p.wordWidth
    calc
      readWires data (zeroAncillaJointBasis p system) =
          data.map (fun _ => false) := by
        apply List.map_congr_left
        intro wire member
        have fullMember := List.mem_of_mem_take member
        rcases List.mem_map.mp fullMember with ⟨bit, _, rfl⟩
        exact zeroAncillaJointBasis_ancilla p system _
      _ = List.replicate data.length false := by simp
      _ = List.replicate p.wordWidth false := by
        rw [show data.length = p.wordWidth by
          exact candidateWordAt_data_length p word]
  marker_zero := by
    intro word
    simp [candidateMarkerWire, candidateWordWire,
      RegisterSlice.ancillaWire]

/-- marker初期化列は、任意candidate wordのdata部分を変更しない。 -/
theorem initializeCandidateMarkersReference_data
    (p : QParameters) (words : List (Fin p.sortWordCount))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (dataWord : Fin p.sortWordCount) :
    readWires ((candidateWordAt p dataWord).take p.wordWidth)
        (initializeCandidateMarkersReference p words input) =
      readWires ((candidateWordAt p dataWord).take p.wordWidth) input := by
  apply List.map_congr_left
  intro wire member
  apply initializeCandidateMarkersReference_other
  intro markerWord markerMember equal
  exact candidateMarkerWire_not_mem_data_any p markerWord dataWord
    (equal ▸ member)

/-- clean領域を全marker初期化した直後もdataは0のままである。 -/
theorem initializeAllCandidateMarkersReference_data_zero
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CandidateRegionClean p input)
    (dataWord : Fin p.sortWordCount) :
    readWires ((candidateWordAt p dataWord).take p.wordWidth)
        (initializeCandidateMarkersReference p
          (List.finRange p.sortWordCount) input) =
      List.replicate p.wordWidth false := by
  rw [initializeCandidateMarkersReference_data]
  exact clean.data_zero dataWord

/-- clean領域を全marker初期化した直後は、全markerが1になる。 -/
theorem initializeAllCandidateMarkersReference_marker_one
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CandidateRegionClean p input)
    (word : Fin p.sortWordCount) :
    initializeCandidateMarkersReference p (List.finRange p.sortWordCount) input
        (candidateMarkerWire p word) = true := by
  rw [initializeAllCandidateMarkersReference_marker]
  simp [clean.marker_zero word]

/-- candidate slot列を左から条件付きコピーする純粋な基底作用。 -/
def prepareCandidateSlotsReference
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slots : List (Fin p.K))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  slots.foldl (fun state slot =>
    prepareCandidateSlotReference p register slot state) input

/-- candidate slot列全体もsource registerの任意wireを保存する。 -/
theorem prepareCandidateSlotsReference_register
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (wire : Wire p.ancillaWidth p.systemWidth), wire ∈ register →
      prepareCandidateSlotsReference p register slots input wire = input wire
  | [], _, _, _ => rfl
  | slot :: slots, input, wire, member => by
      change prepareCandidateSlotsReference p register slots
          (prepareCandidateSlotReference p register slot input) wire = input wire
      rw [prepareCandidateSlotsReference_register p register layout slots _ wire
        member]
      exact prepareCandidateSlotReference_register p register layout slot input
        wire member

/-- candidate slot列全体も任意のpresent flagを保存する。 -/
theorem prepareCandidateSlotsReference_present
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (presentSlot : Fin p.K),
      prepareCandidateSlotsReference p register slots input
          (oraclePresentWireAt p presentSlot) =
        input (oraclePresentWireAt p presentSlot)
  | [], _, _ => rfl
  | slot :: slots, input, presentSlot => by
      change prepareCandidateSlotsReference p register slots
          (prepareCandidateSlotReference p register slot input)
            (oraclePresentWireAt p presentSlot) = _
      rw [prepareCandidateSlotsReference_present p register slots _ presentSlot]
      exact prepareCandidateSlotReference_present p register slot presentSlot input

/-- 対象slotを含まないslot列は、そのcandidate data wordを保存する。 -/
theorem prepareCandidateSlotsReference_data_of_not_mem
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (target : Fin p.K), target ∉ slots →
      readWires
          ((candidateWordAt p (slotToSortWord p target)).take p.wordWidth)
          (prepareCandidateSlotsReference p register slots input) =
        readWires
          ((candidateWordAt p (slotToSortWord p target)).take p.wordWidth) input
  | [], _, _, _ => rfl
  | slot :: slots, input, target, absent => by
      have targetNeSlot : target ≠ slot := by
        intro equal
        subst slot
        exact absent (by simp)
      have targetAbsentTail : target ∉ slots := by
        intro member
        exact absent (by simp [member])
      have wordDifferent : slotToSortWord p target ≠ slotToSortWord p slot := by
        intro equal
        exact targetNeSlot (slotToSortWord_injective p equal)
      change readWires _ (prepareCandidateSlotsReference p register slots
          (prepareCandidateSlotReference p register slot input)) = _
      rw [prepareCandidateSlotsReference_data_of_not_mem p register slots _ target
        targetAbsentTail]
      exact prepareCandidateSlotReference_data_other_word p register slot
        (slotToSortWord p target) wordDifferent input

/-- 対象slotを含まないslot列は、そのcandidate markerを保存する。 -/
theorem prepareCandidateSlotsReference_marker_of_not_mem
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (target : Fin p.K), target ∉ slots →
      prepareCandidateSlotsReference p register slots input
          (candidateMarkerWire p (slotToSortWord p target)) =
        input (candidateMarkerWire p (slotToSortWord p target))
  | [], _, _, _ => rfl
  | slot :: slots, input, target, absent => by
      have targetNeSlot : target ≠ slot := by
        intro equal
        subst slot
        exact absent (by simp)
      have targetAbsentTail : target ∉ slots := by
        intro member
        exact absent (by simp [member])
      have wordDifferent : slotToSortWord p target ≠ slotToSortWord p slot := by
        intro equal
        exact targetNeSlot (slotToSortWord_injective p equal)
      change prepareCandidateSlotsReference p register slots
          (prepareCandidateSlotReference p register slot input)
            (candidateMarkerWire p (slotToSortWord p target)) = _
      rw [prepareCandidateSlotsReference_marker_of_not_mem p register slots _ target
        targetAbsentTail]
      exact prepareCandidateSlotReference_marker_other_word p register slot
        (slotToSortWord p target) wordDifferent input

/-- 全slotが異なるwordを担当するなら、任意のpadding data wordは保存される。 -/
theorem prepareCandidateSlotsReference_data_word_of_forall_ne
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (word : Fin p.sortWordCount),
      (∀ slot ∈ slots, word ≠ slotToSortWord p slot) →
      readWires ((candidateWordAt p word).take p.wordWidth)
          (prepareCandidateSlotsReference p register slots input) =
        readWires ((candidateWordAt p word).take p.wordWidth) input
  | [], _, _, _ => rfl
  | slot :: slots, input, word, different => by
      have headDifferent := different slot (by simp)
      have tailDifferent : ∀ tailSlot ∈ slots,
          word ≠ slotToSortWord p tailSlot := by
        intro tailSlot member
        exact different tailSlot (by simp [member])
      change readWires _ (prepareCandidateSlotsReference p register slots
          (prepareCandidateSlotReference p register slot input)) = _
      rw [prepareCandidateSlotsReference_data_word_of_forall_ne p register slots _
        word tailDifferent]
      exact prepareCandidateSlotReference_data_other_word p register slot word
        headDifferent input

/-- 全slotが異なるwordを担当するなら、任意のpadding markerは保存される。 -/
theorem prepareCandidateSlotsReference_marker_word_of_forall_ne
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (word : Fin p.sortWordCount),
      (∀ slot ∈ slots, word ≠ slotToSortWord p slot) →
      prepareCandidateSlotsReference p register slots input
          (candidateMarkerWire p word) = input (candidateMarkerWire p word)
  | [], _, _, _ => rfl
  | slot :: slots, input, word, different => by
      have headDifferent := different slot (by simp)
      have tailDifferent : ∀ tailSlot ∈ slots,
          word ≠ slotToSortWord p tailSlot := by
        intro tailSlot member
        exact different tailSlot (by simp [member])
      change prepareCandidateSlotsReference p register slots
          (prepareCandidateSlotReference p register slot input)
            (candidateMarkerWire p word) = _
      rw [prepareCandidateSlotsReference_marker_word_of_forall_ne p register slots _
        word tailDifferent]
      exact prepareCandidateSlotReference_marker_other_word p register slot word
        headDifferent input

/-- Nodupなslot列では、対象candidate dataへそのslot作用がちょうど一回反映される。 -/
theorem prepareCandidateSlotsReference_data
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (target : Fin p.K), slots.Nodup → target ∈ slots →
      let source := registerWordAt p register target
      let data :=
        (candidateWordAt p (slotToSortWord p target)).take p.wordWidth
      readWires data (prepareCandidateSlotsReference p register slots input) =
        if input (oraclePresentWireAt p target) then
          List.zipWith
            (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
            (readWires source input) (readWires data input)
        else readWires data input
  | [], _, _, _, member => by simp at member
  | slot :: slots, input, target, nodup, member => by
      dsimp only
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rcases List.mem_cons.mp member with targetHead | targetTail
      · subst slot
        change readWires _ (prepareCandidateSlotsReference p register slots
            (prepareCandidateSlotReference p register target input)) = _
        rw [prepareCandidateSlotsReference_data_of_not_mem p register slots _ target
          headAbsent]
        exact prepareCandidateSlotReference_data p register layout target input
      · have targetNeSlot : target ≠ slot := by
          intro equal
          subst slot
          exact headAbsent targetTail
        have wordDifferent :
            slotToSortWord p target ≠ slotToSortWord p slot := by
          intro equal
          exact targetNeSlot (slotToSortWord_injective p equal)
        let afterHead := prepareCandidateSlotReference p register slot input
        change readWires _
            (prepareCandidateSlotsReference p register slots afterHead) = _
        rw [prepareCandidateSlotsReference_data p register layout slots afterHead
          target tailNodup targetTail]
        have presentPreserved := prepareCandidateSlotReference_present p register
          slot target input
        change afterHead (oraclePresentWireAt p target) =
          input (oraclePresentWireAt p target) at presentPreserved
        have dataPreserved := prepareCandidateSlotReference_data_other_word p
          register slot (slotToSortWord p target) wordDifferent input
        change readWires
            ((candidateWordAt p (slotToSortWord p target)).take p.wordWidth)
              afterHead =
          readWires
            ((candidateWordAt p (slotToSortWord p target)).take p.wordWidth)
              input at dataPreserved
        have sourcePreserved :
            readWires (registerWordAt p register target) afterHead =
              readWires (registerWordAt p register target) input := by
          apply List.map_congr_left
          intro wire sourceMember
          exact prepareCandidateSlotReference_register p register layout slot input
            wire (mem_register_of_mem_registerWordAt p register target sourceMember)
        rw [presentPreserved, sourcePreserved, dataPreserved]

/-- Nodupなslot列では、対象candidate markerへpresentがちょうど一回XORされる。 -/
theorem prepareCandidateSlotsReference_marker
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (target : Fin p.K), slots.Nodup → target ∈ slots →
      prepareCandidateSlotsReference p register slots input
          (candidateMarkerWire p (slotToSortWord p target)) =
        if input (oraclePresentWireAt p target) then
          !(input (candidateMarkerWire p (slotToSortWord p target)))
        else input (candidateMarkerWire p (slotToSortWord p target))
  | [], _, _, _, member => by simp at member
  | slot :: slots, input, target, nodup, member => by
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rcases List.mem_cons.mp member with targetHead | targetTail
      · subst slot
        change prepareCandidateSlotsReference p register slots
            (prepareCandidateSlotReference p register target input)
              (candidateMarkerWire p (slotToSortWord p target)) = _
        rw [prepareCandidateSlotsReference_marker_of_not_mem p register slots _ target
          headAbsent]
        exact prepareCandidateSlotReference_marker p register layout target input
      · have targetNeSlot : target ≠ slot := by
          intro equal
          subst slot
          exact headAbsent targetTail
        have wordDifferent :
            slotToSortWord p target ≠ slotToSortWord p slot := by
          intro equal
          exact targetNeSlot (slotToSortWord_injective p equal)
        let afterHead := prepareCandidateSlotReference p register slot input
        change prepareCandidateSlotsReference p register slots afterHead
            (candidateMarkerWire p (slotToSortWord p target)) = _
        rw [prepareCandidateSlotsReference_marker p register layout slots afterHead
          target tailNodup targetTail]
        have presentPreserved := prepareCandidateSlotReference_present p register
          slot target input
        change afterHead (oraclePresentWireAt p target) =
          input (oraclePresentWireAt p target) at presentPreserved
        have markerPreserved := prepareCandidateSlotReference_marker_other_word p
          register slot (slotToSortWord p target) wordDifferent input
        change afterHead (candidateMarkerWire p (slotToSortWord p target)) =
          input (candidateMarkerWire p (slotToSortWord p target)) at markerPreserved
        rw [presentPreserved, markerPreserved]

/-- `xorConfigurationIntoCandidateRegisterCircuit`全体の基底作用参照関数。 -/
def ConfigurationToCandidateRegisterXorSpec
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let marked := initializeCandidateMarkersReference p
    (List.finRange p.sortWordCount) input
  prepareCandidateSlotsReference p register (List.finRange p.K) marked

/-- false列へのbitwise XORはsource bit列そのものになる。 -/
theorem candidateZipWithXorFalse (bits : List Bool) :
    List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        bits (List.replicate bits.length false) = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      cases bit <;>
        simp [List.replicate_succ, ← Nat.succ_eq_add_one, inductionHypothesis]

/--
clean領域からcandidate生成全体を実行すると、active slotのdataはpresent時にsource word、
absent時に0 wordとなる。
-/
theorem configurationToCandidateRegisterXorSpec_active_data
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CandidateRegionClean p input)
    (target : Fin p.K) :
    let data :=
      (candidateWordAt p (slotToSortWord p target)).take p.wordWidth
    readWires data (ConfigurationToCandidateRegisterXorSpec p register input) =
      if input (oraclePresentWireAt p target) then
        readWires (registerWordAt p register target) input
      else List.replicate p.wordWidth false := by
  dsimp only
  let marked := initializeCandidateMarkersReference p
    (List.finRange p.sortWordCount) input
  rw [ConfigurationToCandidateRegisterXorSpec]
  change readWires _
      (prepareCandidateSlotsReference p register (List.finRange p.K) marked) = _
  rw [prepareCandidateSlotsReference_data p register layout
    (List.finRange p.K) marked target (List.nodup_finRange _)
    (List.mem_finRange _)]
  have presentMarked : marked (oraclePresentWireAt p target) =
      input (oraclePresentWireAt p target) := by
    apply initializeCandidateMarkersReference_other
    intro markerWord markerMember equal
    have presentMember : oraclePresentWireAt p target ∈ oraclePresentWires p := by
      simp [oraclePresentWireAt, oraclePresentWires, QParameters.presentWidth]
    rw [equal] at presentMember
    exact (List.disjoint_left.mp
      (oraclePresentWires_disjoint_candidateSlice p) presentMember)
      (candidateMarkerWire_mem_candidateSlice p markerWord)
  have sourceMarked :
      readWires (registerWordAt p register target) marked =
        readWires (registerWordAt p register target) input := by
    apply List.map_congr_left
    intro wire sourceMember
    apply initializeCandidateMarkersReference_other
    intro markerWord markerMember equal
    have registerMember := mem_register_of_mem_registerWordAt p register target
      sourceMember
    rw [equal] at registerMember
    exact (List.disjoint_left.mp layout.disjoint_candidate registerMember)
      (candidateMarkerWire_mem_candidateSlice p markerWord)
  have dataMarked := initializeAllCandidateMarkersReference_data_zero p input clean
    (slotToSortWord p target)
  change readWires
      ((candidateWordAt p (slotToSortWord p target)).take p.wordWidth) marked =
        List.replicate p.wordWidth false at dataMarked
  rw [presentMarked, sourceMarked, dataMarked]
  by_cases present : input (oraclePresentWireAt p target) = true
  · simp only [present, if_true]
    have sourceLength := registerWordAt_length p register
      layout.membership.decoder.length_eq target
    rw [← sourceLength]
    simpa [readWires] using candidateZipWithXorFalse
      (readWires (registerWordAt p register target) input)
  · have absent : input (oraclePresentWireAt p target) = false :=
      Bool.eq_false_of_not_eq_true present
    simp [absent]

/-- clean領域からのcandidate生成後、active slotのmarkerはpresentの否定になる。 -/
theorem configurationToCandidateRegisterXorSpec_active_marker
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CandidateRegionClean p input)
    (target : Fin p.K) :
    ConfigurationToCandidateRegisterXorSpec p register input
        (candidateMarkerWire p (slotToSortWord p target)) =
      !(input (oraclePresentWireAt p target)) := by
  let marked := initializeCandidateMarkersReference p
    (List.finRange p.sortWordCount) input
  rw [ConfigurationToCandidateRegisterXorSpec]
  change prepareCandidateSlotsReference p register (List.finRange p.K) marked
      (candidateMarkerWire p (slotToSortWord p target)) = _
  rw [prepareCandidateSlotsReference_marker p register layout
    (List.finRange p.K) marked target (List.nodup_finRange _)
    (List.mem_finRange _)]
  have presentMarked : marked (oraclePresentWireAt p target) =
      input (oraclePresentWireAt p target) := by
    apply initializeCandidateMarkersReference_other
    intro markerWord markerMember equal
    have presentMember : oraclePresentWireAt p target ∈ oraclePresentWires p := by
      simp [oraclePresentWireAt, oraclePresentWires, QParameters.presentWidth]
    rw [equal] at presentMember
    exact (List.disjoint_left.mp
      (oraclePresentWires_disjoint_candidateSlice p) presentMember)
      (candidateMarkerWire_mem_candidateSlice p markerWord)
  have markerMarked := initializeAllCandidateMarkersReference_marker_one p input clean
    (slotToSortWord p target)
  change marked (candidateMarkerWire p (slotToSortWord p target)) = true at markerMarked
  rw [presentMarked, markerMarked]
  cases input (oraclePresentWireAt p target) <;> rfl

/-- clean領域では、`word.val ≥ K`のpadding candidate dataは生成後も0である。 -/
theorem configurationToCandidateRegisterXorSpec_padding_data
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CandidateRegionClean p input)
    (word : Fin p.sortWordCount) (padding : p.K ≤ word.val) :
    readWires ((candidateWordAt p word).take p.wordWidth)
        (ConfigurationToCandidateRegisterXorSpec p register input) =
      List.replicate p.wordWidth false := by
  let marked := initializeCandidateMarkersReference p
    (List.finRange p.sortWordCount) input
  rw [ConfigurationToCandidateRegisterXorSpec]
  change readWires _
      (prepareCandidateSlotsReference p register (List.finRange p.K) marked) = _
  rw [prepareCandidateSlotsReference_data_word_of_forall_ne p register
    (List.finRange p.K) marked word]
  · exact initializeAllCandidateMarkersReference_data_zero p input clean word
  · intro slot slotMember equal
    have values := congrArg Fin.val equal
    simp [slotToSortWord] at values
    omega

/-- clean領域では、`word.val ≥ K`のpadding candidate markerは生成後も1である。 -/
theorem configurationToCandidateRegisterXorSpec_padding_marker
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CandidateRegionClean p input)
    (word : Fin p.sortWordCount) (padding : p.K ≤ word.val) :
    ConfigurationToCandidateRegisterXorSpec p register input (candidateMarkerWire p word) =
      true := by
  let marked := initializeCandidateMarkersReference p
    (List.finRange p.sortWordCount) input
  rw [ConfigurationToCandidateRegisterXorSpec]
  change prepareCandidateSlotsReference p register (List.finRange p.K) marked
      (candidateMarkerWire p word) = _
  rw [prepareCandidateSlotsReference_marker_word_of_forall_ne p register
    (List.finRange p.K) marked word]
  · exact initializeAllCandidateMarkersReference_marker_one p input clean word
  · intro slot slotMember equal
    have values := congrArg Fin.val equal
    simp [slotToSortWord] at values
    omega

/-- 任意のword列についてmarker初期化回路列は参照作用と一致する。 -/
theorem runBasis_initializeCandidateMarkerSequence (p : QParameters) :
    ∀ (words : List (Fin p.sortWordCount))
      (input : JointBasis p.ancillaWidth p.systemWidth),
    (Circuit.sequence <| words.map fun word =>
      initializeCandidateMarkerTyped p word).runBasis
        reversibleGatePermutation input =
      initializeCandidateMarkersReference p words input
  | [], _ => rfl
  | word :: words, input => by
      simp only [List.map_cons, Circuit.sequence,
        VerifiedCircuitCore.Circuit.sequence, runBasis_seq,
        initializeCandidateMarkerTyped, runBasis_x]
      exact runBasis_initializeCandidateMarkerSequence p words
        (xBasisAction (candidateMarkerWire p word) input)

/-- 任意のslot列についてcandidate copy回路列は参照作用と一致する。 -/
theorem runBasis_prepareCandidateSlotSequence
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth),
    (Circuit.sequence <| slots.map fun slot =>
      prepareCandidateSlotTyped p register slot).runBasis
        reversibleGatePermutation input =
      prepareCandidateSlotsReference p register slots input
  | [], _ => rfl
  | slot :: slots, input => by
      simp only [List.map_cons, Circuit.sequence,
        VerifiedCircuitCore.Circuit.sequence, runBasis_seq]
      rw [runBasis_prepareCandidateSlotTyped p register layout slot input]
      exact runBasis_prepareCandidateSlotSequence p register layout slots
        (prepareCandidateSlotReference p register slot input)

/-- 型安全なcandidate生成正本回路全体は参照作用と厳密に一致する。 -/
theorem runBasis_xorConfigurationIntoCandidateRegisterCircuit
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (xorConfigurationIntoCandidateRegisterCircuit p register).runBasis
        reversibleGatePermutation input =
      ConfigurationToCandidateRegisterXorSpec p register input := by
  rw [xorConfigurationIntoCandidateRegisterCircuit, runBasis_seq]
  rw [show initializeCandidateMarkersTyped p =
      (List.finRange p.sortWordCount).map fun word =>
        initializeCandidateMarkerTyped p word by rfl]
  rw [runBasis_initializeCandidateMarkerSequence p
    (List.finRange p.sortWordCount) input]
  rw [show prepareCandidateSlotsTyped p register =
      (List.finRange p.K).map fun slot =>
        prepareCandidateSlotTyped p register slot by rfl]
  exact runBasis_prepareCandidateSlotSequence p register layout
    (List.finRange p.K)
    (initializeCandidateMarkersReference p (List.finRange p.sortWordCount) input)

end ReversibleCircuit

end ProbabilityGeneratorQProof
