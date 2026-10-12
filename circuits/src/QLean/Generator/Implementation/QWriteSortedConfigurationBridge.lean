import QLean.Generator.Implementation.QWriteMovedSelectorLayoutCanonical
import QLean.Generator.Implementation.QSortedCandidateBridge
import QLean.Generator.Implementation.ReversibleLogicSharedCoreReadoutAdapter

/-!
# sorted writer と合法配置の接続

degree one-hot と canonical candidate を、sorted writer の有限 fold 仕様へ接続する。
全状態や巨大行列は列挙せず、唯一の有効 degree だけをリスト分解で取り出す。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- canonical 出力registerの相異なる二つのword sliceは交わらない。 -/
theorem canonicalRegisterWordAt_disjoint_of_ne
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (left right : Fin p.K) (different : left ≠ right) :
    (registerWordAt p (canonicalSortedOutputWires p kind) left).Disjoint
      (registerWordAt p (canonicalSortedOutputWires p kind) right) := by
  rw [List.disjoint_left]
  intro wire leftMember rightMember
  rcases List.mem_iff_getElem.mp leftMember with
    ⟨leftBit, leftBitLt, leftAt⟩
  rcases List.mem_iff_getElem.mp rightMember with
    ⟨rightBit, rightBitLt, rightAt⟩
  have leftBitWidth : leftBit < p.wordWidth := by
    exact lt_of_lt_of_le leftBitLt (List.length_take_le _ _)
  have rightBitWidth : rightBit < p.wordWidth := by
    exact lt_of_lt_of_le rightBitLt (List.length_take_le _ _)
  have leftPhysicalLt : p.wordWidth * left.val + leftBit < p.systemWidth := by
    simp only [QParameters.systemWidth]
    have slotNext : left.val + 1 ≤ p.K := Nat.succ_le_of_lt left.isLt
    calc
      p.wordWidth * left.val + leftBit <
          p.wordWidth * left.val + p.wordWidth :=
        Nat.add_lt_add_left leftBitWidth _
      _ = (left.val + 1) * p.wordWidth := by
        rw [Nat.succ_mul, Nat.mul_comm p.wordWidth left.val]
      _ ≤ p.K * p.wordWidth := Nat.mul_le_mul_right p.wordWidth slotNext
      _ = p.wordWidth * p.K := Nat.mul_comm _ _
      _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _
  have rightPhysicalLt : p.wordWidth * right.val + rightBit < p.systemWidth := by
    simp only [QParameters.systemWidth]
    have slotNext : right.val + 1 ≤ p.K := Nat.succ_le_of_lt right.isLt
    calc
      p.wordWidth * right.val + rightBit <
          p.wordWidth * right.val + p.wordWidth :=
        Nat.add_lt_add_left rightBitWidth _
      _ = (right.val + 1) * p.wordWidth := by
        rw [Nat.succ_mul, Nat.mul_comm p.wordWidth right.val]
      _ ≤ p.K * p.wordWidth := Nat.mul_le_mul_right p.wordWidth slotNext
      _ = p.wordWidth * p.K := Nat.mul_comm _ _
      _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _
  have leftOutputLt : p.wordWidth * left.val + leftBit <
      (canonicalSortedOutputWires p kind).length := by
    simpa using leftPhysicalLt
  have rightOutputLt : p.wordWidth * right.val + rightBit <
      (canonicalSortedOutputWires p kind).length := by
    simpa using rightPhysicalLt
  have leftAtFull :
      (canonicalSortedOutputWires p kind).get
          ⟨p.wordWidth * left.val + leftBit, leftOutputLt⟩
          = wire := by
    simpa [registerWordAt, Nat.mul_comm] using leftAt
  have rightAtFull :
      (canonicalSortedOutputWires p kind).get
          ⟨p.wordWidth * right.val + rightBit, rightOutputLt⟩
          = wire := by
    simpa [registerWordAt, Nat.mul_comm] using rightAt
  have positionsEqual :
      p.wordWidth * left.val + leftBit =
        p.wordWidth * right.val + rightBit := by
    exact (List.Nodup.getElem_inj_iff
      (canonicalSortedOutputWires_nodup p kind)).mp
        (leftAtFull.trans rightAtFull.symm)
  have wordWidthPositive : 0 < p.wordWidth := by
    simp [QParameters.wordWidth, p.q_pos]
  have leftValEqRightVal : left.val = right.val := by
    have leftDiv := congrArg (fun value => value / p.wordWidth) positionsEqual
    simpa [Nat.mul_add_div wordWidthPositive, Nat.div_eq_of_lt leftBitWidth,
      Nat.div_eq_of_lt rightBitWidth] using leftDiv
  exact different (Fin.ext leftValEqRightVal)

/-- canonical 出力の一つのword copyは、そのtarget wordを候補dataとのbitwise XORへ写す。 -/
theorem writeSortedCopyReference_read_own_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (slot : Fin outputDegree)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    let source := (candidateWordAt p
      (sortedOutputCandidateSlot p outputDegree outputDegreeLe slot)).take
        p.wordWidth
    let target := registerWordAt p (canonicalSortedOutputWires p kind)
      (sortedOutputRegisterSlot p outputDegree outputDegreeLe slot)
    readWires target
        (writeSortedCopyReference p (canonicalSortedOutputWires p kind)
          outputDegree outputDegreeLe true slot input) =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (readWires source input) (readWires target input) := by
  dsimp only
  let source := (candidateWordAt p
    (sortedOutputCandidateSlot p outputDegree outputDegreeLe slot)).take
      p.wordWidth
  let target := registerWordAt p (canonicalSortedOutputWires p kind)
    (sortedOutputRegisterSlot p outputDegree outputDegreeLe slot)
  have layout := canonicalSortedCopyLayout p kind
    (sortedOutputCandidateSlot p outputDegree outputDegreeLe slot)
    (sortedOutputRegisterSlot p outputDegree outputDegreeLe slot)
  have targetNodup : target.Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist p.wordWidth
        ((canonicalSortedOutputWires p kind).drop
          ((sortedOutputRegisterSlot p outputDegree outputDegreeLe slot).val *
            p.wordWidth))).trans
        (List.drop_sublist
          ((sortedOutputRegisterSlot p outputDegree outputDegreeLe slot).val *
            p.wordWidth) (canonicalSortedOutputWires p kind)))
    exact canonicalSortedOutputWires_nodup p kind
  have sourceNodup : source.Nodup := by
    change ((candidateWordAt p
      (sortedOutputCandidateSlot p outputDegree outputDegreeLe slot)).take
        p.wordWidth).Nodup
    exact (candidateWordAt_nodup p
      (sortedOutputCandidateSlot p outputDegree outputDegreeLe slot)).take
  let copyLayout := ValidatedRegisterXorCopyLayout.ofLists source target
    sourceNodup targetNodup layout.1 layout.2.1
  rw [show writeSortedCopyReference p (canonicalSortedOutputWires p kind)
      outputDegree outputDegreeLe true slot input =
        controlledCopyBasisReference true source target input by rfl]
  rw [show controlledCopyBasisReference true source target input =
      copyLayout.basisAction input by
    simp only [controlledCopyBasisReference, if_true]
    simpa [copyLayout] using
      copyLayout.xorCopyStage_reference_eq_basisAction input]
  simpa [copyLayout] using
    readWires_validatedRegisterXorCopyBasisAction_target copyLayout input

/-- 相異なるslotのcanonical word copyは、観測対象wordの全bitを保存する。 -/
theorem writeSortedCopyReference_read_other_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (sourceSlot observedSlot : Fin outputDegree)
    (different : sourceSlot ≠ observedSlot)
    (enabled : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (registerWordAt p (canonicalSortedOutputWires p kind)
        (sortedOutputRegisterSlot p outputDegree outputDegreeLe observedSlot))
      (writeSortedCopyReference p (canonicalSortedOutputWires p kind)
        outputDegree outputDegreeLe enabled sourceSlot input) =
    readWires (registerWordAt p (canonicalSortedOutputWires p kind)
      (sortedOutputRegisterSlot p outputDegree outputDegreeLe observedSlot)) input := by
  let sourceRegisterSlot :=
    sortedOutputRegisterSlot p outputDegree outputDegreeLe sourceSlot
  let observedRegisterSlot :=
    sortedOutputRegisterSlot p outputDegree outputDegreeLe observedSlot
  have registerSlotsDifferent : sourceRegisterSlot ≠ observedRegisterSlot := by
    intro equal
    apply different
    apply Fin.ext
    simpa [sourceRegisterSlot, observedRegisterSlot,
      sortedOutputRegisterSlot] using congrArg Fin.val equal
  have targetDisjointObserved :
      (registerWordAt p (canonicalSortedOutputWires p kind)
        sourceRegisterSlot).Disjoint
      (registerWordAt p (canonicalSortedOutputWires p kind)
        observedRegisterSlot) :=
    canonicalRegisterWordAt_disjoint_of_ne p kind sourceRegisterSlot
      observedRegisterSlot registerSlotsDifferent
  apply List.map_congr_left
  intro wire observedMember
  unfold writeSortedCopyReference
  apply controlledCopyBasisReference_outside_target
  exact (List.disjoint_left.mp targetDisjointObserved.symm) observedMember

/--
copy元slotを`Fin K`へ埋め込んだ位置と異なる任意のcanonical register wordは保存される。
-/
theorem writeSortedCopyReference_read_registerWord_other_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (sourceSlot : Fin outputDegree) (observedSlot : Fin p.K)
    (different :
      sortedOutputRegisterSlot p outputDegree outputDegreeLe sourceSlot ≠
        observedSlot)
    (enabled : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (registerWordAt p (canonicalSortedOutputWires p kind) observedSlot)
      (writeSortedCopyReference p (canonicalSortedOutputWires p kind)
        outputDegree outputDegreeLe enabled sourceSlot input) =
    readWires (registerWordAt p (canonicalSortedOutputWires p kind) observedSlot)
      input := by
  have targetDisjointObserved := canonicalRegisterWordAt_disjoint_of_ne p kind
    (sortedOutputRegisterSlot p outputDegree outputDegreeLe sourceSlot)
    observedSlot different
  apply List.map_congr_left
  intro wire observedMember
  unfold writeSortedCopyReference
  apply controlledCopyBasisReference_outside_target
  exact (List.disjoint_left.mp targetDisjointObserved.symm) observedMember

/--
copy元を`Fin K`へ埋め込んだ全slotと異なるwordは、sorted copyの有限fold全体で保存される。
-/
theorem writeSortedCopyReference_fold_read_registerWord_other_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (observedSlot : Fin p.K) (enabled : Bool) :
    ∀ (slots : List (Fin outputDegree))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      (∀ slot ∈ slots,
        sortedOutputRegisterSlot p outputDegree outputDegreeLe slot ≠
          observedSlot) →
      readWires (registerWordAt p (canonicalSortedOutputWires p kind)
          observedSlot)
        (slots.foldl (fun state slot =>
          writeSortedCopyReference p (canonicalSortedOutputWires p kind)
            outputDegree outputDegreeLe enabled slot state) input) =
      readWires (registerWordAt p (canonicalSortedOutputWires p kind)
        observedSlot) input
  | [], _, _ => rfl
  | slot :: slots, input, allDifferent => by
      simp only [List.foldl_cons]
      rw [writeSortedCopyReference_fold_read_registerWord_other_canonical p kind
        outputDegree outputDegreeLe observedSlot enabled slots]
      · exact writeSortedCopyReference_read_registerWord_other_canonical p kind
          outputDegree outputDegreeLe slot observedSlot
          (allDifferent slot (by simp)) enabled input
      · intro tail tailMember
        exact allDifferent tail (by simp [tailMember])

/--
観測slotと異なるslotだけを畳み込むcanonical copy列は、観測wordの読出しを保存する。
-/
theorem writeSortedCopyReference_fold_read_other_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (observedSlot : Fin outputDegree) (enabled : Bool) :
    ∀ (slots : List (Fin outputDegree))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      (∀ slot ∈ slots, slot ≠ observedSlot) →
      readWires (registerWordAt p (canonicalSortedOutputWires p kind)
          (sortedOutputRegisterSlot p outputDegree outputDegreeLe observedSlot))
        (slots.foldl (fun state slot =>
          writeSortedCopyReference p (canonicalSortedOutputWires p kind)
            outputDegree outputDegreeLe enabled slot state) input) =
      readWires (registerWordAt p (canonicalSortedOutputWires p kind)
        (sortedOutputRegisterSlot p outputDegree outputDegreeLe observedSlot)) input
  | [], _, _ => rfl
  | slot :: slots, input, allDifferent => by
      simp only [List.foldl_cons]
      rw [writeSortedCopyReference_fold_read_other_canonical p kind outputDegree
        outputDegreeLe observedSlot enabled slots]
      · exact writeSortedCopyReference_read_other_canonical p kind outputDegree
          outputDegreeLe slot observedSlot (allDifferent slot (by simp)) enabled
          input
      · intro tail tailMember
        exact allDifferent tail (by simp [tailMember])

/-- canonical 出力register外の任意wire列は、sorted copyの有限foldを通して保存される。 -/
theorem writeSortedCopyReference_fold_read_outside_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool)
    (wires : List (Wire p.ancillaWidth p.systemWidth))
    (outside : ∀ wire ∈ wires,
      wire ∉ canonicalSortedOutputWires p kind) :
    ∀ (slots : List (Fin outputDegree))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      readWires wires
        (slots.foldl (fun state slot =>
          writeSortedCopyReference p (canonicalSortedOutputWires p kind)
            outputDegree outputDegreeLe enabled slot state) input) =
      readWires wires input
  | [], _ => rfl
  | slot :: slots, input => by
      simp only [List.foldl_cons]
      rw [writeSortedCopyReference_fold_read_outside_canonical p kind
        outputDegree outputDegreeLe enabled wires outside slots]
      apply List.map_congr_left
      intro wire member
      exact writeSortedCopyReference_outside p
        (canonicalSortedOutputWires p kind) outputDegree outputDegreeLe enabled
        slot input wire (outside wire member)

/--
canonical sorted-data fold後の任意active wordは、対応candidate dataを元のwordへ
bitwise XORした値になる。
-/
theorem writeSortedDataReference_read_word_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (observedSlot : Fin outputDegree)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    let candidateSlot :=
      sortedOutputCandidateSlot p outputDegree outputDegreeLe observedSlot
    let registerSlot :=
      sortedOutputRegisterSlot p outputDegree outputDegreeLe observedSlot
    let source := (candidateWordAt p candidateSlot).take p.wordWidth
    let target := registerWordAt p (canonicalSortedOutputWires p kind) registerSlot
    readWires target
        (writeSortedDataReference p (canonicalSortedOutputWires p kind)
          outputDegree outputDegreeLe true input) =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (readWires source input) (readWires target input) := by
  dsimp only
  let slots := List.finRange outputDegree
  let before := slots.take observedSlot.val
  let after := slots.drop (observedSlot.val + 1)
  let source := (candidateWordAt p
    (sortedOutputCandidateSlot p outputDegree outputDegreeLe observedSlot)).take
      p.wordWidth
  let target := registerWordAt p (canonicalSortedOutputWires p kind)
    (sortedOutputRegisterSlot p outputDegree outputDegreeLe observedSlot)
  have slotAt : slots[observedSlot.val]'(by simp [slots]) = observedSlot := by
    simp [slots]
  have splitSlots : slots = before ++ observedSlot :: after := by
    calc
      slots = slots.take observedSlot.val ++ slots.drop observedSlot.val :=
        (List.take_append_drop observedSlot.val slots).symm
      _ = before ++ slots[observedSlot.val]'(by simp [slots]) :: after := by
        simp only [before, after]
        rw [List.drop_eq_getElem_cons]
      _ = before ++ observedSlot :: after := by rw [slotAt]
  have splitNodup : (before ++ observedSlot :: after).Nodup := by
    rw [← splitSlots]
    exact List.nodup_finRange outputDegree
  have beforeAfterSeparated :
      ∀ left ∈ before, ∀ right ∈ observedSlot :: after, left ≠ right :=
    (List.nodup_append.mp splitNodup).2.2
  have beforeDifferent : ∀ slot ∈ before, slot ≠ observedSlot := by
    intro slot member
    exact beforeAfterSeparated slot member observedSlot (by simp)
  have observedNotAfter : observedSlot ∉ after :=
    (List.nodup_cons.mp (List.nodup_append.mp splitNodup).2.1).1
  have afterDifferent : ∀ slot ∈ after, slot ≠ observedSlot := by
    intro slot member equal
    exact observedNotAfter (equal ▸ member)
  let beforeState := before.foldl (fun state slot =>
    writeSortedCopyReference p (canonicalSortedOutputWires p kind)
      outputDegree outputDegreeLe true slot state) input
  have beforeTarget : readWires target beforeState = readWires target input := by
    exact writeSortedCopyReference_fold_read_other_canonical p kind outputDegree
      outputDegreeLe observedSlot true before input beforeDifferent
  have sourceOutside : ∀ wire ∈ source,
      wire ∉ canonicalSortedOutputWires p kind := by
    intro wire sourceMember outputMember
    have candidateMember : wire ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).candidate).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) :=
      candidateWordAt_mem_candidateSlice p
        (sortedOutputCandidateSlot p outputDegree outputDegreeLe observedSlot)
        (List.mem_of_mem_take sourceMember)
    exact (List.disjoint_left.mp
      (canonicalSortedOutputWires_disjoint_oracleSlice p kind
        (OracleWorkLayout.canonical p).candidate)) outputMember candidateMember
  have beforeSource : readWires source beforeState = readWires source input := by
    exact writeSortedCopyReference_fold_read_outside_canonical p kind
      outputDegree outputDegreeLe true source sourceOutside before input
  let selectedState := writeSortedCopyReference p
    (canonicalSortedOutputWires p kind) outputDegree outputDegreeLe true
      observedSlot beforeState
  have selectedTarget : readWires target selectedState =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (readWires source input) (readWires target input) := by
    rw [show selectedState = writeSortedCopyReference p
        (canonicalSortedOutputWires p kind) outputDegree outputDegreeLe true
          observedSlot beforeState by rfl]
    rw [writeSortedCopyReference_read_own_canonical p kind outputDegree
      outputDegreeLe observedSlot beforeState, beforeSource, beforeTarget]
  have afterTarget :
      readWires target
          (after.foldl (fun state slot =>
            writeSortedCopyReference p (canonicalSortedOutputWires p kind)
              outputDegree outputDegreeLe true slot state) selectedState) =
        readWires target selectedState := by
    exact writeSortedCopyReference_fold_read_other_canonical p kind outputDegree
      outputDegreeLe observedSlot true after selectedState afterDifferent
  unfold writeSortedDataReference
  rw [show List.finRange outputDegree = slots by rfl, splitSlots,
    List.foldl_append]
  simp only [List.foldl_cons]
  exact afterTarget.trans selectedTarget

/-- output次数以降のpadding wordは、canonical sorted-data foldで保存される。 -/
theorem writeSortedDataReference_read_padding_word_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (observedSlot : Fin p.K) (padding : outputDegree ≤ observedSlot.val)
    (enabled : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (registerWordAt p (canonicalSortedOutputWires p kind) observedSlot)
        (writeSortedDataReference p (canonicalSortedOutputWires p kind)
          outputDegree outputDegreeLe enabled input) =
      readWires (registerWordAt p (canonicalSortedOutputWires p kind)
        observedSlot) input := by
  unfold writeSortedDataReference
  apply writeSortedCopyReference_fold_read_registerWord_other_canonical p kind
    outputDegree outputDegreeLe observedSlot enabled (List.finRange outputDegree)
      input
  intro slot _ equal
  have valuesEqual := congrArg Fin.val equal
  simp [sortedOutputRegisterSlot] at valuesEqual
  omega

/--
candidate値がconfigurationのcanonical値なら、sorted-data fold後の各active wordは、
対応site wordを元の出力wordへXORした値になる。
-/
theorem writeSortedDataReference_read_configuration_word_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesEqual : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (slot : Fin configuration.1.card) :
    let registerSlot : Fin p.K :=
      ⟨slot.val, lt_of_lt_of_le slot.isLt configuration.2.2⟩
    let target := registerWordAt p (canonicalSortedOutputWires p kind)
      registerSlot
    readWires target
        (writeSortedDataReference p (canonicalSortedOutputWires p kind)
          configuration.1.card configuration.2.2 true input) =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        (siteWordBits p (configuration.siteAt slot))
        (readWires target input) := by
  dsimp only
  let candidateSlot : Fin p.sortWordCount :=
    ⟨slot.val, lt_of_lt_of_le
      (lt_of_lt_of_le slot.isLt configuration.2.2) p.K_le_sortWordCount⟩
  have candidateRead :
      readWires ((candidateWordAt p candidateSlot).take p.wordWidth) input =
        siteWordBits p (configuration.siteAt slot) := by
    have active : candidateSlot.val < configuration.1.card := slot.isLt
    have result := candidateData_eq_siteWordBits_of_value_eq p configuration input
      valuesEqual candidateSlot active
    simpa [candidateSlot] using result
  have result := writeSortedDataReference_read_word_canonical p kind
    configuration.1.card configuration.2.2 slot input
  simpa [candidateSlot, sortedOutputCandidateSlot,
    sortedOutputRegisterSlot, candidateRead] using result

/-- canonical 出力registerの全wordより後ろにある末尾delimiter wire。 -/
def canonicalSortedOutputFinalWire (p : QParameters)
    (kind : CanonicalSortedOutputKind) :
    Wire p.ancillaWidth p.systemWidth :=
  (canonicalSortedOutputWires p kind).get ⟨p.wordWidth * p.K, by
    rw [canonicalSortedOutputWires_length]
    simp [QParameters.systemWidth]⟩

/-- 末尾delimiter wireは任意の物理word sliceに含まれない。 -/
theorem canonicalSortedOutputFinalWire_not_mem_registerWordAt
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (slot : Fin p.K) :
    canonicalSortedOutputFinalWire p kind ∉
      registerWordAt p (canonicalSortedOutputWires p kind) slot := by
  intro member
  rcases List.mem_iff_getElem.mp member with ⟨bit, bitLt, bitAt⟩
  have bitWidth : bit < p.wordWidth :=
    lt_of_lt_of_le bitLt (List.length_take_le _ _)
  have physicalLt : p.wordWidth * slot.val + bit < p.systemWidth := by
    simp only [QParameters.systemWidth]
    have slotNext : slot.val + 1 ≤ p.K := Nat.succ_le_of_lt slot.isLt
    calc
      p.wordWidth * slot.val + bit < p.wordWidth * slot.val + p.wordWidth :=
        Nat.add_lt_add_left bitWidth _
      _ = (slot.val + 1) * p.wordWidth := by
        rw [Nat.succ_mul, Nat.mul_comm p.wordWidth slot.val]
      _ ≤ p.K * p.wordWidth := Nat.mul_le_mul_right p.wordWidth slotNext
      _ = p.wordWidth * p.K := Nat.mul_comm _ _
      _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _
  have outputLt : p.wordWidth * slot.val + bit <
      (canonicalSortedOutputWires p kind).length := by
    simpa using physicalLt
  have bitAtFull :
      (canonicalSortedOutputWires p kind).get
          ⟨p.wordWidth * slot.val + bit, outputLt⟩ =
        canonicalSortedOutputFinalWire p kind := by
    simpa [registerWordAt, canonicalSortedOutputFinalWire, Nat.mul_comm]
      using bitAt
  have positionsEqual : p.wordWidth * slot.val + bit = p.wordWidth * p.K := by
    exact (List.Nodup.getElem_inj_iff
      (canonicalSortedOutputWires_nodup p kind)).mp bitAtFull
  have wordWidthPositive : 0 < p.wordWidth := by
    simp [QParameters.wordWidth, p.q_pos]
  have quotientEqual := congrArg (fun value => value / p.wordWidth)
    positionsEqual
  have quotientEqual' :
      (p.wordWidth * slot.val + bit) / p.wordWidth =
        p.K * p.wordWidth / p.wordWidth := by
    simpa [Nat.mul_comm] using quotientEqual
  rw [Nat.mul_div_left p.K wordWidthPositive] at quotientEqual'
  have slotValEqual : slot.val = p.K := by
    simpa [Nat.mul_add_div wordWidthPositive, Nat.div_eq_of_lt bitWidth]
      using quotientEqual'
  omega

/-- canonical sorted-data foldは末尾delimiter wireを保存する。 -/
theorem writeSortedDataReference_finalWire_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    writeSortedDataReference p (canonicalSortedOutputWires p kind)
        outputDegree outputDegreeLe enabled input
        (canonicalSortedOutputFinalWire p kind) =
      input (canonicalSortedOutputFinalWire p kind) := by
  unfold writeSortedDataReference
  generalize slotsEq : List.finRange outputDegree = slots
  clear slotsEq
  induction slots generalizing input with
  | nil => rfl
  | cons slot slots inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      unfold writeSortedCopyReference
      apply controlledCopyBasisReference_outside_target
      exact canonicalSortedOutputFinalWire_not_mem_registerWordAt p kind
        (sortedOutputRegisterSlot p outputDegree outputDegreeLe slot)

/-- 無効制御の sorted-use 純粋作用は入力状態を変更しない。 -/
theorem writeSortedUseReference_disabled
    (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    writeSortedUseReference p output outputLength outputActive outputDegree
      outputDegreeLe false input = input := by
  have copiesIdentity : ∀ (slots : List (Fin outputDegree))
      (state : JointBasis p.ancillaWidth p.systemWidth),
      slots.foldl (fun current slot =>
        writeSortedCopyReference p output outputDegree outputDegreeLe false slot
          current) state = state := by
    intro slots state
    induction slots generalizing state with
    | nil => rfl
    | cons slot slots inductionHypothesis =>
        simp only [List.foldl_cons]
        rw [show writeSortedCopyReference p output outputDegree outputDegreeLe
            false slot state = state by
          simp [writeSortedCopyReference]]
        exact inductionHypothesis state
  unfold writeSortedUseReference
  rw [show writeSortedDataReference p output outputDegree outputDegreeLe false
      input = input by
    exact copiesIdentity (List.finRange outputDegree) input]
  unfold toggleOutputIndexReference
  split <;> rfl

/-- degree flag が偽なら、その degree の sorted 参照分岐は恒等作用である。 -/
theorem writeSortedDegreeReference_of_degree_false
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (degreeFalse : input (oracleDegreeWireAt p degreeSlot) = false) :
    writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) degreeSlot degreeChange input = input := by
  simp [writeSortedDegreeReference, degreeFalse,
    writeSortedUseReference_disabled]

/-- 全要素の degree flag が偽なら、任意の有限 degree fold は恒等作用である。 -/
theorem writeSortedDegreeReference_fold_of_degree_false
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeChange : Int) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      (∀ slot ∈ slots, input (oracleDegreeWireAt p slot) = false) →
      slots.foldl (fun state degreeSlot =>
        writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
          (canonicalSortedOutputWires_length p kind)
          (canonicalSortedOutputActive p kind) degreeSlot degreeChange state) input =
        input
  | [], _, _ => rfl
  | slot :: slots, input, allFalse => by
      simp only [List.foldl_cons]
      rw [writeSortedDegreeReference_of_degree_false p kind slot degreeChange input
        (allFalse slot (by simp))]
      exact writeSortedDegreeReference_fold_of_degree_false p kind degreeChange
        slots input (fun tail tailMember => allFalse tail (by simp [tailMember]))

/-- 選択 degree の出力次数が配置次数なら、その一分岐は有効 sorted-use そのものである。 -/
theorem writeSortedDegreeReference_selected_configuration
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (configuration : QConfiguration p)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (outputDegree : Int.ofNat (degreeSlot.val + 1) + degreeChange =
      Int.ofNat configuration.1.card)
    (branchTrue : input (oracleBranchWire p) = true)
    (degreeTrue : input (oracleDegreeWireAt p degreeSlot) = true) :
    writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeSlot degreeChange input =
      writeSortedUseReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) configuration.1.card configuration.2.2
        true input := by
  unfold writeSortedDegreeReference
  have valid : (1 : Int) ≤
        Int.ofNat (degreeSlot.val + 1) + degreeChange ∧
      Int.ofNat (degreeSlot.val + 1) + degreeChange ≤ Int.ofNat p.K := by
    rw [outputDegree]
    constructor
    · exact Int.ofNat_le.mpr configuration.2.1
    · exact Int.ofNat_le.mpr configuration.2.2
  rw [dif_pos valid]
  simp only [branchTrue, degreeTrue, Bool.true_and]
  have toNat :
      (Int.ofNat (degreeSlot.val + 1) + degreeChange).toNat =
        configuration.1.card := by
    rw [outputDegree]
    simp
  congr 1

/-- degree one-hot の全 fold は、唯一選択された degree 分岐だけに厳密に一致する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_eq_selected
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (degreeOneHot : ∀ slot : Fin p.K,
      input (oracleDegreeWireAt p slot) = decide (slot = degreeSlot)) :
    SortedCandidatesDelimiterOutputXorSpec p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeChange input =
      writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeSlot degreeChange input := by
  let slots := List.finRange p.K
  let before := slots.take degreeSlot.val
  let after := slots.drop (degreeSlot.val + 1)
  have slotAt : slots[degreeSlot.val]'(by simp [slots]) =
      degreeSlot := by
    simp [slots]
  have splitSlots : slots = before ++ degreeSlot :: after := by
    calc
      slots = slots.take degreeSlot.val ++ slots.drop degreeSlot.val :=
        (List.take_append_drop degreeSlot.val slots).symm
      _ = before ++
          slots[degreeSlot.val]'(by simp [slots]) :: after := by
        simp only [before, after]
        rw [List.drop_eq_getElem_cons]
      _ = before ++ degreeSlot :: after := by rw [slotAt]
  have splitNodup : (before ++ degreeSlot :: after).Nodup := by
    rw [← splitSlots]
    exact List.nodup_finRange p.K
  have beforeAfterSeparated :
      ∀ left ∈ before, ∀ right ∈ degreeSlot :: after, left ≠ right :=
    (List.nodup_append.mp splitNodup).2.2
  have beforeDifferent : ∀ slot ∈ before, slot ≠ degreeSlot := by
    intro slot member
    exact beforeAfterSeparated slot member degreeSlot (by simp)
  have beforeFalse : ∀ slot ∈ before,
      input (oracleDegreeWireAt p slot) = false := by
    intro slot member
    rw [degreeOneHot slot]
    simp [beforeDifferent slot member]
  have beforeIdentity := writeSortedDegreeReference_fold_of_degree_false p kind
    degreeChange before input beforeFalse
  let selectedState := writeSortedDegreeReference p
    (canonicalSortedOutputWires p kind)
    (canonicalSortedOutputWires_length p kind)
    (canonicalSortedOutputActive p kind) degreeSlot degreeChange input
  have selectedNotAfter : degreeSlot ∉ after :=
    (List.nodup_cons.mp (List.nodup_append.mp splitNodup).2.1).1
  have afterDifferent : ∀ slot ∈ after, slot ≠ degreeSlot := by
    intro slot member equal
    exact selectedNotAfter (equal ▸ member)
  have degreeMember : ∀ slot : Fin p.K,
      oracleDegreeWireAt p slot ∈ writeSortedPairSupport p := by
    intro slot
    simp [writeSortedPairSupport, oracleDegreeWireAt, RegisterSlice.wireList]
  have afterFalse : ∀ slot ∈ after,
      selectedState (oracleDegreeWireAt p slot) = false := by
    intro slot member
    rw [show selectedState (oracleDegreeWireAt p slot) =
        input (oracleDegreeWireAt p slot) by
      exact writeSortedDegreeReference_preserves_pairSupport p kind degreeSlot
        degreeChange input (degreeMember slot)]
    rw [degreeOneHot slot]
    simp [afterDifferent slot member]
  have afterIdentity := writeSortedDegreeReference_fold_of_degree_false p kind
    degreeChange after selectedState afterFalse
  unfold SortedCandidatesDelimiterOutputXorSpec
  rw [show List.finRange p.K = slots by rfl, splitSlots, List.foldl_append,
    beforeIdentity]
  simp only [List.foldl_cons]
  simpa [selectedState] using afterIdentity

/--
degree one-hot と次数整合の下で、sorted writer の純粋全 fold は配置次数の一回の
有効 use へ簡約される。
-/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_eq_configuration_use
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (configuration : QConfiguration p)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (outputDegree : Int.ofNat (degreeSlot.val + 1) + degreeChange =
      Int.ofNat configuration.1.card)
    (branchTrue : input (oracleBranchWire p) = true)
    (degreeOneHot : ∀ slot : Fin p.K,
      input (oracleDegreeWireAt p slot) = decide (slot = degreeSlot)) :
    SortedCandidatesDelimiterOutputXorSpec p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeChange input =
      writeSortedUseReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) configuration.1.card configuration.2.2
        true input := by
  rw [xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_eq_selected p kind degreeSlot degreeChange input
    degreeOneHot]
  apply writeSortedDegreeReference_selected_configuration p kind configuration
    degreeSlot degreeChange input outputDegree branchTrue
  simpa using degreeOneHot degreeSlot

/--
clean な canonical writer の実回路は、degree one-hot と出力次数の一致の下で、
configuration の要素数を選んだ一回の use 参照作用に厳密に一致する。
-/
theorem runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_eq_configuration_use
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (configuration : QConfiguration p)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (outputDegree : Int.ofNat (degreeSlot.val + 1) + degreeChange =
      Int.ofNat configuration.1.card)
    (branchTrue : input (oracleBranchWire p) = true)
    (degreeOneHot : ∀ slot : Fin p.K,
      input (oracleDegreeWireAt p slot) = decide (slot = degreeSlot)) :
    (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) degreeChange).runBasis
        reversibleGatePermutation input =
      writeSortedUseReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) configuration.1.card configuration.2.2
        true input := by
  rw [runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical p kind degreeChange input scratchZero
    pairZero]
  exact xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_eq_configuration_use p kind configuration
    degreeSlot degreeChange input outputDegree branchTrue degreeOneHot

end ReversibleCircuit

end ProbabilityGeneratorQProof
