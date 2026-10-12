import QLean.Generator.Implementation.QOracleDiagonalBranchCorrectness
import QLean.Generator.Implementation.QOracleEventReferenceBridge
import QLean.Generator.Implementation.QEventLayoutBridge
import QLean.Generator.Implementation.QConfigurationCandidateCount
import QLean.Generator.Implementation.CircuitSequenceCorrectness
import QLean.Generator.Implementation.FiniteValueCountUpdate
import QLean.Generator.Implementation.QWriteMovedSelectorLayoutCanonical
import QLean.Generator.Implementation.QWriteSortedConfigurationBridge
import QLean.Generator.Implementation.ReversibleLogicSharedCoreReadoutAdapter

/-!
# Q oracle の row event 分岐の一般基底作用

このファイルは、任意の正の `q,K` と型安全な `slot,offset` について、
`applyRowEventReferenceAndRestoreWorkCircuit` の正本基本ゲート回路を行列展開せずに検証する。
証明は compute--use--uncompute の基底作用、有限 word 列、および
`rowReference` の event 条件だけを用いる。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- row event offset が collision 分岐を指定するかを表す。 -/
def rowEventCollision (offset : Fin 6) : Bool :=
  decide (offset.val % 2 = 1)

/-- row event offset が縦方向を指定するかを表す。 -/
def rowEventVertical (offset : Fin 6) : Bool :=
  decide (4 ≤ offset.val)

/-- row event offset に対応する物理方向。 -/
def rowEventDirection (offset : Fin 6) : QDirection :=
  if offset.val < 4 then .right else .up

/-- row event 分岐の selector 比較回路。 -/
def rowEventSelectorCompute (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  selectorEqualsConstant (rowSelectorWires p) (decoderAndScratchWires p)
    (6 * slot.val + offset.val) (oracleSelectedWire p)

/-- row event 分岐で arrival word を moved work へ複写する回路。 -/
def rowEventMovedCopy (p : QParameters) (slot : Fin p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  xorCopy (registerWordAt p (systemWires p) slot) (oracleMovedWires p)

/-- row event 分岐で arrival から predecessor source へ一歩戻す回路。 -/
def rowEventMoveBackward (p : QParameters) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let coordinate := if 4 ≤ offset.val then
    (oracleMovedWires p).drop p.q |>.take p.q
  else (oracleMovedWires p).take p.q
  decrementWordMod2PowInPlaceCircuit coordinate (decoderAndScratchWires p)

/-- row event 分岐の membership 判定回路。 -/
def rowEventMembership (p : QParameters) (slot : Fin p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  xorMembershipMatchGoodAndAbsentFlagsCircuit p (systemWires p) slot false

/-- row event 分岐の受理 bit を計算する回路。 -/
def rowEventBranchCompute (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let controls := [oracleLegalWire p, oracleSelectedWire p,
    oraclePresentWireAt p slot, oracleAbsentWire p] ++
      if offset.val % 2 = 1 then [oracleDegreeConditionWire p] else []
  positiveMultiControlledX controls (decoderAndScratchWires p)
    (oracleBranchWire p)

/-- collision追加branchの局所slotをdegree one-hot添字へ埋め込む。 -/
def rowEventCollisionDegreeIndex (p : QParameters)
    (degreeSlot : Fin (p.K - 1)) : Fin p.K :=
  ⟨degreeSlot.val, lt_of_lt_of_le degreeSlot.isLt (Nat.sub_le _ _)⟩

/-- collision追加branchの局所slotが書き込むcandidate添字。 -/
def rowEventCollisionCandidateIndex (p : QParameters)
    (degreeSlot : Fin (p.K - 1)) : Fin p.sortWordCount :=
  ⟨degreeSlot.val + 1, by
    have : degreeSlot.val + 1 < p.K := by omega
    exact lt_of_lt_of_le this p.K_le_sortWordCount⟩

/-- collision predecessorの一degree slotに対応するcandidate追加回路。 -/
def controlledUpdateRowCollisionCandidateAtDegreeCircuit (p : QParameters) (degreeSlot : Fin (p.K - 1)) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let degreeIndex := rowEventCollisionDegreeIndex p degreeSlot
  let candidateIndex := rowEventCollisionCandidateIndex p degreeSlot
  let candidate := candidateWordAt p candidateIndex
  let pairFlag := oraclePairWire p
  let pairCompute := positiveMultiControlledX
    [oracleBranchWire p, oracleDegreeWireAt p degreeIndex]
    (decoderAndScratchWires p) pairFlag
  let append := controlledXorCopy pairFlag (oracleMovedWires p)
    (candidate.take p.wordWidth)
  let marker := safeCnot pairFlag (candidateMarkerWire p candidateIndex)
  Circuit.computeUseUncompute id pairCompute <| .seq append marker

/-- collision predecessor用 candidate追加回路。 -/
def controlledUpdateSelectedRowCollisionCandidateWordCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  Circuit.sequence <| (List.finRange (p.K - 1)).map fun degreeSlot =>
    controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot

/-- replacement predecessor 用 candidate 置換回路。 -/
def controlledUpdateSelectedRowReplacementCandidateWordCircuit (p : QParameters) (slot : Fin p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let candidate := candidateWordAt p (slotToSortWord p slot)
  .seq (controlledXorCopy (oracleBranchWire p)
      (registerWordAt p (systemWires p) slot)
      (candidate.take p.wordWidth)) <|
    controlledXorCopy (oracleBranchWire p) (oracleMovedWires p)
      (candidate.take p.wordWidth)

/-- row event 分岐の candidate 変更回路。 -/
def controlledUpdateSelectedRowCandidateWordCircuit (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  if offset.val % 2 = 1 then controlledUpdateSelectedRowCollisionCandidateWordCircuit p
  else controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot

/-- row event 分岐の compute 部分全体。 -/
def computeRowEventPredecessorCandidateUpdateAndSortCircuit (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .seq (rowEventSelectorCompute p slot offset) <|
    .seq (rowEventMovedCopy p slot) <|
    .seq (rowEventMoveBackward p offset) <|
    .seq (rowEventMembership p slot) <|
    .seq (rowEventBranchCompute p slot offset) <|
    .seq (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)) <|
    .seq (controlledUpdateSelectedRowCandidateWordCircuit p slot offset) (reversiblySortCandidateWordsAndRestoreHistoryCircuit p)

/-- row event 分岐の use 部分全体。 -/
def xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit (p : QParameters) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .seq (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (columnKeyWires p)
      (by simp [columnKeyWires]) (keySignalWire p)
      (if offset.val % 2 = 1 then 1 else 0)) <|
    xorMovedMemberPositionIntoSelectorOutputCircuit p offset.val (columnSelectorWires p)

/-- 正本 row event AST は、明示した compute と use の C-U-U 合成である。 -/
theorem applyRowEventReferenceAndRestoreWorkCircuit_eq_computeUseUncompute
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    applyRowEventReferenceAndRestoreWorkCircuit p slot offset =
      Circuit.computeUseUncompute id (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset)
        (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset) := by
  rfl

/-- row event compute の各段階を保持する行列非展開な状態記録。 -/
structure RowEventComputedStates (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) where
  /-- selector 比較直後の状態。 -/
  afterSelector : JointBasis p.ancillaWidth p.systemWidth
  /-- arrival 複写直後の状態。 -/
  afterMovedCopy : JointBasis p.ancillaWidth p.systemWidth
  /-- predecessor source への逆移動直後の状態。 -/
  afterMoveBackward : JointBasis p.ancillaWidth p.systemWidth
  /-- membership 判定直後の状態。 -/
  afterMembership : JointBasis p.ancillaWidth p.systemWidth
  /-- branch bit 計算直後の状態。 -/
  afterBranch : JointBasis p.ancillaWidth p.systemWidth
  /-- candidate 準備直後の状態。 -/
  afterCandidates : JointBasis p.ancillaWidth p.systemWidth
  /-- candidate 追加または置換直後の状態。 -/
  afterModify : JointBasis p.ancillaWidth p.systemWidth
  /-- bitonic sort 直後、すなわち compute 完了時の状態。 -/
  output : JointBasis p.ancillaWidth p.systemWidth
  /-- selector 段階は正本回路の基底作用である。 -/
  selector_eq : afterSelector =
    (rowEventSelectorCompute p slot offset).runBasis
      reversibleGatePermutation input
  /-- arrival 複写段階は正本回路の基底作用である。 -/
  moved_eq : afterMovedCopy =
    (rowEventMovedCopy p slot).runBasis reversibleGatePermutation afterSelector
  /-- 逆移動段階は正本回路の基底作用である。 -/
  moveBackward_eq : afterMoveBackward =
    (rowEventMoveBackward p offset).runBasis
      reversibleGatePermutation afterMovedCopy
  /-- membership 段階は正本回路の基底作用である。 -/
  membership_eq : afterMembership =
    (rowEventMembership p slot).runBasis
      reversibleGatePermutation afterMoveBackward
  /-- branch 段階は正本回路の基底作用である。 -/
  branch_eq : afterBranch =
    (rowEventBranchCompute p slot offset).runBasis
      reversibleGatePermutation afterMembership
  /-- candidate 準備段階は正本回路の基底作用である。 -/
  candidates_eq : afterCandidates =
    (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
      reversibleGatePermutation afterBranch
  /-- candidate 変更段階は正本回路の基底作用である。 -/
  modify_eq : afterModify =
    (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis
      reversibleGatePermutation afterCandidates
  /-- sort 段階は正本回路の基底作用である。 -/
  sort_eq : output =
    (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
      reversibleGatePermutation afterModify

/-- 任意の基底入力に対する row event compute の正本状態記録。 -/
def rowEventPredecessorCandidateUpdateAndSortExecutionTrace (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    RowEventComputedStates p slot offset input := by
  let afterSelector := (rowEventSelectorCompute p slot offset).runBasis
    reversibleGatePermutation input
  let afterMovedCopy := (rowEventMovedCopy p slot).runBasis
    reversibleGatePermutation afterSelector
  let afterMoveBackward := (rowEventMoveBackward p offset).runBasis
    reversibleGatePermutation afterMovedCopy
  let afterMembership := (rowEventMembership p slot).runBasis
    reversibleGatePermutation afterMoveBackward
  let afterBranch := (rowEventBranchCompute p slot offset).runBasis
    reversibleGatePermutation afterMembership
  let afterCandidates := (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
    reversibleGatePermutation afterBranch
  let afterModify := (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis
    reversibleGatePermutation afterCandidates
  let output := (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
    reversibleGatePermutation afterModify
  exact {
    afterSelector := afterSelector
    afterMovedCopy := afterMovedCopy
    afterMoveBackward := afterMoveBackward
    afterMembership := afterMembership
    afterBranch := afterBranch
    afterCandidates := afterCandidates
    afterModify := afterModify
    output := output
    selector_eq := rfl
    moved_eq := rfl
    moveBackward_eq := rfl
    membership_eq := rfl
    branch_eq := rfl
    candidates_eq := rfl
    modify_eq := rfl
    sort_eq := rfl }

/-- 状態記録の最終状態は row event compute 正本回路の実行結果に等しい。 -/
theorem rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output =
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis
        reversibleGatePermutation input := by
  rfl

/-- branch wireは任意candidate data wordの外にある。 -/
theorem oracleBranchWire_not_mem_candidateData
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

/-- branch wireはmoved wordの外にある。 -/
theorem oracleBranchWire_not_mem_oracleMovedWires (p : QParameters) :
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

/-- moved wordと任意candidate data wordは交わらない。 -/
theorem oracleMovedWires_disjoint_candidateData
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

/-- system slot wordと任意candidate data wordは交わらない。 -/
theorem systemRegisterWord_disjoint_candidateData
    (p : QParameters) (slot : Fin p.K) (word : Fin p.sortWordCount) :
    (registerWordAt p (systemWires p) slot).Disjoint
      ((candidateWordAt p word).take p.wordWidth) := by
  rw [List.disjoint_left]
  intro wire systemMember candidateMember
  have systemFull : wire ∈ systemWires p :=
    mem_register_of_mem_registerWordAt p (systemWires p) slot systemMember
  have candidateFull : wire ∈
      ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
    candidateWordAt_mem_candidateSlice p word
      (List.mem_of_mem_take candidateMember)
  exact (List.disjoint_left.mp
    (systemWires_candidateInputLayout p).disjoint_candidate)
      systemFull candidateFull

/-- 任意candidate wordはsorted pair計算supportと交わらない。 -/
theorem candidateWordAt_disjoint_writeSortedPairSupport
    (p : QParameters) (word : Fin p.sortWordCount) :
    (candidateWordAt p word).Disjoint (writeSortedPairSupport p) := by
  let candidateSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  let degreeSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
  let branchSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).branch
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  let pairSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).pair
  have degreeCandidate :
      (degreeSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [degreeSlice, candidateSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have candidateBranch :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [candidateSlice, branchSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have candidateAnd :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [candidateSlice, andSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have candidatePair :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [candidateSlice, pairSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  rw [List.disjoint_left]
  intro wire candidateMember supportMember
  have candidateFull : wire ∈
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    candidateWordAt_mem_candidateSlice p word candidateMember
  unfold writeSortedPairSupport at supportMember
  rcases List.mem_append.mp supportMember with supportMember | pairMember
  · rcases List.mem_append.mp supportMember with supportMember | andMember
    · rcases List.mem_append.mp supportMember with branchMember | degreeMember
      · exact (List.disjoint_left.mp candidateBranch) candidateFull branchMember
      · exact (List.disjoint_left.mp degreeCandidate) degreeMember candidateFull
    · exact (List.disjoint_left.mp candidateAnd) candidateFull andMember
  · exact (List.disjoint_left.mp candidatePair) candidateFull pairMember

/-- pair flagはmoved wordの外にある。 -/
theorem oraclePairWire_not_mem_oracleMovedWires (p : QParameters) :
    oraclePairWire p ∉ oracleMovedWires p := by
  let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
  let pairSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).pair
  have separated :
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [movedSlice, pairSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  intro movedMember
  have movedFull : oraclePairWire p ∈
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using movedMember
  have pairMember : oraclePairWire p ∈
      (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change pairSlice.ancillaWire ⟨0, by
      simpa [QParameters.pairWidth] using p.K_pos⟩ ∈ _
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨⟨0, by
      simpa [QParameters.pairWidth] using p.K_pos⟩,
      List.mem_finRange _, rfl⟩
  exact (List.disjoint_left.mp separated) movedFull pairMember

/-- 一つのcollision slotが有効なときの、pair復元後candidate追加参照作用。 -/
def rowEventCollisionAppendReference (p : QParameters)
    (degreeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let candidateIndex := rowEventCollisionCandidateIndex p degreeSlot
  let candidateData := (candidateWordAt p candidateIndex).take p.wordWidth
  xBasisAction (candidateMarkerWire p candidateIndex)
    (controlledCopyBasisReference true (oracleMovedWires p) candidateData input)

/-- collision追加参照作用はpair計算support上の全wireを保存する。 -/
theorem rowEventCollisionAppendReference_preserves_pairSupport
    (p : QParameters) (degreeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    BasisAgreeOn (writeSortedPairSupport p)
      (rowEventCollisionAppendReference p degreeSlot input) input := by
  let candidateIndex := rowEventCollisionCandidateIndex p degreeSlot
  let candidateData := (candidateWordAt p candidateIndex).take p.wordWidth
  let marker := candidateMarkerWire p candidateIndex
  have candidateDisjoint :=
    candidateWordAt_disjoint_writeSortedPairSupport p candidateIndex
  intro wire supportMember
  have dataOutside : wire ∉ candidateData := by
    intro dataMember
    exact (List.disjoint_left.mp candidateDisjoint)
      (List.mem_of_mem_take dataMember) supportMember
  have markerOutside : wire ≠ marker := by
    intro equal
    subst wire
    exact (List.disjoint_left.mp candidateDisjoint)
      (by simp [marker, candidateMarkerWire, candidateWordAt]) supportMember
  unfold rowEventCollisionAppendReference
  rw [xBasisAction_other marker wire markerOutside]
  exact controlledCopyBasisReference_outside_target true (oracleMovedWires p)
    candidateData input wire dataOutside

/--
branch・degreeが有効でpair/scratchがcleanなら、一collision slotの実C-U-U回路は
candidate dataへmoved wordをXORしmarkerを反転した参照状態に厳密一致する。
-/
theorem runBasis_rowEventCollisionModifyAt_active
    (p : QParameters) (degreeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (branchTrue : input (oracleBranchWire p) = true)
    (degreeTrue : input
      (oracleDegreeWireAt p (rowEventCollisionDegreeIndex p degreeSlot)) = true) :
    (controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot).runBasis
        reversibleGatePermutation input =
      rowEventCollisionAppendReference p degreeSlot input := by
  let degreeIndex := rowEventCollisionDegreeIndex p degreeSlot
  let candidateIndex := rowEventCollisionCandidateIndex p degreeSlot
  let candidateData := (candidateWordAt p candidateIndex).take p.wordWidth
  let marker := candidateMarkerWire p candidateIndex
  let pair := oraclePairWire p
  let compute := writeSortedPairComputeCircuit p degreeIndex
  let use : Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
    .seq (controlledXorCopy pair (oracleMovedWires p) candidateData)
      (safeCnot pair marker)
  let output := rowEventCollisionAppendReference p degreeSlot input
  let computed := compute.runBasis reversibleGatePermutation input
  let appended := (controlledXorCopy pair (oracleMovedWires p) candidateData).runBasis
    reversibleGatePermutation computed
  have computedEq : computed = xBasisAction pair input := by
    have result := runBasis_writeSortedPairComputeCircuit_canonical p degreeIndex input
      scratchZero pairZero
    rw [branchTrue, degreeTrue] at result
    simpa [computed, compute, degreeIndex, pair] using result
  have pairAbsentCandidate : pair ∉ candidateData := by
    intro member
    exact oraclePairWire_not_mem_candidateSlice p
      (candidateWordAt_mem_candidateSlice p candidateIndex
        (List.mem_of_mem_take member))
  have pairAbsentMoved : pair ∉ oracleMovedWires p :=
    oraclePairWire_not_mem_oracleMovedWires p
  have movedDisjoint : (oracleMovedWires p).Disjoint candidateData :=
    oracleMovedWires_disjoint_candidateData p candidateIndex
  have sameLength : (oracleMovedWires p).length = candidateData.length := by
    simp [oracleMovedWires, QParameters.movedWidth, candidateData]
  have candidateNodup : candidateData.Nodup :=
    (candidateWordAt_nodup p candidateIndex).take
  have movedNodup : (oracleMovedWires p).Nodup := by
    let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
    simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using
      (RegisterSlice.wireList_nodup (systemWidth := p.systemWidth) movedSlice)
  have appendedEq : appended =
      xBasisAction pair
        (controlledCopyBasisReference true (oracleMovedWires p) candidateData input) := by
    rw [show appended = controlledCopyBasisReference (computed pair)
          (oracleMovedWires p) candidateData computed by
      exact runBasis_validatedControlledXorCopyLists_eq_controlledCopyBasisReference pair
        (oracleMovedWires p) candidateData computed movedNodup candidateNodup
        sameLength movedDisjoint pairAbsentMoved pairAbsentCandidate]
    have computedPair : computed pair = true := by
      rw [computedEq, xBasisAction_target]
      have pairZero' : input pair = false := by simpa [pair] using pairZero
      rw [pairZero']
      rfl
    rw [computedPair, computedEq]
    exact controlledCopyBasisReference_x_outside true (oracleMovedWires p)
      candidateData input pair movedNodup candidateNodup sameLength movedDisjoint
      pairAbsentMoved pairAbsentCandidate
  have appendedPair : appended pair = true := by
    rw [appendedEq, xBasisAction_target]
    rw [controlledCopyBasisReference_outside_target true (oracleMovedWires p)
      candidateData input pair pairAbsentCandidate]
    have pairZero' : input pair = false := by simpa [pair] using pairZero
    rw [pairZero']
    rfl
  have pairNeMarker : pair ≠ marker := by
    intro equal
    apply oraclePairWire_not_mem_candidateSlice p
    rw [show oraclePairWire p = marker by simpa [pair] using equal]
    exact candidateMarkerWire_mem_candidateSlice p candidateIndex
  have usedEq : use.runBasis reversibleGatePermutation computed =
      xBasisAction pair output := by
    rw [show use.runBasis reversibleGatePermutation computed =
        (safeCnot pair marker).runBasis reversibleGatePermutation appended by rfl]
    rw [runBasis_safeCnot pair marker pairNeMarker]
    have cnotEq : cnotBasisAction pair marker appended =
        xBasisAction marker appended := by
      funext wire
      simp [cnotBasisAction, xBasisAction, appendedPair]
    rw [cnotEq, appendedEq]
    simpa [output, rowEventCollisionAppendReference, candidateIndex, candidateData,
      marker] using xBasisAction_commute marker pair pairNeMarker.symm
        (controlledCopyBasisReference true (oracleMovedWires p) candidateData input)
  have outputPreserves : BasisAgreeOn (writeSortedPairSupport p) output input := by
    simpa [output] using
      rowEventCollisionAppendReference_preserves_pairSupport p degreeSlot input
  have outputScratch : ∀ wire ∈ decoderAndScratchWires p,
      output wire = false := by
    intro wire member
    rw [outputPreserves wire (decoderAndScratchWire_mem_writeSortedPairSupport p member)]
    exact scratchZero wire member
  have outputPair : output pair = false := by
    rw [outputPreserves pair (oraclePairWire_mem_writeSortedPairSupport p)]
    exact pairZero
  have outputBranch : output (oracleBranchWire p) = true := by
    rw [outputPreserves (oracleBranchWire p) (by
      simp [writeSortedPairSupport, oracleBranchWire, oracleSingletonWire,
        RegisterSlice.wireList])]
    exact branchTrue
  have outputDegree : output (oracleDegreeWireAt p degreeIndex) = true := by
    rw [outputPreserves (oracleDegreeWireAt p degreeIndex) (by
      simp [writeSortedPairSupport, oracleDegreeWireAt, RegisterSlice.wireList])]
    exact degreeTrue
  have computeOutputEq : compute.runBasis reversibleGatePermutation output =
      xBasisAction pair output := by
    have result := runBasis_writeSortedPairComputeCircuit_canonical p degreeIndex output
      outputScratch outputPair
    rw [outputBranch, outputDegree] at result
    simpa [compute, degreeIndex, pair] using result
  change (Circuit.computeUseUncompute id compute use).runBasis
      reversibleGatePermutation input = output
  apply Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl) compute use input output
  change use.runBasis reversibleGatePermutation computed =
    compute.runBasis reversibleGatePermutation output
  rw [usedEq, computeOutputEq]

/--
branch または対応 degree が偽で、pair と scratch が clean なら、
一つの collision 追加 slot は基底状態全体を恒等に保つ。
-/
theorem runBasis_rowEventCollisionModifyAt_inactive
    (p : QParameters) (degreeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (inactive : input (oracleBranchWire p) = false ∨
      input (oracleDegreeWireAt p
        (rowEventCollisionDegreeIndex p degreeSlot)) = false) :
    (controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot).runBasis
        reversibleGatePermutation input = input := by
  let degreeIndex := rowEventCollisionDegreeIndex p degreeSlot
  let candidateIndex := rowEventCollisionCandidateIndex p degreeSlot
  let candidateData := (candidateWordAt p candidateIndex).take p.wordWidth
  let marker := candidateMarkerWire p candidateIndex
  let pair := oraclePairWire p
  let compute := writeSortedPairComputeCircuit p degreeIndex
  let use : Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
    .seq (controlledXorCopy pair (oracleMovedWires p) candidateData)
      (safeCnot pair marker)
  have computedEq : compute.runBasis reversibleGatePermutation input = input := by
    have result := runBasis_writeSortedPairComputeCircuit_canonical p degreeIndex
      input scratchZero pairZero
    rcases inactive with branchFalse | degreeFalse
    · rw [branchFalse] at result
      simpa [compute, degreeIndex] using result
    · rw [degreeFalse] at result
      simpa [compute, degreeIndex] using result
  have pairAbsentCandidate : pair ∉ candidateData := by
    intro member
    exact oraclePairWire_not_mem_candidateSlice p
      (candidateWordAt_mem_candidateSlice p candidateIndex
        (List.mem_of_mem_take member))
  have pairAbsentMoved : pair ∉ oracleMovedWires p :=
    oraclePairWire_not_mem_oracleMovedWires p
  have movedDisjoint : (oracleMovedWires p).Disjoint candidateData :=
    oracleMovedWires_disjoint_candidateData p candidateIndex
  have sameLength : (oracleMovedWires p).length = candidateData.length := by
    simp [oracleMovedWires, QParameters.movedWidth, candidateData]
  have candidateNodup : candidateData.Nodup :=
    (candidateWordAt_nodup p candidateIndex).take
  have movedNodup : (oracleMovedWires p).Nodup := by
    let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
    simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using
      (RegisterSlice.wireList_nodup (systemWidth := p.systemWidth) movedSlice)
  have pairNeMarker : pair ≠ marker := by
    intro equal
    apply oraclePairWire_not_mem_candidateSlice p
    rw [show oraclePairWire p = marker by simpa [pair] using equal]
    exact candidateMarkerWire_mem_candidateSlice p candidateIndex
  have copyEq :
      (controlledXorCopy pair (oracleMovedWires p) candidateData).runBasis
          reversibleGatePermutation input = input := by
    have pairZero' : input pair = false := by simpa [pair] using pairZero
    exact runBasis_validatedControlledXorCopyLists_of_control_false pair
      (oracleMovedWires p) candidateData input movedNodup candidateNodup
      sameLength movedDisjoint pairAbsentMoved pairAbsentCandidate pairZero'
  have useEq : use.runBasis reversibleGatePermutation input = input := by
    change (safeCnot pair marker).runBasis reversibleGatePermutation
      ((controlledXorCopy pair (oracleMovedWires p) candidateData).runBasis
        reversibleGatePermutation input) = input
    rw [copyEq, runBasis_safeCnot pair marker pairNeMarker]
    funext wire
    simp [cnotBasisAction, pairZero, pair]
  change (Circuit.computeUseUncompute id compute use).runBasis
      reversibleGatePermutation input = input
  apply Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl) compute use input input
  change use.runBasis reversibleGatePermutation
      (compute.runBasis reversibleGatePermutation input) =
    compute.runBasis reversibleGatePermutation input
  rw [computedEq, useEq]

/--
添字が重複しない回路列で一つの添字だけが active なら、他の回路が active の
前後の状態を保つことから、列全体の作用は active 回路の作用だけに一致する。
-/
theorem runBasis_sequence_map_eq_of_unique_active
    {Gate basis index : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (indices : List index) (circuitAt : index → Circuit Gate)
    (activeIndex : index) (input output : basis)
    (indicesNodup : indices.Nodup) (activeMember : activeIndex ∈ indices)
    (inactiveInput : ∀ index ∈ indices, index ≠ activeIndex →
      (circuitAt index).runBasis gatePermutation input = input)
    (activeResult : (circuitAt activeIndex).runBasis gatePermutation input = output)
    (inactiveOutput : ∀ index ∈ indices, index ≠ activeIndex →
      (circuitAt index).runBasis gatePermutation output = output) :
    (Circuit.sequence (indices.map circuitAt)).runBasis gatePermutation input =
      output := by
  classical
  induction indices with
  | nil => simp at activeMember
  | cons index rest inductionHypothesis =>
      have restNodup := indicesNodup.tail
      change (Circuit.sequence (rest.map circuitAt)).runBasis gatePermutation
          ((circuitAt index).runBasis gatePermutation input) = output
      by_cases isActive : index = activeIndex
      · subst index
        rw [activeResult]
        apply Circuit.runBasis_sequence_eq_input_of_each gatePermutation
          (rest.map circuitAt) output
        intro circuit circuitMember
        obtain ⟨restIndex, restMember, rfl⟩ := List.mem_map.mp circuitMember
        apply inactiveOutput restIndex (by simp [restMember])
        intro equal
        subst restIndex
        exact (List.nodup_cons.mp indicesNodup).1 restMember
      · rw [inactiveInput index (by simp) isActive]
        have activeInRest : activeIndex ∈ rest := by
          have split := List.mem_cons.mp activeMember
          cases split with
          | inl headEqual => exact (isActive headEqual.symm).elim
          | inr tailMember => exact tailMember
        exact inductionHypothesis restNodup activeInRest (by
          intro restIndex restMember different
          exact inactiveInput restIndex (by simp [restMember]) different) (by
          intro restIndex restMember different
          exact inactiveOutput restIndex (by simp [restMember]) different)

/--
degree one-hot が `activeSlot` を指すとき、collision 追加列全体はその一つの
slot だけに moved word を追加する純粋基底作用と厳密に一致する。
-/
theorem runBasis_rowEventCollisionModify_active
    (p : QParameters) (activeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (branchTrue : input (oracleBranchWire p) = true)
    (activeDegree : input (oracleDegreeWireAt p
      (rowEventCollisionDegreeIndex p activeSlot)) = true)
    (otherDegree : ∀ degreeSlot : Fin (p.K - 1), degreeSlot ≠ activeSlot →
      input (oracleDegreeWireAt p
        (rowEventCollisionDegreeIndex p degreeSlot)) = false) :
    (controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis reversibleGatePermutation input =
      rowEventCollisionAppendReference p activeSlot input := by
  let output := rowEventCollisionAppendReference p activeSlot input
  have outputPreserves : BasisAgreeOn (writeSortedPairSupport p) output input := by
    simpa [output] using
      rowEventCollisionAppendReference_preserves_pairSupport p activeSlot input
  have outputScratch : ∀ wire ∈ decoderAndScratchWires p,
      output wire = false := by
    intro wire member
    rw [outputPreserves wire
      (decoderAndScratchWire_mem_writeSortedPairSupport p member)]
    exact scratchZero wire member
  have outputPair : output (oraclePairWire p) = false := by
    rw [outputPreserves (oraclePairWire p)
      (oraclePairWire_mem_writeSortedPairSupport p)]
    exact pairZero
  have outputOtherDegree : ∀ degreeSlot : Fin (p.K - 1),
      degreeSlot ≠ activeSlot →
      output (oracleDegreeWireAt p
        (rowEventCollisionDegreeIndex p degreeSlot)) = false := by
    intro degreeSlot different
    rw [outputPreserves (oracleDegreeWireAt p
      (rowEventCollisionDegreeIndex p degreeSlot)) (by
        simp [writeSortedPairSupport, oracleDegreeWireAt,
          RegisterSlice.wireList])]
    exact otherDegree degreeSlot different
  have activeResult :
      (controlledUpdateRowCollisionCandidateAtDegreeCircuit p activeSlot).runBasis
          reversibleGatePermutation input = output := by
    simpa [output] using runBasis_rowEventCollisionModifyAt_active p activeSlot input
      scratchZero pairZero branchTrue activeDegree
  have sequenceResult := runBasis_sequence_map_eq_of_unique_active
    reversibleGatePermutation (List.finRange (p.K - 1))
    (controlledUpdateRowCollisionCandidateAtDegreeCircuit p) activeSlot input output
    (List.nodup_finRange (p.K - 1)) (List.mem_finRange activeSlot) (by
      intro degreeSlot degreeMember different
      exact runBasis_rowEventCollisionModifyAt_inactive p degreeSlot input
        scratchZero pairZero (Or.inr (otherDegree degreeSlot different)))
    activeResult (by
      intro degreeSlot degreeMember different
      exact runBasis_rowEventCollisionModifyAt_inactive p degreeSlot output
        outputScratch outputPair
        (Or.inr (outputOtherDegree degreeSlot different)))
  simpa [controlledUpdateSelectedRowCollisionCandidateWordCircuit, output] using sequenceResult

/--
collision 追加参照作用は、指定した最初の padding candidate を source site値へ
置き換え、他の candidate 自然数をすべて保存する。
-/
theorem qCandidateValue_rowEventCollisionAppendReference
    (p : QParameters) (configuration : QConfiguration p) (source : QSite p)
    (activeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (movedRead : readWires (oracleMovedWires p) input = siteWordBits p source)
    (candidateDataZero : readWires
      ((candidateWordAt p
        (rowEventCollisionCandidateIndex p activeSlot)).take p.wordWidth) input =
      List.replicate p.wordWidth false)
    (candidateMarkerOne : input (candidateMarkerWire p
      (rowEventCollisionCandidateIndex p activeSlot)) = true) :
    qCandidateValue p
        (rowEventCollisionAppendReference p activeSlot input) =
      fun word =>
        if word = rowEventCollisionCandidateIndex p activeSlot then source.val
        else configurationCandidateValue p configuration word := by
  let selected := rowEventCollisionCandidateIndex p activeSlot
  let candidateData := (candidateWordAt p selected).take p.wordWidth
  let marker := candidateMarkerWire p selected
  let output := rowEventCollisionAppendReference p activeSlot input
  have sameLength : (oracleMovedWires p).length = candidateData.length := by
    simp [oracleMovedWires, QParameters.movedWidth, candidateData]
  have movedDisjoint : (oracleMovedWires p).Disjoint candidateData :=
    oracleMovedWires_disjoint_candidateData p selected
  have candidateNodup : candidateData.Nodup :=
    (candidateWordAt_nodup p selected).take
  have movedNodup : (oracleMovedWires p).Nodup := by
    let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
    simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using
      (RegisterSlice.wireList_nodup
        (systemWidth := p.systemWidth) movedSlice)
  let copyLayout := ValidatedRegisterXorCopyLayout.ofLists
    (oracleMovedWires p) candidateData movedNodup
    candidateNodup sameLength movedDisjoint
  have markerAbsentData : marker ∉ candidateData := by
    simpa [marker, candidateData] using candidateMarkerWire_not_mem_data p selected
  have targetRead : readWires candidateData output = siteWordBits p source := by
    change readWires candidateData
      (xBasisAction marker
        (controlledCopyBasisReference true (oracleMovedWires p)
          candidateData input)) = siteWordBits p source
    rw [readWires_xBasisAction_of_not_mem candidateData marker _ markerAbsentData]
    rw [show controlledCopyBasisReference true (oracleMovedWires p)
        candidateData input = copyLayout.basisAction input by
      simp only [controlledCopyBasisReference, if_true]
      simpa [copyLayout] using
        copyLayout.xorCopyStage_reference_eq_basisAction input]
    rw [show readWires candidateData (copyLayout.basisAction input) =
        List.zipWith
          (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
          (readWires (oracleMovedWires p) input)
          (readWires candidateData input) by
      simpa [copyLayout] using
        readWires_validatedRegisterXorCopyBasisAction_target copyLayout input]
    rw [movedRead]
    have zeroRead : readWires candidateData input =
        List.replicate p.wordWidth false := by
      simpa [candidateData, selected] using candidateDataZero
    rw [zeroRead]
    have sourceLength : (siteWordBits p source).length = p.wordWidth := by
      simp [siteWordBits, QParameters.wordWidth]
    rw [← sourceLength]
    exact candidateZipWithXorFalse (siteWordBits p source)
  have markerRead : output marker = false := by
    change xBasisAction marker
      (controlledCopyBasisReference true (oracleMovedWires p)
        candidateData input) marker = false
    rw [xBasisAction_target]
    rw [controlledCopyBasisReference_outside_target true (oracleMovedWires p)
      candidateData input marker markerAbsentData]
    have markerOne : input marker = true := by
      simpa [marker, selected] using candidateMarkerOne
    rw [markerOne]
    rfl
  funext word
  by_cases isSelected : word = selected
  · subst word
    rw [if_pos rfl]
    rw [qCandidateValue_eq_of_data_marker p output selected
      (siteWordBits p source) false targetRead markerRead]
    simp [littleEndianNat_append, littleEndianNat_siteWordBits, littleEndianNat]
  · rw [if_neg isSelected]
    have wordRead : readWires (candidateWordAt p word) output =
        readWires (candidateWordAt p word) input := by
      apply List.map_congr_left
      intro wire wordMember
      have wordsDisjoint := candidateWordAt_disjoint_of_ne p word selected isSelected
      have dataOutside : wire ∉ candidateData := by
        intro dataMember
        exact (List.disjoint_left.mp wordsDisjoint) wordMember
          (List.mem_of_mem_take dataMember)
      have markerDifferent : wire ≠ marker := by
        intro equal
        subst wire
        exact (List.disjoint_left.mp wordsDisjoint) wordMember
          (by simp [marker, candidateMarkerWire, candidateWordAt])
      change xBasisAction marker
          (controlledCopyBasisReference true (oracleMovedWires p)
            candidateData input) wire = input wire
      rw [xBasisAction_other marker wire markerDifferent]
      exact controlledCopyBasisReference_outside_target true
        (oracleMovedWires p) candidateData input wire dataOutside
    unfold qCandidateValue
    rw [wordRead]
    exact congrFun valuesBefore word

/--
一candidate wordの自然数値がpadding marker値 `2^wordWidth` なら、そのbit表現は
data全0とmarker 1に一意に決まる。
-/
theorem candidateDataMarker_of_qCandidateValue_eq_marker
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (word : Fin p.sortWordCount)
    (valueAt : qCandidateValue p input word = 2 ^ p.wordWidth) :
    readWires ((candidateWordAt p word).take p.wordWidth) input =
        List.replicate p.wordWidth false ∧
      input (candidateMarkerWire p word) = true := by
  let fullBits := readWires (candidateWordAt p word) input
  let markerBits := List.replicate p.wordWidth false ++ [true]
  have sameLength : fullBits.length = markerBits.length := by
    simp [fullBits, markerBits, readWires]
  have markerValue : littleEndianNat markerBits = 2 ^ p.wordWidth := by
    simp [markerBits, littleEndianNat_append, littleEndianNat]
  have sameValue : littleEndianNat fullBits = littleEndianNat markerBits := by
    exact valueAt.trans markerValue.symm
  have fullEqual : fullBits = markerBits :=
    littleEndianNat_injective_of_length_eq fullBits markerBits sameLength sameValue
  have splitFull : fullBits =
      readWires ((candidateWordAt p word).take p.wordWidth) input ++
        [input (candidateMarkerWire p word)] := by
    unfold fullBits
    rw [candidateWordAt_eq_data_append_marker p word]
    simp [readWires]
  rw [splitFull] at fullEqual
  have dataEqual := congrArg (List.take p.wordWidth) fullEqual
  have dataLength :
      (readWires ((candidateWordAt p word).take p.wordWidth) input).length =
        p.wordWidth := by simp [readWires]
  have dataEqual' :
      readWires ((candidateWordAt p word).take p.wordWidth) input =
        List.replicate p.wordWidth false := by
    simpa [markerBits, dataLength, readWires] using dataEqual
  constructor
  · exact dataEqual'
  · rw [dataEqual'] at fullEqual
    simpa [markerBits] using fullEqual

/--
collision の逆向き追加参照作用後の candidate 多重集合は、任意の自然数値について
元の predecessor 配置の canonical candidate 多重集合と一致する。
-/
theorem rowEventCollisionAppendReference_preserves_predecessor_valueCount
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (collision : moveSite source direction ∈ configuration.1.erase source)
    (activeSlot : Fin (p.K - 1))
    (slotAtBoundary : activeSlot.val + 1 =
      (eventOutput configuration source direction).1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p
        (eventOutput configuration source direction))
    (movedRead : readWires (oracleMovedWires p) input = siteWordBits p source)
    (candidateDataZero : readWires
      ((candidateWordAt p
        (rowEventCollisionCandidateIndex p activeSlot)).take p.wordWidth) input =
      List.replicate p.wordWidth false)
    (candidateMarkerOne : input (candidateMarkerWire p
      (rowEventCollisionCandidateIndex p activeSlot)) = true)
    (target : Nat) :
    finiteValueCount target
        (qCandidateValue p
          (rowEventCollisionAppendReference p activeSlot input)) =
      finiteValueCount target
        (configurationCandidateValue p configuration) := by
  let outputConfiguration := eventOutput configuration source direction
  let selected := rowEventCollisionCandidateIndex p activeSlot
  have actualValues := qCandidateValue_rowEventCollisionAppendReference p
    outputConfiguration source activeSlot input valuesBefore movedRead
    candidateDataZero candidateMarkerOne
  rw [actualValues]
  have selectedValue : selected.val = outputConfiguration.1.card := by
    simpa [selected, rowEventCollisionCandidateIndex, outputConfiguration] using
      slotAtBoundary
  have oldAt : configurationCandidateValue p outputConfiguration selected =
      2 ^ p.wordWidth := by
    apply configurationCandidateValue_padding
    omega
  have updateBalance := finiteValueCount_update_one_balance_general target
    (configurationCandidateValue p outputConfiguration) selected source.val
  rw [oldAt] at updateBalance
  by_cases below : target < 2 ^ p.wordWidth
  · let targetSite : QSite p := ⟨target, by
      have capacity : p.G * p.G = 2 ^ p.wordWidth := by
        simp [QParameters.G, QParameters.wordWidth, two_mul, pow_add]
      simpa [capacity] using below⟩
    have physicalBalance :=
      finiteValueCount_configurationCandidateValue_collision_balance
        configuration (source, direction) member collision targetSite
    have targetEqSource : targetSite = source ↔ target = source.val := by
      constructor
      · intro equal
        exact congrArg Fin.val equal
      · intro equal
        exact Fin.ext equal
    change finiteValueCount target
          (configurationCandidateValue p outputConfiguration) +
          (if targetSite = source then 1 else 0) =
        finiteValueCount target (configurationCandidateValue p configuration)
      at physicalBalance
    simp only [targetEqSource] at physicalBalance
    have sourceIndicator :
        (if source.val = target then 1 else 0) =
          (if target = source.val then 1 else 0) := by
      by_cases equal : target = source.val <;> simp [equal, eq_comm]
    have markerDifferent : 2 ^ p.wordWidth ≠ target :=
      Nat.ne_of_gt below
    rw [sourceIndicator] at updateBalance
    simp only [markerDifferent, if_false, Nat.add_zero] at updateBalance
    exact updateBalance.trans physicalBalance
  · have markerOrAbove : 2 ^ p.wordWidth ≤ target := Nat.le_of_not_gt below
    by_cases marker : target = 2 ^ p.wordWidth
    · subst target
      have sourceBelow := qSite_val_lt_marker p source
      have sourceDifferent : source.val ≠ 2 ^ p.wordWidth := sourceBelow.ne
      simp only [ite_true, sourceDifferent, if_false, Nat.add_zero] at updateBalance
      have markerCount :=
        finiteValueCount_configurationCandidateValue_collision_marker
          configuration (source, direction) member collision
      change finiteValueCount (2 ^ p.wordWidth)
          (configurationCandidateValue p outputConfiguration) =
        finiteValueCount (2 ^ p.wordWidth)
            (configurationCandidateValue p configuration) + 1 at markerCount
      exact Nat.add_right_cancel (updateBalance.trans markerCount)
    · have above : 2 ^ p.wordWidth < target := by omega
      have sourceDifferent : source.val ≠ target :=
        Nat.ne_of_lt (lt_trans (qSite_val_lt_marker p source) above)
      have markerDifferent : 2 ^ p.wordWidth ≠ target := by omega
      simp only [markerDifferent, sourceDifferent, if_false, Nat.add_zero]
        at updateBalance
      rw [updateBalance,
        finiteValueCount_configurationCandidateValue_gt_marker p
          outputConfiguration target above,
        finiteValueCount_configurationCandidateValue_gt_marker p
          configuration target above]

/--
collision branch の実candidate追加列と実bitonic sortを合成すると、sort後の
candidate値関数は元の predecessor 配置のcanonical昇順関数へ厳密に一致する。
-/
theorem rowEventCollisionModify_sort_correct
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (collision : moveSite source direction ∈ configuration.1.erase source)
    (activeSlot : Fin (p.K - 1))
    (slotAtBoundary : activeSlot.val + 1 =
      (eventOutput configuration source direction).1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p
        (eventOutput configuration source direction))
    (movedRead : readWires (oracleMovedWires p) input = siteWordBits p source)
    (candidateDataZero : readWires
      ((candidateWordAt p
        (rowEventCollisionCandidateIndex p activeSlot)).take p.wordWidth) input =
      List.replicate p.wordWidth false)
    (candidateMarkerOne : input (candidateMarkerWire p
      (rowEventCollisionCandidateIndex p activeSlot)) = true)
    (decoderScratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (branchTrue : input (oracleBranchWire p) = true)
    (activeDegree : input (oracleDegreeWireAt p
      (rowEventCollisionDegreeIndex p activeSlot)) = true)
    (otherDegree : ∀ degreeSlot : Fin (p.K - 1), degreeSlot ≠ activeSlot →
      input (oracleDegreeWireAt p
        (rowEventCollisionDegreeIndex p degreeSlot)) = false)
    (flagsZero : readWires (sortCompareWorkWires p)
        ((controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis reversibleGatePermutation input) =
      List.replicate (sortCompareWorkWires p).length false)
    (sortScratchZero : ∀ wire ∈ sortAndScratchWires p,
      ((controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis reversibleGatePermutation input) wire =
        false)
    (historiesZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      ((controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis reversibleGatePermutation input)
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).sortFlags).ancillaWire
              instruction.history) = false) :
    qCandidateValue p
        ((reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
          ((controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis
            reversibleGatePermutation input)) =
      configurationCandidateValue p configuration := by
  let modified := (controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis
    reversibleGatePermutation input
  have modifiedEq : modified =
      rowEventCollisionAppendReference p activeSlot input := by
    simpa [modified] using runBasis_rowEventCollisionModify_active p activeSlot input
      decoderScratchZero pairZero branchTrue activeDegree otherDegree
  apply qBitonicSort_candidateValue_eq_configurationCandidateValue p configuration
    modified flagsZero sortScratchZero historiesZero
  intro target
  rw [modifiedEq]
  exact rowEventCollisionAppendReference_preserves_predecessor_valueCount
    configuration source member direction collision activeSlot slotAtBoundary input
    valuesBefore movedRead candidateDataZero candidateMarkerOne target

/--
collision境界slotのdata全0・marker 1はcanonical candidate値から従うため、
明示的なbit仮定なしでも実追加列とsortの正しさを適用できる。
-/
theorem rowEventCollisionModify_sort_correct_of_values
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (collision : moveSite source direction ∈ configuration.1.erase source)
    (activeSlot : Fin (p.K - 1))
    (slotAtBoundary : activeSlot.val + 1 =
      (eventOutput configuration source direction).1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p
        (eventOutput configuration source direction))
    (movedRead : readWires (oracleMovedWires p) input = siteWordBits p source)
    (decoderScratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (branchTrue : input (oracleBranchWire p) = true)
    (activeDegree : input (oracleDegreeWireAt p
      (rowEventCollisionDegreeIndex p activeSlot)) = true)
    (otherDegree : ∀ degreeSlot : Fin (p.K - 1), degreeSlot ≠ activeSlot →
      input (oracleDegreeWireAt p
        (rowEventCollisionDegreeIndex p degreeSlot)) = false)
    (flagsZero : readWires (sortCompareWorkWires p)
        ((controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis reversibleGatePermutation input) =
      List.replicate (sortCompareWorkWires p).length false)
    (sortScratchZero : ∀ wire ∈ sortAndScratchWires p,
      ((controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis reversibleGatePermutation input) wire =
        false)
    (historiesZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      ((controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis reversibleGatePermutation input)
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).sortFlags).ancillaWire
              instruction.history) = false) :
    qCandidateValue p
        ((reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
          ((controlledUpdateSelectedRowCollisionCandidateWordCircuit p).runBasis
            reversibleGatePermutation input)) =
      configurationCandidateValue p configuration := by
  let selected := rowEventCollisionCandidateIndex p activeSlot
  have selectedValue : selected.val =
      (eventOutput configuration source direction).1.card := by
    simpa [selected, rowEventCollisionCandidateIndex] using slotAtBoundary
  have canonicalPadding : configurationCandidateValue p
      (eventOutput configuration source direction) selected =
        2 ^ p.wordWidth := by
    apply configurationCandidateValue_padding
    omega
  have physicalPadding : qCandidateValue p input selected =
      2 ^ p.wordWidth := by
    rw [congrFun valuesBefore selected]
    exact canonicalPadding
  have paddingBits := candidateDataMarker_of_qCandidateValue_eq_marker p input
    selected physicalPadding
  exact rowEventCollisionModify_sort_correct configuration source member direction
    collision activeSlot slotAtBoundary input valuesBefore movedRead paddingBits.1
    paddingBits.2 decoderScratchZero pairZero branchTrue activeDegree otherDegree
    flagsZero sortScratchZero historiesZero

/--
row event use全体の実回路は、canonical sorted writer参照作用の後にmoved-selector
参照foldを適用し、column-selector外の全wireをsorted直後の値に保つ。
-/
theorem runBasis_xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_reference
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (if offset.val % 2 = 1 then 1 else 0) input)) :
    let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
      (by simp [columnKeyWires]) (keySignalWire p)
      (if offset.val % 2 = 1 then 1 else 0) input
    let output := (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input
    readWires (columnSelectorWires p) output =
        movedMemberPositionSelectorOutputXorReference p offset.val (columnSelectorWires p)
          sorted ∧
      BasisAgreeOutside (columnSelectorWires p) output sorted := by
  let degreeChange : Int := if offset.val % 2 = 1 then 1 else 0
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
    (by simp [columnKeyWires]) (keySignalWire p) degreeChange input
  let output := (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input
  have sortedEq :
      (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (columnKeyWires p) (by simp [columnKeyWires])
        (keySignalWire p) degreeChange).runBasis reversibleGatePermutation input =
        sorted := by
    simpa [sorted, degreeChange, canonicalSortedOutputWires,
      canonicalSortedOutputActive] using
      runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical p .columnKey degreeChange input
        scratchZero pairZero
  have outputEq : output =
      (xorMovedMemberPositionIntoSelectorOutputCircuit p offset.val (columnSelectorWires p)).runBasis
        reversibleGatePermutation sorted := by
    change (xorMovedMemberPositionIntoSelectorOutputCircuit p offset.val (columnSelectorWires p)).runBasis
      reversibleGatePermutation
        ((xorSortedCandidatesAsDelimiterIntoOutputCircuit p (columnKeyWires p) (by simp [columnKeyWires])
          (keySignalWire p) degreeChange).runBasis
            reversibleGatePermutation input) = _
    rw [sortedEq]
  change readWires (columnSelectorWires p) output =
      movedMemberPositionSelectorOutputXorReference p offset.val (columnSelectorWires p)
        sorted ∧
    BasisAgreeOutside (columnSelectorWires p) output sorted
  rw [outputEq, runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_slotFold]
  have result := runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitSlotList_correct p offset.val
    (columnSelectorWires p) sorted
    (MovedMemberPositionSelectorOutputLayout_columnSelector_canonical p) movedClean
    (List.finRange p.K) sorted (by
      intro wire outside
      rfl)
  exact result

/-- 一degreeのsorted writer参照作用はcolumn-keyとkey-signal外を保存する。 -/
theorem writeSortedDegreeReference_outside_columnKey
    (p : QParameters) (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideKey : wire ∉ columnKeyWires p)
    (outsideSignal : wire ≠ keySignalWire p) :
    writeSortedDegreeReference p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p) degreeSlot degreeChange
        input wire = input wire := by
  unfold writeSortedDegreeReference
  split
  · apply writeSortedUseReference_outside p (columnKeyWires p)
      (by simp [columnKeyWires]) (keySignalWire p) _ _ _ input wire
      outsideKey outsideSignal
  · rfl

/-- sorted writer参照fold全体もcolumn-keyとkey-signal外を保存する。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_columnKey
    (p : QParameters) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideKey : wire ∉ columnKeyWires p)
    (outsideSignal : wire ≠ keySignalWire p) :
    SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p) degreeChange input wire =
      input wire := by
  unfold SortedCandidatesDelimiterOutputXorSpec
  let slots := List.finRange p.K
  change slots.foldl (fun state degreeSlot =>
      writeSortedDegreeReference p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p) degreeSlot degreeChange
          state) input wire = input wire
  induction slots generalizing input with
  | nil => rfl
  | cons degreeSlot slots inductionHypothesis =>
      simp only [List.foldl_cons]
      calc
        slots.foldl (fun state nextSlot =>
            writeSortedDegreeReference p (columnKeyWires p)
              (by simp [columnKeyWires]) (keySignalWire p) nextSlot
                degreeChange state)
            (writeSortedDegreeReference p (columnKeyWires p)
              (by simp [columnKeyWires]) (keySignalWire p) degreeSlot
                degreeChange input) wire =
          writeSortedDegreeReference p (columnKeyWires p)
            (by simp [columnKeyWires]) (keySignalWire p) degreeSlot
              degreeChange input wire := inductionHypothesis _
        _ = input wire := writeSortedDegreeReference_outside_columnKey p
          degreeSlot degreeChange input wire outsideKey outsideSignal

/--
sorted writerの二出力とmoved selector出力がsupport外なら、row event use全体は
そのsupport上の全bitを厳密に保存する。
-/
theorem xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_preserves_support
    (p : QParameters) (offset : Fin 6)
    (support : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (if offset.val % 2 = 1 then 1 else 0) input))
    (supportDisjointKey : support.Disjoint (columnKeyWires p))
    (supportDisjointSelector : support.Disjoint (columnSelectorWires p))
    (signalOutside : keySignalWire p ∉ support) :
    BasisAgreeOn support
      ((xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input) input := by
  let degreeChange : Int := if offset.val % 2 = 1 then 1 else 0
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
    (by simp [columnKeyWires]) (keySignalWire p) degreeChange input
  have useResult := runBasis_xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_reference p offset input scratchZero
    pairZero movedClean
  intro wire supportMember
  have outsideSelector : wire ∉ columnSelectorWires p := by
    intro selectorMember
    exact (List.disjoint_left.mp supportDisjointSelector) supportMember
      selectorMember
  have outsideKey : wire ∉ columnKeyWires p := by
    intro keyMember
    exact (List.disjoint_left.mp supportDisjointKey) supportMember keyMember
  have outsideSignal : wire ≠ keySignalWire p := by
    intro equal
    subst wire
    exact signalOutside supportMember
  calc
    (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input wire =
        sorted wire := useResult.2 wire outsideSelector
    _ = input wire := xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_columnKey p
      degreeChange input wire outsideKey outsideSignal

/-- row event computeが読むrow-selector・system・oracle-workをまとめた有限support。 -/
def rowEventBroadSupport (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  rowSelectorWires p ++ systemWires p ++ diagonalOracleWorkWires p

/-- row event broad supportはcolumn-key出力registerと交わらない。 -/
theorem rowEventBroadSupport_disjoint_columnKey (p : QParameters) :
    (rowEventBroadSupport p).Disjoint (columnKeyWires p) := by
  rw [List.disjoint_left]
  intro wire supportMember keyMember
  rcases List.mem_append.mp supportMember with prefixMember | workMember
  · rcases List.mem_append.mp prefixMember with selectorMember | systemMember
    · exact (List.disjoint_left.mp (rowDiagonalSupport_disjoint_columnKey p))
        (List.mem_append_left _ selectorMember) keyMember
    · have systemDisjointKey :
          (systemWires p).Disjoint (columnKeyWires p) := by
        simpa [systemWires, topSystemWires, QLayout.systemWire,
          columnKeyWires_eq_topColumnKeyWires]
          using topSystemWires_disjoint_topColumnKeyWires p
      exact (List.disjoint_left.mp systemDisjointKey)
        systemMember keyMember
  · exact (List.disjoint_left.mp (rowDiagonalSupport_disjoint_columnKey p))
      (List.mem_append_right _ workMember) keyMember

/-- row event broad supportはcolumn-selector出力registerと交わらない。 -/
theorem rowEventBroadSupport_disjoint_columnSelector (p : QParameters) :
    (rowEventBroadSupport p).Disjoint (columnSelectorWires p) := by
  rw [List.disjoint_left]
  intro wire supportMember selectorOutputMember
  rcases List.mem_append.mp supportMember with prefixMember | workMember
  · rcases List.mem_append.mp prefixMember with selectorMember | systemMember
    · exact (List.disjoint_left.mp
        (rowDiagonalSupport_disjoint_columnSelector p))
          (List.mem_append_left _ selectorMember) selectorOutputMember
    · have systemDisjointSelector :
          (systemWires p).Disjoint (columnSelectorWires p) := by
        rw [List.disjoint_left]
        intro shared systemMembership selectorMembership
        rcases List.mem_map.mp systemMembership with
          ⟨systemIndex, _, systemEqual⟩
        rcases List.mem_map.mp selectorMembership with
          ⟨selectorIndex, _, selectorEqual⟩
        have impossible : QLayout.systemWire p systemIndex =
            columnSelectorWire p selectorIndex :=
          systemEqual.trans selectorEqual.symm
        cases impossible
      exact (List.disjoint_left.mp systemDisjointSelector)
        systemMember selectorOutputMember
  · exact (List.disjoint_left.mp
      (rowDiagonalSupport_disjoint_columnSelector p))
        (List.mem_append_right _ workMember) selectorOutputMember

/-- key-signal出力bitはrow event broad supportに含まれない。 -/
theorem keySignalWire_not_mem_rowEventBroadSupport (p : QParameters) :
    keySignalWire p ∉ rowEventBroadSupport p := by
  intro supportMember
  rcases List.mem_append.mp supportMember with prefixMember | workMember
  · rcases List.mem_append.mp prefixMember with selectorMember | systemMember
    · exact keySignalWire_not_mem_rowDiagonalSupport p
        (List.mem_append_left _ selectorMember)
    · rcases List.mem_map.mp systemMember with
        ⟨systemIndex, _, impossible⟩
      cases impossible
  · exact keySignalWire_not_mem_rowDiagonalSupport p
      (List.mem_append_right _ workMember)

/-- canonical broad supportについて、actual row event useはsupport全bitを保存する。 -/
theorem xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_preserves_broadSupport
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (if offset.val % 2 = 1 then 1 else 0) input)) :
    BasisAgreeOn (rowEventBroadSupport p)
      ((xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input) input := by
  exact xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_preserves_support p offset (rowEventBroadSupport p) input
    scratchZero pairZero movedClean
    (rowEventBroadSupport_disjoint_columnKey p)
    (rowEventBroadSupport_disjoint_columnSelector p)
    (keySignalWire_not_mem_rowEventBroadSupport p)

/--
任意の有限compute supportについて、row event computeの局所性とuseのsupport保存が
分かれば、分岐全体はsupport復元参照作用と厳密に一致する。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_eq_restoreSupport
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (support : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (computeUses : circuitUsesOnly support (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset))
    (usePreserves : BasisAgreeOn support
      ((xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
        ((computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis
          reversibleGatePermutation input))
      ((computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis
        reversibleGatePermutation input)) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input =
      restoreSupport support input
        ((xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
          ((computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis
            reversibleGatePermutation input)) := by
  rw [applyRowEventReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
  exact Circuit.computeUseUncompute_local_clean support
    (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset) input computeUses
    usePreserves

/--
canonical broad support 上の compute 局所性を与えると、clean な actual compute 出力に対する
row event 分岐全体は、use 結果の外部出力だけを残して broad support を入力へ厳密に戻す。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_eq_restoreBroadSupport
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (computeUses : circuitUsesOnly (rowEventBroadSupport p)
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset))
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
  apply applyRowEventReferenceAndRestoreWorkCircuit_eq_restoreSupport p slot offset
    (rowEventBroadSupport p) input computeUses
  apply xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_preserves_broadSupport p offset
  · exact scratchZero
  · exact pairZero
  · exact movedClean

/--
row event 分岐の純粋 writer 参照出力と、compute support の厳密な復元をまとめた仕様。
-/
structure RowEventBranchReferenceResult (p : QParameters) (offset : Fin 6)
    (input computed output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- column-key は canonical sorted writer 参照作用の出力に一致する。 -/
  column_key : readWires (columnKeyWires p) output =
    readWires (columnKeyWires p)
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (if offset.val % 2 = 1 then 1 else 0) computed)
  /-- column-selector は sorted writer 後の moved-selector 純粋 fold に一致する。 -/
  column_selector : readWires (columnSelectorWires p) output =
    movedMemberPositionSelectorOutputXorReference p offset.val (columnSelectorWires p)
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (if offset.val % 2 = 1 then 1 else 0) computed)
  /-- key-signal は canonical sorted writer 参照作用の出力に一致する。 -/
  key_signal : output (keySignalWire p) =
    SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
      (by simp [columnKeyWires]) (keySignalWire p)
      (if offset.val % 2 = 1 then 1 else 0) computed (keySignalWire p)
  /-- row-selector・system・oracle-work の全 support は入力値へ戻る。 -/
  support_restored : BasisAgreeOn (rowEventBroadSupport p) output input

/--
compute の broad-support 局所性と actual use の clean 条件から、row event 分岐全体が
純粋 writer 参照出力を返し、全内部 support を入力へ復元することが従う。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_reference_correct
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (computeUses : circuitUsesOnly (rowEventBroadSupport p)
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset))
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
  let computed := (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
  let sorted := SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
    (by simp [columnKeyWires]) (keySignalWire p)
    (if offset.val % 2 = 1 then 1 else 0) computed
  let used := (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation computed
  let output := (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
    reversibleGatePermutation input
  have outputEq : output = restoreSupport (rowEventBroadSupport p) input used := by
    dsimp [output, used, computed]
    exact applyRowEventReferenceAndRestoreWorkCircuit_eq_restoreBroadSupport p slot offset input
      computeUses scratchZero pairZero movedClean
  have useSpec :
      readWires (columnSelectorWires p) used =
          movedMemberPositionSelectorOutputXorReference p offset.val (columnSelectorWires p)
            sorted ∧
        BasisAgreeOutside (columnSelectorWires p) used sorted := by
    dsimp [used, sorted, computed]
    exact runBasis_xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_reference p offset _ scratchZero pairZero movedClean
  have keyUsed : readWires (columnKeyWires p) used =
      readWires (columnKeyWires p) sorted := by
    apply List.map_congr_left
    intro wire member
    exact useSpec.2 wire
      ((List.disjoint_left.mp (columnKeyWires_disjoint_columnSelectorWires p))
        member)
  have signalUsed : used (keySignalWire p) = sorted (keySignalWire p) :=
    useSpec.2 (keySignalWire p) (keySignalWire_not_mem_columnSelectorWires p)
  have keyFinal : readWires (columnKeyWires p) output =
      readWires (columnKeyWires p) used := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (rowEventBroadSupport p) input used wire
      (fun supportMember =>
        (List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnKey p))
          supportMember member)
  have selectorFinal : readWires (columnSelectorWires p) output =
      readWires (columnSelectorWires p) used := by
    rw [outputEq]
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (rowEventBroadSupport p) input used wire
      (fun supportMember =>
        (List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnSelector p))
          supportMember member)
  have signalFinal : output (keySignalWire p) = used (keySignalWire p) := by
    rw [outputEq]
    exact restoreSupport_outside (rowEventBroadSupport p) input used
      (keySignalWire p) (keySignalWire_not_mem_rowEventBroadSupport p)
  change RowEventBranchReferenceResult p offset input computed output
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [sorted] using keyFinal.trans keyUsed
  · simpa [sorted] using selectorFinal.trans useSpec.1
  · simpa [sorted] using signalFinal.trans signalUsed
  · intro wire member
    rw [outputEq]
    exact restoreSupport_agrees_input (rowEventBroadSupport p) input used wire member

/-- 同一bit列どうしのbitwise XORは同じ長さの全0列である。 -/
theorem candidateZipWithXorSelf (bits : List Bool) :
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

/-- 有限関数の一添字更新について、更新前後の値出現個数を加法的に比較する。 -/
theorem finiteValueCount_update_one_balance
    {index value : Type*} [Fintype index] [DecidableEq index]
    [DecidableEq value]
    (target : value) (values : index → value) (selected : index) (newValue : value) :
    finiteValueCount target
          (fun position => if position = selected then newValue else values position) +
        (if values selected = target then 1 else 0) =
      finiteValueCount target values +
        (if newValue = target then 1 else 0) := by
  unfold finiteValueCount
  let oldTerm := fun position : index => if values position = target then 1 else 0
  let newTerm := fun position : index =>
    if (if position = selected then newValue else values position) = target then 1 else 0
  have oldAsSum : oldTerm selected =
      ∑ position : index, if position = selected then oldTerm selected else 0 := by
    simp
  have newAsSum : (if newValue = target then 1 else 0) =
      ∑ position : index,
        if position = selected then (if newValue = target then 1 else 0) else 0 := by
    simp
  change (∑ position : index, newTerm position) + oldTerm selected =
    (∑ position : index, oldTerm position) +
      (if newValue = target then 1 else 0)
  rw [oldAsSum, newAsSum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro position _
  by_cases equal : position = selected
  · subst position
    simp [newTerm, oldTerm, Nat.add_comm]
  · simp [newTerm, oldTerm, equal]

/--
branchが有効なreplacement変更回路は、選択candidate dataをsystem上のarrivalから
moved上のpredecessor sourceへ厳密に置き換える。
-/
theorem runBasis_rowEventReplacementModify_target
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (arrival source : QSite p)
    (branchTrue : input (oracleBranchWire p) = true)
    (systemRead : readWires (registerWordAt p (systemWires p) slot) input =
      siteWordBits p arrival)
    (candidateRead : readWires
      ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth) input =
        siteWordBits p arrival)
    (movedRead : readWires (oracleMovedWires p) input =
      siteWordBits p source) :
    readWires ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth)
        ((controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis
          reversibleGatePermutation input) = siteWordBits p source := by
  let systemWord := registerWordAt p (systemWires p) slot
  let candidateData :=
    (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let branch := oracleBranchWire p
  let afterRemove := (controlledXorCopy branch systemWord candidateData).runBasis
    reversibleGatePermutation input
  have systemLength : systemWord.length = candidateData.length := by
    rw [show systemWord.length = p.wordWidth by
      exact registerWordAt_length p (systemWires p) (by simp [systemWires]) slot]
    simp [candidateData]
  have movedLength : (oracleMovedWires p).length = candidateData.length := by
    simp [oracleMovedWires, QParameters.movedWidth, candidateData]
  have systemDisjoint : systemWord.Disjoint candidateData :=
    systemRegisterWord_disjoint_candidateData p slot (slotToSortWord p slot)
  have movedDisjoint : (oracleMovedWires p).Disjoint candidateData :=
    oracleMovedWires_disjoint_candidateData p (slotToSortWord p slot)
  have branchAbsentSystem : branch ∉ systemWord := by
    intro member
    exact oracleBranchWire_not_mem_systemWires p
      (mem_register_of_mem_registerWordAt p (systemWires p) slot member)
  have branchAbsentCandidate : branch ∉ candidateData :=
    oracleBranchWire_not_mem_candidateData p (slotToSortWord p slot)
  have branchAbsentMoved : branch ∉ oracleMovedWires p :=
    oracleBranchWire_not_mem_oracleMovedWires p
  have candidateNodup : candidateData.Nodup :=
    (candidateWordAt_nodup p (slotToSortWord p slot)).take
  have systemNodup : systemWord.Nodup := by
    dsimp [systemWord, registerWordAt]
    exact (systemWires_nodup p).drop.take
  have movedNodup : (oracleMovedWires p).Nodup := by
    let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
    simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using
      (RegisterSlice.wireList_nodup (systemWidth := p.systemWidth) movedSlice)
  have removedRead : readWires candidateData afterRemove =
      List.replicate p.wordWidth false := by
    have result := readWires_validatedControlledXorCopyLists_target branch
      systemWord candidateData input systemNodup candidateNodup systemLength
      systemDisjoint branchAbsentSystem branchAbsentCandidate
    rw [branchTrue] at result
    rw [systemRead, candidateRead] at result
    simpa [systemWord, candidateData] using
      result.trans (candidateZipWithXorSelf (siteWordBits p arrival))
  have branchAfter : afterRemove branch = true := by
    dsimp only [afterRemove]
    rw [runBasis_validatedControlledXorCopyLists_outside branch systemWord
      candidateData input systemNodup candidateNodup systemLength systemDisjoint
      branchAbsentSystem branchAbsentCandidate branch branchAbsentCandidate]
    exact branchTrue
  have movedAfter : readWires (oracleMovedWires p) afterRemove =
      siteWordBits p source := by
    rw [readWires_validatedControlledXorCopyLists_outside branch systemWord
      candidateData (oracleMovedWires p) input systemNodup candidateNodup
      systemLength systemDisjoint branchAbsentSystem branchAbsentCandidate
      movedDisjoint]
    exact movedRead
  rw [controlledUpdateSelectedRowReplacementCandidateWordCircuit, runBasis_seq]
  change readWires candidateData
    ((controlledXorCopy branch (oracleMovedWires p) candidateData).runBasis
      reversibleGatePermutation afterRemove) = _
  rw [readWires_validatedControlledXorCopyLists_target branch
    (oracleMovedWires p) candidateData afterRemove movedNodup candidateNodup
    movedLength movedDisjoint branchAbsentMoved branchAbsentCandidate]
  rw [branchAfter]
  rw [movedAfter, removedRead]
  simpa using candidateZipWithXorFalse (siteWordBits p source)

/-- replacement変更回路は選択candidate data外の任意wireを保存する。 -/
theorem runBasis_rowEventReplacementModify_outside
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉
      (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth) :
    (controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis
        reversibleGatePermutation input wire = input wire := by
  let systemWord := registerWordAt p (systemWires p) slot
  let candidateData :=
    (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let branch := oracleBranchWire p
  let afterRemove := (controlledXorCopy branch systemWord candidateData).runBasis
    reversibleGatePermutation input
  have systemLength : systemWord.length = candidateData.length := by
    rw [show systemWord.length = p.wordWidth by
      exact registerWordAt_length p (systemWires p) (by simp [systemWires]) slot]
    simp [candidateData]
  have movedLength : (oracleMovedWires p).length = candidateData.length := by
    simp [oracleMovedWires, QParameters.movedWidth, candidateData]
  have systemDisjoint : systemWord.Disjoint candidateData :=
    systemRegisterWord_disjoint_candidateData p slot (slotToSortWord p slot)
  have movedDisjoint : (oracleMovedWires p).Disjoint candidateData :=
    oracleMovedWires_disjoint_candidateData p (slotToSortWord p slot)
  have branchAbsentSystem : branch ∉ systemWord := by
    intro member
    exact oracleBranchWire_not_mem_systemWires p
      (mem_register_of_mem_registerWordAt p (systemWires p) slot member)
  have branchAbsentCandidate : branch ∉ candidateData :=
    oracleBranchWire_not_mem_candidateData p (slotToSortWord p slot)
  have branchAbsentMoved : branch ∉ oracleMovedWires p :=
    oracleBranchWire_not_mem_oracleMovedWires p
  have candidateNodup : candidateData.Nodup :=
    (candidateWordAt_nodup p (slotToSortWord p slot)).take
  have systemNodup : systemWord.Nodup := by
    dsimp [systemWord, registerWordAt]
    exact (systemWires_nodup p).drop.take
  have movedNodup : (oracleMovedWires p).Nodup := by
    let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
    simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using
      (RegisterSlice.wireList_nodup (systemWidth := p.systemWidth) movedSlice)
  rw [controlledUpdateSelectedRowReplacementCandidateWordCircuit, runBasis_seq]
  change (controlledXorCopy branch (oracleMovedWires p) candidateData).runBasis
      reversibleGatePermutation afterRemove wire = input wire
  rw [runBasis_validatedControlledXorCopyLists_outside branch
    (oracleMovedWires p) candidateData afterRemove movedNodup candidateNodup
    movedLength movedDisjoint branchAbsentMoved branchAbsentCandidate wire outside]
  exact runBasis_validatedControlledXorCopyLists_outside branch systemWord
    candidateData input systemNodup candidateNodup systemLength systemDisjoint
    branchAbsentSystem branchAbsentCandidate wire outside

/--
有効replacement branchでは、変更後candidate値は選択slotだけpredecessor source値となり、
他の全wordは出力配置のcanonical値を保つ。
-/
theorem qCandidateValue_runBasis_rowEventReplacementModify
    (p : QParameters) (configuration : QConfiguration p) (source : QSite p)
    (slot : Fin p.K) (active : slot.val < configuration.1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (systemWires p)
      configuration source input)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (branchTrue : input (oracleBranchWire p) = true) :
    qCandidateValue p
        ((controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis
          reversibleGatePermutation input) =
      fun word => if word = slotToSortWord p slot then source.val
        else configurationCandidateValue p configuration word := by
  let selectedWord := slotToSortWord p slot
  let arrivalSite := configuration.siteAt ⟨slot.val, active⟩
  let output := (controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis
    reversibleGatePermutation input
  have systemRead : readWires (registerWordAt p (systemWires p) slot) input =
      siteWordBits p arrivalSite := by
    exact specification.active_word slot active
  have selectedActive : selectedWord.val < configuration.1.card := active
  have candidateRead : readWires
      ((candidateWordAt p selectedWord).take p.wordWidth) input =
        siteWordBits p arrivalSite := by
    exact candidateData_eq_siteWordBits_of_value_eq p configuration input
      valuesBefore selectedWord selectedActive
  have movedRead : readWires (oracleMovedWires p) input = siteWordBits p source :=
    specification.moved_word
  have targetRead : readWires
      ((candidateWordAt p selectedWord).take p.wordWidth) output =
        siteWordBits p source := by
    exact runBasis_rowEventReplacementModify_target p slot input arrivalSite source
      branchTrue systemRead candidateRead movedRead
  have markerBefore : input (candidateMarkerWire p selectedWord) = false :=
    candidateMarker_false_of_value_eq p configuration input valuesBefore
      selectedWord selectedActive
  have markerAfter : output (candidateMarkerWire p selectedWord) = false := by
    dsimp only [output, selectedWord]
    rw [runBasis_rowEventReplacementModify_outside p slot input
      (candidateMarkerWire p (slotToSortWord p slot))
      (candidateMarkerWire_not_mem_data p (slotToSortWord p slot))]
    exact markerBefore
  funext word
  by_cases selected : word = selectedWord
  · subst word
    rw [if_pos rfl]
    rw [qCandidateValue_eq_of_data_marker p output selectedWord
      (siteWordBits p source) false targetRead markerAfter]
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
      exact runBasis_rowEventReplacementModify_outside p slot input wire
        (fun targetMember =>
          (List.disjoint_left.mp wordDisjointTarget) wordMember targetMember)
    unfold qCandidateValue
    rw [wordRead]
    exact congrFun valuesBefore word

/--
非衝突eventの出力配置をrow側で逆算するreplacement変更回路は、全自然数値について
元配置のcanonical candidateと同じ出現個数を持つ。
-/
theorem rowEventReplacementModify_preserves_predecessor_valueCount
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (noCollision : moveSite source direction ∉ configuration.1.erase source)
    (slot : Fin p.K)
    (active : slot.val < (eventOutput configuration source direction).1.card)
    (arrivalAt :
      (eventOutput configuration source direction).siteAt ⟨slot.val, active⟩ =
        moveSite source direction)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (systemWires p)
      (eventOutput configuration source direction) source input)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p (eventOutput configuration source direction))
    (branchTrue : input (oracleBranchWire p) = true)
    (target : Nat) :
    finiteValueCount target
        (qCandidateValue p
          ((controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis
            reversibleGatePermutation input)) =
      finiteValueCount target (configurationCandidateValue p configuration) := by
  let outputConfiguration := eventOutput configuration source direction
  let selectedWord := slotToSortWord p slot
  let moved := moveSite source direction
  have actualValues := qCandidateValue_runBasis_rowEventReplacementModify p
    outputConfiguration source slot active input specification valuesBefore branchTrue
  rw [actualValues]
  have oldAt : configurationCandidateValue p outputConfiguration selectedWord =
      moved.val := by
    rw [configurationCandidateValue_active p outputConfiguration selectedWord active]
    exact congrArg Fin.val arrivalAt
  have updateBalance := finiteValueCount_update_one_balance target
    (configurationCandidateValue p outputConfiguration) selectedWord source.val
  rw [oldAt] at updateBalance
  by_cases below : target < 2 ^ p.wordWidth
  · let targetSite : QSite p := ⟨target, by
      have capacity : p.G * p.G = 2 ^ p.wordWidth := by
        simp [QParameters.G, QParameters.wordWidth, two_mul, pow_add]
      simpa [capacity] using below⟩
    have physicalBalance :=
      finiteValueCount_configurationCandidateValue_noCollision_balance
        configuration (source, direction) member noCollision targetSite
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
          (configurationCandidateValue p outputConfiguration) +
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
    exact Nat.add_right_cancel (updateBalance.trans physicalBalance)
  · have markerOrAbove : 2 ^ p.wordWidth ≤ target := Nat.le_of_not_gt below
    by_cases marker : target = 2 ^ p.wordWidth
    · subst target
      have sourceBelow := qSite_val_lt_marker p source
      have movedBelow := qSite_val_lt_marker p moved
      simp [sourceBelow.ne, movedBelow.ne] at updateBalance
      rw [updateBalance]
      exact finiteValueCount_configurationCandidateValue_noCollision_marker
        configuration (source, direction) member noCollision
    · have above : 2 ^ p.wordWidth < target := by omega
      have sourceDifferent : source.val ≠ target := by
        exact Nat.ne_of_lt (lt_trans (qSite_val_lt_marker p source) above)
      have movedDifferent : moved.val ≠ target := by
        exact Nat.ne_of_lt (lt_trans (qSite_val_lt_marker p moved) above)
      simp [sourceDifferent, movedDifferent] at updateBalance
      rw [updateBalance,
        finiteValueCount_configurationCandidateValue_gt_marker p
          outputConfiguration target above,
        finiteValueCount_configurationCandidateValue_gt_marker p
          configuration target above]

/--
非衝突replacement branchの実変更回路と実bitonic sortを合成すると、全candidate値は
元predecessor配置のcanonical昇順関数に厳密一致する。
-/
theorem rowEventReplacementModify_sort_correct
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (noCollision : moveSite source direction ∉ configuration.1.erase source)
    (slot : Fin p.K)
    (active : slot.val < (eventOutput configuration source direction).1.card)
    (arrivalAt :
      (eventOutput configuration source direction).siteAt ⟨slot.val, active⟩ =
        moveSite source direction)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (systemWires p)
      (eventOutput configuration source direction) source input)
    (valuesBefore : qCandidateValue p input =
      configurationCandidateValue p (eventOutput configuration source direction))
    (branchTrue : input (oracleBranchWire p) = true)
    (flagsZero : readWires (sortCompareWorkWires p)
        ((controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis
          reversibleGatePermutation input) =
      List.replicate (sortCompareWorkWires p).length false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p,
      ((controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis
        reversibleGatePermutation input) wire = false)
    (historiesZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      ((controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis
        reversibleGatePermutation input)
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).sortFlags).ancillaWire
              instruction.history) = false) :
    qCandidateValue p
        ((reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
          ((controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis
            reversibleGatePermutation input)) =
      configurationCandidateValue p configuration := by
  let modified := (controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis
    reversibleGatePermutation input
  apply qBitonicSort_candidateValue_eq_configurationCandidateValue p configuration
    modified flagsZero scratchZero historiesZero
  intro target
  exact rowEventReplacementModify_preserves_predecessor_valueCount configuration
    source member direction noCollision slot active arrivalAt input specification
    valuesBefore branchTrue target

/-- event 範囲 `2..5` の offset は方向と collision 指定から一意に復元できる。 -/
theorem eventOffset_rowEventDirection_rowEventCollision
    (offset : Fin 6) (eventRange : 2 ≤ offset.val) :
    eventOffset (rowEventDirection offset) (rowEventCollision offset) = offset := by
  apply Fin.ext
  by_cases horizontal : offset.val < 4
  · by_cases collision : offset.val % 2 = 1
    · simp [rowEventDirection, rowEventCollision, eventOffset, horizontal,
        collision]
      omega
    · simp [rowEventDirection, rowEventCollision, eventOffset, horizontal,
        collision]
      omega
  · by_cases collision : offset.val % 2 = 1
    · simp [rowEventDirection, rowEventCollision, eventOffset, horizontal,
        collision]
      omega
    · simp [rowEventDirection, rowEventCollision, eventOffset, horizontal,
        collision]
      omega

/-- event 範囲では row event の方向判定が selector の方向判定に一致する。 -/
theorem selectorDirection_of_rowEventOffset
    {p : QParameters} (slot : Fin p.K) (offset : Fin 6) :
    selectorDirection (selectorOfSlotOffset slot offset) =
      rowEventDirection offset := by
  simp [selectorDirection, rowEventDirection]

/-- event 範囲では row event の collision 判定が selector の判定に一致する。 -/
theorem selectorRequestsCollision_of_rowEventOffset
    {p : QParameters} (slot : Fin p.K) (offset : Fin 6) :
    selectorRequestsCollision (selectorOfSlotOffset slot offset) =
      rowEventCollision offset := by
  simp [selectorRequestsCollision, rowEventCollision]

/-- row event の逆移動後に moved register が持つべき純粋な bit 列。 -/
def rowEventMovedBitsReference (p : QParameters) (offset : Fin 6)
    (arrivalBits : List Bool) : List Bool :=
  if offset.val < 4 then
    decrementBits (arrivalBits.take p.q) ++ arrivalBits.drop p.q
  else
    arrivalBits.take p.q ++ decrementBits (arrivalBits.drop p.q)

/-- 純粋な逆移動 bit 列は物理 site の `moveSiteBackward` と厳密に一致する。 -/
theorem rowEventMovedBitsReference_site
    (p : QParameters) (offset : Fin 6) (arrival : QSite p) :
    rowEventMovedBitsReference p offset (siteWordBits p arrival) =
      siteWordBits p (moveSiteBackward arrival (rowEventDirection offset)) := by
  rw [siteWordBits_moveSiteBackward]
  by_cases horizontal : offset.val < 4
  · simp [rowEventMovedBitsReference, rowEventDirection, horizontal]
  · simp [rowEventMovedBitsReference, rowEventDirection, horizontal]

/-- event 範囲の selector が指定する predecessor source の純粋な bit 列。 -/
theorem rowEventMovedBitsReference_selectorSource
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (arrival : QSite p) :
    rowEventMovedBitsReference p offset (siteWordBits p arrival) =
      siteWordBits p
        (moveSiteBackward arrival
          (selectorDirection (selectorOfSlotOffset slot offset))) := by
  rw [selectorDirection_of_rowEventOffset]
  exact rowEventMovedBitsReference_site p offset arrival

/-- canonical moved register の長さは一つの site word 幅である。 -/
@[simp] theorem oracleMovedWires_length (p : QParameters) :
    (oracleMovedWires p).length = p.wordWidth := by
  simp [oracleMovedWires, QParameters.movedWidth]

/-- canonical moved register には wire の重複がない。 -/
theorem oracleMovedWires_nodup (p : QParameters) :
    (oracleMovedWires p).Nodup := by
  let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
  simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using
    (RegisterSlice.wireList_nodup
      (systemWidth := p.systemWidth) movedSlice)

/-- 物理 system register と moved work register は交わらない。 -/
theorem systemWires_disjoint_oracleMovedWires (p : QParameters) :
    (systemWires p).Disjoint (oracleMovedWires p) := by
  let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
  simpa [systemWires, QLayout.systemWire, oracleMovedWires, movedSlice,
    RegisterSlice.wireList] using
    (RegisterSlice.systemWires_disjoint_wireList
      (systemWidth := p.systemWidth) movedSlice)

/-- moved work register と decrement/AND scratch は交わらない。 -/
theorem oracleMovedWires_disjoint_decoderAndScratch (p : QParameters) :
    (oracleMovedWires p).Disjoint (decoderAndScratchWires p) := by
  let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have separated : movedSlice.start + p.movedWidth ≤ andSlice.start := by
    simp [movedSlice, andSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have full :
      (movedSlice.wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
    movedSlice.wireList_disjoint_of_end_le_start andSlice separated
  rw [List.disjoint_left]
  intro wire movedMember scratchMember
  apply (List.disjoint_left.mp full)
  · simpa [oracleMovedWires, movedSlice, RegisterSlice.wireList] using movedMember
  · have andMember : wire ∈ oracleAndWorkWires p :=
      List.mem_of_mem_drop scratchMember
    simpa [oracleAndWorkWires, andSlice, RegisterSlice.wireList] using andMember

/-- moved register が全0なら、arrival copy 後の値は選択 system word そのものである。 -/
theorem runBasis_rowEventMovedCopy_readWires
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (movedZero : ∀ wire ∈ oracleMovedWires p, input wire = false) :
    readWires (oracleMovedWires p)
        ((rowEventMovedCopy p slot).runBasis reversibleGatePermutation input) =
      readWires (registerWordAt p (systemWires p) slot) input := by
  let source := registerWordAt p (systemWires p) slot
  let target := oracleMovedWires p
  have sourceLength : source.length = p.wordWidth := by
    exact registerWordAt_length p (systemWires p) (systemWires_length p) slot
  have sameLength : source.length = target.length := by
    simp [source, target, sourceLength]
  have sourceSubset : ∀ wire ∈ source, wire ∈ systemWires p := by
    intro wire member
    exact mem_register_of_mem_registerWordAt p (systemWires p) slot member
  have disjoint : source.Disjoint target := by
    rw [List.disjoint_left]
    intro wire sourceMember targetMember
    exact (List.disjoint_left.mp (systemWires_disjoint_oracleMovedWires p))
      (sourceSubset wire sourceMember) targetMember
  have targetNodup : target.Nodup := by
    simpa [target] using oracleMovedWires_nodup p
  have sourceNodup : source.Nodup := by
    simpa [source] using registerWordAt_nodup_of_nodup p (systemWires p) slot
      (systemWires_nodup p)
  have targetZero : readWires target input =
      List.replicate target.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact movedZero wire (by simpa [target] using member)
  rw [rowEventMovedCopy]
  rw [readWires_validatedXorCopyLists_target source target input sourceNodup
    targetNodup sameLength disjoint]
  rw [targetZero, ← sameLength]
  simpa [readWires, source] using
    candidateZipWithXorFalse (readWires source input)

/-- The canonical row moved-copy execution is the independent pure reference. -/
theorem runBasis_rowEventMovedCopy_eq_controlledCopyReference
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (rowEventMovedCopy p slot).runBasis reversibleGatePermutation input =
      controlledCopyBasisReference true
        (registerWordAt p (systemWires p) slot) (oracleMovedWires p) input := by
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
  exact runBasis_validatedXorCopyLists_eq_controlledCopyBasisReference_true
    (registerWordAt p (systemWires p) slot) (oracleMovedWires p) input
    (registerWordAt_nodup_of_nodup p (systemWires p) slot
      (systemWires_nodup p)) (oracleMovedWires_nodup p) sameLength
    sourceDisjoint

/-- 重複のない列を分割すると、先頭部分と末尾部分は交わらない。 -/
theorem nodup_take_disjoint_drop {α : Type}
    (words : List α) (count : Nat) (nodup : words.Nodup) :
    (words.take count).Disjoint (words.drop count) := by
  rw [List.disjoint_left]
  intro word takeMember dropMember
  have splitNodup : (words.take count ++ words.drop count).Nodup := by
    simpa using nodup
  exact (List.nodup_append.mp splitNodup).2.2 word takeMember word dropMember rfl

/--
周期decrementは、decrement対象と交わらないwire列の読出し値を保存する。
-/
theorem readWires_decrementWordMod2PowInPlaceCircuit_disjoint
    {ancillaQubits systemQubits : Nat}
    (word scratches other : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (disjoint : word.Disjoint other) :
    readWires other
        ((decrementWordMod2PowInPlaceCircuit word scratches).runBasis
          reversibleGatePermutation input) =
      readWires other input := by
  rw [runBasis_decrementWordMod2PowInPlaceCircuit word scratches input enoughScratch
    layoutNodup scratchZero]
  apply List.map_congr_left
  intro wire otherMember
  apply decrementWordBorrowSequenceReference_outside [] word wire input
  intro wordMember
  exact (List.disjoint_left.mp disjoint) wordMember otherMember

/--
`rowEventMoveBackward`は任意の`q`でarrival wordの指定座標だけを周期decrementし、
もう一方の座標を保存する。
-/
theorem runBasis_rowEventMoveBackward_readWires
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false) :
    readWires (oracleMovedWires p)
        ((rowEventMoveBackward p offset).runBasis
          reversibleGatePermutation input) =
      rowEventMovedBitsReference p offset
        (readWires (oracleMovedWires p) input) := by
  let moved := oracleMovedWires p
  let lower := moved.take p.q
  let higher := moved.drop p.q
  let scratches := decoderAndScratchWires p
  have movedNodup : moved.Nodup := by
    simpa [moved] using oracleMovedWires_nodup p
  have scratchNodup : scratches.Nodup := by
    simpa [scratches] using
      (List.Nodup.sublist (by simp) (decoderAndScratchFlags_nodup p))
  have movedScratch : moved.Disjoint scratches := by
    simpa [moved, scratches] using
      oracleMovedWires_disjoint_decoderAndScratch p
  have lowerNodup : lower.Nodup := by
    exact List.Pairwise.take movedNodup
  have higherNodup : higher.Nodup := by
    exact List.Pairwise.drop movedNodup
  have lowerHigher : lower.Disjoint higher := by
    exact nodup_take_disjoint_drop moved p.q movedNodup
  have lowerScratch : lower.Disjoint scratches := by
    rw [List.disjoint_left]
    intro wire lowerMember scratchMember
    exact (List.disjoint_left.mp movedScratch)
      (List.mem_of_mem_take lowerMember) scratchMember
  have higherScratch : higher.Disjoint scratches := by
    rw [List.disjoint_left]
    intro wire higherMember scratchMember
    exact (List.disjoint_left.mp movedScratch)
      (List.mem_of_mem_drop higherMember) scratchMember
  have lowerLayout : (lower ++ scratches).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨lowerNodup, scratchNodup, ?_⟩
    intro left leftMember right rightMember equal
    exact (List.disjoint_left.mp lowerScratch) leftMember
      (equal ▸ rightMember)
  have higherLayout : (higher ++ scratches).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨higherNodup, scratchNodup, ?_⟩
    intro left leftMember right rightMember equal
    exact (List.disjoint_left.mp higherScratch) leftMember
      (equal ▸ rightMember)
  have lowerLength : lower.length = p.q := by
    simp [lower, moved, oracleMovedWires_length, QParameters.wordWidth]
    omega
  have higherLength : higher.length = p.q := by
    simp [higher, moved, oracleMovedWires_length, QParameters.wordWidth]
    omega
  have readLowerLength : (readWires lower input).length = p.q := by
    simpa [readWires] using lowerLength
  have scratchEnough := decoderAndScratchWires_wordWidth_le p
  have lowerEnough : lower.length ≤ scratches.length + 2 := by
    simp [lowerLength, scratches, QParameters.wordWidth] at scratchEnough ⊢
    omega
  have higherEnough : higher.length ≤ scratches.length + 2 := by
    simp [higherLength, scratches, QParameters.wordWidth] at scratchEnough ⊢
    omega
  have movedSplit : lower ++ higher = moved := by
    exact List.take_append_drop p.q moved
  by_cases horizontal : offset.val < 4
  · have notVertical : ¬4 ≤ offset.val := by omega
    have lowerResult := readWires_decrementWordMod2PowInPlaceCircuit lower scratches input
      lowerEnough lowerLayout (by simpa [scratches] using scratchZero)
    have higherResult := readWires_decrementWordMod2PowInPlaceCircuit_disjoint
      lower scratches higher input lowerEnough lowerLayout
      (by simpa [scratches] using scratchZero) lowerHigher
    rw [rowEventMoveBackward]
    simp only [notVertical, if_false]
    change readWires moved
        ((decrementWordMod2PowInPlaceCircuit lower scratches).runBasis
          reversibleGatePermutation input) =
      rowEventMovedBitsReference p offset (readWires moved input)
    rw [← movedSplit]
    have afterSplit :
        readWires (lower ++ higher)
            ((decrementWordMod2PowInPlaceCircuit lower scratches).runBasis
              reversibleGatePermutation input) =
          readWires lower
              ((decrementWordMod2PowInPlaceCircuit lower scratches).runBasis
                reversibleGatePermutation input) ++
            readWires higher
              ((decrementWordMod2PowInPlaceCircuit lower scratches).runBasis
                reversibleGatePermutation input) := by
      simp [readWires]
    have inputSplit : readWires (lower ++ higher) input =
        readWires lower input ++ readWires higher input := by
      simp [readWires]
    rw [afterSplit, inputSplit, lowerResult, higherResult]
    simp [rowEventMovedBitsReference, horizontal, readLowerLength]
  · have vertical : 4 ≤ offset.val := by omega
    have higherResult := readWires_decrementWordMod2PowInPlaceCircuit higher scratches input
      higherEnough higherLayout (by simpa [scratches] using scratchZero)
    have lowerResult := readWires_decrementWordMod2PowInPlaceCircuit_disjoint
      higher scratches lower input higherEnough higherLayout
      (by simpa [scratches] using scratchZero) lowerHigher.symm
    rw [rowEventMoveBackward]
    simp only [vertical, if_true]
    have takeHigher : higher.take p.q = higher := by
      rw [← higherLength]
      simp
    rw [takeHigher]
    change readWires moved
        ((decrementWordMod2PowInPlaceCircuit higher scratches).runBasis
          reversibleGatePermutation input) =
      rowEventMovedBitsReference p offset (readWires moved input)
    rw [← movedSplit]
    have afterSplit :
        readWires (lower ++ higher)
            ((decrementWordMod2PowInPlaceCircuit higher scratches).runBasis
              reversibleGatePermutation input) =
          readWires lower
              ((decrementWordMod2PowInPlaceCircuit higher scratches).runBasis
                reversibleGatePermutation input) ++
            readWires higher
              ((decrementWordMod2PowInPlaceCircuit higher scratches).runBasis
                reversibleGatePermutation input) := by
      simp [readWires]
    have inputSplit : readWires (lower ++ higher) input =
        readWires lower input ++ readWires higher input := by
      simp [readWires]
    rw [afterSplit, inputSplit, lowerResult, higherResult]
    simp [rowEventMovedBitsReference, horizontal, readLowerLength]

/-- systemの選択wordをmovedへ複写してpredecessorへ戻す二段の正本回路。 -/
def rowEventMovedComputation (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  .seq (rowEventMovedCopy p slot) (rowEventMoveBackward p offset)

/--
movedとscratchがcleanなら、複写と周期decrementの合成結果は選択system wordの
純粋なpredecessor bit列に一致する。
-/
theorem runBasis_rowEventMovedComputation_readWires
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (movedZero : ∀ wire ∈ oracleMovedWires p, input wire = false)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false) :
    readWires (oracleMovedWires p)
        ((rowEventMovedComputation p slot offset).runBasis
          reversibleGatePermutation input) =
      rowEventMovedBitsReference p offset
        (readWires (registerWordAt p (systemWires p) slot) input) := by
  let copied := (rowEventMovedCopy p slot).runBasis
    reversibleGatePermutation input
  have copySameLength :
      (registerWordAt p (systemWires p) slot).length =
        (oracleMovedWires p).length := by
    rw [registerWordAt_length p (systemWires p) (systemWires_length p) slot]
    simp [oracleMovedWires, QParameters.movedWidth, QParameters.wordWidth]
  have copyDisjoint :
      (registerWordAt p (systemWires p) slot).Disjoint
        (oracleMovedWires p) := by
    rw [List.disjoint_left]
    intro observed sourceMember targetMember
    exact (List.disjoint_left.mp (systemWires_disjoint_oracleMovedWires p))
      (mem_register_of_mem_registerWordAt p (systemWires p) slot sourceMember)
      targetMember
  have copiedScratchZero : ∀ wire ∈ decoderAndScratchWires p,
      copied wire = false := by
    intro wire scratchMember
    have outsideMoved : wire ∉ oracleMovedWires p := by
      intro movedMember
      exact (List.disjoint_left.mp
        (oracleMovedWires_disjoint_decoderAndScratch p))
          movedMember scratchMember
    have preserved := runBasis_validatedXorCopyLists_outside
      (registerWordAt p (systemWires p) slot) (oracleMovedWires p) input
      (registerWordAt_nodup_of_nodup p (systemWires p) slot
        (systemWires_nodup p)) (oracleMovedWires_nodup p) copySameLength
      copyDisjoint wire outsideMoved
    change copied wire = false
    simpa [copied, rowEventMovedCopy] using
      preserved.trans (scratchZero wire scratchMember)
  have movedResult := runBasis_rowEventMoveBackward_readWires p offset copied
    copiedScratchZero
  have copiedResult := runBasis_rowEventMovedCopy_readWires p slot input movedZero
  rw [rowEventMovedComputation, runBasis_seq]
  change readWires (oracleMovedWires p)
      ((rowEventMoveBackward p offset).runBasis
        reversibleGatePermutation copied) = _
  rw [movedResult, copiedResult]

/--
選択system wordがarrival siteを表すとき、複写・decrement正本回路のmoved出力は
数学的な`moveSiteBackward` sourceを表す。
-/
theorem runBasis_rowEventMovedComputation_site
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (arrival : QSite p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (arrivalWord :
      readWires (registerWordAt p (systemWires p) slot) input =
        siteWordBits p arrival)
    (movedZero : ∀ wire ∈ oracleMovedWires p, input wire = false)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false) :
    readWires (oracleMovedWires p)
        ((rowEventMovedComputation p slot offset).runBasis
          reversibleGatePermutation input) =
      siteWordBits p
        (moveSiteBackward arrival (rowEventDirection offset)) := by
  rw [runBasis_rowEventMovedComputation_readWires p slot offset input
    movedZero scratchZero, arrivalWord]
  exact rowEventMovedBitsReference_site p offset arrival

/--
合法配置とpredecessor sourceを保持する状態では、row membership正本のabsent bitは
`source ∉ configuration`という集合条件に一致する。
-/
theorem runBasis_rowEventMembership_absent_configuration
    (p : QParameters) (configuration : QConfiguration p)
    (source : QSite p) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (systemWires p)
      configuration source input)
    (slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input)
    (flagsClean : MembershipFlagsClean p input) :
    (rowEventMembership p slot).runBasis reversibleGatePermutation input
        (oracleAbsentWire p) =
      decide (source ∉ configuration.1) := by
  calc
    (rowEventMembership p slot).runBasis reversibleGatePermutation input
          (oracleAbsentWire p) =
        noMembershipMatch p (systemWires p) input := by
          simpa [rowEventMembership] using
            runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_absent p (systemWires p)
              (systemWires_membershipInputLayout p) slot false input
              slotClean flagsClean
    _ = decide (source ∉ configuration.1) :=
      noMembershipMatch_configuration p (systemWires p) configuration source
        input specification

/-- predecessor sourceが既に配置内なら、実membership回路は偽predecessorを拒否する。 -/
theorem runBasis_rowEventMembership_falsePredecessor
    (p : QParameters) (configuration : QConfiguration p)
    (source : QSite p) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (systemWires p)
      configuration source input)
    (slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input)
    (flagsClean : MembershipFlagsClean p input)
    (sourcePresent : source ∈ configuration.1) :
    (rowEventMembership p slot).runBasis reversibleGatePermutation input
        (oracleAbsentWire p) = false := by
  rw [runBasis_rowEventMembership_absent_configuration p configuration source
    slot input specification slotClean flagsClean]
  simp [sourcePresent]

/-- predecessor sourceが配置外なら、実membership回路のabsent bitは真になる。 -/
theorem runBasis_rowEventMembership_accepts_absent
    (p : QParameters) (configuration : QConfiguration p)
    (source : QSite p) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (systemWires p)
      configuration source input)
    (slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input)
    (flagsClean : MembershipFlagsClean p input)
    (sourceAbsent : source ∉ configuration.1) :
    (rowEventMembership p slot).runBasis reversibleGatePermutation input
        (oracleAbsentWire p) = true := by
  rw [runBasis_rowEventMembership_absent_configuration p configuration source
    slot input specification slotClean flagsClean]
  simp [sourceAbsent]

/-- 同じwire列の読出しが等しければ、その列に属する各wireの値も等しい。 -/
theorem readWires_eq_at_of_eq
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (left right : JointBasis ancillaQubits systemQubits)
    (equal : readWires wires left = readWires wires right) :
    ∀ {wire}, wire ∈ wires → left wire = right wire := by
  induction wires with
  | nil => simp
  | cons head tail inductionHypothesis =>
      intro wire member
      have parts : left head = right head ∧
          readWires tail left = readWires tail right := by
        simpa [readWires] using List.cons.inj equal
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact parts.1
      · exact inductionHypothesis parts.2 tailMember

/-- branchが偽なら、moved selector純粋foldの各slotは無効である。 -/
theorem xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_of_branch_false
    (p : QParameters) (offset : Nat)
    (slots : List (Fin p.K))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (bits : List Bool)
    (branchFalse : input (oracleBranchWire p) = false) :
    xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset slots input bits = bits := by
  induction slots generalizing bits with
  | nil => rfl
  | cons slot slots inductionHypothesis =>
      rw [xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_cons]
      have disabled : movedSelectorSlotEnabled p slot input = false := by
        simp [movedSelectorSlotEnabled, branchFalse]
      rw [disabled]
      simp
      exact inductionHypothesis bits

/--
静的layoutとclean workの下でbranchが偽なら、moved selector正本回路全体は恒等である。
-/
theorem runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_of_branch_false
    (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layouts : ∀ slot : Fin p.K,
      WriteMovedSelectorSlotLayout p slot outputSelector)
    (clean : WriteMovedSelectorSlotClean p input)
    (branchFalse : input (oracleBranchWire p) = false) :
    (xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector).runBasis
        reversibleGatePermutation input = input := by
  rw [runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_slotFold]
  let finalState := (List.finRange p.K).foldl (fun state slot =>
    (xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit p offset outputSelector slot).runBasis
      reversibleGatePermutation state) input
  have result := runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitSlotList_correct p offset
    outputSelector input layouts clean (List.finRange p.K) input (by
      intro wire outside
      rfl)
  have readEqual : readWires outputSelector finalState =
      readWires outputSelector input := by
    have referenceIdentity := xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_of_branch_false
      p offset (List.finRange p.K) input (readWires outputSelector input)
      branchFalse
    simpa [finalState, referenceIdentity] using result.1
  have outsideEqual : BasisAgreeOutside outputSelector finalState input := by
    simpa [finalState] using result.2
  change finalState = input
  funext wire
  by_cases member : wire ∈ outputSelector
  · exact readWires_eq_at_of_eq outputSelector finalState input readEqual member
  · exact outsideEqual wire member

/-- 無効な制御ではsorted dataの純粋有限foldは入力を変更しない。 -/
theorem writeSortedDataReference_false
    (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    writeSortedDataReference p output outputDegree outputDegreeLe false input =
      input := by
  unfold writeSortedDataReference
  generalize slotsEq : List.finRange outputDegree = slots
  induction slots generalizing input with
  | nil => rfl
  | cons slot slots inductionHypothesis =>
      simp only [List.foldl_cons]
      simp [writeSortedCopyReference]

/-- branchが偽なら、一つのsorted degree参照作用は恒等である。 -/
theorem writeSortedDegreeReference_of_branch_false
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchFalse : input (oracleBranchWire p) = false) :
    writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeSlot degreeChange input =
      input := by
  simp [writeSortedDegreeReference, branchFalse, writeSortedUseReference,
    writeSortedDataReference_false, toggleOutputIndexReference]
  intro _ _
  split <;> rfl

/-- branchが偽なら、全degreeのsorted純粋有限foldは恒等である。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_of_branch_false
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchFalse : input (oracleBranchWire p) = false) :
    SortedCandidatesDelimiterOutputXorSpec p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeChange input = input := by
  unfold SortedCandidatesDelimiterOutputXorSpec
  generalize slotsEq : List.finRange p.K = slots
  clear slotsEq
  induction slots generalizing input with
  | nil => rfl
  | cons degreeSlot slots inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [writeSortedDegreeReference_of_branch_false p kind degreeSlot
        degreeChange input branchFalse]
      exact inductionHypothesis input branchFalse

/-- clean workでbranchが偽なら、canonical sorted出力正本回路は恒等である。 -/
theorem runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_of_branch_false
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (pairZero : input (oraclePairWire p) = false)
    (branchFalse : input (oracleBranchWire p) = false) :
    (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) degreeChange).runBasis
        reversibleGatePermutation input = input := by
  rw [runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical p kind degreeChange input
    scratchZero pairZero]
  exact xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_of_branch_false p kind degreeChange input
    branchFalse

/--
clean workでbranchが偽なら、row event useのsorted出力とmoved selector出力はともに
恒等となる。
-/
theorem xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_of_branch_false
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layouts : ∀ slot : Fin p.K,
      WriteMovedSelectorSlotLayout p slot (columnSelectorWires p))
    (clean : WriteMovedSelectorSlotClean p input)
    (branchFalse : input (oracleBranchWire p) = false) :
    (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input = input := by
  let degreeChange : Int := if offset.val % 2 = 1 then 1 else 0
  have sortedIdentity := runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_of_branch_false p
    .columnKey degreeChange input clean.scratch_zero clean.pair_zero branchFalse
  have sortedActual :
      (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p) degreeChange).runBasis
          reversibleGatePermutation input = input := by
    simpa [canonicalSortedOutputWires, canonicalSortedOutputActive] using
      sortedIdentity
  have selectorIdentity := runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_of_branch_false p
    offset.val (columnSelectorWires p) input layouts clean branchFalse
  simp only [xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit, runBasis_seq]
  change (xorMovedMemberPositionIntoSelectorOutputCircuit p offset.val (columnSelectorWires p)).runBasis
      reversibleGatePermutation
        ((xorSortedCandidatesAsDelimiterIntoOutputCircuit p (columnKeyWires p)
          (by simp [columnKeyWires]) (keySignalWire p) degreeChange).runBasis
            reversibleGatePermutation input) = input
  rw [sortedActual]
  exact selectorIdentity

/--
row event compute後のbranchが偽でuse用workがcleanなら、外側の
compute--use--uncomputeは入力全体を厳密に復元する。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_computed
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input computed : JointBasis p.ancillaWidth p.systemWidth)
    (computeRun :
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
        computed)
    (layouts : ∀ sortedSlot : Fin p.K,
      WriteMovedSelectorSlotLayout p sortedSlot (columnSelectorWires p))
    (clean : WriteMovedSelectorSlotClean p computed)
    (branchFalse : computed (oracleBranchWire p) = false) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  rw [applyRowEventReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
  apply Circuit.computeUseUncompute_clean id reversibleGatePermutation
    (by intro gate; cases gate <;> rfl)
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset) input input
  change (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
      ((computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis
        reversibleGatePermutation input) =
    (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis
      reversibleGatePermutation input
  rw [computeRun]
  exact xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_of_branch_false p offset computed layouts clean branchFalse

/--
正本computeの実際の最終状態でbranchが偽なら、row event分岐全体は恒等である。
この等式はselected・branch・candidate・sort workを含む全wireの復元を同時に述べる。
-/
theorem applyRowEventReferenceAndRestoreWorkCircuit_inactive
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layouts : ∀ sortedSlot : Fin p.K,
      WriteMovedSelectorSlotLayout p sortedSlot (columnSelectorWires p))
    (clean : WriteMovedSelectorSlotClean p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)
    (branchFalse :
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
        (oracleBranchWire p) = false) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  apply applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_computed p slot offset input
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
  · exact (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output p slot offset input).symm
  · exact layouts
  · exact clean
  · exact branchFalse

/-- inactive row event分岐は物理system registerを点ごとに保存する。 -/
theorem applyRowEventReferenceAndRestoreWorkCircuit_inactive_system
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layouts : ∀ sortedSlot : Fin p.K,
      WriteMovedSelectorSlotLayout p sortedSlot (columnSelectorWires p))
    (clean : WriteMovedSelectorSlotClean p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)
    (branchFalse :
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
        (oracleBranchWire p) = false) :
    readWires (systemWires p)
        ((applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
          reversibleGatePermutation input) =
      readWires (systemWires p) input := by
  rw [applyRowEventReferenceAndRestoreWorkCircuit_inactive p slot offset input layouts clean branchFalse]

/-- inactive row event分岐はrow selector registerを点ごとに保存する。 -/
theorem applyRowEventReferenceAndRestoreWorkCircuit_inactive_rowSelector
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layouts : ∀ sortedSlot : Fin p.K,
      WriteMovedSelectorSlotLayout p sortedSlot (columnSelectorWires p))
    (clean : WriteMovedSelectorSlotClean p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)
    (branchFalse :
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
        (oracleBranchWire p) = false) :
    readWires (rowSelectorWires p)
        ((applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
          reversibleGatePermutation input) =
      readWires (rowSelectorWires p) input := by
  rw [applyRowEventReferenceAndRestoreWorkCircuit_inactive p slot offset input layouts clean branchFalse]

/-- inactive row event分岐はoracle内部work全体を入力値へ復元する。 -/
theorem applyRowEventReferenceAndRestoreWorkCircuit_inactive_internalWork
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layouts : ∀ sortedSlot : Fin p.K,
      WriteMovedSelectorSlotLayout p sortedSlot (columnSelectorWires p))
    (clean : WriteMovedSelectorSlotClean p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)
    (branchFalse :
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
        (oracleBranchWire p) = false) :
    readWires (diagonalOracleWorkWires p)
        ((applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
          reversibleGatePermutation input) =
      readWires (diagonalOracleWorkWires p) input := by
  rw [applyRowEventReferenceAndRestoreWorkCircuit_inactive p slot offset input layouts clean branchFalse]

/-- canonical配置では、branch偽のrow event use恒等性にlayout仮定は不要である。 -/
theorem xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_of_branch_false_canonical
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : WriteMovedSelectorSlotClean p input)
    (branchFalse : input (oracleBranchWire p) = false) :
    (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation input = input := by
  exact xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit_of_branch_false p offset input
    (MovedMemberPositionSelectorOutputLayout_columnSelector_canonical p) clean branchFalse

/-- canonical配置では、compute後branch偽ならrow event分岐全体が厳密に恒等である。 -/
theorem applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_computed_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input computed : JointBasis p.ancillaWidth p.systemWidth)
    (computeRun :
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
        computed)
    (clean : WriteMovedSelectorSlotClean p computed)
    (branchFalse : computed (oracleBranchWire p) = false) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  exact applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_computed p slot offset input computed
    computeRun (MovedMemberPositionSelectorOutputLayout_columnSelector_canonical p) clean
    branchFalse

/-- canonical配置の正本compute最終状態でbranch偽なら、row event分岐は厳密に恒等である。 -/
theorem applyRowEventReferenceAndRestoreWorkCircuit_inactive_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : WriteMovedSelectorSlotClean p
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)
    (branchFalse :
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
        (oracleBranchWire p) = false) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  exact applyRowEventReferenceAndRestoreWorkCircuit_inactive p slot offset input
    (MovedMemberPositionSelectorOutputLayout_columnSelector_canonical p) clean branchFalse

/-- row event selector定数との一致を表す純粋なBool条件。 -/
def rowEventSelectorMatches (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Bool :=
  diagonalSelectorMatches (rowSelectorWires p)
    (6 * slot.val + offset.val) input

/-- clean scratch上でrow event selector比較正本は純粋一致条件に一致する。 -/
theorem runBasis_rowEventSelectorCompute
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false) :
    (rowEventSelectorCompute p slot offset).runBasis
        reversibleGatePermutation input =
      if rowEventSelectorMatches p slot offset input then
        xBasisAction (oracleSelectedWire p) input
      else input := by
  have result := runBasis_selectorEqualsConstant_bits (rowSelectorWires p)
    (decoderAndScratchWires p) (6 * slot.val + offset.val)
    (oracleSelectedWire p) input
    (by simpa [rowSelectorWires] using
      selectorWidth_le_decoderAndScratch_add_one p)
    (rowSelector_decoderScratch_selected_nodup p) scratchZero
  simpa [rowEventSelectorCompute, rowEventSelectorMatches,
    diagonalSelectorMatches] using result

/-- row event branch多重制御に渡すwire列。 -/
def rowEventBranchControls (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  [oracleLegalWire p, oracleSelectedWire p,
    oraclePresentWireAt p slot, oracleAbsentWire p] ++
      if offset.val % 2 = 1 then [oracleDegreeConditionWire p] else []

/-- canonical oracle layoutはrow event branchの全制御・scratch・target非重複条件を満たす。 -/
theorem rowEventBranchControls_layout_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    (rowEventBranchControls p slot offset ++ decoderAndScratchWires p ++
      [oracleBranchWire p]).Nodup := by
  let legal := oracleLegalWire p
  let selected := oracleSelectedWire p
  let present := oraclePresentWireAt p slot
  let absent := oracleAbsentWire p
  let degree := oracleDegreeConditionWire p
  let branch := oracleBranchWire p
  let scratch := decoderAndScratchWires p
  let legalSlice := (OracleWorkLayout.canonical p).legal
  let selectedSlice := (OracleWorkLayout.canonical p).selected
  let presentSlice := (OracleWorkLayout.canonical p).present
  let absentSlice := (OracleWorkLayout.canonical p).absent
  let degreeSlice := (OracleWorkLayout.canonical p).degreeCondition
  let branchSlice := (OracleWorkLayout.canonical p).branch
  have base := diagonalBranch_controls_scratch_branch_nodup p slot
  have basePrefixScratch : ([legal, selected, present] ++ scratch).Nodup := by
    simpa [legal, selected, present, branch, scratch] using
      (List.nodup_append.mp base).1
  have baseControlsNodup : [legal, selected, present].Nodup :=
    (List.nodup_append.mp basePrefixScratch).1
  have scratchNodup : scratch.Nodup :=
    (List.nodup_append.mp basePrefixScratch).2.1
  have baseControlsScratchSeparated :
      ∀ left ∈ [legal, selected, present], ∀ right ∈ scratch, left ≠ right :=
    (List.nodup_append.mp basePrefixScratch).2.2
  have basePrefixBranchSeparated :
      ∀ left ∈ [legal, selected, present] ++ scratch,
        ∀ right ∈ [branch], left ≠ right := by
    simpa [legal, selected, present, branch, scratch] using
      (List.nodup_append.mp base).2.2
  have absentNeLegal : absent ≠ legal := by
    simpa [absent, legal, absentSlice, legalSlice, oracleAbsentWire,
      oracleSingletonWire, oracleLegalWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p absentSlice legalSlice 0 0
        (by simp [absentSlice, legalSlice, OracleWorkLayout.canonical]; omega)
  have absentNeSelected : absent ≠ selected := by
    simpa [absent, selected, absentSlice, selectedSlice, oracleAbsentWire,
      oracleSelectedWire, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p absentSlice selectedSlice 0 0
        (by simp [absentSlice, selectedSlice, OracleWorkLayout.canonical]; omega)
  have absentNePresent : absent ≠ present := by
    simpa [absent, present, absentSlice, presentSlice, oracleAbsentWire,
      oraclePresentWireAt, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p absentSlice presentSlice 0 slot
        (by simp [absentSlice, presentSlice, OracleWorkLayout.canonical]; omega)
  have degreeNeLegal : degree ≠ legal := by
    simpa [degree, legal, degreeSlice, legalSlice, oracleDegreeConditionWire,
      oracleSingletonWire, oracleLegalWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p degreeSlice legalSlice 0 0
        (by simp [degreeSlice, legalSlice, OracleWorkLayout.canonical]; omega)
  have degreeNeSelected : degree ≠ selected := by
    simpa [degree, selected, degreeSlice, selectedSlice,
      oracleDegreeConditionWire, oracleSelectedWire, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p degreeSlice selectedSlice 0 0
        (by simp [degreeSlice, selectedSlice, OracleWorkLayout.canonical]; omega)
  have degreeNePresent : degree ≠ present := by
    simpa [degree, present, degreeSlice, presentSlice,
      oracleDegreeConditionWire, oraclePresentWireAt, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p degreeSlice presentSlice 0 slot
        (by simp [degreeSlice, presentSlice, OracleWorkLayout.canonical]; omega)
  have degreeNeAbsent : degree ≠ absent := by
    simpa [degree, absent, degreeSlice, absentSlice,
      oracleDegreeConditionWire, oracleAbsentWire, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p degreeSlice absentSlice 0 0
        (by simp [degreeSlice, absentSlice, OracleWorkLayout.canonical]; omega)
  have absentNeBranch : absent ≠ branch := by
    simpa [absent, branch, absentSlice, branchSlice, oracleAbsentWire,
      oracleBranchWire, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p absentSlice branchSlice 0 0
        (by simp [absentSlice, branchSlice, OracleWorkLayout.canonical]; omega)
  have degreeNeBranch : degree ≠ branch := by
    simpa [degree, branch, degreeSlice, branchSlice,
      oracleDegreeConditionWire, oracleBranchWire, oracleSingletonWire] using
      oracleSlice_ancillaWire_ne_of_localIndex_ne p degreeSlice branchSlice 0 0
        (by simp [degreeSlice, branchSlice, OracleWorkLayout.canonical]; omega)
  have absentScratch : absent ∉ scratch := by
    intro member
    have disjoint := oracleSlice_disjoint_decoderAndScratch p absentSlice
      (by simp [absentSlice, OracleWorkLayout.canonical]; omega)
    have absentMember : absent ∈
        ((QLayout.oracleSlice absentSlice).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      change (QLayout.oracleSlice absentSlice).ancillaWire 0 ∈ _
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
    exact (List.disjoint_left.mp disjoint) absentMember member
  have degreeScratch : degree ∉ scratch := by
    intro member
    have disjoint := oracleSlice_disjoint_decoderAndScratch p degreeSlice
      (by simp [degreeSlice, OracleWorkLayout.canonical]; omega)
    have degreeMember : degree ∈
        ((QLayout.oracleSlice degreeSlice).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      change (QLayout.oracleSlice degreeSlice).ancillaWire 0 ∈ _
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
    exact (List.disjoint_left.mp disjoint) degreeMember member
  have controlsFour : [legal, selected, present, absent].Nodup := by
    have appended : ([legal, selected, present] ++ [absent]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨baseControlsNodup, by simp, ?_⟩
      intro left leftMember right rightMember
      have rightEq : right = absent := by simpa using rightMember
      subst right
      simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember
      rcases leftMember with rfl | rfl | rfl
      · exact absentNeLegal.symm
      · exact absentNeSelected.symm
      · exact absentNePresent.symm
    simpa using appended
  by_cases collision : offset.val % 2 = 1
  · have controlsFive : [legal, selected, present, absent, degree].Nodup := by
      have appended : ([legal, selected, present, absent] ++ [degree]).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨controlsFour, by simp, ?_⟩
        intro left leftMember right rightMember
        have rightEq : right = degree := by simpa using rightMember
        subst right
        simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember
        rcases leftMember with rfl | rfl | rfl | rfl
        · exact degreeNeLegal.symm
        · exact degreeNeSelected.symm
        · exact degreeNePresent.symm
        · exact degreeNeAbsent.symm
      simpa using appended
    have controlsScratch :
        ([legal, selected, present, absent, degree] ++ scratch).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨controlsFive, scratchNodup, ?_⟩
      intro left leftMember right rightMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember
      rcases leftMember with rfl | rfl | rfl | rfl | rfl
      · exact baseControlsScratchSeparated legal (by simp) right rightMember
      · exact baseControlsScratchSeparated selected (by simp) right rightMember
      · exact baseControlsScratchSeparated present (by simp) right rightMember
      · intro equal
        exact absentScratch (equal ▸ rightMember)
      · intro equal
        exact degreeScratch (equal ▸ rightMember)
    have full :
        ([legal, selected, present, absent, degree] ++ scratch ++ [branch]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨controlsScratch, by simp, ?_⟩
      intro left leftMember right rightMember
      have rightEq : right = branch := by simpa using rightMember
      subst right
      rcases List.mem_append.mp leftMember with controlMember | scratchMember
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at controlMember
        rcases controlMember with rfl | rfl | rfl | rfl | rfl
        · exact basePrefixBranchSeparated legal (by simp) branch (by simp)
        · exact basePrefixBranchSeparated selected (by simp) branch (by simp)
        · exact basePrefixBranchSeparated present (by simp) branch (by simp)
        · exact absentNeBranch
        · exact degreeNeBranch
      · exact basePrefixBranchSeparated left
          (List.mem_append_right _ scratchMember) branch (by simp)
    simpa [rowEventBranchControls, collision, legal, selected, present,
      absent, degree, branch, scratch] using full
  · have controlsScratch :
        ([legal, selected, present, absent] ++ scratch).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨controlsFour, scratchNodup, ?_⟩
      intro left leftMember right rightMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember
      rcases leftMember with rfl | rfl | rfl | rfl
      · exact baseControlsScratchSeparated legal (by simp) right rightMember
      · exact baseControlsScratchSeparated selected (by simp) right rightMember
      · exact baseControlsScratchSeparated present (by simp) right rightMember
      · intro equal
        exact absentScratch (equal ▸ rightMember)
    have full :
        ([legal, selected, present, absent] ++ scratch ++ [branch]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨controlsScratch, by simp, ?_⟩
      intro left leftMember right rightMember
      have rightEq : right = branch := by simpa using rightMember
      subst right
      rcases List.mem_append.mp leftMember with controlMember | scratchMember
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at controlMember
        rcases controlMember with rfl | rfl | rfl | rfl
        · exact basePrefixBranchSeparated legal (by simp) branch (by simp)
        · exact basePrefixBranchSeparated selected (by simp) branch (by simp)
        · exact basePrefixBranchSeparated present (by simp) branch (by simp)
        · exact absentNeBranch
      · exact basePrefixBranchSeparated left
          (List.mem_append_right _ scratchMember) branch (by simp)
    simpa [rowEventBranchControls, collision, legal, selected, present,
      absent, branch, scratch] using full

/-- row event branch制御本数にはcanonical AND scratchが十分である。 -/
theorem rowEventBranchControls_enoughScratch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    (rowEventBranchControls p slot offset).length ≤
      (decoderAndScratchWires p).length + 1 := by
  by_cases collision : offset.val % 2 = 1 <;>
    simp [rowEventBranchControls, collision, decoderAndScratchWires,
      oracleAndWorkWires, QParameters.andWorkWidth, QParameters.wordWidth] <;>
    omega

/--
静的な非重複配置とclean scratchの下で、row event branch正本は制御論理積を
branch bitへXORする。
-/
theorem runBasis_rowEventBranchCompute
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (rowEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input =
      if allWiresTrue (rowEventBranchControls p slot offset) input then
        xBasisAction (oracleBranchWire p) input
      else input := by
  have result := runBasis_positiveMultiControlledX
    (rowEventBranchControls p slot offset) (decoderAndScratchWires p)
    (oracleBranchWire p) input
    (rowEventBranchControls_enoughScratch p slot offset)
    layoutNodup scratchZero
  simpa [rowEventBranchCompute, rowEventBranchControls] using result

/-- canonical配置では、row event branch正本の制御論理積仕様は外部の配置仮定を要しない。 -/
theorem runBasis_rowEventBranchCompute_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input =
      if allWiresTrue (rowEventBranchControls p slot offset) input then
        xBasisAction (oracleBranchWire p) input
      else input := by
  exact runBasis_rowEventBranchCompute p slot offset input
    (rowEventBranchControls_layout_canonical p slot offset) scratchZero

/-- branch bitがcleanなら、branch計算後の値は全制御の論理積そのものである。 -/
theorem runBasis_rowEventBranchCompute_branch
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (rowEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) =
      allWiresTrue (rowEventBranchControls p slot offset) input := by
  rw [runBasis_rowEventBranchCompute p slot offset input layoutNodup scratchZero]
  by_cases enabled : allWiresTrue (rowEventBranchControls p slot offset) input
  · simp [enabled, xBasisAction, branchZero]
  · have disabled := Bool.eq_false_of_not_eq_true enabled
    simp [disabled, branchZero]

/-- canonical配置でbranch bitがcleanなら、計算後の値は全制御の論理積である。 -/
theorem runBasis_rowEventBranchCompute_branch_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) =
      allWiresTrue (rowEventBranchControls p slot offset) input := by
  exact runBasis_rowEventBranchCompute_branch p slot offset input
    (rowEventBranchControls_layout_canonical p slot offset) scratchZero branchZero

/-- legal制御が偽ならrow event branch計算後のbranch bitも偽である。 -/
theorem runBasis_rowEventBranchCompute_false_of_legal
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (rowEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (legalFalse : input (oracleLegalWire p) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_rowEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [rowEventBranchControls, allWiresTrue, readWires, legalFalse]

/-- selected制御が偽ならpadding・selector不一致branchは受理されない。 -/
theorem runBasis_rowEventBranchCompute_false_of_selected
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (rowEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (selectedFalse : input (oracleSelectedWire p) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_rowEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [rowEventBranchControls, allWiresTrue, readWires, selectedFalse]

/-- present制御が偽なら範囲外slot branchは受理されない。 -/
theorem runBasis_rowEventBranchCompute_false_of_present
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (rowEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (presentFalse : input (oraclePresentWireAt p slot) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_rowEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [rowEventBranchControls, allWiresTrue, readWires, presentFalse]

/-- absent制御が偽なら偽predecessor branchは受理されない。 -/
theorem runBasis_rowEventBranchCompute_false_of_absent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (rowEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (absentFalse : input (oracleAbsentWire p) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_rowEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [rowEventBranchControls, allWiresTrue, readWires, absentFalse]

/-- collisionでdegree条件が偽なら満杯境界branchは受理されない。 -/
theorem runBasis_rowEventBranchCompute_false_of_degree
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layoutNodup :
      (rowEventBranchControls p slot offset ++ decoderAndScratchWires p ++
        [oracleBranchWire p]).Nodup)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (collision : offset.val % 2 = 1)
    (degreeFalse : input (oracleDegreeConditionWire p) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [runBasis_rowEventBranchCompute_branch p slot offset input layoutNodup
    scratchZero branchZero]
  simp [rowEventBranchControls, collision, allWiresTrue, readWires, degreeFalse]

/-- canonical配置ではlegal制御が偽ならbranch bitも偽である。 -/
theorem runBasis_rowEventBranchCompute_false_of_legal_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (legalFalse : input (oracleLegalWire p) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_rowEventBranchCompute_false_of_legal p slot offset input
    (rowEventBranchControls_layout_canonical p slot offset) scratchZero branchZero
    legalFalse

/-- canonical配置ではselected制御が偽ならpadding・selector不一致branchは受理されない。 -/
theorem runBasis_rowEventBranchCompute_false_of_selected_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (selectedFalse : input (oracleSelectedWire p) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_rowEventBranchCompute_false_of_selected p slot offset input
    (rowEventBranchControls_layout_canonical p slot offset) scratchZero branchZero
    selectedFalse

/-- canonical配置ではpresent制御が偽なら範囲外slot branchは受理されない。 -/
theorem runBasis_rowEventBranchCompute_false_of_present_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (presentFalse : input (oraclePresentWireAt p slot) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_rowEventBranchCompute_false_of_present p slot offset input
    (rowEventBranchControls_layout_canonical p slot offset) scratchZero branchZero
    presentFalse

/-- canonical配置ではabsent制御が偽なら偽predecessor branchは受理されない。 -/
theorem runBasis_rowEventBranchCompute_false_of_absent_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (absentFalse : input (oracleAbsentWire p) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_rowEventBranchCompute_false_of_absent p slot offset input
    (rowEventBranchControls_layout_canonical p slot offset) scratchZero branchZero
    absentFalse

/-- canonical配置のcollisionではdegree条件が偽なら満杯境界branchは受理されない。 -/
theorem runBasis_rowEventBranchCompute_false_of_degree_canonical
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      input wire = false)
    (branchZero : input (oracleBranchWire p) = false)
    (collision : offset.val % 2 = 1)
    (degreeFalse : input (oracleDegreeConditionWire p) = false) :
    (rowEventBranchCompute p slot offset).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  exact runBasis_rowEventBranchCompute_false_of_degree p slot offset input
    (rowEventBranchControls_layout_canonical p slot offset) scratchZero branchZero
    collision degreeFalse

/-- active な物理 event の row selector は純粋 row 参照関数で元配置へ戻る。 -/
theorem rowEventReference_active
    {p : QParameters} (input : QConfiguration p)
    (source : QSite p) (member : source ∈ input.1)
    (direction : QDirection) :
    rowReference (eventOutput input source direction)
        (rowSelectorForEvent input source member direction) =
      some ⟨input, selectorForEvent input source member direction⟩ := by
  exact rowReference_rowSelectorForEvent input source member direction

/--
合法配置の event selector に対し、row predecessor が存在する条件は
「逆移動 source が出力配置に存在せず、collision なら degree に空きがある」ことと同値である。
したがって偽 predecessor、`|S|=K` の collision 境界、rep/coll の分岐を一つの式で覆う。
-/
theorem rowReference_eventSelector_isSome_iff
    {p : QParameters} (output : QConfiguration p)
    (arrival : QSite p) (member : arrival ∈ output.1)
    (offset : Fin 6) (eventRange : 2 ≤ offset.val) :
    let selector := selectorOfSlotOffset (slotOfMember output arrival member) offset
    let source := moveSiteBackward arrival (rowEventDirection offset)
    (rowReference output selector).isSome = true ↔
      source ∉ output.1 ∧
        (rowEventCollision offset = false ∨ output.1.card < p.K) := by
  dsimp only
  let slot := slotOfMember output arrival member
  let selector := selectorOfSlotOffset slot offset
  let source := moveSiteBackward arrival (rowEventDirection offset)
  have selected : configurationSlot? output (selectorSlot selector) =
      some ⟨arrival, member⟩ := by
    simp [selector, slot]
  have notDiagonal :
      ¬(selectorOffset
          (selectorOfSlotOffset (slotOfMember output arrival member) offset)).val < 2 := by
    simp
    omega
  have sourceEq :
      moveSiteBackward arrival
          (selectorDirection
            (selectorOfSlotOffset (slotOfMember output arrival member) offset)) =
        source := by
    rw [selectorDirection_of_rowEventOffset]
  have collisionEq :
      selectorRequestsCollision
          (selectorOfSlotOffset (slotOfMember output arrival member) offset) =
        rowEventCollision offset := by
    exact selectorRequestsCollision_of_rowEventOffset _ offset
  unfold rowReference
  split
  · rename_i selectedNone
    rw [selectedNone] at selected
    contradiction
  · rename_i selectedArrival selectedSome
    have arrivalEq : selectedArrival = ⟨arrival, member⟩ := by
      exact Option.some.inj (selectedSome.symm.trans selected)
    subst selectedArrival
    rw [dif_neg notDiagonal]
    dsimp only
    let actualSource := moveSiteBackward arrival
      (selectorDirection
        (selectorOfSlotOffset (slotOfMember output arrival member) offset))
    have actualSourceEq : actualSource = source := sourceEq
    by_cases actualPresent : actualSource ∈ output.1
    · have sourcePresent : source ∈ output.1 := actualSourceEq ▸ actualPresent
      have rowSourcePresent :
          moveSiteBackward arrival (rowEventDirection offset) ∈ output.1 := by
        simpa [source] using sourcePresent
      simp [actualSource, actualPresent]
      intro rowSourceAbsent
      exact (rowSourceAbsent rowSourcePresent).elim
    · have sourceAbsent : source ∉ output.1 := by
        intro sourceMember
        exact actualPresent (actualSourceEq.symm ▸ sourceMember)
      have rowSourceAbsent :
          moveSiteBackward arrival (rowEventDirection offset) ∉ output.1 := by
        simpa [source] using sourceAbsent
      by_cases actualCollision :
          selectorRequestsCollision
            (selectorOfSlotOffset (slotOfMember output arrival member) offset) = true
      · have rowCollision : rowEventCollision offset = true :=
          collisionEq ▸ actualCollision
        simp [actualSource, actualPresent, actualCollision, rowCollision]
        intro _degreeRoom
        exact rowSourceAbsent
      · have actualCollisionFalse :
            selectorRequestsCollision
              (selectorOfSlotOffset (slotOfMember output arrival member) offset) =
                false := Bool.eq_false_of_not_eq_true actualCollision
        have rowCollisionFalse : rowEventCollision offset = false :=
          collisionEq.symm.trans actualCollisionFalse
        simp [actualSource, actualPresent, actualCollisionFalse,
          rowCollisionFalse]
        exact rowSourceAbsent

/-- replacement event は degree が `K` に達していても predecessor を持てる。 -/
theorem rowReference_replacement_boundary_isSome
    {p : QParameters} (output : QConfiguration p)
    (arrival : QSite p) (member : arrival ∈ output.1)
    (offset : Fin 6) (eventRange : 2 ≤ offset.val)
    (replacement : rowEventCollision offset = false)
    (sourceAbsent :
      moveSiteBackward arrival (rowEventDirection offset) ∉ output.1) :
    (rowReference output
      (selectorOfSlotOffset (slotOfMember output arrival member) offset)).isSome = true := by
  have criterion := (rowReference_eventSelector_isSome_iff output arrival member
    offset eventRange).2 ⟨sourceAbsent, Or.inl replacement⟩
  simpa only using criterion

/-- collision event は degree が `K` なら偽 predecessor として拒否される。 -/
theorem rowReference_collision_full_isNone
    {p : QParameters} (output : QConfiguration p)
    (arrival : QSite p) (member : arrival ∈ output.1)
    (offset : Fin 6) (eventRange : 2 ≤ offset.val)
    (collision : rowEventCollision offset = true)
    (full : output.1.card = p.K) :
    rowReference output
      (selectorOfSlotOffset (slotOfMember output arrival member) offset) = none := by
  cases referenceEq : rowReference output
      (selectorOfSlotOffset (slotOfMember output arrival member) offset) with
  | none => rfl
  | some result =>
      exfalso
      have isSome :
          (rowReference output
            (selectorOfSlotOffset (slotOfMember output arrival member) offset)).isSome =
              true := by
        simp [referenceEq]
      have criterion := (rowReference_eventSelector_isSome_iff output arrival member
        offset eventRange).1 isSome
      rcases criterion.2 with collisionFalse | degreeRoom
      · simp [collision] at collisionFalse
      · omega

/-- 逆移動 source がすでに出力配置にあれば rep/coll の双方で拒否される。 -/
theorem rowReference_falsePredecessor_isNone
    {p : QParameters} (output : QConfiguration p)
    (arrival : QSite p) (member : arrival ∈ output.1)
    (offset : Fin 6) (eventRange : 2 ≤ offset.val)
    (sourcePresent :
      moveSiteBackward arrival (rowEventDirection offset) ∈ output.1) :
    rowReference output
      (selectorOfSlotOffset (slotOfMember output arrival member) offset) = none := by
  cases referenceEq : rowReference output
      (selectorOfSlotOffset (slotOfMember output arrival member) offset) with
  | none => rfl
  | some result =>
      exfalso
      have isSome :
          (rowReference output
            (selectorOfSlotOffset (slotOfMember output arrival member) offset)).isSome =
              true := by
        simp [referenceEq]
      have criterion := (rowReference_eventSelector_isSome_iff output arrival member
        offset eventRange).1 isSome
      exact criterion.1 sourcePresent

end ReversibleCircuit

end ProbabilityGeneratorQProof
