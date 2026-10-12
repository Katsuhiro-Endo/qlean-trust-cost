import QLean.Generator.Implementation.QOracleColumnEventBranchCorrectness
import QLean.Generator.Implementation.QOracleRowEventBranchCorrectness

/-!
# Q oracle event compute の疎な局所性

column/row event の compute 部分が参照する wire を、永続入力 register と oracle work に
限定する。証明は回路構文木を直接合成し、巨大行列や計算基底の列挙を用いない。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- XOR copy は source・target を含む support 内だけを使う。 -/
theorem circuitUsesOnly_xorCopy
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    ∀ (source target : List (Wire ancillaQubits systemQubits)),
      (∀ wire ∈ source, wire ∈ support) →
      (∀ wire ∈ target, wire ∈ support) →
      circuitUsesOnly support (xorCopy source target)
  | [], _, _, _ => by simp [xorCopy, circuitUsesOnly]
  | _ :: _, [], _, _ => by simp [xorCopy, circuitUsesOnly]
  | source :: sources, target :: targets, sourceMembers, targetMembers => by
      simp only [xorCopy, circuitUsesOnly]
      constructor
      · exact circuitUsesOnly_safeCnot support source target
          (sourceMembers source (by simp)) (targetMembers target (by simp))
      · exact circuitUsesOnly_xorCopy support sources targets
          (by intro wire member; exact sourceMembers wire (by simp [member]))
          (by intro wire member; exact targetMembers wire (by simp [member]))

/-- 制御 XOR copy は control・source・target を含む support 内だけを使う。 -/
theorem circuitUsesOnly_controlledXorCopy
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (controlMember : control ∈ support)
    (sourceMembers : ∀ wire ∈ source, wire ∈ support)
    (targetMembers : ∀ wire ∈ target, wire ∈ support) :
    circuitUsesOnly support (controlledXorCopy control source target) := by
  induction source generalizing target with
  | nil =>
      change circuitUsesOnly support (Circuit.sequence [])
      exact circuitUsesOnly_sequence support [] (by simp)
  | cons source sources inductionHypothesis =>
      cases target with
      | nil =>
          change circuitUsesOnly support (Circuit.sequence [])
          exact circuitUsesOnly_sequence support [] (by simp)
      | cons target targets =>
          simp only [controlledXorCopy, List.zip_cons_cons, List.map_cons,
            Circuit.sequence]
          constructor
          · exact circuitUsesOnly_safeToffoli support control source target
              controlMember (sourceMembers source (by simp))
                (targetMembers target (by simp))
          · exact inductionHypothesis targets
              (by intro wire member; exact sourceMembers wire (by simp [member]))
              (by intro wire member; exact targetMembers wire (by simp [member]))

/-- lower controls を蓄積する increment は word・scratch の support 内だけを使う。 -/
theorem circuitUsesOnly_incrementWordCarrySequenceCircuit
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    ∀ (lower higher scratch : List (Wire ancillaQubits systemQubits)),
      (∀ wire ∈ lower, wire ∈ support) →
      (∀ wire ∈ higher, wire ∈ support) →
      (∀ wire ∈ scratch, wire ∈ support) →
      circuitUsesOnly support
        (incrementWordCarrySequenceCircuit lower higher scratch)
  | _, [], _, _, _, _ => by simp [incrementWordCarrySequenceCircuit, circuitUsesOnly]
  | lower, target :: higher, scratch, lowerMembers, higherMembers, scratchMembers => by
      simp only [incrementWordCarrySequenceCircuit, circuitUsesOnly]
      constructor
      · apply circuitUsesOnly_incrementWordCarrySequenceCircuit support
          (lower ++ [target]) higher scratch
        · intro wire member
          rcases List.mem_append.mp member with member | member
          · exact lowerMembers wire member
          · simp only [List.mem_singleton] at member
            subst wire
            exact higherMembers target (by simp)
        · intro wire member
          exact higherMembers wire (by simp [member])
        · exact scratchMembers
      · exact circuitUsesOnly_positiveMultiControlledX support lower scratch target
          lowerMembers scratchMembers (higherMembers target (by simp))

/-- 周期 increment は word・scratch の support 内だけを使う。 -/
theorem circuitUsesOnly_incrementWordMod2PowInPlaceCircuit
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (word scratch : List (Wire ancillaQubits systemQubits))
    (wordMembers : ∀ wire ∈ word, wire ∈ support)
    (scratchMembers : ∀ wire ∈ scratch, wire ∈ support) :
    circuitUsesOnly support (incrementWordMod2PowInPlaceCircuit word scratch) := by
  exact circuitUsesOnly_incrementWordCarrySequenceCircuit support [] word scratch
    (by simp) wordMembers scratchMembers

/-- lower 0-controls を蓄積する decrement は word・scratch の support 内だけを使う。 -/
theorem circuitUsesOnly_decrementWordBorrowSequenceCircuit
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    ∀ (lower higher scratch : List (Wire ancillaQubits systemQubits)),
      (∀ wire ∈ lower, wire ∈ support) →
      (∀ wire ∈ higher, wire ∈ support) →
      (∀ wire ∈ scratch, wire ∈ support) →
      circuitUsesOnly support
        (decrementWordBorrowSequenceCircuit lower higher scratch)
  | _, [], _, _, _, _ => by simp [decrementWordBorrowSequenceCircuit, circuitUsesOnly]
  | lower, target :: higher, scratch, lowerMembers, higherMembers, scratchMembers => by
      simp only [decrementWordBorrowSequenceCircuit, circuitUsesOnly]
      constructor
      · apply circuitUsesOnly_decrementWordBorrowSequenceCircuit support
          (lower ++ [target]) higher scratch
        · intro wire member
          rcases List.mem_append.mp member with member | member
          · exact lowerMembers wire member
          · simp only [List.mem_singleton] at member
            subst wire
            exact higherMembers target (by simp)
        · intro wire member
          exact higherMembers wire (by simp [member])
        · exact scratchMembers
      · apply circuitUsesOnly_boolMultiControlledX support
        · intro control member
          rcases List.mem_map.mp member with ⟨wire, wireMember, rfl⟩
          exact lowerMembers wire wireMember
        · exact scratchMembers
        · exact higherMembers target (by simp)

/-- 周期 decrement は word・scratch の support 内だけを使う。 -/
theorem circuitUsesOnly_decrementWordMod2PowInPlaceCircuit
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (word scratch : List (Wire ancillaQubits systemQubits))
    (wordMembers : ∀ wire ∈ word, wire ∈ support)
    (scratchMembers : ∀ wire ∈ scratch, wire ∈ support) :
    circuitUsesOnly support (decrementWordMod2PowInPlaceCircuit word scratch) := by
  exact circuitUsesOnly_decrementWordBorrowSequenceCircuit support [] word scratch
    (by simp) wordMembers scratchMembers

/-- word 等値回路は左右 word・flag・scratch・target の support 内だけを使う。 -/
theorem circuitUsesOnly_equality
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (left right flags scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (leftMembers : ∀ wire ∈ left, wire ∈ support)
    (rightMembers : ∀ wire ∈ right, wire ∈ support)
    (flagMembers : ∀ wire ∈ flags, wire ∈ support)
    (scratchMembers : ∀ wire ∈ scratch, wire ∈ support)
    (targetMember : target ∈ support) :
    circuitUsesOnly support (xorEqualityIntoTargetCircuit left right flags scratch target) := by
  let compute := computeEqualityFlags left right flags
  have computeUses : circuitUsesOnly support compute :=
    circuitUsesOnly_computeEqualityFlags support left right flags
      leftMembers rightMembers flagMembers
  exact ⟨computeUses,
    ⟨circuitUsesOnly_positiveMultiControlledX support flags scratch target
        flagMembers scratchMembers targetMember,
      circuitUsesOnly_reverse_id support compute computeUses⟩⟩

/-- 一 bit の controlled swap は三 wire の support 内だけを使う。 -/
theorem circuitUsesOnly_controlledSwapBit
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (control left right : Wire ancillaQubits systemQubits)
    (controlMember : control ∈ support) (leftMember : left ∈ support)
    (rightMember : right ∈ support) :
    circuitUsesOnly support (controlledSwapBit control left right) := by
  exact ⟨circuitUsesOnly_safeCnot support left right leftMember rightMember,
    ⟨circuitUsesOnly_safeToffoli support control right left controlMember
        rightMember leftMember,
      circuitUsesOnly_safeCnot support left right leftMember rightMember⟩⟩

/-- word controlled swap は control と両 word の support 内だけを使う。 -/
theorem circuitUsesOnly_controlledSwapWord
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (control : Wire ancillaQubits systemQubits)
    (left right : List (Wire ancillaQubits systemQubits))
    (controlMember : control ∈ support)
    (leftMembers : ∀ wire ∈ left, wire ∈ support)
    (rightMembers : ∀ wire ∈ right, wire ∈ support) :
    circuitUsesOnly support (controlledSwapWord control left right) := by
  induction left generalizing right with
  | nil =>
      change circuitUsesOnly support (Circuit.sequence [])
      exact circuitUsesOnly_sequence support [] (by simp)
  | cons left lefts inductionHypothesis =>
      cases right with
      | nil =>
          change circuitUsesOnly support (Circuit.sequence [])
          exact circuitUsesOnly_sequence support [] (by simp)
      | cons right rights =>
          simp only [controlledSwapWord, List.zip_cons_cons, List.map_cons,
            Circuit.sequence]
          constructor
          · exact circuitUsesOnly_controlledSwapBit support control left right
              controlMember (leftMembers left (by simp))
                (rightMembers right (by simp))
          · exact inductionHypothesis rights
              (by intro wire member; exact leftMembers wire (by simp [member]))
              (by intro wire member; exact rightMembers wire (by simp [member]))

/-- 型安全な bitonic compare--exchange は指定部品の support 内だけを使う。 -/
theorem circuitUsesOnly_emitTypedBitonicCompareExchange
    {ancillaQubits systemQubits wordCount historyCount : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (word : Fin wordCount → List (Wire ancillaQubits systemQubits))
    (equalFlags scratch : List (Wire ancillaQubits systemQubits))
    (history : Wire ancillaQubits systemQubits)
    (instruction : TypedBitonicCompareExchange wordCount historyCount)
    (wordMembers : ∀ index wire, wire ∈ word index → wire ∈ support)
    (flagMembers : ∀ wire ∈ equalFlags, wire ∈ support)
    (scratchMembers : ∀ wire ∈ scratch, wire ∈ support)
    (historyMember : history ∈ support) :
    circuitUsesOnly support
      (emitTypedBitonicCompareExchange word equalFlags scratch history instruction) := by
  unfold emitTypedBitonicCompareExchange
  dsimp only
  constructor
  · split
    · exact circuitUsesOnly_lessThan support (word instruction.right)
        (word instruction.left) equalFlags scratch history
        (wordMembers instruction.right) (wordMembers instruction.left)
        flagMembers scratchMembers historyMember
    · exact circuitUsesOnly_lessThan support (word instruction.left)
        (word instruction.right) equalFlags scratch history
        (wordMembers instruction.left) (wordMembers instruction.right)
        flagMembers scratchMembers historyMember
  · exact circuitUsesOnly_controlledSwapWord support history
      (word instruction.left) (word instruction.right) historyMember
      (wordMembers instruction.left) (wordMembers instruction.right)

/-- 型安全な bitonic sort は全 word・比較 work・履歴 wire の support 内だけを使う。 -/
theorem circuitUsesOnly_emitTypedBitonicSort
    {ancillaQubits systemQubits wordCount historyCount : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (word : Fin wordCount → List (Wire ancillaQubits systemQubits))
    (equalFlags scratch : List (Wire ancillaQubits systemQubits))
    (history : Fin historyCount → Wire ancillaQubits systemQubits)
    (schedule : List (TypedBitonicCompareExchange wordCount historyCount))
    (wordMembers : ∀ index wire, wire ∈ word index → wire ∈ support)
    (flagMembers : ∀ wire ∈ equalFlags, wire ∈ support)
    (scratchMembers : ∀ wire ∈ scratch, wire ∈ support)
    (historyMembers : ∀ index, history index ∈ support) :
    circuitUsesOnly support
      (emitTypedBitonicSort word equalFlags scratch history schedule) := by
  apply circuitUsesOnly_sequence support
  intro circuit circuitMember
  rcases List.mem_map.mp circuitMember with ⟨instruction, instructionMember, rfl⟩
  exact circuitUsesOnly_emitTypedBitonicCompareExchange support word equalFlags scratch
    (history instruction.history) instruction wordMembers flagMembers scratchMembers
    (historyMembers instruction.history)

/-- compute--use--uncompute は compute と use が同じ support 内なら同じ support 内だけを使う。 -/
theorem circuitUsesOnly_computeUseUncompute
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (compute use : Circuit (ReversibleGate ancillaQubits systemQubits))
    (computeUses : circuitUsesOnly support compute)
    (useUses : circuitUsesOnly support use) :
    circuitUsesOnly support (Circuit.computeUseUncompute id compute use) := by
  exact ⟨computeUses, ⟨useUses,
    circuitUsesOnly_reverse_id support compute computeUses⟩⟩

/-- selector 定数比較は selector・scratch・target の support 内だけを使う。 -/
theorem circuitUsesOnly_selectorEqualsConstant
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (selector scratch : List (Wire ancillaQubits systemQubits))
    (constant : Nat) (target : Wire ancillaQubits systemQubits)
    (selectorMembers : ∀ wire ∈ selector, wire ∈ support)
    (scratchMembers : ∀ wire ∈ scratch, wire ∈ support)
    (targetMember : target ∈ support) :
    circuitUsesOnly support
      (selectorEqualsConstant selector scratch constant target) := by
  apply circuitUsesOnly_boolMultiControlledX
  · intro control controlMember
    have mapped : control.1 ∈
        (selectorConstantControls selector constant).map Prod.fst :=
      List.mem_map.mpr ⟨control, controlMember, rfl⟩
    have mapEq : (selectorConstantControls selector constant).map Prod.fst =
        selector := by simp [selectorConstantControls]
    exact selectorMembers control.1 (mapEq ▸ mapped)
  · exact scratchMembers
  · exact targetMember

/-- column event compute の疎な support。 -/
def columnEventCandidateUpdateAndSortSupport (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  columnSelectorWires p ++ columnKeyWires p ++ diagonalOracleWorkWires p

/-- row event compute の疎な support。 -/
def rowEventPredecessorCandidateUpdateAndSortSupport (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  rowSelectorWires p ++ systemWires p ++ diagonalOracleWorkWires p

/-- column selector wire は column event compute support に属する。 -/
theorem columnSelectorWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ columnSelectorWires p) :
    wire ∈ columnEventCandidateUpdateAndSortSupport p := by
  simp [columnEventCandidateUpdateAndSortSupport, member]

/-- column key wire は column event compute support に属する。 -/
theorem columnKeyWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ columnKeyWires p) :
    wire ∈ columnEventCandidateUpdateAndSortSupport p := by
  simp [columnEventCandidateUpdateAndSortSupport, member]

/-- oracle work wire は column event compute support に属する。 -/
theorem oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ diagonalOracleWorkWires p) :
    wire ∈ columnEventCandidateUpdateAndSortSupport p := by
  simp [columnEventCandidateUpdateAndSortSupport, member]

/-- row selector wire は row event compute support に属する。 -/
theorem rowSelectorWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ rowSelectorWires p) :
    wire ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
  simp [rowEventPredecessorCandidateUpdateAndSortSupport, member]

/-- system wire は row event compute support に属する。 -/
theorem systemWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ systemWires p) :
    wire ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
  simp [rowEventPredecessorCandidateUpdateAndSortSupport, member]

/-- oracle work wire は row event compute support に属する。 -/
theorem oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ diagonalOracleWorkWires p) :
    wire ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
  simp [rowEventPredecessorCandidateUpdateAndSortSupport, member]

/-- oracle work 内の任意 slice wire は column event compute support に属する。 -/
theorem oracleSliceWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) {width : Nat}
    (slice : RegisterSlice p.oracleWorkWidth width) (index : Fin width) :
    (QLayout.oracleSlice slice).ancillaWire index ∈
      columnEventCandidateUpdateAndSortSupport p := by
  apply oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
  apply diagonalOracleSlice_subset_work p slice
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩

/-- oracle work 内の任意 slice wire は row event compute support に属する。 -/
theorem oracleSliceWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) {width : Nat}
    (slice : RegisterSlice p.oracleWorkWidth width) (index : Fin width) :
    (QLayout.oracleSlice slice).ancillaWire index ∈
      rowEventPredecessorCandidateUpdateAndSortSupport p := by
  apply oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
  apply diagonalOracleSlice_subset_work p slice
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩

/-- moved word の wire は column event compute support に属する。 -/
theorem movedWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ oracleMovedWires p) :
    wire ∈ columnEventCandidateUpdateAndSortSupport p := by
  apply oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
  apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).moved
  simpa [oracleMovedWires, RegisterSlice.wireList] using member

/-- moved word の wire は row event compute support に属する。 -/
theorem movedWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ oracleMovedWires p) :
    wire ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
  apply oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
  apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).moved
  simpa [oracleMovedWires, RegisterSlice.wireList] using member

/-- decoder scratch wire は column event compute support に属する。 -/
theorem decoderScratchWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ decoderAndScratchWires p) :
    wire ∈ columnEventCandidateUpdateAndSortSupport p :=
  oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
    (decoderAndScratchWire_mem_diagonalOracleWorkWires p member)

/-- decoder scratch wire は row event compute support に属する。 -/
theorem decoderScratchWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ decoderAndScratchWires p) :
    wire ∈ rowEventPredecessorCandidateUpdateAndSortSupport p :=
  oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
    (decoderAndScratchWire_mem_diagonalOracleWorkWires p member)

/-- compare work wire は column event compute support に属する。 -/
theorem compareWorkWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ oracleCompareWorkWires p) :
    wire ∈ columnEventCandidateUpdateAndSortSupport p := by
  apply oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
  apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).compareWork
  simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member

/-- compare work wire は row event compute support に属する。 -/
theorem compareWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ oracleCompareWorkWires p) :
    wire ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
  apply oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
  apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).compareWork
  simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member

/-- membership equal flag は column event compute support に属する。 -/
theorem membershipEqualWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) (slot : Fin p.K) :
    membershipEqualWireAt p slot ∈ columnEventCandidateUpdateAndSortSupport p := by
  exact oracleSliceWire_mem_columnEventCandidateUpdateAndSortSupport p
    (OracleWorkLayout.canonical p).membershipEqual slot

/-- membership equal flag は row event compute support に属する。 -/
theorem membershipEqualWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) (slot : Fin p.K) :
    membershipEqualWireAt p slot ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
  exact oracleSliceWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
    (OracleWorkLayout.canonical p).membershipEqual slot

/-- membership good flag は column event compute support に属する。 -/
theorem membershipGoodWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) (slot : Fin p.K) :
    membershipGoodWireAt p slot ∈ columnEventCandidateUpdateAndSortSupport p := by
  exact oracleSliceWire_mem_columnEventCandidateUpdateAndSortSupport p
    (OracleWorkLayout.canonical p).membershipGood slot

/-- membership good flag は row event compute support に属する。 -/
theorem membershipGoodWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) (slot : Fin p.K) :
    membershipGoodWireAt p slot ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
  exact oracleSliceWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
    (OracleWorkLayout.canonical p).membershipGood slot

/-- candidate word の wire は column event compute support に属する。 -/
theorem candidateWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) (word : Fin p.sortWordCount)
    {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ candidateWordAt p word) :
    wire ∈ columnEventCandidateUpdateAndSortSupport p := by
  apply oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
  exact diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).candidate
    (candidateWordAt_mem_candidateSlice p word member)

/-- candidate word の wire は row event compute support に属する。 -/
theorem candidateWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) (word : Fin p.sortWordCount)
    {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ candidateWordAt p word) :
    wire ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
  apply oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
  exact diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).candidate
    (candidateWordAt_mem_candidateSlice p word member)

/-- 任意の oracle singleton wire は column event compute support に属する。 -/
theorem oracleSingletonWire_mem_columnEventCandidateUpdateAndSortSupport
    (p : QParameters) (slice : RegisterSlice p.oracleWorkWidth 1) :
    oracleSingletonWire p slice ∈ columnEventCandidateUpdateAndSortSupport p := by
  exact oracleSliceWire_mem_columnEventCandidateUpdateAndSortSupport p slice 0

/-- 任意の oracle singleton wire は row event compute support に属する。 -/
theorem oracleSingletonWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport
    (p : QParameters) (slice : RegisterSlice p.oracleWorkWidth 1) :
    oracleSingletonWire p slice ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
  exact oracleSliceWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p slice 0

/-- 型安全な一 slot membership 回路は register と oracle work の support 内だけを使う。 -/
theorem circuitUsesOnly_membershipSlotCircuitTyped
    (p : QParameters)
    (support : List (Wire p.ancillaWidth p.systemWidth))
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (registerMembers : ∀ wire ∈ register, wire ∈ support)
    (workMembers : ∀ wire ∈ diagonalOracleWorkWires p, wire ∈ support) :
    circuitUsesOnly support
      (xorSiteSlotMatchAndGoodFlagAtIndexCircuit p register selectedSlot slot includePresentOther) := by
  let word := registerWordAt p register slot
  let equalFlag := membershipEqualWireAt p slot
  let goodFlag := membershipGoodWireAt p slot
  let presentFlag := oraclePresentWireAt p slot
  let presentOther := oraclePresentOtherWire p
  have movedMembers : ∀ wire ∈ oracleMovedWires p, wire ∈ support := by
    intro wire member
    exact workMembers wire (by
      apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).moved
      simpa [oracleMovedWires, RegisterSlice.wireList] using member)
  have wordMembers : ∀ wire ∈ word, wire ∈ support := by
    intro wire member
    exact registerMembers wire
      (mem_register_of_mem_registerWordAt p register slot member)
  have compareMembers : ∀ wire ∈ oracleCompareWorkWires p,
      wire ∈ support := by
    intro wire member
    exact workMembers wire (by
      apply diagonalOracleSlice_subset_work p
        (OracleWorkLayout.canonical p).compareWork
      simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member)
  have scratchMembers : ∀ wire ∈ decoderAndScratchWires p,
      wire ∈ support := by
    intro wire member
    exact workMembers wire
      (decoderAndScratchWire_mem_diagonalOracleWorkWires p member)
  have presentMember : presentFlag ∈ support :=
    workMembers presentFlag (oraclePresentWireAt_mem_diagonalOracleWorkWires p slot)
  have equalMember : equalFlag ∈ support := by
    apply workMembers
    apply diagonalOracleSlice_subset_work p
      (OracleWorkLayout.canonical p).membershipEqual
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).membershipEqual).ancillaWire slot ∈ _
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩
  have goodMember : goodFlag ∈ support := by
    apply workMembers
    apply diagonalOracleSlice_subset_work p
      (OracleWorkLayout.canonical p).membershipGood
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).membershipGood).ancillaWire slot ∈ _
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩
  have presentOtherMember : presentOther ∈ support :=
    workMembers presentOther (by
      apply diagonalOracleSlice_subset_work p
        (OracleWorkLayout.canonical p).presentOther
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).presentOther).ancillaWire 0 ∈ _
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
  change circuitUsesOnly support
    (membershipSlotCircuit (oracleMovedWires p) word
      (oracleCompareWorkWires p) (decoderAndScratchWires p)
      presentFlag equalFlag goodFlag presentOther
      (includePresentOther && slot != selectedSlot))
  simp only [membershipSlotCircuit, circuitUsesOnly]
  refine ⟨circuitUsesOnly_equality support (oracleMovedWires p) word
      (oracleCompareWorkWires p) (decoderAndScratchWires p) equalFlag
      movedMembers wordMembers compareMembers scratchMembers equalMember, ?_⟩
  refine ⟨circuitUsesOnly_x support goodFlag goodMember, ?_⟩
  refine ⟨circuitUsesOnly_safeToffoli support presentFlag equalFlag goodFlag
      presentMember equalMember goodMember, ?_⟩
  split
  · exact circuitUsesOnly_safeToffoli support presentFlag equalFlag presentOther
      presentMember equalMember presentOtherMember
  · trivial

/-- 型安全な membership 全体は register と oracle work の support 内だけを使う。 -/
theorem circuitUsesOnly_xorMembershipMatchGoodAndAbsentFlagsCircuit
    (p : QParameters)
    (support : List (Wire p.ancillaWidth p.systemWidth))
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (registerMembers : ∀ wire ∈ register, wire ∈ support)
    (workMembers : ∀ wire ∈ diagonalOracleWorkWires p, wire ∈ support) :
    circuitUsesOnly support
      (xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot includePresentOther) := by
  constructor
  · apply circuitUsesOnly_sequence support
    intro circuit circuitMember
    rcases List.mem_map.mp circuitMember with ⟨slot, slotMember, rfl⟩
    exact circuitUsesOnly_membershipSlotCircuitTyped p support register selectedSlot
      slot includePresentOther registerMembers workMembers
  · apply circuitUsesOnly_positiveMultiControlledX
    · intro wire member
      rcases List.mem_map.mp member with ⟨slot, slotMember, rfl⟩
      apply workMembers
      apply diagonalOracleSlice_subset_work p
        (OracleWorkLayout.canonical p).membershipGood
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, rfl⟩
    · intro wire member
      exact workMembers wire
        (decoderAndScratchWire_mem_diagonalOracleWorkWires p member)
    · apply workMembers
      apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).absent
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).absent).ancillaWire 0 ∈ _
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩

/-- 一 slot の candidate 準備は register と oracle work の support 内だけを使う。 -/
theorem circuitUsesOnly_prepareCandidateSlotTyped
    (p : QParameters)
    (support : List (Wire p.ancillaWidth p.systemWidth))
    (register : List (Wire p.ancillaWidth p.systemWidth)) (slot : Fin p.K)
    (registerMembers : ∀ wire ∈ register, wire ∈ support)
    (workMembers : ∀ wire ∈ diagonalOracleWorkWires p, wire ∈ support) :
    circuitUsesOnly support (prepareCandidateSlotTyped p register slot) := by
  let word := slotToSortWord p slot
  let target := candidateWordAt p word
  have presentMember : oraclePresentWireAt p slot ∈ support :=
    workMembers _ (oraclePresentWireAt_mem_diagonalOracleWorkWires p slot)
  have sourceMembers : ∀ wire ∈ registerWordAt p register slot,
      wire ∈ support := by
    intro wire member
    exact registerMembers wire
      (mem_register_of_mem_registerWordAt p register slot member)
  have targetMembers : ∀ wire ∈ target.take p.wordWidth,
      wire ∈ support := by
    intro wire member
    apply workMembers
    exact diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).candidate
      (candidateWordAt_mem_candidateSlice p word (List.mem_of_mem_take member))
  have markerMember : candidateMarkerWire p word ∈ support := by
    apply workMembers
    exact diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).candidate
      (candidateMarkerWire_mem_candidateSlice p word)
  change circuitUsesOnly support
    (.seq (controlledXorCopy (oraclePresentWireAt p slot)
      (registerWordAt p register slot) (target.take p.wordWidth))
      (safeCnot (oraclePresentWireAt p slot) (candidateMarkerWire p word)))
  exact ⟨circuitUsesOnly_controlledXorCopy support
      (oraclePresentWireAt p slot) (registerWordAt p register slot)
      (target.take p.wordWidth) presentMember sourceMembers targetMembers,
    circuitUsesOnly_safeCnot support (oraclePresentWireAt p slot)
      (candidateMarkerWire p word) presentMember markerMember⟩

/-- candidate 準備全体は register と oracle work の support 内だけを使う。 -/
theorem circuitUsesOnly_xorConfigurationIntoCandidateRegisterCircuit
    (p : QParameters)
    (support : List (Wire p.ancillaWidth p.systemWidth))
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (registerMembers : ∀ wire ∈ register, wire ∈ support)
    (workMembers : ∀ wire ∈ diagonalOracleWorkWires p, wire ∈ support) :
    circuitUsesOnly support (xorConfigurationIntoCandidateRegisterCircuit p register) := by
  constructor
  · apply circuitUsesOnly_sequence support
    intro circuit circuitMember
    rcases List.mem_map.mp circuitMember with ⟨word, wordMember, rfl⟩
    apply circuitUsesOnly_x
    apply workMembers
    exact diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).candidate
      (candidateMarkerWire_mem_candidateSlice p word)
  · apply circuitUsesOnly_sequence support
    intro circuit circuitMember
    rcases List.mem_map.mp circuitMember with ⟨slot, slotMember, rfl⟩
    exact circuitUsesOnly_prepareCandidateSlotTyped p support register slot
      registerMembers workMembers

/-- Q bitonic sort は oracle work support 内だけを使う。 -/
theorem circuitUsesOnly_reversiblySortCandidateWordsAndRestoreHistoryCircuit
    (p : QParameters)
    (support : List (Wire p.ancillaWidth p.systemWidth))
    (workMembers : ∀ wire ∈ diagonalOracleWorkWires p, wire ∈ support) :
    circuitUsesOnly support (reversiblySortCandidateWordsAndRestoreHistoryCircuit p) := by
  apply circuitUsesOnly_emitTypedBitonicSort
  · intro word wire member
    apply workMembers
    exact diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).candidate
      (candidateWordAt_mem_candidateSlice p word member)
  · intro wire member
    unfold sortCompareWorkWires at member
    rcases List.mem_append.mp member with member | member
    · apply workMembers
      apply diagonalOracleSlice_subset_work p
        (OracleWorkLayout.canonical p).compareWork
      simpa [RegisterSlice.wireList] using member
    · simp only [List.mem_singleton] at member
      subst wire
      apply workMembers
      apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).andWork
      rw [RegisterSlice.wireList]
      let first : Fin p.andWorkWidth := ⟨0, by
        simp [QParameters.andWorkWidth]⟩
      exact List.mem_map.mpr ⟨first, List.mem_finRange first, rfl⟩
  · intro wire member
    apply workMembers
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).andWork
    rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨⟨index.val + 1, by
      simp [QParameters.andWorkWidth] at index ⊢
      omega⟩, List.mem_finRange _, rfl⟩
  · intro index
    apply workMembers
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).sortFlags
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩

/-- column event の selector 比較は broad compute support 内だけを使う。 -/
theorem columnEventSelectorCompute_usesOnly
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    circuitUsesOnly (columnEventCandidateUpdateAndSortSupport p)
      (columnEventSelectorCompute p slot offset) := by
  apply circuitUsesOnly_selectorEqualsConstant
  · intro wire member
    exact columnSelectorWire_mem_columnEventCandidateUpdateAndSortSupport p member
  · intro wire member
    exact decoderScratchWire_mem_columnEventCandidateUpdateAndSortSupport p member
  · exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
      (oracleSelectedWire_mem_diagonalOracleWorkWires p)

/-- row event の selector 比較は broad compute support 内だけを使う。 -/
theorem rowEventSelectorCompute_usesOnly
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    circuitUsesOnly (rowEventPredecessorCandidateUpdateAndSortSupport p)
      (rowEventSelectorCompute p slot offset) := by
  apply circuitUsesOnly_selectorEqualsConstant
  · intro wire member
    exact rowSelectorWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member
  · intro wire member
    exact decoderScratchWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member
  · exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
      (oracleSelectedWire_mem_diagonalOracleWorkWires p)

/-- column event の moved copy は broad compute support 内だけを使う。 -/
theorem columnEventMovedCopy_usesOnly
    (p : QParameters) (slot : Fin p.K) :
    circuitUsesOnly (columnEventCandidateUpdateAndSortSupport p)
      (columnEventMovedCopy p slot) := by
  apply circuitUsesOnly_xorCopy
  · intro wire member
    apply columnKeyWire_mem_columnEventCandidateUpdateAndSortSupport p
    exact mem_register_of_mem_registerWordAt p (columnKeyWires p) slot member
  · intro wire member
    exact movedWire_mem_columnEventCandidateUpdateAndSortSupport p member

/-- row event の moved copy は broad compute support 内だけを使う。 -/
theorem rowEventMovedCopy_usesOnly
    (p : QParameters) (slot : Fin p.K) :
    circuitUsesOnly (rowEventPredecessorCandidateUpdateAndSortSupport p)
      (rowEventMovedCopy p slot) := by
  apply circuitUsesOnly_xorCopy
  · intro wire member
    apply systemWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
    exact mem_register_of_mem_registerWordAt p (systemWires p) slot member
  · intro wire member
    exact movedWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member

/-- column event の周期 increment は broad compute support 内だけを使う。 -/
theorem columnEventMoveForward_usesOnly
    (p : QParameters) (offset : Fin 6) :
    circuitUsesOnly (columnEventCandidateUpdateAndSortSupport p)
      (columnEventMoveForward p offset) := by
  apply circuitUsesOnly_incrementWordMod2PowInPlaceCircuit
  · intro wire member
    apply movedWire_mem_columnEventCandidateUpdateAndSortSupport p
    unfold columnEventCoordinate at member
    split at member
    · exact List.mem_of_mem_drop (List.mem_of_mem_take member)
    · exact List.mem_of_mem_take member
  · intro wire member
    exact decoderScratchWire_mem_columnEventCandidateUpdateAndSortSupport p member

/-- row event の周期 decrement は broad compute support 内だけを使う。 -/
theorem rowEventMoveBackward_usesOnly
    (p : QParameters) (offset : Fin 6) :
    circuitUsesOnly (rowEventPredecessorCandidateUpdateAndSortSupport p)
      (rowEventMoveBackward p offset) := by
  unfold rowEventMoveBackward
  apply circuitUsesOnly_decrementWordMod2PowInPlaceCircuit
  · intro wire member
    apply movedWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
    split at member
    · exact List.mem_of_mem_drop (List.mem_of_mem_take member)
    · exact List.mem_of_mem_take member
  · intro wire member
    exact decoderScratchWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member

/-- column event の membership は broad compute support 内だけを使う。 -/
theorem columnEventMembership_usesOnly
    (p : QParameters) (slot : Fin p.K) :
    circuitUsesOnly (columnEventCandidateUpdateAndSortSupport p)
      (columnEventMembership p slot) := by
  exact circuitUsesOnly_xorMembershipMatchGoodAndAbsentFlagsCircuit p (columnEventCandidateUpdateAndSortSupport p)
    (columnKeyWires p) slot true
    (by intro wire member
        exact columnKeyWire_mem_columnEventCandidateUpdateAndSortSupport p member)
    (by intro wire member
        exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p member)

/-- row event の membership は broad compute support 内だけを使う。 -/
theorem rowEventMembership_usesOnly
    (p : QParameters) (slot : Fin p.K) :
    circuitUsesOnly (rowEventPredecessorCandidateUpdateAndSortSupport p)
      (rowEventMembership p slot) := by
  exact circuitUsesOnly_xorMembershipMatchGoodAndAbsentFlagsCircuit p (rowEventPredecessorCandidateUpdateAndSortSupport p)
    (systemWires p) slot false
    (by intro wire member
        exact systemWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member)
    (by intro wire member
        exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member)

/-- column event branch の全 control wire は broad compute support に属する。 -/
theorem columnEventBranchControl_mem_support
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ columnEventBranchControls p slot offset) :
    wire ∈ columnEventCandidateUpdateAndSortSupport p := by
  by_cases collision : offset.val % 2 = 1
  · simp [columnEventBranchControls, collision] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
        (oracleLegalWire_mem_diagonalOracleWorkWires p)
    · exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
        (oracleSelectedWire_mem_diagonalOracleWorkWires p)
    · exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
        (oraclePresentWireAt_mem_diagonalOracleWorkWires p slot)
    · exact oracleSingletonWire_mem_columnEventCandidateUpdateAndSortSupport p
        (OracleWorkLayout.canonical p).presentOther
    · exact oracleSingletonWire_mem_columnEventCandidateUpdateAndSortSupport p
        (OracleWorkLayout.canonical p).degreeCondition
  · simp [columnEventBranchControls, collision] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
        (oracleLegalWire_mem_diagonalOracleWorkWires p)
    · exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
        (oracleSelectedWire_mem_diagonalOracleWorkWires p)
    · exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
        (oraclePresentWireAt_mem_diagonalOracleWorkWires p slot)
    · exact oracleSingletonWire_mem_columnEventCandidateUpdateAndSortSupport p
        (OracleWorkLayout.canonical p).absent

/-- row event branch の全 control wire は broad compute support に属する。 -/
theorem rowEventBranchControl_mem_support
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈
      ([oracleLegalWire p, oracleSelectedWire p,
        oraclePresentWireAt p slot, oracleAbsentWire p] ++
          if offset.val % 2 = 1 then [oracleDegreeConditionWire p] else [])) :
    wire ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
  by_cases collision : offset.val % 2 = 1
  · simp [collision] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
        (oracleLegalWire_mem_diagonalOracleWorkWires p)
    · exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
        (oracleSelectedWire_mem_diagonalOracleWorkWires p)
    · exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
        (oraclePresentWireAt_mem_diagonalOracleWorkWires p slot)
    · exact oracleSingletonWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
        (OracleWorkLayout.canonical p).absent
    · exact oracleSingletonWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
        (OracleWorkLayout.canonical p).degreeCondition
  · simp [collision] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
        (oracleLegalWire_mem_diagonalOracleWorkWires p)
    · exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
        (oracleSelectedWire_mem_diagonalOracleWorkWires p)
    · exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
        (oraclePresentWireAt_mem_diagonalOracleWorkWires p slot)
    · exact oracleSingletonWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
        (OracleWorkLayout.canonical p).absent

/-- column event の受理 branch 計算は broad compute support 内だけを使う。 -/
theorem columnEventBranchCompute_usesOnly
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    circuitUsesOnly (columnEventCandidateUpdateAndSortSupport p)
      (columnEventBranchCompute p slot offset) := by
  apply circuitUsesOnly_positiveMultiControlledX
  · intro wire member
    exact columnEventBranchControl_mem_support p slot offset member
  · intro wire member
    exact decoderScratchWire_mem_columnEventCandidateUpdateAndSortSupport p member
  · exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
      (oracleBranchWire_mem_diagonalOracleWorkWires p)

/-- row event の受理 branch 計算は broad compute support 内だけを使う。 -/
theorem rowEventBranchCompute_usesOnly
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    circuitUsesOnly (rowEventPredecessorCandidateUpdateAndSortSupport p)
      (rowEventBranchCompute p slot offset) := by
  unfold rowEventBranchCompute
  apply circuitUsesOnly_positiveMultiControlledX
  · intro wire member
    exact rowEventBranchControl_mem_support p slot offset member
  · intro wire member
    exact decoderScratchWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member
  · exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
      (oracleBranchWire_mem_diagonalOracleWorkWires p)

/-- column event の candidate 変更は broad compute support 内だけを使う。 -/
theorem columnEventModify_usesOnly
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    circuitUsesOnly (columnEventCandidateUpdateAndSortSupport p)
      (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset) := by
  have branchMember : oracleBranchWire p ∈ columnEventCandidateUpdateAndSortSupport p :=
    oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p
      (oracleBranchWire_mem_diagonalOracleWorkWires p)
  have sourceMembers : ∀ wire ∈ registerWordAt p (columnKeyWires p) slot,
      wire ∈ columnEventCandidateUpdateAndSortSupport p := by
    intro wire member
    apply columnKeyWire_mem_columnEventCandidateUpdateAndSortSupport p
    exact mem_register_of_mem_registerWordAt p (columnKeyWires p) slot member
  have candidateMembers : ∀ wire ∈
      (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth,
      wire ∈ columnEventCandidateUpdateAndSortSupport p := by
    intro wire member
    exact candidateWire_mem_columnEventCandidateUpdateAndSortSupport p (slotToSortWord p slot)
      (List.mem_of_mem_take member)
  unfold controlledUpdateSelectedColumnCandidateWordCircuit columnEventRemoveSource
  split
  · exact ⟨circuitUsesOnly_controlledXorCopy _ _ _ _ branchMember
        sourceMembers candidateMembers,
      circuitUsesOnly_safeCnot _ _ _ branchMember
        (candidateWire_mem_columnEventCandidateUpdateAndSortSupport p (slotToSortWord p slot)
          (by simp [candidateMarkerWire, candidateWordAt]))⟩
  · exact ⟨circuitUsesOnly_controlledXorCopy _ _ _ _ branchMember
        sourceMembers candidateMembers,
      circuitUsesOnly_controlledXorCopy _ _ _ _ branchMember
        (by intro wire member
            exact movedWire_mem_columnEventCandidateUpdateAndSortSupport p member)
        candidateMembers⟩

/-- row collision の一 candidate 追加は broad compute support 内だけを使う。 -/
theorem rowEventCollisionModifyAt_usesOnly
    (p : QParameters) (degreeSlot : Fin (p.K - 1)) :
    circuitUsesOnly (rowEventPredecessorCandidateUpdateAndSortSupport p)
      (controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot) := by
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
  have branchMember : oracleBranchWire p ∈ rowEventPredecessorCandidateUpdateAndSortSupport p :=
    oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
      (oracleBranchWire_mem_diagonalOracleWorkWires p)
  have degreeMember : oracleDegreeWireAt p degreeIndex ∈
      rowEventPredecessorCandidateUpdateAndSortSupport p :=
    oracleSliceWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
      (OracleWorkLayout.canonical p).degree degreeIndex
  have pairMember : pairFlag ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
    apply oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).pair
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).pair).ancillaWire
        ⟨0, by simpa [QParameters.pairWidth] using p.K_pos⟩ ∈ _
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
  have candidateMembers : ∀ wire ∈ candidate.take p.wordWidth,
      wire ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
    intro wire member
    exact candidateWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p candidateIndex
      (List.mem_of_mem_take member)
  change circuitUsesOnly (rowEventPredecessorCandidateUpdateAndSortSupport p)
    (Circuit.computeUseUncompute id pairCompute (.seq append marker))
  apply circuitUsesOnly_computeUseUncompute
  · apply circuitUsesOnly_positiveMultiControlledX
    · intro wire member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact branchMember
      · exact degreeMember
    · intro wire member
      exact decoderScratchWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member
    · exact pairMember
  · exact ⟨circuitUsesOnly_controlledXorCopy _ _ _ _ pairMember
        (by intro wire member
            exact movedWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member)
        candidateMembers,
      circuitUsesOnly_safeCnot _ _ _ pairMember
        (candidateWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p candidateIndex
          (by simp [candidateMarkerWire, candidateWordAt]))⟩

/-- row event の candidate 変更は broad compute support 内だけを使う。 -/
theorem rowEventModify_usesOnly
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    circuitUsesOnly (rowEventPredecessorCandidateUpdateAndSortSupport p)
      (controlledUpdateSelectedRowCandidateWordCircuit p slot offset) := by
  unfold controlledUpdateSelectedRowCandidateWordCircuit
  split
  · unfold controlledUpdateSelectedRowCollisionCandidateWordCircuit
    apply circuitUsesOnly_sequence
    intro circuit circuitMember
    rcases List.mem_map.mp circuitMember with ⟨degreeSlot, degreeSlotMember, rfl⟩
    exact rowEventCollisionModifyAt_usesOnly p degreeSlot
  · unfold controlledUpdateSelectedRowReplacementCandidateWordCircuit
    let candidate := candidateWordAt p (slotToSortWord p slot)
    have branchMember : oracleBranchWire p ∈ rowEventPredecessorCandidateUpdateAndSortSupport p :=
      oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
        (oracleBranchWire_mem_diagonalOracleWorkWires p)
    have candidateMembers : ∀ wire ∈ candidate.take p.wordWidth,
        wire ∈ rowEventPredecessorCandidateUpdateAndSortSupport p := by
      intro wire member
      exact candidateWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p (slotToSortWord p slot)
        (List.mem_of_mem_take member)
    exact ⟨circuitUsesOnly_controlledXorCopy _ _ _ _ branchMember
        (by intro wire member
            apply systemWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p
            exact mem_register_of_mem_registerWordAt p (systemWires p) slot member)
        candidateMembers,
      circuitUsesOnly_controlledXorCopy _ _ _ _ branchMember
        (by intro wire member
            exact movedWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member)
        candidateMembers⟩

/-- column event compute 全体は broad support 内だけを使う。 -/
theorem computeColumnEventCandidateUpdateAndSortCircuit_usesOnly
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    circuitUsesOnly (columnEventCandidateUpdateAndSortSupport p)
      (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) := by
  exact ⟨columnEventSelectorCompute_usesOnly p slot offset,
    ⟨columnEventMovedCopy_usesOnly p slot,
      ⟨columnEventMoveForward_usesOnly p offset,
        ⟨columnEventMembership_usesOnly p slot,
          ⟨columnEventBranchCompute_usesOnly p slot offset,
            ⟨circuitUsesOnly_xorConfigurationIntoCandidateRegisterCircuit p
                (columnEventCandidateUpdateAndSortSupport p) (columnKeyWires p)
                (by intro wire member
                    exact columnKeyWire_mem_columnEventCandidateUpdateAndSortSupport p member)
                (by intro wire member
                    exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p member),
              ⟨columnEventModify_usesOnly p slot offset,
                circuitUsesOnly_reversiblySortCandidateWordsAndRestoreHistoryCircuit p
                  (columnEventCandidateUpdateAndSortSupport p)
                  (by intro wire member
                      exact oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p member)⟩⟩⟩⟩⟩⟩⟩

/-- row event compute 全体は broad support 内だけを使う。 -/
theorem computeRowEventPredecessorCandidateUpdateAndSortCircuit_usesOnly
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    circuitUsesOnly (rowEventPredecessorCandidateUpdateAndSortSupport p)
      (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) := by
  exact ⟨rowEventSelectorCompute_usesOnly p slot offset,
    ⟨rowEventMovedCopy_usesOnly p slot,
      ⟨rowEventMoveBackward_usesOnly p offset,
        ⟨rowEventMembership_usesOnly p slot,
          ⟨rowEventBranchCompute_usesOnly p slot offset,
            ⟨circuitUsesOnly_xorConfigurationIntoCandidateRegisterCircuit p
                (rowEventPredecessorCandidateUpdateAndSortSupport p) (systemWires p)
                (by intro wire member
                    exact systemWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member)
                (by intro wire member
                    exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member),
              ⟨rowEventModify_usesOnly p slot offset,
                circuitUsesOnly_reversiblySortCandidateWordsAndRestoreHistoryCircuit p
                  (rowEventPredecessorCandidateUpdateAndSortSupport p)
                  (by intro wire member
                      exact oracleWorkWire_mem_rowEventPredecessorCandidateUpdateAndSortSupport p member)⟩⟩⟩⟩⟩⟩⟩

/-- row 担当の broad support は本ファイルの compute support と一致する。 -/
theorem rowEventPredecessorCandidateUpdateAndSortSupport_eq_broadSupport (p : QParameters) :
    rowEventPredecessorCandidateUpdateAndSortSupport p = rowEventBroadSupport p := by
  rfl

end ReversibleCircuit

end ProbabilityGeneratorQProof
