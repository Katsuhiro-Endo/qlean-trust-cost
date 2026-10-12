import QLean.Generator.Implementation.QOracleCandidateCorrectness
import QLean.Generator.Implementation.ReversibleLogicSharedCoreReadoutAdapter

/-!
# sorted出力とmoved selector出力の基底作用仕様

このファイルでは、`xorSortedCandidatesAsDelimiterIntoOutputCircuit`と`xorMovedMemberPositionIntoSelectorOutputCircuit`が満たすべき
計算基底上の純粋仕様を、巨大行列を作らず有限foldとして定義する。
特にselector出力については、各sorted slotの受理条件をBool式として固定し、
正本回路が走査するslot列と純粋仕様が同じ一般の`Fin K`列であることを示す。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- moved selectorの一つのsorted slotが受理される純粋な基底条件。 -/
def movedSelectorSlotEnabled (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Bool :=
  input (oracleBranchWire p) &&
    decide (readWires (oracleMovedWires p) input =
      readWires
        ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth) input) &&
    !(input (candidateMarkerWire p (slotToSortWord p slot)))

/--
任意のslot列について、受理されたslot定数をselector bit列へ順にXORする純粋仕様。
-/
def xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom (p : QParameters) (offset : Nat)
    (slots : List (Fin p.K))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    List Bool → List Bool :=
  slots.foldl (fun bits slot =>
    controlledXorConstantBits (movedSelectorSlotEnabled p slot input)
      (6 * slot.val + offset) 0 bits)

/-- 正本が走査する全`Fin K` slotに対するmoved selectorの純粋仕様。 -/
def movedMemberPositionSelectorOutputXorReference (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth) : List Bool :=
  xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset (List.finRange p.K) input
    (readWires outputSelector input)

/-- 制御値が偽なら、純粋な定数XORは任意幅のbit列を変更しない。 -/
@[simp] theorem controlledXorConstantBits_false (constant start : Nat) :
    ∀ bits : List Bool,
      controlledXorConstantBits false constant start bits = bits
  | [] => rfl
  | bit :: bits => by
      simp [controlledXorConstantBits,
        controlledXorConstantBits_false constant (start + 1) bits]

/-- 空のslot列ではmoved selector参照作用は恒等作用である。 -/
@[simp] theorem xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_nil
    (p : QParameters) (offset : Nat)
    (input : JointBasis p.ancillaWidth p.systemWidth) (bits : List Bool) :
    xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset [] input bits = bits := by
  rfl

/-- slot列の先頭を追加すると、そのslotの定数XORを行ってから残りを走査する。 -/
theorem xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_cons
    (p : QParameters) (offset : Nat) (slot : Fin p.K)
    (slots : List (Fin p.K))
    (input : JointBasis p.ancillaWidth p.systemWidth) (bits : List Bool) :
    xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset (slot :: slots) input bits =
      xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset slots input
        (controlledXorConstantBits (movedSelectorSlotEnabled p slot input)
          (6 * slot.val + offset) 0 bits) := by
  simp [xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom, List.foldl]

/-- 受理されない先頭slotは参照selector作用から除去できる。 -/
theorem xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_cons_disabled
    (p : QParameters) (offset : Nat) (slot : Fin p.K)
    (slots : List (Fin p.K))
    (input : JointBasis p.ancillaWidth p.systemWidth) (bits : List Bool)
    (disabled : movedSelectorSlotEnabled p slot input = false) :
    xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset (slot :: slots) input bits =
      xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset slots input bits := by
  rw [xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_cons, disabled]
  simp

/-- 一つのmoved selector slotを構成する正本compute--use--uncompute回路。 -/
def xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let positionFlag := oraclePositionWire p
  let pairFlag := oraclePairWire p
  let word := candidateWordAt p (slotToSortWord p slot)
  let equal := ReversibleCircuit.xorEqualityIntoTargetCircuit (oracleMovedWires p)
    (word.take p.wordWidth) (oracleCompareWorkWires p)
    (decoderAndScratchWires p) positionFlag
  let marker := candidateMarkerWire p (slotToSortWord p slot)
  let invert := (.gate (.x marker) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth))
  let markerUse := .seq invert <| .seq
    (ReversibleCircuit.positiveMultiControlledX
      [oracleBranchWire p, positionFlag, marker]
      (decoderAndScratchWires p) pairFlag) invert
  let compute := .seq equal markerUse
  let use := controlledXorConstant pairFlag outputSelector
    (6 * slot.val + offset)
  Circuit.computeUseUncompute id compute use

/-- moved selector正本は、型安全な全slot回路列の逐次合成に定義的に等しい。 -/
theorem xorMovedMemberPositionIntoSelectorOutputCircuit_eq_slotSequence (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth)) :
    xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector =
      Circuit.sequence ((List.finRange p.K).map fun slot =>
        xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit p offset outputSelector slot) := by
  rfl

/--
正本moved selectorの基底実行は、一般の`K`についてslot回路の有限foldに一致する。
これは全基底列挙ではなく、回路構文木の`sequence`意味論だけから得られる。
-/
theorem runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_slotFold (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector).runBasis
        reversibleGatePermutation input =
      (List.finRange p.K).foldl (fun state slot =>
        (xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit p offset outputSelector slot).runBasis
          reversibleGatePermutation state) input := by
  rw [xorMovedMemberPositionIntoSelectorOutputCircuit_eq_slotSequence]
  rw [Circuit.runBasis_sequence]
  simp only [List.foldl_map]

/-- 一つのmoved selector slotのcompute部分だけを切り出した正本回路。 -/
def xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit (p : QParameters) (slot : Fin p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let positionFlag := oraclePositionWire p
  let pairFlag := oraclePairWire p
  let word := candidateWordAt p (slotToSortWord p slot)
  let equal := ReversibleCircuit.xorEqualityIntoTargetCircuit (oracleMovedWires p)
    (word.take p.wordWidth) (oracleCompareWorkWires p)
    (decoderAndScratchWires p) positionFlag
  let marker := candidateMarkerWire p (slotToSortWord p slot)
  let invert := (.gate (.x marker) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth))
  let markerUse := .seq invert <| .seq
    (ReversibleCircuit.positiveMultiControlledX
      [oracleBranchWire p, positionFlag, marker]
      (decoderAndScratchWires p) pairFlag) invert
  .seq equal markerUse

/-- 一つのmoved selector computeが参照する全wireの有限support。 -/
def xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport (p : QParameters) (slot : Fin p.K) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  oracleMovedWires p ++
    (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth ++
    oracleCompareWorkWires p ++ decoderAndScratchWires p ++
    [oracleBranchWire p, oraclePositionWire p,
      candidateMarkerWire p (slotToSortWord p slot), oraclePairWire p]

/--
一つのmoved selector slotに必要な局所配置条件。
これらは値に関するoracle契約ではなく、正本layoutの静的な長さ・非交差条件である。
-/
structure WriteMovedSelectorSlotLayout (p : QParameters) (slot : Fin p.K)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth)) : Prop where
  /-- moved wordと比較workの長さは等しい。 -/
  moved_length : (oracleMovedWires p).length = (oracleCompareWorkWires p).length
  /-- candidate dataと比較workの長さは等しい。 -/
  word_length :
    ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth).length =
      (oracleCompareWorkWires p).length
  /-- moved wordと比較workは交わらない。 -/
  moved_disjoint_compare :
    (oracleMovedWires p).Disjoint (oracleCompareWorkWires p)
  /-- candidate dataと比較workは交わらない。 -/
  word_disjoint_compare :
    ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth).Disjoint
      (oracleCompareWorkWires p)
  /-- 比較workとAND scratchは交わらない。 -/
  compare_disjoint_scratch :
    (oracleCompareWorkWires p).Disjoint (decoderAndScratchWires p)
  /-- 比較workには重複がない。 -/
  compare_nodup : (oracleCompareWorkWires p).Nodup
  /-- 等値判定の制御・scratch・target配置に重複がない。 -/
  equality_layout :
    (oracleCompareWorkWires p ++ decoderAndScratchWires p ++
      [oraclePositionWire p]).Nodup
  /-- position flagはmoved word外にある。 -/
  position_absent_moved : oraclePositionWire p ∉ oracleMovedWires p
  /-- position flagはcandidate data外にある。 -/
  position_absent_word : oraclePositionWire p ∉
    (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  /-- 等値判定に十分なscratchがある。 -/
  equality_scratch_enough :
    (oracleCompareWorkWires p).length ≤ (decoderAndScratchWires p).length + 1
  /-- 三制御ANDの配置に重複がない。 -/
  pair_layout :
    ([oracleBranchWire p, oraclePositionWire p,
        candidateMarkerWire p (slotToSortWord p slot)] ++
      decoderAndScratchWires p ++ [oraclePairWire p]).Nodup
  /-- 三制御ANDに十分なscratchがある。 -/
  pair_scratch_enough : 3 ≤ (decoderAndScratchWires p).length + 1
  /-- branch flagとposition flagは異なる。 -/
  branch_ne_position : oracleBranchWire p ≠ oraclePositionWire p
  /-- branch flagとmarkerは異なる。 -/
  branch_ne_marker : oracleBranchWire p ≠
    candidateMarkerWire p (slotToSortWord p slot)
  /-- position flagとmarkerは異なる。 -/
  position_ne_marker : oraclePositionWire p ≠
    candidateMarkerWire p (slotToSortWord p slot)
  /-- pair flagとposition flagは異なる。 -/
  pair_ne_position : oraclePairWire p ≠ oraclePositionWire p
  /-- pair flagとmarkerは異なる。 -/
  pair_ne_marker : oraclePairWire p ≠
    candidateMarkerWire p (slotToSortWord p slot)
  /-- branch flagは比較work外にある。 -/
  branch_absent_compare : oracleBranchWire p ∉ oracleCompareWorkWires p
  /-- markerは比較work外にある。 -/
  marker_absent_compare : candidateMarkerWire p (slotToSortWord p slot) ∉
    oracleCompareWorkWires p
  /-- pair flagは比較work外にある。 -/
  pair_absent_compare : oraclePairWire p ∉ oracleCompareWorkWires p
  /-- branch flagはscratch外にある。 -/
  branch_absent_scratch : oracleBranchWire p ∉ decoderAndScratchWires p
  /-- position flagはscratch外にある。 -/
  position_absent_scratch : oraclePositionWire p ∉ decoderAndScratchWires p
  /-- markerはscratch外にある。 -/
  marker_absent_scratch : candidateMarkerWire p (slotToSortWord p slot) ∉
    decoderAndScratchWires p
  /-- pair flagはscratch外にある。 -/
  pair_absent_scratch : oraclePairWire p ∉ decoderAndScratchWires p
  /-- selector出力wire列には重複がない。 -/
  output_nodup : outputSelector.Nodup
  /-- selector出力はcompute supportと交わらない。 -/
  output_disjoint_support : outputSelector.Disjoint
    (xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport p slot)

/-- 一つのmoved selector slotを実行する前に必要なclean値条件。 -/
structure WriteMovedSelectorSlotClean (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 比較workは全0である。 -/
  compare_zero : readWires (oracleCompareWorkWires p) input =
    List.replicate (oracleCompareWorkWires p).length false
  /-- AND scratchは全0である。 -/
  scratch_zero : ∀ wire ∈ decoderAndScratchWires p, input wire = false
  /-- position flagは0である。 -/
  position_zero : input (oraclePositionWire p) = false
  /-- pair flagは0である。 -/
  pair_zero : input (oraclePairWire p) = false

/-- moved selectorのcompute回路は明示した有限support内だけを参照する。 -/
theorem xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit_usesOnly (p : QParameters)
    (slot : Fin p.K) :
    circuitUsesOnly (xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport p slot)
      (xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit p slot) := by
  let support := xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport p slot
  let moved := oracleMovedWires p
  let word := (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let compare := oracleCompareWorkWires p
  let scratch := decoderAndScratchWires p
  let branch := oracleBranchWire p
  let position := oraclePositionWire p
  let marker := candidateMarkerWire p (slotToSortWord p slot)
  let pair := oraclePairWire p
  have movedMember : ∀ wire ∈ moved, wire ∈ support := by
    intro wire member
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, moved, member]
  have wordMember : ∀ wire ∈ word, wire ∈ support := by
    intro wire member
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, word, member]
  have compareMember : ∀ wire ∈ compare, wire ∈ support := by
    intro wire member
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, compare, member]
  have scratchMember : ∀ wire ∈ scratch, wire ∈ support := by
    intro wire member
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, scratch, member]
  have branchMember : branch ∈ support := by
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, branch]
  have positionMember : position ∈ support := by
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, position]
  have markerMember : marker ∈ support := by
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, marker]
  have pairMember : pair ∈ support := by
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, pair]
  have equalityUses : circuitUsesOnly support
      (ReversibleCircuit.xorEqualityIntoTargetCircuit moved word compare scratch position) := by
    unfold ReversibleCircuit.xorEqualityIntoTargetCircuit
    have computeUses := circuitUsesOnly_computeEqualityFlags support moved word compare
      movedMember wordMember compareMember
    have useUses := circuitUsesOnly_positiveMultiControlledX support compare scratch
      position compareMember scratchMember positionMember
    exact ⟨computeUses, ⟨useUses,
      circuitUsesOnly_reverse_id support _ computeUses⟩⟩
  have invertUses : circuitUsesOnly support
      (.gate (.x marker) : Circuit (ReversibleGate p.ancillaWidth p.systemWidth)) :=
    circuitUsesOnly_x support marker markerMember
  have pairUses : circuitUsesOnly support
      (positiveMultiControlledX [branch, position, marker] scratch pair) :=
    circuitUsesOnly_positiveMultiControlledX support _ scratch pair
      (by intro wire member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact branchMember
          · exact positionMember
          · exact markerMember)
      scratchMember pairMember
  simpa [xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit, support, moved, word, compare, scratch,
    branch, position, marker, pair] using
      (show circuitUsesOnly support
          (.seq (ReversibleCircuit.xorEqualityIntoTargetCircuit moved word compare scratch position)
            (.seq (.gate (.x marker))
              (.seq (positiveMultiControlledX [branch, position, marker] scratch pair)
                (.gate (.x marker))))) from
        ⟨equalityUses, ⟨invertUses, ⟨pairUses, invertUses⟩⟩⟩)

/--
cleanな一slot compute後のpair flagは、branch・word等値・非padding markerの
三条件の論理積に厳密に一致する。
-/
theorem runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit_pair
    (p : QParameters) (slot : Fin p.K)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layout : WriteMovedSelectorSlotLayout p slot outputSelector)
    (clean : WriteMovedSelectorSlotClean p input) :
    (xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit p slot).runBasis
        reversibleGatePermutation input (oraclePairWire p) =
      movedSelectorSlotEnabled p slot input := by
  let moved := oracleMovedWires p
  let word := (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let compare := oracleCompareWorkWires p
  let scratch := decoderAndScratchWires p
  let branch := oracleBranchWire p
  let position := oraclePositionWire p
  let marker := candidateMarkerWire p (slotToSortWord p slot)
  let pair := oraclePairWire p
  let afterEqual :=
    if decide (readWires moved input = readWires word input) then
      xBasisAction position input
    else input
  let afterInvert := xBasisAction marker afterEqual
  have scratchAfterInvert : ∀ wire ∈ scratch, afterInvert wire = false := by
    intro wire member
    have wireNePosition : wire ≠ position := by
      intro equal
      subst wire
      exact layout.position_absent_scratch member
    have wireNeMarker : wire ≠ marker := by
      intro equal
      subst wire
      exact layout.marker_absent_scratch member
    by_cases equalWords : readWires moved input = readWires word input
    · simp [afterInvert, afterEqual, equalWords, xBasisAction, wireNePosition,
        wireNeMarker,
        clean.scratch_zero wire member]
    · simp [afterInvert, afterEqual, equalWords, wireNeMarker,
        clean.scratch_zero wire member]
  rw [xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit, runBasis_seq]
  rw [runBasis_xorEqualityIntoTargetCircuit moved word compare scratch position input
    layout.moved_length layout.word_length layout.moved_disjoint_compare
    layout.word_disjoint_compare layout.compare_disjoint_scratch
    layout.compare_nodup layout.equality_layout layout.position_absent_moved
    layout.position_absent_word clean.compare_zero clean.scratch_zero
    layout.equality_scratch_enough]
  change
    ((.seq (.gate (.x marker))
      (.seq (positiveMultiControlledX [branch, position, marker] scratch pair)
        (.gate (.x marker))) :
      Circuit (ReversibleGate p.ancillaWidth p.systemWidth))).runBasis
        reversibleGatePermutation afterEqual pair = _
  rw [runBasis_core_seq, runBasis_x, runBasis_core_seq]
  rw [runBasis_core_eq_local reversibleGatePermutation
    (positiveMultiControlledX [branch, position, marker] scratch pair) afterInvert]
  rw [runBasis_positiveMultiControlledX [branch, position, marker] scratch pair
    afterInvert layout.pair_scratch_enough layout.pair_layout scratchAfterInvert]
  rw [runBasis_x]
  have branchNePosition : branch ≠ position := by
    simpa [branch, position] using layout.branch_ne_position
  have branchNeMarker : branch ≠ marker := by
    simpa [branch, marker] using layout.branch_ne_marker
  have positionNeMarker : position ≠ marker := by
    simpa [position, marker] using layout.position_ne_marker
  have pairNePosition : pair ≠ position := by
    simpa [pair, position] using layout.pair_ne_position
  have pairNeMarker : pair ≠ marker := by
    simpa [pair, marker] using layout.pair_ne_marker
  have positionZero : input position = false := by
    simpa [position] using clean.position_zero
  have pairZero : input pair = false := by
    simpa [pair] using clean.pair_zero
  have branchAfter : afterInvert branch = input branch := by
    by_cases equalWords : readWires moved input = readWires word input <;>
      simp [afterInvert, afterEqual, equalWords, xBasisAction,
        branchNeMarker, branchNePosition]
  have positionAfter : afterInvert position =
      decide (readWires moved input = readWires word input) := by
    by_cases equalWords : readWires moved input = readWires word input
    · simp [afterInvert, afterEqual, equalWords, positionNeMarker, positionZero]
    · simp [afterInvert, afterEqual, equalWords, positionNeMarker, positionZero]
  have markerAfter : afterInvert marker = !(input marker) := by
    by_cases equalWords : readWires moved input = readWires word input <;>
      simp [afterInvert, afterEqual, equalWords, xBasisAction,
        positionNeMarker.symm]
  have pairAfter : afterInvert pair = false := by
    by_cases equalWords : readWires moved input = readWires word input <;>
      simp [afterInvert, afterEqual, equalWords, xBasisAction,
        pairNePosition, pairNeMarker, pairZero]
  have controlValue :
      allWiresTrue [branch, position, marker] afterInvert =
        movedSelectorSlotEnabled p slot input := by
    simp [allWiresTrue, readWires, branchAfter, positionAfter, markerAfter,
      movedSelectorSlotEnabled, moved, word, branch, position, marker,
      Bool.and_assoc]
  rw [controlValue]
  cases enabled : movedSelectorSlotEnabled p slot input <;>
    simp [xBasisAction, pairAfter, pairNeMarker]

/--
一つのmoved selector slot回路後のselector registerは、純粋な条件付き定数XOR仕様に
厳密に一致する。compute workは局所uncompute補題により入力値へ戻される。
-/
theorem readWires_xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit
    (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layout : WriteMovedSelectorSlotLayout p slot outputSelector)
    (clean : WriteMovedSelectorSlotClean p input) :
    readWires outputSelector
        ((xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit p offset outputSelector slot).runBasis
          reversibleGatePermutation input) =
      controlledXorConstantBits (movedSelectorSlotEnabled p slot input)
        (6 * slot.val + offset) 0 (readWires outputSelector input) := by
  let support := xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport p slot
  let compute := xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit p slot
  let pair := oraclePairWire p
  let constant := 6 * slot.val + offset
  let use := controlledXorConstant pair outputSelector constant
  let computed := compute.runBasis reversibleGatePermutation input
  have computeUses : circuitUsesOnly support compute := by
    simpa [support, compute] using xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit_usesOnly p slot
  have pairMember : pair ∈ support := by
    simp [pair, support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport]
  have outputOutside : ∀ wire ∈ outputSelector, wire ∉ support := by
    intro wire outputMember supportMember
    exact (List.disjoint_left.mp layout.output_disjoint_support outputMember)
      supportMember
  have pairAbsentOutput : pair ∉ outputSelector := by
    intro member
    exact outputOutside pair member pairMember
  have usePreserves : BasisAgreeOn support
      (use.runBasis reversibleGatePermutation computed) computed := by
    intro wire supportMember
    rw [show use = controlledXorConstant pair outputSelector constant by rfl]
    rw [runBasis_controlledXorConstant pair outputSelector constant computed
      pairAbsentOutput]
    exact controlledXorConstantBasisAction_outside pair constant 0 outputSelector
      computed wire (by
        intro outputMember
        exact outputOutside wire outputMember supportMember)
  have localClean := Circuit.computeUseUncompute_local_clean support compute use input
    computeUses usePreserves
  have stageAsComputeUse :
      xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit p offset outputSelector slot =
        Circuit.computeUseUncompute id compute use := by
    rfl
  rw [stageAsComputeUse, localClean]
  have restoreRead :
      readWires outputSelector
          (restoreSupport support input
            (use.runBasis reversibleGatePermutation computed)) =
        readWires outputSelector
          (use.runBasis reversibleGatePermutation computed) := by
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside support input
      (use.runBasis reversibleGatePermutation computed) wire
      (outputOutside wire member)
  rw [restoreRead]
  rw [show use = controlledXorConstant pair outputSelector constant by rfl]
  rw [readWires_controlledXorConstant pair outputSelector constant computed
    layout.output_nodup pairAbsentOutput]
  have pairValue : computed pair = movedSelectorSlotEnabled p slot input := by
    simpa [computed, compute, pair] using
      runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit_pair p slot outputSelector input
        layout clean
  rw [pairValue]
  congr 1
  apply List.map_congr_left
  intro wire member
  exact Circuit.runBasis_outside_of_usesOnly support compute computeUses input wire
    (outputOutside wire member)

/--
一つのmoved selector slot回路はselector出力列以外の任意wireを変更しない。
とくにposition・pair・compare・AND scratchはcompute--use--uncompute後に元へ戻る。
-/
theorem runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit_other
    (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layout : WriteMovedSelectorSlotLayout p slot outputSelector)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideOutput : wire ∉ outputSelector) :
    (xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit p offset outputSelector slot).runBasis
        reversibleGatePermutation input wire = input wire := by
  let support := xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport p slot
  let compute := xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit p slot
  let pair := oraclePairWire p
  let constant := 6 * slot.val + offset
  let use := controlledXorConstant pair outputSelector constant
  let computed := compute.runBasis reversibleGatePermutation input
  have computeUses : circuitUsesOnly support compute := by
    simpa [support, compute] using xorMovedMemberPositionIntoSelectorOutputCircuitComputeCircuit_usesOnly p slot
  have pairMember : pair ∈ support := by
    simp [pair, support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport]
  have outputOutsideSupport : ∀ target ∈ outputSelector, target ∉ support := by
    intro target outputMember supportMember
    exact (List.disjoint_left.mp layout.output_disjoint_support outputMember)
      supportMember
  have pairAbsentOutput : pair ∉ outputSelector := by
    intro member
    exact outputOutsideSupport pair member pairMember
  have usePreserves : BasisAgreeOn support
      (use.runBasis reversibleGatePermutation computed) computed := by
    intro target supportMember
    rw [show use = controlledXorConstant pair outputSelector constant by rfl]
    rw [runBasis_controlledXorConstant pair outputSelector constant computed
      pairAbsentOutput]
    exact controlledXorConstantBasisAction_outside pair constant 0 outputSelector
      computed target (by
        intro outputMember
        exact outputOutsideSupport target outputMember supportMember)
  have localClean := Circuit.computeUseUncompute_local_clean support compute use input
    computeUses usePreserves
  have stageAsComputeUse :
      xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit p offset outputSelector slot =
        Circuit.computeUseUncompute id compute use := by
    rfl
  rw [stageAsComputeUse, localClean]
  by_cases insideSupport : wire ∈ support
  · exact restoreSupport_agrees_input support input
      (use.runBasis reversibleGatePermutation computed) wire insideSupport
  · rw [restoreSupport_outside support input
      (use.runBasis reversibleGatePermutation computed) wire insideSupport]
    rw [show use = controlledXorConstant pair outputSelector constant by rfl]
    rw [runBasis_controlledXorConstant pair outputSelector constant computed
      pairAbsentOutput]
    rw [controlledXorConstantBasisAction_outside pair constant 0 outputSelector
      computed wire outsideOutput]
    exact Circuit.runBasis_outside_of_usesOnly support compute computeUses input wire
      insideSupport

/-- 指定出力列の外側で二つの基底状態が一致するという有限support用の関係。 -/
def BasisAgreeOutside
    {ancillaQubits systemQubits : Nat}
    (output : List (Wire ancillaQubits systemQubits))
    (left right : JointBasis ancillaQubits systemQubits) : Prop :=
  ∀ wire, wire ∉ output → left wire = right wire

/--
selector出力外で一致する状態では、一slotの受理条件も一致する。
受理条件が読む全wireは静的compute support内にあるためである。
-/
theorem movedSelectorSlotEnabled_congr_outside
    (p : QParameters) (slot : Fin p.K)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (left right : JointBasis p.ancillaWidth p.systemWidth)
    (layout : WriteMovedSelectorSlotLayout p slot outputSelector)
    (agree : BasisAgreeOutside outputSelector left right) :
    movedSelectorSlotEnabled p slot left = movedSelectorSlotEnabled p slot right := by
  let support := xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport p slot
  have outsideOfSupport : ∀ wire ∈ support, wire ∉ outputSelector := by
    intro wire supportMember outputMember
    exact (List.disjoint_left.mp layout.output_disjoint_support outputMember)
      supportMember
  have branchMember : oracleBranchWire p ∈ support := by
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport]
  have markerMember : candidateMarkerWire p (slotToSortWord p slot) ∈ support := by
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport]
  have movedMembers : ∀ wire ∈ oracleMovedWires p, wire ∈ support := by
    intro wire member
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, member]
  have wordMembers : ∀ wire ∈
      (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth,
      wire ∈ support := by
    intro wire member
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, member]
  have branchEqual : left (oracleBranchWire p) = right (oracleBranchWire p) :=
    agree _ (outsideOfSupport _ branchMember)
  have markerEqual :
      left (candidateMarkerWire p (slotToSortWord p slot)) =
        right (candidateMarkerWire p (slotToSortWord p slot)) :=
    agree _ (outsideOfSupport _ markerMember)
  have movedEqual : readWires (oracleMovedWires p) left =
      readWires (oracleMovedWires p) right := by
    apply List.map_congr_left
    intro wire member
    exact agree wire (outsideOfSupport wire (movedMembers wire member))
  have wordEqual :
      readWires
          ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth) left =
        readWires
          ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth) right := by
    apply List.map_congr_left
    intro wire member
    exact agree wire (outsideOfSupport wire (wordMembers wire member))
  simp [movedSelectorSlotEnabled, branchEqual, markerEqual, movedEqual, wordEqual]

/-- selector出力外でclean入力と一致する状態も、一slotのclean条件を満たす。 -/
theorem xorMovedMemberPositionIntoSelectorOutputCircuitSlotClean_of_agreesOutside
    (p : QParameters) (slot : Fin p.K)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (original state : JointBasis p.ancillaWidth p.systemWidth)
    (layout : WriteMovedSelectorSlotLayout p slot outputSelector)
    (clean : WriteMovedSelectorSlotClean p original)
    (agree : BasisAgreeOutside outputSelector state original) :
    WriteMovedSelectorSlotClean p state := by
  let support := xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport p slot
  have outsideOfSupport : ∀ wire ∈ support, wire ∉ outputSelector := by
    intro wire supportMember outputMember
    exact (List.disjoint_left.mp layout.output_disjoint_support outputMember)
      supportMember
  have compareMembers : ∀ wire ∈ oracleCompareWorkWires p, wire ∈ support := by
    intro wire member
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, member]
  have scratchMembers : ∀ wire ∈ decoderAndScratchWires p, wire ∈ support := by
    intro wire member
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport, member]
  have positionMember : oraclePositionWire p ∈ support := by
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport]
  have pairMember : oraclePairWire p ∈ support := by
    simp [support, xorMovedMemberPositionIntoSelectorOutputCircuitComputeSupport]
  refine {
    compare_zero := ?_
    scratch_zero := ?_
    position_zero := ?_
    pair_zero := ?_ }
  · calc
      readWires (oracleCompareWorkWires p) state =
          readWires (oracleCompareWorkWires p) original := by
            apply List.map_congr_left
            intro wire member
            exact agree wire (outsideOfSupport wire (compareMembers wire member))
      _ = List.replicate (oracleCompareWorkWires p).length false := clean.compare_zero
  · intro wire member
    rw [agree wire (outsideOfSupport wire (scratchMembers wire member))]
    exact clean.scratch_zero wire member
  · rw [agree _ (outsideOfSupport _ positionMember)]
    exact clean.position_zero
  · rw [agree _ (outsideOfSupport _ pairMember)]
    exact clean.pair_zero

/--
任意のslot列を順に実行した結果を、純粋selector XOR foldと非出力wire保存へ同時に
帰納する。帰納変数はslot列だけであり、全計算基底の列挙は行わない。
-/
theorem runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitSlotList_correct
    (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (original : JointBasis p.ancillaWidth p.systemWidth)
    (layouts : ∀ slot : Fin p.K,
      WriteMovedSelectorSlotLayout p slot outputSelector)
    (originalClean : WriteMovedSelectorSlotClean p original) :
    ∀ (slots : List (Fin p.K))
      (state : JointBasis p.ancillaWidth p.systemWidth),
      BasisAgreeOutside outputSelector state original →
      let finalState := slots.foldl (fun current slot =>
        (xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit p offset outputSelector slot).runBasis
          reversibleGatePermutation current) state
      readWires outputSelector finalState =
          xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset slots original
            (readWires outputSelector state) ∧
        BasisAgreeOutside outputSelector finalState original
  | [], state, agree => by
      exact ⟨rfl, agree⟩
  | slot :: slots, state, agree => by
      let layout := layouts slot
      let next := (xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit p offset outputSelector slot).runBasis
        reversibleGatePermutation state
      have stateClean : WriteMovedSelectorSlotClean p state :=
        xorMovedMemberPositionIntoSelectorOutputCircuitSlotClean_of_agreesOutside p slot outputSelector
          original state layout originalClean agree
      have nextRead : readWires outputSelector next =
          controlledXorConstantBits (movedSelectorSlotEnabled p slot state)
            (6 * slot.val + offset) 0 (readWires outputSelector state) := by
        simpa [next, layout] using
          readWires_xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit p offset outputSelector slot state
            layout stateClean
      have enabledEqual : movedSelectorSlotEnabled p slot state =
          movedSelectorSlotEnabled p slot original :=
        movedSelectorSlotEnabled_congr_outside p slot outputSelector state original
          layout agree
      have nextAgree : BasisAgreeOutside outputSelector next original := by
        intro wire outside
        rw [show next wire = state wire by
          exact runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitSlotCircuit_other p offset outputSelector
            slot state layout wire outside]
        exact agree wire outside
      have tailResult := runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitSlotList_correct p offset
        outputSelector original layouts originalClean slots next nextAgree
      rw [nextRead, enabledEqual] at tailResult
      simpa [xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom, List.foldl, next] using tailResult

/--
全`Fin K` slotを走査するmoved selector正本の出力は、純粋有限fold仕様に一致する。
仮定は静的layout条件とclean work条件だけであり、受理path契約を引数に取らない。
-/
theorem readWires_xorMovedMemberPositionIntoSelectorOutputCircuit
    (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (layouts : ∀ slot : Fin p.K,
      WriteMovedSelectorSlotLayout p slot outputSelector)
    (clean : WriteMovedSelectorSlotClean p input) :
    readWires outputSelector
        ((xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector).runBasis
          reversibleGatePermutation input) =
      movedMemberPositionSelectorOutputXorReference p offset outputSelector input := by
  rw [runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_slotFold]
  exact (runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitSlotList_correct p offset outputSelector input
    layouts clean (List.finRange p.K) input (by
      intro wire outside
      rfl)).1

/-- degree変化後の出力degreeが`1..K`内なら、そのNat値を返す純粋関数。 -/
def shiftedOutputDegree? (p : QParameters) (degreeSlot : Fin p.K)
    (degreeChange : Int) : Option Nat :=
  let outputDegreeInt := Int.ofNat (degreeSlot.val + 1) + degreeChange
  if (1 : Int) ≤ outputDegreeInt ∧ outputDegreeInt ≤ Int.ofNat p.K then
    some outputDegreeInt.toNat
  else none

/-- sorted出力の一つのdegree branchが有効になる純粋な基底条件。 -/
def sortedOutputDegreeEnabled (p : QParameters) (degreeSlot : Fin p.K)
    (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Bool :=
  match shiftedOutputDegree? p degreeSlot degreeChange with
  | none => false
  | some _ => input (oracleBranchWire p) && input (oracleDegreeWireAt p degreeSlot)

/-- sorted出力の一degree branchでpair flagを計算する正本多重制御回路。 -/
def writeSortedPairComputeCircuit (p : QParameters) (degreeSlot : Fin p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  positiveMultiControlledX
    [oracleBranchWire p, oracleDegreeWireAt p degreeSlot]
    (decoderAndScratchWires p) (oraclePairWire p)

/-- sorted pair計算が参照するoracle-work sliceをまとめた有限support。 -/
def writeSortedPairSupport (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  ((QLayout.oracleSlice (OracleWorkLayout.canonical p).branch).wireList :
      List (Wire p.ancillaWidth p.systemWidth)) ++
  ((QLayout.oracleSlice (OracleWorkLayout.canonical p).degree).wireList :
      List (Wire p.ancillaWidth p.systemWidth)) ++
  ((QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).wireList :
      List (Wire p.ancillaWidth p.systemWidth)) ++
  ((QLayout.oracleSlice (OracleWorkLayout.canonical p).pair).wireList :
      List (Wire p.ancillaWidth p.systemWidth))

/-- pair flag は pair 計算の局所supportに含まれる。 -/
theorem oraclePairWire_mem_writeSortedPairSupport (p : QParameters) :
    oraclePairWire p ∈ writeSortedPairSupport p := by
  simp [writeSortedPairSupport, oraclePairWire, RegisterSlice.wireList]

/-- sorted pair計算回路は明示したoracle-work support内だけを使う。 -/
theorem writeSortedPairComputeCircuit_usesOnly
    (p : QParameters) (degreeSlot : Fin p.K) :
    circuitUsesOnly (writeSortedPairSupport p)
      (writeSortedPairComputeCircuit p degreeSlot) := by
  unfold writeSortedPairComputeCircuit
  apply circuitUsesOnly_positiveMultiControlledX
  · intro wire member
    rcases List.mem_cons.mp member with rfl | member
    · simp [writeSortedPairSupport, oracleBranchWire, oracleSingletonWire,
        RegisterSlice.wireList]
    · have degreeEqual : wire = oracleDegreeWireAt p degreeSlot := by simpa using member
      subst wire
      simp [writeSortedPairSupport, oracleDegreeWireAt, RegisterSlice.wireList]
  · intro wire member
    have andMember : wire ∈
        ((QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [decoderAndScratchWires, oracleAndWorkWires,
        QParameters.andWorkWidth, RegisterSlice.wireList] using
          List.mem_of_mem_drop member
    simp [writeSortedPairSupport, andMember]
  · simp [writeSortedPairSupport, oraclePairWire, RegisterSlice.wireList]

/-- sorted出力のpair計算に必要な静的配置とclean値条件。 -/
structure WriteSortedPairInput (p : QParameters) (degreeSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 二制御ANDに十分なscratchがある。 -/
  scratch_enough : 2 ≤ (decoderAndScratchWires p).length + 1
  /-- controls・scratch・pair targetに重複がない。 -/
  layout_nodup :
    ([oracleBranchWire p, oracleDegreeWireAt p degreeSlot] ++
      decoderAndScratchWires p ++ [oraclePairWire p]).Nodup
  /-- AND scratchは全0である。 -/
  scratch_zero : ∀ wire ∈ decoderAndScratchWires p, input wire = false
  /-- pair targetは0である。 -/
  pair_zero : input (oraclePairWire p) = false

/-- canonical `QLayout` では、scratch と pair が 0 なら sorted 出力用の pair 計算条件が自動的に得られる。 -/
theorem writeSortedPairInput_canonical
    (p : QParameters) (degreeSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false) :
    WriteSortedPairInput p degreeSlot input := by
  let branchSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).branch
  let degreeSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
  let pairSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).pair
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have scratchEnough : 2 ≤ (decoderAndScratchWires p).length + 1 := by
    have wordEnough := decoderAndScratchWires_wordWidth_le p
    have wordLower : 2 ≤ p.wordWidth := by
      have qPositive := p.q_pos
      simp [QParameters.wordWidth]
      omega
    omega
  have scratchNodup : (decoderAndScratchWires p).Nodup :=
    List.Nodup.sublist (by simp) (decoderAndScratchFlags_nodup p)
  have branchNeDegree :
      oracleBranchWire p ≠ oracleDegreeWireAt p degreeSlot := by
    intro equal
    have numbers := congrArg wireNumber equal
    simp [oracleBranchWire, oracleDegreeWireAt, oracleSingletonWire,
      QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
      RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber,
      QParameters.degreeWidth] at numbers
    omega
  have branchNePair : oracleBranchWire p ≠ oraclePairWire p := by
    intro equal
    have numbers := congrArg wireNumber equal
    simp [oracleBranchWire, oraclePairWire, oracleSingletonWire,
      QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
      RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber,
      QParameters.pairWidth] at numbers
    omega
  have degreeNePair : oracleDegreeWireAt p degreeSlot ≠ oraclePairWire p := by
    intro equal
    have numbers := congrArg wireNumber equal
    simp [oracleDegreeWireAt, oraclePairWire,
      QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
      RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber,
      QParameters.degreeWidth, QParameters.pairWidth] at numbers
    omega
  have scratchInAnd : ∀ wire ∈ decoderAndScratchWires p,
      wire ∈ (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    intro wire member
    simpa [decoderAndScratchWires, oracleAndWorkWires, andSlice,
      RegisterSlice.wireList] using List.mem_of_mem_drop member
  have branchBeforeAnd : branchSlice.start + 1 ≤ andSlice.start := by
    simp [branchSlice, andSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have pairBeforeAnd : pairSlice.start + p.pairWidth ≤ andSlice.start := by
    simp [pairSlice, andSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have branchMember : oracleBranchWire p ∈
      (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change branchSlice.ancillaWire 0 ∈
      (branchSlice.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  have pairMember : oraclePairWire p ∈
      (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change pairSlice.ancillaWire ⟨0, by
      simpa [QParameters.pairWidth] using p.K_pos⟩ ∈
      (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨⟨0, by
      simpa [QParameters.pairWidth] using p.K_pos⟩,
      List.mem_finRange _, rfl⟩
  have branchAbsentScratch : oracleBranchWire p ∉ decoderAndScratchWires p := by
    intro member
    exact (List.disjoint_left.mp
      (branchSlice.wireList_disjoint_of_end_le_start andSlice branchBeforeAnd))
      branchMember (scratchInAnd _ member)
  have pairAbsentScratch : oraclePairWire p ∉ decoderAndScratchWires p := by
    intro member
    exact (List.disjoint_left.mp
      (pairSlice.wireList_disjoint_of_end_le_start andSlice pairBeforeAnd))
      pairMember (scratchInAnd _ member)
  have degreeAbsentScratch :
      oracleDegreeWireAt p degreeSlot ∉ decoderAndScratchWires p := by
    intro member
    have degreeMember : oracleDegreeWireAt p degreeSlot ∈ oracleDegreeWires p := by
      simp [oracleDegreeWireAt, oracleDegreeWires, QParameters.degreeWidth]
    exact (List.disjoint_left.mp (oracleDegreeWires_disjoint_andWork p))
      degreeMember (decoderComparisonAndMember p (by simp [member]))
  have controlsNodup :
      [oracleBranchWire p, oracleDegreeWireAt p degreeSlot].Nodup := by
    simp [branchNeDegree]
  have controlsDisjointScratch :
      [oracleBranchWire p, oracleDegreeWireAt p degreeSlot].Disjoint
        (decoderAndScratchWires p) := by
    rw [List.disjoint_left]
    intro wire controlMember scratchMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at controlMember
    rcases controlMember with rfl | rfl
    · exact branchAbsentScratch scratchMember
    · exact degreeAbsentScratch scratchMember
  have prefixNodup :
      ([oracleBranchWire p, oracleDegreeWireAt p degreeSlot] ++
        decoderAndScratchWires p).Nodup :=
    List.nodup_append.mpr ⟨controlsNodup, scratchNodup, by
      intro left leftMember right rightMember equal
      exact (List.disjoint_left.mp controlsDisjointScratch)
        leftMember (equal ▸ rightMember)⟩
  have pairAbsentPrefix : oraclePairWire p ∉
      ([oracleBranchWire p, oracleDegreeWireAt p degreeSlot] ++
        decoderAndScratchWires p) := by
    intro member
    rcases List.mem_append.mp member with controlMember | scratchMember
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at controlMember
      rcases controlMember with equal | equal
      · exact branchNePair equal.symm
      · exact degreeNePair equal.symm
    · exact pairAbsentScratch scratchMember
  refine {
    scratch_enough := scratchEnough
    layout_nodup := ?_
    scratch_zero := scratchZero
    pair_zero := pairZero }
  exact List.nodup_append.mpr ⟨prefixNodup, by simp, by
    intro left leftMember right rightMember equal
    have rightEq : right = oraclePairWire p := by simpa using rightMember
    have leftEq : left = oraclePairWire p := equal.trans rightEq
    exact pairAbsentPrefix (leftEq ▸ leftMember)⟩

/--
clean入力ではsorted出力用pair flagが`branch ∧ degree[slot]`へ厳密に一致する。
-/
theorem runBasis_writeSortedPairComputeCircuit_pair
    (p : QParameters) (degreeSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (conditions : WriteSortedPairInput p degreeSlot input) :
    (writeSortedPairComputeCircuit p degreeSlot).runBasis
        reversibleGatePermutation input (oraclePairWire p) =
      (input (oracleBranchWire p) && input (oracleDegreeWireAt p degreeSlot)) := by
  rw [writeSortedPairComputeCircuit]
  rw [runBasis_positiveMultiControlledX
    [oracleBranchWire p, oracleDegreeWireAt p degreeSlot]
    (decoderAndScratchWires p) (oraclePairWire p) input
    conditions.scratch_enough conditions.layout_nodup conditions.scratch_zero]
  cases branchValue : input (oracleBranchWire p) <;>
    cases degreeValue : input (oracleDegreeWireAt p degreeSlot) <;>
      simp [allWiresTrue, readWires, xBasisAction, conditions.pair_zero,
        branchValue, degreeValue]

/-- `xorSortedCandidatesAsDelimiterIntoOutputCircuit` を構成する一つの degree slot の正本回路を切り出す。 -/
def writeSortedDegreeCircuit (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (degreeChange : Int) (degreeSlot : Fin p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let pairFlag := oraclePairWire p
  let inputDegree := degreeSlot.val + 1
  let outputDegreeInt := Int.ofNat inputDegree + degreeChange
  if valid : (1 : Int) ≤ outputDegreeInt ∧
      outputDegreeInt ≤ Int.ofNat p.K then
    let outputDegree := outputDegreeInt.toNat
    have outputDegreeLe : outputDegree ≤ p.K := by
      dsimp only [outputDegree]
      exact Int.toNat_le.mpr valid.2
    let compute := writeSortedPairComputeCircuit p degreeSlot
    let dataUse := Circuit.sequence <|
      (List.finRange outputDegree).map fun outputSlot =>
        let registerSlot : Fin p.K :=
          ⟨outputSlot.val,
            lt_of_lt_of_le outputSlot.isLt outputDegreeLe⟩
        let candidateSlot : Fin p.sortWordCount :=
          ⟨outputSlot.val, lt_of_lt_of_le registerSlot.isLt
            p.K_le_sortWordCount⟩
        controlledXorCopy pairFlag
          ((candidateWordAt p candidateSlot).take p.wordWidth)
          (registerWordAt p output registerSlot)
    have delimiterLt : p.wordWidth * outputDegree < output.length := by
      rw [outputLength]
      calc
        p.wordWidth * outputDegree ≤ p.wordWidth * p.K :=
          Nat.mul_le_mul_left p.wordWidth outputDegreeLe
        _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _
        _ = p.systemWidth := rfl
    let delimiter := output.get ⟨p.wordWidth * outputDegree, delimiterLt⟩
    let delimiterUse := safeCnot pairFlag delimiter
    let activeUse := safeCnot pairFlag outputActive
    Circuit.computeUseUncompute id compute <|
      .seq dataUse <| .seq delimiterUse activeUse
  else .identity

/-- 正本の `xorSortedCandidatesAsDelimiterIntoOutputCircuit` は、切り出した degree slot 回路列と定義上同一である。 -/
theorem xorSortedCandidatesAsDelimiterIntoOutputCircuit_eq_degreeSequence (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (degreeChange : Int) :
    xorSortedCandidatesAsDelimiterIntoOutputCircuit p output outputLength outputActive degreeChange =
      Circuit.sequence ((List.finRange p.K).map fun degreeSlot =>
        writeSortedDegreeCircuit p output outputLength outputActive degreeChange
          degreeSlot) := by
  rfl

/-- 正本 sorted 出力回路の基底作用は、一般の `K` に対する degree slot の有限 fold である。 -/
theorem runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_degreeFold (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (xorSortedCandidatesAsDelimiterIntoOutputCircuit p output outputLength outputActive degreeChange).runBasis
        reversibleGatePermutation input =
      (List.finRange p.K).foldl (fun state degreeSlot =>
        (writeSortedDegreeCircuit p output outputLength outputActive degreeChange
          degreeSlot).runBasis reversibleGatePermutation state) input := by
  rw [xorSortedCandidatesAsDelimiterIntoOutputCircuit_eq_degreeSequence]
  rw [Circuit.runBasis_sequence]
  simp only [List.foldl_map]

/-- canonical layout と clean work から、各 degree slot の内部 pair 計算の意味論を直接得る。 -/
theorem runBasis_writeSortedPairComputeCircuit_pair_canonical
    (p : QParameters) (degreeSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false) :
    (writeSortedPairComputeCircuit p degreeSlot).runBasis
        reversibleGatePermutation input (oraclePairWire p) =
      (input (oracleBranchWire p) && input (oracleDegreeWireAt p degreeSlot)) := by
  exact runBasis_writeSortedPairComputeCircuit_pair p degreeSlot input
    (writeSortedPairInput_canonical p degreeSlot input scratchZero pairZero)

/-- canonical clean 入力では pair 計算回路全体が、必要時の pair 一本の反転に一致する。 -/
theorem runBasis_writeSortedPairComputeCircuit_canonical
    (p : QParameters) (degreeSlot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false) :
    (writeSortedPairComputeCircuit p degreeSlot).runBasis
        reversibleGatePermutation input =
      if input (oracleBranchWire p) && input (oracleDegreeWireAt p degreeSlot)
      then xBasisAction (oraclePairWire p) input
      else input := by
  have conditions := writeSortedPairInput_canonical p degreeSlot input scratchZero
    pairZero
  rw [writeSortedPairComputeCircuit]
  rw [runBasis_positiveMultiControlledX
    [oracleBranchWire p, oracleDegreeWireAt p degreeSlot]
    (decoderAndScratchWires p) (oraclePairWire p) input
    conditions.scratch_enough conditions.layout_nodup conditions.scratch_zero]
  cases branchValue : input (oracleBranchWire p) <;>
    cases degreeValue : input (oracleDegreeWireAt p degreeSlot) <;>
      simp [allWiresTrue, readWires, branchValue, degreeValue]

/-- 正本で sorted 出力先として使う二種類の canonical register。 -/
inductive CanonicalSortedOutputKind where
  /-- column oracle が書き込む row-output register。 -/
  | rowOutput
  /-- row oracle が書き込む column-key register。 -/
  | columnKey
  deriving DecidableEq

/-- canonical な sorted 出力 register の wire 列。 -/
def canonicalSortedOutputWires (p : QParameters) :
    CanonicalSortedOutputKind → List (Wire p.ancillaWidth p.systemWidth)
  | .rowOutput => rowOutputWires p
  | .columnKey => columnKeyWires p

/-- canonical な sorted 出力に対応する active signal。 -/
def canonicalSortedOutputActive (p : QParameters) :
    CanonicalSortedOutputKind → Wire p.ancillaWidth p.systemWidth
  | .rowOutput => activeWire p
  | .columnKey => keySignalWire p

/-- canonical sorted 出力 register の長さは常に system 幅である。 -/
@[simp] theorem canonicalSortedOutputWires_length
    (p : QParameters) (kind : CanonicalSortedOutputKind) :
    (canonicalSortedOutputWires p kind).length = p.systemWidth := by
  cases kind <;> simp [canonicalSortedOutputWires, rowOutputWires,
    columnKeyWires]

/-- canonical sorted 出力 register に wire の重複はない。 -/
theorem canonicalSortedOutputWires_nodup
    (p : QParameters) (kind : CanonicalSortedOutputKind) :
    (canonicalSortedOutputWires p kind).Nodup := by
  cases kind
  · let slice := (QLayout.canonical p).rowOutput
    simpa [canonicalSortedOutputWires, rowOutputWires, rowOutputWire, slice,
      RegisterSlice.wireList] using
        (slice.wireList_nodup :
          (slice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Nodup)
  · simpa [canonicalSortedOutputWires] using columnKeyWires_nodup p

/-- canonical sorted 出力 register は任意の oracle-work 部分 slice と交わらない。 -/
theorem canonicalSortedOutputWires_disjoint_oracleSlice
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    {width : Nat} (slice : RegisterSlice p.oracleWorkWidth width) :
    (canonicalSortedOutputWires p kind).Disjoint
      ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  cases kind with
  | columnKey =>
      simpa [canonicalSortedOutputWires] using
        columnKeyWires_disjoint_oracleSlice p slice
  | rowOutput =>
      let outputSlice := (QLayout.canonical p).rowOutput
      let lifted := QLayout.oracleSlice slice
      have separated : outputSlice.start + p.systemWidth ≤ lifted.start := by
        simp [outputSlice, lifted, QLayout.canonical, QLayout.oracleSlice,
          RegisterSlice.compose]
        omega
      have full :
          (outputSlice.wireList :
              List (Wire p.ancillaWidth p.systemWidth)).Disjoint
            (lifted.wireList :
              List (Wire p.ancillaWidth p.systemWidth)) :=
        outputSlice.wireList_disjoint_of_end_le_start lifted separated
      simpa [canonicalSortedOutputWires, rowOutputWires, rowOutputWire,
        outputSlice, lifted, RegisterSlice.wireList] using full

/-- canonical active signal は対応する出力 register の外側にある。 -/
theorem canonicalSortedOutputActive_not_mem_output
    (p : QParameters) (kind : CanonicalSortedOutputKind) :
    canonicalSortedOutputActive p kind ∉ canonicalSortedOutputWires p kind := by
  cases kind with
  | rowOutput =>
      let outputSlice := (QLayout.canonical p).rowOutput
      let signalSlice := (QLayout.canonical p).active
      have separated : outputSlice.start + p.systemWidth ≤ signalSlice.start := by
        simp [outputSlice, signalSlice, QLayout.canonical]
        omega
      have disjoint :
          (outputSlice.wireList :
              List (Wire p.ancillaWidth p.systemWidth)).Disjoint
            (signalSlice.wireList :
              List (Wire p.ancillaWidth p.systemWidth)) :=
        outputSlice.wireList_disjoint_of_end_le_start signalSlice separated
      intro member
      apply (List.disjoint_left.mp disjoint)
        (by simpa [canonicalSortedOutputWires, rowOutputWires, rowOutputWire,
          outputSlice, RegisterSlice.wireList] using member)
      change signalSlice.ancillaWire 0 ∈
        (signalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth))
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  | columnKey =>
      let outputSlice := (QLayout.canonical p).columnKey
      let signalSlice := (QLayout.canonical p).keySignal
      have separated : outputSlice.start + p.systemWidth ≤ signalSlice.start := by
        simp [outputSlice, signalSlice, QLayout.canonical]
      have disjoint :
          (outputSlice.wireList :
              List (Wire p.ancillaWidth p.systemWidth)).Disjoint
            (signalSlice.wireList :
              List (Wire p.ancillaWidth p.systemWidth)) :=
        outputSlice.wireList_disjoint_of_end_le_start signalSlice separated
      intro member
      apply (List.disjoint_left.mp disjoint)
        (by simpa [canonicalSortedOutputWires, columnKeyWires, columnKeyWire,
          outputSlice, RegisterSlice.wireList] using member)
      change signalSlice.ancillaWire 0 ∈
        (signalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth))
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩

/-- canonical active signal は任意の oracle-work 部分 slice の外側にある。 -/
theorem canonicalSortedOutputActive_not_mem_oracleSlice
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    {width : Nat} (slice : RegisterSlice p.oracleWorkWidth width) :
    canonicalSortedOutputActive p kind ∉
      ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  let signalSlice : RegisterSlice p.ancillaWidth 1 :=
    match kind with
    | .rowOutput => (QLayout.canonical p).active
    | .columnKey => (QLayout.canonical p).keySignal
  let lifted := QLayout.oracleSlice slice
  have separated : signalSlice.start + 1 ≤ lifted.start := by
    cases kind
    · simp [signalSlice, lifted, QLayout.canonical, QLayout.oracleSlice,
        RegisterSlice.compose]
    · simp [signalSlice, lifted, QLayout.canonical, QLayout.oracleSlice,
        RegisterSlice.compose]
      omega
  have disjoint :
      (signalSlice.wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (lifted.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
    signalSlice.wireList_disjoint_of_end_le_start lifted separated
  intro member
  apply (List.disjoint_left.mp disjoint) ?_ (by simpa [lifted] using member)
  cases kind
  · change signalSlice.ancillaWire 0 ∈
      (signalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  · change signalSlice.ancillaWire 0 ∈
      (signalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩

/-- canonical sorted 出力 register は pair 計算が使う全 work wire と交わらない。 -/
theorem canonicalSortedOutputWires_disjoint_writeSortedPairSupport
    (p : QParameters) (kind : CanonicalSortedOutputKind) :
    (canonicalSortedOutputWires p kind).Disjoint (writeSortedPairSupport p) := by
  rw [List.disjoint_left]
  intro wire outputMember supportMember
  simp only [writeSortedPairSupport, List.mem_append] at supportMember
  rcases supportMember with supportMember | pairMember
  · rcases supportMember with supportMember | andMember
    · rcases supportMember with branchMember | degreeMember
      · exact (List.disjoint_left.mp
      (canonicalSortedOutputWires_disjoint_oracleSlice p kind
        (OracleWorkLayout.canonical p).branch)) outputMember branchMember
      · exact (List.disjoint_left.mp
          (canonicalSortedOutputWires_disjoint_oracleSlice p kind
            (OracleWorkLayout.canonical p).degree)) outputMember degreeMember
    · exact (List.disjoint_left.mp
        (canonicalSortedOutputWires_disjoint_oracleSlice p kind
          (OracleWorkLayout.canonical p).andWork)) outputMember andMember
  · exact (List.disjoint_left.mp
      (canonicalSortedOutputWires_disjoint_oracleSlice p kind
        (OracleWorkLayout.canonical p).pair)) outputMember pairMember

/-- canonical active signal は pair 計算が使う全 work wire の外側にある。 -/
theorem canonicalSortedOutputActive_not_mem_writeSortedPairSupport
    (p : QParameters) (kind : CanonicalSortedOutputKind) :
    canonicalSortedOutputActive p kind ∉ writeSortedPairSupport p := by
  intro supportMember
  simp only [writeSortedPairSupport, List.mem_append] at supportMember
  rcases supportMember with supportMember | pairMember
  · rcases supportMember with supportMember | andMember
    · rcases supportMember with branchMember | degreeMember
      · exact canonicalSortedOutputActive_not_mem_oracleSlice p kind
          (OracleWorkLayout.canonical p).branch branchMember
      · exact canonicalSortedOutputActive_not_mem_oracleSlice p kind
          (OracleWorkLayout.canonical p).degree degreeMember
    · exact canonicalSortedOutputActive_not_mem_oracleSlice p kind
        (OracleWorkLayout.canonical p).andWork andMember
  · exact canonicalSortedOutputActive_not_mem_oracleSlice p kind
      (OracleWorkLayout.canonical p).pair pairMember

/-- pair flag は candidate 全体 slice の外側にある。 -/
theorem oraclePairWire_not_mem_candidateSlice (p : QParameters) :
    oraclePairWire p ∉
      ((QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  let candidateSlice :=
    QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  let pairSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).pair
  have separated : candidateSlice.start + p.candidateWidth ≤ pairSlice.start := by
    simp [candidateSlice, pairSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have disjoint :
      (candidateSlice.wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (pairSlice.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
    candidateSlice.wireList_disjoint_of_end_le_start pairSlice separated
  intro member
  apply (List.disjoint_left.mp disjoint) (by simpa [candidateSlice] using member)
  change pairSlice.ancillaWire ⟨0, by
      simpa [QParameters.pairWidth] using p.K_pos⟩ ∈
    (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth))
  rw [RegisterSlice.wireList]
  exact List.mem_map.mpr ⟨⟨0, by
    simpa [QParameters.pairWidth] using p.K_pos⟩,
    List.mem_finRange _, rfl⟩

/--
When enabled, XOR corresponding source/target bits without using a circuit
execution function. The control value and all source values are read from the
state before each corresponding target update.
-/
def controlledCopyBasisReference
    {ancillaQubits systemQubits : Nat} (enabled : Bool)
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if enabled then (TotalReversibleStage.xorCopy source target).reference input
  else input

/-- 純粋controlled-copy参照作用はtarget列の外側を変更しない。 -/
theorem controlledCopyBasisReference_outside_target
    {ancillaQubits systemQubits : Nat} (enabled : Bool)
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits) (outside : wire ∉ target) :
    controlledCopyBasisReference enabled source target input wire = input wire := by
  cases enabled with
  | false => simp [controlledCopyBasisReference]
  | true =>
      simp only [controlledCopyBasisReference, if_true]
      exact TotalReversibleStage.xorCopy_reference_apply_outside_target
        source target input wire outside

/-- control が偽なら、純粋な controlled-copy 参照作用は恒等作用である。 -/
@[simp] theorem controlledCopyBasisReference_false
    {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) :
    controlledCopyBasisReference false source target input = input := by
  simp [controlledCopyBasisReference]

/-- control が真なら、純粋参照作用は通常の bitwise XOR copy の基底作用に一致する。 -/
theorem controlledCopyBasisReference_true_eq_runBasis_xorCopy
    {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (_sourceDisjointTarget : source.Disjoint target) :
    controlledCopyBasisReference true source target input =
      (xorCopy source target).runBasis reversibleGatePermutation input := by
  simp only [controlledCopyBasisReference, if_true]
  rw [← TotalReversibleStage.compiledStage_runBasis_eq_reference,
    TotalReversibleStage.compile_xorCopy]

/--
On a validated layout, the frozen XOR-copy execution agrees with the
circuit-independent controlled-copy reference at enabled control.
-/
theorem runBasis_validatedXorCopyLists_eq_controlledCopyBasisReference_true
    {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target) :
    (xorCopy source target).runBasis reversibleGatePermutation input =
      controlledCopyBasisReference true source target input := by
  let layout := ValidatedRegisterXorCopyLayout.ofLists source target
    sourceNodup targetNodup sameLength sourceTargetDisjoint
  calc
    (xorCopy source target).runBasis reversibleGatePermutation input =
        layout.basisAction input := by
      simpa [layout] using runBasis_validatedXorCopy_eq_basisAction layout input
    _ = controlledCopyBasisReference true source target input := by
      simp only [controlledCopyBasisReference, if_true]
      exact (by
        simpa [layout] using
          (layout.xorCopyStage_reference_eq_basisAction input).symm)

/-- A validated controlled-copy reference preserves every target-external wire. -/
theorem controlledCopyBasisReference_validated_outside_target
    {ancillaQubits systemQubits : Nat} (enabled : Bool)
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (wire : Wire ancillaQubits systemQubits) (outside : wire ∉ target) :
    controlledCopyBasisReference enabled source target input wire = input wire := by
  cases enabled with
  | false => simp [controlledCopyBasisReference]
  | true =>
      let layout := ValidatedRegisterXorCopyLayout.ofLists source target
        sourceNodup targetNodup sameLength sourceTargetDisjoint
      simp only [controlledCopyBasisReference, if_true]
      rw [show (TotalReversibleStage.xorCopy source target).reference input =
          layout.basisAction input by
        simpa [layout] using layout.xorCopyStage_reference_eq_basisAction input]
      apply layout.basisAction_applyOutside
      intro index equal
      apply outside
      change wire = target.get (Fin.cast sameLength index) at equal
      exact equal.symm ▸ List.get_mem target (Fin.cast sameLength index)

/--
On a validated copy layout, XOR on a wire outside both registers commutes with
the shared pure copy action.
-/
theorem controlledCopyBasisReference_x_outside
    {ancillaQubits systemQubits : Nat} (enabled : Bool)
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceDisjointTarget : source.Disjoint target)
    (outsideSource : wire ∉ source) (outsideTarget : wire ∉ target) :
    controlledCopyBasisReference enabled source target (xBasisAction wire input) =
      xBasisAction wire (controlledCopyBasisReference enabled source target input) := by
  cases enabled with
  | false => simp [controlledCopyBasisReference]
  | true =>
      let layout := ValidatedRegisterXorCopyLayout.ofLists source target
        sourceNodup targetNodup sameLength sourceDisjointTarget
      calc
        controlledCopyBasisReference true source target
            (xBasisAction wire input) =
          layout.basisAction (xBasisAction wire input) := by
            simp only [controlledCopyBasisReference, if_true]
            simpa [layout] using
              layout.xorCopyStage_reference_eq_basisAction
                (xBasisAction wire input)
        _ = xBasisAction wire (layout.basisAction input) :=
          layout.basisAction_commutes_xBasisAction_outside wire input
            (fun index equal => outsideSource (by
              simpa [layout, ValidatedRegisterXorCopyLayout.ofLists] using
                (equal ▸ List.get_mem source index)))
            (fun index equal => outsideTarget (by
              have membership := List.get_mem target
                (Fin.cast sameLength index)
              simpa [layout, ValidatedRegisterXorCopyLayout.ofLists] using
                (equal ▸ membership)))
        _ = xBasisAction wire
            (controlledCopyBasisReference true source target input) := by
          congr 1
          simp only [controlledCopyBasisReference, if_true]
          symm
          simpa [layout] using
            layout.xorCopyStage_reference_eq_basisAction input

/--
The validated frozen compiler executes the shared conditional pure action.
The target reference is assembled from shared register actions and contains no
raw-list collision or zip-truncation correctness proof.
-/
theorem runBasis_validatedControlledXorCopyLists_eq_controlledCopyBasisReference
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceDisjointTarget : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target) :
    (controlledXorCopy control source target).runBasis
        reversibleGatePermutation input =
      controlledCopyBasisReference (input control) source target input := by
  let layout := ValidatedControlledRegisterXorCopyLayout.ofLists control
    source target sourceNodup targetNodup sameLength sourceDisjointTarget
    controlAbsentSource controlAbsentTarget
  calc
    (controlledXorCopy control source target).runBasis
        reversibleGatePermutation input = layout.basisAction input := by
      simpa [layout] using
        runBasis_validatedControlledXorCopy_eq_basisAction layout input
    _ = if input control then
          layout.toRegisterXorCopyLayout.basisAction input
        else input := layout.basisAction_eq_if input
    _ = controlledCopyBasisReference (input control) source target input := by
      cases controlValue : input control
      · simp [controlledCopyBasisReference]
      · simp only [if_true, controlledCopyBasisReference]
        symm
        simpa [layout,
          ValidatedControlledRegisterXorCopyLayout.toRegisterXorCopyLayout]
          using
            (ValidatedRegisterXorCopyLayout.xorCopyStage_reference_eq_basisAction
              layout.toRegisterXorCopyLayout input)

/-- output degree 内の slot を物理 register の `Fin K` slot へ埋め込む。 -/
def sortedOutputRegisterSlot (p : QParameters) (outputDegree : Nat)
    (outputDegreeLe : outputDegree ≤ p.K) (slot : Fin outputDegree) : Fin p.K :=
  ⟨slot.val, lt_of_lt_of_le slot.isLt outputDegreeLe⟩

/-- output degree 内の slot を padding 込み candidate slot へ埋め込む。 -/
def sortedOutputCandidateSlot (p : QParameters) (outputDegree : Nat)
    (outputDegreeLe : outputDegree ≤ p.K) (slot : Fin outputDegree) :
    Fin p.sortWordCount :=
  let registerSlot := sortedOutputRegisterSlot p outputDegree outputDegreeLe slot
  ⟨slot.val, lt_of_lt_of_le registerSlot.isLt p.K_le_sortWordCount⟩

/-- sorted data 部の一つの candidate-word copy 回路。 -/
def writeSortedCopyCircuit (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (slot : Fin outputDegree) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  controlledXorCopy (oraclePairWire p)
    ((candidateWordAt p
      (sortedOutputCandidateSlot p outputDegree outputDegreeLe slot)).take
        p.wordWidth)
    (registerWordAt p output
      (sortedOutputRegisterSlot p outputDegree outputDegreeLe slot))

/-- sorted data 部の一つの candidate-word copy に対応する純粋基底作用。 -/
def writeSortedCopyReference (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (slot : Fin outputDegree)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  controlledCopyBasisReference enabled
    ((candidateWordAt p
      (sortedOutputCandidateSlot p outputDegree outputDegreeLe slot)).take
        p.wordWidth)
    (registerWordAt p output
      (sortedOutputRegisterSlot p outputDegree outputDegreeLe slot)) input

/-- sortedの一word copy参照作用は出力register外を変更しない。 -/
theorem writeSortedCopyReference_outside
    (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (slot : Fin outputDegree)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth) (outside : wire ∉ output) :
    writeSortedCopyReference p output outputDegree outputDegreeLe enabled slot input wire =
      input wire := by
  apply controlledCopyBasisReference_outside_target
  intro targetMember
  apply outside
  exact mem_register_of_mem_registerWordAt p output
    (sortedOutputRegisterSlot p outputDegree outputDegreeLe slot) targetMember

/-- sorted data 部全体を基本ゲート回路列として構成する。 -/
def writeSortedDataUseCircuit (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  Circuit.sequence <| (List.finRange outputDegree).map fun slot =>
    writeSortedCopyCircuit p output outputDegree outputDegreeLe slot

/-- sorted data 部全体の行列非展開な純粋基底参照作用。 -/
def writeSortedDataReference (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (List.finRange outputDegree).foldl (fun state slot =>
    writeSortedCopyReference p output outputDegree outputDegreeLe enabled slot state)
    input

/-- 任意のslot列を走査するsorted data参照foldは出力register外を変更しない。 -/
theorem writeSortedCopyReference_fold_outside
    (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (slots : List (Fin outputDegree))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth) (outside : wire ∉ output) :
    slots.foldl (fun state slot =>
        writeSortedCopyReference p output outputDegree outputDegreeLe enabled slot state)
        input wire = input wire := by
  induction slots generalizing input with
  | nil => rfl
  | cons slot slots inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      exact writeSortedCopyReference_outside p output outputDegree outputDegreeLe
        enabled slot input wire outside

/-- sorted data参照作用全体は出力register外を変更しない。 -/
theorem writeSortedDataReference_outside
    (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth) (outside : wire ∉ output) :
    writeSortedDataReference p output outputDegree outputDegreeLe enabled input wire =
      input wire := by
  exact writeSortedCopyReference_fold_outside p output outputDegree outputDegreeLe
    enabled (List.finRange outputDegree) input wire outside

/-- canonical 出力では各 candidate source と対応する output target が型安全に分離される。 -/
theorem canonicalSortedCopyLayout
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (candidateSlot : Fin p.sortWordCount) (registerSlot : Fin p.K) :
    let source := (candidateWordAt p candidateSlot).take p.wordWidth
    let target := registerWordAt p (canonicalSortedOutputWires p kind) registerSlot
    source.length = target.length ∧ source.Disjoint target ∧
      oraclePairWire p ∉ source ∧ oraclePairWire p ∉ target := by
  dsimp only
  let source := (candidateWordAt p candidateSlot).take p.wordWidth
  let target := registerWordAt p (canonicalSortedOutputWires p kind) registerSlot
  let candidateSlice :=
    QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  have outputDisjointCandidate :=
    canonicalSortedOutputWires_disjoint_oracleSlice p kind
      (OracleWorkLayout.canonical p).candidate
  have sameLength : source.length = target.length := by
    rw [show source.length = p.wordWidth by
      simp [source, candidateWordAt_data_length p candidateSlot]]
    symm
    exact registerWordAt_length p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind) registerSlot
  have sourceDisjointTarget : source.Disjoint target := by
    rw [List.disjoint_left]
    intro wire sourceMember targetMember
    have candidateMember : wire ∈
        (candidateSlice.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
      candidateWordAt_mem_candidateSlice p candidateSlot
        (List.mem_of_mem_take sourceMember)
    have outputMember : wire ∈ canonicalSortedOutputWires p kind :=
      mem_register_of_mem_registerWordAt p
        (canonicalSortedOutputWires p kind) registerSlot targetMember
    exact (List.disjoint_left.mp outputDisjointCandidate)
      outputMember candidateMember
  have pairAbsentSource : oraclePairWire p ∉ source := by
    intro member
    exact oraclePairWire_not_mem_candidateSlice p
      (candidateWordAt_mem_candidateSlice p candidateSlot
        (List.mem_of_mem_take member))
  have pairAbsentTarget : oraclePairWire p ∉ target := by
    intro member
    have outputMember : oraclePairWire p ∈ canonicalSortedOutputWires p kind :=
      mem_register_of_mem_registerWordAt p
        (canonicalSortedOutputWires p kind) registerSlot member
    have outputDisjointPair :=
      canonicalSortedOutputWires_disjoint_oracleSlice p kind
        (OracleWorkLayout.canonical p).pair
    have pairMember : oraclePairWire p ∈
        ((QLayout.oracleSlice (OracleWorkLayout.canonical p).pair).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      let pairSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).pair
      change pairSlice.ancillaWire ⟨0, by
          simpa [QParameters.pairWidth] using p.K_pos⟩ ∈
        (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth))
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨⟨0, by
        simpa [QParameters.pairWidth] using p.K_pos⟩,
        List.mem_finRange _, rfl⟩
    exact (List.disjoint_left.mp outputDisjointPair) outputMember pairMember
  exact ⟨sameLength, sourceDisjointTarget, pairAbsentSource, pairAbsentTarget⟩

/-- canonical 一word参照作用は、そのsource・target外にある pair flag のX作用と可換である。 -/
theorem writeSortedCopyReference_x_pair_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (slot : Fin outputDegree)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    writeSortedCopyReference p (canonicalSortedOutputWires p kind) outputDegree
        outputDegreeLe enabled slot (xBasisAction (oraclePairWire p) input) =
      xBasisAction (oraclePairWire p)
        (writeSortedCopyReference p (canonicalSortedOutputWires p kind)
          outputDegree outputDegreeLe enabled slot input) := by
  let candidateSlot :=
    sortedOutputCandidateSlot p outputDegree outputDegreeLe slot
  let registerSlot := sortedOutputRegisterSlot p outputDegree outputDegreeLe slot
  have layout := canonicalSortedCopyLayout p kind candidateSlot registerSlot
  have sourceNodup :
      ((candidateWordAt p candidateSlot).take p.wordWidth).Nodup :=
    (candidateWordAt_nodup p candidateSlot).take
  have targetNodup :
      (registerWordAt p (canonicalSortedOutputWires p kind)
        registerSlot).Nodup := by
    unfold registerWordAt
    exact (canonicalSortedOutputWires_nodup p kind).drop.take
  exact controlledCopyBasisReference_x_outside enabled
    ((candidateWordAt p candidateSlot).take p.wordWidth)
    (registerWordAt p (canonicalSortedOutputWires p kind) registerSlot) input
    (oraclePairWire p) sourceNodup targetNodup layout.1 layout.2.1
    layout.2.2.1 layout.2.2.2

/-- 任意slot列のcanonical data参照foldは pair flag のX作用と可換である。 -/
theorem writeSortedCopyReference_fold_x_pair_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (slots : List (Fin outputDegree))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    slots.foldl (fun state slot =>
        writeSortedCopyReference p (canonicalSortedOutputWires p kind)
          outputDegree outputDegreeLe enabled slot state)
        (xBasisAction (oraclePairWire p) input) =
      xBasisAction (oraclePairWire p)
        (slots.foldl (fun state slot =>
          writeSortedCopyReference p (canonicalSortedOutputWires p kind)
            outputDegree outputDegreeLe enabled slot state) input) := by
  induction slots generalizing input with
  | nil => rfl
  | cons slot slots inductionHypothesis =>
      rw [List.foldl_cons, List.foldl_cons,
        writeSortedCopyReference_x_pair_canonical]
      exact inductionHypothesis
        (writeSortedCopyReference p (canonicalSortedOutputWires p kind)
          outputDegree outputDegreeLe enabled slot input)

/-- canonical sorted data参照作用全体は pair flag のX作用と可換である。 -/
theorem writeSortedDataReference_x_pair_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (input : JointBasis p.ancillaWidth p.systemWidth) :
    writeSortedDataReference p (canonicalSortedOutputWires p kind) outputDegree
        outputDegreeLe enabled (xBasisAction (oraclePairWire p) input) =
      xBasisAction (oraclePairWire p)
        (writeSortedDataReference p (canonicalSortedOutputWires p kind)
          outputDegree outputDegreeLe enabled input) := by
  exact writeSortedCopyReference_fold_x_pair_canonical p kind outputDegree
    outputDegreeLe enabled (List.finRange outputDegree) input

/-- 任意の slot 部分列について、実回路列と純粋 data 参照作用が一致し pair flag を保存する。 -/
theorem runBasis_writeSortedCopyList_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) :
    ∀ (slots : List (Fin outputDegree))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      input (oraclePairWire p) = enabled →
      let finalState := slots.foldl (fun state slot =>
        (writeSortedCopyCircuit p (canonicalSortedOutputWires p kind)
          outputDegree outputDegreeLe slot).runBasis
            reversibleGatePermutation state) input
      finalState = slots.foldl (fun state slot =>
          writeSortedCopyReference p (canonicalSortedOutputWires p kind)
            outputDegree outputDegreeLe enabled slot state) input ∧
        finalState (oraclePairWire p) = enabled
  | [], input, pairValue => by
      exact ⟨rfl, pairValue⟩
  | slot :: slots, input, pairValue => by
      let source := (candidateWordAt p
        (sortedOutputCandidateSlot p outputDegree outputDegreeLe slot)).take
          p.wordWidth
      let target := registerWordAt p (canonicalSortedOutputWires p kind)
        (sortedOutputRegisterSlot p outputDegree outputDegreeLe slot)
      let next := (writeSortedCopyCircuit p
        (canonicalSortedOutputWires p kind) outputDegree outputDegreeLe slot).runBasis
          reversibleGatePermutation input
      have layout := canonicalSortedCopyLayout p kind
        (sortedOutputCandidateSlot p outputDegree outputDegreeLe slot)
        (sortedOutputRegisterSlot p outputDegree outputDegreeLe slot)
      have sourceNodup : source.Nodup := by
        dsimp [source]
        exact (candidateWordAt_nodup p
          (sortedOutputCandidateSlot p outputDegree outputDegreeLe slot)).take
      have targetNodup : target.Nodup := by
        dsimp [target, registerWordAt]
        exact (canonicalSortedOutputWires_nodup p kind).drop.take
      have nextEq : next = writeSortedCopyReference p
          (canonicalSortedOutputWires p kind) outputDegree outputDegreeLe enabled
          slot input := by
        change (controlledXorCopy (oraclePairWire p) source target).runBasis
            reversibleGatePermutation input =
          controlledCopyBasisReference enabled source target input
        rw [runBasis_validatedControlledXorCopyLists_eq_controlledCopyBasisReference
          (oraclePairWire p) source target input sourceNodup targetNodup
          layout.1 layout.2.1 layout.2.2.1 layout.2.2.2]
        rw [pairValue]
      have nextPair : next (oraclePairWire p) = enabled := by
        change (controlledXorCopy (oraclePairWire p) source target).runBasis
            reversibleGatePermutation input (oraclePairWire p) = enabled
        rw [runBasis_validatedControlledXorCopyLists_outside
          (oraclePairWire p) source target input sourceNodup targetNodup
          layout.1 layout.2.1 layout.2.2.1 layout.2.2.2
          (oraclePairWire p) layout.2.2.2]
        exact pairValue
      have tail := runBasis_writeSortedCopyList_canonical p kind outputDegree
        outputDegreeLe enabled slots next nextPair
      simpa [List.foldl, next, nextEq] using tail

/-- canonical sorted data-use 回路全体は純粋な finite-fold 参照作用に一致する。 -/
theorem runBasis_writeSortedDataUseCircuit_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (pairValue : input (oraclePairWire p) = enabled) :
    (writeSortedDataUseCircuit p (canonicalSortedOutputWires p kind)
      outputDegree outputDegreeLe).runBasis reversibleGatePermutation input =
      writeSortedDataReference p (canonicalSortedOutputWires p kind)
        outputDegree outputDegreeLe enabled input := by
  rw [writeSortedDataUseCircuit, Circuit.runBasis_sequence]
  simp only [List.foldl_map]
  exact (runBasis_writeSortedCopyList_canonical p kind outputDegree outputDegreeLe
    enabled (List.finRange outputDegree) input pairValue).1

/-- canonical 出力 register は pair flag を含まない。 -/
theorem oraclePairWire_not_mem_canonicalSortedOutput
    (p : QParameters) (kind : CanonicalSortedOutputKind) :
    oraclePairWire p ∉ canonicalSortedOutputWires p kind := by
  intro member
  have disjoint := canonicalSortedOutputWires_disjoint_oracleSlice p kind
    (OracleWorkLayout.canonical p).pair
  have pairMember : oraclePairWire p ∈
      ((QLayout.oracleSlice (OracleWorkLayout.canonical p).pair).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
    let pairSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).pair
    change pairSlice.ancillaWire ⟨0, by
        simpa [QParameters.pairWidth] using p.K_pos⟩ ∈
      (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨⟨0, by
      simpa [QParameters.pairWidth] using p.K_pos⟩,
      List.mem_finRange _, rfl⟩
  exact (List.disjoint_left.mp disjoint) member pairMember

/-- canonical active signal と pair flag は異なる wire である。 -/
theorem canonicalSortedOutputActive_ne_pair
    (p : QParameters) (kind : CanonicalSortedOutputKind) :
    canonicalSortedOutputActive p kind ≠ oraclePairWire p := by
  intro equal
  apply canonicalSortedOutputActive_not_mem_oracleSlice p kind
    (OracleWorkLayout.canonical p).pair
  let pairSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).pair
  have pairMember : oraclePairWire p ∈
      (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change pairSlice.ancillaWire ⟨0, by
        simpa [QParameters.pairWidth] using p.K_pos⟩ ∈
      (pairSlice.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨⟨0, by
      simpa [QParameters.pairWidth] using p.K_pos⟩,
      List.mem_finRange _, rfl⟩
  exact equal ▸ pairMember

/-- 指定した出力 index が存在すれば、その wire を条件付きで反転する純粋基底作用。 -/
def toggleOutputIndexReference
    {ancillaQubits systemQubits : Nat} (enabled : Bool)
    (output : List (Wire ancillaQubits systemQubits)) (index : Nat)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  match output[index]? with
  | none => input
  | some target => if enabled then xBasisAction target input else input

/-- 範囲内 index では、純粋 delimiter 参照作用は対応 wire の条件付き X である。 -/
theorem toggleOutputIndexReference_of_lt
    {ancillaQubits systemQubits : Nat} (enabled : Bool)
    (output : List (Wire ancillaQubits systemQubits))
    (index : Nat) (indexLt : index < output.length)
    (input : JointBasis ancillaQubits systemQubits) :
    toggleOutputIndexReference enabled output index input =
      if enabled then xBasisAction (output.get ⟨index, indexLt⟩) input else input := by
  simp [toggleOutputIndexReference, indexLt]

/-- delimiter参照作用は出力register外のwireを変更しない。 -/
theorem toggleOutputIndexReference_outside
    {ancillaQubits systemQubits : Nat} (enabled : Bool)
    (output : List (Wire ancillaQubits systemQubits)) (index : Nat)
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits) (outside : wire ∉ output) :
    toggleOutputIndexReference enabled output index input wire = input wire := by
  unfold toggleOutputIndexReference
  cases found : output[index]? with
  | none => rfl
  | some target =>
      have targetMember : target ∈ output := List.mem_iff_getElem?.mpr ⟨index, found⟩
      have wireNeTarget : wire ≠ target := by
        intro equal
        exact outside (equal ▸ targetMember)
      cases enabled
      · rfl
      · exact xBasisAction_other target wire wireNeTarget input

/-- 出力register外の一本のX作用はdelimiter参照作用と可換である。 -/
theorem toggleOutputIndexReference_x_outside
    {ancillaQubits systemQubits : Nat} (enabled : Bool)
    (output : List (Wire ancillaQubits systemQubits)) (index : Nat)
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits) (outside : wire ∉ output) :
    toggleOutputIndexReference enabled output index (xBasisAction wire input) =
      xBasisAction wire (toggleOutputIndexReference enabled output index input) := by
  unfold toggleOutputIndexReference
  cases found : output[index]? with
  | none => rfl
  | some target =>
      have targetMember : target ∈ output := List.mem_iff_getElem?.mpr ⟨index, found⟩
      have targetNeWire : target ≠ wire := by
        intro equal
        exact outside (equal ▸ targetMember)
      cases enabled
      · rfl
      · exact xBasisAction_commute target wire targetNeWire input

/-- sorted use 部全体（data・delimiter・active）の正本基本ゲート回路。 -/
def writeSortedUseCircuit (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let dataUse := writeSortedDataUseCircuit p output outputDegree outputDegreeLe
  have delimiterLt : p.wordWidth * outputDegree < output.length := by
    rw [outputLength]
    calc
      p.wordWidth * outputDegree ≤ p.wordWidth * p.K :=
        Nat.mul_le_mul_left p.wordWidth outputDegreeLe
      _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _
      _ = p.systemWidth := rfl
  let delimiter := output.get ⟨p.wordWidth * outputDegree, delimiterLt⟩
  .seq dataUse <| .seq (safeCnot (oraclePairWire p) delimiter)
    (safeCnot (oraclePairWire p) outputActive)

/-- sorted use 部全体に対応する行列非展開な純粋基底作用。 -/
def writeSortedUseReference (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (_outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let copied := writeSortedDataReference p output outputDegree outputDegreeLe
    enabled input
  let withDelimiter := toggleOutputIndexReference enabled output
    (p.wordWidth * outputDegree) copied
  if enabled then xBasisAction outputActive withDelimiter else withDelimiter

/-- sorted use参照作用は、出力registerとactive signalの外側を変更しない。 -/
theorem writeSortedUseReference_outside
    (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideOutput : wire ∉ output) (outsideActive : wire ≠ outputActive) :
    writeSortedUseReference p output outputLength outputActive outputDegree
        outputDegreeLe enabled input wire = input wire := by
  unfold writeSortedUseReference
  let copied := writeSortedDataReference p output outputDegree outputDegreeLe
    enabled input
  have copiedWire : copied wire = input wire :=
    writeSortedDataReference_outside p output outputDegree outputDegreeLe enabled
      input wire outsideOutput
  have delimiterWire :
      toggleOutputIndexReference enabled output (p.wordWidth * outputDegree)
          copied wire = copied wire :=
    toggleOutputIndexReference_outside enabled output (p.wordWidth * outputDegree)
      copied wire outsideOutput
  cases enabled
  · exact delimiterWire.trans copiedWire
  · simp only [if_true]
    rw [xBasisAction_other outputActive wire outsideActive]
    exact delimiterWire.trans copiedWire

/-- canonical sorted-use参照作用全体は、一時pair flagのX作用と可換である。 -/
theorem writeSortedUseReference_x_pair_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool) (input : JointBasis p.ancillaWidth p.systemWidth) :
    writeSortedUseReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) outputDegree outputDegreeLe enabled
        (xBasisAction (oraclePairWire p) input) =
      xBasisAction (oraclePairWire p)
        (writeSortedUseReference p (canonicalSortedOutputWires p kind)
          (canonicalSortedOutputWires_length p kind)
          (canonicalSortedOutputActive p kind) outputDegree outputDegreeLe enabled
          input) := by
  unfold writeSortedUseReference
  rw [writeSortedDataReference_x_pair_canonical]
  dsimp only
  rw [toggleOutputIndexReference_x_outside enabled
    (canonicalSortedOutputWires p kind) (p.wordWidth * outputDegree)
    (writeSortedDataReference p (canonicalSortedOutputWires p kind)
      outputDegree outputDegreeLe enabled input) (oraclePairWire p)
    (oraclePairWire_not_mem_canonicalSortedOutput p kind)]
  cases enabled
  · rfl
  · rw [xBasisAction_commute (canonicalSortedOutputActive p kind)
      (oraclePairWire p) (canonicalSortedOutputActive_ne_pair p kind)]
    simp

/-- canonical 出力に対する sorted use 実回路は data・delimiter・active の純粋参照作用に一致する。 -/
theorem runBasis_writeSortedUseCircuit_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (outputDegree : Nat) (outputDegreeLe : outputDegree ≤ p.K)
    (enabled : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (pairValue : input (oraclePairWire p) = enabled) :
    (writeSortedUseCircuit p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) outputDegree outputDegreeLe).runBasis
        reversibleGatePermutation input =
      writeSortedUseReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) outputDegree outputDegreeLe enabled
        input := by
  let output := canonicalSortedOutputWires p kind
  let active := canonicalSortedOutputActive p kind
  let outputLength := canonicalSortedOutputWires_length p kind
  let dataUse := writeSortedDataUseCircuit p output outputDegree outputDegreeLe
  let copied := writeSortedDataReference p output outputDegree outputDegreeLe
    enabled input
  have delimiterLt : p.wordWidth * outputDegree < output.length := by
    rw [outputLength]
    calc
      p.wordWidth * outputDegree ≤ p.wordWidth * p.K :=
        Nat.mul_le_mul_left p.wordWidth outputDegreeLe
      _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _
      _ = p.systemWidth := rfl
  let delimiter := output.get ⟨p.wordWidth * outputDegree, delimiterLt⟩
  have pairAbsentOutput : oraclePairWire p ∉ output := by
    simpa [output] using oraclePairWire_not_mem_canonicalSortedOutput p kind
  have pairNeDelimiter : oraclePairWire p ≠ delimiter := by
    intro equal
    apply pairAbsentOutput
    rw [equal]
    exact List.get_mem output ⟨p.wordWidth * outputDegree, delimiterLt⟩
  have activeNePair : active ≠ oraclePairWire p := by
    simpa [active] using canonicalSortedOutputActive_ne_pair p kind
  have pairNeActive : oraclePairWire p ≠ active := activeNePair.symm
  have activeNeDelimiter : active ≠ delimiter := by
    intro equal
    apply canonicalSortedOutputActive_not_mem_output p kind
    change active ∈ output
    rw [equal]
    exact List.get_mem output ⟨p.wordWidth * outputDegree, delimiterLt⟩
  have copiedEq : dataUse.runBasis reversibleGatePermutation input = copied := by
    simpa [dataUse, copied, output] using
      runBasis_writeSortedDataUseCircuit_canonical p kind outputDegree
        outputDegreeLe enabled input pairValue
  have copiedPair : copied (oraclePairWire p) = enabled := by
    have result := runBasis_writeSortedCopyList_canonical p kind outputDegree
      outputDegreeLe enabled (List.finRange outputDegree) input pairValue
    have referencePair :
        (List.finRange outputDegree).foldl (fun state slot =>
          writeSortedCopyReference p (canonicalSortedOutputWires p kind)
            outputDegree outputDegreeLe enabled slot state) input
            (oraclePairWire p) = enabled := by
      rw [← result.1]
      exact result.2
    simpa [copied, output, writeSortedDataReference] using referencePair
  rw [show writeSortedUseCircuit p output outputLength active outputDegree
      outputDegreeLe = .seq dataUse
        (.seq (safeCnot (oraclePairWire p) delimiter)
          (safeCnot (oraclePairWire p) active)) by rfl]
  rw [runBasis_seq, copiedEq, runBasis_seq]
  rw [runBasis_safeCnot (oraclePairWire p) delimiter pairNeDelimiter]
  rw [runBasis_safeCnot (oraclePairWire p) active pairNeActive]
  rw [show writeSortedUseReference p output outputLength active outputDegree
      outputDegreeLe enabled input =
        (if enabled then
          xBasisAction active
            (toggleOutputIndexReference enabled output
              (p.wordWidth * outputDegree) copied)
        else
          toggleOutputIndexReference enabled output
            (p.wordWidth * outputDegree) copied) by rfl]
  rw [toggleOutputIndexReference_of_lt enabled output
    (p.wordWidth * outputDegree) delimiterLt copied]
  cases enabled
  · change cnotBasisAction (oraclePairWire p) active
      (cnotBasisAction (oraclePairWire p) delimiter copied) = copied
    funext wire
    simp [cnotBasisAction, copiedPair]
  · change cnotBasisAction (oraclePairWire p) active
      (cnotBasisAction (oraclePairWire p) delimiter copied) =
        xBasisAction active (xBasisAction delimiter copied)
    funext wire
    simp [cnotBasisAction, xBasisAction, copiedPair, pairNeDelimiter]

/--
一つの有効degree branchが先頭`outputDegree` candidateをdelimiter出力へXORする純粋作用。
-/
def writeSortedDegreeReference (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let outputDegreeInt := Int.ofNat (degreeSlot.val + 1) + degreeChange
  if valid : (1 : Int) ≤ outputDegreeInt ∧
      outputDegreeInt ≤ Int.ofNat p.K then
    let outputDegree := outputDegreeInt.toNat
    have outputDegreeLe : outputDegree ≤ p.K := by
      dsimp only [outputDegree]
      exact Int.toNat_le.mpr valid.2
    let enabled := input (oracleBranchWire p) &&
      input (oracleDegreeWireAt p degreeSlot)
    writeSortedUseReference p output outputLength outputActive outputDegree
      outputDegreeLe enabled input
  else input

/-- AND scratch列の各wireはpair計算の局所supportに含まれる。 -/
theorem decoderAndScratchWire_mem_writeSortedPairSupport
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

/-- canonical degree参照作用はpair計算support上の全wireを保存する。 -/
theorem writeSortedDegreeReference_preserves_pairSupport
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    {wire : Wire p.ancillaWidth p.systemWidth}
    (supportMember : wire ∈ writeSortedPairSupport p) :
    writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeSlot degreeChange input wire =
      input wire := by
  unfold writeSortedDegreeReference
  split
  · apply writeSortedUseReference_outside
    · intro outputMember
      exact (List.disjoint_left.mp
        (canonicalSortedOutputWires_disjoint_writeSortedPairSupport p kind))
          outputMember supportMember
    · intro equal
      subst wire
      exact canonicalSortedOutputActive_not_mem_writeSortedPairSupport p kind
        supportMember
  · rfl

/--
canonical配置・clean workでは、一つのdegree branchの正本
compute--use--uncompute回路が純粋参照作用に厳密一致し、pairとAND scratchを復元する。
-/
theorem runBasis_writeSortedDegreeCircuit_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeSlot : Fin p.K) (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false) :
    (writeSortedDegreeCircuit p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) degreeChange degreeSlot).runBasis
        reversibleGatePermutation input =
      writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeSlot degreeChange input := by
  let output := canonicalSortedOutputWires p kind
  let outputLength := canonicalSortedOutputWires_length p kind
  let outputActive := canonicalSortedOutputActive p kind
  let outputDegreeInt := Int.ofNat (degreeSlot.val + 1) + degreeChange
  by_cases valid : (1 : Int) ≤ outputDegreeInt ∧
      outputDegreeInt ≤ Int.ofNat p.K
  · let outputDegree := outputDegreeInt.toNat
    have outputDegreeLe : outputDegree ≤ p.K := by
      exact Int.toNat_le.mpr valid.2
    let compute := writeSortedPairComputeCircuit p degreeSlot
    let use := writeSortedUseCircuit p output outputLength outputActive
      outputDegree outputDegreeLe
    let enabled := input (oracleBranchWire p) &&
      input (oracleDegreeWireAt p degreeSlot)
    let computed := compute.runBasis reversibleGatePermutation input
    let used := use.runBasis reversibleGatePermutation computed
    let reference := writeSortedUseReference p output outputLength outputActive
      outputDegree outputDegreeLe enabled input
    have computedEq : computed =
        if enabled then xBasisAction (oraclePairWire p) input else input := by
      simpa [computed, compute, enabled] using
        runBasis_writeSortedPairComputeCircuit_canonical p degreeSlot input
          scratchZero pairZero
    have computedPair : computed (oraclePairWire p) = enabled := by
      rw [computedEq]
      cases enabled <;> simp [pairZero, xBasisAction_target]
    have usedEq : used =
        writeSortedUseReference p output outputLength outputActive outputDegree
          outputDegreeLe enabled computed := by
      simpa [used, use, output, outputLength, outputActive] using
        runBasis_writeSortedUseCircuit_canonical p kind outputDegree
          outputDegreeLe enabled computed computedPair
    have usedSupport : BasisAgreeOn (writeSortedPairSupport p) used computed := by
      intro wire wireMember
      rw [usedEq]
      have outsideOutput : wire ∉ output := by
        intro outputMember
        exact (List.disjoint_left.mp
          (canonicalSortedOutputWires_disjoint_writeSortedPairSupport p kind))
            outputMember wireMember
      have outsideActive : wire ≠ outputActive := by
        intro equal
        subst wire
        exact canonicalSortedOutputActive_not_mem_writeSortedPairSupport p kind
          wireMember
      exact writeSortedUseReference_outside p output outputLength outputActive
        outputDegree outputDegreeLe enabled computed wire outsideOutput outsideActive
    have localClean := Circuit.computeUseUncompute_local_clean
      (writeSortedPairSupport p) compute use input
      (writeSortedPairComputeCircuit_usesOnly p degreeSlot) usedSupport
    have referenceOutside :
        ∀ wire ∈ writeSortedPairSupport p, reference wire = input wire := by
      intro wire wireMember
      have outsideOutput : wire ∉ output := by
        intro outputMember
        exact (List.disjoint_left.mp
          (canonicalSortedOutputWires_disjoint_writeSortedPairSupport p kind))
            outputMember wireMember
      have outsideActive : wire ≠ outputActive := by
        intro equal
        subst wire
        exact canonicalSortedOutputActive_not_mem_writeSortedPairSupport p kind
          wireMember
      exact writeSortedUseReference_outside p output outputLength outputActive
        outputDegree outputDegreeLe enabled input wire outsideOutput outsideActive
    have usedReference : used =
        if enabled then xBasisAction (oraclePairWire p) reference else reference := by
      by_cases enabledTrue : enabled = true
      · rw [if_pos enabledTrue, usedEq, computedEq, if_pos enabledTrue]
        simpa [reference, output, outputLength, outputActive, enabledTrue] using
          writeSortedUseReference_x_pair_canonical p kind outputDegree
            outputDegreeLe true input
      · rw [if_neg enabledTrue, usedEq, computedEq, if_neg enabledTrue]
    have restoredReference :
        restoreSupport (writeSortedPairSupport p) input used = reference := by
      funext wire
      by_cases inside : wire ∈ writeSortedPairSupport p
      · rw [show restoreSupport (writeSortedPairSupport p) input used wire =
            input wire by simp [restoreSupport, inside]]
        exact (referenceOutside wire inside).symm
      · rw [restoreSupport_outside (writeSortedPairSupport p) input used wire inside]
        rw [usedReference]
        cases enabled
        · rfl
        · rw [if_pos rfl]
          exact xBasisAction_other (oraclePairWire p) wire (by
            intro equal
            apply inside
            subst wire
            exact oraclePairWire_mem_writeSortedPairSupport p) reference
    have validRaw :
        (1 : Int) ≤ Int.ofNat (degreeSlot.val + 1) + degreeChange ∧
          Int.ofNat (degreeSlot.val + 1) + degreeChange ≤ Int.ofNat p.K := by
      simpa [outputDegreeInt] using valid
    rw [show writeSortedDegreeCircuit p output outputLength outputActive
          degreeChange degreeSlot =
        Circuit.computeUseUncompute id compute use by
          unfold writeSortedDegreeCircuit
          rw [dif_pos validRaw]
          rfl]
    rw [localClean, restoredReference]
    show reference = writeSortedDegreeReference p output outputLength outputActive
      degreeSlot degreeChange input
    symm
    unfold writeSortedDegreeReference
    rw [dif_pos validRaw]
  · have invalidRaw : ¬((1 : Int) ≤
        Int.ofNat (degreeSlot.val + 1) + degreeChange ∧
        Int.ofNat (degreeSlot.val + 1) + degreeChange ≤ Int.ofNat p.K) := by
      simpa [outputDegreeInt] using valid
    unfold writeSortedDegreeCircuit writeSortedDegreeReference
    rw [dif_neg invalidRaw, dif_neg invalidRaw]
    rfl

/-- 全degree slotを走査するsorted出力の、行列を用いない純粋基底仕様。 -/
def SortedCandidatesDelimiterOutputXorSpec (p : QParameters)
    (output : List (Wire p.ancillaWidth p.systemWidth))
    (outputLength : output.length = p.systemWidth)
    (outputActive : Wire p.ancillaWidth p.systemWidth)
    (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
  JointBasis p.ancillaWidth p.systemWidth :=
  (List.finRange p.K).foldl (fun state degreeSlot =>
    writeSortedDegreeReference p output outputLength outputActive degreeSlot
      degreeChange state) input

/--
任意のdegree-slot列について、正本回路foldと純粋参照foldが一致し、
AND scratchとpair flagのclean不変条件が次段へ保存される。
-/
theorem runBasis_writeSortedDegreeList_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeChange : Int) (slots : List (Fin p.K))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false) :
    let actualFinal := slots.foldl (fun state degreeSlot =>
      (writeSortedDegreeCircuit p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeChange degreeSlot).runBasis
          reversibleGatePermutation state) input
    let referenceFinal := slots.foldl (fun state degreeSlot =>
      writeSortedDegreeReference p (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeSlot degreeChange state) input
    actualFinal = referenceFinal ∧
      (∀ wire ∈ decoderAndScratchWires p, referenceFinal wire = false) ∧
      referenceFinal (oraclePairWire p) = false := by
  induction slots generalizing input with
  | nil => exact ⟨rfl, scratchZero, pairZero⟩
  | cons degreeSlot slots inductionHypothesis =>
      let nextReference := writeSortedDegreeReference p
        (canonicalSortedOutputWires p kind)
        (canonicalSortedOutputWires_length p kind)
        (canonicalSortedOutputActive p kind) degreeSlot degreeChange input
      have firstEq :
          (writeSortedDegreeCircuit p (canonicalSortedOutputWires p kind)
            (canonicalSortedOutputWires_length p kind)
            (canonicalSortedOutputActive p kind) degreeChange degreeSlot).runBasis
              reversibleGatePermutation input = nextReference := by
        simpa [nextReference] using
          runBasis_writeSortedDegreeCircuit_canonical p kind degreeSlot
            degreeChange input scratchZero pairZero
      have nextScratchZero :
          ∀ wire ∈ decoderAndScratchWires p, nextReference wire = false := by
        intro wire member
        rw [show nextReference wire = input wire by
          exact writeSortedDegreeReference_preserves_pairSupport p kind degreeSlot
            degreeChange input
              (decoderAndScratchWire_mem_writeSortedPairSupport p member)]
        exact scratchZero wire member
      have nextPairZero : nextReference (oraclePairWire p) = false := by
        rw [show nextReference (oraclePairWire p) = input (oraclePairWire p) by
          exact writeSortedDegreeReference_preserves_pairSupport p kind degreeSlot
            degreeChange input (oraclePairWire_mem_writeSortedPairSupport p)]
        exact pairZero
      have tail := inductionHypothesis nextReference nextScratchZero nextPairZero
      simpa only [List.foldl_cons, firstEq] using tail

/-- canonical sorted-output正本回路全体は、一般`K`の純粋有限fold仕様に一致する。 -/
theorem runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical
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
  exact (runBasis_writeSortedDegreeList_canonical p kind degreeChange
    (List.finRange p.K) input scratchZero pairZero).1

/-- canonical sorted-output正本回路全体はAND scratchとpair flagを0へ戻す。 -/
theorem runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_work_clean_canonical
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeChange : Int)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p, input wire = false)
    (pairZero : input (oraclePairWire p) = false) :
    let output := (xorSortedCandidatesAsDelimiterIntoOutputCircuit p (canonicalSortedOutputWires p kind)
      (canonicalSortedOutputWires_length p kind)
      (canonicalSortedOutputActive p kind) degreeChange).runBasis
        reversibleGatePermutation input
    (∀ wire ∈ decoderAndScratchWires p, output wire = false) ∧
      output (oraclePairWire p) = false := by
  have result := runBasis_writeSortedDegreeList_canonical p kind degreeChange
    (List.finRange p.K) input scratchZero pairZero
  rw [runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical p kind degreeChange input scratchZero
    pairZero]
  exact result.2

end ReversibleCircuit

end ProbabilityGeneratorQProof
