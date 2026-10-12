import QLean.Generator.Implementation.QOracleColumnFullCorrectness
import QLean.Generator.Implementation.QOracleRowIllegalInputCorrectness
import QLean.Generator.Implementation.QCompactDecoderWorkRestoration

/-!
# Q column oracle の非合法 delimiter 入力

Column-key register が delimiter として復号できない場合に、巨大行列を展開せず、
column oracle 全体が計算基底を厳密に固定することを証明する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/--
非合法 column-key 基底に対する一般入力仕様。外部出力 register は任意の XOR
accumulator のままとし、column-key、selector、oracle work だけを指定する。
-/
structure ColumnOracleIllegalInputSpec (p : QParameters)
    (basis : RegisterBasis p.systemWidth) (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- Column-key register は指定した物理基底を保持する。 -/
  column_key_bits : readWires (columnKeyWires p) input =
    registerBitList basis
  /-- Column-selector register は指定した canonical 定数 bit 列を保持する。 -/
  selector_bits : readWires (columnSelectorWires p) input =
    constantBits selector.val (columnSelectorWires p).length
  /-- Canonical oracle work の全 wire は 0 である。 -/
  work_zero : ∀ wire ∈ diagonalOracleWorkWires p, input wire = false

/-- 非合法 column 入力では任意の canonical oracle slice が 0 である。 -/
theorem ColumnOracleIllegalInputSpec.slice_zero
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleIllegalInputSpec p basis selector input)
    {width : Nat} (slice : RegisterSlice p.oracleWorkWidth width) :
    ∀ wire ∈ ((QLayout.oracleSlice slice).wireList :
      List (Wire p.ancillaWidth p.systemWidth)), input wire = false := by
  intro wire member
  exact specification.work_zero wire (by
    simpa [diagonalOracleWorkWires] using
      oracleSliceWire_mem_oracleWork p slice member)

/-- 非合法 column 入力は compact decoder の基底 clean 条件を満たす。 -/
theorem ColumnOracleIllegalInputSpec.compactBasisClean
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleIllegalInputSpec p basis selector input) :
    CompactDecoderBasisCleanInput p (columnKeyWires p) basis input := by
  refine {
    input_bits := specification.column_key_bits
    suffix_zero := ?_
    degree_zero := ?_
    compare_zero := ?_
    and_zero := ?_
    legal_zero := ?_ }
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).candidate
    simpa [decoderSuffixWires, RegisterSlice.wireList] using
      List.mem_of_mem_take member
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).degree
    simpa [oracleDegreeWires, RegisterSlice.wireList] using member
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).compareWork
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member
  · intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).andWork
    simpa [oracleAndWorkWires, RegisterSlice.wireList] using member
  · apply specification.slice_zero (OracleWorkLayout.canonical p).legal
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).legal).ancillaWire 0 ∈ _
    simp [RegisterSlice.wireList]

/-- 非合法 column 入力は event・sort の初期 clean 条件を満たす。 -/
theorem ColumnOracleIllegalInputSpec.eventSortClean
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleIllegalInputSpec p basis selector input) :
    EventSortCleanInput p input := by
  refine {
    moved_selector := {
      compare_zero := specification.compactBasisClean.compare_zero
      scratch_zero := ?_
      position_zero := ?_
      pair_zero := ?_ }
    sort_compare_zero := ?_
    sort_scratch_zero := ?_
    sort_history_zero := ?_ }
  · intro wire member
    exact specification.compactBasisClean.and_zero wire
      (decoderComparisonAndMember p (by simp [member]))
  · apply specification.slice_zero
      (OracleWorkLayout.canonical p).positionMatch
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).positionMatch).ancillaWire _ ∈ _
    simp [RegisterSlice.wireList]
  · apply specification.slice_zero (OracleWorkLayout.canonical p).pair
    change (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).pair).ancillaWire _ ∈ _
    simp [RegisterSlice.wireList]
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    simp only [sortCompareWorkWires, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with compareMember | extraMember
    · exact pointwise_false_of_readWires_eq_replicate
        (oracleCompareWorkWires p) input
        specification.compactBasisClean.compare_zero wire compareMember
    · subst wire
      exact specification.compactBasisClean.and_zero _
        (by simp [oracleAndWorkWires])
  · intro wire member
    exact specification.compactBasisClean.and_zero wire (by
      simpa [oracleAndWorkWires, RegisterSlice.wireList] using
        sortAndScratchWires_mem_andSlice p member)
  · intro instruction instructionMember
    apply specification.slice_zero (OracleWorkLayout.canonical p).sortFlags
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history, rfl⟩

/-- 非合法 column 入力では persistent compute 後も legal flag が偽である。 -/
theorem ColumnOracleIllegalInputSpec.persistentLegalFalse
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleIllegalInputSpec p basis selector input)
    (illegal : decodeDelimiter basis = none) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input (oracleLegalWire p) = false := by
  exact computeSharedDecoderPresenceParityAndOneFlagsCircuit_legal_false_of_basis_clean p
    (columnKeyWires p) (columnKeyWires_oraclePersistentInputLayout p) basis
    input specification.compactBasisClean illegal false

/-- 非合法 column 入力では persistent compute 後も event・sort work が clean である。 -/
theorem ColumnOracleIllegalInputSpec.persistentEventSortClean
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleIllegalInputSpec p basis selector input) :
    EventSortCleanInput p
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input) := by
  exact computeSharedDecoderPresenceParityAndOneFlagsCircuit_output_eventSortClean_of_workZero p
    (columnKeyWires p) (columnKeyWires_compactDecoderInputLayout p)
    (columnKeyWires_disjoint_diagonalOracleWorkWires p) false input
    specification.eventSortClean specification.compactBasisClean.compare_zero
    specification.compactBasisClean.and_zero

/-- 非合法 column 入力では persistent compute 後も selected flag が 0 である。 -/
theorem ColumnOracleIllegalInputSpec.persistentSelectedZero
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleIllegalInputSpec p basis selector input) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input (oracleSelectedWire p) = false := by
  rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_preCandidateSlice p (columnKeyWires p)
    (columnKeyWires_disjoint_diagonalOracleWorkWires p) false input
    (OracleWorkLayout.canonical p).selected]
  · apply specification.slice_zero (OracleWorkLayout.canonical p).selected
    simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [oraclePersistentSpecialSlice, OracleWorkLayout.canonical]
  · simp [OracleWorkLayout.canonical]
  · simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]

/-- 非合法 column 入力では persistent compute 後も branch flag が 0 である。 -/
theorem ColumnOracleIllegalInputSpec.persistentBranchZero
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleIllegalInputSpec p basis selector input) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input (oracleBranchWire p) = false := by
  rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_middleOracleSlice p (columnKeyWires p)
    (columnKeyWires_disjoint_diagonalOracleWorkWires p) false input
    (OracleWorkLayout.canonical p).branch]
  · apply specification.slice_zero (OracleWorkLayout.canonical p).branch
    simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [OracleWorkLayout.canonical]
    omega
  · simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]

/--
復号不能な column-key 入力から、全 branch を恒等化する persistent 非合法仕様を得る。
-/
theorem ColumnOracleIllegalInputSpec.afterPersistent
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleIllegalInputSpec p basis selector input)
    (illegal : decodeDelimiter basis = none) :
    ColumnOraclePersistentIllegalSpec p
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation input) := {
  legal_false := specification.persistentLegalFalse illegal
  selected_zero := specification.persistentSelectedZero
  branch_zero := specification.persistentBranchZero
  event_clean := specification.persistentEventSortClean }

/--
Column-key が delimiter として復号不能なら、column oracle 全体は一般 accumulator 入力を
厳密に固定する。
-/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_illegal_identity
    (p : QParameters) (basis : RegisterBasis p.systemWidth)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOracleIllegalInputSpec p basis selector input)
    (illegal : decodeDelimiter basis = none) :
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input = input := by
  exact applyColumnOracleReferenceAndRestoreWorkCircuit_identity_of_persistentIllegal p input
    (specification.afterPersistent illegal)

end ReversibleCircuit

end ProbabilityGeneratorQProof
