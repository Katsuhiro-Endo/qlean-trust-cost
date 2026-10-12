import QLean.Generator.Implementation.ComponentCombinators
import QLean.Generator.Analysis.QOracleAnalyticStateSpecs
import QLean.Generator.Implementation.QActualDiagonalAcceptedCorrectness
import QLean.Generator.Implementation.QOracleEventComputedClean
import QLean.Generator.Implementation.QWriteSortedConfigurationBridge
import QLean.Generator.Implementation.BitonicSharedCleanAdapter

/-!
# Q oracleを構成する再利用可能な検証済み部品

算術、membership、candidate生成、bitonic sort、sorted writer、およびcolumn/row oracleを、
回路から独立した参照関数と局所的なclean条件を持つ公開契約へ包装する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 入出力の解析関係が一意なとき、その唯一の出力だけを選ぶ回路非依存の参照関数。 -/
noncomputable def uniqueSpecificationReference
    {basis : Type*} (specification : basis → basis → Prop)
    (input : basis) : basis := by
  classical
  by_cases uniqueOutput : ∃! output, specification input output
  · exact Classical.choose uniqueOutput.exists
  · exact input

/-- 一意出力が存在すれば、選択した参照値も解析関係を満たす。 -/
theorem uniqueSpecificationReference_spec
    {basis : Type*} {specification : basis → basis → Prop}
    {input : basis} (uniqueOutput : ∃! output, specification input output) :
    specification input (uniqueSpecificationReference specification input) := by
  classical
  unfold uniqueSpecificationReference
  split
  · exact Classical.choose_spec uniqueOutput.exists
  · contradiction

/-- 周期加算・減算部品が保証する、work復元とword読出しの解析仕様。 -/
structure WordArithmeticRestoration
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (expectedBits : List Bool)
    (input output : JointBasis ancillaQubits systemQubits) : Prop where
  /-- scratchは全て0へ戻る。 -/
  scratch_zero : ∀ wire ∈ scratches, output wire = false
  /-- 対象wordは指定した解析的bit列になる。 -/
  word_bits : readWires word output = expectedBits

/-- 任意幅の周期incrementを純粋参照作用へ結ぶclean部品。 -/
def compiledIncrementWordMod2PowInPlaceBridgeCleanComponent
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup) :
    CleanComponent (reversibleGatePermutation (ancillaQubits := ancillaQubits)
      (systemQubits := systemQubits)) where
  circuit := incrementWordMod2PowInPlaceCircuit word scratches
  reference := incrementWordCarrySequenceReference [] word
  inputCondition := fun input => ∀ wire ∈ scratches, input wire = false
  outputCondition := fun output => ∀ wire ∈ scratches, output wire = false
  restoration := fun input output =>
    WordArithmeticRestoration word scratches
      (incrementBits (readWires word input)) input output
  runBasis_correct := by
    intro input scratchZero
    exact runBasis_incrementWordMod2PowInPlaceCircuit word scratches input enoughScratch
      layoutNodup scratchZero
  outputCondition_correct := by
    intro input scratchZero wire member
    rw [incrementWordCarrySequenceReference_outside [] word wire input]
    · exact scratchZero wire member
    · have separated := (List.nodup_append.mp layoutNodup).2.2
      exact fun wordMember => (separated _ wordMember _ member) rfl
  restoration_correct := by
    intro input scratchZero
    refine { scratch_zero := ?_, word_bits := ?_ }
    · intro wire member
      rw [incrementWordCarrySequenceReference_outside [] word wire input]
      · exact scratchZero wire member
      · have separated := (List.nodup_append.mp layoutNodup).2.2
        exact fun wordMember => (separated _ wordMember _ member) rfl
    simpa [incrementBits, allWiresTrue, readWires] using
      (readWires_incrementWordCarrySequenceReference
        ([] : List (Wire ancillaQubits systemQubits)) word input
        (by simpa using (List.nodup_append.mp layoutNodup).1))

/-- 任意幅の周期decrementを純粋参照作用へ結ぶclean部品。 -/
def compiledDecrementWordMod2PowInPlaceBridgeCleanComponent
    {ancillaQubits systemQubits : Nat}
    (word scratches : List (Wire ancillaQubits systemQubits))
    (enoughScratch : word.length ≤ scratches.length + 2)
    (layoutNodup : (word ++ scratches).Nodup) :
    CleanComponent (reversibleGatePermutation (ancillaQubits := ancillaQubits)
      (systemQubits := systemQubits)) where
  circuit := decrementWordMod2PowInPlaceCircuit word scratches
  reference := decrementWordBorrowSequenceReference [] word
  inputCondition := fun input => ∀ wire ∈ scratches, input wire = false
  outputCondition := fun output => ∀ wire ∈ scratches, output wire = false
  restoration := fun input output =>
    WordArithmeticRestoration word scratches
      (decrementBits (readWires word input)) input output
  runBasis_correct := by
    intro input scratchZero
    exact runBasis_decrementWordMod2PowInPlaceCircuit word scratches input enoughScratch
      layoutNodup scratchZero
  outputCondition_correct := by
    intro input scratchZero wire member
    rw [decrementWordBorrowSequenceReference_outside [] word wire input]
    · exact scratchZero wire member
    · have separated := (List.nodup_append.mp layoutNodup).2.2
      exact fun wordMember => (separated _ wordMember _ member) rfl
  restoration_correct := by
    intro input scratchZero
    refine { scratch_zero := ?_, word_bits := ?_ }
    · intro wire member
      rw [decrementWordBorrowSequenceReference_outside [] word wire input]
      · exact scratchZero wire member
      · have separated := (List.nodup_append.mp layoutNodup).2.2
        exact fun wordMember => (separated _ wordMember _ member) rfl
    simpa [decrementBits, allWiresFalse, readWires] using
      (readWires_decrementWordBorrowSequenceReference
        ([] : List (Wire ancillaQubits systemQubits)) word input
        (by simpa using (List.nodup_append.mp layoutNodup).1))

/-- 二wordの等値に応じてtargetだけを反転する回路非依存の解析作用。 -/
def equalityAnalyticAction
    {ancillaQubits systemQubits : Nat}
    (left right : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if decide (readWires left input = readWires right input) then
    xBasisAction target input
  else input

/-- cleanな等値比較正本は解析的等値作用と厳密に一致する。 -/
theorem verifiedEquality_correct
    {ancillaQubits systemQubits : Nat}
    (left right flags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = flags.length)
    (rightLength : right.length = flags.length)
    (leftDisjointFlags : left.Disjoint flags)
    (rightDisjointFlags : right.Disjoint flags)
    (flagsDisjointScratch : flags.Disjoint scratches)
    (flagsNodup : flags.Nodup)
    (positiveLayout : (flags ++ scratches ++ [target]).Nodup)
    (targetAbsentLeft : target ∉ left)
    (targetAbsentRight : target ∉ right)
    (flagsZero : readWires flags input = List.replicate flags.length false)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (enoughScratch : flags.length ≤ scratches.length + 1) :
    (xorEqualityIntoTargetCircuit left right flags scratches target).runBasis
        reversibleGatePermutation input =
      equalityAnalyticAction left right target input := by
  exact runBasis_xorEqualityIntoTargetCircuit left right flags scratches target input
    leftLength rightLength leftDisjointFlags rightDisjointFlags
    flagsDisjointScratch flagsNodup positiveLayout targetAbsentLeft
    targetAbsentRight flagsZero scratchZero enoughScratch

/-- 等値比較正本を解析作用へ包装した再利用可能なclean component。 -/
def compiledXorEqualityIntoTargetBridgeCleanComponent
    {ancillaQubits systemQubits : Nat}
    (left right flags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (leftLength : left.length = flags.length)
    (rightLength : right.length = flags.length)
    (leftDisjointFlags : left.Disjoint flags)
    (rightDisjointFlags : right.Disjoint flags)
    (flagsDisjointScratch : flags.Disjoint scratches)
    (flagsNodup : flags.Nodup)
    (positiveLayout : (flags ++ scratches ++ [target]).Nodup)
    (targetAbsentLeft : target ∉ left)
    (targetAbsentRight : target ∉ right)
    (enoughScratch : flags.length ≤ scratches.length + 1) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := xorEqualityIntoTargetCircuit left right flags scratches target
  reference := equalityAnalyticAction left right target
  inputCondition := fun input =>
    readWires flags input = List.replicate flags.length false ∧
      ∀ wire ∈ scratches, input wire = false
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = equalityAnalyticAction left right target input
  runBasis_correct := by
    intro input clean
    exact verifiedEquality_correct left right flags scratches target input
      leftLength rightLength leftDisjointFlags rightDisjointFlags
      flagsDisjointScratch flagsNodup positiveLayout targetAbsentLeft
      targetAbsentRight clean.1 clean.2 enoughScratch
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- 二wordのlittle-endian自然数大小に応じてtargetだけを反転する解析作用。 -/
def lessThanAnalyticAction
    {ancillaQubits systemQubits : Nat}
    (left right : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if decide (littleEndianNat (readWires left input) <
      littleEndianNat (readWires right input)) then
    xBasisAction target input
  else input

/-- cleanなless-than正本は通常の自然数大小判定作用と厳密に一致する。 -/
theorem verifiedLessThan_correct
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = equalFlags.length)
    (rightLength : right.length = equalFlags.length)
    (leftDisjointFlags : left.Disjoint equalFlags)
    (rightDisjointFlags : right.Disjoint equalFlags)
    (flagsDisjointScratch : equalFlags.Disjoint scratches)
    (flagsNodup : equalFlags.Nodup)
    (targetAbsentLeft : target ∉ left)
    (targetAbsentRight : target ∉ right)
    (targetAbsentFlags : target ∉ equalFlags)
    (flagsZero : readWires equalFlags input =
      List.replicate equalFlags.length false)
    (scratchZero : ∀ wire ∈ scratches, input wire = false)
    (programEnough : ∀ controls ∈ lessThanControlProgram left right equalFlags,
      controls.length ≤ scratches.length + 1)
    (programLayout : ∀ controls ∈ lessThanControlProgram left right equalFlags,
      (controls.map Prod.fst ++ scratches ++ [target]).Nodup) :
    (xorLessThanIntoTargetCircuit left right equalFlags scratches target).runBasis
        reversibleGatePermutation input =
      lessThanAnalyticAction left right target input := by
  exact runBasis_xorLessThanIntoTargetCircuit_nat left right equalFlags scratches target input
    leftLength rightLength leftDisjointFlags rightDisjointFlags
    flagsDisjointScratch flagsNodup targetAbsentLeft targetAbsentRight
    targetAbsentFlags flagsZero scratchZero programEnough programLayout

/-- less-than正本を通常の自然数大小判定作用へ包装したclean component。 -/
def compiledXorLessThanIntoTargetBridgeCleanComponent
    {ancillaQubits systemQubits : Nat}
    (left right equalFlags scratches : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (leftLength : left.length = equalFlags.length)
    (rightLength : right.length = equalFlags.length)
    (leftDisjointFlags : left.Disjoint equalFlags)
    (rightDisjointFlags : right.Disjoint equalFlags)
    (flagsDisjointScratch : equalFlags.Disjoint scratches)
    (flagsNodup : equalFlags.Nodup)
    (targetAbsentLeft : target ∉ left)
    (targetAbsentRight : target ∉ right)
    (targetAbsentFlags : target ∉ equalFlags)
    (programEnough : ∀ controls ∈ lessThanControlProgram left right equalFlags,
      controls.length ≤ scratches.length + 1)
    (programLayout : ∀ controls ∈ lessThanControlProgram left right equalFlags,
      (controls.map Prod.fst ++ scratches ++ [target]).Nodup) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := ancillaQubits) (systemQubits := systemQubits)) where
  circuit := xorLessThanIntoTargetCircuit left right equalFlags scratches target
  reference := lessThanAnalyticAction left right target
  inputCondition := fun input =>
    readWires equalFlags input = List.replicate equalFlags.length false ∧
      ∀ wire ∈ scratches, input wire = false
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = lessThanAnalyticAction left right target input
  runBasis_correct := by
    intro input clean
    exact verifiedLessThan_correct left right equalFlags scratches target input
      leftLength rightLength leftDisjointFlags rightDisjointFlags
      flagsDisjointScratch flagsNodup targetAbsentLeft targetAbsentRight
      targetAbsentFlags clean.1 clean.2 programEnough programLayout
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- compact decoderの合法入力に対する解析的出力とwork復元を一括した公開仕様。 -/
structure CompactDecoderAnalyticResult (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p)
    (output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 入力delimiter registerは保存される。 -/
  input_preserved : readWires inputWires output =
    registerBitList (delimiterEncoding configuration)
  /-- degree registerは粒子数のone-hotになる。 -/
  degree_one_hot : readWires (oracleDegreeWires p) output =
    degreeOneHotFrom p.K configuration.1.card 0
  /-- 合法性flagは真になる。 -/
  legal_true : output (oracleLegalWire p) = true
  /-- 比較workは0へ戻る。 -/
  compare_zero : ∀ wire ∈ oracleCompareWorkWires p, output wire = false
  /-- AND workは0へ戻る。 -/
  and_zero : ∀ wire ∈ oracleAndWorkWires p, output wire = false

/-- compact decoderの解析出力とdegree/legal以外の全wire復元を合わせた一意な仕様。 -/
structure DelimiterLegalityAndDegreeOneHotXorSpec (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop
    extends CompactDecoderAnalyticResult p inputWires configuration output where
  /-- degree registerとlegal bit以外の全wireは入力へ戻る。 -/
  outside_restored : ∀ wire, wire ∉ oracleDegreeWires p →
    wire ≠ oracleLegalWire p → output wire = input wire

/-- compact decoder component仕様は全wire上で出力を一意に定める。 -/
theorem DelimiterLegalityAndDegreeOneHotXorSpec.unique
    {p : QParameters} {inputWires : List (Wire p.ancillaWidth p.systemWidth)}
    {configuration : QConfiguration p}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration input left)
    (rightSpec : DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration input right) :
    left = right := by
  funext wire
  by_cases degreeMember : wire ∈ oracleDegreeWires p
  · exact readWires_eq_at_of_eq (oracleDegreeWires p) left right
      (leftSpec.degree_one_hot.trans rightSpec.degree_one_hot.symm) degreeMember
  by_cases legalEq : wire = oracleLegalWire p
  · subst wire
    exact leftSpec.legal_true.trans rightSpec.legal_true.symm
  exact (leftSpec.outside_restored wire degreeMember legalEq).trans
    (rightSpec.outside_restored wire degreeMember legalEq).symm

/-- compact decoder正本はdelimiter保存・degree one-hot・合法性・work復元を同時に満たす。 -/
theorem verifiedCompactDecoder_correct
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    CompactDecoderAnalyticResult p inputWires configuration
      ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input) := by
  have work := xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_work_clean_of_clean p inputWires
    layout configuration input clean
  exact {
    input_preserved := xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_input_preserved_of_clean
      p inputWires layout configuration input clean
    degree_one_hot := xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_degree_of_clean p inputWires
      layout configuration input clean
    legal_true := xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_true_of_clean p inputWires
      layout configuration input clean
    compare_zero := work.1
    and_zero := work.2 }

/-- cleanなactual compact decoderは一意な全wire component仕様を満たす。 -/
theorem verifiedDelimiterLegalityAndDegreeOneHotXorSpec
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration input
      ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input) := by
  let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
    reversibleGatePermutation input
  let decoded := (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires
    (decoderSuffixWires p) (oracleDegreeWires p)).runBasis
      reversibleGatePermutation input
  have result : CompactDecoderAnalyticResult p inputWires configuration output :=
    verifiedCompactDecoder_correct p inputWires layout configuration input clean
  refine {
    toCompactDecoderAnalyticResult := result
    outside_restored := ?_ }
  intro wire outsideDegree notLegal
  by_cases inputMember : wire ∈ inputWires
  · exact readWires_eq_at_of_eq inputWires output input
      (result.input_preserved.trans clean.input_bits.symm) inputMember
  by_cases suffixMember : wire ∈ decoderSuffixWires p
  · have agree := xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_support_restored_of_input p
      inputWires layout input
    have outputDecoded : output wire = decoded wire := by
      exact agree wire (by
        simp [decoderLegalitySupportFor, suffixMember])
    have supportClean := runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_support_clean p.wordWidth
      inputWires (decoderSuffixWires p) (oracleDegreeWires p) input
      layout.disjoint_suffix layout.disjoint_degree
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    have decodedInput : decoded wire = input wire := by
      exact readWires_eq_at_of_eq (inputWires ++ decoderSuffixWires p)
        decoded input (by simpa [decoded] using supportClean) (by simp [suffixMember])
    exact outputDecoded.trans decodedInput
  by_cases compareMember : wire ∈ oracleCompareWorkWires p
  · change output wire = input wire
    rw [result.compare_zero wire compareMember]
    exact (pointwise_false_of_readWires_eq_replicate
      (oracleCompareWorkWires p) input clean.compare_zero wire compareMember).symm
  by_cases andMember : wire ∈ oracleAndWorkWires p
  · change output wire = input wire
    rw [result.and_zero wire andMember, clean.and_zero wire andMember]
  · have outsideSupport : wire ∉ decoderLegalitySupportFor p inputWires := by
      simp [decoderLegalitySupportFor, inputMember, suffixMember, outsideDegree,
        compareMember, andMember]
    have outputDecoded : output wire = decoded wire := by
      exact xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_outside_of_input p inputWires layout
        input wire outsideSupport notLegal
    have decodedInput : decoded wire = input wire := by
      exact runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
        (decoderSuffixWires p) (oracleDegreeWires p) wire input
        (by simp [layout.length_eq])
        layout.disjoint_suffix layout.disjoint_degree
        (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
        (decoderSuffixWires_nodup p) inputMember suffixMember outsideDegree
    exact outputDecoded.trans decodedInput

/-- compact decoderのpure出力が一意であることも入力契約に束ねた公開component。 -/
noncomputable def compiledDelimiterLegalityAndDegreeOneHotBridgeCleanComponent
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires
  reference := uniqueSpecificationReference fun input output =>
    DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration input output
  inputCondition := CompactDecoderCleanInput p inputWires configuration
  outputCondition := fun _ => True
  restoration := fun input output =>
    DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration input output
  runBasis_correct := by
    intro input conditions
    let actual := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    have actualSpec := verifiedDelimiterLegalityAndDegreeOneHotXorSpec p inputWires layout
      configuration input conditions
    have uniqueOutput : ∃! output,
        DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    have referenceSpec := uniqueSpecificationReference_spec uniqueOutput
    exact uniqueOutput.unique actualSpec referenceSpec
  outputCondition_correct := by simp
  restoration_correct := by
    intro input conditions
    let actual := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    have actualSpec := verifiedDelimiterLegalityAndDegreeOneHotXorSpec p inputWires layout
      configuration input conditions
    have uniqueOutput : ∃! output,
        DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    exact uniqueSpecificationReference_spec uniqueOutput

/-- column対角分岐のXOR式と全外部wire復元を合わせた一意なcomponent仕様。 -/
structure ColumnDiagonalRestoredReferenceIdentification (p : QParameters) (constant : Nat)
    (enabled : Bool) (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop
    extends ColumnDiagonalResultWithWorkRestorationSpec p constant enabled input output where
  /-- 四外部出力以外のwireは全て入力へ戻る。 -/
  outside_restored : ∀ wire,
    wire ∉ rowOutputWires p → wire ∉ selectorOutputWires p →
      wire ≠ negativeWire p → wire ≠ activeWire p → output wire = input wire

/-- row対角分岐のXOR式と全外部wire復元を合わせた一意なcomponent仕様。 -/
structure RowDiagonalRestoredReferenceIdentification (p : QParameters) (constant : Nat)
    (enabled : Bool) (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop
    extends RowDiagonalResultWithWorkRestorationSpec p constant enabled input output where
  /-- 三外部出力以外のwireは全て入力へ戻る。 -/
  outside_restored : ∀ wire,
    wire ∉ columnKeyWires p → wire ∉ columnSelectorWires p →
      wire ≠ keySignalWire p → output wire = input wire

/-- column対角component仕様は全wire上で出力を一意に定める。 -/
theorem ColumnDiagonalRestoredReferenceIdentification.unique
    {p : QParameters} {constant : Nat} {enabled : Bool}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : ColumnDiagonalRestoredReferenceIdentification p constant enabled input left)
    (rightSpec : ColumnDiagonalRestoredReferenceIdentification p constant enabled input right) :
    left = right := by
  funext wire
  by_cases outputMember : wire ∈ rowOutputWires p
  · exact readWires_eq_at_of_eq (rowOutputWires p) left right
      (leftSpec.row_output.trans rightSpec.row_output.symm) outputMember
  by_cases selectorMember : wire ∈ selectorOutputWires p
  · exact readWires_eq_at_of_eq (selectorOutputWires p) left right
      (leftSpec.selector_output.trans rightSpec.selector_output.symm)
      selectorMember
  by_cases negativeEq : wire = negativeWire p
  · subst wire
    exact leftSpec.negative.trans rightSpec.negative.symm
  by_cases activeEq : wire = activeWire p
  · subst wire
    exact leftSpec.active.trans rightSpec.active.symm
  exact (leftSpec.outside_restored wire outputMember selectorMember negativeEq
    activeEq).trans (rightSpec.outside_restored wire outputMember selectorMember
      negativeEq activeEq).symm

/-- row対角component仕様は全wire上で出力を一意に定める。 -/
theorem RowDiagonalRestoredReferenceIdentification.unique
    {p : QParameters} {constant : Nat} {enabled : Bool}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : RowDiagonalRestoredReferenceIdentification p constant enabled input left)
    (rightSpec : RowDiagonalRestoredReferenceIdentification p constant enabled input right) :
    left = right := by
  funext wire
  by_cases keyMember : wire ∈ columnKeyWires p
  · exact readWires_eq_at_of_eq (columnKeyWires p) left right
      (leftSpec.column_key.trans rightSpec.column_key.symm) keyMember
  by_cases selectorMember : wire ∈ columnSelectorWires p
  · exact readWires_eq_at_of_eq (columnSelectorWires p) left right
      (leftSpec.column_selector.trans rightSpec.column_selector.symm)
      selectorMember
  by_cases signalEq : wire = keySignalWire p
  · subst wire
    exact leftSpec.key_signal.trans rightSpec.key_signal.symm
  exact (leftSpec.outside_restored wire keyMember selectorMember signalEq).trans
    (rightSpec.outside_restored wire keyMember selectorMember signalEq).symm

/-- cleanなactual column対角分岐は一意なcomponent仕様を満たす。 -/
theorem verifiedColumnDiagonalRestoredReferenceIdentification
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input) :
    ColumnDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input) input
      ((columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input) := by
  have result := columnDiagonalResultComputeUseUncomputeCircuit_correct p
    slot copy legalValue presentValue input clean
  refine {
    row_output := result.row_output
    selector_output := result.selector_output
    negative := result.negative
    active := result.active
    selected_restored := result.selected_restored
    branch_restored := result.branch_restored
    scratch_restored := result.scratch_restored
    outside_restored := ?_ }
  intro wire outsideOutput outsideSelector outsideNegative outsideActive
  exact columnDiagonalResultComputeUseUncomputeCircuit_outside_outputs_restored p slot copy input wire
    outsideOutput outsideSelector outsideNegative outsideActive

/-- cleanなactual row対角分岐は一意なcomponent仕様を満たす。 -/
theorem verifiedRowDiagonalRestoredReferenceIdentification
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input) :
    RowDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input) input
      ((rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input) := by
  have result := rowDiagonalResultComputeUseUncomputeCircuit_correct p slot
    copy legalValue presentValue input clean
  refine {
    column_key := result.column_key
    column_selector := result.column_selector
    key_signal := result.key_signal
    selected_restored := result.selected_restored
    branch_restored := result.branch_restored
    scratch_restored := result.scratch_restored
    outside_restored := ?_ }
  intro wire outsideKey outsideSelector outsideSignal
  exact rowDiagonalResultComputeUseUncomputeCircuit_outside_outputs_restored_actual p slot copy input wire
    outsideKey outsideSelector outsideSignal

/-- column event分岐族はpure writer出力とcompute support復元仕様を満たす。 -/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_correct
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false)
    (pairZero : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset)
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output)) :
    ColumnEventBranchReferenceResult p offset input
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      ((applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  exact applyColumnEventReferenceAndRestoreWorkCircuit_reference_correct p slot offset input scratchZero
    pairZero movedClean

/-- row event分岐族はpure writer出力とbroad support復元仕様を満たす。 -/
theorem applyRowEventReferenceAndRestoreWorkCircuit_correct
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
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
  exact applyRowEventReferenceAndRestoreWorkCircuit_reference_correct_canonical p slot offset input
    scratchZero pairZero movedClean

/-- column eventのpure writer式と全外部wire復元を合わせた一意なcomponent仕様。 -/
structure ColumnEventRestoredReferenceIdentification (p : QParameters) (offset : Fin 6)
    (input computed output : JointBasis p.ancillaWidth p.systemWidth) : Prop
    extends ColumnEventBranchReferenceResult p offset input computed output where
  /-- 三外部出力以外のwireは全て入力へ戻る。 -/
  outside_restored : ∀ wire,
    wire ∉ rowOutputWires p → wire ∉ selectorOutputWires p →
      wire ≠ activeWire p → output wire = input wire

/-- row eventのpure writer式と全外部wire復元を合わせた一意なcomponent仕様。 -/
structure RowEventRestoredReferenceIdentification (p : QParameters) (offset : Fin 6)
    (input computed output : JointBasis p.ancillaWidth p.systemWidth) : Prop
    extends RowEventBranchReferenceResult p offset input computed output where
  /-- 三外部出力以外のwireは全て入力へ戻る。 -/
  outside_restored : ∀ wire,
    wire ∉ columnKeyWires p → wire ∉ columnSelectorWires p →
      wire ≠ keySignalWire p → output wire = input wire

/-- column event component仕様は全wire上で出力を一意に定める。 -/
theorem ColumnEventRestoredReferenceIdentification.unique
    {p : QParameters} {offset : Fin 6}
    {input computed left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : ColumnEventRestoredReferenceIdentification p offset input computed left)
    (rightSpec : ColumnEventRestoredReferenceIdentification p offset input computed right) :
    left = right := by
  funext wire
  by_cases outputMember : wire ∈ rowOutputWires p
  · exact readWires_eq_at_of_eq (rowOutputWires p) left right
      (leftSpec.row_output.trans rightSpec.row_output.symm) outputMember
  by_cases selectorMember : wire ∈ selectorOutputWires p
  · exact readWires_eq_at_of_eq (selectorOutputWires p) left right
      (leftSpec.selector_output.trans rightSpec.selector_output.symm)
      selectorMember
  by_cases activeEq : wire = activeWire p
  · subst wire
    exact leftSpec.active.trans rightSpec.active.symm
  exact (leftSpec.outside_restored wire outputMember selectorMember activeEq).trans
    (rightSpec.outside_restored wire outputMember selectorMember activeEq).symm

/-- row event component仕様は全wire上で出力を一意に定める。 -/
theorem RowEventRestoredReferenceIdentification.unique
    {p : QParameters} {offset : Fin 6}
    {input computed left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : RowEventRestoredReferenceIdentification p offset input computed left)
    (rightSpec : RowEventRestoredReferenceIdentification p offset input computed right) :
    left = right := by
  funext wire
  by_cases keyMember : wire ∈ columnKeyWires p
  · exact readWires_eq_at_of_eq (columnKeyWires p) left right
      (leftSpec.column_key.trans rightSpec.column_key.symm) keyMember
  by_cases selectorMember : wire ∈ columnSelectorWires p
  · exact readWires_eq_at_of_eq (columnSelectorWires p) left right
      (leftSpec.column_selector.trans rightSpec.column_selector.symm)
      selectorMember
  by_cases signalEq : wire = keySignalWire p
  · subst wire
    exact leftSpec.key_signal.trans rightSpec.key_signal.symm
  exact (leftSpec.outside_restored wire keyMember selectorMember signalEq).trans
    (rightSpec.outside_restored wire keyMember selectorMember signalEq).symm

/-- cleanなactual column event分岐は一意なcomponent仕様を満たす。 -/
theorem verifiedColumnEventRestoredReferenceIdentification
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false)
    (pairZero : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset)
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output)) :
    ColumnEventRestoredReferenceIdentification p offset input
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      ((applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  refine {
    toColumnEventBranchReferenceResult :=
      applyColumnEventReferenceAndRestoreWorkCircuit_correct p slot offset input scratchZero
        pairZero movedClean
    outside_restored := ?_ }
  intro wire outsideOutput outsideSelector outsideActive
  exact applyColumnEventReferenceAndRestoreWorkCircuit_outside_outputs_restored p slot offset input
    scratchZero pairZero movedClean wire outsideOutput outsideSelector outsideActive

/-- cleanなactual row event分岐は一意なcomponent仕様を満たす。 -/
theorem verifiedRowEventRestoredReferenceIdentification
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false)
    (pairZero : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false)
    (movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (if offset.val % 2 = 1 then 1 else 0)
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)) :
    RowEventRestoredReferenceIdentification p offset input
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      ((applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  refine {
    toRowEventBranchReferenceResult :=
      applyRowEventReferenceAndRestoreWorkCircuit_correct p slot offset input scratchZero pairZero
        movedClean
    outside_restored := ?_ }
  intro wire outsideKey outsideSelector outsideSignal
  exact applyRowEventReferenceAndRestoreWorkCircuit_outside_outputs_restored_canonical p slot offset input
    scratchZero pairZero movedClean wire outsideKey outsideSelector outsideSignal

/-- column対角分岐のclean条件とpure出力一意性を束ねる公開component。 -/
noncomputable def compiledColumnDiagonalPhysicalContractBridgeComponent
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := columnDiagonalResultComputeUseUncomputeCircuit p slot copy
  reference := uniqueSpecificationReference fun input output =>
    ColumnDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input) input output
  inputCondition := DiagonalBranchCleanInput p slot legalValue presentValue
  outputCondition := fun _ => True
  restoration := fun input output =>
    ColumnDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input) input output
  runBasis_correct := by
    intro input conditions
    let actual := (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
      reversibleGatePermutation input
    have actualSpec := verifiedColumnDiagonalRestoredReferenceIdentification p slot copy
      legalValue presentValue input conditions
    have uniqueOutput : ∃! output, ColumnDiagonalRestoredReferenceIdentification p
        (6 * slot.val + copy.val)
        (diagonalBranchEnabled p (columnSelectorWires p) slot
          (6 * slot.val + copy.val) legalValue presentValue input) input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    have referenceSpec := uniqueSpecificationReference_spec uniqueOutput
    exact uniqueOutput.unique actualSpec referenceSpec
  outputCondition_correct := by simp
  restoration_correct := by
    intro input conditions
    let actual := (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
      reversibleGatePermutation input
    have actualSpec := verifiedColumnDiagonalRestoredReferenceIdentification p slot copy
      legalValue presentValue input conditions
    have uniqueOutput : ∃! output, ColumnDiagonalRestoredReferenceIdentification p
        (6 * slot.val + copy.val)
        (diagonalBranchEnabled p (columnSelectorWires p) slot
          (6 * slot.val + copy.val) legalValue presentValue input) input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    exact uniqueSpecificationReference_spec uniqueOutput

/-- row対角分岐のclean条件とpure出力一意性を束ねる公開component。 -/
noncomputable def compiledRowDiagonalPhysicalContractBridgeComponent
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := rowDiagonalResultComputeUseUncomputeCircuit p slot copy
  reference := uniqueSpecificationReference fun input output =>
    RowDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input) input output
  inputCondition := DiagonalBranchCleanInput p slot legalValue presentValue
  outputCondition := fun _ => True
  restoration := fun input output =>
    RowDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input) input output
  runBasis_correct := by
    intro input conditions
    let actual := (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
      reversibleGatePermutation input
    have actualSpec := verifiedRowDiagonalRestoredReferenceIdentification p slot copy
      legalValue presentValue input conditions
    have uniqueOutput : ∃! output, RowDiagonalRestoredReferenceIdentification p
        (6 * slot.val + copy.val)
        (diagonalBranchEnabled p (rowSelectorWires p) slot
          (6 * slot.val + copy.val) legalValue presentValue input) input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    have referenceSpec := uniqueSpecificationReference_spec uniqueOutput
    exact uniqueOutput.unique actualSpec referenceSpec
  outputCondition_correct := by simp
  restoration_correct := by
    intro input conditions
    let actual := (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
      reversibleGatePermutation input
    have actualSpec := verifiedRowDiagonalRestoredReferenceIdentification p slot copy
      legalValue presentValue input conditions
    have uniqueOutput : ∃! output, RowDiagonalRestoredReferenceIdentification p
        (6 * slot.val + copy.val)
        (diagonalBranchEnabled p (rowSelectorWires p) slot
          (6 * slot.val + copy.val) legalValue presentValue input) input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    exact uniqueSpecificationReference_spec uniqueOutput

/-- column event分岐componentのclean条件とpure出力一意性。 -/
structure ColumnEventBranchComponentInput (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- computed AND scratchは0である。 -/
  scratch_zero : ∀ wire ∈ decoderAndScratchWires p,
    (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false
  /-- computed pair flagは0である。 -/
  pair_zero : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
    (oraclePairWire p) = false
  /-- moved selector writerの入力はcleanである。 -/
  moved_clean : WriteMovedSelectorSlotClean p
    (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
      (by simp [rowOutputWires]) (activeWire p)
      (columnEventDegreeChange offset)
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output)

/-- row event分岐componentのclean条件とpure出力一意性。 -/
structure RowEventBranchComponentInput (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- computed AND scratchは0である。 -/
  scratch_zero : ∀ wire ∈ decoderAndScratchWires p,
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false
  /-- computed pair flagは0である。 -/
  pair_zero : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
    (oraclePairWire p) = false
  /-- moved selector writerの入力はcleanである。 -/
  moved_clean : WriteMovedSelectorSlotClean p
    (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
      (by simp [columnKeyWires]) (keySignalWire p)
      (if offset.val % 2 = 1 then 1 else 0)
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output)

/-- column event分岐族をpure writer仕様へ包装したclean component。 -/
noncomputable def compiledColumnEventPhysicalContractBridgeComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := applyColumnEventReferenceAndRestoreWorkCircuit p slot offset
  reference := uniqueSpecificationReference fun input output =>
    ColumnEventRestoredReferenceIdentification p offset input
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output output
  inputCondition := ColumnEventBranchComponentInput p slot offset
  outputCondition := fun _ => True
  restoration := fun input output =>
    ColumnEventRestoredReferenceIdentification p offset input
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output output
  runBasis_correct := by
    intro input conditions
    let actual := (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
      reversibleGatePermutation input
    have actualSpec := verifiedColumnEventRestoredReferenceIdentification p slot offset input
      conditions.scratch_zero conditions.pair_zero conditions.moved_clean
    have uniqueOutput : ∃! output, ColumnEventRestoredReferenceIdentification p offset input
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    have referenceSpec : ColumnEventRestoredReferenceIdentification p offset input
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
        (uniqueSpecificationReference (fun state output =>
          ColumnEventRestoredReferenceIdentification p offset state
            (columnEventCandidateUpdateAndSortExecutionTrace p slot offset state).output output) input) :=
      uniqueSpecificationReference_spec uniqueOutput
    exact uniqueOutput.unique actualSpec referenceSpec
  outputCondition_correct := by simp
  restoration_correct := by
    intro input conditions
    let actual := (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
      reversibleGatePermutation input
    have actualSpec := verifiedColumnEventRestoredReferenceIdentification p slot offset input
      conditions.scratch_zero conditions.pair_zero conditions.moved_clean
    have uniqueOutput : ∃! output, ColumnEventRestoredReferenceIdentification p offset input
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    exact uniqueSpecificationReference_spec uniqueOutput

/-- row event分岐族をpure writer仕様へ包装したclean component。 -/
noncomputable def compiledRowEventPhysicalContractBridgeComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := applyRowEventReferenceAndRestoreWorkCircuit p slot offset
  reference := uniqueSpecificationReference fun input output =>
    RowEventRestoredReferenceIdentification p offset input
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output output
  inputCondition := RowEventBranchComponentInput p slot offset
  outputCondition := fun _ => True
  restoration := fun input output =>
    RowEventRestoredReferenceIdentification p offset input
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output output
  runBasis_correct := by
    intro input conditions
    let actual := (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
      reversibleGatePermutation input
    have actualSpec := verifiedRowEventRestoredReferenceIdentification p slot offset input
      conditions.scratch_zero conditions.pair_zero conditions.moved_clean
    have uniqueOutput : ∃! output, RowEventRestoredReferenceIdentification p offset input
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    have referenceSpec : RowEventRestoredReferenceIdentification p offset input
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
        (uniqueSpecificationReference (fun state output =>
          RowEventRestoredReferenceIdentification p offset state
            (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset state).output output) input) :=
      uniqueSpecificationReference_spec uniqueOutput
    exact uniqueOutput.unique actualSpec referenceSpec
  outputCondition_correct := by simp
  restoration_correct := by
    intro input conditions
    let actual := (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
      reversibleGatePermutation input
    have actualSpec := verifiedRowEventRestoredReferenceIdentification p slot offset input
      conditions.scratch_zero conditions.pair_zero conditions.moved_clean
    have uniqueOutput : ∃! output, RowEventRestoredReferenceIdentification p offset input
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    exact uniqueSpecificationReference_spec uniqueOutput

/-- membership部品で比較workとAND scratchが0へ戻ることを表す復元仕様。 -/
def MembershipWorkRestored (p : QParameters)
    (output : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  MembershipSlotClean (oracleCompareWorkWires p)
    (decoderAndScratchWires p) output

/-- 全slot membership判定を純粋有限fold参照作用へ結ぶclean部品。 -/
def compiledXorMembershipMatchGoodAndAbsentFlagsBridgeCleanComponent
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot includePresentOther
  reference := MembershipMatchGoodAndAbsentFlagsXorSpec p register selectedSlot
    includePresentOther
  inputCondition := MembershipWorkRestored p
  outputCondition := MembershipWorkRestored p
  restoration := fun _ output => MembershipWorkRestored p output
  runBasis_correct := by
    intro input clean
    exact (runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit p register inputLayout selectedSlot
      includePresentOther input clean).1
  outputCondition_correct := by
    intro input clean
    have result := runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit p register inputLayout
      selectedSlot includePresentOther input clean
    rw [← result.1]
    exact result.2
  restoration_correct := by
    intro input clean
    have result := runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit p register inputLayout
      selectedSlot includePresentOther input clean
    rw [← result.1]
    exact result.2

/-- candidate生成がcandidate slice外を保存するという解析的復元関係。 -/
def CandidateOutsideRestored (p : QParameters)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ wire, wire ∉ ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).candidate).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) →
    output wire = input wire

/--
column eventのcandidate一点更新を、二回のcontrolled XORまたはmarker反転として記述する
回路非依存の解析作用。
-/
def ControlledSelectedColumnCandidateWordUpdateSpec (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let branch := oracleBranchWire p
  let keyWord := registerWordAt p (columnKeyWires p) slot
  let candidateData :=
    (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let afterRemove := controlledCopyBasisReference (input branch)
    keyWord candidateData input
  if offset.val % 2 = 1 then
    cnotBasisAction branch (candidateMarkerWire p (slotToSortWord p slot)) afterRemove
  else
    controlledCopyBasisReference (afterRemove branch)
      (oracleMovedWires p) candidateData afterRemove

/-- candidate一点更新の基本ゲート列はpureな解析作用と全入力で厳密に一致する。 -/
theorem runBasis_columnEventModify_eq_analytic
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation input =
      ControlledSelectedColumnCandidateWordUpdateSpec p slot offset input := by
  let branch := oracleBranchWire p
  let keyWord := registerWordAt p (columnKeyWires p) slot
  let candidateData :=
    (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let moved := oracleMovedWires p
  let afterRemove := controlledCopyBasisReference (input branch)
    keyWord candidateData input
  have keyLength : keyWord.length = candidateData.length := by
    rw [show keyWord.length = p.wordWidth by
      exact registerWordAt_length p (columnKeyWires p)
        (by simp [columnKeyWires]) slot]
    simp [candidateData]
  have movedLength : moved.length = candidateData.length := by
    simp [moved, oracleMovedWires, QParameters.movedWidth, candidateData]
  have keyDisjoint : keyWord.Disjoint candidateData :=
    columnKeyRegisterWord_disjoint_candidateData p slot (slotToSortWord p slot)
  have movedDisjoint : moved.Disjoint candidateData :=
    columnOracleMoved_disjoint_candidateData p (slotToSortWord p slot)
  have keyNodup : keyWord.Nodup := by
    dsimp [keyWord, registerWordAt]
    exact (columnKeyWires_nodup p).drop.take
  have candidateNodup : candidateData.Nodup :=
    (candidateWordAt_nodup p (slotToSortWord p slot)).take
  have movedNodup : moved.Nodup := by
    simpa [moved] using (columnEventMoveLayout_canonical p slot offset).moved_nodup
  have branchAbsentKey : branch ∉ keyWord := by
    intro member
    exact oracleBranchWire_not_mem_columnKeyWires p
      (mem_register_of_mem_registerWordAt p (columnKeyWires p) slot member)
  have branchAbsentCandidate : branch ∉ candidateData :=
    columnOracleBranchWire_not_mem_candidateData p (slotToSortWord p slot)
  have branchAbsentMoved : branch ∉ moved :=
    columnOracleBranchWire_not_mem_moved p
  have removeEq :
      (columnEventRemoveSource p slot).runBasis reversibleGatePermutation input =
        afterRemove := by
    simpa [columnEventRemoveSource, branch, keyWord, candidateData, afterRemove] using
      runBasis_validatedControlledXorCopyLists_eq_controlledCopyBasisReference
        branch keyWord candidateData input keyNodup candidateNodup
        keyLength keyDisjoint branchAbsentKey branchAbsentCandidate
  by_cases collision : offset.val % 2 = 1
  · rw [controlledUpdateSelectedColumnCandidateWordCircuit, if_pos collision, runBasis_seq, removeEq]
    rw [runBasis_safeCnot branch
      (candidateMarkerWire p (slotToSortWord p slot))
      (columnOracleBranchWire_ne_candidateMarker p (slotToSortWord p slot))]
    simp [ControlledSelectedColumnCandidateWordUpdateSpec, collision, branch, keyWord,
      candidateData, afterRemove]
  · rw [controlledUpdateSelectedColumnCandidateWordCircuit, if_neg collision, runBasis_seq, removeEq]
    rw [runBasis_validatedControlledXorCopyLists_eq_controlledCopyBasisReference
      branch moved candidateData afterRemove movedNodup candidateNodup
      movedLength movedDisjoint branchAbsentMoved branchAbsentCandidate]
    simp [ControlledSelectedColumnCandidateWordUpdateSpec, collision, branch, keyWord,
      candidateData, moved, afterRemove]

/-- column eventのcandidate一点更新を解析作用と外部wire保存へ包装した公開部品族。 -/
def verifiedControlledUpdateSelectedColumnCandidateWordCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := controlledUpdateSelectedColumnCandidateWordCircuit p slot offset
  reference := ControlledSelectedColumnCandidateWordUpdateSpec p slot offset
  inputCondition := fun _ => True
  outputCondition := fun _ => True
  restoration := CandidateOutsideRestored p
  runBasis_correct := by
    intro input _
    exact runBasis_columnEventModify_eq_analytic p slot offset input
  outputCondition_correct := by simp
  restoration_correct := by
    intro input _ wire outside
    rw [← runBasis_columnEventModify_eq_analytic p slot offset input]
    exact runBasis_columnEventModify_outside_candidateSlice p slot offset input wire outside

/-- row candidate更新の一時pairとAND scratchの自然なclean条件。 -/
structure RowCandidateUpdateCleanInput (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- AND scratchは0である。 -/
  scratch_zero : ∀ wire ∈ decoderAndScratchWires p, input wire = false
  /-- pair flagは0である。 -/
  pair_zero : input (oraclePairWire p) = false

/-- 一つのdegree slotに対応するrow collision追加のpure条件分岐作用。 -/
def rowEventCollisionStepAnalyticAction (p : QParameters)
    (degreeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  if input (oracleBranchWire p) = true ∧
      input (oracleDegreeWireAt p
        (rowEventCollisionDegreeIndex p degreeSlot)) = true then
    rowEventCollisionAppendReference p degreeSlot input
  else input

/-- degree slot有限列に沿ってcollision追加作用を合成するpure有限fold。 -/
def rowEventCollisionSequenceAnalyticAction (p : QParameters)
    (slots : List (Fin (p.K - 1)))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  slots.foldl (fun state degreeSlot =>
    rowEventCollisionStepAnalyticAction p degreeSlot state) input

/-- replacement時にarrival candidateをmoved sourceへ置き換えるpure XOR作用。 -/
def rowEventReplacementAnalyticAction (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let branch := oracleBranchWire p
  let arrival := registerWordAt p (systemWires p) slot
  let candidate :=
    (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let removed := controlledCopyBasisReference (input branch)
    arrival candidate input
  controlledCopyBasisReference (removed branch)
    (oracleMovedWires p) candidate removed

/-- collision/replacementをoffsetの偶奇で選ぶrow candidate更新のpure作用。 -/
def ControlledSelectedRowCandidateWordUpdateSpec (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  if offset.val % 2 = 1 then
    rowEventCollisionSequenceAnalyticAction p (List.finRange (p.K - 1)) input
  else rowEventReplacementAnalyticAction p slot input

/-- 一slotのcollision回路はclean入力上でpure条件分岐作用に一致する。 -/
theorem runBasis_rowEventCollisionModifyAt_eq_analytic
    (p : QParameters) (degreeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowCandidateUpdateCleanInput p input) :
    (controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot).runBasis
        reversibleGatePermutation input =
      rowEventCollisionStepAnalyticAction p degreeSlot input := by
  by_cases branchTrue : input (oracleBranchWire p) = true
  · by_cases degreeTrue : input (oracleDegreeWireAt p
        (rowEventCollisionDegreeIndex p degreeSlot)) = true
    · simpa [rowEventCollisionStepAnalyticAction, branchTrue, degreeTrue] using
        runBasis_rowEventCollisionModifyAt_active p degreeSlot input
          clean.scratch_zero clean.pair_zero branchTrue degreeTrue
    · have degreeFalse := Bool.eq_false_of_not_eq_true degreeTrue
      simpa [rowEventCollisionStepAnalyticAction, branchTrue, degreeFalse] using
        runBasis_rowEventCollisionModifyAt_inactive p degreeSlot input
          clean.scratch_zero clean.pair_zero (Or.inr degreeFalse)
  · have branchFalse := Bool.eq_false_of_not_eq_true branchTrue
    simpa [rowEventCollisionStepAnalyticAction, branchFalse] using
      runBasis_rowEventCollisionModifyAt_inactive p degreeSlot input
        clean.scratch_zero clean.pair_zero (Or.inl branchFalse)

/-- 一slotのpure collision作用はpairとAND scratchのclean性を保存する。 -/
theorem rowEventCollisionStepAnalyticAction_clean
    (p : QParameters) (degreeSlot : Fin (p.K - 1))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowCandidateUpdateCleanInput p input) :
    RowCandidateUpdateCleanInput p
      (rowEventCollisionStepAnalyticAction p degreeSlot input) := by
  by_cases enabled : input (oracleBranchWire p) = true ∧
      input (oracleDegreeWireAt p
        (rowEventCollisionDegreeIndex p degreeSlot)) = true
  · have preserve := rowEventCollisionAppendReference_preserves_pairSupport
      p degreeSlot input
    refine { scratch_zero := ?_, pair_zero := ?_ }
    · intro wire member
      rw [show rowEventCollisionStepAnalyticAction p degreeSlot input =
          rowEventCollisionAppendReference p degreeSlot input by
        simp [rowEventCollisionStepAnalyticAction, enabled]]
      rw [preserve wire (decoderAndScratchWire_mem_writeSortedPairSupport p member)]
      exact clean.scratch_zero wire member
    · rw [show rowEventCollisionStepAnalyticAction p degreeSlot input =
          rowEventCollisionAppendReference p degreeSlot input by
        simp [rowEventCollisionStepAnalyticAction, enabled]]
      rw [preserve (oraclePairWire p) (oraclePairWire_mem_writeSortedPairSupport p)]
      exact clean.pair_zero
  · simpa [rowEventCollisionStepAnalyticAction, enabled] using clean

/-- collision回路有限列とpure有限foldの一致を、列長について帰納的に証明する。 -/
theorem runBasis_rowEventCollisionSequence_eq_analytic
    (p : QParameters) : ∀ (slots : List (Fin (p.K - 1)))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      RowCandidateUpdateCleanInput p input →
      (Circuit.sequence (slots.map (controlledUpdateRowCollisionCandidateAtDegreeCircuit p))).runBasis
          reversibleGatePermutation input =
        rowEventCollisionSequenceAnalyticAction p slots input
  | [], _, _ => rfl
  | degreeSlot :: slots, input, clean => by
      change (Circuit.sequence (slots.map (controlledUpdateRowCollisionCandidateAtDegreeCircuit p))).runBasis
        reversibleGatePermutation
          ((controlledUpdateRowCollisionCandidateAtDegreeCircuit p degreeSlot).runBasis
            reversibleGatePermutation input) = _
      rw [runBasis_rowEventCollisionModifyAt_eq_analytic p degreeSlot input clean]
      exact runBasis_rowEventCollisionSequence_eq_analytic p slots
        (rowEventCollisionStepAnalyticAction p degreeSlot input)
        (rowEventCollisionStepAnalyticAction_clean p degreeSlot input clean)

/-- replacement回路は全入力上でpureな二段controlled XOR作用に一致する。 -/
theorem runBasis_rowEventReplacementModify_eq_analytic
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledUpdateSelectedRowReplacementCandidateWordCircuit p slot).runBasis reversibleGatePermutation input =
      rowEventReplacementAnalyticAction p slot input := by
  let branch := oracleBranchWire p
  let arrival := registerWordAt p (systemWires p) slot
  let candidate :=
    (candidateWordAt p (slotToSortWord p slot)).take p.wordWidth
  let removed := controlledCopyBasisReference (input branch) arrival candidate input
  have arrivalLength : arrival.length = candidate.length := by
    rw [show arrival.length = p.wordWidth by
      exact registerWordAt_length p (systemWires p) (systemWires_length p) slot]
    simp [candidate]
  have movedLength : (oracleMovedWires p).length = candidate.length := by
    simp [oracleMovedWires, QParameters.movedWidth, candidate]
  have arrivalDisjoint := systemRegisterWord_disjoint_candidateData p slot
    (slotToSortWord p slot)
  have movedDisjoint := oracleMovedWires_disjoint_candidateData p
    (slotToSortWord p slot)
  have arrivalNodup : arrival.Nodup := by
    dsimp [arrival, registerWordAt]
    exact (systemWires_nodup p).drop.take
  have candidateNodup : candidate.Nodup :=
    (candidateWordAt_nodup p (slotToSortWord p slot)).take
  have movedNodup : (oracleMovedWires p).Nodup :=
    oracleMovedWires_nodup p
  have branchAbsentArrival : branch ∉ arrival := by
    intro member
    exact oracleBranchWire_not_mem_systemWires p
      (mem_register_of_mem_registerWordAt p (systemWires p) slot member)
  have branchAbsentMoved : branch ∉ oracleMovedWires p := by
    exact columnOracleBranchWire_not_mem_moved p
  have branchAbsentCandidate : branch ∉ candidate :=
    oracleBranchWire_not_mem_candidateData p (slotToSortWord p slot)
  have removeEq :
      (controlledXorCopy branch arrival candidate).runBasis
          reversibleGatePermutation input = removed := by
    exact runBasis_validatedControlledXorCopyLists_eq_controlledCopyBasisReference
      branch arrival candidate input arrivalNodup candidateNodup
      arrivalLength arrivalDisjoint branchAbsentArrival branchAbsentCandidate
  rw [controlledUpdateSelectedRowReplacementCandidateWordCircuit, runBasis_seq, removeEq]
  rw [runBasis_validatedControlledXorCopyLists_eq_controlledCopyBasisReference
    branch (oracleMovedWires p) candidate removed movedNodup candidateNodup
    movedLength movedDisjoint branchAbsentMoved branchAbsentCandidate]
  rfl

/-- row candidate更新正本はclean入力上でpure更新作用に一致する。 -/
theorem runBasis_rowEventModify_eq_analytic
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowCandidateUpdateCleanInput p input) :
    (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation input =
      ControlledSelectedRowCandidateWordUpdateSpec p slot offset input := by
  by_cases collision : offset.val % 2 = 1
  · simpa [controlledUpdateSelectedRowCandidateWordCircuit, ControlledSelectedRowCandidateWordUpdateSpec, collision,
      controlledUpdateSelectedRowCollisionCandidateWordCircuit] using
      runBasis_rowEventCollisionSequence_eq_analytic p
        (List.finRange (p.K - 1)) input clean
  · simpa [controlledUpdateSelectedRowCandidateWordCircuit, ControlledSelectedRowCandidateWordUpdateSpec, collision] using
      runBasis_rowEventReplacementModify_eq_analytic p slot input

/-- row candidate更新をpure作用とcandidate外保存へ包装した公開clean component。 -/
def verifiedControlledUpdateSelectedRowCandidateWordCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := controlledUpdateSelectedRowCandidateWordCircuit p slot offset
  reference := ControlledSelectedRowCandidateWordUpdateSpec p slot offset
  inputCondition := EventSortCleanInput p
  outputCondition := fun _ => True
  restoration := CandidateOutsideRestored p
  runBasis_correct := by
    intro input clean
    exact runBasis_rowEventModify_eq_analytic p slot offset input
      ⟨clean.moved_selector.scratch_zero, clean.moved_selector.pair_zero⟩
  outputCondition_correct := by simp
  restoration_correct := by
    intro input clean wire outside
    rw [← runBasis_rowEventModify_eq_analytic p slot offset input
      ⟨clean.moved_selector.scratch_zero, clean.moved_selector.pair_zero⟩]
    exact runBasis_rowEventModify_outside_candidateSlice p slot offset input clean
      wire outside

/-- candidate更新部品族のcolumn/row両モードを型安全に区別する添字。 -/
inductive CandidateUpdateMode (p : QParameters) where
  /-- column eventのsource除去・collision markerまたはreplacement追加。 -/
  | column (slot : Fin p.K) (offset : Fin 6)
  /-- row eventのcollision有限foldまたはreplacement。 -/
  | row (slot : Fin p.K) (offset : Fin 6)

/-- column/row modeを一つの型で受け取る、selected candidate word更新の解析作用。 -/
def ControlledSelectedCandidateWordUpdateSpec (p : QParameters) :
    CandidateUpdateMode p → JointBasis p.ancillaWidth p.systemWidth →
      JointBasis p.ancillaWidth p.systemWidth
  | .column slot offset => ControlledSelectedColumnCandidateWordUpdateSpec p slot offset
  | .row slot offset => ControlledSelectedRowCandidateWordUpdateSpec p slot offset

/-- column/row modeからcandidate更新の正本回路ASTを選ぶ公開回路族。 -/
def controlledUpdateSelectedCandidateWordCircuit (p : QParameters) :
    CandidateUpdateMode p → Circuit (ReversibleGate p.ancillaWidth p.systemWidth)
  | .column slot offset => controlledUpdateSelectedColumnCandidateWordCircuit p slot offset
  | .row slot offset => controlledUpdateSelectedRowCandidateWordCircuit p slot offset

/-- column/row candidate更新を一つの公開parameterized component familyに統合する。 -/
def verifiedControlledUpdateSelectedCandidateWordCleanComponent (p : QParameters) :
    CandidateUpdateMode p →
      CleanComponent (reversibleGatePermutation
        (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth))
  | .column slot offset => verifiedControlledUpdateSelectedColumnCandidateWordCleanComponent p slot offset
  | .row slot offset => verifiedControlledUpdateSelectedRowCandidateWordCleanComponent p slot offset

/-- candidate更新component族のcircuit fieldは公開正本回路族に一致する。 -/
@[simp] theorem verifiedControlledUpdateSelectedCandidateWordCleanComponent_circuit
    (p : QParameters) (mode : CandidateUpdateMode p) :
    (verifiedControlledUpdateSelectedCandidateWordCleanComponent p mode).circuit = controlledUpdateSelectedCandidateWordCircuit p mode := by
  cases mode <;> rfl

/-- candidate更新component familyのreferenceはmode別解析作用と定義的に一致する。 -/
@[simp] theorem verifiedControlledUpdateSelectedCandidateWordCleanComponent_reference
    (p : QParameters) (mode : CandidateUpdateMode p) :
    (verifiedControlledUpdateSelectedCandidateWordCleanComponent p mode).reference =
      ControlledSelectedCandidateWordUpdateSpec p mode := by
  cases mode <;> rfl

/-- delimiter由来のwordからcandidate列を作る純粋参照作用の検証済み部品。 -/
def verifiedXorConfigurationIntoCandidateRegisterCleanComponent
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorConfigurationIntoCandidateRegisterCircuit p register
  reference := ConfigurationToCandidateRegisterXorSpec p register
  inputCondition := fun _ => True
  outputCondition := fun _ => True
  restoration := CandidateOutsideRestored p
  runBasis_correct := by
    intro input _
    exact runBasis_xorConfigurationIntoCandidateRegisterCircuit p register layout input
  outputCondition_correct := by simp
  restoration_correct := by
    intro input _ wire outside
    apply configurationToCandidateRegisterXorSpec_other
    · intro word member
      exact outside (candidateWordAt_mem_candidateSlice p word
        (List.mem_of_mem_take member))
    · intro word equal
      apply outside
      rw [equal]
      exact candidateMarkerWire_mem_candidateSlice p word

/-- bitonic sortを実行可能にするcompare・scratch・historyのclean条件。 -/
structure BitonicSortCleanInput (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 比較workは0である。 -/
  compare_zero : readWires (sortCompareWorkWires p) input =
    List.replicate (sortCompareWorkWires p).length false
  /-- AND scratchは0である。 -/
  scratch_zero : ∀ wire ∈ sortAndScratchWires p, input wire = false
  /-- 各compare--exchangeのhistory bitは0である。 -/
  history_zero : ∀ instruction ∈ qTypedBitonicSchedule p,
    input ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire
        instruction.history) = false

private theorem BitonicSortCleanInput.toShared
    {p : QParameters} {input : JointBasis p.ancillaWidth p.systemWidth}
    (clean : BitonicSortCleanInput p input) :
    BitonicSharedClean.SharedBitonicSortCleanInput p
      (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input) := by
  constructor
  · intro coreWire coreMember
    rcases List.mem_map.mp coreMember with ⟨wire, wireMember, rfl⟩
    have zero := readWires_eq_replicate_false_at
      (sortCompareWorkWires p) input clean.compare_zero wireMember
    simpa [analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv] using zero
  · intro coreWire coreMember
    rcases List.mem_map.mp coreMember with ⟨wire, wireMember, rfl⟩
    simpa [analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv] using
      clean.scratch_zero wire wireMember
  · intro instruction member
    simpa [BitonicSharedClean.historyCoreWire,
      analyticJointBasisCoreEquiv, analyticCanonicalWireEquiv] using
      clean.history_zero instruction member

/-- bitonic sortが候補・history以外を保存するという解析的復元関係。 -/
def BitonicOutsideRestored (p : QParameters)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ wire,
    (∀ word : Fin p.sortWordCount, wire ∉ candidateWordAt p word) →
    (∀ instruction ∈ qTypedBitonicSchedule p,
      wire ≠ (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) →
    output wire = input wire

/-- Shared-combinator Q-basis adapter for the frozen sort permutation child. -/
private def sharedReversibleCandidateSortCleanComponent (p : QParameters) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  CleanComponent.refineReference
    (CleanComponent.ofPermutation (BitonicTotalProgram.sortPermutationComponent p))
    (CanonicalCandidateSortWithHistoryRestorationSpec p (qTypedBitonicSchedule p))
    (BitonicSortCleanInput p)
    (fun output => IsSortedFin (qCandidateValue p output))
    (BitonicOutsideRestored p)
    (by intro _ _; trivial)
    (by
      intro input clean
      change (BitonicTotalProgram.sort p).permutationComponent.reference input = _
      rw [TotalReversibleStage.permutationComponent_reference]
      exact BitonicSharedClean.sortReference_eq_canonicalCandidateReference
        p input clean.toShared)
    (by
      intro input clean
      have sorted :=
        (BitonicSharedClean.sharedBitonicSortCleanPlan p).outputCondition_correct
          (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input)
          clean.toShared
      change IsSortedFin (BitonicSharedClean.sharedReadValues p
        (VerifiedCircuitCore.bitonicCompareSwapSequenceBasisAction
          (BitonicSharedClean.compareSwapSpecs p)
          (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input))) at sorted
      rw [BitonicSharedClean.bitonicCompareSwapSequenceBasisAction_eq_sharedCanonicalReference
        p _ clean.toShared] at sorted
      unfold BitonicSharedClean.sharedReadValues at sorted
      unfold BitonicSharedClean.sharedCanonicalReference at sorted
      simpa only [Equiv.symm_apply_apply] using sorted)
    (by
      intro input _ wire outsideCandidates outsideHistories
      exact canonicalCandidateSortWithHistoryRestorationSpec_preserves_other p
        (qTypedBitonicSchedule p) input wire outsideCandidates outsideHistories)

/-- Q用bitonic正本を、shared clean parentと純粋schedule作用へ結ぶclean部品。 -/
def verifiedReversibleCandidateSortWithHistoryRestorationCleanComponent (p : QParameters) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := reversiblySortCandidateWordsAndRestoreHistoryCircuit p
  reference := CanonicalCandidateSortWithHistoryRestorationSpec p (qTypedBitonicSchedule p)
  inputCondition := BitonicSortCleanInput p
  outputCondition := fun output => IsSortedFin (qCandidateValue p output)
  restoration := BitonicOutsideRestored p
  runBasis_correct := by
    intro input clean
    rw [← BitonicTotalProgram.compile_sort,
      ← TotalReversibleStage.permutationComponent_circuit]
    exact (sharedReversibleCandidateSortCleanComponent p).runBasis_correct input clean
  outputCondition_correct :=
    (sharedReversibleCandidateSortCleanComponent p).outputCondition_correct
  restoration_correct :=
    (sharedReversibleCandidateSortCleanComponent p).restoration_correct

/-- sorted writer内部のAND scratchとpair flagのclean条件。 -/
structure SortedWriterCleanInput (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- AND scratchは0である。 -/
  scratch_zero : ∀ wire ∈ decoderAndScratchWires p, input wire = false
  /-- 一時pair flagは0である。 -/
  pair_zero : input (oraclePairWire p) = false

/-- canonical sorted writerを純粋有限fold作用へ結ぶclean部品。 -/
def verifiedXorSortedCandidatesAsDelimiterIntoOutputCleanComponent
    (p : QParameters) (kind : CanonicalSortedOutputKind)
    (degreeChange : Int) : CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorSortedCandidatesAsDelimiterIntoOutputCircuit p (canonicalSortedOutputWires p kind)
    (canonicalSortedOutputWires_length p kind)
    (canonicalSortedOutputActive p kind) degreeChange
  reference := SortedCandidatesDelimiterOutputXorSpec p
    (canonicalSortedOutputWires p kind)
    (canonicalSortedOutputWires_length p kind)
    (canonicalSortedOutputActive p kind) degreeChange
  inputCondition := SortedWriterCleanInput p
  outputCondition := SortedWriterCleanInput p
  restoration := fun _ output => SortedWriterCleanInput p output
  runBasis_correct := by
    intro input clean
    exact runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical p kind degreeChange input
      clean.scratch_zero clean.pair_zero
  outputCondition_correct := by
    intro input clean
    have result := runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_work_clean_canonical p kind
      degreeChange input clean.scratch_zero clean.pair_zero
    rw [runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical p kind degreeChange input
      clean.scratch_zero clean.pair_zero] at result
    exact ⟨result.1, result.2⟩
  restoration_correct := by
    intro input clean
    have result := runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_work_clean_canonical p kind
      degreeChange input clean.scratch_zero clean.pair_zero
    rw [runBasis_xorSortedCandidatesAsDelimiterIntoOutputCircuit_canonical p kind degreeChange input
      clean.scratch_zero clean.pair_zero] at result
    exact ⟨result.1, result.2⟩

/--
moved selector writerのpure有限fold出力と、selector accumulator外の全wire保存を合わせた
一意な解析仕様。
-/
structure MovedMemberPositionSelectorOutputXorSpec (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- selector accumulatorはpure有限foldが与えるbit列になる。 -/
  selector_bits : readWires outputSelector output =
    movedMemberPositionSelectorOutputXorReference p offset outputSelector input
  /-- selector accumulator外の全wireは入力値を保存する。 -/
  outside_restored : BasisAgreeOutside outputSelector output input

/-- moved selector writerの解析仕様は全wire上で出力を一意に定める。 -/
theorem MovedMemberPositionSelectorOutputXorSpec.unique
    {p : QParameters} {offset : Nat}
    {outputSelector : List (Wire p.ancillaWidth p.systemWidth)}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : MovedMemberPositionSelectorOutputXorSpec p offset outputSelector input left)
    (rightSpec : MovedMemberPositionSelectorOutputXorSpec p offset outputSelector input right) :
    left = right := by
  funext wire
  by_cases member : wire ∈ outputSelector
  · exact readWires_eq_at_of_eq outputSelector left right
      (leftSpec.selector_bits.trans rightSpec.selector_bits.symm) member
  · exact (leftSpec.outside_restored wire member).trans
      (rightSpec.outside_restored wire member).symm

/-- canonical layout上のmoved selector正本は一意なpure全wire仕様を満たす。 -/
theorem verifiedMovedMemberPositionSelectorOutputXorSpec
    (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (layouts : ∀ slot : Fin p.K,
      WriteMovedSelectorSlotLayout p slot outputSelector)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : WriteMovedSelectorSlotClean p input) :
    MovedMemberPositionSelectorOutputXorSpec p offset outputSelector input
      ((xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector).runBasis
        reversibleGatePermutation input) := by
  refine {
    selector_bits := readWires_xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector input
      layouts clean
    outside_restored := ?_ }
  rw [runBasis_xorMovedMemberPositionIntoSelectorOutputCircuit_slotFold]
  exact (runBasis_xorMovedMemberPositionIntoSelectorOutputCircuitSlotList_correct p offset outputSelector input
    layouts clean (List.finRange p.K) input (by
      intro wire outside
      rfl)).2

/-- moved selector writerをpure有限fold作用と全内部work保存へ包装した公開部品族。 -/
noncomputable def verifiedXorMovedMemberPositionIntoSelectorOutputCleanComponent
    (p : QParameters) (offset : Nat)
    (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (layouts : ∀ slot : Fin p.K,
      WriteMovedSelectorSlotLayout p slot outputSelector) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector
  reference := uniqueSpecificationReference fun input output =>
    MovedMemberPositionSelectorOutputXorSpec p offset outputSelector input output
  inputCondition := WriteMovedSelectorSlotClean p
  outputCondition := fun _ => True
  restoration := MovedMemberPositionSelectorOutputXorSpec p offset outputSelector
  runBasis_correct := by
    intro input clean
    let actual := (xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector).runBasis
      reversibleGatePermutation input
    have actualSpec : MovedMemberPositionSelectorOutputXorSpec p offset outputSelector
        input actual :=
      verifiedMovedMemberPositionSelectorOutputXorSpec p offset outputSelector layouts input clean
    have uniqueOutput : ∃! output,
        MovedMemberPositionSelectorOutputXorSpec p offset outputSelector input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    have referenceSpec := uniqueSpecificationReference_spec uniqueOutput
    exact uniqueOutput.unique actualSpec referenceSpec
  outputCondition_correct := by simp
  restoration_correct := by
    intro input clean
    let actual := (xorMovedMemberPositionIntoSelectorOutputCircuit p offset outputSelector).runBasis
      reversibleGatePermutation input
    have actualSpec : MovedMemberPositionSelectorOutputXorSpec p offset outputSelector
        input actual :=
      verifiedMovedMemberPositionSelectorOutputXorSpec p offset outputSelector layouts input clean
    have uniqueOutput : ∃! output,
        MovedMemberPositionSelectorOutputXorSpec p offset outputSelector input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    exact uniqueSpecificationReference_spec uniqueOutput

/-! ## event branch の第2版階層契約 -/

/-- selector比較を回路非依存の条件分岐として表す解析作用。 -/
def selectorEqualsConstantAnalyticAction
    {ancillaQubits systemQubits : Nat}
    (selector : List (Wire ancillaQubits systemQubits)) (constant : Nat)
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if decide (readWires selector input = constantBits constant selector.length) then
    xBasisAction target input
  else input

/-- 多重制御ANDの解析作用。 -/
def positiveControlAnalyticAction
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if allWiresTrue controls input then xBasisAction target input else input

/-- column event computeを構成する八つのpure参照作用の状態記録。 -/
/- column event computeへ代入する八つのpure子参照関数。 -/
def columnEventPrimitiveReferences (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    OracleAnalytic.EventPrimitiveReferences
      (JointBasis p.ancillaWidth p.systemWidth) where
  selector := selectorEqualsConstantAnalyticAction (columnSelectorWires p)
    (6 * slot.val + offset.val) (oracleSelectedWire p)
  moved := controlledCopyBasisReference true
    (registerWordAt p (columnKeyWires p) slot) (oracleMovedWires p)
  move := incrementWordCarrySequenceReference [] (columnEventCoordinate p offset)
  membership := MembershipMatchGoodAndAbsentFlagsXorSpec p (columnKeyWires p) slot true
  branch := positiveControlAnalyticAction (columnEventBranchControls p slot offset)
    (oracleBranchWire p)
  candidates := ConfigurationToCandidateRegisterXorSpec p (columnKeyWires p)
  modify := ControlledSelectedColumnCandidateWordUpdateSpec p slot offset
  sort := CanonicalCandidateSortWithHistoryRestorationSpec p (qTypedBitonicSchedule p)

/-- column event computeの八段階をpure子参照関数から組み立てる。 -/
def ColumnEventCandidateUpdateAndSortStateSpec (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    EventComputeAnalyticStates
      (JointBasis p.ancillaWidth p.systemWidth) :=
  OracleAnalytic.eventStates (columnEventPrimitiveReferences p slot offset) input

/-- column event computeの各子部品を適用できるpureな段階別clean条件。 -/
structure ColumnEventCandidateUpdateAndSortCleanInput (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- selector比較用scratchは0である。 -/
  selector_scratch : ∀ wire ∈ decoderAndScratchWires p, input wire = false
  /-- increment開始時のscratchは0である。 -/
  move_scratch : ∀ wire ∈ decoderAndScratchWires p,
    (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).afterMovedCopy wire = false
  /-- membership部品の入力workはcleanである。 -/
  membership_clean : MembershipWorkRestored p
    (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).afterMove
  /-- branch AND開始時のscratchは0である。 -/
  branch_scratch : ∀ wire ∈ decoderAndScratchWires p,
    (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).afterMembership wire = false
  /-- sort部品の入力workはcleanである。 -/
  sort_clean : BitonicSortCleanInput p
    (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).afterModify

/-- 通常のevent-sort clean条件からcolumn event子component列の段階別clean条件を導く。 -/
theorem ColumnEventCandidateUpdateAndSortCleanInput.ofEventSortClean
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    ColumnEventCandidateUpdateAndSortCleanInput p slot offset input := by
  let states := ColumnEventCandidateUpdateAndSortStateSpec p slot offset input
  have selectorEq :
      (columnEventSelectorCompute p slot offset).runBasis
          reversibleGatePermutation input = states.afterSelector := by
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      selectorEqualsConstantAnalyticAction, columnEventSelectorMatches,
      diagonalSelectorMatches] using
      runBasis_columnEventSelectorCompute p slot offset input
        clean.moved_selector.scratch_zero
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [← selectorEq]
    exact EventSortCleanInput.of_columnEventSelectorCompute p slot offset input clean
  have movedEq :
      (columnEventMovedCopy p slot).runBasis reversibleGatePermutation
          states.afterSelector = states.afterMovedCopy := by
    exact runBasis_columnEventMovedCopy_eq_controlledCopyReference p slot
      states.afterSelector
  have movedClean : EventSortCleanInput p states.afterMovedCopy := by
    rw [← movedEq]
    exact EventSortCleanInput.of_columnEventMovedCopy p slot _ selectorClean
  have moveEq :
      (columnEventMoveForward p offset).runBasis reversibleGatePermutation
          states.afterMovedCopy = states.afterMove := by
    exact (compiledIncrementWordMod2PowInPlaceBridgeCleanComponent (columnEventCoordinate p offset)
      (decoderAndScratchWires p)
      (columnEventMoveLayout_canonical p slot offset).enough_scratch
      (columnEventMoveLayout_canonical p slot offset).coordinate_scratch_nodup
      ).runBasis_correct states.afterMovedCopy
        movedClean.moved_selector.scratch_zero
  have moveClean : EventSortCleanInput p states.afterMove := by
    rw [← moveEq]
    exact EventSortCleanInput.of_columnEventMoveForward p offset _ movedClean
  have membershipInput : MembershipWorkRestored p states.afterMove := {
    equalWork_zero := moveClean.moved_selector.compare_zero
    scratch_zero := moveClean.moved_selector.scratch_zero }
  have membershipEq :
      (columnEventMembership p slot).runBasis reversibleGatePermutation
          states.afterMove = states.afterMembership :=
    (compiledXorMembershipMatchGoodAndAbsentFlagsBridgeCleanComponent p (columnKeyWires p)
      (columnKeyWires_membershipInputLayout p) slot true).runBasis_correct
        states.afterMove membershipInput
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    rw [← membershipEq]
    exact EventSortCleanInput.of_columnEventMembership p slot _ moveClean
  have branchEq :
      (columnEventBranchCompute p slot offset).runBasis reversibleGatePermutation
          states.afterMembership = states.afterBranch := by
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      positiveControlAnalyticAction] using
      runBasis_columnEventBranchCompute_canonical p slot offset
        states.afterMembership membershipClean.moved_selector.scratch_zero
  have branchClean : EventSortCleanInput p states.afterBranch := by
    rw [← branchEq]
    exact EventSortCleanInput.of_columnEventBranchCompute p slot offset _
      membershipClean
  have candidatesEq :
      (xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
          reversibleGatePermutation states.afterBranch = states.afterCandidates := by
    have result := (verifiedXorConfigurationIntoCandidateRegisterCleanComponent p (columnKeyWires p)
      (columnKeyWires_candidateInputLayout p)).runBasis_correct
        states.afterBranch trivial
    change (xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
      reversibleGatePermutation states.afterBranch =
        ConfigurationToCandidateRegisterXorSpec p (columnKeyWires p) states.afterBranch at result
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedXorConfigurationIntoCandidateRegisterCleanComponent] using result
  have candidatesClean : EventSortCleanInput p states.afterCandidates := by
    rw [← candidatesEq]
    exact EventSortCleanInput.of_xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)
      (columnKeyWires_candidateInputLayout p) _ branchClean
  have modifyEq :
      (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
          states.afterCandidates = states.afterModify := by
    have result := (verifiedControlledUpdateSelectedColumnCandidateWordCleanComponent p slot offset).runBasis_correct
      states.afterCandidates trivial
    change (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
      states.afterCandidates = ControlledSelectedColumnCandidateWordUpdateSpec p slot offset
        states.afterCandidates at result
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedControlledUpdateSelectedColumnCandidateWordCleanComponent] using result
  have modifyClean : EventSortCleanInput p states.afterModify := by
    rw [← modifyEq]
    exact EventSortCleanInput.of_columnEventModify p slot offset _ candidatesClean
  exact {
    selector_scratch := clean.moved_selector.scratch_zero
    move_scratch := movedClean.moved_selector.scratch_zero
    membership_clean := membershipInput
    branch_scratch := membershipClean.moved_selector.scratch_zero
    sort_clean := {
      compare_zero := modifyClean.sort_compare_zero
      scratch_zero := modifyClean.sort_scratch_zero
      history_zero := modifyClean.sort_history_zero } }

/--
column event compute正本は、membership・candidate準備/更新・sort各公開componentの
`runBasis_correct`を逐次合成したpure状態記録の末尾に一致する。
-/
theorem computeColumnEventCandidateUpdateAndSortCircuit_eq_analyticStates
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnEventCandidateUpdateAndSortCleanInput p slot offset input) :
    (computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output := by
  let states := ColumnEventCandidateUpdateAndSortStateSpec p slot offset input
  have selectorEq :
      (columnEventSelectorCompute p slot offset).runBasis
          reversibleGatePermutation input = states.afterSelector := by
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      selectorEqualsConstantAnalyticAction, columnEventSelectorMatches,
      diagonalSelectorMatches] using
      runBasis_columnEventSelectorCompute p slot offset input
        clean.selector_scratch
  have movedEq :
      (columnEventMovedCopy p slot).runBasis reversibleGatePermutation
          states.afterSelector = states.afterMovedCopy := by
    exact runBasis_columnEventMovedCopy_eq_controlledCopyReference p slot
      states.afterSelector
  have moveEq :
      (columnEventMoveForward p offset).runBasis reversibleGatePermutation
          states.afterMovedCopy = states.afterMove := by
    exact (compiledIncrementWordMod2PowInPlaceBridgeCleanComponent (columnEventCoordinate p offset)
      (decoderAndScratchWires p)
      (columnEventMoveLayout_canonical p slot offset).enough_scratch
      (columnEventMoveLayout_canonical p slot offset).coordinate_scratch_nodup
      ).runBasis_correct states.afterMovedCopy clean.move_scratch
  have membershipEq :
      (columnEventMembership p slot).runBasis reversibleGatePermutation
          states.afterMove = states.afterMembership := by
    exact (compiledXorMembershipMatchGoodAndAbsentFlagsBridgeCleanComponent p (columnKeyWires p)
      (columnKeyWires_membershipInputLayout p) slot true).runBasis_correct
        states.afterMove clean.membership_clean
  have branchEq :
      (columnEventBranchCompute p slot offset).runBasis
          reversibleGatePermutation states.afterMembership = states.afterBranch := by
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      positiveControlAnalyticAction] using
      runBasis_columnEventBranchCompute_canonical p slot offset
        states.afterMembership clean.branch_scratch
  have candidatesEq :
      (xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
          reversibleGatePermutation states.afterBranch = states.afterCandidates := by
    have result := (verifiedXorConfigurationIntoCandidateRegisterCleanComponent p (columnKeyWires p)
      (columnKeyWires_candidateInputLayout p)).runBasis_correct
        states.afterBranch trivial
    change (xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
      reversibleGatePermutation states.afterBranch =
        ConfigurationToCandidateRegisterXorSpec p (columnKeyWires p) states.afterBranch at result
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedXorConfigurationIntoCandidateRegisterCleanComponent] using result
  have modifyEq :
      (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
          states.afterCandidates = states.afterModify := by
    have result := (verifiedControlledUpdateSelectedColumnCandidateWordCleanComponent p slot offset).runBasis_correct
      states.afterCandidates trivial
    change (controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
      states.afterCandidates =
        ControlledSelectedColumnCandidateWordUpdateSpec p slot offset states.afterCandidates at result
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedControlledUpdateSelectedColumnCandidateWordCleanComponent] using result
  have sortEq :
      (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
          states.afterModify = states.output := by
    have result := (verifiedReversibleCandidateSortWithHistoryRestorationCleanComponent p).runBasis_correct
      states.afterModify clean.sort_clean
    change (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
      states.afterModify =
        CanonicalCandidateSortWithHistoryRestorationSpec p (qTypedBitonicSchedule p) states.afterModify at result
    simpa [states, ColumnEventCandidateUpdateAndSortStateSpec, columnEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedReversibleCandidateSortWithHistoryRestorationCleanComponent] using result
  change
    (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
      ((controlledUpdateSelectedColumnCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
        ((xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
          reversibleGatePermutation
          ((columnEventBranchCompute p slot offset).runBasis
            reversibleGatePermutation
            ((columnEventMembership p slot).runBasis reversibleGatePermutation
              ((columnEventMoveForward p offset).runBasis
                reversibleGatePermutation
                ((columnEventMovedCopy p slot).runBasis
                  reversibleGatePermutation
                  ((columnEventSelectorCompute p slot offset).runBasis
                    reversibleGatePermutation input))))))) = states.output
  rw [selectorEq]
  rw [movedEq, moveEq, membershipEq, branchEq, candidatesEq, modifyEq, sortEq]

/-- column event computeを子componentのpure参照合成へ束ねた第2版clean component。 -/
def compiledColumnEventCandidateUpdateAndSortCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := computeColumnEventCandidateUpdateAndSortCircuit p slot offset
  reference := fun input => (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output
  inputCondition := ColumnEventCandidateUpdateAndSortCleanInput p slot offset
  outputCondition := fun _ => True
  restoration := fun _ _ => True
  runBasis_correct := computeColumnEventCandidateUpdateAndSortCircuit_eq_analyticStates p slot offset
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- column event useをsorted writerとselector writerの二子部品から合成する。 -/
noncomputable def verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent
    (p : QParameters) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  CleanComponent.seq
    (verifiedXorSortedCandidatesAsDelimiterIntoOutputCleanComponent p .rowOutput
      (columnEventDegreeChange offset))
    (verifiedXorMovedMemberPositionIntoSelectorOutputCleanComponent p offset.val (selectorOutputWires p)
      (MovedMemberPositionSelectorOutputLayout_selectorOutput_canonical p))

/-- column eventのdelimiter出力とselector出力を順にXORする解析作用。 -/
noncomputable def ColumnEventDelimiterAndSelectorOutputsXorSpec
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let afterDelimiter := SortedCandidatesDelimiterOutputXorSpec p
    (rowOutputWires p) (by simp [rowOutputWires]) (activeWire p)
    (columnEventDegreeChange offset) input
  uniqueSpecificationReference
    (fun source output => MovedMemberPositionSelectorOutputXorSpec p offset.val
      (selectorOutputWires p) source output) afterDelimiter

/-- column event use componentのreferenceは二つのwriter解析作用の合成である。 -/
theorem verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent_reference
    (p : QParameters) (offset : Fin 6) :
    (verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference =
      ColumnEventDelimiterAndSelectorOutputsXorSpec p offset := by
  rfl

/-- 第2版column event親部品の自然なclean入力。 -/
def ColumnEventPhysicalComputeUseUncomputeInput (p : QParameters) (slot : Fin p.K)
    (offset : Fin 6) (input : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  (compiledColumnEventCandidateUpdateAndSortCleanComponent p slot offset).inputCondition input ∧
    (verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).inputCondition
      ((compiledColumnEventCandidateUpdateAndSortCleanComponent p slot offset).reference input)

/-- 二つのwriter子部品の復元契約から、column compute supportが保存される。 -/
theorem columnEventDelimiterAndSelectorOutputs_preserveComputeSupport
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : (verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).inputCondition input) :
    BasisAgreeOn (columnEventCandidateUpdateAndSortSupport p)
      ((verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference input) input := by
  let sortedComponent := verifiedXorSortedCandidatesAsDelimiterIntoOutputCleanComponent p .rowOutput
    (columnEventDegreeChange offset)
  let selectorComponent := verifiedXorMovedMemberPositionIntoSelectorOutputCleanComponent p offset.val
    (selectorOutputWires p)
    (MovedMemberPositionSelectorOutputLayout_selectorOutput_canonical p)
  have selectorRestoration := selectorComponent.restoration_correct
    (sortedComponent.reference input) clean.2
  intro wire supportMember
  have outsideSelector : wire ∉ selectorOutputWires p := fun selectorMember =>
    (List.disjoint_left.mp (columnEventCandidateUpdateAndSortSupport_disjoint_selectorOutput p))
      supportMember selectorMember
  have outsideOutput : wire ∉ rowOutputWires p := fun outputMember =>
    (List.disjoint_left.mp (columnEventCandidateUpdateAndSortSupport_disjoint_rowOutput p))
      supportMember outputMember
  have outsideActive : wire ≠ activeWire p := fun equal =>
    activeWire_not_mem_columnEventCandidateUpdateAndSortSupport p (equal ▸ supportMember)
  change selectorComponent.reference (sortedComponent.reference input) wire = input wire
  rw [selectorRestoration.outside_restored wire outsideSelector]
  exact xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_rowOutput p
    (columnEventDegreeChange offset) input wire outsideOutput outsideActive

/--
column event branchの第2版親component。runBasis証明はcompute/use子componentの公開fieldと
一般の局所compute--use--uncompute定理だけを使う。
-/
noncomputable def compiledColumnEventResultComputeUseUncomputeCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := applyColumnEventReferenceAndRestoreWorkCircuit p slot offset
  reference := fun input => restoreSupport (columnEventCandidateUpdateAndSortSupport p) input
    ((verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference
      ((compiledColumnEventCandidateUpdateAndSortCleanComponent p slot offset).reference input))
  inputCondition := ColumnEventPhysicalComputeUseUncomputeInput p slot offset
  outputCondition := fun _ => True
  restoration := fun input output => output = restoreSupport
    (columnEventCandidateUpdateAndSortSupport p) input
    ((verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference
      ((compiledColumnEventCandidateUpdateAndSortCleanComponent p slot offset).reference input))
  runBasis_correct := by
    intro input clean
    rw [applyColumnEventReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
    have computeEq := (compiledColumnEventCandidateUpdateAndSortCleanComponent p slot offset).runBasis_correct
      input clean.1
    change (computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output at computeEq
    have useEq := (verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).runBasis_correct
      ((compiledColumnEventCandidateUpdateAndSortCleanComponent p slot offset).reference input) clean.2
    change (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
      ((ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output) =
        (verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference
          ((ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output) at useEq
    have preserveActual : BasisAgreeOn (columnEventCandidateUpdateAndSortSupport p)
        ((xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
          ((computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis
            reversibleGatePermutation input))
        ((computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis
          reversibleGatePermutation input) := by
      rw [computeEq, useEq]
      exact columnEventDelimiterAndSelectorOutputs_preserveComputeSupport p offset _ clean.2
    calc
      (Circuit.computeUseUncompute id (computeColumnEventCandidateUpdateAndSortCircuit p slot offset)
          (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset)).runBasis reversibleGatePermutation input =
        restoreSupport (columnEventCandidateUpdateAndSortSupport p) input
          ((xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
            ((computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis
              reversibleGatePermutation input)) :=
        Circuit.computeUseUncompute_local_clean (columnEventCandidateUpdateAndSortSupport p)
          (computeColumnEventCandidateUpdateAndSortCircuit p slot offset) (xorColumnEventDelimiterAndSelectorIntoOutputsCircuit p offset) input
          (computeColumnEventCandidateUpdateAndSortCircuit_usesOnly p slot offset) preserveActual
      _ = _ := by
        rw [computeEq, useEq]
        rfl
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- row event computeを構成する八つのpure参照作用の状態記録。 -/
/- row event computeへ代入する八つのpure子参照関数。 -/
def rowEventPrimitiveReferences (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6) :
    OracleAnalytic.EventPrimitiveReferences
      (JointBasis p.ancillaWidth p.systemWidth) where
  selector := selectorEqualsConstantAnalyticAction (rowSelectorWires p)
    (6 * slot.val + offset.val) (oracleSelectedWire p)
  moved := controlledCopyBasisReference true
    (registerWordAt p (systemWires p) slot) (oracleMovedWires p)
  move := decrementWordBorrowSequenceReference [] (columnEventCoordinate p offset)
  membership := MembershipMatchGoodAndAbsentFlagsXorSpec p (systemWires p) slot false
  branch := positiveControlAnalyticAction (rowEventBranchControls p slot offset)
    (oracleBranchWire p)
  candidates := ConfigurationToCandidateRegisterXorSpec p (systemWires p)
  modify := ControlledSelectedRowCandidateWordUpdateSpec p slot offset
  sort := CanonicalCandidateSortWithHistoryRestorationSpec p (qTypedBitonicSchedule p)

/-- row event computeの八段階をpure子参照関数から組み立てる。 -/
def RowEventPredecessorCandidateUpdateAndSortStateSpec (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    EventComputeAnalyticStates
      (JointBasis p.ancillaWidth p.systemWidth) :=
  OracleAnalytic.eventStates (rowEventPrimitiveReferences p slot offset) input

/-- row event computeの各子部品を適用できるpureな段階別clean条件。 -/
structure RowEventPredecessorCandidateUpdateAndSortCleanInput (p : QParameters)
    (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- selector比較用scratchは0である。 -/
  selector_scratch : ∀ wire ∈ decoderAndScratchWires p, input wire = false
  /-- decrement開始時のscratchは0である。 -/
  move_scratch : ∀ wire ∈ decoderAndScratchWires p,
    (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).afterMovedCopy wire = false
  /-- membership部品の入力workはcleanである。 -/
  membership_clean : MembershipWorkRestored p
    (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).afterMove
  /-- branch AND開始時のscratchは0である。 -/
  branch_scratch : ∀ wire ∈ decoderAndScratchWires p,
    (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).afterMembership wire = false
  /-- row candidate更新部品の入力workはcleanである。 -/
  update_clean : EventSortCleanInput p
    (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).afterCandidates
  /-- sort部品の入力workはcleanである。 -/
  sort_clean : BitonicSortCleanInput p
    (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).afterModify

/-- 通常のevent-sort clean条件からrow event子component列の段階別clean条件を導く。 -/
theorem RowEventPredecessorCandidateUpdateAndSortCleanInput.ofEventSortClean
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    RowEventPredecessorCandidateUpdateAndSortCleanInput p slot offset input := by
  let states := RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input
  have selectorEq :
      (rowEventSelectorCompute p slot offset).runBasis reversibleGatePermutation input =
        states.afterSelector := by
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      selectorEqualsConstantAnalyticAction, rowEventSelectorMatches,
      diagonalSelectorMatches] using
      runBasis_rowEventSelectorCompute p slot offset input
        clean.moved_selector.scratch_zero
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [← selectorEq]
    exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input clean
  have movedEq :
      (rowEventMovedCopy p slot).runBasis reversibleGatePermutation
          states.afterSelector = states.afterMovedCopy := by
    exact runBasis_rowEventMovedCopy_eq_controlledCopyReference p slot
      states.afterSelector
  have movedClean : EventSortCleanInput p states.afterMovedCopy := by
    rw [← movedEq]
    exact EventSortCleanInput.of_rowEventMovedCopy p slot _ selectorClean
  have moveEq :
      (rowEventMoveBackward p offset).runBasis reversibleGatePermutation
          states.afterMovedCopy = states.afterMove := by
    have result := (compiledDecrementWordMod2PowInPlaceBridgeCleanComponent (columnEventCoordinate p offset)
      (decoderAndScratchWires p)
      (columnEventMoveLayout_canonical p slot offset).enough_scratch
      (columnEventMoveLayout_canonical p slot offset).coordinate_scratch_nodup
      ).runBasis_correct states.afterMovedCopy
        movedClean.moved_selector.scratch_zero
    change (decrementWordMod2PowInPlaceCircuit (columnEventCoordinate p offset)
      (decoderAndScratchWires p)).runBasis reversibleGatePermutation
        states.afterMovedCopy = decrementWordBorrowSequenceReference []
          (columnEventCoordinate p offset) states.afterMovedCopy at result
    simpa [rowEventMoveBackward, columnEventCoordinate, states,
      RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates] using result
  have moveClean : EventSortCleanInput p states.afterMove := by
    rw [← moveEq]
    exact EventSortCleanInput.of_rowEventMoveBackward p offset _ movedClean
  have membershipInput : MembershipWorkRestored p states.afterMove := {
    equalWork_zero := moveClean.moved_selector.compare_zero
    scratch_zero := moveClean.moved_selector.scratch_zero }
  have membershipEq :
      (rowEventMembership p slot).runBasis reversibleGatePermutation
          states.afterMove = states.afterMembership :=
    (compiledXorMembershipMatchGoodAndAbsentFlagsBridgeCleanComponent p (systemWires p)
      (systemWires_membershipInputLayout p) slot false).runBasis_correct
        states.afterMove membershipInput
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    rw [← membershipEq]
    exact EventSortCleanInput.of_rowEventMembership p slot _ moveClean
  have branchEq :
      (rowEventBranchCompute p slot offset).runBasis reversibleGatePermutation
          states.afterMembership = states.afterBranch := by
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      positiveControlAnalyticAction] using
      runBasis_rowEventBranchCompute_canonical p slot offset
        states.afterMembership membershipClean.moved_selector.scratch_zero
  have branchClean : EventSortCleanInput p states.afterBranch := by
    rw [← branchEq]
    exact EventSortCleanInput.of_rowEventBranchCompute p slot offset _ membershipClean
  have candidatesEq :
      (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
          reversibleGatePermutation states.afterBranch = states.afterCandidates := by
    have result := (verifiedXorConfigurationIntoCandidateRegisterCleanComponent p (systemWires p)
      (systemWires_candidateInputLayout p)).runBasis_correct states.afterBranch trivial
    change (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
      reversibleGatePermutation states.afterBranch =
        ConfigurationToCandidateRegisterXorSpec p (systemWires p) states.afterBranch at result
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedXorConfigurationIntoCandidateRegisterCleanComponent] using result
  have candidatesClean : EventSortCleanInput p states.afterCandidates := by
    rw [← candidatesEq]
    exact EventSortCleanInput.of_xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)
      (systemWires_candidateInputLayout p) _ branchClean
  have modifyEq :
      (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
          states.afterCandidates = states.afterModify := by
    have result := (verifiedControlledUpdateSelectedRowCandidateWordCleanComponent p slot offset).runBasis_correct
      states.afterCandidates candidatesClean
    change (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
      states.afterCandidates = ControlledSelectedRowCandidateWordUpdateSpec p slot offset
        states.afterCandidates at result
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedControlledUpdateSelectedRowCandidateWordCleanComponent] using result
  have modifyClean : EventSortCleanInput p states.afterModify := by
    rw [← modifyEq]
    exact EventSortCleanInput.of_rowEventModify p slot offset _ candidatesClean
  exact {
    selector_scratch := clean.moved_selector.scratch_zero
    move_scratch := movedClean.moved_selector.scratch_zero
    membership_clean := membershipInput
    branch_scratch := membershipClean.moved_selector.scratch_zero
    update_clean := candidatesClean
    sort_clean := {
      compare_zero := modifyClean.sort_compare_zero
      scratch_zero := modifyClean.sort_scratch_zero
      history_zero := modifyClean.sort_history_zero } }

/--
row event compute正本は、membership・candidate準備/更新・sort各公開componentの
`runBasis_correct`を逐次合成したpure状態記録の末尾に一致する。
-/
theorem computeRowEventPredecessorCandidateUpdateAndSortCircuit_eq_analyticStates
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowEventPredecessorCandidateUpdateAndSortCleanInput p slot offset input) :
    (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output := by
  let states := RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input
  have selectorEq :
      (rowEventSelectorCompute p slot offset).runBasis
          reversibleGatePermutation input = states.afterSelector := by
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      selectorEqualsConstantAnalyticAction, rowEventSelectorMatches,
      diagonalSelectorMatches] using
      runBasis_rowEventSelectorCompute p slot offset input clean.selector_scratch
  have movedEq :
      (rowEventMovedCopy p slot).runBasis reversibleGatePermutation
          states.afterSelector = states.afterMovedCopy := by
    exact runBasis_rowEventMovedCopy_eq_controlledCopyReference p slot
      states.afterSelector
  have moveEq :
      (rowEventMoveBackward p offset).runBasis reversibleGatePermutation
          states.afterMovedCopy = states.afterMove := by
    have result := (compiledDecrementWordMod2PowInPlaceBridgeCleanComponent (columnEventCoordinate p offset)
      (decoderAndScratchWires p)
      (columnEventMoveLayout_canonical p slot offset).enough_scratch
      (columnEventMoveLayout_canonical p slot offset).coordinate_scratch_nodup
      ).runBasis_correct states.afterMovedCopy clean.move_scratch
    change (decrementWordMod2PowInPlaceCircuit (columnEventCoordinate p offset)
      (decoderAndScratchWires p)).runBasis reversibleGatePermutation
        states.afterMovedCopy = decrementWordBorrowSequenceReference []
          (columnEventCoordinate p offset) states.afterMovedCopy at result
    simpa [rowEventMoveBackward, columnEventCoordinate, states,
      RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates] using result
  have membershipEq :
      (rowEventMembership p slot).runBasis reversibleGatePermutation
          states.afterMove = states.afterMembership := by
    exact (compiledXorMembershipMatchGoodAndAbsentFlagsBridgeCleanComponent p (systemWires p)
      (systemWires_membershipInputLayout p) slot false).runBasis_correct
        states.afterMove clean.membership_clean
  have branchEq :
      (rowEventBranchCompute p slot offset).runBasis reversibleGatePermutation
          states.afterMembership = states.afterBranch := by
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      positiveControlAnalyticAction] using
      runBasis_rowEventBranchCompute_canonical p slot offset
        states.afterMembership clean.branch_scratch
  have candidatesEq :
      (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
          reversibleGatePermutation states.afterBranch = states.afterCandidates := by
    have result := (verifiedXorConfigurationIntoCandidateRegisterCleanComponent p (systemWires p)
      (systemWires_candidateInputLayout p)).runBasis_correct
        states.afterBranch trivial
    change (xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
      reversibleGatePermutation states.afterBranch =
        ConfigurationToCandidateRegisterXorSpec p (systemWires p) states.afterBranch at result
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedXorConfigurationIntoCandidateRegisterCleanComponent] using result
  have modifyEq :
      (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
          states.afterCandidates = states.afterModify := by
    have result := (verifiedControlledUpdateSelectedRowCandidateWordCleanComponent p slot offset).runBasis_correct
      states.afterCandidates clean.update_clean
    change (controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
      states.afterCandidates =
        ControlledSelectedRowCandidateWordUpdateSpec p slot offset states.afterCandidates at result
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedControlledUpdateSelectedRowCandidateWordCleanComponent] using result
  have sortEq :
      (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
          states.afterModify = states.output := by
    have result := (verifiedReversibleCandidateSortWithHistoryRestorationCleanComponent p).runBasis_correct
      states.afterModify clean.sort_clean
    change (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
      states.afterModify =
        CanonicalCandidateSortWithHistoryRestorationSpec p (qTypedBitonicSchedule p) states.afterModify at result
    simpa [states, RowEventPredecessorCandidateUpdateAndSortStateSpec, rowEventPrimitiveReferences,
      OracleAnalytic.eventStates, buildEventComputeAnalyticStates,
      verifiedReversibleCandidateSortWithHistoryRestorationCleanComponent] using result
  change
    (reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis reversibleGatePermutation
      ((controlledUpdateSelectedRowCandidateWordCircuit p slot offset).runBasis reversibleGatePermutation
        ((xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
          reversibleGatePermutation
          ((rowEventBranchCompute p slot offset).runBasis reversibleGatePermutation
            ((rowEventMembership p slot).runBasis reversibleGatePermutation
              ((rowEventMoveBackward p offset).runBasis reversibleGatePermutation
                ((rowEventMovedCopy p slot).runBasis reversibleGatePermutation
                  ((rowEventSelectorCompute p slot offset).runBasis
                    reversibleGatePermutation input))))))) = states.output
  rw [selectorEq, movedEq, moveEq, membershipEq, branchEq, candidatesEq,
    modifyEq, sortEq]

/-- row event computeを子componentのpure参照合成へ束ねた第2版clean component。 -/
def compiledRowEventPredecessorCandidateUpdateAndSortCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset
  reference := fun input => (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output
  inputCondition := RowEventPredecessorCandidateUpdateAndSortCleanInput p slot offset
  outputCondition := fun _ => True
  restoration := fun _ _ => True
  runBasis_correct := computeRowEventPredecessorCandidateUpdateAndSortCircuit_eq_analyticStates p slot offset
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- row event useをsorted writerとselector writerの二子部品から合成する。 -/
noncomputable def verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent
    (p : QParameters) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  CleanComponent.seq
    (verifiedXorSortedCandidatesAsDelimiterIntoOutputCleanComponent p .columnKey (rowEventDegreeChange offset))
    (verifiedXorMovedMemberPositionIntoSelectorOutputCleanComponent p offset.val (columnSelectorWires p)
      (MovedMemberPositionSelectorOutputLayout_columnSelector_canonical p))

/-- row eventのpredecessor delimiterとselector出力を順にXORする解析作用。 -/
noncomputable def RowEventPredecessorDelimiterAndSelectorOutputsXorSpec
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let afterDelimiter := SortedCandidatesDelimiterOutputXorSpec p
    (columnKeyWires p) (by simp [columnKeyWires]) (keySignalWire p)
    (rowEventDegreeChange offset) input
  uniqueSpecificationReference
    (fun source output => MovedMemberPositionSelectorOutputXorSpec p offset.val
      (columnSelectorWires p) source output) afterDelimiter

/-- row event use componentのreferenceは二つのwriter解析作用の合成である。 -/
theorem verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent_reference
    (p : QParameters) (offset : Fin 6) :
    (verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference =
      RowEventPredecessorDelimiterAndSelectorOutputsXorSpec p offset := by
  rfl

/-- 第2版row event親部品の自然なclean入力。 -/
def RowEventPhysicalComputeUseUncomputeInput (p : QParameters) (slot : Fin p.K)
    (offset : Fin 6) (input : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  (compiledRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).inputCondition input ∧
    (verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).inputCondition
      ((compiledRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).reference input)

/-- 二つのwriter子部品の復元契約から、row compute supportが保存される。 -/
theorem rowEventPredecessorDelimiterAndSelectorOutputs_preserveComputeSupport
    (p : QParameters) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : (verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).inputCondition input) :
    BasisAgreeOn (rowEventPredecessorCandidateUpdateAndSortSupport p)
      ((verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference input) input := by
  let sortedComponent := verifiedXorSortedCandidatesAsDelimiterIntoOutputCleanComponent p .columnKey
    (rowEventDegreeChange offset)
  let selectorComponent := verifiedXorMovedMemberPositionIntoSelectorOutputCleanComponent p offset.val
    (columnSelectorWires p)
    (MovedMemberPositionSelectorOutputLayout_columnSelector_canonical p)
  have selectorRestoration := selectorComponent.restoration_correct
    (sortedComponent.reference input) clean.2
  intro wire supportMember
  have broadMember : wire ∈ rowEventBroadSupport p := by
    rw [← rowEventPredecessorCandidateUpdateAndSortSupport_eq_broadSupport p]
    exact supportMember
  have outsideSelector : wire ∉ columnSelectorWires p := fun selectorMember =>
    (List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnSelector p))
      broadMember selectorMember
  have outsideKey : wire ∉ columnKeyWires p := fun keyMember =>
    (List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnKey p))
      broadMember keyMember
  have outsideSignal : wire ≠ keySignalWire p := fun equal =>
    keySignalWire_not_mem_rowEventBroadSupport p (equal ▸ broadMember)
  change selectorComponent.reference (sortedComponent.reference input) wire = input wire
  rw [selectorRestoration.outside_restored wire outsideSelector]
  exact xorSortedCandidatesAsDelimiterIntoOutputCircuitReference_outside_columnKey p
    (rowEventDegreeChange offset) input wire outsideKey outsideSignal

/--
row event branchの第2版親component。runBasis証明はcompute/use子componentの公開fieldと
一般の局所compute--use--uncompute定理だけを使う。
-/
noncomputable def compiledRowEventResultComputeUseUncomputeCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := applyRowEventReferenceAndRestoreWorkCircuit p slot offset
  reference := fun input => restoreSupport (rowEventPredecessorCandidateUpdateAndSortSupport p) input
    ((verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference
      ((compiledRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).reference input))
  inputCondition := RowEventPhysicalComputeUseUncomputeInput p slot offset
  outputCondition := fun _ => True
  restoration := fun input output => output = restoreSupport
    (rowEventPredecessorCandidateUpdateAndSortSupport p) input
    ((verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference
      ((compiledRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).reference input))
  runBasis_correct := by
    intro input clean
    rw [applyRowEventReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]
    have computeEq := (compiledRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).runBasis_correct
      input clean.1
    change (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output at computeEq
    have useEq := (verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).runBasis_correct
      ((compiledRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).reference input) clean.2
    change (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
      ((RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output) =
        (verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference
          ((RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output) at useEq
    have preserveActual : BasisAgreeOn (rowEventPredecessorCandidateUpdateAndSortSupport p)
        ((xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
          ((computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input))
        ((computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input) := by
      rw [computeEq, useEq]
      exact rowEventPredecessorDelimiterAndSelectorOutputs_preserveComputeSupport p offset _ clean.2
    calc
      (Circuit.computeUseUncompute id (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset)
          (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset)).runBasis reversibleGatePermutation input =
        restoreSupport (rowEventPredecessorCandidateUpdateAndSortSupport p) input
          ((xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset).runBasis reversibleGatePermutation
            ((computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis
              reversibleGatePermutation input)) :=
        Circuit.computeUseUncompute_local_clean (rowEventPredecessorCandidateUpdateAndSortSupport p)
          (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset) (xorRowEventPredecessorDelimiterAndSelectorIntoOutputsCircuit p offset) input
          (computeRowEventPredecessorCandidateUpdateAndSortCircuit_usesOnly p slot offset) preserveActual
      _ = _ := by
        rw [computeEq, useEq]
        rfl
  outputCondition_correct := by simp
  restoration_correct := by simp

/-! ## event branch の最終解析仕様への橋 -/

/-- column event の子component合成が与える低水準のpure参照作用。 -/
noncomputable def ColumnEventComputeUseUncomputeReference (p : QParameters) (slot : Fin p.K)
    (offset : Fin 6) (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  restoreSupport (columnEventCandidateUpdateAndSortSupport p) input
    ((verifiedXorColumnEventDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference
      ((compiledColumnEventCandidateUpdateAndSortCleanComponent p slot offset).reference input))

/-- row event の子component合成が与える低水準のpure参照作用。 -/
noncomputable def RowEventComputeUseUncomputeReference (p : QParameters) (slot : Fin p.K)
    (offset : Fin 6) (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  restoreSupport (rowEventPredecessorCandidateUpdateAndSortSupport p) input
    ((verifiedXorRowEventPredecessorDelimiterAndSelectorIntoOutputsCleanComponent p offset).reference
      ((compiledRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).reference input))

/--
column event の子合成参照は、回路実行をstatementに含まない最終Q解析仕様を満たす。
既存のwire-level証拠はこのcanonical子component内部の橋にだけ隔離する。
-/
theorem identifyColumnEventImplementationWithRestoredReference
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnEventPhysicalComputeUseUncomputeInput p slot offset input) :
    ColumnEventRestoredReferenceIdentification p offset input
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output
      (ColumnEventComputeUseUncomputeReference p slot offset input) := by
  have computeEq :=
    (compiledColumnEventCandidateUpdateAndSortCleanComponent p slot offset).runBasis_correct input clean.1
  change (computeColumnEventCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
    (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output at computeEq
  have computedEq :
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output =
        (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output :=
    (columnEventCandidateUpdateAndSortExecutionTrace_output p slot offset input).trans computeEq
  have scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false := by
    intro wire member
    rw [computedEq]
    exact clean.2.1.scratch_zero wire member
  have pairZero : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false := by
    rw [computedEq]
    exact clean.2.1.pair_zero
  have movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (rowOutputWires p)
        (by simp [rowOutputWires]) (activeWire p)
        (columnEventDegreeChange offset)
        (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output) := by
    rw [computedEq]
    exact clean.2.2
  have actualSpec := verifiedColumnEventRestoredReferenceIdentification p slot offset input
    scratchZero pairZero movedClean
  have actualEq :=
    (compiledColumnEventResultComputeUseUncomputeCleanComponent p slot offset).runBasis_correct input clean
  change (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
    reversibleGatePermutation input = ColumnEventComputeUseUncomputeReference p slot offset input
    at actualEq
  rw [actualEq, computedEq] at actualSpec
  exact actualSpec

/--
row event の子合成参照は、回路実行をstatementに含まない最終Q解析仕様を満たす。
既存のwire-level証拠はこのcanonical子component内部の橋にだけ隔離する。
-/
theorem identifyRowEventImplementationWithRestoredReference
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowEventPhysicalComputeUseUncomputeInput p slot offset input) :
    RowEventRestoredReferenceIdentification p offset input
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output
      (RowEventComputeUseUncomputeReference p slot offset input) := by
  have computeEq :=
    (compiledRowEventPredecessorCandidateUpdateAndSortCleanComponent p slot offset).runBasis_correct input clean.1
  change (computeRowEventPredecessorCandidateUpdateAndSortCircuit p slot offset).runBasis reversibleGatePermutation input =
    (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output at computeEq
  have computedEq :
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output =
        (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output :=
    (rowEventPredecessorCandidateUpdateAndSortExecutionTrace_output p slot offset input).trans computeEq
  have scratchZero : ∀ wire ∈ decoderAndScratchWires p,
      (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output wire = false := by
    intro wire member
    rw [computedEq]
    exact clean.2.1.scratch_zero wire member
  have pairZero : (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output
      (oraclePairWire p) = false := by
    rw [computedEq]
    exact clean.2.1.pair_zero
  have movedClean : WriteMovedSelectorSlotClean p
      (SortedCandidatesDelimiterOutputXorSpec p (columnKeyWires p)
        (by simp [columnKeyWires]) (keySignalWire p)
        (if offset.val % 2 = 1 then 1 else 0)
        (rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input).output) := by
    rw [computedEq]
    exact clean.2.2
  have actualSpec := verifiedRowEventRestoredReferenceIdentification p slot offset input
    scratchZero pairZero movedClean
  have actualEq :=
    (compiledRowEventResultComputeUseUncomputeCleanComponent p slot offset).runBasis_correct input clean
  change (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
    reversibleGatePermutation input = RowEventComputeUseUncomputeReference p slot offset input
    at actualEq
  rw [actualEq, computedEq] at actualSpec
  exact actualSpec

/-- 最終Q解析仕様をreferenceに持つcolumn event公開親component。 -/
private noncomputable def compiledColumnEventPhysicalReferenceBridgeCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := applyColumnEventReferenceAndRestoreWorkCircuit p slot offset
  reference := uniqueSpecificationReference fun input output =>
    ColumnEventRestoredReferenceIdentification p offset input
      (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output output
  inputCondition := ColumnEventPhysicalComputeUseUncomputeInput p slot offset
  outputCondition := fun _ => True
  restoration := fun input output => ColumnEventRestoredReferenceIdentification p offset input
    (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output output
  runBasis_correct := by
    intro input clean
    have actualEq :=
      (compiledColumnEventResultComputeUseUncomputeCleanComponent p slot offset).runBasis_correct input clean
    change (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis reversibleGatePermutation input =
      ColumnEventComputeUseUncomputeReference p slot offset input at actualEq
    have composedSpec := identifyColumnEventImplementationWithRestoredReference p slot offset input clean
    have uniqueOutput : ∃! output, ColumnEventRestoredReferenceIdentification p offset input
        (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output output :=
      ⟨ColumnEventComputeUseUncomputeReference p slot offset input, composedSpec,
        fun other otherSpec => otherSpec.unique composedSpec⟩
    exact actualEq.trans
      (composedSpec.unique (uniqueSpecificationReference_spec uniqueOutput))
  outputCondition_correct := by simp
  restoration_correct := by
    intro input clean
    have composedSpec := identifyColumnEventImplementationWithRestoredReference p slot offset input clean
    have uniqueOutput : ∃! output, ColumnEventRestoredReferenceIdentification p offset input
        (ColumnEventCandidateUpdateAndSortStateSpec p slot offset input).output output :=
      ⟨ColumnEventComputeUseUncomputeReference p slot offset input, composedSpec,
        fun other otherSpec => otherSpec.unique composedSpec⟩
    exact uniqueSpecificationReference_spec uniqueOutput

/-- 最終Q解析仕様をreferenceに持つrow event公開親component。 -/
private noncomputable def compiledRowEventPhysicalReferenceBridgeCleanComponent
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := applyRowEventReferenceAndRestoreWorkCircuit p slot offset
  reference := uniqueSpecificationReference fun input output =>
    RowEventRestoredReferenceIdentification p offset input
      (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output output
  inputCondition := RowEventPhysicalComputeUseUncomputeInput p slot offset
  outputCondition := fun _ => True
  restoration := fun input output => RowEventRestoredReferenceIdentification p offset input
    (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output output
  runBasis_correct := by
    intro input clean
    have actualEq :=
      (compiledRowEventResultComputeUseUncomputeCleanComponent p slot offset).runBasis_correct input clean
    change (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis reversibleGatePermutation input =
      RowEventComputeUseUncomputeReference p slot offset input at actualEq
    have composedSpec := identifyRowEventImplementationWithRestoredReference p slot offset input clean
    have uniqueOutput : ∃! output, RowEventRestoredReferenceIdentification p offset input
        (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output output :=
      ⟨RowEventComputeUseUncomputeReference p slot offset input, composedSpec,
        fun other otherSpec => otherSpec.unique composedSpec⟩
    exact actualEq.trans
      (composedSpec.unique (uniqueSpecificationReference_spec uniqueOutput))
  outputCondition_correct := by simp
  restoration_correct := by
    intro input clean
    have composedSpec := identifyRowEventImplementationWithRestoredReference p slot offset input clean
    have uniqueOutput : ∃! output, RowEventRestoredReferenceIdentification p offset input
        (RowEventPredecessorCandidateUpdateAndSortStateSpec p slot offset input).output output :=
      ⟨RowEventComputeUseUncomputeReference p slot offset input, composedSpec,
        fun other otherSpec => otherSpec.unique composedSpec⟩
    exact uniqueSpecificationReference_spec uniqueOutput

/-- 解析仕様側のregister bit列は既存のdelimiter読出しと定義的に一致する。 -/
@[simp] theorem analyticRegisterBits_eq_registerBitList
    {width : Nat} (basis : RegisterBasis width) :
    analyticRegisterBits basis = registerBitList basis := rfl

/-- 解析仕様側のbitwise XORは既存の外部accumulator仕様と一致する。 -/
theorem analyticXorBits_eq_reference (source target : List Bool) :
    analyticXorBits source target =
      List.zipWith
        (fun sourceBit targetBit => if sourceBit then !targetBit else targetBit)
        source target := by
  induction source generalizing target with
  | nil => cases target <;> rfl
  | cons bit source inductionHypothesis =>
      cases target with
      | nil => rfl
      | cons targetBit target =>
          simp only [analyticXorBits, List.zipWith]
          congr 1
          · cases bit <;> cases targetBit <;> rfl
          · exact inductionHypothesis target

/-- 解析仕様側の定数XORは既存のlittle-endian accumulator仕様と一致する。 -/
theorem analyticXorConstantAux_eq_reference
    (constant start : Nat) (bits : List Bool) :
    analyticXorConstantAux constant start bits =
      controlledXorConstantBits true constant start bits := by
  induction bits generalizing start with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      cases test : constant.testBit start <;> cases bit <;>
        simp [analyticXorConstantAux, controlledXorConstantBits, test,
          inductionHypothesis]

/-- 下位bitから始める解析的定数XORの既存参照関数との一致。 -/
theorem analyticXorConstant_eq_reference
    (constant : Nat) (bits : List Bool) :
    analyticXorConstant constant bits =
      controlledXorConstantBits true constant 0 bits := by
  exact analyticXorConstantAux_eq_reference constant 0 bits

/-- 物理基底からcolumn oracleの外部四registerだけを観測する。 -/
def observeColumnOracle (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) :
    ColumnOracleObservation where
  rowOutput := readWires (rowOutputWires p) basis
  selectorOutput := readWires (selectorOutputWires p) basis
  negative := basis (negativeWire p)
  active := basis (activeWire p)

/-- 物理基底からrow oracleの外部三registerだけを観測する。 -/
def observeRowOracle (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) :
    RowOracleObservation where
  columnKey := readWires (columnKeyWires p) basis
  columnSelector := readWires (columnSelectorWires p) basis
  keySignal := basis (keySignalWire p)

/--
column oracleの物理基底仕様。外部四registerはpure解析作用に一致し、それ以外の全wireは
入力値へ戻るため、内部work復元と外部wire保存を同時に表す。
-/
structure ColumnOracleRestoredReferenceIdentification (p : QParameters)
    (configuration : QConfiguration p) (selector : QSelector p)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 外部観測値は回路非依存のcolumn解析作用に一致する。 -/
  observation : observeColumnOracle p output =
    columnOracleAnalyticAction configuration selector
      (observeColumnOracle p input)
  /-- 外部出力四register以外の全wireは入力へ復元される。 -/
  outside_restored : ∀ wire,
    wire ∉ rowOutputWires p → wire ∉ selectorOutputWires p →
      wire ≠ negativeWire p → wire ≠ activeWire p →
      output wire = input wire

/--
row oracleの物理基底仕様。外部三registerはpure解析作用に一致し、それ以外の全wireは
入力値へ戻るため、内部work復元と外部wire保存を同時に表す。
-/
structure RowOracleRestoredReferenceIdentification (p : QParameters)
    (configuration : QConfiguration p) (selector : QSelector p)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 外部観測値は回路非依存のrow解析作用に一致する。 -/
  observation : observeRowOracle p output =
    rowOracleAnalyticAction configuration selector (observeRowOracle p input)
  /-- 外部出力三register以外の全wireは入力へ復元される。 -/
  outside_restored : ∀ wire,
    wire ∉ columnKeyWires p → wire ∉ columnSelectorWires p →
      wire ≠ keySignalWire p → output wire = input wire

/-- column物理仕様を満たす出力基底は一意である。 -/
theorem ColumnOracleRestoredReferenceIdentification.unique
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : ColumnOracleRestoredReferenceIdentification p configuration selector input left)
    (rightSpec : ColumnOracleRestoredReferenceIdentification p configuration selector input right) :
    left = right := by
  funext wire
  by_cases rowMember : wire ∈ rowOutputWires p
  · have observationEq := leftSpec.observation.trans rightSpec.observation.symm
    have rowEq := congrArg ColumnOracleObservation.rowOutput observationEq
    exact readWires_eq_at_of_eq (rowOutputWires p) left right
      (by simpa [observeColumnOracle] using rowEq) rowMember
  by_cases selectorMember : wire ∈ selectorOutputWires p
  · have observationEq := leftSpec.observation.trans rightSpec.observation.symm
    have selectorEq := congrArg ColumnOracleObservation.selectorOutput observationEq
    exact readWires_eq_at_of_eq (selectorOutputWires p) left right
      (by simpa [observeColumnOracle] using selectorEq) selectorMember
  by_cases negativeEq : wire = negativeWire p
  · subst wire
    simpa [observeColumnOracle] using congrArg ColumnOracleObservation.negative
      (leftSpec.observation.trans rightSpec.observation.symm)
  by_cases activeEq : wire = activeWire p
  · subst wire
    simpa [observeColumnOracle] using congrArg ColumnOracleObservation.active
      (leftSpec.observation.trans rightSpec.observation.symm)
  exact (leftSpec.outside_restored wire rowMember selectorMember negativeEq activeEq).trans
    (rightSpec.outside_restored wire rowMember selectorMember negativeEq activeEq).symm

/-- row物理仕様を満たす出力基底は一意である。 -/
theorem RowOracleRestoredReferenceIdentification.unique
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : RowOracleRestoredReferenceIdentification p configuration selector input left)
    (rightSpec : RowOracleRestoredReferenceIdentification p configuration selector input right) :
    left = right := by
  funext wire
  by_cases keyMember : wire ∈ columnKeyWires p
  · have observationEq := leftSpec.observation.trans rightSpec.observation.symm
    have keyEq := congrArg RowOracleObservation.columnKey observationEq
    exact readWires_eq_at_of_eq (columnKeyWires p) left right
      (by simpa [observeRowOracle] using keyEq) keyMember
  by_cases selectorMember : wire ∈ columnSelectorWires p
  · have observationEq := leftSpec.observation.trans rightSpec.observation.symm
    have selectorEq := congrArg RowOracleObservation.columnSelector observationEq
    exact readWires_eq_at_of_eq (columnSelectorWires p) left right
      (by simpa [observeRowOracle] using selectorEq) selectorMember
  by_cases signalEq : wire = keySignalWire p
  · subst wire
    simpa [observeRowOracle] using congrArg RowOracleObservation.keySignal
      (leftSpec.observation.trans rightSpec.observation.symm)
  exact (leftSpec.outside_restored wire keyMember selectorMember signalEq).trans
    (rightSpec.outside_restored wire keyMember selectorMember signalEq).symm

/-- actual column oracleはpureな物理基底仕様を満たす。 -/
theorem identifyCompiledColumnOracleCircuitWithRestoredReference
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ColumnOracleInputSpec p configuration selector input) :
    ColumnOracleRestoredReferenceIdentification p configuration selector input
      ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input) := by
  cases referenceEq : columnReference configuration selector with
  | none =>
      have outputEq := applyColumnOracleReferenceAndRestoreWorkCircuit_reference_none
        configuration selector input clean referenceEq
      rw [outputEq]
      refine {
        observation := by simp [columnOracleAnalyticAction, referenceEq]
        outside_restored := by simp }
  | some reference =>
      have result := applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some
        configuration selector reference input clean referenceEq
      refine {
        observation := ?_
        outside_restored := result.outside_restored }
      apply ColumnOracleObservation.ext
      · simpa [observeColumnOracle, columnOracleAnalyticAction, referenceEq,
          applyColumnReference, analyticXorBits_eq_reference]
          using result.row_output
      · simpa [observeColumnOracle, columnOracleAnalyticAction, referenceEq,
          applyColumnReference, analyticXorConstant_eq_reference]
          using result.selector_output
      · cases reference.negative <;>
          cases value : input (negativeWire p) <;>
          simpa [observeColumnOracle, columnOracleAnalyticAction, referenceEq,
            applyColumnReference, value] using result.negative
      · simpa [observeColumnOracle, columnOracleAnalyticAction, referenceEq,
          applyColumnReference] using result.active

/-- actual row oracleはpureな物理基底仕様を満たす。 -/
theorem identifyCompiledRowOracleCircuitWithRestoredReference
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : RowOracleInputSpec p configuration selector input) :
    RowOracleRestoredReferenceIdentification p configuration selector input
      ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input) := by
  cases referenceEq : rowReference configuration selector with
  | none =>
      have outputEq := applyRowOracleReferenceAndRestoreWorkCircuit_reference_none
        configuration selector input clean referenceEq
      rw [outputEq]
      refine {
        observation := by simp [rowOracleAnalyticAction, referenceEq]
        outside_restored := by simp }
  | some reference =>
      have result := applyRowOracleReferenceAndRestoreWorkCircuit_reference_some
        configuration selector reference input clean referenceEq
      refine {
        observation := ?_
        outside_restored := result.outside_restored }
      apply RowOracleObservation.ext
      · simpa [observeRowOracle, rowOracleAnalyticAction, referenceEq,
          applyRowReference, analyticXorBits_eq_reference]
          using result.column_key
      · simpa [observeRowOracle, rowOracleAnalyticAction, referenceEq,
          applyRowReference, analyticXorConstant_eq_reference]
          using result.column_selector
      · simpa [observeRowOracle, rowOracleAnalyticAction, referenceEq,
          applyRowReference] using result.key_signal

/-- column物理仕様だけから選ぶ、回路非依存の一意な基底参照関数。 -/
noncomputable def columnOracleBasisReference
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth := by
  classical
  by_cases existsOutput : ∃ output,
      ColumnOracleRestoredReferenceIdentification p configuration selector input output
  · exact Classical.choose existsOutput
  · exact input

/-- row物理仕様だけから選ぶ、回路非依存の一意な基底参照関数。 -/
noncomputable def rowOracleBasisReference
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth := by
  classical
  by_cases existsOutput : ∃ output,
      RowOracleRestoredReferenceIdentification p configuration selector input output
  · exact Classical.choose existsOutput
  · exact input

/-- 出力が存在すればcolumn基底参照関数自身もpure仕様を満たす。 -/
theorem columnOracleRestoredReference_spec
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (existsOutput : ∃ output,
      ColumnOracleRestoredReferenceIdentification p configuration selector input output) :
    ColumnOracleRestoredReferenceIdentification p configuration selector input
      (columnOracleBasisReference configuration selector input) := by
  classical
  unfold columnOracleBasisReference
  split
  · exact Classical.choose_spec existsOutput
  · contradiction

/-- 出力が存在すればrow基底参照関数自身もpure仕様を満たす。 -/
theorem rowOracleRestoredReference_spec
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (existsOutput : ∃ output,
      RowOracleRestoredReferenceIdentification p configuration selector input output) :
    RowOracleRestoredReferenceIdentification p configuration selector input
      (rowOracleBasisReference configuration selector input) := by
  classical
  unfold rowOracleBasisReference
  split
  · exact Classical.choose_spec existsOutput
  · contradiction

/-! ## 対角branchを子componentから構成する第2版 -/

/-- column対角branchのuse部を表す、回路実装から独立した純粋基底作用。 -/
def ControlledColumnDiagonalOutputsXorSpec (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let copied := controlledCopyBasisReference (input (oracleBranchWire p))
    (columnKeyWires p) (rowOutputWires p) input
  let selected := controlledXorConstantBasisAction (oracleBranchWire p)
    (6 * slot.val + copy.val) 0 (selectorOutputWires p) copied
  let signed := cnotBasisAction (oracleBranchWire p) (negativeWire p) selected
  cnotBasisAction (oracleBranchWire p) (activeWire p) signed

/-- row対角branchのuse部を表す、回路実装から独立した純粋基底作用。 -/
def ControlledRowDiagonalOutputsXorSpec (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let copied := controlledCopyBasisReference (input (oracleBranchWire p))
    (systemWires p) (columnKeyWires p) input
  let selected := controlledXorConstantBasisAction (oracleBranchWire p)
    (6 * slot.val + copy.val) 0 (columnSelectorWires p) copied
  cnotBasisAction (oracleBranchWire p) (keySignalWire p) selected

/-- column selector の対角値一致を branch flag へ XOR する専用回路wrapper。 -/
def xorColumnDiagonalSelectorMatchIntoBranchFlagCircuit (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
    (6 * slot.val + copy.val)

/-- column selector 一致flagの解析的XOR作用。 -/
def ColumnDiagonalSelectorMatchFlagXorSpec (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  selectorMatchBranchFlagXorReference p (columnSelectorWires p) slot
    (6 * slot.val + copy.val) input

/-- row selector の対角値一致を branch flag へ XOR する専用回路wrapper。 -/
def xorRowDiagonalSelectorMatchIntoBranchFlagCircuit (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
    (6 * slot.val + copy.val)

/-- row selector 一致flagの解析的XOR作用。 -/
def RowDiagonalSelectorMatchFlagXorSpec (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  selectorMatchBranchFlagXorReference p (rowSelectorWires p) slot
    (6 * slot.val + copy.val) input

/-- column対角branchのselector比較と三制御ANDを一つのclean compute契約にする。 -/
def verifiedXorColumnDiagonalSelectorMatchIntoBranchFlagCleanComponent (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorColumnDiagonalSelectorMatchIntoBranchFlagCircuit p slot copy
  reference := ColumnDiagonalSelectorMatchFlagXorSpec p slot copy
  inputCondition := fun input =>
    ∀ wire ∈ decoderAndScratchWires p, input wire = false
  outputCondition := fun _ => True
  restoration := fun input output => output =
    ColumnDiagonalSelectorMatchFlagXorSpec p slot copy input
  runBasis_correct := by
    intro input clean
    exact runBasis_columnDiagonalCompute p slot copy input clean
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- row対角branchのselector比較と三制御ANDを一つのclean compute契約にする。 -/
def verifiedXorRowDiagonalSelectorMatchIntoBranchFlagCleanComponent (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorRowDiagonalSelectorMatchIntoBranchFlagCircuit p slot copy
  reference := RowDiagonalSelectorMatchFlagXorSpec p slot copy
  inputCondition := fun input =>
    ∀ wire ∈ decoderAndScratchWires p, input wire = false
  outputCondition := fun _ => True
  restoration := fun input output => output =
    RowDiagonalSelectorMatchFlagXorSpec p slot copy input
  runBasis_correct := by
    intro input clean
    exact runBasis_rowDiagonalCompute p slot copy input clean
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- column対角branchの外部XOR列を純粋作用へ結ぶ全入力component。 -/
def verifiedControlledXorColumnDiagonalResultIntoOutputsCleanComponent (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy
  reference := ControlledColumnDiagonalOutputsXorSpec p slot copy
  inputCondition := fun _ => True
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = ControlledColumnDiagonalOutputsXorSpec p slot copy input
  runBasis_correct := by
    intro input _
    simp only [controlledXorColumnDiagonalResultIntoOutputsCircuit, runBasis_seq,
      ControlledColumnDiagonalOutputsXorSpec]
    rw [runBasis_validatedControlledXorCopyLists_eq_controlledCopyBasisReference
      (oracleBranchWire p) (columnKeyWires p) (rowOutputWires p) input
      (columnKeyWires_nodup p) (rowOutputWires_nodup p)
      (by simp) (columnKeyWires_disjoint_rowOutputWires p)
      (oracleBranchWire_not_mem_columnKeyWires p)
      (oracleBranchWire_not_mem_rowOutputWires p)]
    rw [runBasis_controlledXorConstant (oracleBranchWire p)
      (selectorOutputWires p) (6 * slot.val + copy.val) _
      (oracleBranchWire_not_mem_selectorOutputWires p)]
    rw [runBasis_safeCnot (oracleBranchWire p) (negativeWire p)
      (oracleBranchWire_ne_negativeWire p)]
    rw [runBasis_safeCnot (oracleBranchWire p) (activeWire p)
      (oracleBranchWire_ne_activeWire p)]
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- row対角branchの外部XOR列を純粋作用へ結ぶ全入力component。 -/
def verifiedControlledXorRowDiagonalResultIntoOutputsCleanComponent (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy
  reference := ControlledRowDiagonalOutputsXorSpec p slot copy
  inputCondition := fun _ => True
  outputCondition := fun _ => True
  restoration := fun input output =>
    output = ControlledRowDiagonalOutputsXorSpec p slot copy input
  runBasis_correct := by
    intro input _
    have systemDisjointKey : (systemWires p).Disjoint (columnKeyWires p) := by
      simpa [systemWires, topSystemWires, QLayout.systemWire,
        columnKeyWires_eq_topColumnKeyWires]
        using topSystemWires_disjoint_topColumnKeyWires p
    simp only [controlledXorRowDiagonalResultIntoOutputsCircuit, runBasis_seq,
      ControlledRowDiagonalOutputsXorSpec]
    rw [runBasis_validatedControlledXorCopyLists_eq_controlledCopyBasisReference
      (oracleBranchWire p) (systemWires p) (columnKeyWires p) input
      (systemWires_nodup p) (columnKeyWires_nodup p)
      (by simp) systemDisjointKey
      (oracleBranchWire_not_mem_systemWires p)
      (oracleBranchWire_not_mem_columnKeyWires p)]
    rw [runBasis_controlledXorConstant (oracleBranchWire p)
      (columnSelectorWires p) (6 * slot.val + copy.val) _
      (oracleBranchWire_not_mem_columnSelectorWires p)]
    rw [runBasis_safeCnot (oracleBranchWire p) (keySignalWire p)
      (oracleBranchWire_ne_keySignalWire p)]
  outputCondition_correct := by simp
  restoration_correct := by simp

/-- column対角branchのcompute/use/C-U-U合成が与える純粋参照作用。 -/
def columnDiagonalComposedReference (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  restoreSupport (columnDiagonalComputeSupport p) input
    (ControlledColumnDiagonalOutputsXorSpec p slot copy
      (selectorMatchBranchFlagXorReference p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) input))

/-- row対角branchのcompute/use/C-U-U合成が与える純粋参照作用。 -/
def rowDiagonalComposedReference (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  restoreSupport (rowDiagonalComputeSupport p) input
    (ControlledRowDiagonalOutputsXorSpec p slot copy
      (selectorMatchBranchFlagXorReference p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) input))

/-- column対角branch正本の実行をcompute/use子componentの公開契約だけで合成する。 -/
theorem runBasis_columnDiagonalResultComputeUseUncomputeCircuit_eq_composed_of_components
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input) :
    (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input =
      columnDiagonalComposedReference p slot copy input := by
  rw [runBasis_columnDiagonalResultComputeUseUncomputeCircuit_restoreSupport]
  have computeEq :
      (xorSelectorMatchIntoBranchFlagCircuit p (columnSelectorWires p) slot
        (6 * slot.val + copy.val)).runBasis reversibleGatePermutation input =
      selectorMatchBranchFlagXorReference p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) input := by
    simpa [verifiedXorColumnDiagonalSelectorMatchIntoBranchFlagCleanComponent,
      xorColumnDiagonalSelectorMatchIntoBranchFlagCircuit,
      ColumnDiagonalSelectorMatchFlagXorSpec] using
      (verifiedXorColumnDiagonalSelectorMatchIntoBranchFlagCleanComponent p slot copy).runBasis_correct
        input clean.scratch_zero
  rw [computeEq]
  have useEq :
      (controlledXorColumnDiagonalResultIntoOutputsCircuit p slot copy).runBasis reversibleGatePermutation
        (selectorMatchBranchFlagXorReference p (columnSelectorWires p) slot
          (6 * slot.val + copy.val) input) =
      ControlledColumnDiagonalOutputsXorSpec p slot copy
        (selectorMatchBranchFlagXorReference p (columnSelectorWires p) slot
          (6 * slot.val + copy.val) input) := by
    simpa [verifiedControlledXorColumnDiagonalResultIntoOutputsCleanComponent] using
      (verifiedControlledXorColumnDiagonalResultIntoOutputsCleanComponent p slot copy).runBasis_correct _ trivial
  rw [useEq]
  rfl

/-- row対角branch正本の実行をcompute/use子componentの公開契約だけで合成する。 -/
theorem runBasis_rowDiagonalResultComputeUseUncomputeCircuit_eq_composed_of_components
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input) :
    (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input =
      rowDiagonalComposedReference p slot copy input := by
  rw [runBasis_rowDiagonalResultComputeUseUncomputeCircuit_restoreSupport]
  have computeEq :
      (xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
        (6 * slot.val + copy.val)).runBasis reversibleGatePermutation input =
      selectorMatchBranchFlagXorReference p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) input := by
    simpa [verifiedXorRowDiagonalSelectorMatchIntoBranchFlagCleanComponent,
      xorRowDiagonalSelectorMatchIntoBranchFlagCircuit,
      RowDiagonalSelectorMatchFlagXorSpec] using
      (verifiedXorRowDiagonalSelectorMatchIntoBranchFlagCleanComponent p slot copy).runBasis_correct
        input clean.scratch_zero
  rw [computeEq]
  have useEq :
      (controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy).runBasis reversibleGatePermutation
        (selectorMatchBranchFlagXorReference p (rowSelectorWires p) slot
          (6 * slot.val + copy.val) input) =
      ControlledRowDiagonalOutputsXorSpec p slot copy
        (selectorMatchBranchFlagXorReference p (rowSelectorWires p) slot
          (6 * slot.val + copy.val) input) := by
    simpa [verifiedControlledXorRowDiagonalResultIntoOutputsCleanComponent] using
      (verifiedControlledXorRowDiagonalResultIntoOutputsCleanComponent p slot copy).runBasis_correct _ trivial
  rw [useEq]
  rfl

/-- 子componentを合成したcolumn参照作用は、公開する解析的branch仕様に一致する。 -/
theorem identifyColumnDiagonalComposedReferenceWithRestoredReference (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input) :
    columnDiagonalComposedReference p slot copy input =
      uniqueSpecificationReference (fun source output =>
        ColumnDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
          (diagonalBranchEnabled p (columnSelectorWires p) slot
            (6 * slot.val + copy.val) legalValue presentValue source)
          source output) input := by
  let actual := (columnDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
    reversibleGatePermutation input
  have actualSpec := verifiedColumnDiagonalRestoredReferenceIdentification p slot copy
    legalValue presentValue input clean
  have actualEq : actual = columnDiagonalComposedReference p slot copy input := by
    simpa [actual] using
      runBasis_columnDiagonalResultComputeUseUncomputeCircuit_eq_composed_of_components p slot copy
        legalValue presentValue input clean
  have composedSpec : ColumnDiagonalRestoredReferenceIdentification p
      (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input)
      input (columnDiagonalComposedReference p slot copy input) := by
    rw [← actualEq]
    exact actualSpec
  have uniqueOutput : ∃! output, ColumnDiagonalRestoredReferenceIdentification p
      (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input)
      input output := ⟨_, composedSpec, fun other otherSpec =>
        otherSpec.unique composedSpec⟩
  exact composedSpec.unique (uniqueSpecificationReference_spec uniqueOutput)

/-- 子componentを合成したrow参照作用は、公開する解析的branch仕様に一致する。 -/
theorem identifyRowDiagonalComposedReferenceWithRestoredReference (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) (legalValue presentValue : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : DiagonalBranchCleanInput p slot legalValue presentValue input) :
    rowDiagonalComposedReference p slot copy input =
      uniqueSpecificationReference (fun source output =>
        RowDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
          (diagonalBranchEnabled p (rowSelectorWires p) slot
            (6 * slot.val + copy.val) legalValue presentValue source)
          source output) input := by
  let actual := (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
    reversibleGatePermutation input
  have actualSpec := verifiedRowDiagonalRestoredReferenceIdentification p slot copy
    legalValue presentValue input clean
  have actualEq : actual = rowDiagonalComposedReference p slot copy input := by
    simpa [actual] using
      runBasis_rowDiagonalResultComputeUseUncomputeCircuit_eq_composed_of_components p slot copy
        legalValue presentValue input clean
  have composedSpec : RowDiagonalRestoredReferenceIdentification p
      (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input)
      input (rowDiagonalComposedReference p slot copy input) := by
    rw [← actualEq]
    exact actualSpec
  have uniqueOutput : ∃! output, RowDiagonalRestoredReferenceIdentification p
      (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input)
      input output := ⟨_, composedSpec, fun other otherSpec =>
        otherSpec.unique composedSpec⟩
  exact composedSpec.unique (uniqueSpecificationReference_spec uniqueOutput)

/-- column対角branchをcompute component・use component・C-U-U則から組み立てる第2版。 -/
noncomputable def verifiedColumnDiagonalResultComputeUseUncomputeCleanComponent
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := columnDiagonalResultComputeUseUncomputeCircuit p slot copy
  reference := uniqueSpecificationReference fun input output =>
    ColumnDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input) input output
  inputCondition := DiagonalBranchCleanInput p slot legalValue presentValue
  outputCondition := fun _ => True
  restoration := fun input output =>
    ColumnDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (columnSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input) input output
  runBasis_correct := by
    intro input clean
    rw [runBasis_core_eq_local reversibleGatePermutation
      (columnDiagonalResultComputeUseUncomputeCircuit p slot copy) input]
    rw [runBasis_columnDiagonalResultComputeUseUncomputeCircuit_eq_composed_of_components p slot copy
      legalValue presentValue input clean]
    exact identifyColumnDiagonalComposedReferenceWithRestoredReference p slot copy legalValue
      presentValue input clean
  outputCondition_correct := by simp
  restoration_correct := by
    intro input clean
    have result := identifyColumnDiagonalComposedReferenceWithRestoredReference p slot copy legalValue
      presentValue input clean
    rw [← result]
    have actualSpec := verifiedColumnDiagonalRestoredReferenceIdentification p slot copy
      legalValue presentValue input clean
    rw [runBasis_columnDiagonalResultComputeUseUncomputeCircuit_eq_composed_of_components p slot copy
      legalValue presentValue input clean] at actualSpec
    exact actualSpec

/-- row対角branchをcompute component・use component・C-U-U則から組み立てる第2版。 -/
noncomputable def verifiedRowDiagonalResultComputeUseUncomputeCleanComponent
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (legalValue presentValue : Bool) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := rowDiagonalResultComputeUseUncomputeCircuit p slot copy
  reference := uniqueSpecificationReference fun input output =>
    RowDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input) input output
  inputCondition := DiagonalBranchCleanInput p slot legalValue presentValue
  outputCondition := fun _ => True
  restoration := fun input output =>
    RowDiagonalRestoredReferenceIdentification p (6 * slot.val + copy.val)
      (diagonalBranchEnabled p (rowSelectorWires p) slot
        (6 * slot.val + copy.val) legalValue presentValue input) input output
  runBasis_correct := by
    intro input clean
    rw [runBasis_core_eq_local reversibleGatePermutation
      (rowDiagonalResultComputeUseUncomputeCircuit p slot copy) input]
    rw [runBasis_rowDiagonalResultComputeUseUncomputeCircuit_eq_composed_of_components p slot copy
      legalValue presentValue input clean]
    exact identifyRowDiagonalComposedReferenceWithRestoredReference p slot copy legalValue
      presentValue input clean
  outputCondition_correct := by simp
  restoration_correct := by
    intro input clean
    have result := identifyRowDiagonalComposedReferenceWithRestoredReference p slot copy legalValue
      presentValue input clean
    rw [← result]
    have actualSpec := verifiedRowDiagonalRestoredReferenceIdentification p slot copy
      legalValue presentValue input clean
    rw [runBasis_rowDiagonalResultComputeUseUncomputeCircuit_eq_composed_of_components p slot copy
      legalValue presentValue input clean] at actualSpec
    exact actualSpec

end ReversibleCircuit

end ProbabilityGeneratorQProof
