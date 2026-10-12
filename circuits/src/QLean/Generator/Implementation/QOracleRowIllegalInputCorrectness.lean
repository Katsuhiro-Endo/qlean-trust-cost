import QLean.Generator.Implementation.QOracleRowEventComplete
import QLean.Generator.Implementation.QDecoderLegalityCompleteness

/-!
# Q row oracle の非合法 delimiter 入力に対する完全な基底作用

system register が delimiter として復号できない場合を、巨大行列を展開せずに扱う。
compact decoder の局所 support と基底作用を用いて legal flag が偽であることを示し、
対角・event の全分岐と最外 compute--uncompute が恒等作用になることを証明する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/--
任意の適正配置registerに対するcompact decoderの基底clean条件。合法configurationを
要求せず、入力bit列と全scratchの初期値だけを指定する。
-/
structure CompactDecoderBasisCleanInput (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 入力registerは指定した有限基底を保持する。 -/
  input_bits : readWires inputWires input = registerBitList basis
  /-- suffix scratchは全0である。 -/
  suffix_zero : readWires (decoderSuffixWires p) input =
    List.replicate (decoderSuffixWires p).length false
  /-- degree flag列は全0である。 -/
  degree_zero : readWires (oracleDegreeWires p) input =
    List.replicate (oracleDegreeWires p).length false
  /-- 比較workは全0である。 -/
  compare_zero : readWires (oracleCompareWorkWires p) input =
    List.replicate (oracleCompareWorkWires p).length false
  /-- AND workは全0である。 -/
  and_zero : ∀ wire ∈ oracleAndWorkWires p, input wire = false
  /-- 保持用legal wireは0である。 -/
  legal_zero : input (oracleLegalWire p) = false

/-- 任意配置のclean基底をdegree decodeすると純粋degree bit列を得る。 -/
theorem readWires_degreeDecode_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input) :
    readWires (oracleDegreeWires p)
        ((xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
          (oracleDegreeWires p)).runBasis reversibleGatePermutation input) =
      decoderDegreeBits p (registerBitList basis) := by
  have result := readWires_xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires
    (decoderSuffixWires p) (oracleDegreeWires p) input
    (by simp [layout.length_eq]) layout.disjoint_suffix layout.disjoint_degree
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p) (oracleDegreeWires_nodup p)
    clean.suffix_zero clean.degree_zero
  simpa [decoderDegreeBits, clean.input_bits] using result

/--
任意配置のclean基底で、degree decode後の実比較列は純粋good bit列を返し、
共有AND scratchを0へ戻す。
-/
theorem decoderComparison_after_degreeDecode_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input) :
    let degree := oracleDegreeWires p
    let words := splitSystemWords p.wordWidth p.K inputWires
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let compared :=
      (decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation decoded
    readWires (decoderGoodWires p) compared =
        decoderGoodBits p (registerBitList basis) ∧
      ∀ wire ∈ decoderAndScratchWires p, compared wire = false := by
  dsimp only
  let degree := oracleDegreeWires p
  let words := splitSystemWords p.wordWidth p.K inputWires
  let compare := oracleCompareWorkWires p
  let scratch := decoderAndScratchWires p
  let less := decoderLessWires p
  let need := decoderNeedWires p
  let good := decoderGoodWires p
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  have suffixDisjointDegree : (decoderSuffixWires p).Disjoint degree := by
    simpa [degree] using (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
  have degreeValues : readWires degree decoded =
      decoderDegreeBits p (registerBitList basis) := by
    simpa [degree, decoded] using
      readWires_degreeDecode_of_basis_clean p inputWires layout basis input clean
  have wordValues : words.map (fun word => readWires word decoded) =
      splitBitWords p.wordWidth p.K (registerBitList basis) := by
    calc
      words.map (fun word => readWires word decoded) =
          words.map (fun word => readWires word input) := by
        apply List.map_congr_left
        intro word wordMember
        apply List.map_congr_left
        intro wire wireMember
        apply runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_input_wire p.wordWidth inputWires
          (decoderSuffixWires p) degree wire input layout.disjoint_suffix
          layout.disjoint_degree suffixDisjointDegree
        rcases List.mem_map.mp wordMember with ⟨slot, _, rfl⟩
        exact List.mem_of_mem_drop (List.mem_of_mem_take wireMember)
      _ = splitBitWords p.wordWidth p.K (readWires inputWires input) := by
        exact readWires_splitSystemWords p.wordWidth p.K inputWires input
      _ = splitBitWords p.wordWidth p.K (registerBitList basis) := by
        rw [clean.input_bits]
  have compareAfterZero : ∀ wire ∈ compare, decoded wire = false := by
    have compareInputZero : ∀ wire ∈ compare, input wire = false := by
      apply pointwise_false_of_readWires_eq_replicate compare input
      simpa [compare] using clean.compare_zero
    intro wire member
    change (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input wire = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
      (decoderSuffixWires p) degree wire input (by simp [layout.length_eq])
      layout.disjoint_suffix layout.disjoint_degree suffixDisjointDegree
      (decoderSuffixWires_nodup p)]
    · exact compareInputZero wire member
    · exact (List.disjoint_left.mp layout.disjoint_compare.symm member)
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_compareWork p).symm member)
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_compareWork p).symm member)
  have andAfterZero : ∀ wire ∈ oracleAndWorkWires p, decoded wire = false := by
    intro wire member
    change (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input wire = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
      (decoderSuffixWires p) degree wire input (by simp [layout.length_eq])
      layout.disjoint_suffix layout.disjoint_degree suffixDisjointDegree
      (decoderSuffixWires_nodup p)]
    · exact clean.and_zero wire member
    · exact (List.disjoint_left.mp layout.disjoint_and.symm member)
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_andWork p).symm member)
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_andWork p).symm member)
  have compareZero : readWires compare decoded =
      List.replicate compare.length false :=
    readWires_eq_replicate_false_of_forall compare decoded compareAfterZero
  have scratchZero : ∀ wire ∈ scratch, decoded wire = false := by
    intro wire member
    exact andAfterZero wire
      (decoderComparisonAndMember p (by simp [scratch, member]))
  have lessZero : readWires less decoded = List.replicate less.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p
      (by simp [less, decoderComparisonFlagWires, member]))
  have needZero : readWires need decoded = List.replicate need.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p
      (by simp [need, decoderComparisonFlagWires, member]))
  have goodZero : readWires good decoded = List.replicate good.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p
      (by simp [good, decoderComparisonFlagWires, member]))
  have wordCount : words.length = good.length + 1 := by
    have positive := p.K_pos
    simp [words, good, splitSystemWords]
    omega
  have lessCount : less.length = good.length := by simp [less, good]
  have needCount : need.length = good.length := by simp [need, good]
  have wordLengths : ∀ word ∈ words, word.length = compare.length := by
    intro word member
    rcases List.mem_map.mp member with ⟨slot, slotMember, rfl⟩
    have slotLt : slot < p.K := List.mem_range.mp slotMember
    rw [List.length_take, List.length_drop, layout.length_eq]
    have enough : p.wordWidth + slot * p.wordWidth ≤ p.systemWidth := by
      simp [QParameters.systemWidth]
      nlinarith
    rw [Nat.min_eq_left (Nat.le_sub_of_add_le enough)]
    simp [compare]
  have supportNodup :
      (decoderComparisonSupport degree compare scratch words less need good).Nodup := by
    simpa [degree, compare, scratch, words, less, need, good] using
      decoderComparisonSupport_input_nodup p inputWires layout
  have goodResult := readWires_decoderComparisonSequence_good degree compare scratch
    0 words less need good decoded wordCount lessCount needCount wordLengths
    supportNodup compareZero scratchZero lessZero needZero goodZero
    (by simpa [compare, scratch] using decoderAndScratchWires_wordWidth_le p)
  have scratchResult := runBasis_decoderComparisonSequence_scratch_clean
    degree compare scratch 0 words less need good decoded wordCount lessCount
    needCount wordLengths supportNodup compareZero scratchZero lessZero needZero
    goodZero (by simpa [compare, scratch] using
      decoderAndScratchWires_wordWidth_le p)
  constructor
  · calc
      readWires good
          ((decoderComparisonSequence degree compare scratch 0 words less need good).runBasis
            reversibleGatePermutation decoded) =
          decoderExpectedGoodBits (readWires degree decoded) 0
            (words.map fun word => readWires word decoded) := goodResult
      _ = decoderGoodBits p (registerBitList basis) := by
        rw [degreeValues, wordValues]
        rfl
  · exact scratchResult

/-- 任意配置でもdegree-valid回路はdegree parityだけを標的へXORする。 -/
theorem decoderDegreeValid_after_degreeDecode_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input) :
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded =
      if boolParity (decoderDegreeBits p (registerBitList basis)) then
        xBasisAction (decoderDegreeValidWire p) decoded
      else decoded := by
  dsimp only
  have targetAbsent : decoderDegreeValidWire p ∉ oracleDegreeWires p := by
    intro member
    exact (List.disjoint_left.mp (oracleDegreeWires_disjoint_andWork p) member)
      (decoderDegreeValid_mem_andWork p)
  rw [show decoderDegreeValidCircuit (oracleDegreeWires p)
      (decoderDegreeValidWire p) =
      xorSourceParityIntoTargetCircuit (oracleDegreeWires p) (decoderDegreeValidWire p) by rfl]
  rw [runBasis_xorSourceParityIntoTargetCircuit (oracleDegreeWires p)
    (decoderDegreeValidWire p) _ targetAbsent]
  rw [readWires_degreeDecode_of_basis_clean p inputWires layout basis input clean]

/--
degree-valid計算を比較列の前へ加えても、任意配置のgood列とscratch復元結果は
純粋基底仕様に一致する。
-/
theorem decoderComparison_after_degreeValid_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input) :
    let degree := oracleDegreeWires p
    let words := splitSystemWords p.wordWidth p.K inputWires
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let prepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    let compared :=
      (decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation prepared
    readWires (decoderGoodWires p) compared =
        decoderGoodBits p (registerBitList basis) ∧
      ∀ wire ∈ decoderAndScratchWires p, compared wire = false := by
  dsimp only
  let degree := oracleDegreeWires p
  let words := splitSystemWords p.wordWidth p.K inputWires
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let prepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have preparedEq : prepared =
      if boolParity (decoderDegreeBits p (registerBitList basis)) then
        xBasisAction (decoderDegreeValidWire p) decoded
      else decoded := by
    simpa [prepared, decoded, degree] using
      decoderDegreeValid_after_degreeDecode_of_basis_clean p inputWires layout
        basis input clean
  have beforeAgree : BasisAgreeOn support prepared decoded := by
    intro wire member
    rw [preparedEq]
    split
    · apply xBasisAction_other
      intro equal
      subst wire
      exact decoderDegreeValid_not_mem_comparisonSupport_input p inputWires layout
        (by simpa [support, degree, words] using member)
    · rfl
  have agree : BasisAgreeOn support
      (comparison.runBasis reversibleGatePermutation prepared)
      (comparison.runBasis reversibleGatePermutation decoded) := by
    apply Circuit.runBasis_congr_on_of_usesOnly support comparison
    · simpa [support, comparison, degree, words] using
        decoderComparisonSequence_usesOnly_input p inputWires
    · exact beforeAgree
  have result := decoderComparison_after_degreeDecode_of_basis_clean p inputWires
    layout basis input clean
  constructor
  · calc
      readWires (decoderGoodWires p)
          (comparison.runBasis reversibleGatePermutation prepared) =
          readWires (decoderGoodWires p)
            (comparison.runBasis reversibleGatePermutation decoded) := by
        apply List.map_congr_left
        intro wire member
        exact agree wire (by simp [support, decoderComparisonSupport, member])
      _ = decoderGoodBits p (registerBitList basis) := by
        simpa [comparison, decoded, degree, words] using result.1
  · intro wire member
    calc
      comparison.runBasis reversibleGatePermutation prepared wire =
          comparison.runBasis reversibleGatePermutation decoded wire :=
        agree wire (by simp [support, decoderComparisonSupport, member])
      _ = false := by
        exact result.2 wire member

/-- 比較後のdegree-valid wireは任意配置でも純粋degree parityに一致する。 -/
theorem decoderDegreeValid_after_comparison_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input) :
    let degree := oracleDegreeWires p
    let words := splitSystemWords p.wordWidth p.K inputWires
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let prepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    let compared :=
      (decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation prepared
    compared (decoderDegreeValidWire p) =
      boolParity (decoderDegreeBits p (registerBitList basis)) := by
  dsimp only
  let degree := oracleDegreeWires p
  let words := splitSystemWords p.wordWidth p.K inputWires
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let prepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have outside : decoderDegreeValidWire p ∉ support := by
    simpa [support, degree, words] using
      decoderDegreeValid_not_mem_comparisonSupport_input p inputWires layout
  rw [Circuit.runBasis_outside_of_usesOnly support comparison
    (by simpa [support, comparison, degree, words] using
      decoderComparisonSequence_usesOnly_input p inputWires) prepared
    (decoderDegreeValidWire p) outside]
  have preparedEq : prepared =
      if boolParity (decoderDegreeBits p (registerBitList basis)) then
        xBasisAction (decoderDegreeValidWire p) decoded
      else decoded := by
    simpa [prepared, decoded, degree] using
      decoderDegreeValid_after_degreeDecode_of_basis_clean p inputWires layout
        basis input clean
  have decodedFalse : decoded (decoderDegreeValidWire p) = false := by
    change (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
        (decoderDegreeValidWire p) = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
      (decoderSuffixWires p) degree (decoderDegreeValidWire p) input
      (by simp [layout.length_eq]) layout.disjoint_suffix layout.disjoint_degree
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
      (decoderSuffixWires_nodup p)]
    · exact clean.and_zero _ (decoderDegreeValid_mem_andWork p)
    · exact (List.disjoint_left.mp layout.disjoint_and.symm
        (decoderDegreeValid_mem_andWork p))
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_andWork p).symm
        (decoderDegreeValid_mem_andWork p))
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_andWork p).symm
        (decoderDegreeValid_mem_andWork p))
  rw [preparedEq]
  cases parity : boolParity (decoderDegreeBits p (registerBitList basis)) <;>
    simp [decodedFalse, xBasisAction_target]

/-- 任意配置の合法性computeは保持前のtemporaryへ純粋受理Boolを書く。 -/
theorem decoderLegalityCompute_temporary_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input) :
    let degree := oracleDegreeWires p
    let words := splitSystemWords p.wordWidth p.K inputWires
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    (decoderLegalityCompute words degree (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p) (decoderDegreeValidWire p)
      (decoderLegalTemporaryWire p)).runBasis reversibleGatePermutation decoded
        (decoderLegalTemporaryWire p) =
      (boolParity (decoderDegreeBits p (registerBitList basis)) &&
        (decoderGoodBits p (registerBitList basis)).all id) := by
  dsimp only
  let degree := oracleDegreeWires p
  let words := splitSystemWords p.wordWidth p.K inputWires
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let prepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  let compared := comparison.runBasis reversibleGatePermutation prepared
  let controls := decoderDegreeValidWire p :: decoderGoodWires p
  let scratch := decoderAndScratchWires p
  let target := decoderLegalTemporaryWire p
  change (positiveMultiControlledX controls scratch target).runBasis
    reversibleGatePermutation compared target = _
  have comparedResult := decoderComparison_after_degreeValid_of_basis_clean
    p inputWires layout basis input clean
  have scratchZero : ∀ wire ∈ scratch, compared wire = false := by
    simpa [scratch, compared, comparison, prepared, decoded, degree, words] using
      comparedResult.2
  rw [runBasis_positiveMultiControlledX controls scratch target compared
    (by simpa [controls, scratch] using decoderAllGood_enoughScratch p)
    (by simpa [controls, scratch, target] using decoderAllGood_layout_nodup p)
    scratchZero]
  have controlsValue : allWiresTrue controls compared =
      (boolParity (decoderDegreeBits p (registerBitList basis)) &&
        (decoderGoodBits p (registerBitList basis)).all id) := by
    have degreeValue : compared (decoderDegreeValidWire p) =
        boolParity (decoderDegreeBits p (registerBitList basis)) := by
      simpa [compared, comparison, prepared, decoded, degree, words] using
        decoderDegreeValid_after_comparison_of_basis_clean p inputWires layout
          basis input clean
    have goodValue : readWires (decoderGoodWires p) compared =
        decoderGoodBits p (registerBitList basis) := by
      simpa [compared, comparison, prepared, decoded, degree, words] using
        comparedResult.1
    change (compared (decoderDegreeValidWire p) ::
      readWires (decoderGoodWires p) compared).all id = _
    rw [degreeValue, goodValue]
    rfl
  rw [controlsValue]
  have outsideTarget : target ∉ support := by
    simpa [target, support, degree, words] using
      decoderLegalTemporary_not_mem_comparisonSupport_input p inputWires layout
  have comparedTarget : compared target = prepared target :=
    Circuit.runBasis_outside_of_usesOnly support comparison
      (by simpa [support, comparison, degree, words] using
        decoderComparisonSequence_usesOnly_input p inputWires)
      prepared target outsideTarget
  have preparedEq : prepared =
      if boolParity (decoderDegreeBits p (registerBitList basis)) then
        xBasisAction (decoderDegreeValidWire p) decoded
      else decoded := by
    simpa [prepared, decoded, degree] using
      decoderDegreeValid_after_degreeDecode_of_basis_clean p inputWires layout
        basis input clean
  have targetNeDegree : target ≠ decoderDegreeValidWire p := by
    have fresh := (List.nodup_cons.mp (decoderAllGood_layout_nodup p)).1
    have degreeNeTarget :
        decoderDegreeValidWire p ≠ decoderLegalTemporaryWire p := by
      intro equal
      exact fresh (by simp [equal])
    simpa [target] using degreeNeTarget.symm
  have preparedTarget : prepared target = decoded target := by
    rw [preparedEq]
    split
    · exact xBasisAction_other (decoderDegreeValidWire p) target
        targetNeDegree decoded
    · rfl
  have decodedTarget : decoded target = false := by
    change (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input target = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
      (decoderSuffixWires p) degree target input (by simp [layout.length_eq])
      layout.disjoint_suffix layout.disjoint_degree
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
      (decoderSuffixWires_nodup p)]
    · exact clean.and_zero target (by
        simpa [target] using decoderLegalTemporary_mem_andWork p)
    · exact (List.disjoint_left.mp layout.disjoint_and.symm
        (by simpa [target] using decoderLegalTemporary_mem_andWork p))
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_andWork p).symm
        (by simpa [target] using decoderLegalTemporary_mem_andWork p))
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_andWork p).symm
        (by simpa [target] using decoderLegalTemporary_mem_andWork p))
  cases acceptedValue :
      (boolParity (decoderDegreeBits p (registerBitList basis)) &&
        (decoderGoodBits p (registerBitList basis)).all id)
  · simp only [Bool.false_eq_true, if_false]
    rw [comparedTarget, preparedTarget, decodedTarget]
  · simp only [if_true, xBasisAction_target]
    rw [comparedTarget, preparedTarget, decodedTarget]
    rfl

/-- 任意配置のcompact decoderのlegal出力は純粋受理Boolと厳密に一致する。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_eq_accepts_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input) :
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input (oracleLegalWire p) =
      (boolParity (decoderDegreeBits p (registerBitList basis)) &&
        (decoderGoodBits p (registerBitList basis)).all id) := by
  let degree := oracleDegreeWires p
  let words := splitSystemWords p.wordWidth p.K inputWires
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let compute := decoderLegalityCompute words degree (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p) (oracleCompareWorkWires p)
    (decoderAndScratchWires p) (decoderDegreeValidWire p)
    (decoderLegalTemporaryWire p)
  let use := safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)
  let support := decoderLegalitySupportFor p inputWires
  change (Circuit.computeUseUncompute id compute use).runBasis
    reversibleGatePermutation decoded (oracleLegalWire p) = _
  have computeUses : circuitUsesOnly support compute := by
    simpa [support, compute, words, degree] using
      decoderLegalityCompute_usesOnly_input p inputWires
  have legalOutside : oracleLegalWire p ∉ support := by
    simpa [support] using
      oracleLegal_not_mem_decoderLegalitySupportFor p inputWires layout
  have temporaryMember : decoderLegalTemporaryWire p ∈ support := by
    have andMember := decoderLegalTemporary_mem_andWork p
    simp [support, decoderLegalitySupportFor, andMember]
  have sourceDifferent : decoderLegalTemporaryWire p ≠ oracleLegalWire p := by
    intro equal
    apply legalOutside
    simpa [equal] using temporaryMember
  have usePreserves : BasisAgreeOn support
      (use.runBasis reversibleGatePermutation
        (compute.runBasis reversibleGatePermutation decoded))
      (compute.runBasis reversibleGatePermutation decoded) := by
    simpa [support, use] using decoderLegalityUse_preservesSupportFor p inputWires
      layout (compute.runBasis reversibleGatePermutation decoded)
  rw [Circuit.computeUseUncompute_local_clean support compute use decoded computeUses
    usePreserves]
  rw [restoreSupport_outside support decoded
    (use.runBasis reversibleGatePermutation
      (compute.runBasis reversibleGatePermutation decoded))
    (oracleLegalWire p) legalOutside]
  rw [show use = safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p) by rfl]
  rw [runBasis_safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)
    sourceDifferent]
  rw [cnotBasisAction_target]
  have temporaryValue : compute.runBasis reversibleGatePermutation decoded
      (decoderLegalTemporaryWire p) =
      (boolParity (decoderDegreeBits p (registerBitList basis)) &&
        (decoderGoodBits p (registerBitList basis)).all id) := by
    simpa [compute, decoded, degree, words] using
      decoderLegalityCompute_temporary_of_basis_clean p inputWires layout basis
        input clean
  have computedLegal : compute.runBasis reversibleGatePermutation decoded
      (oracleLegalWire p) = decoded (oracleLegalWire p) :=
    Circuit.runBasis_outside_of_usesOnly support compute computeUses decoded
      (oracleLegalWire p) legalOutside
  have decodedLegal : decoded (oracleLegalWire p) = false := by
    change (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input (oracleLegalWire p) = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
      (decoderSuffixWires p) degree (oracleLegalWire p) input
      (by simp [layout.length_eq]) layout.disjoint_suffix layout.disjoint_degree
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
      (decoderSuffixWires_nodup p)]
    · exact clean.legal_zero
    · exact layout.legal_fresh
    · intro member
      exact legalOutside (by simp [support, decoderLegalitySupportFor, member])
    · intro member
      exact legalOutside
        (by simp [support, decoderLegalitySupportFor, degree, member])
  rw [temporaryValue, computedLegal, decodedLegal]
  cases boolParity (decoderDegreeBits p (registerBitList basis)) <;>
    cases (decoderGoodBits p (registerBitList basis)).all id <;> rfl

/-- decode不能な任意配置基底ではcompact decoderのlegal flagが偽になる。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_false_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input)
    (illegal : decodeDelimiter basis = none) :
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input (oracleLegalWire p) = false := by
  rw [xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_eq_accepts_of_basis_clean p
    inputWires layout basis input clean]
  apply Bool.eq_false_of_not_eq_true
  intro acceptedBool
  have accepted : DecoderAccepts p (registerBitList basis) := by
    simpa [DecoderAccepts, Bool.and_eq_true] using acceptedBool
  have legalDelimiter := (decoderAccepts_iff_isLegalDelimiter p basis).mp accepted
  exact (decodeDelimiter_eq_none_iff.mp illegal) legalDelimiter

/-- 任意配置のcompact decoderは基底clean入力の比較・AND workを0へ戻す。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_work_clean_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input) :
    let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    (∀ wire ∈ oracleCompareWorkWires p, output wire = false) ∧
      (∀ wire ∈ oracleAndWorkWires p, output wire = false) := by
  dsimp only
  let degree := oracleDegreeWires p
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
    reversibleGatePermutation input
  have agree : BasisAgreeOn (decoderLegalitySupportFor p inputWires)
      output decoded := by
    simpa [output, decoded, degree] using
      xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_support_restored_of_input p inputWires
        layout input
  constructor
  · intro wire member
    change output wire = false
    rw [agree wire (by simp [decoderLegalitySupportFor, member])]
    change (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input wire = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
      (decoderSuffixWires p) degree wire input (by simp [layout.length_eq])
      layout.disjoint_suffix layout.disjoint_degree
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
      (decoderSuffixWires_nodup p)]
    · exact pointwise_false_of_readWires_eq_replicate
        (oracleCompareWorkWires p) input clean.compare_zero wire member
    · exact (List.disjoint_left.mp layout.disjoint_compare.symm member)
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_compareWork p).symm member)
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_compareWork p).symm member)
  · intro wire member
    change output wire = false
    rw [agree wire (by simp [decoderLegalitySupportFor, member])]
    change (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input wire = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
      (decoderSuffixWires p) degree wire input (by simp [layout.length_eq])
      layout.disjoint_suffix layout.disjoint_degree
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
      (decoderSuffixWires_nodup p)]
    · exact clean.and_zero wire member
    · exact (List.disjoint_left.mp layout.disjoint_and.symm member)
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_andWork p).symm member)
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_andWork p).symm member)

/-- decode不能な任意配置基底ではpersistent compute後もlegal flagが偽である。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_legal_false_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input)
    (illegal : decodeDelimiter basis = none)
    (rowMode : Bool) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input (oracleLegalWire p) = false := by
  rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_eq_compactDecoder_outside p inputWires rowMode
    input (oracleLegalWire p)]
  · exact xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_false_of_basis_clean p inputWires
      layout.decoder basis input clean illegal
  · intro presentMember
    exact oraclePresentWire_ne_legal p presentMember rfl
  · exact (oraclePersistentSpecialWire_ne_legal p
      (oracleDegreeConditionWire_mem_special p)).symm
  · exact (oraclePersistentSpecialWire_ne_legal p
      (oracleOneWire_mem_special p)).symm

/-- 任意配置のpersistent compute後も比較・AND workは0に復元される。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_work_clean_of_basis_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (basis : RegisterBasis p.systemWidth)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderBasisCleanInput p inputWires basis input)
    (rowMode : Bool) :
    let output := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
      reversibleGatePermutation input
    (∀ wire ∈ oracleCompareWorkWires p, output wire = false) ∧
      (∀ wire ∈ oracleAndWorkWires p, output wire = false) := by
  dsimp only
  have compactClean := xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_work_clean_of_basis_clean
    p inputWires layout.decoder basis input clean
  constructor
  · intro wire member
    rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_work_eq_compactDecoder p inputWires rowMode input
      wire (Or.inl member)]
    exact compactClean.1 wire member
  · intro wire member
    rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_work_eq_compactDecoder p inputWires rowMode input
      wire (Or.inr member)]
    exact compactClean.2 wire member

/--
非合法 system 基底に対する canonical row oracle 入力仕様。system と row selector の値、
および全 oracle work の 0 初期化だけを要求し、外部 accumulator は任意に保つ。
-/
structure RowOracleIllegalInputSpec (p : QParameters)
    (basis : RegisterBasis p.systemWidth) (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- system register は指定した物理基底を保持する。 -/
  system_bits : readWires (systemWires p) input = registerBitList basis
  /-- row selector は指定した canonical 定数 bit 列を保持する。 -/
  selector_bits : readWires (rowSelectorWires p) input =
    constantBits selector.val (rowSelectorWires p).length
  /-- canonical oracle work の全 wire は 0 である。 -/
  work_zero : ∀ wire ∈ diagonalOracleWorkWires p, input wire = false

/-- 非合法 row 入力仕様では、任意の canonical oracle slice が 0 である。 -/
theorem RowOracleIllegalInputSpec.slice_zero
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleIllegalInputSpec p basis selector input)
    {width : Nat} (slice : RegisterSlice p.oracleWorkWidth width) :
    ∀ wire ∈ ((QLayout.oracleSlice slice).wireList :
      List (Wire p.ancillaWidth p.systemWidth)), input wire = false := by
  intro wire member
  exact specification.work_zero wire (by
    simpa [diagonalOracleWorkWires] using
      oracleSliceWire_mem_oracleWork p slice member)

/-- 非合法 row 入力仕様は event/sort の初期 clean 条件を満たす。 -/
theorem RowOracleIllegalInputSpec.eventSortClean
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleIllegalInputSpec p basis selector input) :
    EventSortCleanInput p input := by
  refine {
    moved_selector := {
      compare_zero := ?_
      scratch_zero := ?_
      position_zero := ?_
      pair_zero := ?_ }
    sort_compare_zero := ?_
    sort_scratch_zero := ?_
    sort_history_zero := ?_ }
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply specification.slice_zero (OracleWorkLayout.canonical p).compareWork
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using member
  · intro wire member
    exact specification.work_zero wire
      (decoderAndScratchWire_mem_diagonalOracleWorkWires p member)
  · apply specification.slice_zero (OracleWorkLayout.canonical p).positionMatch
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
    · apply specification.slice_zero
        (OracleWorkLayout.canonical p).compareWork
      simpa [RegisterSlice.wireList] using compareMember
    · subst wire
      apply specification.slice_zero (OracleWorkLayout.canonical p).andWork
      simp [RegisterSlice.wireList]
  · intro wire member
    rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
    apply specification.slice_zero (OracleWorkLayout.canonical p).andWork
    rw [RegisterSlice.wireList]
    apply List.mem_map.mpr
    exact ⟨⟨index.val + 1, by
      simp [QParameters.andWorkWidth] at index ⊢
      omega⟩, List.mem_finRange _, rfl⟩
  · intro instruction instructionMember
    apply specification.slice_zero (OracleWorkLayout.canonical p).sortFlags
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr
      ⟨instruction.history, List.mem_finRange instruction.history, rfl⟩

/-- compact decoder が比較・AND work を任意入力値へ厳密に戻す。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_preserves_compareOrAnd
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ oracleCompareWorkWires p ∨
      wire ∈ oracleAndWorkWires p) :
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
        reversibleGatePermutation input wire = input wire := by
  let decoded := (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p)
    (decoderSuffixWires p) (oracleDegreeWires p)).runBasis
      reversibleGatePermutation input
  have restored : BasisAgreeOn
      (decoderLegalitySupportFor p (systemWires p))
      ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
        reversibleGatePermutation input) decoded := by
    simpa [decoded] using
      xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_support_restored_of_input p
        (systemWires p) (systemWires_compactDecoderInputLayout p) input
  rw [restored wire (by
    rcases member with compareMember | andMember
    · simp [decoderLegalitySupportFor, compareMember]
    · simp [decoderLegalitySupportFor, andMember])]
  change (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p)
    (decoderSuffixWires p) (oracleDegreeWires p)).runBasis
      reversibleGatePermutation input wire = input wire
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth (systemWires p)
    (decoderSuffixWires p) (oracleDegreeWires p) wire input
    (by simp) (systemWires_disjoint_decoderSuffix p)
    (systemWires_disjoint_degree p)
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p)]
  · rcases member with compareMember | andMember
    · exact (List.disjoint_left.mp
        (systemWires_disjoint_compareWork p).symm compareMember)
    · exact (List.disjoint_left.mp
        (systemWires_disjoint_andWork p).symm andMember)
  · rcases member with compareMember | andMember
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_compareWork p).symm compareMember)
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_andWork p).symm andMember)
  · rcases member with compareMember | andMember
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_compareWork p).symm compareMember)
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_andWork p).symm andMember)

/-- persistent compute も比較・AND work を任意入力値へ厳密に戻す。 -/
theorem rowOraclePersistentCompute_preserves_compareOrAnd
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ oracleCompareWorkWires p ∨
      wire ∈ oracleAndWorkWires p) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_work_eq_compactDecoder p (systemWires p) true
    input wire member]
  exact xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_preserves_compareOrAnd p input wire member

/-- sort history wire は row persistent compute の実 support 外なので保存される。 -/
theorem rowOraclePersistentCompute_preserves_sortHistory
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (instruction : TypedBitonicCompareExchange
      p.sortWordCount p.sortFlagWidth) :
    let wire : Wire p.ancillaWidth p.systemWidth := (QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input wire = input wire := by
  dsimp only
  let wire : Wire p.ancillaWidth p.systemWidth := (QLayout.oracleSlice
    (OracleWorkLayout.canonical p).sortFlags).ancillaWire instruction.history
  have outsidePresent : wire ∉ oraclePresentWires p := by
    intro presentMember
    exact laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).present
      (OracleWorkLayout.canonical p).sortFlags
      (by simp [OracleWorkLayout.canonical]; omega) instruction.history
      (by simpa [wire, oraclePresentWires, RegisterSlice.wireList] using
        presentMember)
  have differentCondition : wire ≠ oracleDegreeConditionWire p := by
    intro equal
    apply laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).degreeCondition
      (OracleWorkLayout.canonical p).sortFlags
      (by simp [OracleWorkLayout.canonical]; omega) instruction.history
    change wire ∈ _
    rw [equal]
    simp [oracleDegreeConditionWire, oracleSingletonWire,
      RegisterSlice.wireList]
  have differentOne : wire ≠ oracleOneWire p := by
    intro equal
    apply laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).constantOne
      (OracleWorkLayout.canonical p).sortFlags
      (by simp [OracleWorkLayout.canonical]; omega) instruction.history
    change wire ∈ _
    rw [equal]
    simp [oracleOneWire, oracleSingletonWire, RegisterSlice.wireList]
  rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_eq_compactDecoder_outside p (systemWires p) true
    input wire outsidePresent differentCondition differentOne]
  apply Circuit.runBasis_outside_of_usesOnly
    (compactDecoderExactSupport p (systemWires p))
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p))
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_usesOnly_exact p (systemWires p)) input wire
  intro supportMember
  have supportCases : wire ∈ systemWires p ∨ wire ∈ decoderSuffixWires p ∨
      wire ∈ oracleDegreeWires p ∨ wire ∈ oracleCompareWorkWires p ∨
      wire ∈ oracleAndWorkWires p ∨ wire = oracleLegalWire p := by
    simpa only [compactDecoderExactSupport, decoderLegalitySupportFor,
      List.mem_append, List.mem_singleton, or_assoc] using supportMember
  rcases supportCases with systemMember | suffixMember | degreeMember |
      compareMember | andMember | legalEqual
  · exact (List.disjoint_left.mp
      (systemWires_disjoint_diagonalOracleWorkWires p) systemMember)
        (diagonalOracleSlice_subset_work p
          (OracleWorkLayout.canonical p).sortFlags (by
            simp [wire, RegisterSlice.wireList]))
  · exact sortHistoryWire_not_mem_candidateSlice p instruction
      (by
        apply List.mem_of_mem_take
        simpa [decoderSuffixWires, RegisterSlice.wireList] using suffixMember)
  · exact laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).degree
      (OracleWorkLayout.canonical p).sortFlags
      (by simp [OracleWorkLayout.canonical]; omega) instruction.history
      (by simpa [wire, oracleDegreeWires, RegisterSlice.wireList] using
        degreeMember)
  · apply sortHistoryWire_not_mem_compare p instruction.history
    exact List.mem_append_left _ compareMember
  · exact (List.disjoint_left.mp (sortHistorySlice_disjoint_andSlice p)
      (sortHistoryWire_mem_sortSlice p instruction.history)) (by
        simpa [wire, oracleAndWorkWires, RegisterSlice.wireList] using andMember)
  · exact laterOracleSliceWire_not_mem_earlier p
      (OracleWorkLayout.canonical p).legal
      (OracleWorkLayout.canonical p).sortFlags
      (by simp [OracleWorkLayout.canonical]; omega) instruction.history
      (by
        change wire ∈ _
        rw [legalEqual]
        simp [oracleLegalWire, RegisterSlice.wireList])

/-- 非合法入力でも row persistent compute 後の event/sort work は clean である。 -/
theorem RowOracleIllegalInputSpec.persistentEventSortClean
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleIllegalInputSpec p basis selector input) :
    EventSortCleanInput p
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input) := by
  let output := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
    reversibleGatePermutation input
  apply EventSortCleanInput.of_agree p input output specification.eventSortClean
  · apply List.map_congr_left
    intro wire member
    exact rowOraclePersistentCompute_preserves_compareOrAnd p input wire
      (Or.inl member)
  · intro wire member
    exact rowOraclePersistentCompute_preserves_compareOrAnd p input wire
      (Or.inr (decoderComparisonAndMember p (by simp [member])))
  · exact computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_middleOracleSlice p
      (systemWires p) (systemWires_disjoint_diagonalOracleWorkWires p) true input
      (OracleWorkLayout.canonical p).positionMatch
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]) (oraclePositionWire p) (by
        simp [oraclePositionWire, RegisterSlice.wireList])
  · exact computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_middleOracleSlice p
      (systemWires p) (systemWires_disjoint_diagonalOracleWorkWires p) true input
      (OracleWorkLayout.canonical p).pair
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]) (oraclePairWire p) (by
        simp [oraclePairWire, RegisterSlice.wireList])
  · apply List.map_congr_left
    intro wire member
    simp only [sortCompareWorkWires, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with compareMember | extraMember
    · exact rowOraclePersistentCompute_preserves_compareOrAnd p input wire
        (Or.inl compareMember)
    · subst wire
      exact rowOraclePersistentCompute_preserves_compareOrAnd p input _
        (Or.inr (by simp [oracleAndWorkWires]))
  · intro wire member
    exact rowOraclePersistentCompute_preserves_compareOrAnd p input wire
      (Or.inr (by
        simpa [oracleAndWorkWires, RegisterSlice.wireList] using
          sortAndScratchWires_mem_andSlice p member))
  · intro instruction instructionMember
    exact rowOraclePersistentCompute_preserves_sortHistory p input instruction

/--
非合法入力と同じ system 基底を持つ全0 ancilla基底は、persistent support 上で入力と一致する。
-/
theorem RowOracleIllegalInputSpec.agreesZeroAncillaOnPersistentSupport
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleIllegalInputSpec p basis selector input) :
    BasisAgreeOn (oraclePersistentSupport p (systemWires p)) input
      (zeroAncillaJointBasis p basis) := by
  intro wire member
  rcases List.mem_append.mp member with systemMember | workMember
  · have values : readWires (systemWires p) input =
        readWires (systemWires p) (zeroAncillaJointBasis p basis) := by
      rw [specification.system_bits, readWires_systemWires_zeroAncilla]
    exact readWires_eq_at_of_eq _ _ _ values systemMember
  · rw [specification.work_zero wire workMember]
    rcases List.mem_map.mp workMember with ⟨index, indexMember, rfl⟩
    rfl

/-- decode不能な system 基底では compact decoder の legal flag が偽になる。 -/
theorem RowOracleIllegalInputSpec.compactLegalFalse
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleIllegalInputSpec p basis selector input)
    (illegal : decodeDelimiter basis = none) :
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
        reversibleGatePermutation input (oracleLegalWire p) = false := by
  let baseline := zeroAncillaJointBasis p basis
  let support := compactDecoderExactSupport p (systemWires p)
  have supportSubset : ∀ wire ∈ support,
      wire ∈ oraclePersistentSupport p (systemWires p) := by
    intro wire member
    rcases (by
      simpa only [support, compactDecoderExactSupport, List.mem_append,
        List.mem_singleton] using member) with decoderMember | legalEqual
    · exact decoderLegalitySupportFor_subset_persistent p (systemWires p)
        wire decoderMember
    · subst wire
      exact List.mem_append_right _
        (oracleLegalWire_mem_diagonalOracleWorkWires p)
  have inputsAgree : BasisAgreeOn support input baseline := by
    intro wire member
    exact specification.agreesZeroAncillaOnPersistentSupport wire
      (supportSubset wire member)
  have outputsAgree : BasisAgreeOn support
      ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
        reversibleGatePermutation input)
      ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
        reversibleGatePermutation baseline) := by
    exact Circuit.runBasis_congr_on_of_usesOnly support
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p))
      (by simpa [support] using
        xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_usesOnly_exact p (systemWires p))
      input baseline inputsAgree
  have baselineFalse :
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
        reversibleGatePermutation baseline (oracleLegalWire p) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro legalTrue
    have legalDelimiter :=
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_iff_isLegalDelimiter p basis).mp
        (by simpa [baseline] using legalTrue)
    exact (decodeDelimiter_eq_none_iff.mp illegal) legalDelimiter
  exact (outputsAgree (oracleLegalWire p) (by
    simp [support, compactDecoderExactSupport])).trans baselineFalse

/-- decode不能な system 基底では row persistent compute 後も legal flag が偽である。 -/
theorem RowOracleIllegalInputSpec.persistentLegalFalse
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleIllegalInputSpec p basis selector input)
    (illegal : decodeDelimiter basis = none) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input (oracleLegalWire p) = false := by
  rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_eq_compactDecoder_outside p (systemWires p) true
    input (oracleLegalWire p)]
  · exact specification.compactLegalFalse illegal
  · intro presentMember
    have legalMember : oracleLegalWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).legal).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleLegalWire, RegisterSlice.wireList]
    have presentSliceMember : oracleLegalWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).present).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oraclePresentWires, RegisterSlice.wireList] using presentMember
    exact oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).legal
      (OracleWorkLayout.canonical p).present
      (by simp [OracleWorkLayout.canonical]) legalMember presentSliceMember rfl
  · intro equal
    have legalMember : oracleLegalWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).legal).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleLegalWire, RegisterSlice.wireList]
    have conditionMember : oracleDegreeConditionWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).degreeCondition).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleDegreeConditionWire, oracleSingletonWire,
        RegisterSlice.wireList]
    exact (oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).legal
      (OracleWorkLayout.canonical p).degreeCondition
      (by simp [OracleWorkLayout.canonical]) legalMember
      conditionMember) equal
  · intro equal
    have legalMember : oracleLegalWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).legal).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleLegalWire, RegisterSlice.wireList]
    have oneMember : oracleOneWire p ∈ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).constantOne).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleOneWire, oracleSingletonWire, RegisterSlice.wireList]
    exact (oracleSliceMembers_ne_of_end_le_start p
      (OracleWorkLayout.canonical p).legal
      (OracleWorkLayout.canonical p).constantOne
      (by simp [OracleWorkLayout.canonical]; omega) legalMember oneMember) equal

/-- 非合法入力の persistent compute 後に全 row 分岐が共有する最小仕様。 -/
structure RowIllegalPersistentInputSpec (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- delimiter legal flag は偽である。 -/
  legal_false : input (oracleLegalWire p) = false
  /-- selector 比較 flag は各分岐開始時に 0 である。 -/
  selected_zero : input (oracleSelectedWire p) = false
  /-- branch flag は各分岐開始時に 0 である。 -/
  branch_zero : input (oracleBranchWire p) = false
  /-- event/sort の全 transient work は clean である。 -/
  event_clean : EventSortCleanInput p input

/-- 非合法 canonical 入力を persistent compute へ通すと共有分岐仕様が得られる。 -/
theorem RowOracleIllegalInputSpec.afterPersistent
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowOracleIllegalInputSpec p basis selector input)
    (illegal : decodeDelimiter basis = none) :
    RowIllegalPersistentInputSpec p
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation input) := by
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
    reversibleGatePermutation input
  refine {
    legal_false := specification.persistentLegalFalse illegal
    selected_zero := ?_
    branch_zero := ?_
    event_clean := specification.persistentEventSortClean }
  · rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_preCandidateSlice p (systemWires p)
      (systemWires_disjoint_diagonalOracleWorkWires p) true input
      (OracleWorkLayout.canonical p).selected]
    · exact specification.work_zero _
        (diagonalOracleSlice_subset_work p
          (OracleWorkLayout.canonical p).selected (by
            simp [oracleSelectedWire, oracleSingletonWire,
              RegisterSlice.wireList]))
    · simp [OracleWorkLayout.canonical]
      omega
    · simp [oraclePersistentSpecialSlice, OracleWorkLayout.canonical]
    · simp [OracleWorkLayout.canonical]
    · simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
  · rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_middleOracleSlice p (systemWires p)
      (systemWires_disjoint_diagonalOracleWorkWires p) true input
      (OracleWorkLayout.canonical p).branch]
    · exact specification.work_zero _
        (diagonalOracleSlice_subset_work p
          (OracleWorkLayout.canonical p).branch (by
            simp [oracleBranchWire, oracleSingletonWire,
              RegisterSlice.wireList]))
    · simp [OracleWorkLayout.canonical]
      omega
    · simp [OracleWorkLayout.canonical]
      omega
    · simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList]

/-- 非合法 persistent 状態は任意 slot の対角分岐 clean 条件を満たす。 -/
theorem RowIllegalPersistentInputSpec.diagonalClean
    {p : QParameters} {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : RowIllegalPersistentInputSpec p input)
    (slot : Fin p.K) :
    DiagonalBranchCleanInput p slot false
      (input (oraclePresentWireAt p slot)) input := by
  exact {
    scratch_zero := specification.event_clean.moved_selector.scratch_zero
    selected_zero := specification.selected_zero
    branch_zero := specification.branch_zero
    legal_value := specification.legal_false
    present_value := rfl }

/-- legal=false の persistent 状態では任意 row event 分岐が恒等作用になる。 -/
theorem applyRowEventReferenceAndRestoreWorkCircuit_illegal_identity
    (p : QParameters) (slot : Fin p.K) (offset : Fin 6)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowIllegalPersistentInputSpec p input) :
    (applyRowEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  let states := rowEventPredecessorCandidateUpdateAndSortExecutionTrace p slot offset input
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_rowEventSelectorCompute p slot offset input
      specification.event_clean
  have movedClean : EventSortCleanInput p states.afterMoveBackward := by
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.moved_eq]
      exact EventSortCleanInput.of_rowEventMovedCopy p slot _ selectorClean
    rw [states.moveBackward_eq]
    exact EventSortCleanInput.of_rowEventMoveBackward p offset _ copiedClean
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    rw [states.membership_eq]
    exact EventSortCleanInput.of_rowEventMembership p slot _ movedClean
  have branchZeroAfterMembership : states.afterMembership
      (oracleBranchWire p) = false := by
    have afterMoveValues :=
      rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMoveBackward_laterSlice p slot offset input
        specification.event_clean (OracleWorkLayout.canonical p).branch (by
          simp [OracleWorkLayout.canonical]
          omega)
    have afterMoveZero : states.afterMoveBackward (oracleBranchWire p) = false :=
      (readWires_eq_at_of_eq _ _ _ afterMoveValues (by
        simp [oracleBranchWire, oracleSingletonWire,
          RegisterSlice.wireList])).trans specification.branch_zero
    rw [states.membership_eq]
    exact (runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other p (systemWires p)
      (systemWires_membershipInputLayout p) slot false states.afterMoveBackward
      {
        equalWork_zero := movedClean.moved_selector.compare_zero
        scratch_zero := movedClean.moved_selector.scratch_zero }
      (oracleBranchWire p)
      (MembershipOutputsSeparated.of_laterSlice p
        (OracleWorkLayout.canonical p).branch (by
          simp [OracleWorkLayout.canonical]) (oracleBranchWire p) (by
            simp [oracleBranchWire, oracleSingletonWire,
              RegisterSlice.wireList]))).trans afterMoveZero
  have legalAfterMembership : states.afterMembership (oracleLegalWire p) = false := by
    have membershipValues := rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterMembership_earlierSlice
      p slot offset input specification.event_clean
        (OracleWorkLayout.canonical p).legal (by
          simp [OracleWorkLayout.canonical]
          omega)
    have legalAfterMove : states.afterMoveBackward (oracleLegalWire p) = false := by
      have legalOutsideMoved : oracleLegalWire p ∉ ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).moved).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
        intro movedMember
        have legalMember : oracleLegalWire p ∈ ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).legal).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
          simp [oracleLegalWire, RegisterSlice.wireList]
        exact (List.disjoint_left.mp
          (RegisterSlice.wireList_disjoint_of_end_le_start
            (QLayout.oracleSlice (OracleWorkLayout.canonical p).legal)
            (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
            (by
              simp [QLayout.oracleSlice, RegisterSlice.compose,
                OracleWorkLayout.canonical]
              omega))) legalMember movedMember
      have legalDifferentSelected : oracleLegalWire p ≠ oracleSelectedWire p := by
        have legalMember : oracleLegalWire p ∈ ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).legal).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
          simp [oracleLegalWire, RegisterSlice.wireList]
        have selectedMember : oracleSelectedWire p ∈ ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).selected).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
          simp [oracleSelectedWire, oracleSingletonWire,
            RegisterSlice.wireList]
        exact oracleSliceMembers_ne_of_end_le_start p
          (OracleWorkLayout.canonical p).legal
          (OracleWorkLayout.canonical p).selected
          (by simp [OracleWorkLayout.canonical]; omega) legalMember selectedMember
      calc
        states.afterMoveBackward (oracleLegalWire p) =
            states.afterSelector (oracleLegalWire p) := by
          rw [states.moveBackward_eq, states.moved_eq]
          exact runBasis_rowEventMovedComputation_outside_movedSlice p slot offset
            states.afterSelector selectorClean _ legalOutsideMoved
        _ = input (oracleLegalWire p) := by
          rw [states.selector_eq]
          exact runBasis_rowEventSelectorCompute_other p slot offset input
            specification.event_clean _ legalDifferentSelected
        _ = false := specification.legal_false
    exact (readWires_eq_at_of_eq _ _ _ membershipValues (by
      simp [oracleLegalWire, RegisterSlice.wireList])).trans legalAfterMove
  have branchFalse : states.afterBranch (oracleBranchWire p) = false := by
    rw [states.branch_eq]
    exact runBasis_rowEventBranchCompute_false_of_legal_canonical p slot offset
      states.afterMembership membershipClean.moved_selector.scratch_zero
      branchZeroAfterMembership legalAfterMembership
  apply applyRowEventReferenceAndRestoreWorkCircuit_inactive_of_afterBranch p slot offset input
  · exact rowEventPredecessorCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input
      specification.event_clean
  · exact branchFalse

/-- legal=false の persistent 状態では任意 selector の row 分岐が恒等作用になる。 -/
theorem dispatchRowSelectorToDiagonalOrEventCircuit_illegal_identity
    (p : QParameters) (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowIllegalPersistentInputSpec p input) :
    (dispatchRowSelectorToDiagonalOrEventCircuit p selector).runBasis reversibleGatePermutation input =
      input := by
  let slot := selectorSlot selector
  let offset := selectorOffset selector
  unfold dispatchRowSelectorToDiagonalOrEventCircuit
  by_cases diagonal : offset.val < 2
  · rw [dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal p slot offset diagonal]
    exact rowDiagonalResultComputeUseUncomputeCircuit_illegal_identity p slot
      ⟨offset.val, diagonal⟩ (input (oraclePresentWireAt p slot)) input
        (specification.diagonalClean slot)
  · rw [dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_event p slot offset diagonal]
    exact applyRowEventReferenceAndRestoreWorkCircuit_illegal_identity p slot offset input specification

/--
decode不能な system 基底・canonical row selector・全0 oracle workでは、全 `6K` 分岐と
persistent compute--uncomputeを含むrow oracle全体が基底状態を厳密に保存する。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_illegal_identity
    (p : QParameters) (basis : RegisterBasis p.systemWidth)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOracleIllegalInputSpec p basis selector input)
    (illegal : decodeDelimiter basis = none) :
    (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input =
      input := by
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
    reversibleGatePermutation input
  have persistentSpecification : RowIllegalPersistentInputSpec p persistent := by
    simpa [persistent] using specification.afterPersistent illegal
  apply applyRowOracleReferenceAndRestoreWorkCircuit_eq_input_of_eachBranch p input
  intro branch
  exact dispatchRowSelectorToDiagonalOrEventCircuit_illegal_identity p branch persistent
    persistentSpecification

end ReversibleCircuit

end ProbabilityGeneratorQProof
