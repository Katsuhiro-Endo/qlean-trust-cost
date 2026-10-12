import QLean.Generator.Implementation.BitonicSortCorrectness
import QLean.Generator.Implementation.QOracleCircuit

/-!
# column・row oracle回路の基底作用証明

oracleを構成するcontrolled copy、定数XOR、membership、candidate生成から順に、
純粋参照関数との一致とwork-clean性を全状態列挙なしで証明する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 物理system wire列の長さはQ回路のsystem幅に一致する。 -/
@[simp] theorem systemWires_length (p : QParameters) :
    (systemWires p).length = p.systemWidth := by
  simp [systemWires]

/-- 物理system wire列には重複がない。 -/
theorem systemWires_nodup (p : QParameters) : (systemWires p).Nodup := by
  apply List.Nodup.map
  · intro left right equal
    exact Wire.system.inj equal
  · exact List.nodup_finRange p.systemWidth

/-- 全0アンシラと結合した基底でsystem wire列を読むと、元のsystem bit列になる。 -/
theorem readWires_systemWires_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    readWires (systemWires p) (zeroAncillaJointBasis p system) =
      registerBitList system := by
  simp [readWires, systemWires, registerBitList, QLayout.systemWire]

/-- system wireをword分割して読むと、元の物理bit列を同じ幅で分割した結果になる。 -/
theorem readWires_splitSystemWords_system_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    (splitSystemWords p.wordWidth p.K (systemWires p)).map
        (fun word => readWires word (zeroAncillaJointBasis p system)) =
      splitBitWords p.wordWidth p.K (registerBitList system) := by
  rw [readWires_splitSystemWords]
  rw [readWires_systemWires_zeroAncilla]

/-- system wire列を`K`分割した各wordは一般`q,K`で正確に`2q`本を持つ。 -/
theorem splitSystemWords_system_word_length (p : QParameters) :
    ∀ word ∈ splitSystemWords p.wordWidth p.K (systemWires p),
      word.length = p.wordWidth := by
  intro word member
  rcases List.mem_map.mp member with ⟨slot, slotMember, rfl⟩
  have slotLt : slot < p.K := List.mem_range.mp slotMember
  have enough : slot * p.wordWidth + p.wordWidth ≤ p.systemWidth := by
    calc
      slot * p.wordWidth + p.wordWidth = (slot + 1) * p.wordWidth := by
        rw [Nat.succ_mul]
      _ ≤ p.K * p.wordWidth :=
        Nat.mul_le_mul_right p.wordWidth (Nat.succ_le_of_lt slotLt)
      _ = p.wordWidth * p.K := Nat.mul_comm _ _
      _ ≤ p.wordWidth * p.K + 1 := Nat.le_succ _
      _ = p.systemWidth := rfl
  rw [List.length_take, List.length_drop]
  rw [systemWires_length]
  have enough' : p.wordWidth + slot * p.wordWidth ≤ p.systemWidth := by
    simpa [Nat.add_comm] using enough
  exact Nat.min_eq_left (Nat.le_sub_of_add_le enough')

/-- 物理system wire列とdecoder比較work sliceは互いに素である。 -/
theorem systemWires_disjoint_compareWork (p : QParameters) :
    (systemWires p).Disjoint (oracleCompareWorkWires p) := by
  let compareSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork
  simpa [systemWires, QLayout.systemWire, oracleCompareWorkWires,
    RegisterSlice.wireList, compareSlice] using
    (RegisterSlice.systemWires_disjoint_wireList
      (systemWidth := p.systemWidth) compareSlice)

/-- 物理system wire列とdegree sliceは互いに素である。 -/
theorem systemWires_disjoint_degree (p : QParameters) :
    (systemWires p).Disjoint (oracleDegreeWires p) := by
  let degreeSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
  simpa [systemWires, QLayout.systemWire, oracleDegreeWires,
    RegisterSlice.wireList, degreeSlice] using
    (RegisterSlice.systemWires_disjoint_wireList
      (systemWidth := p.systemWidth) degreeSlice)

/-- 物理system wire列とAND work sliceは互いに素である。 -/
theorem systemWires_disjoint_andWork (p : QParameters) :
    (systemWires p).Disjoint (oracleAndWorkWires p) := by
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  simpa [systemWires, QLayout.systemWire, oracleAndWorkWires,
    RegisterSlice.wireList, andSlice] using
    (RegisterSlice.systemWires_disjoint_wireList
      (systemWidth := p.systemWidth) andSlice)

/-- 物理system wire列とdecoder suffix scratch列は互いに素である。 -/
theorem systemWires_disjoint_decoderSuffix (p : QParameters) :
    (systemWires p).Disjoint (decoderSuffixWires p) := by
  let candidateSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  have fullDisjoint :
      (systemWires p).Disjoint
        (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [systemWires, QLayout.systemWire] using
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) candidateSlice)
  rw [List.disjoint_left]
  intro wire systemMember suffixMember
  apply (List.disjoint_left.mp fullDisjoint systemMember)
  exact List.mem_of_mem_take suffixMember

/-- 標準入力ではdecoder suffix scratch列は全0である。 -/
theorem readWires_decoderSuffix_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    readWires (decoderSuffixWires p) (zeroAncillaJointBasis p system) =
      List.replicate (decoderSuffixWires p).length false := by
  let candidateSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  apply readWires_eq_replicate_false_of_forall
  intro wire member
  have fullMember : wire ∈
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply List.mem_of_mem_take member
  rcases List.mem_map.mp fullMember with ⟨index, _, rfl⟩
  rfl

/-- 標準入力ではdegree wire列は全0である。 -/
theorem readWires_oracleDegree_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    readWires (oracleDegreeWires p) (zeroAncillaJointBasis p system) =
      List.replicate (oracleDegreeWires p).length false := by
  apply readWires_eq_replicate_false_of_forall
  intro wire member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  rfl

/-- 標準入力では比較work wire列は全0である。 -/
theorem readWires_oracleCompare_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    readWires (oracleCompareWorkWires p) (zeroAncillaJointBasis p system) =
      List.replicate (oracleCompareWorkWires p).length false := by
  apply readWires_eq_replicate_false_of_forall
  intro wire member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  rfl

/-- 標準入力ではAND work sliceに属する任意のwireが0である。 -/
theorem zeroAncilla_oracleAndWork_member
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ oracleAndWorkWires p) :
    zeroAncillaJointBasis p system wire = false := by
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  rfl

/-- 標準入力ではdecoder less flag列は全0である。 -/
theorem readWires_decoderLess_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    readWires (decoderLessWires p) (zeroAncillaJointBasis p system) =
      List.replicate (decoderLessWires p).length false := by
  apply readWires_eq_replicate_false_of_forall
  intro wire member
  apply zeroAncilla_oracleAndWork_member p system
  exact decoderComparisonAndMember p
    (by simp [decoderComparisonFlagWires, member])

/-- 標準入力ではdecoder need flag列は全0である。 -/
theorem readWires_decoderNeed_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    readWires (decoderNeedWires p) (zeroAncillaJointBasis p system) =
      List.replicate (decoderNeedWires p).length false := by
  apply readWires_eq_replicate_false_of_forall
  intro wire member
  apply zeroAncilla_oracleAndWork_member p system
  exact decoderComparisonAndMember p
    (by simp [decoderComparisonFlagWires, member])

/-- 標準入力ではdecoder good flag列は全0である。 -/
theorem readWires_decoderGood_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    readWires (decoderGoodWires p) (zeroAncillaJointBasis p system) =
      List.replicate (decoderGoodWires p).length false := by
  apply readWires_eq_replicate_false_of_forall
  intro wire member
  apply zeroAncilla_oracleAndWork_member p system
  exact decoderComparisonAndMember p
    (by simp [decoderComparisonFlagWires, member])

/-- 標準入力ではdecoderのAND scratch各wireが0である。 -/
theorem decoderAndScratch_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    ∀ wire ∈ decoderAndScratchWires p,
      zeroAncillaJointBasis p system wire = false := by
  intro wire member
  apply zeroAncilla_oracleAndWork_member p system
  exact decoderComparisonAndMember p (by simp [member])

/-- system word列を含む実decoder比較support全体にはwire重複がない。 -/
theorem decoderComparisonSupport_system_nodup (p : QParameters) :
    (decoderComparisonSupport
      (oracleDegreeWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p)
      (splitSystemWords p.wordWidth p.K (systemWires p))
      (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p)).Nodup := by
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let systemPrefix := words.flatten
  let ancillaSupport :=
    oracleCompareWorkWires p ++ decoderAndScratchWires p ++
      oracleDegreeWires p ++ decoderLessWires p ++ decoderNeedWires p ++
      decoderGoodWires p
  have prefixEq : systemPrefix = (systemWires p).take (p.K * p.wordWidth) := by
    exact flatten_splitSystemWords p.wordWidth p.K (systemWires p)
  have prefixNodup : systemPrefix.Nodup := by
    rw [prefixEq]
    exact (systemWires_nodup p).take
  have ancillaNodup : ancillaSupport.Nodup := by
    simpa [ancillaSupport] using decoderComparisonAncilla_nodup p
  have systemDisjointCompare :
      (systemWires p).Disjoint (oracleCompareWorkWires p) := by
    let compareSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork
    simpa [systemWires, QLayout.systemWire, oracleCompareWorkWires,
      RegisterSlice.wireList, compareSlice] using
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) compareSlice)
  have systemDisjointDegree :
      (systemWires p).Disjoint (oracleDegreeWires p) := by
    let degreeSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
    simpa [systemWires, QLayout.systemWire, oracleDegreeWires,
      RegisterSlice.wireList, degreeSlice] using
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) degreeSlice)
  have systemDisjointAnd :
      (systemWires p).Disjoint (oracleAndWorkWires p) := by
    let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
    simpa [systemWires, QLayout.systemWire, oracleAndWorkWires,
      RegisterSlice.wireList, andSlice] using
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) andSlice)
  have separated :
      ∀ systemWire ∈ systemPrefix, ∀ ancillaWire ∈ ancillaSupport,
        systemWire ≠ ancillaWire := by
    intro systemWire systemMember ancillaWire ancillaMember
    have systemFull : systemWire ∈ systemWires p := by
      rw [prefixEq] at systemMember
      exact List.mem_of_mem_take systemMember
    have ancillaCases :
        ancillaWire ∈ oracleCompareWorkWires p ∨
        ancillaWire ∈ decoderAndScratchWires p ∨
        ancillaWire ∈ oracleDegreeWires p ∨
        ancillaWire ∈ decoderLessWires p ∨
        ancillaWire ∈ decoderNeedWires p ∨
        ancillaWire ∈ decoderGoodWires p := by
      simpa only [ancillaSupport, List.mem_append, or_assoc] using ancillaMember
    rcases ancillaCases with compareMember | scratchMember | degreeMember |
      lessMember | needMember | goodMember
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp systemDisjointCompare systemFull) compareMember
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp systemDisjointAnd systemFull)
        (decoderComparisonAndMember p (by simp [scratchMember]))
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp systemDisjointDegree systemFull) degreeMember
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp systemDisjointAnd systemFull)
        (decoderComparisonAndMember p
          (by simp [decoderComparisonFlagWires, lessMember]))
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp systemDisjointAnd systemFull)
        (decoderComparisonAndMember p
          (by simp [decoderComparisonFlagWires, needMember]))
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp systemDisjointAnd systemFull)
        (decoderComparisonAndMember p
          (by simp [decoderComparisonFlagWires, goodMember]))
  have supportNodup : (systemPrefix ++ ancillaSupport).Nodup :=
    List.nodup_append.mpr ⟨prefixNodup, ancillaNodup, separated⟩
  simpa [decoderComparisonSupport, words, systemPrefix, ancillaSupport,
    List.append_assoc] using supportNodup

/-- 実際のsystem隣接比較回路は、その明示的な有限supportだけを使用する。 -/
theorem decoderComparisonSequence_usesOnly_system (p : QParameters) :
    circuitUsesOnly
      (decoderComparisonSupport
        (oracleDegreeWires p) (oracleCompareWorkWires p)
        (decoderAndScratchWires p)
        (splitSystemWords p.wordWidth p.K (systemWires p))
        (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p))
      (decoderComparisonSequence
        (oracleDegreeWires p) (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0
        (splitSystemWords p.wordWidth p.K (systemWires p))
        (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p)) := by
  apply circuitUsesOnly_decoderComparisonSequence
  · intro wire member
    simp [decoderComparisonSupport, member]
  · intro wire member
    simp [decoderComparisonSupport, member]
  · intro wire member
    simp [decoderComparisonSupport, member]
  · intro word wordMember wire wireMember
    simp only [decoderComparisonSupport, List.mem_append, or_assoc]
    exact Or.inl (List.mem_flatten.mpr ⟨word, wordMember, wireMember⟩)
  · intro wire member
    simp [decoderComparisonSupport, member]
  · intro wire member
    simp [decoderComparisonSupport, member]
  · intro wire member
    simp [decoderComparisonSupport, member]

/--
AND work内の特殊wireが比較scratch・保持flagに含まれなければ、実比較support全体の外にある。
-/
theorem oracleAndSpecial_not_mem_decoderComparisonSupport
    (p : QParameters) (special : Wire p.ancillaWidth p.systemWidth)
    (memberAnd : special ∈ oracleAndWorkWires p)
    (freshComparisonAnd : special ∉
      decoderAndScratchWires p ++ decoderComparisonFlagWires p) :
    special ∉ decoderComparisonSupport
      (oracleDegreeWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p)
      (splitSystemWords p.wordWidth p.K (systemWires p))
      (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p) := by
  intro member
  have supportCases :
      special ∈ (splitSystemWords p.wordWidth p.K (systemWires p)).flatten ∨
      special ∈ oracleCompareWorkWires p ∨
      special ∈ decoderAndScratchWires p ∨
      special ∈ oracleDegreeWires p ∨
      special ∈ decoderLessWires p ∨
      special ∈ decoderNeedWires p ∨
      special ∈ decoderGoodWires p := by
    simpa only [decoderComparisonSupport, List.mem_append, or_assoc] using member
  rcases supportCases with systemMember | compareMember | scratchMember |
      degreeMember | lessMember | needMember | goodMember
  · have systemFull : special ∈ systemWires p := by
      rw [flatten_splitSystemWords] at systemMember
      exact List.mem_of_mem_take systemMember
    exact (List.disjoint_left.mp (systemWires_disjoint_andWork p) systemFull)
      memberAnd
  · exact (List.disjoint_left.mp (oracleCompareWorkWires_disjoint_andWork p)
      compareMember) memberAnd
  · apply freshComparisonAnd
    simp [scratchMember]
  · exact (List.disjoint_left.mp (oracleDegreeWires_disjoint_andWork p)
      degreeMember) memberAnd
  · apply freshComparisonAnd
    simp [decoderComparisonFlagWires, lessMember]
  · apply freshComparisonAnd
    simp [decoderComparisonFlagWires, needMember]
  · apply freshComparisonAnd
    simp [decoderComparisonFlagWires, goodMember]

/-- degree-valid wireは実decoder比較supportの外にある。 -/
theorem decoderDegreeValid_not_mem_comparisonSupport_system (p : QParameters) :
    decoderDegreeValidWire p ∉ decoderComparisonSupport
      (oracleDegreeWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p)
      (splitSystemWords p.wordWidth p.K (systemWires p))
      (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p) := by
  exact oracleAndSpecial_not_mem_decoderComparisonSupport p
    (decoderDegreeValidWire p) (decoderDegreeValid_mem_andWork p)
    (decoderDegreeValid_not_mem_comparisonAnd p)

/-- legal-temporary wireは実decoder比較supportの外にある。 -/
theorem decoderLegalTemporary_not_mem_comparisonSupport_system (p : QParameters) :
    decoderLegalTemporaryWire p ∉ decoderComparisonSupport
      (oracleDegreeWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p)
      (splitSystemWords p.wordWidth p.K (systemWires p))
      (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p) := by
  exact oracleAndSpecial_not_mem_decoderComparisonSupport p
    (decoderLegalTemporaryWire p) (decoderLegalTemporary_mem_andWork p)
    (decoderLegalTemporary_not_mem_comparisonAnd p)

/-- 合法delimiterの標準入力をdegree decodeすると、degree列は粒子数one-hotになる。 -/
theorem readWires_degreeDecode_delimiter_system
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input
    readWires (oracleDegreeWires p) decoded =
      degreeOneHotFrom p.K configuration.1.card 0 := by
  dsimp only
  have result := readWires_xorDelimiterDegreeOneHotIntoTargetsCircuit_delimiterEncoding configuration
    (systemWires p) (decoderSuffixWires p) (oracleDegreeWires p)
    (zeroAncillaJointBasis p (delimiterEncoding configuration))
    (by simp) (systemWires_disjoint_decoderSuffix p)
    (systemWires_disjoint_degree p)
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p) (oracleDegreeWires_nodup p)
    (readWires_decoderSuffix_zeroAncilla p (delimiterEncoding configuration))
    (readWires_oracleDegree_zeroAncilla p (delimiterEncoding configuration))
    (readWires_systemWires_zeroAncilla p (delimiterEncoding configuration))
  simpa using result

/-- 合法delimiterのdegree one-hot parity回路はdegree-valid wireを正確に反転する。 -/
theorem decoderDegreeValid_after_degreeDecode
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded =
      xBasisAction (decoderDegreeValidWire p) decoded := by
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
  rw [readWires_degreeDecode_delimiter_system p configuration]
  rw [boolParity_degreeOneHot_configuration configuration]
  rfl

/-- degree decode後も比較work sliceは全0のままである。 -/
theorem oracleCompare_zero_after_degreeDecode
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input
    ∀ wire ∈ oracleCompareWorkWires p, decoded wire = false := by
  dsimp only
  intro wire member
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth (systemWires p)
    (decoderSuffixWires p) (oracleDegreeWires p) wire
    (zeroAncillaJointBasis p (delimiterEncoding configuration)) (by simp)
    (systemWires_disjoint_decoderSuffix p) (systemWires_disjoint_degree p)
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p)]
  · rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl
  · exact (List.disjoint_left.mp (systemWires_disjoint_compareWork p).symm member)
  · exact (List.disjoint_left.mp
      (decoderSuffixWires_disjoint_compareWork p).symm member)
  · exact (List.disjoint_left.mp
      (oracleDegreeWires_disjoint_compareWork p).symm member)

/-- degree decode後もAND work sliceは全0のままである。 -/
theorem oracleAndWork_zero_after_degreeDecode
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input
    ∀ wire ∈ oracleAndWorkWires p, decoded wire = false := by
  dsimp only
  intro wire member
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth (systemWires p)
    (decoderSuffixWires p) (oracleDegreeWires p) wire
    (zeroAncillaJointBasis p (delimiterEncoding configuration)) (by simp)
    (systemWires_disjoint_decoderSuffix p) (systemWires_disjoint_degree p)
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p)]
  · exact zeroAncilla_oracleAndWork_member p (delimiterEncoding configuration)
      member
  · exact (List.disjoint_left.mp (systemWires_disjoint_andWork p).symm member)
  · exact (List.disjoint_left.mp (decoderSuffixWires_disjoint_andWork p).symm member)
  · exact (List.disjoint_left.mp (oracleDegreeWires_disjoint_andWork p).symm member)

/--
合法delimiterをdegree decodeした直後に実際の隣接比較基本ゲート列を実行すると、
全`K-1`本のgood flagが1になる。外部oracle契約や基底列挙は用いない。
-/
theorem decoderComparison_good_after_degreeDecode
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    readWires (decoderGoodWires p)
        ((decoderComparisonSequence degree (oracleCompareWorkWires p)
          (decoderAndScratchWires p) 0 words (decoderLessWires p)
          (decoderNeedWires p) (decoderGoodWires p)).runBasis
          reversibleGatePermutation decoded) =
      List.replicate (p.K - 1) true := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let inputWires := systemWires p
  let suffix := decoderSuffixWires p
  let degree := oracleDegreeWires p
  let compare := oracleCompareWorkWires p
  let scratch := decoderAndScratchWires p
  let words := splitSystemWords p.wordWidth p.K inputWires
  let less := decoderLessWires p
  let need := decoderNeedWires p
  let good := decoderGoodWires p
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires suffix degree).runBasis
      reversibleGatePermutation input
  have inputDisjointSuffix : inputWires.Disjoint suffix := by
    simpa [inputWires, suffix] using systemWires_disjoint_decoderSuffix p
  have inputDisjointDegree : inputWires.Disjoint degree := by
    simpa [inputWires, degree] using systemWires_disjoint_degree p
  have suffixDisjointDegree : suffix.Disjoint degree := by
    simpa [suffix, degree] using
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
  have sameLength : inputWires.length = suffix.length := by
    simp [inputWires, suffix]
  have degreeValues :
      readWires degree decoded =
        degreeOneHotFrom degree.length configuration.1.card 0 := by
    exact readWires_xorDelimiterDegreeOneHotIntoTargetsCircuit_delimiterEncoding configuration
      inputWires suffix degree input sameLength inputDisjointSuffix
      inputDisjointDegree suffixDisjointDegree (decoderSuffixWires_nodup p)
      (oracleDegreeWires_nodup p)
      (by simpa [input, suffix] using
        readWires_decoderSuffix_zeroAncilla p (delimiterEncoding configuration))
      (by simpa [input, degree] using
        readWires_oracleDegree_zeroAncilla p (delimiterEncoding configuration))
      (by simpa [input, inputWires] using
        readWires_systemWires_zeroAncilla p (delimiterEncoding configuration))
  have wordValues :
      words.map (fun word => readWires word decoded) =
        splitBitWords p.wordWidth p.K
          (registerBitList (delimiterEncoding configuration)) := by
    calc
      words.map (fun word => readWires word decoded) =
          words.map (fun word => readWires word input) := by
        apply List.map_congr_left
        intro word wordMember
        apply List.map_congr_left
        intro wire wireMember
        apply runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_input_wire p.wordWidth inputWires suffix
          degree wire input inputDisjointSuffix inputDisjointDegree
          suffixDisjointDegree
        rcases List.mem_map.mp wordMember with ⟨slot, _, rfl⟩
        exact List.mem_of_mem_drop (List.mem_of_mem_take wireMember)
      _ = splitBitWords p.wordWidth p.K
          (registerBitList (delimiterEncoding configuration)) := by
        simpa [words, inputWires, input] using
          readWires_splitSystemWords_system_zeroAncilla p
            (delimiterEncoding configuration)
  have compareAfterZero : ∀ wire ∈ compare, decoded wire = false := by
    intro wire member
    change
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires suffix degree).runBasis
        reversibleGatePermutation input wire = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires suffix degree
      wire input sameLength inputDisjointSuffix inputDisjointDegree
      suffixDisjointDegree (decoderSuffixWires_nodup p)]
    · rcases List.mem_map.mp member with ⟨index, _, rfl⟩
      rfl
    · exact (List.disjoint_left.mp
        (systemWires_disjoint_compareWork p).symm member)
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_compareWork p).symm member)
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_compareWork p).symm member)
  have andAfterZero : ∀ wire ∈ oracleAndWorkWires p, decoded wire = false := by
    intro wire member
    change
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires suffix degree).runBasis
        reversibleGatePermutation input wire = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires suffix degree
      wire input sameLength inputDisjointSuffix inputDisjointDegree
      suffixDisjointDegree (decoderSuffixWires_nodup p)]
    · exact zeroAncilla_oracleAndWork_member p
        (delimiterEncoding configuration) member
    · exact (List.disjoint_left.mp
        (systemWires_disjoint_andWork p).symm member)
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_andWork p).symm member)
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_andWork p).symm member)
  have compareZero :
      readWires compare decoded = List.replicate compare.length false := by
    exact readWires_eq_replicate_false_of_forall compare decoded compareAfterZero
  have scratchZero : ∀ wire ∈ scratch, decoded wire = false := by
    intro wire member
    apply andAfterZero wire
    exact decoderComparisonAndMember p (by simp [scratch, member])
  have lessZero :
      readWires less decoded = List.replicate less.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply andAfterZero wire
    exact decoderComparisonAndMember p
      (by simp [less, decoderComparisonFlagWires, member])
  have needZero :
      readWires need decoded = List.replicate need.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply andAfterZero wire
    exact decoderComparisonAndMember p
      (by simp [need, decoderComparisonFlagWires, member])
  have goodZero :
      readWires good decoded = List.replicate good.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    apply andAfterZero wire
    exact decoderComparisonAndMember p
      (by simp [good, decoderComparisonFlagWires, member])
  have wordCount : words.length = good.length + 1 := by
    simp [words, good, splitSystemWords]
    omega
  have lessCount : less.length = good.length := by simp [less, good]
  have needCount : need.length = good.length := by simp [need, good]
  have wordLengths : ∀ word ∈ words, word.length = compare.length := by
    intro word member
    rw [show word.length = p.wordWidth by
      exact splitSystemWords_system_word_length p word (by simpa [words, inputWires]
        using member)]
    simp [compare]
  have supportNodup :
      (decoderComparisonSupport degree compare scratch words less need good).Nodup := by
    simpa [degree, compare, scratch, words, less, need, good, inputWires] using
      decoderComparisonSupport_system_nodup p
  have circuitGood := readWires_decoderComparisonSequence_good
    degree compare scratch 0 words less need good decoded wordCount lessCount
    needCount wordLengths supportNodup compareZero scratchZero lessZero needZero
    goodZero (by simpa [compare, scratch] using
      decoderAndScratchWires_wordWidth_le p)
  calc
    readWires good
        ((decoderComparisonSequence degree compare scratch 0 words less need good).runBasis
          reversibleGatePermutation decoded) =
        decoderExpectedGoodBits (readWires degree decoded) 0
          (words.map fun word => readWires word decoded) := circuitGood
    _ = decoderExpectedGoodBits
          (degreeOneHotFrom p.K configuration.1.card 0) 0
          (splitBitWords p.wordWidth p.K
            (registerBitList (delimiterEncoding configuration))) := by
      rw [degreeValues, wordValues]
      simp [degree]
    _ = List.replicate (p.K - 1) true :=
      decoderExpectedGoodBits_delimiterEncoding configuration

/--
合法delimiterのdegree decode後に隣接比較基本ゲート列を実行しても、
共有AND scratchは全て0へ戻る。したがって後続の多重制御ANDへ再利用できる。
-/
theorem decoderComparison_scratch_clean_after_degreeDecode
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let compared :=
      (decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation decoded
    ∀ wire ∈ decoderAndScratchWires p, compared wire = false := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let compare := oracleCompareWorkWires p
  let scratch := decoderAndScratchWires p
  let less := decoderLessWires p
  let need := decoderNeedWires p
  let good := decoderGoodWires p
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  have compareAfterZero : ∀ wire ∈ compare, decoded wire = false := by
    simpa [compare, decoded, degree, input] using
      oracleCompare_zero_after_degreeDecode p configuration
  have andAfterZero : ∀ wire ∈ oracleAndWorkWires p, decoded wire = false := by
    simpa [decoded, degree, input] using
      oracleAndWork_zero_after_degreeDecode p configuration
  have compareZero :
      readWires compare decoded = List.replicate compare.length false :=
    readWires_eq_replicate_false_of_forall compare decoded compareAfterZero
  have scratchZero : ∀ wire ∈ scratch, decoded wire = false := by
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p (by simp [scratch, member]))
  have lessZero :
      readWires less decoded = List.replicate less.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p
      (by simp [less, decoderComparisonFlagWires, member]))
  have needZero :
      readWires need decoded = List.replicate need.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p
      (by simp [need, decoderComparisonFlagWires, member]))
  have goodZero :
      readWires good decoded = List.replicate good.length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    exact andAfterZero wire (decoderComparisonAndMember p
      (by simp [good, decoderComparisonFlagWires, member]))
  have wordCount : words.length = good.length + 1 := by
    simp [words, good, splitSystemWords]
    omega
  have lessCount : less.length = good.length := by simp [less, good]
  have needCount : need.length = good.length := by simp [need, good]
  have wordLengths : ∀ word ∈ words, word.length = compare.length := by
    intro word member
    rw [show word.length = p.wordWidth by
      exact splitSystemWords_system_word_length p word (by simpa [words] using member)]
    simp [compare]
  have supportNodup :
      (decoderComparisonSupport degree compare scratch words less need good).Nodup := by
    simpa [degree, compare, scratch, words, less, need, good] using
      decoderComparisonSupport_system_nodup p
  exact runBasis_decoderComparisonSequence_scratch_clean degree compare scratch 0
    words less need good decoded wordCount lessCount needCount wordLengths
    supportNodup compareZero scratchZero lessZero needZero goodZero
    (by simpa [compare, scratch] using decoderAndScratchWires_wordWidth_le p)

/-- degree-validを先に計算しても、比較回路のsupport上の結果は変わらない。 -/
theorem decoderComparison_after_degreeValid_agrees_on_support
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
      (decoderAndScratchWires p) words (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p)
    let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
      (decoderAndScratchWires p) 0 words (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p)
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let degreePrepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    BasisAgreeOn support
      (comparison.runBasis reversibleGatePermutation degreePrepared)
      (comparison.runBasis reversibleGatePermutation decoded) := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have preparedEq :
      degreePrepared = xBasisAction (decoderDegreeValidWire p) decoded := by
    simpa [degreePrepared, decoded, degree, input] using
      decoderDegreeValid_after_degreeDecode p configuration
  have beforeAgree : BasisAgreeOn support degreePrepared decoded := by
    intro wire member
    rw [preparedEq]
    apply xBasisAction_other
    intro equal
    subst wire
    exact decoderDegreeValid_not_mem_comparisonSupport_system p (by
      simpa [support, degree, words] using member)
  apply Circuit.runBasis_congr_on_of_usesOnly support comparison
  · simpa [support, comparison, degree, words] using
      decoderComparisonSequence_usesOnly_system p
  · exact beforeAgree

/-- degree-valid計算後の実比較列でもgood flagは全て1になる。 -/
theorem decoderComparison_good_after_degreeValid
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let degreePrepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    readWires (decoderGoodWires p)
      ((decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation degreePrepared) =
      List.replicate (p.K - 1) true := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have agree : BasisAgreeOn support
      (comparison.runBasis reversibleGatePermutation degreePrepared)
      (comparison.runBasis reversibleGatePermutation decoded) := by
    simpa [support, comparison, degreePrepared, decoded, degree, words, input] using
      decoderComparison_after_degreeValid_agrees_on_support p configuration
  calc
    readWires (decoderGoodWires p)
        (comparison.runBasis reversibleGatePermutation degreePrepared) =
        readWires (decoderGoodWires p)
          (comparison.runBasis reversibleGatePermutation decoded) := by
      apply List.map_congr_left
      intro wire member
      exact agree wire (by simp [support, decoderComparisonSupport, member])
    _ = List.replicate (p.K - 1) true := by
      simpa [comparison, decoded, degree, words, input] using
        decoderComparison_good_after_degreeDecode p configuration

/-- degree-valid計算後の実比較列も共有AND scratchを全て0へ戻す。 -/
theorem decoderComparison_scratch_clean_after_degreeValid
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let degreePrepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    let compared :=
      (decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation degreePrepared
    ∀ wire ∈ decoderAndScratchWires p, compared wire = false := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have agree : BasisAgreeOn support
      (comparison.runBasis reversibleGatePermutation degreePrepared)
      (comparison.runBasis reversibleGatePermutation decoded) := by
    simpa [support, comparison, degreePrepared, decoded, degree, words, input] using
      decoderComparison_after_degreeValid_agrees_on_support p configuration
  intro wire member
  calc
    comparison.runBasis reversibleGatePermutation degreePrepared wire =
        comparison.runBasis reversibleGatePermutation decoded wire :=
      agree wire (by simp [support, decoderComparisonSupport, member])
    _ = false := by
      exact decoderComparison_scratch_clean_after_degreeDecode p configuration
        wire member

/-- 実比較列の後でもdegree-valid wireは1のまま保存される。 -/
theorem decoderDegreeValid_true_after_comparison
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let degreePrepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    let compared :=
      (decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation degreePrepared
    compared (decoderDegreeValidWire p) = true := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have outside : decoderDegreeValidWire p ∉ support := by
    simpa [support, degree, words] using
      decoderDegreeValid_not_mem_comparisonSupport_system p
  rw [Circuit.runBasis_outside_of_usesOnly support comparison
    (by simpa [support, comparison, degree, words] using
      decoderComparisonSequence_usesOnly_system p) degreePrepared
    (decoderDegreeValidWire p) outside]
  have preparedEq :
      degreePrepared = xBasisAction (decoderDegreeValidWire p) decoded := by
    simpa [degreePrepared, decoded, degree, input] using
      decoderDegreeValid_after_degreeDecode p configuration
  rw [preparedEq, xBasisAction_target]
  have decodedFalse : decoded (decoderDegreeValidWire p) = false := by
    exact oracleAndWork_zero_after_degreeDecode p configuration
      (decoderDegreeValidWire p) (decoderDegreeValid_mem_andWork p)
  rw [decodedFalse]
  rfl

/-- 合法delimiterでは合法性compute回路が一時合法bitを1にする。 -/
theorem decoderLegalityCompute_legalTemporary_true
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let words := splitSystemWords p.wordWidth p.K (systemWires p)
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    (decoderLegalityCompute words degree (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p) (decoderDegreeValidWire p)
      (decoderLegalTemporaryWire p)).runBasis reversibleGatePermutation decoded
        (decoderLegalTemporaryWire p) = true := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  let compared := comparison.runBasis reversibleGatePermutation degreePrepared
  let controls := decoderDegreeValidWire p :: decoderGoodWires p
  let scratch := decoderAndScratchWires p
  let target := decoderLegalTemporaryWire p
  change (positiveMultiControlledX controls scratch target).runBasis
    reversibleGatePermutation compared target = true
  have scratchZero : ∀ wire ∈ scratch, compared wire = false := by
    simpa [scratch, compared, comparison, degreePrepared, decoded, degree, words,
      input] using decoderComparison_scratch_clean_after_degreeValid p configuration
  rw [runBasis_positiveMultiControlledX controls scratch target compared
    (by simpa [controls, scratch] using decoderAllGood_enoughScratch p)
    (by simpa [controls, scratch, target] using decoderAllGood_layout_nodup p)
    scratchZero]
  have controlsTrue : allWiresTrue controls compared = true := by
    have degreeTrue : compared (decoderDegreeValidWire p) = true := by
      simpa [compared, comparison, degreePrepared, decoded, degree, words, input] using
        decoderDegreeValid_true_after_comparison p configuration
    have goodTrue : readWires (decoderGoodWires p) compared =
        List.replicate (p.K - 1) true := by
      simpa [compared, comparison, degreePrepared, decoded, degree, words, input] using
        decoderComparison_good_after_degreeValid p configuration
    change (compared (decoderDegreeValidWire p) ::
      readWires (decoderGoodWires p) compared).all id = true
    rw [degreeTrue, goodTrue]
    simp
  rw [controlsTrue]
  simp only [if_true, xBasisAction_target]
  have outsideTarget : target ∉ support := by
    simpa [target, support, degree, words] using
      decoderLegalTemporary_not_mem_comparisonSupport_system p
  have comparedTarget : compared target = degreePrepared target := by
    exact Circuit.runBasis_outside_of_usesOnly support comparison
      (by simpa [support, comparison, degree, words] using
        decoderComparisonSequence_usesOnly_system p)
      degreePrepared target outsideTarget
  have preparedEq :
      degreePrepared = xBasisAction (decoderDegreeValidWire p) decoded := by
    simpa [degreePrepared, decoded, degree, input] using
      decoderDegreeValid_after_degreeDecode p configuration
  have targetNeDegree : target ≠ decoderDegreeValidWire p := by
    have fresh := (List.nodup_cons.mp (decoderAllGood_layout_nodup p)).1
    have degreeNeTarget :
        decoderDegreeValidWire p ≠ decoderLegalTemporaryWire p := by
      intro equal
      exact fresh (by simp [equal])
    simpa [target] using degreeNeTarget.symm
  have preparedTarget : degreePrepared target = decoded target := by
    rw [preparedEq]
    exact xBasisAction_other (decoderDegreeValidWire p) target targetNeDegree decoded
  have decodedTarget : decoded target = false := by
    exact oracleAndWork_zero_after_degreeDecode p configuration target (by
      simpa [target] using decoderLegalTemporary_mem_andWork p)
  rw [comparedTarget, preparedTarget, decodedTarget]
  rfl

/-- decoder合法性computeが参照する全wireを含む、粗く再利用可能なsupport。 -/
def decoderLegalitySupport (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  systemWires p ++ decoderSuffixWires p ++ oracleDegreeWires p ++
    oracleCompareWorkWires p ++ oracleAndWorkWires p

/-- 保持先のoracle legal wireは合法性compute supportの外にある。 -/
theorem oracleLegal_not_mem_decoderLegalitySupport (p : QParameters) :
    oracleLegalWire p ∉ decoderLegalitySupport p := by
  let degreeSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
  let legalSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).legal
  let candidateSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  let compareSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have legalMember : oracleLegalWire p ∈
      (legalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [oracleLegalWire, legalSlice, RegisterSlice.wireList]
  have notSystem : oracleLegalWire p ∉ systemWires p := by
    intro member
    exact (List.disjoint_left.mp
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) legalSlice) member) legalMember
  have notDegree : oracleLegalWire p ∉ oracleDegreeWires p := by
    have separated : degreeSlice.start + p.degreeWidth ≤ legalSlice.start := by
      simp [degreeSlice, legalSlice, QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical]
    have disjoint :
        (degreeSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (legalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
      degreeSlice.wireList_disjoint_of_end_le_start legalSlice separated
    intro member
    have fullMember : oracleLegalWire p ∈
        (degreeSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oracleDegreeWires, degreeSlice, RegisterSlice.wireList] using member
    exact (List.disjoint_left.mp disjoint fullMember) legalMember
  have notSuffix : oracleLegalWire p ∉ decoderSuffixWires p := by
    have separated : legalSlice.start + 1 ≤ candidateSlice.start := by
      simp [legalSlice, candidateSlice, QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical]
      omega
    have disjoint :
        (legalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
      legalSlice.wireList_disjoint_of_end_le_start candidateSlice separated
    intro member
    have fullMember : oracleLegalWire p ∈
        (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
      List.mem_of_mem_take member
    exact (List.disjoint_left.mp disjoint legalMember) fullMember
  have notCompare : oracleLegalWire p ∉ oracleCompareWorkWires p := by
    have separated : legalSlice.start + 1 ≤ compareSlice.start := by
      simp [legalSlice, compareSlice, QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical]
      omega
    have disjoint :
        (legalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
      legalSlice.wireList_disjoint_of_end_le_start compareSlice separated
    intro member
    have fullMember : oracleLegalWire p ∈
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oracleCompareWorkWires, compareSlice, RegisterSlice.wireList] using member
    exact (List.disjoint_left.mp disjoint legalMember) fullMember
  have notAnd : oracleLegalWire p ∉ oracleAndWorkWires p := by
    have separated : legalSlice.start + 1 ≤ andSlice.start := by
      simp [legalSlice, andSlice, QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical]
      omega
    have disjoint :
        (legalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
      legalSlice.wireList_disjoint_of_end_le_start andSlice separated
    intro member
    have fullMember : oracleLegalWire p ∈
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oracleAndWorkWires, andSlice, RegisterSlice.wireList] using member
    exact (List.disjoint_left.mp disjoint legalMember) fullMember
  simp [decoderLegalitySupport, notSystem, notSuffix, notDegree, notCompare, notAnd]

/-- decoder合法性compute回路は明示したsupport内だけを使用する。 -/
theorem decoderLegalityCompute_usesOnly_system (p : QParameters) :
    circuitUsesOnly (decoderLegalitySupport p)
      (decoderLegalityCompute
        (splitSystemWords p.wordWidth p.K (systemWires p))
        (oracleDegreeWires p) (decoderLessWires p) (decoderNeedWires p)
        (decoderGoodWires p) (oracleCompareWorkWires p)
        (decoderAndScratchWires p) (decoderDegreeValidWire p)
        (decoderLegalTemporaryWire p)) := by
  let support := decoderLegalitySupport p
  let degree := oracleDegreeWires p
  let compare := oracleCompareWorkWires p
  let scratch := decoderAndScratchWires p
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let less := decoderLessWires p
  let need := decoderNeedWires p
  let good := decoderGoodWires p
  let degreeValid := decoderDegreeValidWire p
  let legalTemporary := decoderLegalTemporaryWire p
  have degreeMember : ∀ wire ∈ degree, wire ∈ support := by
    intro wire member
    simp [support, decoderLegalitySupport, degree, member]
  have andMember : ∀ wire ∈ oracleAndWorkWires p, wire ∈ support := by
    intro wire member
    simp [support, decoderLegalitySupport, member]
  have degreeValidMember : degreeValid ∈ support :=
    andMember degreeValid (by simpa [degreeValid] using decoderDegreeValid_mem_andWork p)
  have legalTemporaryMember : legalTemporary ∈ support :=
    andMember legalTemporary
      (by simpa [legalTemporary] using decoderLegalTemporary_mem_andWork p)
  have degreeUses : circuitUsesOnly support
      (decoderDegreeValidCircuit degree degreeValid) := by
    apply circuitUsesOnly_sequence
    intro gate gateMember
    rcases List.mem_map.mp gateMember with ⟨flag, flagMember, rfl⟩
    exact circuitUsesOnly_safeCnot support flag degreeValid
      (degreeMember flag flagMember) degreeValidMember
  have comparisonUses : circuitUsesOnly support
      (decoderComparisonSequence degree compare scratch 0 words less need good) := by
    apply circuitUsesOnly_mono _ _ (by
      simpa [degree, compare, scratch, words, less, need, good] using
        decoderComparisonSequence_usesOnly_system p)
    intro wire member
    have cases :
        wire ∈ words.flatten ∨ wire ∈ compare ∨ wire ∈ scratch ∨
        wire ∈ degree ∨ wire ∈ less ∨ wire ∈ need ∨ wire ∈ good := by
      simpa only [decoderComparisonSupport, List.mem_append, or_assoc] using member
    rcases cases with systemMember | compareMember | scratchMember |
      degreeWireMember | lessMember | needMember | goodMember
    · have fullSystem : wire ∈ systemWires p := by
        rw [flatten_splitSystemWords] at systemMember
        exact List.mem_of_mem_take systemMember
      simp [support, decoderLegalitySupport, fullSystem]
    · simp [support, decoderLegalitySupport, compare, compareMember]
    · apply andMember wire
      exact decoderComparisonAndMember p (by simp [scratch, scratchMember])
    · exact degreeMember wire degreeWireMember
    · apply andMember wire
      exact decoderComparisonAndMember p
        (by simp [less, decoderComparisonFlagWires, lessMember])
    · apply andMember wire
      exact decoderComparisonAndMember p
        (by simp [need, decoderComparisonFlagWires, needMember])
    · apply andMember wire
      exact decoderComparisonAndMember p
        (by simp [good, decoderComparisonFlagWires, goodMember])
  have allGoodUses : circuitUsesOnly support
      (positiveMultiControlledX (degreeValid :: good) scratch legalTemporary) := by
    apply circuitUsesOnly_positiveMultiControlledX
    · intro wire member
      rcases List.mem_cons.mp member with equal | goodMember
      · simpa [equal] using degreeValidMember
      · apply andMember wire
        exact decoderComparisonAndMember p
          (by simp [good, decoderComparisonFlagWires, goodMember])
    · intro wire member
      apply andMember wire
      exact decoderComparisonAndMember p (by simp [scratch, member])
    · exact legalTemporaryMember
  change circuitUsesOnly support
    (.seq (decoderDegreeValidCircuit degree degreeValid)
      (.seq (decoderComparisonSequence degree compare scratch 0 words less need good)
        (positiveMultiControlledX (degreeValid :: good) scratch legalTemporary)))
  exact ⟨degreeUses, comparisonUses, allGoodUses⟩

/-- compact decoder正本回路は合法delimiter入力で保持用legal wireを1にする。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_true
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
      reversibleGatePermutation input (oracleLegalWire p) = true := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let degree := oracleDegreeWires p
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let compute := decoderLegalityCompute words degree (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p) (oracleCompareWorkWires p)
    (decoderAndScratchWires p) (decoderDegreeValidWire p)
    (decoderLegalTemporaryWire p)
  let use := safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)
  let support := decoderLegalitySupport p
  change (Circuit.computeUseUncompute id compute use).runBasis
    reversibleGatePermutation decoded (oracleLegalWire p) = true
  have computeUses : circuitUsesOnly support compute := by
    simpa [support, compute, words, degree] using decoderLegalityCompute_usesOnly_system p
  have legalOutside : oracleLegalWire p ∉ support := by
    simpa [support] using oracleLegal_not_mem_decoderLegalitySupport p
  have temporaryMember : decoderLegalTemporaryWire p ∈ support := by
    have andMember := decoderLegalTemporary_mem_andWork p
    simp [support, decoderLegalitySupport, andMember]
  have sourceDifferent : decoderLegalTemporaryWire p ≠ oracleLegalWire p := by
    intro equal
    apply legalOutside
    simpa [equal] using temporaryMember
  have usePreserves : BasisAgreeOn support
      (use.runBasis reversibleGatePermutation
        (compute.runBasis reversibleGatePermutation decoded))
      (compute.runBasis reversibleGatePermutation decoded) := by
    intro wire member
    rw [show use = safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p) by rfl]
    rw [runBasis_safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)
      sourceDifferent]
    exact cnotBasisAction_other (decoderLegalTemporaryWire p) (oracleLegalWire p)
      wire (by
        intro equal
        subst wire
        exact legalOutside member)
      (compute.runBasis reversibleGatePermutation decoded)
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
  have temporaryTrue :
      compute.runBasis reversibleGatePermutation decoded
        (decoderLegalTemporaryWire p) = true := by
    simpa [compute, decoded, degree, words, input] using
      decoderLegalityCompute_legalTemporary_true p configuration
  have computedLegal :
      compute.runBasis reversibleGatePermutation decoded (oracleLegalWire p) =
        decoded (oracleLegalWire p) := by
    exact Circuit.runBasis_outside_of_usesOnly support compute computeUses decoded
      (oracleLegalWire p) legalOutside
  have decodedLegal : decoded (oracleLegalWire p) = false := by
    change
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input (oracleLegalWire p) = false
    rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth (systemWires p)
      (decoderSuffixWires p) degree (oracleLegalWire p) input (by simp)
      (systemWires_disjoint_decoderSuffix p) (systemWires_disjoint_degree p)
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
      (decoderSuffixWires_nodup p)]
    · rfl
    · intro member
      exact legalOutside (by simp [support, decoderLegalitySupport, member])
    · intro member
      exact legalOutside (by simp [support, decoderLegalitySupport, member])
    · intro member
      exact legalOutside (by simp [support, decoderLegalitySupport, degree, member])
  rw [temporaryTrue, computedLegal, decodedLegal]
  rfl

/-- temporary legalから保持用legalへのCNOTは合法性support上の値を保存する。 -/
theorem decoderLegalityUse_preservesSupport
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    BasisAgreeOn (decoderLegalitySupport p)
      ((safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)).runBasis
        reversibleGatePermutation input)
      input := by
  have legalOutside := oracleLegal_not_mem_decoderLegalitySupport p
  have temporaryMember : decoderLegalTemporaryWire p ∈ decoderLegalitySupport p := by
    have andMember := decoderLegalTemporary_mem_andWork p
    simp [decoderLegalitySupport, andMember]
  have sourceDifferent : decoderLegalTemporaryWire p ≠ oracleLegalWire p := by
    intro equal
    apply legalOutside
    simpa [equal] using temporaryMember
  intro wire member
  rw [runBasis_safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)
    sourceDifferent]
  exact cnotBasisAction_other (decoderLegalTemporaryWire p) (oracleLegalWire p)
    wire (by
      intro equal
      subst wire
      exact legalOutside member) input

/-- compact decoderの合法性compute--use--uncomputeは、明示supportをdegree decode直後へ戻す。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_support_restored
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    BasisAgreeOn (decoderLegalitySupport p)
      ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
        reversibleGatePermutation input)
      decoded := by
  dsimp only
  let degree := oracleDegreeWires p
  let words := splitSystemWords p.wordWidth p.K (systemWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let compute := decoderLegalityCompute words degree (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p) (oracleCompareWorkWires p)
    (decoderAndScratchWires p) (decoderDegreeValidWire p)
    (decoderLegalTemporaryWire p)
  let use := safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)
  let support := decoderLegalitySupport p
  change BasisAgreeOn support
    ((Circuit.computeUseUncompute id compute use).runBasis
      reversibleGatePermutation decoded) decoded
  have computeUses : circuitUsesOnly support compute := by
    simpa [support, compute, words, degree] using decoderLegalityCompute_usesOnly_system p
  have usePreserves : BasisAgreeOn support
      (use.runBasis reversibleGatePermutation
        (compute.runBasis reversibleGatePermutation decoded))
      (compute.runBasis reversibleGatePermutation decoded) := by
    simpa [support, use] using decoderLegalityUse_preservesSupport p
      (compute.runBasis reversibleGatePermutation decoded)
  rw [Circuit.computeUseUncompute_local_clean support compute use decoded computeUses
    usePreserves]
  exact restoreSupport_agrees_input support decoded
    (use.runBasis reversibleGatePermutation
      (compute.runBasis reversibleGatePermutation decoded))

/-- 合法入力のcompact decoderはdegree one-hotを保持出力する。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_degree
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
      reversibleGatePermutation input
    readWires (oracleDegreeWires p) output =
      degreeOneHotFrom p.K configuration.1.card 0 := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let degree := oracleDegreeWires p
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
    reversibleGatePermutation input
  have agree : BasisAgreeOn (decoderLegalitySupport p) output decoded := by
    simpa [output, decoded, degree] using
      xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_support_restored p input
  calc
    readWires degree output = readWires degree decoded := by
      apply List.map_congr_left
      intro wire member
      exact agree wire (by simp [decoderLegalitySupport, degree, member])
    _ = degreeOneHotFrom p.K configuration.1.card 0 := by
      simpa [decoded, degree, input] using
        readWires_degreeDecode_delimiter_system p configuration

/-- 合法入力のcompact decoderは比較workとAND workを全て0へ戻す。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_work_clean
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
      reversibleGatePermutation input
    (∀ wire ∈ oracleCompareWorkWires p, output wire = false) ∧
      (∀ wire ∈ oracleAndWorkWires p, output wire = false) := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let degree := oracleDegreeWires p
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
    reversibleGatePermutation input
  have agree : BasisAgreeOn (decoderLegalitySupport p) output decoded := by
    simpa [output, decoded, degree] using
      xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_support_restored p input
  constructor
  · intro wire member
    change output wire = false
    rw [agree wire (by simp [decoderLegalitySupport, member])]
    exact oracleCompare_zero_after_degreeDecode p configuration wire member
  · intro wire member
    change output wire = false
    rw [agree wire (by simp [decoderLegalitySupport, member])]
    exact oracleAndWork_zero_after_degreeDecode p configuration wire member

/-- 合法入力のcompact decoderはsystem registerを厳密に保存する。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_system_preserved
    (p : QParameters) (configuration : QConfiguration p) :
    let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
    let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
      reversibleGatePermutation input
    readWires (systemWires p) output = registerBitList (delimiterEncoding configuration) := by
  dsimp only
  let input := zeroAncillaJointBasis p (delimiterEncoding configuration)
  let degree := oracleDegreeWires p
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth (systemWires p) (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (systemWires p)).runBasis
    reversibleGatePermutation input
  have agree : BasisAgreeOn (decoderLegalitySupport p) output decoded := by
    simpa [output, decoded, degree] using
      xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_support_restored p input
  calc
    readWires (systemWires p) output = readWires (systemWires p) decoded := by
      apply List.map_congr_left
      intro wire member
      exact agree wire (by simp [decoderLegalitySupport, member])
    _ = readWires (systemWires p) input := by
      apply List.map_congr_left
      intro wire member
      exact runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_input_wire p.wordWidth (systemWires p)
        (decoderSuffixWires p) degree wire input
        (systemWires_disjoint_decoderSuffix p) (systemWires_disjoint_degree p)
        (oracleDegreeWires_disjoint_decoderSuffixWires p).symm member
    _ = registerBitList (delimiterEncoding configuration) :=
      readWires_systemWires_zeroAncilla p (delimiterEncoding configuration)

/-- control付き定数XORの、行列を使わない計算基底上の参照作用。 -/
def controlledXorConstantBasisAction
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits) (constant start : Nat) :
    List (Wire ancillaQubits systemQubits) →
      JointBasis ancillaQubits systemQubits → JointBasis ancillaQubits systemQubits
  | [], input => input
  | target :: targets, input =>
      controlledXorConstantBasisAction control constant (start + 1) targets
        (if constant.testBit start then
          cnotBasisAction control target input
        else input)

/--
再帰的なcontrol付き定数XOR回路は、任意幅について計算基底上の参照作用と一致する。
証明はregister長の帰納法だけを使い、基底や行列を列挙しない。
-/
theorem runBasis_controlledXorConstantAux
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits) (constant start : Nat)
    (targets : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (controlAbsent : control ∉ targets) :
    (controlledXorConstantAux control constant start targets).runBasis
        reversibleGatePermutation input =
      controlledXorConstantBasisAction control constant start targets input := by
  induction targets generalizing input start with
  | nil =>
      rfl
  | cons target targets inductionHypothesis =>
      have controlDifferent : control ≠ target := by
        intro equal
        apply controlAbsent
        simp [equal]
      have controlAbsentTail : control ∉ targets := by
        intro member
        apply controlAbsent
        simp [member]
      simp only [controlledXorConstantAux, runBasis_seq]
      unfold controlledXorConstantBasisAction
      by_cases enabled : constant.testBit start = true
      · simp only [enabled, if_true]
        rw [runBasis_safeCnot control target controlDifferent]
        exact inductionHypothesis (start + 1)
          (cnotBasisAction control target input) controlAbsentTail
      · have disabled : constant.testBit start = false :=
          Bool.eq_false_of_not_eq_true enabled
        simp only [disabled, Bool.false_eq_true, if_false]
        change
          (controlledXorConstantAux control constant (start + 1) targets).runBasis
              reversibleGatePermutation input =
            controlledXorConstantBasisAction control constant (start + 1) targets input
        exact inductionHypothesis (start + 1) input controlAbsentTail

/-- control付き定数XOR正本回路の基底作用は、bit 0から始める参照作用と一致する。 -/
theorem runBasis_controlledXorConstant
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (targets : List (Wire ancillaQubits systemQubits)) (constant : Nat)
    (input : JointBasis ancillaQubits systemQubits)
    (controlAbsent : control ∉ targets) :
    (controlledXorConstant control targets constant).runBasis
        reversibleGatePermutation input =
      controlledXorConstantBasisAction control constant 0 targets input := by
  exact runBasis_controlledXorConstantAux
    control constant 0 targets input controlAbsent

/-- control付き定数XOR参照作用はtarget列外のwireを変更しない。 -/
theorem controlledXorConstantBasisAction_outside
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits) (constant start : Nat)
    (targets : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits) (outside : wire ∉ targets) :
    controlledXorConstantBasisAction control constant start targets input wire =
      input wire := by
  induction targets generalizing input start with
  | nil => rfl
  | cons target targets inductionHypothesis =>
      have wireDifferent : wire ≠ target := by
        intro equal
        apply outside
        simp [equal]
      have outsideTail : wire ∉ targets := by
        intro member
        apply outside
        simp [member]
      unfold controlledXorConstantBasisAction
      rw [inductionHypothesis _ _ outsideTail]
      by_cases enabled : constant.testBit start = true
      · simp [enabled, cnotBasisAction_other control target wire wireDifferent]
      · have disabled : constant.testBit start = false :=
          Bool.eq_false_of_not_eq_true enabled
        simp [disabled]

/-- control値と定数bitに応じてBool列へlittle-endian XORした純粋な参照結果。 -/
def controlledXorConstantBits (controlValue : Bool) (constant start : Nat) :
    List Bool → List Bool
  | [] => []
  | bit :: bits =>
      (if controlValue && constant.testBit start then !bit else bit) ::
        controlledXorConstantBits controlValue constant (start + 1) bits

/--
重複のないtarget列では、control付き定数XOR参照作用後のregister読出しが
純粋なbit列XOR仕様に一致する。
-/
theorem readWires_controlledXorConstantBasisAction
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits) (constant start : Nat)
    (targets : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (targetsNodup : targets.Nodup) (controlAbsent : control ∉ targets) :
    readWires targets
        (controlledXorConstantBasisAction control constant start targets input) =
      controlledXorConstantBits (input control) constant start
        (readWires targets input) := by
  induction targets generalizing input start with
  | nil => rfl
  | cons target targets inductionHypothesis =>
      have targetFresh : target ∉ targets := (List.nodup_cons.mp targetsNodup).1
      have tailNodup : targets.Nodup := (List.nodup_cons.mp targetsNodup).2
      have controlDifferent : control ≠ target := by
        intro equal
        apply controlAbsent
        simp [equal]
      have controlAbsentTail : control ∉ targets := by
        intro member
        apply controlAbsent
        simp [member]
      let firstState :=
        if constant.testBit start then
          cnotBasisAction control target input
        else input
      have controlPreserved : firstState control = input control := by
        dsimp [firstState]
        by_cases enabled : constant.testBit start = true
        · simp [enabled, cnotBasisAction_other control target control
            controlDifferent]
        · have disabled : constant.testBit start = false :=
            Bool.eq_false_of_not_eq_true enabled
          simp [disabled]
      have tailValues : readWires targets firstState = readWires targets input := by
        apply List.map_congr_left
        intro wire member
        dsimp [firstState]
        by_cases enabled : constant.testBit start = true
        · simp [enabled, cnotBasisAction_other control target wire (by
            intro equal
            subst wire
            exact targetFresh member)]
        · have disabled : constant.testBit start = false :=
            Bool.eq_false_of_not_eq_true enabled
          simp [disabled]
      have headAfterTail :
          controlledXorConstantBasisAction control constant (start + 1)
              targets firstState target = firstState target :=
        controlledXorConstantBasisAction_outside control constant (start + 1)
          targets firstState target targetFresh
      have tailResult :
          readWires targets
              (controlledXorConstantBasisAction control constant (start + 1)
                targets firstState) =
            controlledXorConstantBits (input control) constant (start + 1)
              (readWires targets input) := by
        rw [inductionHypothesis (start + 1) firstState tailNodup controlAbsentTail]
        rw [controlPreserved, tailValues]
      unfold controlledXorConstantBasisAction
      change
        controlledXorConstantBasisAction control constant (start + 1)
            targets firstState target ::
          readWires targets
            (controlledXorConstantBasisAction control constant (start + 1)
              targets firstState) = _
      rw [headAfterTail, tailResult]
      dsimp [firstState]
      by_cases enabled : constant.testBit start = true
      · simp [controlledXorConstantBits, readWires, enabled, cnotBasisAction]
      · have disabled : constant.testBit start = false :=
          Bool.eq_false_of_not_eq_true enabled
        simp [controlledXorConstantBits, readWires, disabled]

/-- 正本回路後のtarget register値は純粋なcontrol付き定数XOR仕様に一致する。 -/
theorem readWires_controlledXorConstant
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (targets : List (Wire ancillaQubits systemQubits)) (constant : Nat)
    (input : JointBasis ancillaQubits systemQubits)
    (targetsNodup : targets.Nodup) (controlAbsent : control ∉ targets) :
    readWires targets
        ((controlledXorConstant control targets constant).runBasis
          reversibleGatePermutation input) =
      controlledXorConstantBits (input control) constant 0
        (readWires targets input) := by
  rw [runBasis_controlledXorConstant control targets constant input controlAbsent]
  exact readWires_controlledXorConstantBasisAction
    control constant 0 targets input targetsNodup controlAbsent

/-- Nat定数のlittle-endian bitを、指定開始位置から指定幅だけ並べる。 -/
def constantBitsAux (constant start : Nat) : Nat → List Bool
  | 0 => []
  | width + 1 =>
      constant.testBit start :: constantBitsAux constant (start + 1) width

/-- Nat定数のlittle-endian下位`width` bit。 -/
def constantBits (constant width : Nat) : List Bool :=
  constantBitsAux constant 0 width

/-- 定数bit列の長さは指定幅に等しい。 -/
@[simp] theorem constantBitsAux_length (constant start width : Nat) :
    (constantBitsAux constant start width).length = width := by
  induction width generalizing start with
  | zero => rfl
  | succ width inductionHypothesis =>
      simp [constantBitsAux, inductionHypothesis]

/-- 定数bit列の範囲内要素は、開始位置を加えたNatのtest bitである。 -/
theorem constantBitsAux_getElem?
    (constant start width index : Nat) (inRange : index < width) :
    (constantBitsAux constant start width)[index]? =
      some (constant.testBit (start + index)) := by
  induction width generalizing start index with
  | zero => omega
  | succ width inductionHypothesis =>
      cases index with
      | zero => simp [constantBitsAux]
      | succ index =>
          have tailRange : index < width := by omega
          simp only [constantBitsAux, List.getElem?_cons_succ]
          have indexShape : start + Nat.succ index = start + 1 + index := by omega
          rw [indexShape]
          exact inductionHypothesis (start + 1) index tailRange

/-- 固定幅定数bit列の各要素は、同じ番号のlittle-endian test bitである。 -/
theorem constantBits_getElem?
    (constant width index : Nat) (inRange : index < width) :
    (constantBits constant width)[index]? = some (constant.testBit index) := by
  simpa [constantBits] using constantBitsAux_getElem? constant 0 width index inRange

/-- selector制御列からwireだけを読むと元のselector列へ戻る。 -/
@[simp] theorem selectorConstantControlsAux_map_fst
    {ancillaQubits systemQubits : Nat}
    (constant start : Nat) (selector : List (Wire ancillaQubits systemQubits)) :
    (selectorConstantControlsAux constant start selector).map Prod.fst = selector := by
  induction selector generalizing start with
  | nil => rfl
  | cons wire wires inductionHypothesis =>
      simp [selectorConstantControlsAux, inductionHypothesis]

/-- selector制御列の長さは元のselector幅に等しい。 -/
@[simp] theorem selectorConstantControlsAux_length
    {ancillaQubits systemQubits : Nat}
    (constant start : Nat) (selector : List (Wire ancillaQubits systemQubits)) :
    (selectorConstantControlsAux constant start selector).length = selector.length := by
  induction selector generalizing start with
  | nil => rfl
  | cons wire wires inductionHypothesis =>
      simp [selectorConstantControlsAux, inductionHypothesis]

/-- selector制御列の期待Bool値は定数の対応little-endian bit列である。 -/
@[simp] theorem selectorConstantControlsAux_map_snd
    {ancillaQubits systemQubits : Nat}
    (constant start : Nat) (selector : List (Wire ancillaQubits systemQubits)) :
    (selectorConstantControlsAux constant start selector).map Prod.snd =
      constantBitsAux constant start selector.length := by
  induction selector generalizing start with
  | nil => rfl
  | cons wire wires inductionHypothesis =>
      simp [selectorConstantControlsAux, constantBitsAux, inductionHypothesis]

/-- selector制御条件は、selector読出し値と定数bit列のリスト一致に等しい。 -/
theorem boolControlsSatisfied_selectorConstantControlsAux
    {ancillaQubits systemQubits : Nat}
    (constant start : Nat) (selector : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) :
    boolControlsSatisfied (selectorConstantControlsAux constant start selector) input =
      decide (readWires selector input =
        constantBitsAux constant start selector.length) := by
  induction selector generalizing start with
  | nil => rfl
  | cons wire wires inductionHypothesis =>
      simp only [selectorConstantControlsAux, boolControlsSatisfied,
        readWires, List.map_cons, List.all_cons, List.length_cons,
        constantBitsAux, List.cons.injEq]
      by_cases headEqual : input wire = constant.testBit start
      · simp only [headEqual, decide_true, Bool.true_and, true_and]
        change
          boolControlsSatisfied
              (selectorConstantControlsAux constant (start + 1) wires) input =
            decide (readWires wires input =
              constantBitsAux constant (start + 1) wires.length)
        exact inductionHypothesis (start + 1)
      · simp [headEqual]

/-- selector制御条件は、selector読出し値と定数の下位固定幅bit列の一致に等しい。 -/
theorem boolControlsSatisfied_selectorConstantControls
    {ancillaQubits systemQubits : Nat}
    (selector : List (Wire ancillaQubits systemQubits)) (constant : Nat)
    (input : JointBasis ancillaQubits systemQubits) :
    boolControlsSatisfied (selectorConstantControls selector constant) input =
      decide (readWires selector input = constantBits constant selector.length) := by
  exact boolControlsSatisfied_selectorConstantControlsAux
    constant 0 selector input

/--
selector比較回路は、全selector bitが定数のlittle-endian bitと一致するときだけtargetを反転し、
多重AND用scratchを0へ戻す。
-/
theorem runBasis_selectorEqualsConstant
    {ancillaQubits systemQubits : Nat}
    (selector scratch : List (Wire ancillaQubits systemQubits))
    (constant : Nat) (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : selector.length ≤ scratch.length + 1)
    (layoutNodup : (selector ++ scratch ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratch, input wire = false) :
    (selectorEqualsConstant selector scratch constant target).runBasis
        reversibleGatePermutation input =
      if boolControlsSatisfied (selectorConstantControls selector constant) input then
        xBasisAction target input
      else input := by
  change
    (boolMultiControlledX (selectorConstantControls selector constant) scratch target).runBasis
        reversibleGatePermutation input = _
  have controlWires :
      (selectorConstantControls selector constant).map Prod.fst = selector := by
    simp [selectorConstantControls]
  apply runBasis_boolMultiControlledX
  · simpa [selectorConstantControls] using enoughScratch
  · rw [controlWires]
    exact layoutNodup
  · exact scratchZero

/-- selector比較回路の条件を、register読出し値と固定幅定数bit列の一致で書いた形。 -/
theorem runBasis_selectorEqualsConstant_bits
    {ancillaQubits systemQubits : Nat}
    (selector scratch : List (Wire ancillaQubits systemQubits))
    (constant : Nat) (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (enoughScratch : selector.length ≤ scratch.length + 1)
    (layoutNodup : (selector ++ scratch ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratch, input wire = false) :
    (selectorEqualsConstant selector scratch constant target).runBasis
        reversibleGatePermutation input =
      if decide (readWires selector input = constantBits constant selector.length) then
        xBasisAction target input
      else input := by
  rw [runBasis_selectorEqualsConstant selector scratch constant target input
    enoughScratch layoutNodup scratchZero]
  rw [boolControlsSatisfied_selectorConstantControls selector constant input]

/-- decoderの多重AND scratchはselector比較に必要な本数以上を持つ。 -/
theorem selectorWidth_le_decoderAndScratch_add_one (p : QParameters) :
    p.selectorWidth ≤ (decoderAndScratchWires p).length + 1 := by
  simp [decoderAndScratchWires, oracleAndWorkWires, QParameters.andWorkWidth]
  omega

/-- 全0アンシラ入力ではdecoderの多重AND scratchもすべて0である。 -/
theorem decoderAndScratchWires_zero
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    ∀ wire ∈ decoderAndScratchWires p,
      zeroAncillaJointBasis p system wire = false := by
  intro wire member
  have fullMember : wire ∈ oracleAndWorkWires p :=
    List.mem_of_mem_drop member
  rcases List.mem_map.mp fullMember with ⟨index, _indexMember, rfl⟩
  change zeroAncillaJointBasis p system (.ancilla _) = false
  rfl

/--
selector sliceがselected flagより前にあれば、selector・decoder scratch・selected targetの
配置は重複しない。
-/
theorem selectorSlice_decoderScratch_selected_nodup
    (p : QParameters)
    (selectorSlice : RegisterSlice p.ancillaWidth p.selectorWidth)
    (selectorBeforeSelected :
      selectorSlice.start + p.selectorWidth ≤
        (QLayout.oracleSlice (OracleWorkLayout.canonical p).selected).start) :
    ((selectorSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) ++
        decoderAndScratchWires p ++ [oracleSelectedWire p]).Nodup := by
  let selectedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).selected
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have selectorNodup :
      (selectorSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Nodup :=
    selectorSlice.wireList_nodup
  have andNodup :
      (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Nodup :=
    andSlice.wireList_nodup
  have scratchNodup : (decoderAndScratchWires p).Nodup := by
    have dropped :
        ((andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).drop
          (3 * (p.K - 1) + 2)).Nodup := andNodup.drop
    simpa [decoderAndScratchWires, oracleAndWorkWires,
      RegisterSlice.wireList, andSlice] using dropped
  have selectorSelectedDisjoint :
      (selectorSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (selectedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    selectorSlice.wireList_disjoint_of_end_le_start selectedSlice
      selectorBeforeSelected
  have selectedBeforeAnd : selectedSlice.start + 1 ≤ andSlice.start := by
    simp [selectedSlice, andSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have selectedAndDisjoint :
      (selectedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    selectedSlice.wireList_disjoint_of_end_le_start andSlice selectedBeforeAnd
  have selectorBeforeAnd : selectorSlice.start + p.selectorWidth ≤ andSlice.start :=
    le_trans selectorBeforeSelected (le_trans
      (Nat.le_add_right selectedSlice.start 1) selectedBeforeAnd)
  have selectorAndDisjoint :
      (selectorSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    selectorSlice.wireList_disjoint_of_end_le_start andSlice selectorBeforeAnd
  have selectorScratchDisjoint :
      (selectorSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (decoderAndScratchWires p) := by
    rw [List.disjoint_left]
    intro left leftMember rightMember
    exact (List.disjoint_left.mp selectorAndDisjoint) leftMember
      (List.mem_of_mem_drop rightMember)
  have selectedMember : oracleSelectedWire p ∈
      (selectedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [oracleSelectedWire, oracleSingletonWire, selectedSlice,
      RegisterSlice.wireList]
  have selectedAbsentSelector : oracleSelectedWire p ∉
      (selectorSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    intro member
    exact (List.disjoint_left.mp selectorSelectedDisjoint) member selectedMember
  have selectedAbsentScratch : oracleSelectedWire p ∉ decoderAndScratchWires p := by
    intro member
    exact (List.disjoint_left.mp selectedAndDisjoint) selectedMember
      (List.mem_of_mem_drop member)
  apply List.nodup_append.mpr
  refine ⟨?_, by simp, ?_⟩
  · exact List.nodup_append.mpr ⟨selectorNodup, scratchNodup, by
      intro left leftMember right rightMember equal
      subst right
      exact (List.disjoint_left.mp selectorScratchDisjoint) leftMember rightMember⟩
  · intro wire member target targetMember
    have targetEqual : target = oracleSelectedWire p := by simpa using targetMember
    subst target
    intro equal
    subst wire
    rcases List.mem_append.mp member with selectorMember | scratchMember
    · exact selectedAbsentSelector selectorMember
    · exact selectedAbsentScratch scratchMember

/-- column selector比較で使うcanonical wire配置は重複しない。 -/
theorem columnSelector_decoderScratch_selected_nodup (p : QParameters) :
    (columnSelectorWires p ++ decoderAndScratchWires p ++
      [oracleSelectedWire p]).Nodup := by
  let selectorSlice := (QLayout.canonical p).columnSelector
  have before : selectorSlice.start + p.selectorWidth ≤
      (QLayout.oracleSlice (OracleWorkLayout.canonical p).selected).start := by
    simp [selectorSlice, QLayout.canonical, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  simpa [columnSelectorWires, columnSelectorWire, RegisterSlice.wireList,
    selectorSlice] using
    selectorSlice_decoderScratch_selected_nodup p selectorSlice before

/-- row selector比較で使うcanonical wire配置は重複しない。 -/
theorem rowSelector_decoderScratch_selected_nodup (p : QParameters) :
    (rowSelectorWires p ++ decoderAndScratchWires p ++
      [oracleSelectedWire p]).Nodup := by
  let selectorSlice := (QLayout.canonical p).rowSelector
  have before : selectorSlice.start + p.selectorWidth ≤
      (QLayout.oracleSlice (OracleWorkLayout.canonical p).selected).start := by
    simp [selectorSlice, QLayout.canonical, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  simpa [rowSelectorWires, rowSelectorWire, RegisterSlice.wireList,
    selectorSlice] using
    selectorSlice_decoderScratch_selected_nodup p selectorSlice before

/-- 全0アンシラ入力上のcolumn selector定数比較の完全な基底作用。 -/
theorem runBasis_columnSelectorEqualsConstant_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) (constant : Nat) :
    (selectorEqualsConstant (columnSelectorWires p) (decoderAndScratchWires p)
        constant (oracleSelectedWire p)).runBasis reversibleGatePermutation
        (zeroAncillaJointBasis p system) =
      if decide
          (readWires (columnSelectorWires p) (zeroAncillaJointBasis p system) =
            constantBits constant p.selectorWidth) then
        xBasisAction (oracleSelectedWire p) (zeroAncillaJointBasis p system)
      else zeroAncillaJointBasis p system := by
  have result := runBasis_selectorEqualsConstant_bits
    (columnSelectorWires p) (decoderAndScratchWires p) constant
    (oracleSelectedWire p) (zeroAncillaJointBasis p system)
    (by simpa [columnSelectorWires] using
      selectorWidth_le_decoderAndScratch_add_one p)
    (columnSelector_decoderScratch_selected_nodup p)
    (decoderAndScratchWires_zero p system)
  simpa [columnSelectorWires] using result

/-- 全0アンシラ入力上のrow selector定数比較の完全な基底作用。 -/
theorem runBasis_rowSelectorEqualsConstant_zeroAncilla
    (p : QParameters) (system : RegisterBasis p.systemWidth) (constant : Nat) :
    (selectorEqualsConstant (rowSelectorWires p) (decoderAndScratchWires p)
        constant (oracleSelectedWire p)).runBasis reversibleGatePermutation
        (zeroAncillaJointBasis p system) =
      if decide
          (readWires (rowSelectorWires p) (zeroAncillaJointBasis p system) =
            constantBits constant p.selectorWidth) then
        xBasisAction (oracleSelectedWire p) (zeroAncillaJointBasis p system)
      else zeroAncillaJointBasis p system := by
  have result := runBasis_selectorEqualsConstant_bits
    (rowSelectorWires p) (decoderAndScratchWires p) constant
    (oracleSelectedWire p) (zeroAncillaJointBasis p system)
    (by simpa [rowSelectorWires] using
      selectorWidth_le_decoderAndScratch_add_one p)
    (rowSelector_decoderScratch_selected_nodup p)
    (decoderAndScratchWires_zero p system)
  simpa [rowSelectorWires] using result

/--
分離されたcontrol・source・target配置ではcontrolled XOR copyは、controlが1なら通常の
XOR copy、0なら恒等作用に一致する。
-/
theorem runBasis_controlledXorCopy
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sameLength : source.length = target.length)
    (sourceDisjointTarget : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target) :
    (controlledXorCopy control source target).runBasis
        reversibleGatePermutation input =
      if input control then
        (xorCopy source target).runBasis reversibleGatePermutation input
      else input := by
  induction source generalizing target input with
  | nil =>
      cases target with
      | nil =>
          simp [controlledXorCopy, xorCopy, Circuit.sequence, Circuit.runBasis]
      | cons targetHead targetTail => simp at sameLength
  | cons sourceHead sourceTail inductionHypothesis =>
      cases target with
      | nil => simp at sameLength
      | cons targetHead targetTail =>
          have tailLength : sourceTail.length = targetTail.length := by
            simpa using Nat.succ.inj sameLength
          rcases List.disjoint_cons_left.mp sourceDisjointTarget with
            ⟨sourceHeadAbsentTarget, sourceTailDisjointFull⟩
          rcases List.disjoint_cons_right.mp sourceTailDisjointFull with
            ⟨targetHeadAbsentSourceTail, tailDisjoint⟩
          have controlDifferentSource : control ≠ sourceHead := by
            intro equal
            apply controlAbsentSource
            simp [equal]
          have controlDifferentTarget : control ≠ targetHead := by
            intro equal
            apply controlAbsentTarget
            simp [equal]
          have sourceDifferentTarget : sourceHead ≠ targetHead := by
            intro equal
            subst targetHead
            exact sourceHeadAbsentTarget (by simp)
          have controlAbsentSourceTail : control ∉ sourceTail := by
            intro member
            apply controlAbsentSource
            simp [member]
          have controlAbsentTargetTail : control ∉ targetTail := by
            intro member
            apply controlAbsentTarget
            simp [member]
          simp only [controlledXorCopy, List.zip_cons_cons, List.map_cons,
            Circuit.sequence, runBasis_local_core_sequence_cons]
          rw [runBasis_local_safeToffoli control sourceHead targetHead
            controlDifferentSource controlDifferentTarget sourceDifferentTarget]
          by_cases enabled : input control
          · have firstEqualsCnot :
                toffoliBasisAction control sourceHead targetHead input =
                  cnotBasisAction sourceHead targetHead input := by
              funext wire
              simp [toffoliBasisAction, cnotBasisAction, enabled]
            rw [firstEqualsCnot]
            have controlAfter :
                cnotBasisAction sourceHead targetHead input control = true := by
              rw [cnotBasisAction_other sourceHead targetHead control
                controlDifferentTarget]
              exact enabled
            change
              (controlledXorCopy control sourceTail targetTail).runBasis
                  reversibleGatePermutation
                  (cnotBasisAction sourceHead targetHead input) = _
            rw [inductionHypothesis targetTail
              (cnotBasisAction sourceHead targetHead input) tailLength tailDisjoint
              controlAbsentSourceTail controlAbsentTargetTail]
            rw [controlAfter]
            simp only [if_true]
            rw [xorCopy, runBasis_seq,
              runBasis_safeCnot sourceHead targetHead sourceDifferentTarget]
            simp [enabled]
          · have disabledBool : input control = false := Bool.eq_false_of_not_eq_true enabled
            have firstIdentity :
                toffoliBasisAction control sourceHead targetHead input = input := by
              funext wire
              simp [toffoliBasisAction, disabledBool]
            rw [firstIdentity]
            change
              (controlledXorCopy control sourceTail targetTail).runBasis
                  reversibleGatePermutation input = _
            rw [inductionHypothesis targetTail input tailLength tailDisjoint
              controlAbsentSourceTail controlAbsentTargetTail]
            simp [disabledBool]

end ReversibleCircuit

end ProbabilityGeneratorQProof
