import QLean.Generator.Implementation.QOracleCorrectness
import QLean.Generator.Implementation.QTopLevelCorrectness
import QLean.Generator.Implementation.QSelectorBitBridge
import QLean.Generator.Analysis.UniformPreparationQLayout

/-!
# column・row oracle正本のend-to-end基底作用

任意`q,K`について、delimiter配置とselectorを受け取る実基本ゲート列を純粋参照関数へ
接続する。行列や全計算基底は展開せず、型付きsliceの分離と局所基底作用だけを合成する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- A selected fixed-width word inherits duplicate-freedom from its register. -/
theorem registerWordAt_nodup_of_nodup
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (nodup : register.Nodup) :
    (registerWordAt p register slot).Nodup := by
  unfold registerWordAt
  exact nodup.drop.take

/-- oracle側のcolumn key wire列はCOPY証明側の同じcanonical列に定義的に一致する。 -/
theorem columnKeyWires_eq_topColumnKeyWires (p : QParameters) :
    columnKeyWires p = topColumnKeyWires p := by
  rfl

/-- column key wire列の長さは物理system幅である。 -/
@[simp] theorem columnKeyWires_length (p : QParameters) :
    (columnKeyWires p).length = p.systemWidth := by
  simp [columnKeyWires]

/-- column key wire列には重複がない。 -/
theorem columnKeyWires_nodup (p : QParameters) :
    (columnKeyWires p).Nodup := by
  rw [columnKeyWires_eq_topColumnKeyWires]
  exact topColumnKeyWires_nodup p

/-- column key sliceは任意のoracle内部sliceと互いに素である。 -/
theorem columnKeyWires_disjoint_oracleSlice
    (p : QParameters) {width : Nat}
    (slice : RegisterSlice p.oracleWorkWidth width) :
    (columnKeyWires p).Disjoint
      ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  let keySlice := (QLayout.canonical p).columnKey
  let lifted := QLayout.oracleSlice slice
  have separated : keySlice.start + p.systemWidth ≤ lifted.start := by
    simp [keySlice, lifted, QLayout.canonical, QLayout.oracleSlice,
      RegisterSlice.compose]
    omega
  have full :
      (keySlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (lifted.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    keySlice.wireList_disjoint_of_end_le_start lifted separated
  simpa [columnKeyWires, columnKeyWire, RegisterSlice.wireList, keySlice,
    lifted] using full

/-- column keyとdecoder suffix scratchは互いに素である。 -/
theorem columnKeyWires_disjoint_decoderSuffix (p : QParameters) :
    (columnKeyWires p).Disjoint (decoderSuffixWires p) := by
  let candidate := (OracleWorkLayout.canonical p).candidate
  have full := columnKeyWires_disjoint_oracleSlice p candidate
  rw [List.disjoint_left]
  intro wire keyMember suffixMember
  apply (List.disjoint_left.mp full keyMember)
  exact List.mem_of_mem_take suffixMember

/-- column keyとdegree one-hot列は互いに素である。 -/
theorem columnKeyWires_disjoint_degree (p : QParameters) :
    (columnKeyWires p).Disjoint (oracleDegreeWires p) := by
  let degree := (OracleWorkLayout.canonical p).degree
  simpa [oracleDegreeWires, RegisterSlice.wireList, degree] using
    columnKeyWires_disjoint_oracleSlice p degree

/-- column keyと比較work列は互いに素である。 -/
theorem columnKeyWires_disjoint_compareWork (p : QParameters) :
    (columnKeyWires p).Disjoint (oracleCompareWorkWires p) := by
  let compare := (OracleWorkLayout.canonical p).compareWork
  simpa [oracleCompareWorkWires, RegisterSlice.wireList, compare] using
    columnKeyWires_disjoint_oracleSlice p compare

/-- column keyとAND work列は互いに素である。 -/
theorem columnKeyWires_disjoint_andWork (p : QParameters) :
    (columnKeyWires p).Disjoint (oracleAndWorkWires p) := by
  let andWork := (OracleWorkLayout.canonical p).andWork
  simpa [oracleAndWorkWires, RegisterSlice.wireList, andWork] using
    columnKeyWires_disjoint_oracleSlice p andWork

/-- column selector sliceと物理system registerは互いに素である。 -/
theorem columnSelectorSlice_disjoint_systemWires (p : QParameters) :
    (selectorSliceWires p (columnSelectorWire p)).Disjoint (systemWires p) := by
  change (((QLayout.canonical p).columnSelector.wireList :
      List (Wire p.ancillaWidth p.systemWidth))).Disjoint
    ((List.finRange p.systemWidth).map Wire.system)
  exact (RegisterSlice.systemWires_disjoint_wireList
    (systemWidth := p.systemWidth) (QLayout.canonical p).columnSelector).symm

/-- column selector sliceとcolumn key registerは互いに素である。 -/
theorem columnSelectorSlice_disjoint_columnKeyWires (p : QParameters) :
    (selectorSliceWires p (columnSelectorWire p)).Disjoint
      (columnKeyWires p) := by
  change (((QLayout.canonical p).columnSelector.wireList :
      List (Wire p.ancillaWidth p.systemWidth))).Disjoint
    (((QLayout.canonical p).columnKey.wireList :
      List (Wire p.ancillaWidth p.systemWidth)))
  apply RegisterSlice.wireList_disjoint_of_start_ge_end
  simp [QLayout.canonical]

/-- column selector sliceは任意のoracle内部sliceと互いに素である。 -/
theorem columnSelectorSlice_disjoint_oracleSlice
    (p : QParameters) {width : Nat}
    (slice : RegisterSlice p.oracleWorkWidth width) :
    (selectorSliceWires p (columnSelectorWire p)).Disjoint
      ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
  change (((QLayout.canonical p).columnSelector.wireList :
      List (Wire p.ancillaWidth p.systemWidth))).Disjoint
    ((QLayout.oracleSlice slice).wireList :
      List (Wire p.ancillaWidth p.systemWidth))
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.canonical, QLayout.oracleSlice, RegisterSlice.compose]
  omega

/-- column selector sliceとdecoder suffixは互いに素である。 -/
theorem columnSelectorSlice_disjoint_decoderSuffix (p : QParameters) :
    (selectorSliceWires p (columnSelectorWire p)).Disjoint
      (decoderSuffixWires p) := by
  let candidate := (OracleWorkLayout.canonical p).candidate
  have full := columnSelectorSlice_disjoint_oracleSlice p candidate
  rw [List.disjoint_left]
  intro wire selectorMember suffixMember
  exact (List.disjoint_left.mp full selectorMember)
    (List.mem_of_mem_take suffixMember)

/-- column selector sliceとdegree列は互いに素である。 -/
theorem columnSelectorSlice_disjoint_degree (p : QParameters) :
    (selectorSliceWires p (columnSelectorWire p)).Disjoint
      (oracleDegreeWires p) := by
  let degree := (OracleWorkLayout.canonical p).degree
  simpa [oracleDegreeWires, RegisterSlice.wireList, degree] using
    columnSelectorSlice_disjoint_oracleSlice p degree

/-- column selector sliceと比較work列は互いに素である。 -/
theorem columnSelectorSlice_disjoint_compareWork (p : QParameters) :
    (selectorSliceWires p (columnSelectorWire p)).Disjoint
      (oracleCompareWorkWires p) := by
  let compare := (OracleWorkLayout.canonical p).compareWork
  simpa [oracleCompareWorkWires, RegisterSlice.wireList, compare] using
    columnSelectorSlice_disjoint_oracleSlice p compare

/-- column selector sliceとAND work列は互いに素である。 -/
theorem columnSelectorSlice_disjoint_andWork (p : QParameters) :
    (selectorSliceWires p (columnSelectorWire p)).Disjoint
      (oracleAndWorkWires p) := by
  let andWork := (OracleWorkLayout.canonical p).andWork
  simpa [oracleAndWorkWires, RegisterSlice.wireList, andWork] using
    columnSelectorSlice_disjoint_oracleSlice p andWork

/-- column selector sliceは保持用oracle legal wireを含まない。 -/
theorem oracleLegal_not_mem_columnSelectorSlice (p : QParameters) :
    oracleLegalWire p ∉ selectorSliceWires p (columnSelectorWire p) := by
  let legal := (OracleWorkLayout.canonical p).legal
  have disjoint := columnSelectorSlice_disjoint_oracleSlice p legal
  have legalMember : oracleLegalWire p ∈
      ((QLayout.oracleSlice legal).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [oracleLegalWire, legal, RegisterSlice.wireList]
  intro member
  exact (List.disjoint_left.mp disjoint member) legalMember

/-- selector外が全0アンシラ背景と一致すれば、分離したアンシラwire列は全0である。 -/
theorem outsideColumnSelector_zero_on_disjoint
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p system) basis)
    (wires : List (Wire p.ancillaWidth p.systemWidth))
    (disjoint : (selectorSliceWires p (columnSelectorWire p)).Disjoint wires)
    (backgroundZero : ∀ wire ∈ wires,
      zeroAncillaJointBasis p system wire = false) :
    ∀ wire ∈ wires, basis wire = false := by
  intro wire member
  have selectorOutside : wire ∉ selectorSliceWires p (columnSelectorWire p) := by
    intro selectorMember
    exact (List.disjoint_left.mp disjoint selectorMember) member
  rw [outside wire selectorOutside]
  exact backgroundZero wire member

/-- selector外一致条件の下では、物理systemの読出し値は背景systemと一致する。 -/
theorem readWires_system_of_outsideColumnSelector
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p system) basis) :
    readWires (systemWires p) basis = registerBitList system := by
  simp only [readWires, systemWires, registerBitList, List.map_map]
  apply List.map_congr_left
  intro index member
  have systemMember : (Wire.system index :
      Wire p.ancillaWidth p.systemWidth) ∈ systemWires p := by
    exact List.mem_map.mpr ⟨index, member, rfl⟩
  have selectorOutside : (Wire.system index :
      Wire p.ancillaWidth p.systemWidth) ∉
        selectorSliceWires p (columnSelectorWire p) := by
    intro selectorMember
    exact (List.disjoint_left.mp (columnSelectorSlice_disjoint_systemWires p)
      selectorMember) systemMember
  exact outside (Wire.system index) selectorOutside

/-- compact decoderへ渡す任意wire列の型安全な配置条件。 -/
structure CompactDecoderInputLayout (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth)) : Prop where
  /-- delimiter物理幅と入力wire数が一致する。 -/
  length_eq : inputWires.length = p.systemWidth
  /-- 入力wire列に重複がない。 -/
  nodup : inputWires.Nodup
  /-- suffix scratchと重ならない。 -/
  disjoint_suffix : inputWires.Disjoint (decoderSuffixWires p)
  /-- degree flagと重ならない。 -/
  disjoint_degree : inputWires.Disjoint (oracleDegreeWires p)
  /-- 比較workと重ならない。 -/
  disjoint_compare : inputWires.Disjoint (oracleCompareWorkWires p)
  /-- AND workと重ならない。 -/
  disjoint_and : inputWires.Disjoint (oracleAndWorkWires p)
  /-- 保持用legal wireを入力として使わない。 -/
  legal_fresh : oracleLegalWire p ∉ inputWires

/-- 物理system registerはcompact decoderの適正な入力配置である。 -/
theorem systemWires_compactDecoderInputLayout (p : QParameters) :
    CompactDecoderInputLayout p (systemWires p) where
  length_eq := systemWires_length p
  nodup := systemWires_nodup p
  disjoint_suffix := systemWires_disjoint_decoderSuffix p
  disjoint_degree := systemWires_disjoint_degree p
  disjoint_compare := systemWires_disjoint_compareWork p
  disjoint_and := systemWires_disjoint_andWork p
  legal_fresh := by
    intro member
    rcases List.mem_map.mp member with ⟨index, _, equal⟩
    cases equal

/-- column key registerもcompact decoderの適正な入力配置である。 -/
theorem columnKeyWires_compactDecoderInputLayout (p : QParameters) :
    CompactDecoderInputLayout p (columnKeyWires p) where
  length_eq := columnKeyWires_length p
  nodup := columnKeyWires_nodup p
  disjoint_suffix := columnKeyWires_disjoint_decoderSuffix p
  disjoint_degree := columnKeyWires_disjoint_degree p
  disjoint_compare := columnKeyWires_disjoint_compareWork p
  disjoint_and := columnKeyWires_disjoint_andWork p
  legal_fresh := by
    let keySlice := (QLayout.canonical p).columnKey
    let legalSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).legal
    have separated : keySlice.start + p.systemWidth ≤ legalSlice.start := by
      simp [keySlice, legalSlice, QLayout.canonical, QLayout.oracleSlice,
        RegisterSlice.compose]
      omega
    have disjoint :
        (keySlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (legalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
      keySlice.wireList_disjoint_of_end_le_start legalSlice separated
    intro member
    have keyMember : oracleLegalWire p ∈
        (keySlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [columnKeyWires, columnKeyWire, RegisterSlice.wireList, keySlice] using
        member
    have legalMember : oracleLegalWire p ∈
        (legalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simp [oracleLegalWire, RegisterSlice.wireList, legalSlice]
    exact (List.disjoint_left.mp disjoint keyMember) legalMember

/--
適正配置の任意入力wireをword分割した比較supportには重複がない。
system・column-keyの別を証明本体から分離するための一般補題である。
-/
theorem decoderComparisonSupport_input_nodup
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires) :
    (decoderComparisonSupport
      (oracleDegreeWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p)
      (splitSystemWords p.wordWidth p.K inputWires)
      (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p)).Nodup := by
  let words := splitSystemWords p.wordWidth p.K inputWires
  let inputPrefix := words.flatten
  let ancillaSupport :=
    oracleCompareWorkWires p ++ decoderAndScratchWires p ++
      oracleDegreeWires p ++ decoderLessWires p ++ decoderNeedWires p ++
      decoderGoodWires p
  have prefixEq : inputPrefix = inputWires.take (p.K * p.wordWidth) := by
    exact flatten_splitSystemWords p.wordWidth p.K inputWires
  have prefixNodup : inputPrefix.Nodup := by
    rw [prefixEq]
    exact layout.nodup.take
  have ancillaNodup : ancillaSupport.Nodup := by
    simpa [ancillaSupport] using decoderComparisonAncilla_nodup p
  have separated :
      ∀ inputWire ∈ inputPrefix, ∀ ancillaWire ∈ ancillaSupport,
        inputWire ≠ ancillaWire := by
    intro inputWire inputMember ancillaWire ancillaMember
    have inputFull : inputWire ∈ inputWires := by
      rw [prefixEq] at inputMember
      exact List.mem_of_mem_take inputMember
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
      exact (List.disjoint_left.mp layout.disjoint_compare inputFull) compareMember
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp layout.disjoint_and inputFull)
        (decoderComparisonAndMember p (by simp [scratchMember]))
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp layout.disjoint_degree inputFull) degreeMember
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp layout.disjoint_and inputFull)
        (decoderComparisonAndMember p
          (by simp [decoderComparisonFlagWires, lessMember]))
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp layout.disjoint_and inputFull)
        (decoderComparisonAndMember p
          (by simp [decoderComparisonFlagWires, needMember]))
    · intro equal
      subst ancillaWire
      exact (List.disjoint_left.mp layout.disjoint_and inputFull)
        (decoderComparisonAndMember p
          (by simp [decoderComparisonFlagWires, goodMember]))
  have supportNodup : (inputPrefix ++ ancillaSupport).Nodup :=
    List.nodup_append.mpr ⟨prefixNodup, ancillaNodup, separated⟩
  simpa [decoderComparisonSupport, words, inputPrefix, ancillaSupport,
    List.append_assoc] using supportNodup

/-- 合法delimiterをcompact decoderへ渡す直前の値条件。 -/
structure CompactDecoderCleanInput (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 入力registerは対象delimiter符号を保持する。 -/
  input_bits : readWires inputWires input =
    registerBitList (delimiterEncoding configuration)
  /-- suffix scratchは全0である。 -/
  suffix_zero : readWires (decoderSuffixWires p) input =
    List.replicate (decoderSuffixWires p).length false
  /-- degree列は全0である。 -/
  degree_zero : readWires (oracleDegreeWires p) input =
    List.replicate (oracleDegreeWires p).length false
  /-- 比較workは全0である。 -/
  compare_zero : readWires (oracleCompareWorkWires p) input =
    List.replicate (oracleCompareWorkWires p).length false
  /-- AND workは全0である。 -/
  and_zero : ∀ wire ∈ oracleAndWorkWires p, input wire = false
  /-- 保持用legal wireは0である。 -/
  legal_zero : input (oracleLegalWire p) = false

/-- 任意入力配置に対するcompact decoderの局所support。 -/
def decoderLegalitySupportFor (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth)) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  inputWires ++ decoderSuffixWires p ++ oracleDegreeWires p ++
    oracleCompareWorkWires p ++ oracleAndWorkWires p

/-- 適正入力配置では保持用legal wireは局所supportの外にある。 -/
theorem oracleLegal_not_mem_decoderLegalitySupportFor
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires) :
    oracleLegalWire p ∉ decoderLegalitySupportFor p inputWires := by
  have canonicalOutside := oracleLegal_not_mem_decoderLegalitySupport p
  intro member
  rcases (by
    simpa only [decoderLegalitySupportFor, List.mem_append, or_assoc] using member) with
      inputMember | suffixMember | degreeMember | compareMember | andMember
  · exact layout.legal_fresh inputMember
  · exact canonicalOutside (by
      simp [decoderLegalitySupport, suffixMember])
  · exact canonicalOutside (by
      simp [decoderLegalitySupport, degreeMember])
  · exact canonicalOutside (by
      simp [decoderLegalitySupport, compareMember])
  · exact canonicalOutside (by
      simp [decoderLegalitySupport, andMember])

/--
AND work内の予約wireが比較用scratch・flagでなければ、任意入力配置の比較support外にある。
-/
theorem oracleAndSpecial_not_mem_decoderComparisonSupport_input
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (special : Wire p.ancillaWidth p.systemWidth)
    (memberAnd : special ∈ oracleAndWorkWires p)
    (freshComparisonAnd : special ∉
      decoderAndScratchWires p ++ decoderComparisonFlagWires p) :
    special ∉ decoderComparisonSupport
      (oracleDegreeWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p)
      (splitSystemWords p.wordWidth p.K inputWires)
      (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p) := by
  intro member
  have supportCases :
      special ∈ (splitSystemWords p.wordWidth p.K inputWires).flatten ∨
      special ∈ oracleCompareWorkWires p ∨
      special ∈ decoderAndScratchWires p ∨
      special ∈ oracleDegreeWires p ∨
      special ∈ decoderLessWires p ∨
      special ∈ decoderNeedWires p ∨
      special ∈ decoderGoodWires p := by
    simpa only [decoderComparisonSupport, List.mem_append, or_assoc] using member
  rcases supportCases with inputMember | compareMember | scratchMember |
      degreeMember | lessMember | needMember | goodMember
  · have inputFull : special ∈ inputWires := by
      rw [flatten_splitSystemWords] at inputMember
      exact List.mem_of_mem_take inputMember
    exact (List.disjoint_left.mp layout.disjoint_and inputFull) memberAnd
  · exact (List.disjoint_left.mp (oracleCompareWorkWires_disjoint_andWork p)
      compareMember) memberAnd
  · exact freshComparisonAnd (by simp [scratchMember])
  · exact (List.disjoint_left.mp (oracleDegreeWires_disjoint_andWork p)
      degreeMember) memberAnd
  · exact freshComparisonAnd
      (by simp [decoderComparisonFlagWires, lessMember])
  · exact freshComparisonAnd
      (by simp [decoderComparisonFlagWires, needMember])
  · exact freshComparisonAnd
      (by simp [decoderComparisonFlagWires, goodMember])

/-- degree-valid wireは任意入力配置の比較support外にある。 -/
theorem decoderDegreeValid_not_mem_comparisonSupport_input
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires) :
    decoderDegreeValidWire p ∉ decoderComparisonSupport
      (oracleDegreeWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p)
      (splitSystemWords p.wordWidth p.K inputWires)
      (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p) := by
  exact oracleAndSpecial_not_mem_decoderComparisonSupport_input p inputWires layout
    (decoderDegreeValidWire p) (decoderDegreeValid_mem_andWork p)
    (decoderDegreeValid_not_mem_comparisonAnd p)

/-- legal-temporary wireは任意入力配置の比較support外にある。 -/
theorem decoderLegalTemporary_not_mem_comparisonSupport_input
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires) :
    decoderLegalTemporaryWire p ∉ decoderComparisonSupport
      (oracleDegreeWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p)
      (splitSystemWords p.wordWidth p.K inputWires)
      (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p) := by
  exact oracleAndSpecial_not_mem_decoderComparisonSupport_input p inputWires layout
    (decoderLegalTemporaryWire p) (decoderLegalTemporary_mem_andWork p)
    (decoderLegalTemporary_not_mem_comparisonAnd p)

/--
一様準備後の任意selector基底では、systemからcolumn keyへのCOPY直後が
column-key compact decoderのclean入力条件を満たす。
-/
theorem xorSystemIntoColumnKey_cleanInput
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    CompactDecoderCleanInput p (columnKeyWires p) configuration copied := by
  dsimp only
  let source := topSystemWires p
  let target := topColumnKeyWires p
  let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
    reversibleGatePermutation basis
  have keyInputZero : ∀ wire ∈ columnKeyWires p, basis wire = false := by
    apply outsideColumnSelector_zero_on_disjoint p
      (delimiterEncoding configuration) basis outside (columnKeyWires p)
      (columnSelectorSlice_disjoint_columnKeyWires p)
    intro wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl
  have keyZero : readWires target basis = List.replicate p.systemWidth false := by
    change readWires (topColumnKeyWires p) basis =
      List.replicate p.systemWidth false
    rw [← columnKeyWires_eq_topColumnKeyWires]
    simpa using
      (readWires_eq_replicate_false_of_forall (columnKeyWires p) basis
        keyInputZero)
  have copiedKey : readWires target copied = readWires source basis := by
    exact xorSystemIntoColumnKey_runBasis_key p basis keyZero
  have systemBits : readWires source basis =
      registerBitList (delimiterEncoding configuration) := by
    simpa [source, topSystemWires, systemWires, QLayout.systemWire] using
      readWires_system_of_outsideColumnSelector p
        (delimiterEncoding configuration) basis outside
  have suffixInputZero : ∀ wire ∈ decoderSuffixWires p, basis wire = false := by
    apply outsideColumnSelector_zero_on_disjoint p
      (delimiterEncoding configuration) basis outside (decoderSuffixWires p)
      (columnSelectorSlice_disjoint_decoderSuffix p)
    intro wire member
    have candidateMember : wire ∈
        ((QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) :=
      List.mem_of_mem_take member
    rcases List.mem_map.mp candidateMember with ⟨index, _, rfl⟩
    rfl
  have degreeInputZero : ∀ wire ∈ oracleDegreeWires p, basis wire = false := by
    apply outsideColumnSelector_zero_on_disjoint p
      (delimiterEncoding configuration) basis outside (oracleDegreeWires p)
      (columnSelectorSlice_disjoint_degree p)
    intro wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl
  have compareInputZero : ∀ wire ∈ oracleCompareWorkWires p,
      basis wire = false := by
    apply outsideColumnSelector_zero_on_disjoint p
      (delimiterEncoding configuration) basis outside (oracleCompareWorkWires p)
      (columnSelectorSlice_disjoint_compareWork p)
    intro wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl
  have andInputZero : ∀ wire ∈ oracleAndWorkWires p, basis wire = false := by
    apply outsideColumnSelector_zero_on_disjoint p
      (delimiterEncoding configuration) basis outside (oracleAndWorkWires p)
      (columnSelectorSlice_disjoint_andWork p)
    intro wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl
  have legalInputZero : basis (oracleLegalWire p) = false := by
    rw [outside (oracleLegalWire p) (oracleLegal_not_mem_columnSelectorSlice p)]
    rfl
  have preserveOutsideTarget : ∀
      (wires : List (Wire p.ancillaWidth p.systemWidth)),
      target.Disjoint wires →
      (∀ wire ∈ wires, basis wire = false) →
      ∀ wire ∈ wires, copied wire = false := by
    intro wires disjoint inputZero wire member
    change (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis wire = false
    rw [xorSystemIntoColumnKeyReversibleCircuit]
    rw [runBasis_validatedXorCopyLists_outside source target basis
      (by simpa [source] using topSystemWires_nodup p)
      (by simpa [target] using topColumnKeyWires_nodup p)
      (by simp [source, target])
      (by simpa [source, target] using
        topSystemWires_disjoint_topColumnKeyWires p) wire]
    · exact inputZero wire member
    · intro targetMember
      exact (List.disjoint_left.mp disjoint targetMember) member
  refine {
    input_bits := ?_
    suffix_zero := ?_
    degree_zero := ?_
    compare_zero := ?_
    and_zero := ?_
    legal_zero := ?_ }
  · rw [columnKeyWires_eq_topColumnKeyWires]
    exact copiedKey.trans systemBits
  · apply readWires_eq_replicate_false_of_forall
    apply preserveOutsideTarget (decoderSuffixWires p)
    · simpa [target, columnKeyWires_eq_topColumnKeyWires] using
        columnKeyWires_disjoint_decoderSuffix p
    · exact suffixInputZero
  · apply readWires_eq_replicate_false_of_forall
    apply preserveOutsideTarget (oracleDegreeWires p)
    · simpa [target, columnKeyWires_eq_topColumnKeyWires] using
        columnKeyWires_disjoint_degree p
    · exact degreeInputZero
  · apply readWires_eq_replicate_false_of_forall
    apply preserveOutsideTarget (oracleCompareWorkWires p)
    · simpa [target, columnKeyWires_eq_topColumnKeyWires] using
        columnKeyWires_disjoint_compareWork p
    · exact compareInputZero
  · apply preserveOutsideTarget (oracleAndWorkWires p)
    · simpa [target, columnKeyWires_eq_topColumnKeyWires] using
        columnKeyWires_disjoint_andWork p
    · exact andInputZero
  · change copied (oracleLegalWire p) = false
    rw [show copied = (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis by rfl]
    rw [xorSystemIntoColumnKeyReversibleCircuit]
    rw [runBasis_validatedXorCopyLists_outside source target basis
      (by simpa [source] using topSystemWires_nodup p)
      (by simpa [target] using topColumnKeyWires_nodup p)
      (by simp [source, target])
      (by simpa [source, target] using
        topSystemWires_disjoint_topColumnKeyWires p)
      (oracleLegalWire p)]
    · exact legalInputZero
    · simpa [target, columnKeyWires_eq_topColumnKeyWires] using
        (columnKeyWires_compactDecoderInputLayout p).legal_fresh

/-- 任意入力配置の隣接比較回路は、自分自身の明示supportだけを使用する。 -/
theorem decoderComparisonSequence_usesOnly_input
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth)) :
    let words := splitSystemWords p.wordWidth p.K inputWires
    let support := decoderComparisonSupport
      (oracleDegreeWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p) words (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p)
    circuitUsesOnly support
      (decoderComparisonSequence (oracleDegreeWires p)
        (oracleCompareWorkWires p) (decoderAndScratchWires p) 0 words
        (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p)) := by
  dsimp only
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

/-- wire列の読出しが全0なら、列に属する各wireの値も0である。 -/
theorem pointwise_false_of_readWires_eq_replicate
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (values : readWires wires input = List.replicate wires.length false) :
    ∀ wire ∈ wires, input wire = false := by
  induction wires with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [readWires, List.map_cons, List.length_cons,
        List.replicate_succ] at values
      have parts := List.cons.inj values
      intro wire member
      rcases List.mem_cons.mp member with equal | tailMember
      · subst wire
        exact parts.1
      · apply inductionHypothesis
        · simpa [readWires] using parts.2
        · exact tailMember

/--
適正配置・clean work・合法delimiterからdegree decodeと実比較列を実行すると、
good列は全1となり、共有AND scratchは全0へ戻る。
-/
theorem decoderComparison_after_degreeDecode_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
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
        List.replicate (p.K - 1) true ∧
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
      degreeOneHotFrom degree.length configuration.1.card 0 := by
    exact readWires_xorDelimiterDegreeOneHotIntoTargetsCircuit_delimiterEncoding configuration
      inputWires (decoderSuffixWires p) degree input
      (by simp [layout.length_eq]) layout.disjoint_suffix layout.disjoint_degree
      suffixDisjointDegree (decoderSuffixWires_nodup p)
      (oracleDegreeWires_nodup p) clean.suffix_zero
      (by simpa [degree] using clean.degree_zero) clean.input_bits
  have wordValues : words.map (fun word => readWires word decoded) =
      splitBitWords p.wordWidth p.K
        (registerBitList (delimiterEncoding configuration)) := by
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
      _ = splitBitWords p.wordWidth p.K
          (registerBitList (delimiterEncoding configuration)) := by
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
    simp [words, good, splitSystemWords]
    omega
  have lessCount : less.length = good.length := by simp [less, good]
  have needCount : need.length = good.length := by simp [need, good]
  have wordLengths : ∀ word ∈ words, word.length = compare.length := by
    intro word member
    rcases List.mem_map.mp member with ⟨slot, slotMember, rfl⟩
    have slotLt : slot < p.K := List.mem_range.mp slotMember
    rw [List.length_take, List.length_drop]
    rw [layout.length_eq]
    have enough : p.wordWidth + slot * p.wordWidth ≤ p.systemWidth := by
      simp [QParameters.systemWidth]
      nlinarith
    rw [Nat.min_eq_left (Nat.le_sub_of_add_le enough)]
    simp [compare]
  have supportNodup :
      (decoderComparisonSupport degree compare scratch words less need good).Nodup := by
    simpa [degree, compare, scratch, words, less, need, good] using
      decoderComparisonSupport_input_nodup p inputWires layout
  have goodResult := readWires_decoderComparisonSequence_good
    degree compare scratch 0 words less need good decoded wordCount lessCount
    needCount wordLengths supportNodup compareZero scratchZero lessZero needZero
    goodZero (by simpa [compare, scratch] using
      decoderAndScratchWires_wordWidth_le p)
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
      _ = decoderExpectedGoodBits
            (degreeOneHotFrom p.K configuration.1.card 0) 0
            (splitBitWords p.wordWidth p.K
              (registerBitList (delimiterEncoding configuration))) := by
        rw [degreeValues, wordValues]
        simp [degree]
      _ = List.replicate (p.K - 1) true :=
        decoderExpectedGoodBits_delimiterEncoding configuration
  · exact scratchResult

/-- cleanな合法入力をdegree decodeすると、任意入力配置でも粒子数one-hotを得る。 -/
theorem readWires_degreeDecode_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input
    readWires (oracleDegreeWires p) decoded =
      degreeOneHotFrom p.K configuration.1.card 0 := by
  dsimp only
  simpa using
    (readWires_xorDelimiterDegreeOneHotIntoTargetsCircuit_delimiterEncoding configuration inputWires
      (decoderSuffixWires p) (oracleDegreeWires p) input
      (by simp [layout.length_eq]) layout.disjoint_suffix layout.disjoint_degree
      (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
      (decoderSuffixWires_nodup p) (oracleDegreeWires_nodup p)
      clean.suffix_zero clean.degree_zero clean.input_bits)

/-- 合法入力のdegree one-hot parityは、任意入力配置でもdegree-validを反転する。 -/
theorem decoderDegreeValid_after_degreeDecode_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
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
  rw [readWires_degreeDecode_of_clean p inputWires layout configuration input clean]
  rw [boolParity_degreeOneHot_configuration configuration]
  rfl

/-- degree-valid計算の前後は、任意入力配置の比較support上で一致する。 -/
theorem decoderComparison_after_degreeValid_agrees_on_support_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    let words := splitSystemWords p.wordWidth p.K inputWires
    let degree := oracleDegreeWires p
    let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
      (decoderAndScratchWires p) words (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p)
    let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
      (decoderAndScratchWires p) 0 words (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p)
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let degreePrepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    BasisAgreeOn support
      (comparison.runBasis reversibleGatePermutation degreePrepared)
      (comparison.runBasis reversibleGatePermutation decoded) := by
  dsimp only
  let words := splitSystemWords p.wordWidth p.K inputWires
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have preparedEq :
      degreePrepared = xBasisAction (decoderDegreeValidWire p) decoded := by
    simpa [degreePrepared, decoded, degree] using
      decoderDegreeValid_after_degreeDecode_of_clean p inputWires layout
        configuration input clean
  have beforeAgree : BasisAgreeOn support degreePrepared decoded := by
    intro wire member
    rw [preparedEq]
    apply xBasisAction_other
    intro equal
    subst wire
    exact decoderDegreeValid_not_mem_comparisonSupport_input p inputWires layout
      (by simpa [support, degree, words] using member)
  apply Circuit.runBasis_congr_on_of_usesOnly support comparison
  · simpa [support, comparison, degree, words] using
      decoderComparisonSequence_usesOnly_input p inputWires
  · exact beforeAgree

/-- degree-valid計算後の比較列でもgood全1と共有scratch全0が同時に成立する。 -/
theorem decoderComparison_after_degreeValid_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    let degree := oracleDegreeWires p
    let words := splitSystemWords p.wordWidth p.K inputWires
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    let degreePrepared :=
      (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
        reversibleGatePermutation decoded
    let compared :=
      (decoderComparisonSequence degree (oracleCompareWorkWires p)
        (decoderAndScratchWires p) 0 words (decoderLessWires p)
        (decoderNeedWires p) (decoderGoodWires p)).runBasis
        reversibleGatePermutation degreePrepared
    readWires (decoderGoodWires p) compared =
        List.replicate (p.K - 1) true ∧
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
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have agree : BasisAgreeOn support
      (comparison.runBasis reversibleGatePermutation degreePrepared)
      (comparison.runBasis reversibleGatePermutation decoded) := by
    simpa [support, comparison, degreePrepared, decoded, degree, words] using
      decoderComparison_after_degreeValid_agrees_on_support_of_clean p inputWires
        layout configuration input clean
  have direct := decoderComparison_after_degreeDecode_of_clean p inputWires layout
    configuration input clean
  constructor
  · calc
      readWires (decoderGoodWires p)
          (comparison.runBasis reversibleGatePermutation degreePrepared) =
          readWires (decoderGoodWires p)
            (comparison.runBasis reversibleGatePermutation decoded) := by
        apply List.map_congr_left
        intro wire member
        exact agree wire (by simp [support, decoderComparisonSupport, member])
      _ = List.replicate (p.K - 1) true := by
        simpa [comparison, decoded, degree, words] using direct.1
  · intro wire member
    calc
      comparison.runBasis reversibleGatePermutation degreePrepared wire =
          comparison.runBasis reversibleGatePermutation decoded wire :=
        agree wire (by simp [support, decoderComparisonSupport, member])
      _ = false := by
        exact direct.2 wire member

/-- degree decodeは、適正配置から分離したAND workを全0のまま保存する。 -/
theorem decoderAndWork_zero_after_degreeDecode_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    ∀ wire ∈ oracleAndWorkWires p, decoded wire = false := by
  dsimp only
  intro wire member
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
    (decoderSuffixWires p) (oracleDegreeWires p) wire input
    (by simp [layout.length_eq]) layout.disjoint_suffix layout.disjoint_degree
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p)]
  · exact clean.and_zero wire member
  · exact (List.disjoint_left.mp layout.disjoint_and.symm member)
  · exact (List.disjoint_left.mp
      (decoderSuffixWires_disjoint_andWork p).symm member)
  · exact (List.disjoint_left.mp
      (oracleDegreeWires_disjoint_andWork p).symm member)

/-- 実比較列の後でも、一般入力配置のdegree-valid wireは1のまま保存される。 -/
theorem decoderDegreeValid_true_after_comparison_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    let words := splitSystemWords p.wordWidth p.K inputWires
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
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
  let words := splitSystemWords p.wordWidth p.K inputWires
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
      degree).runBasis reversibleGatePermutation input
  let degreePrepared :=
    (decoderDegreeValidCircuit degree (decoderDegreeValidWire p)).runBasis
      reversibleGatePermutation decoded
  have outside : decoderDegreeValidWire p ∉ support := by
    simpa [support, degree, words] using
      decoderDegreeValid_not_mem_comparisonSupport_input p inputWires layout
  rw [Circuit.runBasis_outside_of_usesOnly support comparison
    (by simpa [support, comparison, degree, words] using
      decoderComparisonSequence_usesOnly_input p inputWires)
    degreePrepared (decoderDegreeValidWire p) outside]
  have preparedEq :
      degreePrepared = xBasisAction (decoderDegreeValidWire p) decoded := by
    simpa [degreePrepared, decoded, degree] using
      decoderDegreeValid_after_degreeDecode_of_clean p inputWires layout
        configuration input clean
  rw [preparedEq, xBasisAction_target]
  have decodedFalse : decoded (decoderDegreeValidWire p) = false := by
    exact decoderAndWork_zero_after_degreeDecode_of_clean p inputWires layout
      configuration input clean (decoderDegreeValidWire p)
      (decoderDegreeValid_mem_andWork p)
  rw [decodedFalse]
  rfl

/-- 合法delimiterでは、任意入力配置の合法性computeが一時legal bitを1にする。 -/
theorem decoderLegalityCompute_legalTemporary_true_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    let words := splitSystemWords p.wordWidth p.K inputWires
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    (decoderLegalityCompute words degree (decoderLessWires p)
      (decoderNeedWires p) (decoderGoodWires p) (oracleCompareWorkWires p)
      (decoderAndScratchWires p) (decoderDegreeValidWire p)
      (decoderLegalTemporaryWire p)).runBasis reversibleGatePermutation decoded
        (decoderLegalTemporaryWire p) = true := by
  dsimp only
  let words := splitSystemWords p.wordWidth p.K inputWires
  let degree := oracleDegreeWires p
  let support := decoderComparisonSupport degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let comparison := decoderComparisonSequence degree (oracleCompareWorkWires p)
    (decoderAndScratchWires p) 0 words (decoderLessWires p)
    (decoderNeedWires p) (decoderGoodWires p)
  let decoded :=
    (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
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
  have comparisonResult := decoderComparison_after_degreeValid_of_clean p inputWires
    layout configuration input clean
  have scratchZero : ∀ wire ∈ scratch, compared wire = false := by
    simpa [scratch, compared, comparison, degreePrepared, decoded, degree, words] using
      comparisonResult.2
  rw [runBasis_positiveMultiControlledX controls scratch target compared
    (by simpa [controls, scratch] using decoderAllGood_enoughScratch p)
    (by simpa [controls, scratch, target] using decoderAllGood_layout_nodup p)
    scratchZero]
  have controlsTrue : allWiresTrue controls compared = true := by
    have degreeTrue : compared (decoderDegreeValidWire p) = true := by
      simpa [compared, comparison, degreePrepared, decoded, degree, words] using
        decoderDegreeValid_true_after_comparison_of_clean p inputWires layout
          configuration input clean
    have goodTrue : readWires (decoderGoodWires p) compared =
        List.replicate (p.K - 1) true := by
      simpa [compared, comparison, degreePrepared, decoded, degree, words] using
        comparisonResult.1
    change (compared (decoderDegreeValidWire p) ::
      readWires (decoderGoodWires p) compared).all id = true
    rw [degreeTrue, goodTrue]
    simp
  rw [controlsTrue]
  simp only [if_true, xBasisAction_target]
  have outsideTarget : target ∉ support := by
    simpa [target, support, degree, words] using
      decoderLegalTemporary_not_mem_comparisonSupport_input p inputWires layout
  have comparedTarget : compared target = degreePrepared target := by
    exact Circuit.runBasis_outside_of_usesOnly support comparison
      (by simpa [support, comparison, degree, words] using
        decoderComparisonSequence_usesOnly_input p inputWires)
      degreePrepared target outsideTarget
  have preparedEq :
      degreePrepared = xBasisAction (decoderDegreeValidWire p) decoded := by
    simpa [degreePrepared, decoded, degree] using
      decoderDegreeValid_after_degreeDecode_of_clean p inputWires layout
        configuration input clean
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
    exact decoderAndWork_zero_after_degreeDecode_of_clean p inputWires layout
      configuration input clean target
      (by simpa [target] using decoderLegalTemporary_mem_andWork p)
  rw [comparedTarget, preparedTarget, decodedTarget]
  rfl

/-- 任意入力配置の合法性compute回路は、その局所support内だけを使用する。 -/
theorem decoderLegalityCompute_usesOnly_input
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth)) :
    circuitUsesOnly (decoderLegalitySupportFor p inputWires)
      (decoderLegalityCompute
        (splitSystemWords p.wordWidth p.K inputWires)
        (oracleDegreeWires p) (decoderLessWires p) (decoderNeedWires p)
        (decoderGoodWires p) (oracleCompareWorkWires p)
        (decoderAndScratchWires p) (decoderDegreeValidWire p)
        (decoderLegalTemporaryWire p)) := by
  let support := decoderLegalitySupportFor p inputWires
  let degree := oracleDegreeWires p
  let compare := oracleCompareWorkWires p
  let scratch := decoderAndScratchWires p
  let words := splitSystemWords p.wordWidth p.K inputWires
  let less := decoderLessWires p
  let need := decoderNeedWires p
  let good := decoderGoodWires p
  let degreeValid := decoderDegreeValidWire p
  let legalTemporary := decoderLegalTemporaryWire p
  have degreeMember : ∀ wire ∈ degree, wire ∈ support := by
    intro wire member
    simp [support, decoderLegalitySupportFor, degree, member]
  have andMember : ∀ wire ∈ oracleAndWorkWires p, wire ∈ support := by
    intro wire member
    simp [support, decoderLegalitySupportFor, member]
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
        decoderComparisonSequence_usesOnly_input p inputWires)
    intro wire member
    have cases :
        wire ∈ words.flatten ∨ wire ∈ compare ∨ wire ∈ scratch ∨
        wire ∈ degree ∨ wire ∈ less ∨ wire ∈ need ∨ wire ∈ good := by
      simpa only [decoderComparisonSupport, List.mem_append, or_assoc] using member
    rcases cases with inputMember | compareMember | scratchMember |
      degreeWireMember | lessMember | needMember | goodMember
    · have fullInput : wire ∈ inputWires := by
        rw [flatten_splitSystemWords] at inputMember
        exact List.mem_of_mem_take inputMember
      simp [support, decoderLegalitySupportFor, fullInput]
    · simp [support, decoderLegalitySupportFor, compare, compareMember]
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

/-- temporary legalから保持用legalへのCNOTは任意入力配置の局所supportを保存する。 -/
theorem decoderLegalityUse_preservesSupportFor
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    BasisAgreeOn (decoderLegalitySupportFor p inputWires)
      ((safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)).runBasis
        reversibleGatePermutation input)
      input := by
  have legalOutside :=
    oracleLegal_not_mem_decoderLegalitySupportFor p inputWires layout
  have temporaryMember : decoderLegalTemporaryWire p ∈
      decoderLegalitySupportFor p inputWires := by
    have andMember := decoderLegalTemporary_mem_andWork p
    simp [decoderLegalitySupportFor, andMember]
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

/--
任意入力配置のcompact decoderは、合法delimiter上で保持用legal wireを実際に1にする。
-/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_true_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input (oracleLegalWire p) = true := by
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
    reversibleGatePermutation decoded (oracleLegalWire p) = true
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
  have temporaryTrue :
      compute.runBasis reversibleGatePermutation decoded
        (decoderLegalTemporaryWire p) = true := by
    simpa [compute, decoded, degree, words] using
      decoderLegalityCompute_legalTemporary_true_of_clean p inputWires layout
        configuration input clean
  have computedLegal :
      compute.runBasis reversibleGatePermutation decoded (oracleLegalWire p) =
        decoded (oracleLegalWire p) := by
    exact Circuit.runBasis_outside_of_usesOnly support compute computeUses decoded
      (oracleLegalWire p) legalOutside
  have decodedLegal : decoded (oracleLegalWire p) = false := by
    change
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
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
  rw [temporaryTrue, computedLegal, decodedLegal]
  rfl

/-- compact decoderのcompute--use--uncomputeは任意入力配置の局所supportを復元する。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_support_restored_of_input
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    let degree := oracleDegreeWires p
    let decoded :=
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        degree).runBasis reversibleGatePermutation input
    BasisAgreeOn (decoderLegalitySupportFor p inputWires)
      ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input)
      decoded := by
  dsimp only
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
  change BasisAgreeOn support
    ((Circuit.computeUseUncompute id compute use).runBasis
      reversibleGatePermutation decoded) decoded
  have computeUses : circuitUsesOnly support compute := by
    simpa [support, compute, words, degree] using
      decoderLegalityCompute_usesOnly_input p inputWires
  have usePreserves : BasisAgreeOn support
      (use.runBasis reversibleGatePermutation
        (compute.runBasis reversibleGatePermutation decoded))
      (compute.runBasis reversibleGatePermutation decoded) := by
    simpa [support, use] using decoderLegalityUse_preservesSupportFor p inputWires
      layout (compute.runBasis reversibleGatePermutation decoded)
  rw [Circuit.computeUseUncompute_local_clean support compute use decoded computeUses
    usePreserves]
  exact restoreSupport_agrees_input support decoded
    (use.runBasis reversibleGatePermutation
      (compute.runBasis reversibleGatePermutation decoded))

/-- compact decoderは局所support外かつlegal以外のwireをdegree decode直後の値に保つ。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_outside_of_input
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ decoderLegalitySupportFor p inputWires)
    (notLegal : wire ≠ oracleLegalWire p) :
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input wire =
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input wire := by
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
      reversibleGatePermutation decoded wire = decoded wire
  have computeUses : circuitUsesOnly support compute := by
    simpa [support, compute, words, degree] using
      decoderLegalityCompute_usesOnly_input p inputWires
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
      (compute.runBasis reversibleGatePermutation decoded)) wire
    (by simpa [support] using outside)]
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
  rw [show use = safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p) by rfl]
  rw [runBasis_safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)
    sourceDifferent]
  rw [cnotBasisAction_other (decoderLegalTemporaryWire p) (oracleLegalWire p)
    wire notLegal]
  exact Circuit.runBasis_outside_of_usesOnly support compute computeUses decoded wire
    (by simpa [support] using outside)

/-- 合法入力の一般compact decoderはdegree one-hotを保持出力する。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_degree_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    readWires (oracleDegreeWires p) output =
      degreeOneHotFrom p.K configuration.1.card 0 := by
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
  calc
    readWires degree output = readWires degree decoded := by
      apply List.map_congr_left
      intro wire member
      exact agree wire (by simp [decoderLegalitySupportFor, degree, member])
    _ = degreeOneHotFrom p.K configuration.1.card 0 := by
      simpa [decoded, degree] using
        readWires_degreeDecode_of_clean p inputWires layout configuration input clean

/-- 合法入力の一般compact decoderは比較workとAND workを全0へ戻す。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_work_clean_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
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
    exact decoderAndWork_zero_after_degreeDecode_of_clean p inputWires layout
      configuration input clean wire member

/-- 合法入力の一般compact decoderは入力registerを厳密に保存する。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_input_preserved_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    let output := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
      reversibleGatePermutation input
    readWires inputWires output = registerBitList (delimiterEncoding configuration) := by
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
  calc
    readWires inputWires output = readWires inputWires decoded := by
      apply List.map_congr_left
      intro wire member
      exact agree wire (by simp [decoderLegalitySupportFor, member])
    _ = readWires inputWires input := by
      apply List.map_congr_left
      intro wire member
      exact runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_input_wire p.wordWidth inputWires
        (decoderSuffixWires p) degree wire input layout.disjoint_suffix
        layout.disjoint_degree
        (oracleDegreeWires_disjoint_decoderSuffixWires p).symm member
    _ = registerBitList (delimiterEncoding configuration) := clean.input_bits

/-- COPY後のcolumn-key compact decoderは各一様selector基底上でlegalを1にする。 -/
theorem compactDecoder_columnKey_after_copy_legal_true
    (p : QParameters) (configuration : QConfiguration p)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding configuration)) basis) :
    let copied := (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p (columnKeyWires p)).runBasis
      reversibleGatePermutation copied (oracleLegalWire p) = true := by
  dsimp only
  exact xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_legal_true_of_clean p (columnKeyWires p)
    (columnKeyWires_compactDecoderInputLayout p) configuration
    ((xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation basis)
    (xorSystemIntoColumnKey_cleanInput p configuration basis outside)

end ReversibleCircuit

end ProbabilityGeneratorQProof
