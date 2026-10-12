import QLean.Generator.Implementation.ReversibleArithmeticCorrectness
import QLean.Generator.Implementation.LayoutCorrectness
import QLean.Generator.Implementation.ReversibleLocality
import QLean.Generator.Analysis.QEncoding

/-!
# compact decoder回路の基底作用証明

delimiter decoderを構成する各可逆部品を、全状態や行列要素を列挙せずに証明する。
まず境界flag、suffix OR、slot存在flagを一般のwire列上で扱い、その後Q layoutへ適用する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 各wire値が0なら、そのwire列の読出しは同じ長さの全0列である。 -/
theorem readWires_eq_replicate_false_of_forall
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (allZero : ∀ wire ∈ wires, input wire = false) :
    readWires wires input = List.replicate wires.length false := by
  induction wires with
  | nil => rfl
  | cons wire wires inductionHypothesis =>
      rw [List.length_cons, List.replicate_succ]
      change input wire :: readWires wires input =
        false :: List.replicate wires.length false
      rw [allZero wire (by simp)]
      congr 1
      apply inductionHypothesis
      intro tailWire member
      exact allZero tailWire (by simp [member])

/-- little-endian Bool列の数値は、その列から構成した`BitVec`の数値に一致する。 -/
theorem littleEndianNat_eq_toNat_ofBoolListLE (bits : List Bool) :
    littleEndianNat bits = (BitVec.ofBoolListLE bits).toNat := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      cases bit <;>
        simp [littleEndianNat, BitVec.ofBoolListLE, inductionHypothesis,
          Nat.mul_comm]

/-- 任意幅`BitVec`の全little-endian bitを読むと、元の自然数値へ戻る。 -/
theorem littleEndianNat_ofFn_getLsb {width : Nat} (vector : BitVec width) :
    littleEndianNat (List.ofFn vector.getLsb) = vector.toNat := by
  rw [littleEndianNat_eq_toNat_ofBoolListLE]
  let reconstructed : BitVec width :=
    (BitVec.ofBoolListLE (List.ofFn vector.getLsb)).cast List.length_ofFn
  have equalVectors : reconstructed = vector := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro index inRange
    change
      ((BitVec.ofBoolListLE (List.ofFn vector.getLsb)).cast
        List.length_ofFn).getLsbD index = vector.getLsbD index
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
      BitVec.getLsbD_eq_getElem?_getD]
    simp [inRange]
  simpa [reconstructed] using congrArg BitVec.toNat equalVectors

/-- 一つのsiteを表す全little-endian bitの自然数値はsite番号そのものである。 -/
theorem littleEndianNat_siteBits (p : QParameters) (site : QSite p) :
    littleEndianNat (List.ofFn fun bit => siteBit p site bit) = site.val := by
  change littleEndianNat (List.ofFn (siteBitVector p site).getLsb) = site.val
  rw [littleEndianNat_ofFn_getLsb]
  simp [siteBitVector, siteCodeEquiv]

/-- 配置を昇順に列挙する`siteAt`はslot番号の狭義大小を保存する。 -/
theorem configuration_siteAt_val_lt {p : QParameters}
    (configuration : QConfiguration p) {left right : Fin configuration.1.card}
    (ordered : left < right) :
    (configuration.siteAt left).val < (configuration.siteAt right).val := by
  have imageOrdered :=
    (configuration.1.orderIsoOfFin rfl).lt_iff_lt.mpr ordered
  simpa [QConfiguration.siteAt] using imageOrdered

/-- Bool列を指定word幅で先頭から分割する純粋な参照関数。 -/
def splitBitWords (wordWidth wordCount : Nat) (bits : List Bool) :
    List (List Bool) :=
  (List.range wordCount).map fun slot =>
    (bits.drop (slot * wordWidth)).take wordWidth

/-- wire列をword分割してから読む操作は、先に読んだBool列のword分割に一致する。 -/
theorem readWires_splitSystemWords
    {ancillaQubits systemQubits : Nat}
    (wordWidth wordCount : Nat)
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) :
    (splitSystemWords wordWidth wordCount wires).map
        (fun word => readWires word input) =
      splitBitWords wordWidth wordCount (readWires wires input) := by
  simp [splitSystemWords, splitBitWords, readWires, List.map_map,
    List.map_drop, List.map_take]

/-- word分割したwire列を再び平坦化すると、元wire列の対応するprefixへ戻る。 -/
theorem flatten_splitSystemWords
    {ancillaQubits systemQubits : Nat}
    (wordWidth wordCount : Nat)
    (wires : List (Wire ancillaQubits systemQubits)) :
    (splitSystemWords wordWidth wordCount wires).flatten =
      wires.take (wordCount * wordWidth) := by
  induction wordCount with
  | zero => simp [splitSystemWords]
  | succ wordCount inductionHypothesis =>
      rw [splitSystemWords, List.range_succ, List.map_append,
        List.flatten_append]
      simp only [List.map_singleton, List.flatten_singleton]
      rw [show
        ((List.range wordCount).map fun slot =>
          (wires.drop (slot * wordWidth)).take wordWidth).flatten =
            wires.take (wordCount * wordWidth) by
              exact inductionHypothesis]
      rw [← List.take_add]
      congr 1
      rw [Nat.succ_mul]

/-- 指定長ごとに先頭chunkを連結し、最後に残り全体を連結する補助関数。 -/
def chunkConcat {α : Type*} : List Nat → List α → List α
  | [], values => values
  | width :: widths, values =>
      values.take width ++ chunkConcat widths (values.drop width)

/-- chunk分割して同じ順に再連結すると元のリストへ戻る。 -/
theorem chunkConcat_eq {α : Type*} (widths : List Nat) (values : List α) :
    chunkConcat widths values = values := by
  induction widths generalizing values with
  | nil => rfl
  | cons width widths inductionHypothesis =>
      simp [chunkConcat, inductionHypothesis, List.take_append_drop]

/-- candidate scratch sliceにはsystem幅のsuffix OR列を格納する十分な本数がある。 -/
theorem systemWidth_le_candidateWidth (p : QParameters) :
    p.systemWidth ≤ p.candidateWidth := by
  have wordsEnough := p.K_le_sortWordCount
  have wordProduct : p.wordWidth * p.K ≤ p.wordWidth * p.sortWordCount :=
    Nat.mul_le_mul_left p.wordWidth wordsEnough
  have oneLeWords : 1 ≤ p.sortWordCount := p.sortWordCount_pos
  calc
    p.systemWidth = p.wordWidth * p.K + 1 := rfl
    _ ≤ p.wordWidth * p.sortWordCount + p.sortWordCount :=
      Nat.add_le_add wordProduct oneLeWords
    _ = p.candidateWidth := by
      simp [QParameters.candidateWidth, Nat.mul_add,
        Nat.mul_comm p.wordWidth p.sortWordCount]

/-- decoderのsuffix scratch列は物理system幅と同じ長さを持つ。 -/
@[simp] theorem decoderSuffixWires_length (p : QParameters) :
    (decoderSuffixWires p).length = p.systemWidth := by
  simp [decoderSuffixWires, systemWidth_le_candidateWidth p]

/-- decoderのsuffix scratch列にはwire重複がない。 -/
theorem decoderSuffixWires_nodup (p : QParameters) :
    (decoderSuffixWires p).Nodup := by
  let candidateSlice :=
    QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  have full :
      ((List.finRange p.candidateWidth).map fun index =>
        candidateSlice.ancillaWire index :
          List (Wire p.ancillaWidth p.systemWidth)).Nodup := by
    simpa [RegisterSlice.wireList] using
      (RegisterSlice.wireList_nodup
        (systemWidth := p.systemWidth) candidateSlice)
  have taken :
      (((List.finRange p.candidateWidth).map fun index =>
        candidateSlice.ancillaWire index).take p.systemWidth :
          List (Wire p.ancillaWidth p.systemWidth)).Nodup := full.take
  simpa [decoderSuffixWires, candidateSlice] using taken

/-- decoderのdegree one-hot wire列には重複がない。 -/
theorem oracleDegreeWires_nodup (p : QParameters) :
    (oracleDegreeWires p).Nodup := by
  let degreeSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
  simpa [oracleDegreeWires, RegisterSlice.wireList, degreeSlice] using
    (RegisterSlice.wireList_nodup
      (systemWidth := p.systemWidth) degreeSlice)

/-- degree one-hot wire列の長さは`K`である。 -/
@[simp] theorem oracleDegreeWires_length (p : QParameters) :
    (oracleDegreeWires p).length = p.K := by
  simp [oracleDegreeWires, QParameters.degreeWidth]

/-- decoder比較work列の長さは一site wordの幅に一致する。 -/
@[simp] theorem oracleCompareWorkWires_length (p : QParameters) :
    (oracleCompareWorkWires p).length = p.wordWidth := by
  simp [oracleCompareWorkWires]

/-- 隣接比較のless flag列は`K-1`本である。 -/
@[simp] theorem decoderLessWires_length (p : QParameters) :
    (decoderLessWires p).length = p.K - 1 := by
  simp [decoderLessWires, oracleAndWorkWires, QParameters.andWorkWidth]
  omega

/-- 隣接比較のneed flag列は`K-1`本である。 -/
@[simp] theorem decoderNeedWires_length (p : QParameters) :
    (decoderNeedWires p).length = p.K - 1 := by
  simp [decoderNeedWires, oracleAndWorkWires, QParameters.andWorkWidth]
  omega

/-- 隣接比較のgood flag列は`K-1`本である。 -/
@[simp] theorem decoderGoodWires_length (p : QParameters) :
    (decoderGoodWires p).length = p.K - 1 := by
  simp [decoderGoodWires, oracleAndWorkWires, QParameters.andWorkWidth]
  omega

/-- 一般`q,K`で、decoderのAND scratchはword比較に必要な`2q`本以上ある。 -/
theorem decoderAndScratchWires_wordWidth_le (p : QParameters) :
    p.wordWidth ≤ (decoderAndScratchWires p).length := by
  simp [decoderAndScratchWires, oracleAndWorkWires,
    QParameters.andWorkWidth, QParameters.wordWidth]
  omega

/-- decoderのdegree one-hot列とsuffix scratch列は異なるsliceにあり互いに素である。 -/
theorem oracleDegreeWires_disjoint_decoderSuffixWires (p : QParameters) :
    (oracleDegreeWires p).Disjoint (decoderSuffixWires p) := by
  let degreeSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
  let candidateSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  have separated : degreeSlice.start + p.degreeWidth ≤ candidateSlice.start := by
    simp [degreeSlice, candidateSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have fullDisjoint :
      (degreeSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    degreeSlice.wireList_disjoint_of_end_le_start candidateSlice separated
  rw [List.disjoint_left]
  intro wire degreeMember suffixMember
  have degreeMemberFull : wire ∈
      (degreeSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [oracleDegreeWires, RegisterSlice.wireList, degreeSlice] using degreeMember
  have suffixMemberFull : wire ∈
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply List.mem_of_mem_take suffixMember
  exact (List.disjoint_left.mp fullDisjoint) degreeMemberFull suffixMemberFull

/-- decoder suffix scratchと比較work sliceは互いに素である。 -/
theorem decoderSuffixWires_disjoint_compareWork (p : QParameters) :
    (decoderSuffixWires p).Disjoint (oracleCompareWorkWires p) := by
  let candidateSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  let compareSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork
  have separated : candidateSlice.start + p.candidateWidth ≤ compareSlice.start := by
    simp [candidateSlice, compareSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have fullDisjoint :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    candidateSlice.wireList_disjoint_of_end_le_start compareSlice separated
  rw [List.disjoint_left]
  intro wire suffixMember compareMember
  have suffixMemberFull : wire ∈
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply List.mem_of_mem_take suffixMember
  have compareMemberFull : wire ∈
      (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [oracleCompareWorkWires, RegisterSlice.wireList, compareSlice] using
      compareMember
  exact (List.disjoint_left.mp fullDisjoint) suffixMemberFull compareMemberFull

/-- decoder suffix scratchとAND work sliceは互いに素である。 -/
theorem decoderSuffixWires_disjoint_andWork (p : QParameters) :
    (decoderSuffixWires p).Disjoint (oracleAndWorkWires p) := by
  let candidateSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have separated : candidateSlice.start + p.candidateWidth ≤ andSlice.start := by
    simp [candidateSlice, andSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have fullDisjoint :
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    candidateSlice.wireList_disjoint_of_end_le_start andSlice separated
  rw [List.disjoint_left]
  intro wire suffixMember andMember
  have suffixMemberFull : wire ∈
      (candidateSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply List.mem_of_mem_take suffixMember
  have andMemberFull : wire ∈
      (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simpa [oracleAndWorkWires, RegisterSlice.wireList, andSlice] using andMember
  exact (List.disjoint_left.mp fullDisjoint) suffixMemberFull andMemberFull

/--
andWork sliceはless・need・good・degree-valid・legal-temporary・残りscratchへ
隙間なく一度ずつ分割される。
-/
theorem decoderAndWork_partition (p : QParameters) :
    decoderLessWires p ++ decoderNeedWires p ++ decoderGoodWires p ++
        [decoderDegreeValidWire p] ++ [decoderLegalTemporaryWire p] ++
        decoderAndScratchWires p =
      oracleAndWorkWires p := by
  let width := p.K - 1
  let values := oracleAndWorkWires p
  have partition := chunkConcat_eq [width, width, width, 1, 1] values
  have firstIndex : width + width + width < values.length := by
    simp [width, values, oracleAndWorkWires, QParameters.andWorkWidth]
    omega
  have secondIndex : width + width + width + 1 < values.length := by
    simp [width, values, oracleAndWorkWires, QParameters.andWorkWidth]
    omega
  have normalized := partition
  simp only [chunkConcat, List.drop_drop] at normalized
  rw [List.take_one_drop_eq_of_lt_length firstIndex,
    List.take_one_drop_eq_of_lt_length secondIndex] at normalized
  simp only [List.append_assoc] at normalized ⊢
  simp only [decoderLessWires, decoderNeedWires,
    decoderGoodWires, decoderDegreeValidWire, decoderLegalTemporaryWire,
    decoderAndScratchWires]
  dsimp only [width, values] at normalized
  ring_nf at normalized ⊢
  exact normalized

/-- decoder内部のandWork各領域を連結したwire列には重複がない。 -/
theorem decoderAndWork_partition_nodup (p : QParameters) :
    (decoderLessWires p ++ decoderNeedWires p ++ decoderGoodWires p ++
      [decoderDegreeValidWire p] ++ [decoderLegalTemporaryWire p] ++
      decoderAndScratchWires p).Nodup := by
  rw [decoderAndWork_partition]
  simpa [oracleAndWorkWires, RegisterSlice.wireList] using
    (RegisterSlice.wireList_nodup
      (systemWidth := p.systemWidth)
      (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork))

/-- 比較で実際に使うAND scratch・less・need・good列を再配置しても重複はない。 -/
theorem decoderAndScratchFlags_nodup (p : QParameters) :
    (decoderAndScratchWires p ++ decoderLessWires p ++
      decoderNeedWires p ++ decoderGoodWires p).Nodup := by
  let rest := decoderLessWires p ++ decoderNeedWires p ++ decoderGoodWires p
  have selectedNodup :
      (rest ++ decoderAndScratchWires p).Nodup := by
    have selectedSub :
        (rest ++ decoderAndScratchWires p).Sublist
          (decoderLessWires p ++ decoderNeedWires p ++ decoderGoodWires p ++
            [decoderDegreeValidWire p] ++ [decoderLegalTemporaryWire p] ++
            decoderAndScratchWires p) := by
      have tailSub : (decoderAndScratchWires p).Sublist
          ([decoderDegreeValidWire p] ++ [decoderLegalTemporaryWire p] ++
            decoderAndScratchWires p) := by simp
      have combined := (List.Sublist.refl rest).append tailSub
      simpa only [rest, List.append_assoc] using combined
    exact List.Nodup.sublist selectedSub (decoderAndWork_partition_nodup p)
  have permutation :
      (decoderAndScratchWires p ++ rest).Perm
        (rest ++ decoderAndScratchWires p) := List.perm_append_comm
  simpa only [rest, List.append_assoc] using
    permutation.nodup_iff.mpr selectedNodup

/-- degree sliceと比較work sliceは互いに素である。 -/
theorem oracleDegreeWires_disjoint_compareWork (p : QParameters) :
    (oracleDegreeWires p).Disjoint (oracleCompareWorkWires p) := by
  let degreeSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
  let compareSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork
  have separated : degreeSlice.start + p.degreeWidth ≤ compareSlice.start := by
    simp [degreeSlice, compareSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have full :
      (degreeSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    degreeSlice.wireList_disjoint_of_end_le_start compareSlice separated
  simpa [oracleDegreeWires, oracleCompareWorkWires, RegisterSlice.wireList,
    degreeSlice, compareSlice] using full

/-- 比較work sliceとAND work sliceは互いに素である。 -/
theorem oracleCompareWorkWires_disjoint_andWork (p : QParameters) :
    (oracleCompareWorkWires p).Disjoint (oracleAndWorkWires p) := by
  let compareSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have separated : compareSlice.start + p.wordWidth ≤ andSlice.start := by
    simp [compareSlice, andSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have full :
      (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    compareSlice.wireList_disjoint_of_end_le_start andSlice separated
  simpa [oracleCompareWorkWires, oracleAndWorkWires, RegisterSlice.wireList,
    compareSlice, andSlice] using full

/-- degree sliceとAND work sliceは互いに素である。 -/
theorem oracleDegreeWires_disjoint_andWork (p : QParameters) :
    (oracleDegreeWires p).Disjoint (oracleAndWorkWires p) := by
  let degreeSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).degree
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have separated : degreeSlice.start + p.degreeWidth ≤ andSlice.start := by
    simp [degreeSlice, andSlice, QLayout.oracleSlice, RegisterSlice.compose,
      OracleWorkLayout.canonical]
    omega
  have full :
      (degreeSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    degreeSlice.wireList_disjoint_of_end_le_start andSlice separated
  simpa [oracleDegreeWires, oracleAndWorkWires, RegisterSlice.wireList,
    degreeSlice, andSlice] using full

/-- decoder隣接比較が保持するless・need・good flag列。 -/
def decoderComparisonFlagWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  decoderLessWires p ++ decoderNeedWires p ++ decoderGoodWires p

/-- degree-valid wireはAND work sliceに属する。 -/
theorem decoderDegreeValid_mem_andWork (p : QParameters) :
    decoderDegreeValidWire p ∈ oracleAndWorkWires p := by
  rw [← decoderAndWork_partition p]
  simp

/-- legal-temporary wireはAND work sliceに属する。 -/
theorem decoderLegalTemporary_mem_andWork (p : QParameters) :
    decoderLegalTemporaryWire p ∈ oracleAndWorkWires p := by
  rw [← decoderAndWork_partition p]
  simp

/-- degree-valid wireは比較scratchおよびless・need・good flag列に現れない。 -/
theorem decoderDegreeValid_not_mem_comparisonAnd (p : QParameters) :
    decoderDegreeValidWire p ∉
      decoderAndScratchWires p ++ decoderComparisonFlagWires p := by
  let before := decoderComparisonFlagWires p
  let after := [decoderLegalTemporaryWire p] ++ decoderAndScratchWires p
  have normalized :
      (before ++ decoderDegreeValidWire p :: after).Nodup := by
    simpa [before, after, decoderComparisonFlagWires, List.append_assoc] using
      decoderAndWork_partition_nodup p
  have split := List.nodup_append.mp normalized
  have degreeNotBefore : decoderDegreeValidWire p ∉ before := by
    intro member
    exact split.2.2 (decoderDegreeValidWire p) member
      (decoderDegreeValidWire p) (by simp) rfl
  have degreeNotAfter : decoderDegreeValidWire p ∉ after :=
    (List.nodup_cons.mp split.2.1).1
  intro member
  rcases List.mem_append.mp member with scratchMember | flagMember
  · apply degreeNotAfter
    simp [after, scratchMember]
  · exact degreeNotBefore flagMember

/-- legal-temporary wireは比較scratchおよびless・need・good flag列に現れない。 -/
theorem decoderLegalTemporary_not_mem_comparisonAnd (p : QParameters) :
    decoderLegalTemporaryWire p ∉
      decoderAndScratchWires p ++ decoderComparisonFlagWires p := by
  let before := decoderComparisonFlagWires p
  let tail := decoderDegreeValidWire p ::
    decoderLegalTemporaryWire p :: decoderAndScratchWires p
  have normalized : (before ++ tail).Nodup := by
    simpa [before, tail, decoderComparisonFlagWires, List.append_assoc] using
      decoderAndWork_partition_nodup p
  have split := List.nodup_append.mp normalized
  have legalNotBefore : decoderLegalTemporaryWire p ∉ before := by
    intro member
    exact split.2.2 (decoderLegalTemporaryWire p) member
      (decoderLegalTemporaryWire p) (by simp [tail]) rfl
  have legalNotScratch : decoderLegalTemporaryWire p ∉ decoderAndScratchWires p := by
    have afterDegree := (List.nodup_cons.mp split.2.1).2
    exact (List.nodup_cons.mp afterDegree).1
  intro member
  rcases List.mem_append.mp member with scratchMember | flagMember
  · exact legalNotScratch scratchMember
  · exact legalNotBefore flagMember

/--
degree-valid・good制御、AND scratch、legal-temporary標的の多重AND配置は重複しない。
-/
theorem decoderAllGood_layout_nodup (p : QParameters) :
    ((decoderDegreeValidWire p :: decoderGoodWires p) ++
      decoderAndScratchWires p ++ [decoderLegalTemporaryWire p]).Nodup := by
  let selected := decoderGoodWires p ++ [decoderDegreeValidWire p] ++
    [decoderLegalTemporaryWire p] ++ decoderAndScratchWires p
  have selectedSub : selected.Sublist
      (decoderLessWires p ++ decoderNeedWires p ++ decoderGoodWires p ++
        [decoderDegreeValidWire p] ++ [decoderLegalTemporaryWire p] ++
        decoderAndScratchWires p) := by
    let leading := decoderLessWires p ++ decoderNeedWires p
    have sub := List.sublist_append_right leading selected
    simpa only [leading, selected, List.append_assoc] using sub
  have selectedNodup : selected.Nodup :=
    List.Nodup.sublist selectedSub (decoderAndWork_partition_nodup p)
  have frontPermutation :
      ([decoderDegreeValidWire p] ++ decoderGoodWires p).Perm
        (decoderGoodWires p ++ [decoderDegreeValidWire p]) :=
    List.perm_append_comm
  have backPermutation :
      (decoderAndScratchWires p ++ [decoderLegalTemporaryWire p]).Perm
        ([decoderLegalTemporaryWire p] ++ decoderAndScratchWires p) :=
    List.perm_append_comm
  have permutation := frontPermutation.append backPermutation
  have normalizedSelected :
      (decoderGoodWires p ++ [decoderDegreeValidWire p] ++
        ([decoderLegalTemporaryWire p] ++ decoderAndScratchWires p)).Nodup := by
    simpa [selected, List.append_assoc] using selectedNodup
  have desiredNodup := permutation.nodup_iff.mpr normalizedSelected
  simpa [selected, List.append_assoc] using desiredNodup

/-- 一般`q,K`で合法性多重ANDに必要なscratch本数が確保されている。 -/
theorem decoderAllGood_enoughScratch (p : QParameters) :
    (decoderDegreeValidWire p :: decoderGoodWires p).length ≤
      (decoderAndScratchWires p).length + 1 := by
  simp [decoderAndScratchWires, oracleAndWorkWires,
    QParameters.andWorkWidth, QParameters.wordWidth]
  omega

/-- decoder比較のscratchまたは保持flagは全てAND work sliceに属する。 -/
theorem decoderComparisonAndMember (p : QParameters)
    {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ decoderAndScratchWires p ++ decoderComparisonFlagWires p) :
    wire ∈ oracleAndWorkWires p := by
  rw [← decoderAndWork_partition p]
  simp only [decoderComparisonFlagWires, List.mem_append] at member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil]
  tauto

/-- 実際のdecoder比較が参照する全ancilla wireには重複がない。 -/
theorem decoderComparisonAncilla_nodup (p : QParameters) :
    (oracleCompareWorkWires p ++ decoderAndScratchWires p ++
      oracleDegreeWires p ++ decoderLessWires p ++ decoderNeedWires p ++
      decoderGoodWires p).Nodup := by
  let scratch := decoderAndScratchWires p
  let degree := oracleDegreeWires p
  let compare := oracleCompareWorkWires p
  let rest := decoderComparisonFlagWires p
  have andNodup : (scratch ++ rest).Nodup := by
    simpa [scratch, rest, decoderComparisonFlagWires, List.append_assoc] using
      decoderAndScratchFlags_nodup p
  have scratchNodup : scratch.Nodup := (List.nodup_append.mp andNodup).1
  have restNodup : rest.Nodup := (List.nodup_append.mp andNodup).2.1
  have scratchSeparatedRest :
      ∀ a ∈ scratch, ∀ b ∈ rest, a ≠ b :=
    (List.nodup_append.mp andNodup).2.2
  have degreeNodup : degree.Nodup := by
    simpa [degree] using oracleDegreeWires_nodup p
  have compareNodup : compare.Nodup := by
    let compareSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).compareWork
    simpa [compare, oracleCompareWorkWires, RegisterSlice.wireList, compareSlice] using
      (RegisterSlice.wireList_nodup
        (systemWidth := p.systemWidth) compareSlice)
  have degreeDisjointScratch : degree.Disjoint scratch := by
    rw [List.disjoint_left]
    intro wire degreeMember scratchMember
    exact (List.disjoint_left.mp (oracleDegreeWires_disjoint_andWork p))
      degreeMember (decoderComparisonAndMember p (by simp [scratch, scratchMember]))
  have degreeDisjointRest : degree.Disjoint rest := by
    rw [List.disjoint_left]
    intro wire degreeMember restMember
    exact (List.disjoint_left.mp (oracleDegreeWires_disjoint_andWork p))
      degreeMember (decoderComparisonAndMember p (by simp [rest, restMember]))
  have compareDisjointScratch : compare.Disjoint scratch := by
    rw [List.disjoint_left]
    intro wire compareMember scratchMember
    exact (List.disjoint_left.mp (oracleCompareWorkWires_disjoint_andWork p))
      compareMember (decoderComparisonAndMember p (by simp [scratch, scratchMember]))
  have compareDisjointRest : compare.Disjoint rest := by
    rw [List.disjoint_left]
    intro wire compareMember restMember
    exact (List.disjoint_left.mp (oracleCompareWorkWires_disjoint_andWork p))
      compareMember (decoderComparisonAndMember p (by simp [rest, restMember]))
  have compareDisjointDegree : compare.Disjoint degree := by
    simpa [compare, degree] using (oracleDegreeWires_disjoint_compareWork p).symm
  have compareScratchNodup : (compare ++ scratch).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨compareNodup, scratchNodup, ?_⟩
    intro compareWire compareMember scratchWire scratchMember equal
    subst scratchWire
    exact (List.disjoint_left.mp compareDisjointScratch compareMember)
      scratchMember
  have compareScratchDegreeNodup : (compare ++ scratch ++ degree).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨compareScratchNodup, degreeNodup, ?_⟩
    intro wire member degreeWire degreeMember
    rcases List.mem_append.mp member with compareMember | scratchMember
    · intro equal
      subst degreeWire
      exact (List.disjoint_left.mp compareDisjointDegree compareMember)
        degreeMember
    · intro equal
      subst degreeWire
      exact (List.disjoint_left.mp degreeDisjointScratch degreeMember)
        scratchMember
  have allNodup : (compare ++ scratch ++ degree ++ rest).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨compareScratchDegreeNodup, restNodup, ?_⟩
    intro wire member restWire restMember
    rcases List.mem_append.mp member with compareScratchMember | degreeMember
    · rcases List.mem_append.mp compareScratchMember with
        compareMember | scratchMember
      · intro equal
        subst restWire
        exact (List.disjoint_left.mp compareDisjointRest compareMember) restMember
      · exact scratchSeparatedRest wire scratchMember restWire restMember
    · intro equal
      subst restWire
      exact (List.disjoint_left.mp degreeDisjointRest degreeMember) restMember
  simpa [compare, scratch, degree, rest, decoderComparisonFlagWires,
    List.append_assoc] using allNodup

/-- 複数sourceから同じtargetへCNOTを順に適用する補助回路。 -/
def xorSourceParityIntoTargetCircuit
    {ancillaQubits systemQubits : Nat}
    (sources : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    Circuit (ReversibleGate ancillaQubits systemQubits) :=
  Circuit.sequence <| sources.map fun source => safeCnot source target

/-- 同じtargetへのCNOT列はsource値のparityが1のときだけtargetを反転する。 -/
theorem runBasis_xorSourceParityIntoTargetCircuit
    {ancillaQubits systemQubits : Nat}
    (sources : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (targetAbsent : target ∉ sources) :
    (xorSourceParityIntoTargetCircuit sources target).runBasis reversibleGatePermutation input =
      if boolParity (readWires sources input) then
        xBasisAction target input
      else input := by
  induction sources generalizing input with
  | nil => rfl
  | cons source sources inductionHypothesis =>
      have sourceDifferentTarget : source ≠ target := by
        intro equal
        apply targetAbsent
        simp [equal]
      have targetAbsentTail : target ∉ sources := by
        intro member
        apply targetAbsent
        simp [member]
      simp only [xorSourceParityIntoTargetCircuit, List.map_cons, Circuit.sequence,
        runBasis_local_core_sequence_cons]
      rw [runBasis_local_safeCnot source target sourceDifferentTarget]
      change
        (xorSourceParityIntoTargetCircuit sources target).runBasis reversibleGatePermutation
            (cnotBasisAction source target input) = _
      rw [inductionHypothesis (cnotBasisAction source target input) targetAbsentTail]
      have tailValues :
          readWires sources (cnotBasisAction source target input) =
            readWires sources input := by
        apply List.map_congr_left
        intro wire member
        exact cnotBasisAction_other source target wire (by
          intro equal
          subst wire
          exact targetAbsentTail member) input
      rw [tailValues]
      cases headValue : input source <;>
        cases tailParity : boolParity (readWires sources input)
      all_goals
        change boolParity (List.map input sources) = _ at tailParity
        simp [readWires, boolParity, headValue, tailParity,
          cnotBasisAction_eq_conditional_x, xBasisAction_involutive]

/-- clean target上では同じtargetへのCNOT列がsource値parityそのものを書き込む。 -/
theorem xorSourceParityIntoTargetCircuit_target_value
    {ancillaQubits systemQubits : Nat}
    (sources : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (targetAbsent : target ∉ sources)
    (targetZero : input target = false) :
    (xorSourceParityIntoTargetCircuit sources target).runBasis reversibleGatePermutation input target =
      boolParity (readWires sources input) := by
  rw [runBasis_xorSourceParityIntoTargetCircuit sources target input targetAbsent]
  cases parity : boolParity (readWires sources input) <;>
    simp [targetZero]

/-- 同じtargetへのCNOT列はtarget以外のwireを変更しない。 -/
theorem runBasis_xorSourceParityIntoTargetCircuit_other
    {ancillaQubits systemQubits : Nat}
    (sources : List (Wire ancillaQubits systemQubits))
    (target wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (targetAbsent : target ∉ sources)
    (wireDifferent : wire ≠ target) :
    (xorSourceParityIntoTargetCircuit sources target).runBasis reversibleGatePermutation input wire =
      input wire := by
  rw [runBasis_xorSourceParityIntoTargetCircuit sources target input targetAbsent]
  by_cases parity : boolParity (readWires sources input) <;>
    simp [parity, wireDifferent]

/-- degree bit列のsuffix parityを各slotの現在値へXORした純粋な参照結果。 -/
def slotPresenceBits : List Bool → Nat → List Bool → List Bool
  | _, _, [] => []
  | degreeBits, slot, presentBit :: presentBits =>
      (if boolParity (degreeBits.drop slot) then !presentBit else presentBit) ::
        slotPresenceBits degreeBits (slot + 1) presentBits

/-- `xorDegreeSuffixParityIntoSlotPresenceCircuit`は出力対象の存在flag列外のwireを変更しない。 -/
theorem runBasis_xorDegreeSuffixParityIntoSlotPresenceCircuit_outside
    {ancillaQubits systemQubits : Nat}
    (degreeFlags presentFlags : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (degreeDisjointPresent : degreeFlags.Disjoint presentFlags)
    (outside : wire ∉ presentFlags) :
    (xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags slot presentFlags).runBasis
        reversibleGatePermutation input wire = input wire := by
  induction presentFlags generalizing slot input with
  | nil => rfl
  | cons presentFlag presentFlags inductionHypothesis =>
      have presentAbsentDegree : presentFlag ∉ degreeFlags := by
        intro member
        exact (List.disjoint_left.mp degreeDisjointPresent) member (by simp)
      have presentAbsentDropped : presentFlag ∉ degreeFlags.drop slot := by
        intro member
        exact presentAbsentDegree (List.mem_of_mem_drop member)
      have wireDifferent : wire ≠ presentFlag := by
        intro equal
        apply outside
        simp [equal]
      have tailOutside : wire ∉ presentFlags := by
        intro member
        apply outside
        simp [member]
      have degreeDisjointTail : degreeFlags.Disjoint presentFlags := by
        exact (List.disjoint_cons_right.mp degreeDisjointPresent).2
      rw [xorDegreeSuffixParityIntoSlotPresenceCircuit, runBasis_seq]
      change
        (xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags (slot + 1) presentFlags).runBasis
            reversibleGatePermutation
            ((xorSourceParityIntoTargetCircuit (degreeFlags.drop slot) presentFlag).runBasis
              reversibleGatePermutation input) wire = input wire
      rw [inductionHypothesis (slot + 1)
        ((xorSourceParityIntoTargetCircuit (degreeFlags.drop slot) presentFlag).runBasis
          reversibleGatePermutation input) degreeDisjointTail tailOutside]
      exact runBasis_xorSourceParityIntoTargetCircuit_other (degreeFlags.drop slot) presentFlag wire
        input presentAbsentDropped wireDifferent

/--
互いに素で重複のないdegree/present配置では、slot存在回路の読出し値がdegree suffixの
parityを各present bitへXORした参照結果に一致する。
-/
theorem readWires_xorDegreeSuffixParityIntoSlotPresenceCircuit
    {ancillaQubits systemQubits : Nat}
    (degreeFlags presentFlags : List (Wire ancillaQubits systemQubits))
    (slot : Nat)
    (input : JointBasis ancillaQubits systemQubits)
    (degreeDisjointPresent : degreeFlags.Disjoint presentFlags)
    (presentNodup : presentFlags.Nodup) :
    readWires presentFlags
        ((xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags slot presentFlags).runBasis
          reversibleGatePermutation input) =
      slotPresenceBits (readWires degreeFlags input) slot
        (readWires presentFlags input) := by
  induction presentFlags generalizing slot input with
  | nil => rfl
  | cons presentFlag presentFlags inductionHypothesis =>
      have presentAbsentDegree : presentFlag ∉ degreeFlags := by
        intro member
        exact (List.disjoint_left.mp degreeDisjointPresent) member (by simp)
      have presentAbsentDropped : presentFlag ∉ degreeFlags.drop slot := by
        intro member
        exact presentAbsentDegree (List.mem_of_mem_drop member)
      have degreeDisjointTail : degreeFlags.Disjoint presentFlags := by
        exact (List.disjoint_cons_right.mp degreeDisjointPresent).2
      have presentFresh : presentFlag ∉ presentFlags :=
        (List.nodup_cons.mp presentNodup).1
      have tailNodup : presentFlags.Nodup :=
        (List.nodup_cons.mp presentNodup).2
      let firstState :=
        (xorSourceParityIntoTargetCircuit (degreeFlags.drop slot) presentFlag).runBasis
          reversibleGatePermutation input
      have degreeValues : readWires degreeFlags firstState =
          readWires degreeFlags input := by
        apply List.map_congr_left
        intro wire member
        exact runBasis_xorSourceParityIntoTargetCircuit_other (degreeFlags.drop slot) presentFlag wire
          input presentAbsentDropped (by
            intro equal
            subst wire
            exact presentAbsentDegree member)
      have tailValues : readWires presentFlags firstState =
          readWires presentFlags input := by
        apply List.map_congr_left
        intro wire member
        exact runBasis_xorSourceParityIntoTargetCircuit_other (degreeFlags.drop slot) presentFlag wire
          input presentAbsentDropped (by
            intro equal
            subst wire
            exact presentFresh member)
      have headAfterFirst : firstState presentFlag =
          if boolParity (readWires (degreeFlags.drop slot) input) then
            !input presentFlag
          else input presentFlag := by
        change
          (xorSourceParityIntoTargetCircuit (degreeFlags.drop slot) presentFlag).runBasis
              reversibleGatePermutation input presentFlag = _
        rw [runBasis_xorSourceParityIntoTargetCircuit (degreeFlags.drop slot) presentFlag input
          presentAbsentDropped]
        by_cases parity : boolParity (readWires (degreeFlags.drop slot) input) <;>
          simp [parity]
      have headAfterTail :
          (xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags (slot + 1) presentFlags).runBasis
              reversibleGatePermutation firstState presentFlag =
            firstState presentFlag := by
        exact runBasis_xorDegreeSuffixParityIntoSlotPresenceCircuit_outside degreeFlags presentFlags (slot + 1)
          presentFlag firstState degreeDisjointTail presentFresh
      have tailResult :
          readWires presentFlags
              ((xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags (slot + 1) presentFlags).runBasis
                reversibleGatePermutation firstState) =
            slotPresenceBits (readWires degreeFlags input) (slot + 1)
              (readWires presentFlags input) := by
        rw [inductionHypothesis (slot + 1) firstState degreeDisjointTail tailNodup]
        rw [degreeValues, tailValues]
      rw [xorDegreeSuffixParityIntoSlotPresenceCircuit, runBasis_seq]
      change
        ((xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags (slot + 1) presentFlags).runBasis
            reversibleGatePermutation firstState) presentFlag ::
          readWires presentFlags
            ((xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags (slot + 1) presentFlags).runBasis
              reversibleGatePermutation firstState) = _
      rw [headAfterTail, headAfterFirst, tailResult]
      simp only [slotPresenceBits, readWires, List.map_cons]
      congr 2
      simp [List.map_drop]

/-- `slotPresenceCircuit`の読出し仕様はslot 0から始まるsuffix parityである。 -/
theorem readWires_slotPresenceCircuit
    {ancillaQubits systemQubits : Nat}
    (degreeFlags presentFlags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (degreeDisjointPresent : degreeFlags.Disjoint presentFlags)
    (presentNodup : presentFlags.Nodup) :
    readWires presentFlags
        ((slotPresenceCircuit degreeFlags presentFlags).runBasis
          reversibleGatePermutation input) =
      slotPresenceBits (readWires degreeFlags input) 0
        (readWires presentFlags input) := by
  exact readWires_xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags presentFlags 0 input
    degreeDisjointPresent presentNodup

/-- 入力delimiter位置が存在しなければdegree境界回路は恒等回路である。 -/
theorem runBasis_degreeBoundaryCircuit_input_none
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires : List (Wire ancillaQubits systemQubits))
    (degree : Nat) (flag : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (inputNone : inputWires[wordWidth * (degree + 1)]? = none) :
    (degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
        reversibleGatePermutation input = input := by
  simp [degreeBoundaryCircuit, inputNone, Circuit.runBasis]

/--
入力delimiterは存在するが右側suffix wireが存在しない境界では、delimiterをflagへ
XORする。
-/
theorem runBasis_degreeBoundaryCircuit_suffix_none
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires : List (Wire ancillaQubits systemQubits))
    (degree : Nat)
    (delimiter flag : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (inputSome : inputWires[wordWidth * (degree + 1)]? = some delimiter)
    (suffixNone : suffixWires[wordWidth * (degree + 1) + 1]? = none)
    (different : delimiter ≠ flag) :
    (degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
        reversibleGatePermutation input =
      cnotBasisAction delimiter flag input := by
  simp [degreeBoundaryCircuit, inputSome, suffixNone,
    ReversibleCircuit.safeCnot, different]

/-- 右側suffix wireがない最終境界では、clean flagへdelimiter値をそのまま書く。 -/
theorem degreeBoundaryCircuit_suffix_none_flag_value
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires : List (Wire ancillaQubits systemQubits))
    (degree : Nat)
    (delimiter flag : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (inputSome : inputWires[wordWidth * (degree + 1)]? = some delimiter)
    (suffixNone : suffixWires[wordWidth * (degree + 1) + 1]? = none)
    (different : delimiter ≠ flag)
    (flagZero : input flag = false) :
    (degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
        reversibleGatePermutation input flag = input delimiter := by
  rw [runBasis_degreeBoundaryCircuit_suffix_none wordWidth inputWires suffixWires
    degree delimiter flag input inputSome suffixNone different]
  cases delimiterValue : input delimiter <;>
    simp [cnotBasisAction, delimiterValue, flagZero]

/--
delimiterと右側suffix wireがともに存在する境界では、`delimiter AND NOT suffix`の
ときだけflagを反転する。
-/
theorem runBasis_degreeBoundaryCircuit_some
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires : List (Wire ancillaQubits systemQubits))
    (degree : Nat)
    (delimiter laterNonzero flag : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (inputSome : inputWires[wordWidth * (degree + 1)]? = some delimiter)
    (suffixSome : suffixWires[wordWidth * (degree + 1) + 1]? = some laterNonzero)
    (delimiterDifferentLater : delimiter ≠ laterNonzero)
    (delimiterDifferentFlag : delimiter ≠ flag)
    (laterDifferentFlag : laterNonzero ≠ flag) :
    (degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
        reversibleGatePermutation input =
      if input delimiter && !input laterNonzero then
        xBasisAction flag input
      else input := by
  simp only [degreeBoundaryCircuit, inputSome, suffixSome, runBasis_seq,
    runBasis_x,
    runBasis_safeToffoli delimiter laterNonzero flag delimiterDifferentLater
      delimiterDifferentFlag laterDifferentFlag]
  funext wire
  cases delimiterValue : input delimiter <;>
    cases laterValue : input laterNonzero <;>
    by_cases wireFlag : wire = flag <;>
    by_cases wireLater : wire = laterNonzero <;>
    simp [xBasisAction, toffoliBasisAction, delimiterValue, laterValue,
      delimiterDifferentLater,
      laterDifferentFlag, laterDifferentFlag.symm, wireFlag, wireLater]

/-- clean flag上では境界回路の出力bitが`delimiter AND NOT suffix`そのものになる。 -/
theorem degreeBoundaryCircuit_flag_value
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires : List (Wire ancillaQubits systemQubits))
    (degree : Nat)
    (delimiter laterNonzero flag : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (inputSome : inputWires[wordWidth * (degree + 1)]? = some delimiter)
    (suffixSome : suffixWires[wordWidth * (degree + 1) + 1]? = some laterNonzero)
    (delimiterDifferentLater : delimiter ≠ laterNonzero)
    (delimiterDifferentFlag : delimiter ≠ flag)
    (laterDifferentFlag : laterNonzero ≠ flag)
    (flagZero : input flag = false) :
    (degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
        reversibleGatePermutation input flag =
      (input delimiter && !input laterNonzero) := by
  rw [runBasis_degreeBoundaryCircuit_some wordWidth inputWires suffixWires degree
    delimiter laterNonzero flag input inputSome suffixSome delimiterDifferentLater
    delimiterDifferentFlag laterDifferentFlag]
  cases delimiterValue : input delimiter <;>
    cases laterValue : input laterNonzero <;>
    simp [flagZero, xBasisAction]

/-- Bool列上でdegree境界flagが表す`delimiter AND NOT later-suffix`条件。 -/
def degreeBoundaryBit (wordWidth : Nat)
    (inputBits suffixBits : List Bool) (degree : Nat) : Bool :=
  let boundary := wordWidth * (degree + 1)
  match inputBits[boundary]?, suffixBits[boundary + 1]? with
  | some delimiter, some laterNonzero => delimiter && !laterNonzero
  | some delimiter, none => delimiter
  | none, _ => false

/-- Option分岐による境界条件は、範囲外を0とする`getD`表示へ統一できる。 -/
theorem degreeBoundaryBit_eq_getD (wordWidth : Nat)
    (inputBits suffixBits : List Bool) (degree : Nat) :
    degreeBoundaryBit wordWidth inputBits suffixBits degree =
      (inputBits[wordWidth * (degree + 1)]?.getD false &&
        !suffixBits[wordWidth * (degree + 1) + 1]?.getD false) := by
  simp only [degreeBoundaryBit]
  cases inputBits[wordWidth * (degree + 1)]? <;>
    cases suffixBits[wordWidth * (degree + 1) + 1]? <;>
    simp

/--
`index`位置が1で`start ≤ index`なら、`start`以降のBool列の論理和は1である。
-/
theorem any_drop_eq_true_of_le_getD
    (bits : List Bool) (start index : Nat)
    (ordered : start ≤ index)
    (value : bits[index]?.getD false = true) :
    (bits.drop start).any id = true := by
  induction start generalizing bits index with
  | zero =>
      have someValue : bits[index]? = some true := by
        cases found : bits[index]? with
        | none => simp [found] at value
        | some bit =>
            cases bit <;> simp_all
      have member : true ∈ bits :=
        List.mem_iff_getElem?.mpr ⟨index, someValue⟩
      simpa using member
  | succ start inductionHypothesis =>
      cases bits with
      | nil => simp at value
      | cons bit bits =>
          cases index with
          | zero => omega
          | succ index =>
              simp only [List.drop_succ_cons]
              apply inductionHypothesis bits index
              · omega
              · simpa using value

/-- 指定位置以降の全`getD`値が0なら、そのsuffix全体の論理和も0である。 -/
theorem any_drop_eq_false_of_forall_getD
    (bits : List Bool) (start : Nat)
    (allZero : ∀ index, start ≤ index → bits[index]?.getD false = false) :
    (bits.drop start).any id = false := by
  induction bits generalizing start with
  | nil => simp
  | cons bit bits inductionHypothesis =>
      cases start with
      | zero =>
          have headZero : bit = false := by
            simpa using allZero 0 (by omega)
          have tailZero : ∀ index, 0 ≤ index → bits[index]?.getD false = false := by
            intro index _
            simpa using allZero (index + 1) (by omega)
          rw [headZero]
          simpa using inductionHypothesis 0 tailZero
      | succ start =>
          simp only [List.drop_succ_cons]
          apply inductionHypothesis start
          intro index ordered
          simpa using allZero (index + 1) (by omega)

/-- 有限register基底を物理添字順のBool列へ変換する。 -/
def registerBitList {width : Nat} (basis : RegisterBasis width) : List Bool :=
  (List.finRange width).map basis

/-- register Bool列の`getD`は範囲内なら基底bit、範囲外なら0である。 -/
theorem registerBitList_getD
    {width : Nat} (basis : RegisterBasis width) (index : Nat) :
    (registerBitList basis)[index]?.getD false =
      if inRange : index < width then basis ⟨index, inRange⟩ else false := by
  by_cases inRange : index < width
  · simp [registerBitList, inRange]
  · simp [registerBitList, inRange]

/-- 合法delimiter符号のactive slotから切り出したwordは、そのsiteの全bitに一致する。 -/
theorem delimiterEncoding_activeWord
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin configuration.1.card) :
    ((registerBitList (delimiterEncoding configuration)).drop
        (slot.val * p.wordWidth)).take p.wordWidth =
      List.ofFn fun bit => siteBit p (configuration.siteAt slot) bit := by
  apply List.ext_getElem?
  intro index
  by_cases inRange : index < p.wordWidth
  · have physicalInRange : slot.val * p.wordWidth + index < p.systemWidth := by
      have slotNext : slot.val + 1 ≤ configuration.1.card :=
        Nat.succ_le_of_lt slot.isLt
      have cardLe := configuration.2.2
      calc
        slot.val * p.wordWidth + index <
            slot.val * p.wordWidth + p.wordWidth :=
          Nat.add_lt_add_left inRange _
        _ = (slot.val + 1) * p.wordWidth := by rw [Nat.succ_mul]
        _ ≤ p.K * p.wordWidth :=
          Nat.mul_le_mul_right p.wordWidth (le_trans slotNext cardLe)
        _ = p.wordWidth * p.K := Nat.mul_comm _ _
        _ < p.wordWidth * p.K + 1 := Nat.lt_succ_self _
        _ = p.systemWidth := rfl
    have leftSome :
        (((registerBitList (delimiterEncoding configuration)).drop
          (slot.val * p.wordWidth)).take p.wordWidth)[index]? =
          some (delimiterEncoding configuration
            ⟨slot.val * p.wordWidth + index, physicalInRange⟩) := by
      simp [registerBitList, inRange, physicalInRange]
    rw [leftSome]
    have physicalWireEq :
        (⟨slot.val * p.wordWidth + index, physicalInRange⟩ :
          Fin p.systemWidth) =
        configurationWordIndex configuration slot ⟨index, inRange⟩ := by
      apply Fin.ext
      simp [configurationWordIndex, Nat.mul_comm]
    rw [physicalWireEq, delimiterEncoding_word]
    simp only [List.getElem?_ofFn, inRange, dite_true]
  · have leftNone :
        (((registerBitList (delimiterEncoding configuration)).drop
          (slot.val * p.wordWidth)).take p.wordWidth)[index]? = none := by
      apply List.getElem?_eq_none
      exact le_trans (List.length_take_le _ _) (Nat.le_of_not_gt inRange)
    have rightNone :
        (List.ofFn fun bit => siteBit p (configuration.siteAt slot) bit)[index]? =
          none := by
      simp [inRange]
    rw [leftNone, rightNone]

/-- 合法delimiterをword分割した列のactive添字には対応するsite wordが入る。 -/
theorem splitBitWords_delimiter_active_get
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Nat) (active : slot < configuration.1.card) :
    (splitBitWords p.wordWidth p.K
      (registerBitList (delimiterEncoding configuration)))[slot]? =
      some (List.ofFn fun bit =>
        siteBit p (configuration.siteAt ⟨slot, active⟩) bit) := by
  have slotInRange : slot < p.K := lt_of_lt_of_le active configuration.2.2
  rw [show
    (splitBitWords p.wordWidth p.K
      (registerBitList (delimiterEncoding configuration)))[slot]? =
      some (((registerBitList (delimiterEncoding configuration)).drop
        (slot * p.wordWidth)).take p.wordWidth) by
          simp [splitBitWords, slotInRange]]
  congr 1
  exact delimiterEncoding_activeWord configuration ⟨slot, active⟩

/-- 実際のdelimiter符号Bool列はdelimiter位置が1で、それより後ろの論理和が0である。 -/
theorem delimiterEncoding_boundaryShape
    {p : QParameters} (configuration : QConfiguration p) :
    let bits := registerBitList (delimiterEncoding configuration)
    bits[p.wordWidth * configuration.1.card]?.getD false = true ∧
      (bits.drop (p.wordWidth * configuration.1.card + 1)).any id = false := by
  dsimp only
  constructor
  · rw [registerBitList_getD]
    have cardLe := configuration.2.2
    have inRange : p.wordWidth * configuration.1.card < p.systemWidth := by
      simp only [QParameters.systemWidth]
      exact Nat.lt_succ_of_le (Nat.mul_le_mul_left p.wordWidth cardLe)
    rw [dif_pos inRange]
    simpa [delimiterIndex] using delimiterEncoding_delimiter configuration
  · apply any_drop_eq_false_of_forall_getD
    intro index after
    rw [registerBitList_getD]
    split
    · rename_i inRange
      apply delimiterEncoding_after_delimiter configuration ⟨index, inRange⟩
      change p.wordWidth * configuration.1.card < index
      omega
    · rfl

/-- delimiter位置とそれより後ろが0という条件から、全degree境界はone-hotになる。 -/
theorem degreeBoundaryBit_oneHot_of_delimiter
    (wordWidth bitsDegree degree : Nat) (bits : List Bool)
    (wordWidthPositive : 0 < wordWidth)
    (delimiterValue : bits[wordWidth * bitsDegree]?.getD false = true)
    (afterDelimiterZero : (bits.drop (wordWidth * bitsDegree + 1)).any id = false) :
    degreeBoundaryBit wordWidth bits (suffixOrBits bits) degree =
      decide (degree + 1 = bitsDegree) := by
  rw [degreeBoundaryBit_eq_getD]
  rw [suffixOrBits_getD]
  by_cases equalDegree : degree + 1 = bitsDegree
  · subst bitsDegree
    simp [delimiterValue, afterDelimiterZero]
  · by_cases beforeDegree : degree + 1 < bitsDegree
    · have boundaryBefore :
          wordWidth * (degree + 1) + 1 ≤ wordWidth * bitsDegree := by
        have strictProduct :
            wordWidth * (degree + 1) < wordWidth * bitsDegree :=
          Nat.mul_lt_mul_of_pos_left beforeDegree wordWidthPositive
        omega
      have laterOne :
          (bits.drop (wordWidth * (degree + 1) + 1)).any id = true :=
        any_drop_eq_true_of_le_getD bits
          (wordWidth * (degree + 1) + 1) (wordWidth * bitsDegree)
          boundaryBefore delimiterValue
      simp [equalDegree, laterOne]
    · have afterDegree : bitsDegree < degree + 1 := by omega
      have delimiterBeforeBoundary :
          wordWidth * bitsDegree + 1 ≤ wordWidth * (degree + 1) := by
        have strictProduct :
            wordWidth * bitsDegree < wordWidth * (degree + 1) :=
          Nat.mul_lt_mul_of_pos_left afterDegree wordWidthPositive
        omega
      have boundaryZero :
          bits[wordWidth * (degree + 1)]?.getD false = false := by
        cases boundaryValue : bits[wordWidth * (degree + 1)]?.getD false with
        | false => rfl
        | true =>
            have laterOne := any_drop_eq_true_of_le_getD bits
              (wordWidth * bitsDegree + 1) (wordWidth * (degree + 1))
              delimiterBeforeBoundary boundaryValue
            rw [afterDelimiterZero] at laterOne
            contradiction
      simp [equalDegree, boundaryZero]

/-- 実際の合法delimiter符号ではdegree境界条件が粒子数に対応するone-hotになる。 -/
theorem degreeBoundaryBit_delimiterEncoding_oneHot
    {p : QParameters} (configuration : QConfiguration p) (degree : Nat) :
    let bits := registerBitList (delimiterEncoding configuration)
    degreeBoundaryBit p.wordWidth bits (suffixOrBits bits) degree =
      decide (degree + 1 = configuration.1.card) := by
  dsimp only
  rcases delimiterEncoding_boundaryShape configuration with
    ⟨delimiterValue, afterDelimiterZero⟩
  exact degreeBoundaryBit_oneHot_of_delimiter p.wordWidth configuration.1.card degree
    (registerBitList (delimiterEncoding configuration))
    (by simp [QParameters.wordWidth, p.q_pos]) delimiterValue afterDelimiterZero

/-- 指定開始degreeからone-hot判定を指定個数だけ並べる純粋なBool列。 -/
def degreeOneHotFrom : Nat → Nat → Nat → List Bool
  | 0, _, _ => []
  | count + 1, particleCount, degree =>
      decide (degree + 1 = particleCount) ::
        degreeOneHotFrom count particleCount (degree + 1)

/-- one-hot列のparityは粒子数が表現区間内にあるとき、かつそのときだけ1である。 -/
theorem boolParity_degreeOneHotFrom
    (count particleCount degree : Nat) :
    boolParity (degreeOneHotFrom count particleCount degree) =
      decide (degree < particleCount ∧ particleCount ≤ degree + count) := by
  induction count generalizing degree with
  | zero => simp [degreeOneHotFrom, boolParity]
  | succ count inductionHypothesis =>
      simp only [degreeOneHotFrom, boolParity]
      rw [inductionHypothesis (degree + 1)]
      by_cases atHead : degree + 1 = particleCount
      · simp [atHead]
        omega
      · by_cases inTail : degree + 1 < particleCount ∧
          particleCount ≤ degree + 1 + count
        · simp [atHead, inTail]
          omega
        · simp [atHead, inTail]
          omega

/-- 合法配置の`K`本degree one-hot列は必ず奇parity、すなわちちょうど一個の1を持つ。 -/
theorem boolParity_degreeOneHot_configuration
    {p : QParameters} (configuration : QConfiguration p) :
    boolParity (degreeOneHotFrom p.K configuration.1.card 0) = true := by
  rw [boolParity_degreeOneHotFrom]
  simp only [zero_add, decide_eq_true_eq]
  exact configuration.2

/-- one-hot列を指定数dropすると、開始degreeと残り個数を同じだけ進めた列になる。 -/
theorem degreeOneHotFrom_drop
    (count particleCount degree slot : Nat) (slotLe : slot ≤ count) :
    (degreeOneHotFrom count particleCount degree).drop slot =
      degreeOneHotFrom (count - slot) particleCount (degree + slot) := by
  induction slot generalizing count degree with
  | zero => simp
  | succ slot inductionHypothesis =>
      cases count with
      | zero => omega
      | succ count =>
          simp only [degreeOneHotFrom, List.drop_succ_cons]
          have result := inductionHypothesis count (degree + 1) (by omega)
          have degreeEqual : degree + 1 + slot = degree + (slot + 1) := by omega
          simpa [Nat.succ_sub_succ_eq_sub, degreeEqual] using result

/-- one-hot列をslotまでdropしたsuffix parityはactive粒子slotの存在判定に等しい。 -/
theorem boolParity_degreeOneHotFrom_drop
    (count particleCount degree slot : Nat) (slotLe : slot ≤ count) :
    boolParity ((degreeOneHotFrom count particleCount degree).drop slot) =
      decide (degree + slot < particleCount ∧ particleCount ≤ degree + count) := by
  rw [degreeOneHotFrom_drop count particleCount degree slot slotLe]
  rw [boolParity_degreeOneHotFrom]
  have upperEqual : degree + slot + (count - slot) = degree + count := by omega
  rw [upperEqual]

/-- 指定slotから粒子数未満のslotだけを1にした存在flag参照列。 -/
def presenceBitsFrom : Nat → Nat → Nat → List Bool
  | 0, _, _ => []
  | count + 1, particleCount, slot =>
      decide (slot < particleCount) ::
        presenceBitsFrom count particleCount (slot + 1)

/-- clean present列へone-hot degreeのsuffix parityを書けば、先頭粒子数個だけが1になる。 -/
theorem slotPresenceBits_degreeOneHot
    (degreeCount particleCount slot presentCount : Nat)
    (withinDegree : slot + presentCount ≤ degreeCount)
    (particleBound : particleCount ≤ degreeCount) :
    slotPresenceBits (degreeOneHotFrom degreeCount particleCount 0) slot
        (List.replicate presentCount false) =
      presenceBitsFrom presentCount particleCount slot := by
  induction presentCount generalizing slot with
  | zero => rfl
  | succ presentCount inductionHypothesis =>
      simp only [List.replicate_succ, slotPresenceBits, presenceBitsFrom]
      rw [boolParity_degreeOneHotFrom_drop degreeCount particleCount 0 slot
        (by omega)]
      rw [show decide (0 + slot < particleCount ∧ particleCount ≤ 0 + degreeCount) =
          decide (slot < particleCount) by simp [particleBound]]
      rw [inductionHypothesis (slot + 1) (by omega)]
      cases decide (slot < particleCount) <;> rfl

/--
input・suffix・flagが互いに分離されflagが0なら、一個の境界回路は純粋な
`degreeBoundaryBit`をflagへ書く。
-/
theorem degreeBoundaryCircuit_flag_value_general
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires : List (Wire ancillaQubits systemQubits))
    (degree : Nat) (flag : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (flagAbsentInput : flag ∉ inputWires)
    (flagAbsentSuffix : flag ∉ suffixWires)
    (flagZero : input flag = false) :
    (degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
        reversibleGatePermutation input flag =
      degreeBoundaryBit wordWidth (readWires inputWires input)
        (readWires suffixWires input) degree := by
  let boundary := wordWidth * (degree + 1)
  cases inputAt : inputWires[boundary]? with
  | none =>
      rw [runBasis_degreeBoundaryCircuit_input_none wordWidth inputWires suffixWires
        degree flag input inputAt]
      simp [degreeBoundaryBit, boundary, readWires, List.getElem?_map, inputAt,
        flagZero]
  | some delimiter =>
      have delimiterMember : delimiter ∈ inputWires :=
        List.mem_iff_getElem?.mpr ⟨boundary, inputAt⟩
      have delimiterDifferentFlag : delimiter ≠ flag := by
        intro equal
        subst delimiter
        exact flagAbsentInput delimiterMember
      cases suffixAt : suffixWires[boundary + 1]? with
      | none =>
          rw [degreeBoundaryCircuit_suffix_none_flag_value wordWidth inputWires
            suffixWires degree delimiter flag input inputAt suffixAt
            delimiterDifferentFlag flagZero]
          simp [degreeBoundaryBit, boundary, readWires, List.getElem?_map,
            inputAt, suffixAt]
      | some laterNonzero =>
          have laterMember : laterNonzero ∈ suffixWires :=
            List.mem_iff_getElem?.mpr ⟨boundary + 1, suffixAt⟩
          have laterDifferentFlag : laterNonzero ≠ flag := by
            intro equal
            subst laterNonzero
            exact flagAbsentSuffix laterMember
          have delimiterDifferentLater : delimiter ≠ laterNonzero := by
            intro equal
            subst laterNonzero
            exact (List.disjoint_left.mp inputDisjointSuffix)
              delimiterMember laterMember
          rw [degreeBoundaryCircuit_flag_value wordWidth inputWires suffixWires
            degree delimiter laterNonzero flag input inputAt suffixAt
            delimiterDifferentLater delimiterDifferentFlag laterDifferentFlag flagZero]
          simp [degreeBoundaryBit, boundary, readWires, List.getElem?_map,
            inputAt, suffixAt]

/--
分離layout上の一個の境界回路は、純粋な境界条件が1のときだけflagへXを作用させる。
-/
theorem runBasis_degreeBoundaryCircuit_general
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires : List (Wire ancillaQubits systemQubits))
    (degree : Nat) (flag : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (flagAbsentInput : flag ∉ inputWires)
    (flagAbsentSuffix : flag ∉ suffixWires) :
    (degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
        reversibleGatePermutation input =
      if degreeBoundaryBit wordWidth (readWires inputWires input)
          (readWires suffixWires input) degree then
        xBasisAction flag input
      else input := by
  let boundary := wordWidth * (degree + 1)
  cases inputAt : inputWires[boundary]? with
  | none =>
      rw [runBasis_degreeBoundaryCircuit_input_none wordWidth inputWires suffixWires
        degree flag input inputAt]
      simp [degreeBoundaryBit, boundary, readWires, List.getElem?_map, inputAt]
  | some delimiter =>
      have delimiterMember : delimiter ∈ inputWires :=
        List.mem_iff_getElem?.mpr ⟨boundary, inputAt⟩
      have delimiterDifferentFlag : delimiter ≠ flag := by
        intro equal
        subst delimiter
        exact flagAbsentInput delimiterMember
      cases suffixAt : suffixWires[boundary + 1]? with
      | none =>
          rw [runBasis_degreeBoundaryCircuit_suffix_none wordWidth inputWires
            suffixWires degree delimiter flag input inputAt suffixAt
            delimiterDifferentFlag]
          rw [cnotBasisAction_eq_conditional_x]
          simp [degreeBoundaryBit, boundary, readWires, List.getElem?_map,
            inputAt, suffixAt]
      | some laterNonzero =>
          have laterMember : laterNonzero ∈ suffixWires :=
            List.mem_iff_getElem?.mpr ⟨boundary + 1, suffixAt⟩
          have laterDifferentFlag : laterNonzero ≠ flag := by
            intro equal
            subst laterNonzero
            exact flagAbsentSuffix laterMember
          have delimiterDifferentLater : delimiter ≠ laterNonzero := by
            intro equal
            subst laterNonzero
            exact (List.disjoint_left.mp inputDisjointSuffix)
              delimiterMember laterMember
          rw [runBasis_degreeBoundaryCircuit_some wordWidth inputWires suffixWires
            degree delimiter laterNonzero flag input inputAt suffixAt
            delimiterDifferentLater delimiterDifferentFlag laterDifferentFlag]
          simp [degreeBoundaryBit, boundary, readWires, List.getElem?_map,
            inputAt, suffixAt]

/-- 分離layout上の境界回路はflag以外のwireを変更しない。 -/
theorem runBasis_degreeBoundaryCircuit_outside
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires : List (Wire ancillaQubits systemQubits))
    (degree : Nat) (flag wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (flagAbsentInput : flag ∉ inputWires)
    (flagAbsentSuffix : flag ∉ suffixWires)
    (wireDifferent : wire ≠ flag) :
    (degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [runBasis_degreeBoundaryCircuit_general wordWidth inputWires suffixWires degree
    flag input inputDisjointSuffix flagAbsentInput flagAbsentSuffix]
  by_cases enabled : degreeBoundaryBit wordWidth (readWires inputWires input)
      (readWires suffixWires input) degree <;>
    simp [enabled, wireDifferent]

/-- degree番号を進めながら境界条件をflag列へXORした純粋な参照結果。 -/
def degreeBoundaryBits (wordWidth : Nat) (inputBits suffixBits : List Bool) :
    Nat → List Bool → List Bool
  | _, [] => []
  | degree, flagBit :: flagBits =>
      (if degreeBoundaryBit wordWidth inputBits suffixBits degree then
        !flagBit else flagBit) ::
      degreeBoundaryBits wordWidth inputBits suffixBits (degree + 1) flagBits

/-- 合法delimiterとclean flag列から得る境界条件列は粒子数のone-hot列である。 -/
theorem degreeBoundaryBits_delimiterEncoding_oneHot
    {p : QParameters} (configuration : QConfiguration p)
    (count degree : Nat) :
    let bits := registerBitList (delimiterEncoding configuration)
    degreeBoundaryBits p.wordWidth bits (suffixOrBits bits) degree
        (List.replicate count false) =
      degreeOneHotFrom count configuration.1.card degree := by
  dsimp only
  induction count generalizing degree with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, degreeBoundaryBits, degreeOneHotFrom]
      rw [degreeBoundaryBit_delimiterEncoding_oneHot configuration degree]
      rw [inductionHypothesis (degree + 1)]
      cases decide (degree + 1 = configuration.1.card) <;> rfl

/-- 境界回路列は出力対象flag列外のwireを変更しない。 -/
theorem runBasis_degreeBoundarySequence_outside
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires flags : List (Wire ancillaQubits systemQubits))
    (degree : Nat) (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (inputDisjointFlags : inputWires.Disjoint flags)
    (suffixDisjointFlags : suffixWires.Disjoint flags)
    (outside : wire ∉ flags) :
    (degreeBoundarySequence wordWidth inputWires suffixWires degree flags).runBasis
        reversibleGatePermutation input wire = input wire := by
  induction flags generalizing degree input with
  | nil => rfl
  | cons flag flags inductionHypothesis =>
      have flagAbsentInput : flag ∉ inputWires := by
        intro member
        exact (List.disjoint_left.mp inputDisjointFlags) member (by simp)
      have flagAbsentSuffix : flag ∉ suffixWires := by
        intro member
        exact (List.disjoint_left.mp suffixDisjointFlags) member (by simp)
      have inputDisjointTail : inputWires.Disjoint flags :=
        (List.disjoint_cons_right.mp inputDisjointFlags).2
      have suffixDisjointTail : suffixWires.Disjoint flags :=
        (List.disjoint_cons_right.mp suffixDisjointFlags).2
      have wireDifferent : wire ≠ flag := by
        intro equal
        apply outside
        simp [equal]
      have tailOutside : wire ∉ flags := by
        intro member
        apply outside
        simp [member]
      rw [degreeBoundarySequence, runBasis_seq]
      rw [inductionHypothesis (degree + 1)
        ((degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
          reversibleGatePermutation input) inputDisjointTail suffixDisjointTail
        tailOutside]
      exact runBasis_degreeBoundaryCircuit_outside wordWidth inputWires suffixWires
        degree flag wire input inputDisjointSuffix flagAbsentInput flagAbsentSuffix
        wireDifferent

/--
互いに分離されたinput・suffix・flag列では、境界回路列の読出し値が純粋な
`degreeBoundaryBits`に一致する。
-/
theorem readWires_degreeBoundarySequence
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires flags : List (Wire ancillaQubits systemQubits))
    (degree : Nat)
    (input : JointBasis ancillaQubits systemQubits)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (inputDisjointFlags : inputWires.Disjoint flags)
    (suffixDisjointFlags : suffixWires.Disjoint flags)
    (flagsNodup : flags.Nodup) :
    readWires flags
        ((degreeBoundarySequence wordWidth inputWires suffixWires degree flags).runBasis
          reversibleGatePermutation input) =
      degreeBoundaryBits wordWidth (readWires inputWires input)
        (readWires suffixWires input) degree (readWires flags input) := by
  induction flags generalizing degree input with
  | nil => rfl
  | cons flag flags inductionHypothesis =>
      have flagAbsentInput : flag ∉ inputWires := by
        intro member
        exact (List.disjoint_left.mp inputDisjointFlags) member (by simp)
      have flagAbsentSuffix : flag ∉ suffixWires := by
        intro member
        exact (List.disjoint_left.mp suffixDisjointFlags) member (by simp)
      have inputDisjointTail : inputWires.Disjoint flags :=
        (List.disjoint_cons_right.mp inputDisjointFlags).2
      have suffixDisjointTail : suffixWires.Disjoint flags :=
        (List.disjoint_cons_right.mp suffixDisjointFlags).2
      have flagFresh : flag ∉ flags := (List.nodup_cons.mp flagsNodup).1
      have tailNodup : flags.Nodup := (List.nodup_cons.mp flagsNodup).2
      let firstState :=
        (degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
          reversibleGatePermutation input
      have inputValues : readWires inputWires firstState = readWires inputWires input := by
        apply List.map_congr_left
        intro wire member
        exact runBasis_degreeBoundaryCircuit_outside wordWidth inputWires suffixWires
          degree flag wire input inputDisjointSuffix flagAbsentInput flagAbsentSuffix
          (by
            intro equal
            subst wire
            exact flagAbsentInput member)
      have suffixValues : readWires suffixWires firstState =
          readWires suffixWires input := by
        apply List.map_congr_left
        intro wire member
        exact runBasis_degreeBoundaryCircuit_outside wordWidth inputWires suffixWires
          degree flag wire input inputDisjointSuffix flagAbsentInput flagAbsentSuffix
          (by
            intro equal
            subst wire
            exact flagAbsentSuffix member)
      have tailValues : readWires flags firstState = readWires flags input := by
        apply List.map_congr_left
        intro wire member
        exact runBasis_degreeBoundaryCircuit_outside wordWidth inputWires suffixWires
          degree flag wire input inputDisjointSuffix flagAbsentInput flagAbsentSuffix
          (by
            intro equal
            subst wire
            exact flagFresh member)
      have headAfterFirst : firstState flag =
          if degreeBoundaryBit wordWidth (readWires inputWires input)
              (readWires suffixWires input) degree then
            !input flag else input flag := by
        change
          (degreeBoundaryCircuit wordWidth inputWires suffixWires degree flag).runBasis
              reversibleGatePermutation input flag = _
        rw [runBasis_degreeBoundaryCircuit_general wordWidth inputWires suffixWires
          degree flag input inputDisjointSuffix flagAbsentInput flagAbsentSuffix]
        by_cases enabled : degreeBoundaryBit wordWidth (readWires inputWires input)
            (readWires suffixWires input) degree <;>
          simp [enabled]
      have headAfterTail :
          (degreeBoundarySequence wordWidth inputWires suffixWires (degree + 1) flags).runBasis
              reversibleGatePermutation firstState flag = firstState flag := by
        exact runBasis_degreeBoundarySequence_outside wordWidth inputWires suffixWires
          flags (degree + 1) flag firstState inputDisjointSuffix inputDisjointTail
          suffixDisjointTail flagFresh
      have tailResult :
          readWires flags
              ((degreeBoundarySequence wordWidth inputWires suffixWires
                (degree + 1) flags).runBasis reversibleGatePermutation firstState) =
            degreeBoundaryBits wordWidth (readWires inputWires input)
              (readWires suffixWires input) (degree + 1)
              (readWires flags input) := by
        rw [inductionHypothesis (degree + 1) firstState inputDisjointTail
          suffixDisjointTail tailNodup]
        rw [inputValues, suffixValues, tailValues]
      rw [degreeBoundarySequence, runBasis_seq]
      change
        ((degreeBoundarySequence wordWidth inputWires suffixWires
            (degree + 1) flags).runBasis reversibleGatePermutation firstState) flag ::
          readWires flags
            ((degreeBoundarySequence wordWidth inputWires suffixWires
              (degree + 1) flags).runBasis reversibleGatePermutation firstState) = _
      rw [headAfterTail, headAfterFirst, tailResult]
      rfl

/-- reversible OR回路は三本の指定wireを含むsupport内だけを使う。 -/
theorem circuitUsesOnly_reversibleOrXor
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (left right target : Wire ancillaQubits systemQubits)
    (leftMember : left ∈ support) (rightMember : right ∈ support)
    (targetMember : target ∈ support) :
    circuitUsesOnly support (reversibleOrXor left right target) := by
  exact ⟨circuitUsesOnly_safeCnot support left target leftMember targetMember,
    ⟨circuitUsesOnly_safeCnot support right target rightMember targetMember,
      circuitUsesOnly_safeToffoli support left right target
        leftMember rightMember targetMember⟩⟩

/-- suffix OR compute回路はinputとsuffixの和集合内だけを参照する。 -/
theorem circuitUsesOnly_suffixOrCircuit
    {ancillaQubits systemQubits : Nat} :
    ∀ (inputWires suffixWires : List (Wire ancillaQubits systemQubits)),
      circuitUsesOnly (inputWires ++ suffixWires)
        (suffixOrCircuit inputWires suffixWires)
  | [], _ => by simp [suffixOrCircuit, circuitUsesOnly]
  | _ :: _, [] => by simp [suffixOrCircuit, circuitUsesOnly]
  | [inputLast], [suffixLast] =>
      circuitUsesOnly_safeCnot _ inputLast suffixLast (by simp) (by simp)
  | inputHead :: inputNext :: inputTail,
      suffixHead :: suffixNext :: suffixTail => by
      let fullInput := inputHead :: inputNext :: inputTail
      let fullSuffix := suffixHead :: suffixNext :: suffixTail
      let tailInput := inputNext :: inputTail
      let tailSuffix := suffixNext :: suffixTail
      have tailUses :
          circuitUsesOnly (tailInput ++ tailSuffix)
            (suffixOrCircuit tailInput tailSuffix) :=
        circuitUsesOnly_suffixOrCircuit tailInput tailSuffix
      have tailIncluded : ∀ wire ∈ tailInput ++ tailSuffix,
          wire ∈ fullInput ++ fullSuffix := by
        intro wire member
        rcases List.mem_append.mp member with inputMember | suffixMember
        · apply List.mem_append_left fullSuffix
          exact List.mem_cons_of_mem inputHead inputMember
        · apply List.mem_append_right fullInput
          exact List.mem_cons_of_mem suffixHead suffixMember
      have tailUsesFull :
          circuitUsesOnly (fullInput ++ fullSuffix)
            (suffixOrCircuit tailInput tailSuffix) :=
        circuitUsesOnly_mono tailIncluded _ tailUses
      have combineUses :
          circuitUsesOnly (fullInput ++ fullSuffix)
            (reversibleOrXor inputHead suffixNext suffixHead) :=
        circuitUsesOnly_reversibleOrXor _ inputHead suffixNext suffixHead
          (by apply List.mem_append_left; simp [fullInput])
          (by apply List.mem_append_right; simp [fullSuffix])
          (by apply List.mem_append_right; simp [fullSuffix])
      exact ⟨tailUsesFull, combineUses⟩
  | [_], _ :: _ :: _ => by simp [suffixOrCircuit, circuitUsesOnly]
  | _ :: _ :: _, [_] => by simp [suffixOrCircuit, circuitUsesOnly]

/--
delimiter隣接比較列はdegree・word・比較work・各出力flagを含むsupport内だけを使う。
共通の比較scratchを各slotで再利用しても、support外のwireには作用しない。
-/
theorem circuitUsesOnly_decoderComparisonSequence
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (degreeMembers : ∀ wire ∈ degreeFlags, wire ∈ support)
    (compareMembers : ∀ wire ∈ compareWork, wire ∈ support)
    (scratchMembers : ∀ wire ∈ andScratch, wire ∈ support) :
    ∀ (slot : Nat) (words : List (List (Wire ancillaQubits systemQubits)))
      (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits)),
      (∀ word ∈ words, ∀ wire ∈ word, wire ∈ support) →
      (∀ wire ∈ lessFlags, wire ∈ support) →
      (∀ wire ∈ needFlags, wire ∈ support) →
      (∀ wire ∈ goodFlags, wire ∈ support) →
      circuitUsesOnly support
        (decoderComparisonSequence degreeFlags compareWork andScratch slot
          words lessFlags needFlags goodFlags)
  | _, _ :: _ :: _, [], _, _, _, _, _, _ => by
      simp [decoderComparisonSequence, circuitUsesOnly]
  | _, _ :: _ :: _, _ :: _, [], _, _, _, _, _ => by
      simp [decoderComparisonSequence, circuitUsesOnly]
  | _, _ :: _ :: _, _ :: _, _ :: _, [], _, _, _, _ => by
      simp [decoderComparisonSequence, circuitUsesOnly]
  | _, [], _, _, _, _, _, _, _ => by
      simp [decoderComparisonSequence, circuitUsesOnly]
  | _, [_], _, _, _, _, _, _, _ => by
      simp [decoderComparisonSequence, circuitUsesOnly]
  | slot, left :: right :: words, less :: lessFlags,
      need :: needFlags, good :: goodFlags,
      wordMembers, lessMembers, needMembers, goodMembers => by
      have leftMembers : ∀ wire ∈ left, wire ∈ support := by
        intro wire member
        exact wordMembers left (by simp) wire member
      have rightMembers : ∀ wire ∈ right, wire ∈ support := by
        intro wire member
        exact wordMembers right (by simp) wire member
      have lessMember : less ∈ support := lessMembers less (by simp)
      have needMember : need ∈ support := needMembers need (by simp)
      have goodMember : good ∈ support := goodMembers good (by simp)
      have lessUses : circuitUsesOnly support
          (xorLessThanIntoTargetCircuit left right compareWork andScratch less) :=
        circuitUsesOnly_lessThan support left right compareWork andScratch less
          leftMembers rightMembers compareMembers scratchMembers lessMember
      have needUses : circuitUsesOnly support
          (Circuit.sequence <| (degreeFlags.drop (slot + 1)).map fun degreeFlag =>
            safeCnot degreeFlag need) := by
        apply circuitUsesOnly_sequence support
        intro gate gateMember
        rcases List.mem_map.mp gateMember with ⟨degreeFlag, flagMember, rfl⟩
        exact circuitUsesOnly_safeCnot support degreeFlag need
          (degreeMembers degreeFlag (List.mem_of_mem_drop flagMember)) needMember
      have tailWords : ∀ word ∈ right :: words,
          ∀ wire ∈ word, wire ∈ support := by
        intro word wordMember wire wireMember
        exact wordMembers word (by simp [wordMember]) wire wireMember
      have tailUses := circuitUsesOnly_decoderComparisonSequence support
        degreeFlags compareWork andScratch degreeMembers compareMembers scratchMembers
        (slot + 1) (right :: words) lessFlags needFlags goodFlags tailWords
        (by
          intro wire member
          exact lessMembers wire (by simp [member]))
        (by
          intro wire member
          exact needMembers wire (by simp [member]))
        (by
          intro wire member
          exact goodMembers wire (by simp [member]))
      have xGood := circuitUsesOnly_x support good goodMember
      have xLess := circuitUsesOnly_x support less lessMember
      have combine := circuitUsesOnly_safeToffoli support need less good
        needMember lessMember goodMember
      have stepUses : circuitUsesOnly support
          (decoderComparisonStep degreeFlags compareWork andScratch slot
            left right less need good) :=
        ⟨lessUses, ⟨needUses, ⟨xGood, ⟨xLess, ⟨combine, xLess⟩⟩⟩⟩⟩
      exact ⟨stepUses, tailUses⟩

/-- delimiter隣接比較列は明示support外の任意wireを保存する。 -/
theorem runBasis_decoderComparisonSequence_outside
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (words : List (List (Wire ancillaQubits systemQubits)))
    (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits)
    (degreeMembers : ∀ item ∈ degreeFlags, item ∈ support)
    (compareMembers : ∀ item ∈ compareWork, item ∈ support)
    (scratchMembers : ∀ item ∈ andScratch, item ∈ support)
    (wordMembers : ∀ word ∈ words, ∀ item ∈ word, item ∈ support)
    (lessMembers : ∀ item ∈ lessFlags, item ∈ support)
    (needMembers : ∀ item ∈ needFlags, item ∈ support)
    (goodMembers : ∀ item ∈ goodFlags, item ∈ support)
    (outside : wire ∉ support) :
    (decoderComparisonSequence degreeFlags compareWork andScratch slot
        words lessFlags needFlags goodFlags).runBasis
        reversibleGatePermutation input wire = input wire := by
  apply Circuit.runBasis_outside_of_usesOnly support
    (decoderComparisonSequence degreeFlags compareWork andScratch slot
      words lessFlags needFlags goodFlags)
  · exact circuitUsesOnly_decoderComparisonSequence support degreeFlags compareWork
      andScratch degreeMembers compareMembers scratchMembers slot words
      lessFlags needFlags goodFlags wordMembers lessMembers needMembers goodMembers
  · exact outside

/-- 隣接比較証明で参照する全wireを、再帰順序を保って一列にまとめる。 -/
def decoderComparisonSupport
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (words : List (List (Wire ancillaQubits systemQubits)))
    (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits)) :
    List (Wire ancillaQubits systemQubits) :=
  words.flatten ++ compareWork ++ andScratch ++ degreeFlags ++
    lessFlags ++ needFlags ++ goodFlags

/--
比較再帰の先頭で使う二word・比較work・less target列は、全比較supportの部分列である。
したがって全体の`Nodup`から一比較器のlayoutを抽出できる。
-/
theorem decoderComparison_headLayout_sublist
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (left right : List (Wire ancillaQubits systemQubits))
    (words : List (List (Wire ancillaQubits systemQubits)))
    (less : Wire ancillaQubits systemQubits)
    (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits)) :
    (left ++ right ++ compareWork ++ andScratch ++ [less]).Sublist
      (decoderComparisonSupport degreeFlags compareWork andScratch
        (left :: right :: words) (less :: lessFlags) needFlags goodFlags) := by
  simp [decoderComparisonSupport, List.append_assoc]

/-- 比較再帰で先頭pairを処理した後のtail supportは元supportの部分列である。 -/
theorem decoderComparison_tailSupport_sublist
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (left right : List (Wire ancillaQubits systemQubits))
    (words : List (List (Wire ancillaQubits systemQubits)))
    (less need good : Wire ancillaQubits systemQubits)
    (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits)) :
    (decoderComparisonSupport degreeFlags compareWork andScratch
        (right :: words) lessFlags needFlags goodFlags).Sublist
      (decoderComparisonSupport degreeFlags compareWork andScratch
        (left :: right :: words) (less :: lessFlags)
        (need :: needFlags) (good :: goodFlags)) := by
  have wordsSub : (right ++ words.flatten).Sublist
      (left ++ right ++ words.flatten) := by
    simp [List.append_assoc]
  have lessSub : lessFlags.Sublist (less :: lessFlags) :=
    List.Sublist.cons less (List.Sublist.refl lessFlags)
  have needSub : needFlags.Sublist (need :: needFlags) :=
    List.Sublist.cons need (List.Sublist.refl needFlags)
  have goodSub : goodFlags.Sublist (good :: goodFlags) :=
    List.Sublist.cons good (List.Sublist.refl goodFlags)
  let fixed := compareWork ++ andScratch ++ degreeFlags
  have fixedSub : fixed.Sublist fixed := List.Sublist.refl fixed
  have combined := (((wordsSub.append fixedSub).append lessSub).append needSub).append goodSub
  simpa [decoderComparisonSupport, fixed, List.append_assoc] using combined

/-- degree one-hotとword列から、各隣接位置が満たすべき純粋な合法性bit列を作る。 -/
def decoderExpectedGoodBits (degreeBits : List Bool) :
    Nat → List (List Bool) → List Bool
  | _, [] => []
  | _, [_] => []
  | slot, left :: right :: words =>
      (decide (littleEndianNat left < littleEndianNat right) ||
        !boolParity (degreeBits.drop (slot + 1))) ::
      decoderExpectedGoodBits degreeBits (slot + 1) (right :: words)

/-- 粒子が両方存在する隣接wordだけに狭義昇順を要求する再帰的な純粋仕様。 -/
def wordsStrictWhenRequired (particleCount : Nat) :
    Nat → List (List Bool) → Prop
  | _, [] => True
  | _, [_] => True
  | slot, left :: right :: words =>
      (slot + 1 < particleCount →
        littleEndianNat left < littleEndianNat right) ∧
      wordsStrictWhenRequired particleCount (slot + 1) (right :: words)

/--
degree one-hotが粒子数を表し、active隣接wordが昇順なら、比較器の全good bitは1になる。
inactive wordの値は仮定せず、delimiterを含む未使用wordにも適用できる。
-/
theorem decoderExpectedGoodBits_eq_replicate_true
    (degreeCount particleCount slot : Nat) (words : List (List Bool))
    (particleBound : particleCount ≤ degreeCount)
    (wordsFit : slot + words.length ≤ degreeCount)
    (strictRequired : wordsStrictWhenRequired particleCount slot words) :
    decoderExpectedGoodBits
        (degreeOneHotFrom degreeCount particleCount 0) slot words =
      List.replicate (words.length - 1) true := by
  induction words generalizing slot with
  | nil => rfl
  | cons left tail inductionHypothesis =>
      cases tail with
      | nil => rfl
      | cons right words =>
          have strictHead : slot + 1 < particleCount →
              littleEndianNat left < littleEndianNat right :=
            strictRequired.1
          have strictTail :
              wordsStrictWhenRequired particleCount (slot + 1)
                (right :: words) := strictRequired.2
          have tailFit : slot + 1 + (right :: words).length ≤ degreeCount := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using wordsFit
          have tailResult := inductionHypothesis (slot + 1) tailFit strictTail
          rw [decoderExpectedGoodBits]
          rw [boolParity_degreeOneHotFrom_drop degreeCount particleCount 0
            (slot + 1) (by omega)]
          have parityCondition :
              decide (0 + (slot + 1) < particleCount ∧
                particleCount ≤ 0 + degreeCount) =
              decide (slot + 1 < particleCount) := by
            simp [particleBound]
          rw [parityCondition]
          by_cases required : slot + 1 < particleCount
          · have ordered := strictHead required
            simp [required, ordered, tailResult, List.replicate_succ]
          · simp [required, tailResult, List.replicate_succ]

/-- word列のactive部分が配置の昇順site列と一致するという参照述語。 -/
def wordsMatchConfigurationFrom {p : QParameters}
    (configuration : QConfiguration p) (start : Nat)
    (words : List (List Bool)) : Prop :=
  ∀ offset (active : start + offset < configuration.1.card),
    words[offset]? = some (List.ofFn fun bit =>
      siteBit p (configuration.siteAt ⟨start + offset, active⟩) bit)

/-- 配置のsite列と一致するactive word列は、必要な全隣接位置で狭義昇順である。 -/
theorem wordsStrictWhenRequired_of_matches
    {p : QParameters} (configuration : QConfiguration p)
    (start : Nat) (words : List (List Bool))
    (wordValues : wordsMatchConfigurationFrom configuration start words) :
    wordsStrictWhenRequired configuration.1.card start words := by
  induction words generalizing start with
  | nil => trivial
  | cons left tail inductionHypothesis =>
      cases tail with
      | nil => trivial
      | cons right words =>
          constructor
          · intro required
            have leftValue := wordValues 0 (by omega)
            have rightValue := wordValues 1 (by omega)
            simp only [List.getElem?_cons_zero, Option.some.injEq] at leftValue
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] at rightValue
            rw [leftValue, rightValue, littleEndianNat_siteBits,
              littleEndianNat_siteBits]
            apply configuration_siteAt_val_lt configuration
            simp
          · apply inductionHypothesis (start + 1)
            intro offset active
            have oldValue := wordValues (offset + 1) (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using oldValue

/-- 合法delimiterを`K` wordへ分割した列は、全active slotで元配置のsite列に一致する。 -/
theorem splitBitWords_delimiter_matches
    {p : QParameters} (configuration : QConfiguration p) :
    wordsMatchConfigurationFrom configuration 0
      (splitBitWords p.wordWidth p.K
        (registerBitList (delimiterEncoding configuration))) := by
  intro offset active
  have active' : offset < configuration.1.card := by simpa using active
  simpa using splitBitWords_delimiter_active_get configuration offset active'

/-- 合法delimiterをword分割した列は、必要な全隣接位置で狭義昇順である。 -/
theorem splitBitWords_delimiter_strict
    {p : QParameters} (configuration : QConfiguration p) :
    wordsStrictWhenRequired configuration.1.card 0
      (splitBitWords p.wordWidth p.K
        (registerBitList (delimiterEncoding configuration))) := by
  apply wordsStrictWhenRequired_of_matches configuration 0
  exact splitBitWords_delimiter_matches configuration

/--
合法delimiterとそのdegree one-hotから得る静的good列は、一般`q,K`で全要素が1である。
-/
theorem decoderExpectedGoodBits_delimiterEncoding
    {p : QParameters} (configuration : QConfiguration p) :
    decoderExpectedGoodBits
        (degreeOneHotFrom p.K configuration.1.card 0) 0
        (splitBitWords p.wordWidth p.K
          (registerBitList (delimiterEncoding configuration))) =
      List.replicate (p.K - 1) true := by
  have result := decoderExpectedGoodBits_eq_replicate_true
    p.K configuration.1.card 0
    (splitBitWords p.wordWidth p.K
      (registerBitList (delimiterEncoding configuration)))
    configuration.2.2 (by simp [splitBitWords])
    (splitBitWords_delimiter_strict configuration)
  simpa [splitBitWords] using result

/-- Bool条件が真のときだけ指定wireを反転する純粋な基底作用。 -/
def conditionalX
    {ancillaQubits systemQubits : Nat}
    (enabled : Bool) (target : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  if enabled then xBasisAction target input else input

/-- 条件付きXはtarget以外のwire値を保存する。 -/
theorem conditionalX_other
    {ancillaQubits systemQubits : Nat}
    (enabled : Bool) (target wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (different : wire ≠ target) :
    conditionalX enabled target input wire = input wire := by
  unfold conditionalX
  split
  · exact xBasisAction_other target wire different input
  · rfl

/--
一個のdelimiter隣接比較stepは、less・need・goodの三flagだけを純粋仕様どおり反転する。
比較器内部のequal flagとAND scratchは一般比較器定理により入力値0へ戻る。
-/
theorem runBasis_decoderComparisonStep
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (left right : List (Wire ancillaQubits systemQubits))
    (less need good : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = compareWork.length)
    (rightLength : right.length = compareWork.length)
    (fullLayout :
      (left ++ right ++ compareWork ++ andScratch ++ degreeFlags ++
        [less, need, good]).Nodup)
    (compareZero : readWires compareWork input =
      List.replicate compareWork.length false)
    (scratchZero : ∀ wire ∈ andScratch, input wire = false)
    (scratchEnough : compareWork.length ≤ andScratch.length)
    (lessZero : input less = false) (needZero : input need = false)
    (goodZero : input good = false) :
    (decoderComparisonStep degreeFlags compareWork andScratch slot
        left right less need good).runBasis reversibleGatePermutation input =
      let lessBit := decide
        (littleEndianNat (readWires left input) < littleEndianNat (readWires right input))
      let needBit := boolParity (readWires (degreeFlags.drop (slot + 1)) input)
      conditionalX (lessBit || !needBit) good
        (conditionalX needBit need (conditionalX lessBit less input)) := by
  have comparatorLayout :
      (left ++ right ++ compareWork ++ andScratch ++ [less]).Nodup := by
    exact List.Nodup.sublist (by simp [List.append_assoc]) fullLayout
  have degreeNeedLayout : (degreeFlags ++ [need]).Nodup := by
    let wirePrefix := left ++ right ++ compareWork ++ andScratch
    have inside : (degreeFlags ++ [need]).Sublist
        (degreeFlags ++ [less, need, good]) := by
      exact (List.Sublist.refl degreeFlags).append (by simp)
    have embedded := inside.trans <|
      List.sublist_append_right wirePrefix (degreeFlags ++ [less, need, good])
    have selected : (degreeFlags ++ [need]).Sublist
        (left ++ right ++ compareWork ++ andScratch ++ degreeFlags ++
          [less, need, good]) := by
      simpa [wirePrefix, List.append_assoc] using embedded
    exact List.Nodup.sublist selected fullLayout
  have degreeLessLayout : (degreeFlags ++ [less]).Nodup := by
    let wirePrefix := left ++ right ++ compareWork ++ andScratch
    have inside : (degreeFlags ++ [less]).Sublist
        (degreeFlags ++ [less, need, good]) := by
      exact (List.Sublist.refl degreeFlags).append (by simp)
    have embedded := inside.trans <|
      List.sublist_append_right wirePrefix (degreeFlags ++ [less, need, good])
    have selected : (degreeFlags ++ [less]).Sublist
        (left ++ right ++ compareWork ++ andScratch ++ degreeFlags ++
          [less, need, good]) := by
      simpa [wirePrefix, List.append_assoc] using embedded
    exact List.Nodup.sublist selected fullLayout
  have flagLayout : [less, need, good].Nodup := by
    let wirePrefix := left ++ right ++ compareWork ++ andScratch ++ degreeFlags
    have selected : [less, need, good].Sublist
        (left ++ right ++ compareWork ++ andScratch ++ degreeFlags ++
          [less, need, good]) := by
      simpa [wirePrefix, List.append_assoc] using
        (List.sublist_append_right wirePrefix [less, need, good])
    exact List.Nodup.sublist selected fullLayout
  have needAbsentDegree : need ∉ degreeFlags := by
    intro member
    exact (List.nodup_append.mp degreeNeedLayout).2.2 need member need (by simp) rfl
  have lessAbsentDegree : less ∉ degreeFlags := by
    intro member
    exact (List.nodup_append.mp degreeLessLayout).2.2 less member less (by simp) rfl
  have lessSplit := List.nodup_cons.mp flagLayout
  have needSplit := List.nodup_cons.mp lessSplit.2
  have lessNeNeed : less ≠ need := by
    intro equal
    exact lessSplit.1 (by simp [equal])
  have lessNeGood : less ≠ good := by
    intro equal
    exact lessSplit.1 (by simp [equal])
  have needNeGood : need ≠ good := by
    intro equal
    exact needSplit.1 (by simp [equal])
  let lessBit := decide
    (littleEndianNat (readWires left input) < littleEndianNat (readWires right input))
  let needBit := boolParity (readWires (degreeFlags.drop (slot + 1)) input)
  let afterLess := conditionalX lessBit less input
  have lessResult :
      (xorLessThanIntoTargetCircuit left right compareWork andScratch less).runBasis
          reversibleGatePermutation input = afterLess := by
    exact runBasis_xorLessThanIntoTargetCircuit_nat_of_layout left right compareWork andScratch less input
      leftLength rightLength comparatorLayout compareZero scratchZero scratchEnough
  have degreeAfterLess :
      readWires (degreeFlags.drop (slot + 1)) afterLess =
        readWires (degreeFlags.drop (slot + 1)) input := by
    apply List.map_congr_left
    intro wire member
    unfold afterLess conditionalX
    split
    · exact xBasisAction_other less wire (by
        intro equal
        subst wire
        exact lessAbsentDegree (List.mem_of_mem_drop member)) input
    · rfl
  have needResult :
      (xorSourceParityIntoTargetCircuit (degreeFlags.drop (slot + 1)) need).runBasis
          reversibleGatePermutation afterLess =
        conditionalX needBit need afterLess := by
    rw [runBasis_xorSourceParityIntoTargetCircuit (degreeFlags.drop (slot + 1)) need afterLess]
    · rw [degreeAfterLess]
      rfl
    · intro member
      exact needAbsentDegree (List.mem_of_mem_drop member)
  simp only [decoderComparisonStep, runBasis_seq, lessResult]
  change
    ((.seq (.gate (.x good)) <| .seq (.gate (.x less)) <|
      .seq (safeToffoli need less good) (.gate (.x less))) :
        Circuit (ReversibleGate ancillaQubits systemQubits)).runBasis
        reversibleGatePermutation
        ((xorSourceParityIntoTargetCircuit (degreeFlags.drop (slot + 1)) need).runBasis
          reversibleGatePermutation afterLess) = _
  rw [needResult]
  rw [runBasis_core_seq, runBasis_core_seq, runBasis_core_seq]
  rw [runBasis_core_safeToffoli need less good lessNeNeed.symm needNeGood lessNeGood]
  change
    xBasisAction less
      (toffoliBasisAction need less good
        (xBasisAction less
          (xBasisAction good (conditionalX needBit need afterLess)))) = _
  by_cases lessEnabled : lessBit = true <;>
    by_cases needEnabled : needBit = true
  all_goals
    funext wire
    by_cases wireLess : wire = less
    · subst wire
      simp [xBasisAction, toffoliBasisAction, lessBit, needBit, afterLess,
        conditionalX, lessEnabled, needEnabled, lessZero, needZero,
        lessNeNeed, lessNeNeed.symm, lessNeGood]
    · by_cases wireNeed : wire = need
      · subst wire
        simp [xBasisAction, toffoliBasisAction, lessBit, needBit, afterLess,
          conditionalX, lessEnabled, needEnabled, lessZero, needZero,
          lessNeNeed, lessNeNeed.symm, needNeGood]
      · by_cases wireGood : wire = good
        · subst wire
          simp [xBasisAction, toffoliBasisAction, lessBit, needBit, afterLess,
            conditionalX, lessEnabled, needEnabled, lessZero, needZero, goodZero,
            lessNeNeed, lessNeNeed.symm, lessNeGood, lessNeGood.symm,
            needNeGood, needNeGood.symm]
        · simp [xBasisAction, toffoliBasisAction, lessBit, needBit, afterLess,
            conditionalX, lessEnabled, needEnabled, wireLess, wireNeed, wireGood]

/-- 一個の比較stepは三出力flag以外の任意wireを保存する。 -/
theorem runBasis_decoderComparisonStep_other
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (left right : List (Wire ancillaQubits systemQubits))
    (less need good wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (leftLength : left.length = compareWork.length)
    (rightLength : right.length = compareWork.length)
    (fullLayout :
      (left ++ right ++ compareWork ++ andScratch ++ degreeFlags ++
        [less, need, good]).Nodup)
    (compareZero : readWires compareWork input =
      List.replicate compareWork.length false)
    (scratchZero : ∀ item ∈ andScratch, input item = false)
    (scratchEnough : compareWork.length ≤ andScratch.length)
    (lessZero : input less = false) (needZero : input need = false)
    (goodZero : input good = false)
    (wireNeLess : wire ≠ less) (wireNeNeed : wire ≠ need)
    (wireNeGood : wire ≠ good) :
    (decoderComparisonStep degreeFlags compareWork andScratch slot
        left right less need good).runBasis reversibleGatePermutation input wire =
      input wire := by
  rw [runBasis_decoderComparisonStep degreeFlags compareWork andScratch slot
    left right less need good input leftLength rightLength fullLayout compareZero
    scratchZero scratchEnough lessZero needZero goodZero]
  rw [conditionalX_other _ good wire _ wireNeGood]
  rw [conditionalX_other _ need wire _ wireNeNeed]
  exact conditionalX_other _ less wire input wireNeLess

/-- 隣接比較列の回路非依存な基底作用仕様。 -/
def decoderComparisonReferenceAction
    {ancillaQubits systemQubits : Nat}
    (degreeFlags : List (Wire ancillaQubits systemQubits)) :
    Nat → List (List (Wire ancillaQubits systemQubits)) →
      List (Wire ancillaQubits systemQubits) →
      List (Wire ancillaQubits systemQubits) →
      List (Wire ancillaQubits systemQubits) →
      JointBasis ancillaQubits systemQubits →
      JointBasis ancillaQubits systemQubits
  | slot, left :: right :: words, less :: lessFlags,
      need :: needFlags, good :: goodFlags, input =>
      let lessBit := decide
        (littleEndianNat (readWires left input) < littleEndianNat (readWires right input))
      let needBit := boolParity (readWires (degreeFlags.drop (slot + 1)) input)
      let next := conditionalX (lessBit || !needBit) good
        (conditionalX needBit need (conditionalX lessBit less input))
      decoderComparisonReferenceAction degreeFlags (slot + 1) (right :: words)
        lessFlags needFlags goodFlags next
  | _, _, _, _, _, input => input

/-- 純粋比較参照関数もless・need・good出力列外のwireを変更しない。 -/
theorem decoderComparisonReferenceAction_outside
    {ancillaQubits systemQubits : Nat}
    (degreeFlags : List (Wire ancillaQubits systemQubits)) :
    ∀ (slot : Nat) (words : List (List (Wire ancillaQubits systemQubits)))
      (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits))
      (input : JointBasis ancillaQubits systemQubits)
      (wire : Wire ancillaQubits systemQubits),
      wire ∉ lessFlags → wire ∉ needFlags → wire ∉ goodFlags →
      decoderComparisonReferenceAction degreeFlags slot words lessFlags
        needFlags goodFlags input wire = input wire := by
  intro slot words lessFlags needFlags goodFlags input wire
    outsideLess outsideNeed outsideGood
  induction goodFlags generalizing slot words lessFlags needFlags input with
  | nil =>
      cases words <;> cases lessFlags <;> cases needFlags <;>
        simp [decoderComparisonReferenceAction]
  | cons good goodFlags inductionHypothesis =>
      cases words with
      | nil => rfl
      | cons left words =>
        cases words with
        | nil => rfl
        | cons right words =>
          cases lessFlags with
          | nil => rfl
          | cons less lessFlags =>
            cases needFlags with
            | nil => rfl
            | cons need needFlags =>
              have wireNeLess : wire ≠ less := by
                intro equal
                exact outsideLess (by simp [equal])
              have wireNeNeed : wire ≠ need := by
                intro equal
                exact outsideNeed (by simp [equal])
              have wireNeGood : wire ≠ good := by
                intro equal
                exact outsideGood (by simp [equal])
              let lessBit := decide
                (littleEndianNat (readWires left input) <
                  littleEndianNat (readWires right input))
              let needBit := boolParity
                (readWires (degreeFlags.drop (slot + 1)) input)
              let next := conditionalX (lessBit || !needBit) good
                (conditionalX needBit need (conditionalX lessBit less input))
              change decoderComparisonReferenceAction degreeFlags (slot + 1)
                  (right :: words) lessFlags needFlags goodFlags next wire = input wire
              rw [inductionHypothesis (slot + 1) (right :: words) lessFlags
                needFlags next (by
                  intro member
                  exact outsideLess (by simp [member])) (by
                  intro member
                  exact outsideNeed (by simp [member])) (by
                  intro member
                  exact outsideGood (by simp [member]))]
              unfold next
              rw [conditionalX_other _ good wire _ wireNeGood,
                conditionalX_other _ need wire _ wireNeNeed]
              exact conditionalX_other _ less wire input wireNeLess

/--
任意本数の隣接wordについて、比較列の基底作用は純粋参照関数と一致する。
全状態列挙は行わず、word本数について帰納し、一step定理とsupport部分列だけを合成する。
-/
theorem runBasis_decoderComparisonSequence_reference
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits)) :
    ∀ (slot : Nat) (words : List (List (Wire ancillaQubits systemQubits)))
      (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits))
      (input : JointBasis ancillaQubits systemQubits),
      words.length = goodFlags.length + 1 →
      lessFlags.length = goodFlags.length →
      needFlags.length = goodFlags.length →
      (∀ word ∈ words, word.length = compareWork.length) →
      (decoderComparisonSupport degreeFlags compareWork andScratch
        words lessFlags needFlags goodFlags).Nodup →
      readWires compareWork input = List.replicate compareWork.length false →
      (∀ wire ∈ andScratch, input wire = false) →
      readWires lessFlags input = List.replicate lessFlags.length false →
      readWires needFlags input = List.replicate needFlags.length false →
      readWires goodFlags input = List.replicate goodFlags.length false →
      compareWork.length ≤ andScratch.length →
      (decoderComparisonSequence degreeFlags compareWork andScratch slot
          words lessFlags needFlags goodFlags).runBasis
          reversibleGatePermutation input =
        decoderComparisonReferenceAction degreeFlags slot words
          lessFlags needFlags goodFlags input := by
  intro slot words lessFlags needFlags goodFlags input wordCount lessCount needCount
    wordLengths supportNodup compareZero scratchZero lessZero needZero goodZero
    scratchEnough
  induction goodFlags generalizing slot words lessFlags needFlags input with
  | nil =>
      cases lessFlags with
      | cons less lessFlags => simp at lessCount
      | nil =>
        cases needFlags with
        | cons need needFlags => simp at needCount
        | nil =>
          cases words with
          | nil => simp at wordCount
          | cons word words =>
              cases words with
              | nil => rfl
              | cons next words => simp at wordCount
  | cons good goodFlags inductionHypothesis =>
      cases lessFlags with
      | nil => simp at lessCount
      | cons less lessFlags =>
        cases needFlags with
        | nil => simp at needCount
        | cons need needFlags =>
          cases words with
          | nil => simp at wordCount
          | cons left words =>
            cases words with
            | nil => simp at wordCount
            | cons right words =>
              have tailWordCount : (right :: words).length = goodFlags.length + 1 := by
                simpa using wordCount
              have tailLessCount : lessFlags.length = goodFlags.length := by
                simpa using lessCount
              have tailNeedCount : needFlags.length = goodFlags.length := by
                simpa using needCount
              have leftLength : left.length = compareWork.length :=
                wordLengths left (by simp)
              have rightLength : right.length = compareWork.length :=
                wordLengths right (by simp)
              have tailWordLengths : ∀ word ∈ right :: words,
                  word.length = compareWork.length := by
                intro word member
                exact wordLengths word (by simp [member])
              have stepLayout :
                  (left ++ right ++ compareWork ++ andScratch ++ degreeFlags ++
                    [less, need, good]).Nodup := by
                apply List.Nodup.sublist _ supportNodup
                simp [decoderComparisonSupport, List.append_assoc]
              have tailSupportNodup :
                  (decoderComparisonSupport degreeFlags compareWork andScratch
                    (right :: words) lessFlags needFlags goodFlags).Nodup :=
                List.Nodup.sublist
                  (decoderComparison_tailSupport_sublist degreeFlags compareWork
                    andScratch left right words less need good lessFlags needFlags
                    goodFlags) supportNodup
              have lessValues : input less = false ∧
                  readWires lessFlags input = List.replicate lessFlags.length false := by
                change input less :: readWires lessFlags input =
                  List.replicate (lessFlags.length + 1) false at lessZero
                rw [show lessFlags.length + 1 = Nat.succ lessFlags.length by omega,
                  List.replicate_succ] at lessZero
                exact List.cons.inj lessZero
              have needValues : input need = false ∧
                  readWires needFlags input = List.replicate needFlags.length false := by
                change input need :: readWires needFlags input =
                  List.replicate (needFlags.length + 1) false at needZero
                rw [show needFlags.length + 1 = Nat.succ needFlags.length by omega,
                  List.replicate_succ] at needZero
                exact List.cons.inj needZero
              have goodValues : input good = false ∧
                  readWires goodFlags input = List.replicate goodFlags.length false := by
                change input good :: readWires goodFlags input =
                  List.replicate (goodFlags.length + 1) false at goodZero
                rw [show goodFlags.length + 1 = Nat.succ goodFlags.length by omega,
                  List.replicate_succ] at goodZero
                exact List.cons.inj goodZero
              let stepCircuit := decoderComparisonStep degreeFlags compareWork andScratch
                slot left right less need good
              let stepState := stepCircuit.runBasis reversibleGatePermutation input
              have stepResult : stepState =
                  let lessBit := decide
                    (littleEndianNat (readWires left input) <
                      littleEndianNat (readWires right input))
                  let needBit := boolParity
                    (readWires (degreeFlags.drop (slot + 1)) input)
                  conditionalX (lessBit || !needBit) good
                    (conditionalX needBit need (conditionalX lessBit less input)) := by
                exact runBasis_decoderComparisonStep degreeFlags compareWork andScratch
                  slot left right less need good input leftLength rightLength stepLayout
                  compareZero scratchZero scratchEnough lessValues.1 needValues.1
                  goodValues.1
              let common := (left :: right :: words).flatten ++ compareWork ++
                andScratch ++ degreeFlags
              have supportShape :
                  (common ++ (less :: lessFlags) ++ (need :: needFlags) ++
                    (good :: goodFlags)).Nodup := by
                simpa [common, decoderComparisonSupport, List.append_assoc] using supportNodup
              have commonSplit : common.Nodup ∧
                  ((less :: lessFlags) ++ (need :: needFlags) ++
                    (good :: goodFlags)).Nodup ∧
                  ∀ a ∈ common,
                    ∀ b ∈ (less :: lessFlags) ++ (need :: needFlags) ++
                      (good :: goodFlags), a ≠ b := by
                rw [← List.nodup_append]
                simpa [List.append_assoc] using supportShape
              have lessSplit : (less :: lessFlags).Nodup ∧
                  ((need :: needFlags) ++ (good :: goodFlags)).Nodup ∧
                  ∀ a ∈ less :: lessFlags,
                    ∀ b ∈ (need :: needFlags) ++ (good :: goodFlags), a ≠ b := by
                rw [← List.nodup_append]
                simpa [List.append_assoc] using commonSplit.2.1
              have needSplit : (need :: needFlags).Nodup ∧
                  (good :: goodFlags).Nodup ∧
                  ∀ a ∈ need :: needFlags, ∀ b ∈ good :: goodFlags, a ≠ b := by
                rw [← List.nodup_append]
                simpa [List.append_assoc] using lessSplit.2.1
              have preserveCommon (wire : Wire ancillaQubits systemQubits)
                  (member : wire ∈ common) : stepState wire = input wire := by
                rw [stepResult]
                rw [conditionalX_other _ good wire _
                  (commonSplit.2.2 wire member good (by simp))]
                rw [conditionalX_other _ need wire _
                  (commonSplit.2.2 wire member need (by simp))]
                exact conditionalX_other _ less wire input
                  (commonSplit.2.2 wire member less (by simp))
              have preserveLessTail (wire : Wire ancillaQubits systemQubits)
                  (member : wire ∈ lessFlags) : stepState wire = input wire := by
                have wireNeLess : wire ≠ less := by
                  exact fun equal => (List.nodup_cons.mp lessSplit.1).1 (by simp [← equal, member])
                have wireNeNeed : wire ≠ need :=
                  lessSplit.2.2 wire (by simp [member]) need (by simp)
                have wireNeGood : wire ≠ good :=
                  lessSplit.2.2 wire (by simp [member]) good (by simp)
                rw [stepResult, conditionalX_other _ good wire _ wireNeGood,
                  conditionalX_other _ need wire _ wireNeNeed]
                exact conditionalX_other _ less wire input wireNeLess
              have preserveNeedTail (wire : Wire ancillaQubits systemQubits)
                  (member : wire ∈ needFlags) : stepState wire = input wire := by
                have wireNeLess : wire ≠ less := by
                  exact (lessSplit.2.2 less (by simp) wire
                    (List.mem_append_left _ (by simp [member]))).symm
                have wireNeNeed : wire ≠ need := by
                  exact fun equal => (List.nodup_cons.mp needSplit.1).1
                    (by simp [← equal, member])
                have wireNeGood : wire ≠ good :=
                  needSplit.2.2 wire (by simp [member]) good (by simp)
                rw [stepResult, conditionalX_other _ good wire _ wireNeGood,
                  conditionalX_other _ need wire _ wireNeNeed]
                exact conditionalX_other _ less wire input wireNeLess
              have preserveGoodTail (wire : Wire ancillaQubits systemQubits)
                  (member : wire ∈ goodFlags) : stepState wire = input wire := by
                have wireNeLess : wire ≠ less := by
                  exact (lessSplit.2.2 less (by simp) wire
                    (List.mem_append_right _ (by simp [member]))).symm
                have wireNeNeed : wire ≠ need := by
                  exact (needSplit.2.2 need (by simp) wire (by simp [member])).symm
                have wireNeGood : wire ≠ good := by
                  exact fun equal => (List.nodup_cons.mp needSplit.2.1).1
                    (by simp [← equal, member])
                rw [stepResult, conditionalX_other _ good wire _ wireNeGood,
                  conditionalX_other _ need wire _ wireNeNeed]
                exact conditionalX_other _ less wire input wireNeLess
              have nextCompareZero : readWires compareWork stepState =
                  List.replicate compareWork.length false := by
                calc
                  readWires compareWork stepState = readWires compareWork input := by
                    apply List.map_congr_left
                    intro wire member
                    exact preserveCommon wire (by simp [common, member])
                  _ = _ := compareZero
              have nextScratchZero : ∀ wire ∈ andScratch,
                  stepState wire = false := by
                intro wire member
                rw [preserveCommon wire (by simp [common, member])]
                exact scratchZero wire member
              have nextLessZero : readWires lessFlags stepState =
                  List.replicate lessFlags.length false := by
                calc
                  readWires lessFlags stepState = readWires lessFlags input := by
                    apply List.map_congr_left
                    exact preserveLessTail
                  _ = _ := lessValues.2
              have nextNeedZero : readWires needFlags stepState =
                  List.replicate needFlags.length false := by
                calc
                  readWires needFlags stepState = readWires needFlags input := by
                    apply List.map_congr_left
                    exact preserveNeedTail
                  _ = _ := needValues.2
              have nextGoodZero : readWires goodFlags stepState =
                  List.replicate goodFlags.length false := by
                calc
                  readWires goodFlags stepState = readWires goodFlags input := by
                    apply List.map_congr_left
                    exact preserveGoodTail
                  _ = _ := goodValues.2
              have tailResult := inductionHypothesis (slot + 1) (right :: words)
                lessFlags needFlags stepState tailWordCount tailLessCount tailNeedCount
                tailWordLengths tailSupportNodup nextCompareZero nextScratchZero
                nextLessZero nextNeedZero nextGoodZero
              simp only [decoderComparisonSequence, runBasis_seq,
                decoderComparisonReferenceAction]
              rw [show
                (decoderComparisonStep degreeFlags compareWork andScratch slot left
                  right less need good).runBasis reversibleGatePermutation input =
                    stepState by rfl]
              rw [← stepResult]
              exact tailResult

/-- 純粋比較参照関数が各good wireへ最終的に書くBool列。 -/
def decoderComparisonReferenceGoodBits
    {ancillaQubits systemQubits : Nat}
    (degreeFlags : List (Wire ancillaQubits systemQubits)) :
    Nat → List (List (Wire ancillaQubits systemQubits)) →
      List (Wire ancillaQubits systemQubits) →
      List (Wire ancillaQubits systemQubits) →
      List (Wire ancillaQubits systemQubits) →
      JointBasis ancillaQubits systemQubits → List Bool
  | slot, left :: right :: words, less :: lessFlags,
      need :: needFlags, good :: goodFlags, input =>
      let lessBit := decide
        (littleEndianNat (readWires left input) < littleEndianNat (readWires right input))
      let needBit := boolParity (readWires (degreeFlags.drop (slot + 1)) input)
      let goodBit := lessBit || !needBit
      let next := conditionalX goodBit good
        (conditionalX needBit need (conditionalX lessBit less input))
      goodBit :: decoderComparisonReferenceGoodBits degreeFlags (slot + 1)
        (right :: words) lessFlags needFlags goodFlags next
  | _, _, _, _, _, _ => []

/-- 純粋比較参照関数を実行後にgood列を読むと、再帰的なgood仕様列に一致する。 -/
theorem readWires_decoderComparisonReferenceAction_good
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits)) :
    ∀ (slot : Nat) (words : List (List (Wire ancillaQubits systemQubits)))
      (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits))
      (input : JointBasis ancillaQubits systemQubits),
      words.length = goodFlags.length + 1 →
      lessFlags.length = goodFlags.length →
      needFlags.length = goodFlags.length →
      (decoderComparisonSupport degreeFlags compareWork andScratch
        words lessFlags needFlags goodFlags).Nodup →
      readWires goodFlags input = List.replicate goodFlags.length false →
      readWires goodFlags
          (decoderComparisonReferenceAction degreeFlags slot words
            lessFlags needFlags goodFlags input) =
        decoderComparisonReferenceGoodBits degreeFlags slot words
          lessFlags needFlags goodFlags input := by
  intro slot words lessFlags needFlags goodFlags input wordCount lessCount needCount
    supportNodup goodZero
  induction goodFlags generalizing slot words lessFlags needFlags input with
  | nil =>
      cases lessFlags with
      | cons less lessFlags => simp at lessCount
      | nil =>
        cases needFlags with
        | cons need needFlags => simp at needCount
        | nil =>
          cases words with
          | nil => simp at wordCount
          | cons word words =>
              cases words with
              | nil => rfl
              | cons next words => simp at wordCount
  | cons good goodFlags inductionHypothesis =>
      cases lessFlags with
      | nil => simp at lessCount
      | cons less lessFlags =>
        cases needFlags with
        | nil => simp at needCount
        | cons need needFlags =>
          cases words with
          | nil => simp at wordCount
          | cons left words =>
            cases words with
            | nil => simp at wordCount
            | cons right words =>
              have tailWordCount : (right :: words).length = goodFlags.length + 1 := by
                simpa using wordCount
              have tailLessCount : lessFlags.length = goodFlags.length := by
                simpa using lessCount
              have tailNeedCount : needFlags.length = goodFlags.length := by
                simpa using needCount
              have tailSupportNodup :
                  (decoderComparisonSupport degreeFlags compareWork andScratch
                    (right :: words) lessFlags needFlags goodFlags).Nodup :=
                List.Nodup.sublist
                  (decoderComparison_tailSupport_sublist degreeFlags compareWork
                    andScratch left right words less need good lessFlags needFlags
                    goodFlags) supportNodup
              have goodValues : input good = false ∧
                  readWires goodFlags input = List.replicate goodFlags.length false := by
                change input good :: readWires goodFlags input =
                  List.replicate (goodFlags.length + 1) false at goodZero
                rw [show goodFlags.length + 1 = Nat.succ goodFlags.length by omega,
                  List.replicate_succ] at goodZero
                exact List.cons.inj goodZero
              let common := (left :: right :: words).flatten ++ compareWork ++
                andScratch ++ degreeFlags
              have supportShape :
                  (common ++ (less :: lessFlags) ++ (need :: needFlags) ++
                    (good :: goodFlags)).Nodup := by
                simpa [common, decoderComparisonSupport, List.append_assoc] using supportNodup
              have commonSplit : common.Nodup ∧
                  ((less :: lessFlags) ++ (need :: needFlags) ++
                    (good :: goodFlags)).Nodup ∧
                  ∀ a ∈ common,
                    ∀ b ∈ (less :: lessFlags) ++ (need :: needFlags) ++
                      (good :: goodFlags), a ≠ b := by
                rw [← List.nodup_append]
                simpa [List.append_assoc] using supportShape
              have lessSplit : (less :: lessFlags).Nodup ∧
                  ((need :: needFlags) ++ (good :: goodFlags)).Nodup ∧
                  ∀ a ∈ less :: lessFlags,
                    ∀ b ∈ (need :: needFlags) ++ (good :: goodFlags), a ≠ b := by
                rw [← List.nodup_append]
                simpa [List.append_assoc] using commonSplit.2.1
              have needSplit : (need :: needFlags).Nodup ∧
                  (good :: goodFlags).Nodup ∧
                  ∀ a ∈ need :: needFlags, ∀ b ∈ good :: goodFlags, a ≠ b := by
                rw [← List.nodup_append]
                simpa [List.append_assoc] using lessSplit.2.1
              have lessNeNeed : less ≠ need :=
                lessSplit.2.2 less (by simp) need (by simp)
              have lessNeGood : less ≠ good :=
                lessSplit.2.2 less (by simp) good (by simp)
              have needNeGood : need ≠ good :=
                needSplit.2.2 need (by simp) good (by simp)
              let lessBit := decide
                (littleEndianNat (readWires left input) <
                  littleEndianNat (readWires right input))
              let needBit := boolParity
                (readWires (degreeFlags.drop (slot + 1)) input)
              let goodBit := lessBit || !needBit
              let next := conditionalX goodBit good
                (conditionalX needBit need (conditionalX lessBit less input))
              have nextGood : next good = goodBit := by
                unfold next conditionalX
                cases lessValue : lessBit <;> cases needValue : needBit <;>
                  simp [goodBit, lessValue, needValue, xBasisAction, goodValues.1,
                    lessNeGood.symm, needNeGood.symm]
              have nextTailZero : readWires goodFlags next =
                  List.replicate goodFlags.length false := by
                calc
                  readWires goodFlags next = readWires goodFlags input := by
                    apply List.map_congr_left
                    intro wire member
                    have wireNeGood : wire ≠ good := by
                      exact fun equal => (List.nodup_cons.mp needSplit.2.1).1
                        (by simp [← equal, member])
                    have wireNeNeed : wire ≠ need := by
                      exact (needSplit.2.2 need (by simp) wire
                        (by simp [member])).symm
                    have wireNeLess : wire ≠ less := by
                      exact (lessSplit.2.2 less (by simp) wire
                        (List.mem_append_right _ (by simp [member]))).symm
                    unfold next
                    rw [conditionalX_other _ good wire _ wireNeGood,
                      conditionalX_other _ need wire _ wireNeNeed]
                    exact conditionalX_other _ less wire input wireNeLess
                  _ = _ := goodValues.2
              have tailResult := inductionHypothesis (slot + 1) (right :: words)
                lessFlags needFlags next tailWordCount tailLessCount tailNeedCount
                tailSupportNodup nextTailZero
              have goodOutsideLess : good ∉ lessFlags := by
                intro member
                exact lessSplit.2.2 good (by simp [member]) good (by simp) rfl
              have goodOutsideNeed : good ∉ needFlags := by
                intro member
                exact needSplit.2.2 good (by simp [member]) good (by simp) rfl
              have goodOutsideGood : good ∉ goodFlags :=
                (List.nodup_cons.mp needSplit.2.1).1
              have finalGood := decoderComparisonReferenceAction_outside degreeFlags
                (slot + 1) (right :: words) lessFlags needFlags goodFlags next good
                goodOutsideLess goodOutsideNeed goodOutsideGood
              change
                decoderComparisonReferenceAction degreeFlags (slot + 1)
                    (right :: words) lessFlags needFlags goodFlags next good ::
                  readWires goodFlags
                    (decoderComparisonReferenceAction degreeFlags (slot + 1)
                      (right :: words) lessFlags needFlags goodFlags next) =
                goodBit :: decoderComparisonReferenceGoodBits degreeFlags (slot + 1)
                  (right :: words) lessFlags needFlags goodFlags next
              rw [finalGood, nextGood, tailResult]

/--
参照関数内で更新されるflagはdegreeとwordを変えないため、動的good列は入力時の
degree suffix parityと隣接word大小だけからなる静的仕様`decoderExpectedGoodBits`に等しい。
-/
theorem decoderComparisonReferenceGoodBits_eq_expected
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits)) :
    ∀ (slot : Nat) (words : List (List (Wire ancillaQubits systemQubits)))
      (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits))
      (input : JointBasis ancillaQubits systemQubits),
      words.length = goodFlags.length + 1 →
      lessFlags.length = goodFlags.length →
      needFlags.length = goodFlags.length →
      (decoderComparisonSupport degreeFlags compareWork andScratch
        words lessFlags needFlags goodFlags).Nodup →
      decoderComparisonReferenceGoodBits degreeFlags slot words
          lessFlags needFlags goodFlags input =
        decoderExpectedGoodBits (readWires degreeFlags input) slot
          (words.map fun word => readWires word input) := by
  intro slot words lessFlags needFlags goodFlags input wordCount lessCount needCount
    supportNodup
  induction goodFlags generalizing slot words lessFlags needFlags input with
  | nil =>
      cases lessFlags with
      | cons less lessFlags => simp at lessCount
      | nil =>
        cases needFlags with
        | cons need needFlags => simp at needCount
        | nil =>
          cases words with
          | nil => simp at wordCount
          | cons word words =>
              cases words with
              | nil => rfl
              | cons next words => simp at wordCount
  | cons good goodFlags inductionHypothesis =>
      cases lessFlags with
      | nil => simp at lessCount
      | cons less lessFlags =>
        cases needFlags with
        | nil => simp at needCount
        | cons need needFlags =>
          cases words with
          | nil => simp at wordCount
          | cons left words =>
            cases words with
            | nil => simp at wordCount
            | cons right words =>
              have tailWordCount : (right :: words).length = goodFlags.length + 1 := by
                simpa using wordCount
              have tailLessCount : lessFlags.length = goodFlags.length := by
                simpa using lessCount
              have tailNeedCount : needFlags.length = goodFlags.length := by
                simpa using needCount
              have tailSupportNodup :
                  (decoderComparisonSupport degreeFlags compareWork andScratch
                    (right :: words) lessFlags needFlags goodFlags).Nodup :=
                List.Nodup.sublist
                  (decoderComparison_tailSupport_sublist degreeFlags compareWork
                    andScratch left right words less need good lessFlags needFlags
                    goodFlags) supportNodup
              let common := (left :: right :: words).flatten ++ compareWork ++
                andScratch ++ degreeFlags
              have supportShape :
                  (common ++ (less :: lessFlags) ++ (need :: needFlags) ++
                    (good :: goodFlags)).Nodup := by
                simpa [common, decoderComparisonSupport, List.append_assoc] using supportNodup
              have commonSplit : common.Nodup ∧
                  ((less :: lessFlags) ++ (need :: needFlags) ++
                    (good :: goodFlags)).Nodup ∧
                  ∀ a ∈ common,
                    ∀ b ∈ (less :: lessFlags) ++ (need :: needFlags) ++
                      (good :: goodFlags), a ≠ b := by
                rw [← List.nodup_append]
                simpa [List.append_assoc] using supportShape
              let lessBit := decide
                (littleEndianNat (readWires left input) <
                  littleEndianNat (readWires right input))
              let needBit := boolParity
                (readWires (degreeFlags.drop (slot + 1)) input)
              let goodBit := lessBit || !needBit
              let next := conditionalX goodBit good
                (conditionalX needBit need (conditionalX lessBit less input))
              have preserveCommon (wire : Wire ancillaQubits systemQubits)
                  (member : wire ∈ common) : next wire = input wire := by
                unfold next
                rw [conditionalX_other _ good wire _
                  (commonSplit.2.2 wire member good (by simp))]
                rw [conditionalX_other _ need wire _
                  (commonSplit.2.2 wire member need (by simp))]
                exact conditionalX_other _ less wire input
                  (commonSplit.2.2 wire member less (by simp))
              have degreeUnchanged : readWires degreeFlags next =
                  readWires degreeFlags input := by
                apply List.map_congr_left
                intro wire member
                exact preserveCommon wire (by simp [common, member])
              have tailWordsUnchanged :
                  (right :: words).map (fun word => readWires word next) =
                    (right :: words).map (fun word => readWires word input) := by
                apply List.map_congr_left
                intro word wordMember
                apply List.map_congr_left
                intro wire wireMember
                have wordInAll : word ∈ left :: right :: words := by
                  simp [wordMember]
                have flatMember : wire ∈ (left :: right :: words).flatten := by
                  rw [List.mem_flatten]
                  exact ⟨word, wordInAll, wireMember⟩
                have first := List.mem_append_left compareWork flatMember
                have second := List.mem_append_left andScratch first
                have third := List.mem_append_left degreeFlags second
                exact preserveCommon wire (by simpa [common] using third)
              have tailResult := inductionHypothesis (slot + 1) (right :: words)
                lessFlags needFlags next tailWordCount tailLessCount tailNeedCount
                tailSupportNodup
              simp only [decoderComparisonReferenceGoodBits,
                decoderExpectedGoodBits, List.map_cons]
              rw [tailResult, degreeUnchanged, tailWordsUnchanged]
              simp [readWires, List.map_drop]

/--
実際の可逆比較列をclean layout上で実行後にgood列を読むと、degreeと隣接wordからなる
静的仕様`decoderExpectedGoodBits`へ厳密に一致する。
-/
theorem readWires_decoderComparisonSequence_good
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (words : List (List (Wire ancillaQubits systemQubits)))
    (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (wordCount : words.length = goodFlags.length + 1)
    (lessCount : lessFlags.length = goodFlags.length)
    (needCount : needFlags.length = goodFlags.length)
    (wordLengths : ∀ word ∈ words, word.length = compareWork.length)
    (supportNodup :
      (decoderComparisonSupport degreeFlags compareWork andScratch
        words lessFlags needFlags goodFlags).Nodup)
    (compareZero : readWires compareWork input =
      List.replicate compareWork.length false)
    (scratchZero : ∀ wire ∈ andScratch, input wire = false)
    (lessZero : readWires lessFlags input =
      List.replicate lessFlags.length false)
    (needZero : readWires needFlags input =
      List.replicate needFlags.length false)
    (goodZero : readWires goodFlags input =
      List.replicate goodFlags.length false)
    (scratchEnough : compareWork.length ≤ andScratch.length) :
    readWires goodFlags
        ((decoderComparisonSequence degreeFlags compareWork andScratch slot
          words lessFlags needFlags goodFlags).runBasis
          reversibleGatePermutation input) =
      decoderExpectedGoodBits (readWires degreeFlags input) slot
        (words.map fun word => readWires word input) := by
  rw [runBasis_decoderComparisonSequence_reference degreeFlags compareWork andScratch
    slot words lessFlags needFlags goodFlags input wordCount lessCount needCount
    wordLengths supportNodup compareZero scratchZero lessZero needZero goodZero
    scratchEnough]
  rw [readWires_decoderComparisonReferenceAction_good degreeFlags compareWork
    andScratch slot words lessFlags needFlags goodFlags input wordCount lessCount
    needCount supportNodup goodZero]
  exact decoderComparisonReferenceGoodBits_eq_expected degreeFlags compareWork
    andScratch slot words lessFlags needFlags goodFlags input wordCount lessCount
    needCount supportNodup

/--
隣接比較列は各比較器のcompute--use--uncomputeによりAND scratchを全て0へ戻す。
この補題はword数やword幅に依存せず、行列成分や全基底を展開しない。
-/
theorem runBasis_decoderComparisonSequence_scratch_clean
    {ancillaQubits systemQubits : Nat}
    (degreeFlags compareWork andScratch : List (Wire ancillaQubits systemQubits))
    (slot : Nat) (words : List (List (Wire ancillaQubits systemQubits)))
    (lessFlags needFlags goodFlags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (wordCount : words.length = goodFlags.length + 1)
    (lessCount : lessFlags.length = goodFlags.length)
    (needCount : needFlags.length = goodFlags.length)
    (wordLengths : ∀ word ∈ words, word.length = compareWork.length)
    (supportNodup :
      (decoderComparisonSupport degreeFlags compareWork andScratch
        words lessFlags needFlags goodFlags).Nodup)
    (compareZero : readWires compareWork input =
      List.replicate compareWork.length false)
    (scratchZero : ∀ wire ∈ andScratch, input wire = false)
    (lessZero : readWires lessFlags input =
      List.replicate lessFlags.length false)
    (needZero : readWires needFlags input =
      List.replicate needFlags.length false)
    (goodZero : readWires goodFlags input =
      List.replicate goodFlags.length false)
    (scratchEnough : compareWork.length ≤ andScratch.length) :
    ∀ wire ∈ andScratch,
      (decoderComparisonSequence degreeFlags compareWork andScratch slot
        words lessFlags needFlags goodFlags).runBasis
        reversibleGatePermutation input wire = false := by
  intro wire member
  rw [runBasis_decoderComparisonSequence_reference degreeFlags compareWork andScratch
    slot words lessFlags needFlags goodFlags input wordCount lessCount needCount
    wordLengths supportNodup compareZero scratchZero lessZero needZero goodZero
    scratchEnough]
  have splitNodup :
      ((words.flatten ++ compareWork ++ andScratch ++ degreeFlags) ++
        (lessFlags ++ needFlags ++ goodFlags)).Nodup := by
    simpa [decoderComparisonSupport, List.append_assoc] using supportNodup
  have separated := (List.nodup_append.mp splitNodup).2.2
  have prefixMember :
      wire ∈ words.flatten ++ compareWork ++ andScratch ++ degreeFlags := by
    simp [member]
  have outsideOutputs : wire ∉ lessFlags ++ needFlags ++ goodFlags := by
    intro outputMember
    exact separated wire prefixMember wire outputMember rfl
  have outsideLess : wire ∉ lessFlags := by
    intro lessMember
    exact outsideOutputs (by simp [lessMember])
  have outsideNeed : wire ∉ needFlags := by
    intro needMember
    exact outsideOutputs (by simp [needMember])
  have outsideGood : wire ∉ goodFlags := by
    intro goodMember
    exact outsideOutputs (by simp [goodMember])
  rw [decoderComparisonReferenceAction_outside degreeFlags slot words lessFlags
    needFlags goodFlags input wire outsideLess outsideNeed outsideGood]
  exact scratchZero wire member

/--
degree decodeのcompute--use--uncomputeはinput・suffixを厳密復元し、degree useが変更した
外部flagだけを残す。
-/
theorem runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_local_clean
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires flags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (inputDisjointFlags : inputWires.Disjoint flags)
    (suffixDisjointFlags : suffixWires.Disjoint flags) :
    (xorDelimiterDegreeOneHotIntoTargetsCircuit wordWidth inputWires suffixWires flags).runBasis
        reversibleGatePermutation input =
      restoreSupport (inputWires ++ suffixWires) input
        ((degreeBoundarySequence wordWidth inputWires suffixWires 0 flags).runBasis
          reversibleGatePermutation
          ((suffixOrCircuit inputWires suffixWires).runBasis
            reversibleGatePermutation input)) := by
  let support := inputWires ++ suffixWires
  let compute := suffixOrCircuit inputWires suffixWires
  let use := degreeBoundarySequence wordWidth inputWires suffixWires 0 flags
  have computeUses : circuitUsesOnly support compute :=
    circuitUsesOnly_suffixOrCircuit inputWires suffixWires
  have usePreserves :
      BasisAgreeOn support
        (use.runBasis reversibleGatePermutation
          (compute.runBasis reversibleGatePermutation input))
        (compute.runBasis reversibleGatePermutation input) := by
    intro wire member
    apply runBasis_degreeBoundarySequence_outside wordWidth inputWires suffixWires
      flags 0 wire (compute.runBasis reversibleGatePermutation input)
      inputDisjointSuffix inputDisjointFlags suffixDisjointFlags
    intro flagMember
    rcases List.mem_append.mp member with inputMember | suffixMember
    · exact (List.disjoint_left.mp inputDisjointFlags) inputMember flagMember
    · exact (List.disjoint_left.mp suffixDisjointFlags) suffixMember flagMember
  simpa [xorDelimiterDegreeOneHotIntoTargetsCircuit, support, compute, use] using
    Circuit.computeUseUncompute_local_clean support compute use input
      computeUses usePreserves

/-- degree decodeはinput・suffix・degree flagの全てから外れたwireを変更しない。 -/
theorem runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires flags : List (Wire ancillaQubits systemQubits))
    (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (sameLength : inputWires.length = suffixWires.length)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (inputDisjointFlags : inputWires.Disjoint flags)
    (suffixDisjointFlags : suffixWires.Disjoint flags)
    (suffixNodup : suffixWires.Nodup)
    (outsideInput : wire ∉ inputWires)
    (outsideSuffix : wire ∉ suffixWires)
    (outsideFlags : wire ∉ flags) :
    (xorDelimiterDegreeOneHotIntoTargetsCircuit wordWidth inputWires suffixWires flags).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_local_clean wordWidth inputWires suffixWires
    flags input inputDisjointSuffix inputDisjointFlags suffixDisjointFlags]
  rw [restoreSupport_outside (inputWires ++ suffixWires) input _ wire
    (by simp [outsideInput, outsideSuffix])]
  rw [runBasis_degreeBoundarySequence_outside wordWidth inputWires suffixWires
    flags 0 wire _ inputDisjointSuffix inputDisjointFlags suffixDisjointFlags
    outsideFlags]
  exact runBasis_suffixOrCircuit_outside inputWires suffixWires wire input
    sameLength inputDisjointSuffix suffixNodup outsideSuffix

/-- degree decodeはcompute--uncomputeにより任意のinput wire値を厳密に復元する。 -/
theorem runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_input_wire
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires flags : List (Wire ancillaQubits systemQubits))
    (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (inputDisjointFlags : inputWires.Disjoint flags)
    (suffixDisjointFlags : suffixWires.Disjoint flags)
    (member : wire ∈ inputWires) :
    (xorDelimiterDegreeOneHotIntoTargetsCircuit wordWidth inputWires suffixWires flags).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_local_clean wordWidth inputWires suffixWires
    flags input inputDisjointSuffix inputDisjointFlags suffixDisjointFlags]
  simp [restoreSupport, member]

/-- degree decode後のinput・suffix supportは開始時の値へ完全に戻る。 -/
theorem runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_support_clean
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires flags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (inputDisjointFlags : inputWires.Disjoint flags)
    (suffixDisjointFlags : suffixWires.Disjoint flags) :
    readWires (inputWires ++ suffixWires)
        ((xorDelimiterDegreeOneHotIntoTargetsCircuit wordWidth inputWires suffixWires flags).runBasis
          reversibleGatePermutation input) =
      readWires (inputWires ++ suffixWires) input := by
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_local_clean wordWidth inputWires suffixWires flags
    input inputDisjointSuffix inputDisjointFlags suffixDisjointFlags]
  apply List.map_congr_left
  intro wire member
  simp [restoreSupport, member]

/--
clean suffix・degree flagからdegree decodeを実行すると、flag列は入力bit列のdelimiter
境界条件列になり、suffixは同じ回路内で消去される。
-/
theorem readWires_xorDelimiterDegreeOneHotIntoTargetsCircuit
    {ancillaQubits systemQubits : Nat}
    (wordWidth : Nat)
    (inputWires suffixWires flags : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (sameLength : inputWires.length = suffixWires.length)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (inputDisjointFlags : inputWires.Disjoint flags)
    (suffixDisjointFlags : suffixWires.Disjoint flags)
    (suffixNodup : suffixWires.Nodup) (flagsNodup : flags.Nodup)
    (suffixZero : readWires suffixWires input =
      List.replicate suffixWires.length false)
    (flagsZero : readWires flags input = List.replicate flags.length false) :
    readWires flags
        ((xorDelimiterDegreeOneHotIntoTargetsCircuit wordWidth inputWires suffixWires flags).runBasis
          reversibleGatePermutation input) =
      degreeBoundaryBits wordWidth (readWires inputWires input)
        (suffixOrBits (readWires inputWires input)) 0
        (List.replicate flags.length false) := by
  let compute := suffixOrCircuit inputWires suffixWires
  let computed := compute.runBasis reversibleGatePermutation input
  let use := degreeBoundarySequence wordWidth inputWires suffixWires 0 flags
  let used := use.runBasis reversibleGatePermutation computed
  have finalState := runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_local_clean wordWidth inputWires
    suffixWires flags input inputDisjointSuffix inputDisjointFlags suffixDisjointFlags
  rw [finalState]
  have flagsOutside : ∀ wire ∈ flags, wire ∉ inputWires ++ suffixWires := by
    intro wire flagMember supportMember
    rcases List.mem_append.mp supportMember with inputMember | suffixMember
    · exact (List.disjoint_left.mp inputDisjointFlags) inputMember flagMember
    · exact (List.disjoint_left.mp suffixDisjointFlags) suffixMember flagMember
  have restoreFlags :
      readWires flags (restoreSupport (inputWires ++ suffixWires) input used) =
        readWires flags used := by
    apply List.map_congr_left
    intro wire member
    exact restoreSupport_outside (inputWires ++ suffixWires) input used wire
      (flagsOutside wire member)
  rw [restoreFlags]
  have inputValues : readWires inputWires computed = readWires inputWires input := by
    apply List.map_congr_left
    intro wire member
    apply runBasis_suffixOrCircuit_outside inputWires suffixWires wire input
      sameLength inputDisjointSuffix suffixNodup
    intro suffixMember
    exact (List.disjoint_left.mp inputDisjointSuffix) member suffixMember
  have suffixValues :
      readWires suffixWires computed = suffixOrBits (readWires inputWires input) := by
    exact readWires_suffixOrCircuit inputWires suffixWires input sameLength
      inputDisjointSuffix suffixNodup suffixZero
  have flagValues : readWires flags computed = readWires flags input := by
    apply List.map_congr_left
    intro wire member
    apply runBasis_suffixOrCircuit_outside inputWires suffixWires wire input
      sameLength inputDisjointSuffix suffixNodup
    intro suffixMember
    exact (List.disjoint_left.mp suffixDisjointFlags) suffixMember member
  change readWires flags (use.runBasis reversibleGatePermutation computed) = _
  rw [readWires_degreeBoundarySequence wordWidth inputWires suffixWires flags 0
    computed inputDisjointSuffix inputDisjointFlags suffixDisjointFlags flagsNodup]
  rw [inputValues, suffixValues, flagValues, flagsZero]

/--
合法delimiter符号を読むdegree decodeは、配置の粒子数に対応するone-hot flag列を返す。
-/
theorem readWires_xorDelimiterDegreeOneHotIntoTargetsCircuit_delimiterEncoding
    {p : QParameters} (configuration : QConfiguration p)
    (inputWires suffixWires flags : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (sameLength : inputWires.length = suffixWires.length)
    (inputDisjointSuffix : inputWires.Disjoint suffixWires)
    (inputDisjointFlags : inputWires.Disjoint flags)
    (suffixDisjointFlags : suffixWires.Disjoint flags)
    (suffixNodup : suffixWires.Nodup) (flagsNodup : flags.Nodup)
    (suffixZero : readWires suffixWires input =
      List.replicate suffixWires.length false)
    (flagsZero : readWires flags input = List.replicate flags.length false)
    (inputBits : readWires inputWires input =
      registerBitList (delimiterEncoding configuration)) :
    readWires flags
        ((xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires suffixWires flags).runBasis
          reversibleGatePermutation input) =
      degreeOneHotFrom flags.length configuration.1.card 0 := by
  rw [readWires_xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires suffixWires flags input
    sameLength inputDisjointSuffix inputDisjointFlags suffixDisjointFlags
    suffixNodup flagsNodup suffixZero flagsZero]
  rw [inputBits]
  exact degreeBoundaryBits_delimiterEncoding_oneHot configuration flags.length 0

/--
one-hot degree flagとclean present flagからslot presence回路を実行すると、粒子数未満の
slotだけが1になる。
-/
theorem readWires_slotPresenceCircuit_degreeOneHot
    {ancillaQubits systemQubits : Nat}
    (degreeFlags presentFlags : List (Wire ancillaQubits systemQubits))
    (particleCount : Nat) (input : JointBasis ancillaQubits systemQubits)
    (degreeDisjointPresent : degreeFlags.Disjoint presentFlags)
    (presentNodup : presentFlags.Nodup)
    (degreeValues : readWires degreeFlags input =
      degreeOneHotFrom degreeFlags.length particleCount 0)
    (presentZero : readWires presentFlags input =
      List.replicate presentFlags.length false)
    (presentFits : presentFlags.length ≤ degreeFlags.length)
    (particleBound : particleCount ≤ degreeFlags.length) :
    readWires presentFlags
        ((slotPresenceCircuit degreeFlags presentFlags).runBasis
          reversibleGatePermutation input) =
      presenceBitsFrom presentFlags.length particleCount 0 := by
  rw [readWires_slotPresenceCircuit degreeFlags presentFlags input
    degreeDisjointPresent presentNodup]
  rw [degreeValues, presentZero]
  exact slotPresenceBits_degreeOneHot degreeFlags.length particleCount 0
    presentFlags.length (by simpa using presentFits) particleBound

end ReversibleCircuit

end ProbabilityGeneratorQProof
