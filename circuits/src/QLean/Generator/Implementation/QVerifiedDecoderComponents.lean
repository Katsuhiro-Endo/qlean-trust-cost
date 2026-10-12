import QLean.Generator.Implementation.QVerifiedArithmeticComponents
import QLean.Generator.Implementation.QVerifiedOracleComponents

/-!
# decoder・membership の作用中心階層component

membership は一つの slot 比較を xorEqualityIntoTargetCircuit 部品と局所 flag 更新から作り、slot 列を
不変条件付き逐次合成で畳み込む。compact decoder は degree decode と legality 判定を
独立な子契約から組み立てるための公開層を与える。
-/

namespace ProbabilityGeneratorQProof

namespace CleanComponent

/-- 指定した不変条件を入出力条件に持つ、空の clean 部品。 -/
def identityOnInvariant
    {Gate basis : Type*} (gatePermutation : Gate → Equiv.Perm basis)
    (invariant : basis → Prop) : CleanComponent gatePermutation where
  circuit := .identity
  reference := id
  inputCondition := invariant
  outputCondition := invariant
  restoration := fun input output => output = input
  runBasis_correct := by intro input _; rfl
  outputCondition_correct := by intro input clean; exact clean
  restoration_correct := by intro input _; rfl

/--
二つの clean 部品が共通不変条件を受理・保存するとき、その不変条件上で逐次合成する。
親は子の基底作用を展開せず、二つの公開 `runBasis_correct` だけを利用する。
-/
def seqOnInvariant
    {Gate basis : Type*} {gatePermutation : Gate → Equiv.Perm basis}
    (invariant : basis → Prop) (first second : CleanComponent gatePermutation)
    (firstAccepts : ∀ input, invariant input → first.inputCondition input)
    (firstPreserves : ∀ output, first.outputCondition output → invariant output)
    (secondAccepts : ∀ input, invariant input → second.inputCondition input)
    (secondPreserves : ∀ output, second.outputCondition output → invariant output) :
    CleanComponent gatePermutation where
  circuit := .seq first.circuit second.circuit
  reference := fun input => second.reference (first.reference input)
  inputCondition := invariant
  outputCondition := invariant
  restoration := fun input output =>
    output = second.reference (first.reference input)
  runBasis_correct := by
    intro input clean
    change second.circuit.toExecutionPermutation gatePermutation
        (first.circuit.toExecutionPermutation gatePermutation input) =
      second.reference (first.reference input)
    rw [show first.circuit.toExecutionPermutation gatePermutation input =
        first.reference input from
      first.runBasis_correct input (firstAccepts input clean)]
    exact second.runBasis_correct (first.reference input)
      (secondAccepts _ (firstPreserves _
        (first.outputCondition_correct input (firstAccepts input clean))))
  outputCondition_correct := by
    intro input clean
    exact secondPreserves _ (second.outputCondition_correct _
      (secondAccepts _ (firstPreserves _
        (first.outputCondition_correct input (firstAccepts input clean)))))
  restoration_correct := by intro input _; rfl

end CleanComponent

namespace ReversibleCircuit

/--
一つの membership slot の作用を、公開 xorEqualityIntoTargetCircuit 子契約と局所 X/Toffoli 作用だけから導く。
-/
theorem runBasis_xorSiteSlotMatchAndGoodFlagAtIndexCircuit
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input) :
    (xorSiteSlotMatchAndGoodFlagAtIndexCircuit p register selectedSlot slot
      includePresentOther).runBasis reversibleGatePermutation input =
      SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
        includePresentOther input := by
  let layout := membershipSlotLayout_canonical p register inputLayout slot
  let equalityChild := verifiedXorEqualityIntoTargetCleanComponent (oracleMovedWires p)
    (registerWordAt p register slot) (oracleCompareWorkWires p)
    (decoderAndScratchWires p) (membershipEqualWireAt p slot)
    layout.moved_length layout.word_length layout.moved_disjoint_equalWork
    layout.word_disjoint_equalWork layout.equalWork_disjoint_scratch
    layout.equalWork_nodup layout.equality_layout layout.equal_absent_moved
    layout.equal_absent_word layout.enough_scratch
  have equalityCorrect :
      (xorEqualityIntoTargetCircuit (oracleMovedWires p) (registerWordAt p register slot)
        (oracleCompareWorkWires p) (decoderAndScratchWires p)
        (membershipEqualWireAt p slot)).runBasis reversibleGatePermutation input =
          equalityAnalyticAction (oracleMovedWires p)
            (registerWordAt p register slot) (membershipEqualWireAt p slot) input
      := by
    simpa [equalityChild, verifiedXorEqualityIntoTargetCleanComponent,
      xorEqualityIntoTargetAnalyticAction, equalityAnalyticAction] using
      equalityChild.runBasis_correct input
        ⟨clean.equalWork_zero, clean.scratch_zero⟩
  simp only [xorSiteSlotMatchAndGoodFlagAtIndexCircuit, membershipSlotCircuit,
    SiteSlotMatchAndGoodFlagAtIndexXorSpec, runBasis_seq]
  rw [equalityCorrect]
  rw [runBasis_local_x]
  rw [runBasis_local_safeToffoli (oraclePresentWireAt p slot)
    (membershipEqualWireAt p slot) (membershipGoodWireAt p slot)
    layout.present_ne_equal layout.present_ne_good layout.equal_ne_good]
  split
  · rw [runBasis_local_safeToffoli (oraclePresentWireAt p slot)
      (membershipEqualWireAt p slot) (oraclePresentOtherWire p)
      layout.present_ne_equal layout.present_ne_other layout.equal_ne_other]
    rfl
  · rfl

/--
一つの membership slot を、公開 xorEqualityIntoTargetCircuit 子部品と局所 flag 更新から構成する。
解析参照は回路から独立な `SiteSlotMatchAndGoodFlagAtIndexXorSpec` である。
-/
def verifiedXorSiteSlotMatchAndGoodFlagAtIndexCleanComponent
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorSiteSlotMatchAndGoodFlagAtIndexCircuit p register selectedSlot slot
    includePresentOther
  reference := SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
    includePresentOther
  inputCondition := MembershipSlotClean (oracleCompareWorkWires p)
    (decoderAndScratchWires p)
  outputCondition := MembershipSlotClean (oracleCompareWorkWires p)
    (decoderAndScratchWires p)
  restoration := fun input output => output =
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
  runBasis_correct := runBasis_xorSiteSlotMatchAndGoodFlagAtIndexCircuit p register inputLayout
    selectedSlot slot includePresentOther
  outputCondition_correct := by
    intro input clean
    rw [← runBasis_xorSiteSlotMatchAndGoodFlagAtIndexCircuit p register inputLayout
      selectedSlot slot includePresentOther input clean]
    exact membershipSlotCircuit_clean_canonical p register inputLayout slot
      (includePresentOther && slot != selectedSlot) input clean
  restoration_correct := by
    intro input _
    rfl

/-- 指定したslot列の局所membership回路を左から順に畳み込む作用名付き回路。 -/
def foldSiteSlotMatchAndGoodFlagsCircuit
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (slots : List (Fin p.K)) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  Circuit.sequence <| slots.map fun slot =>
    xorSiteSlotMatchAndGoodFlagAtIndexCircuit p register selectedSlot slot
      includePresentOther

/--
任意の slot 列について、各 slot 子componentの公開契約だけを帰納合成するfold定理。
-/
theorem runBasis_foldSiteSlotMatchAndGoodFlagsCircuit
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      MembershipSlotClean (oracleCompareWorkWires p)
        (decoderAndScratchWires p) input →
      let output := (foldSiteSlotMatchAndGoodFlagsCircuit p register selectedSlot
        includePresentOther slots).runBasis reversibleGatePermutation input
      output = FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot
          includePresentOther slots input ∧
        MembershipSlotClean (oracleCompareWorkWires p)
          (decoderAndScratchWires p) output
  | [], input, clean => by exact ⟨rfl, clean⟩
  | slot :: slots, input, clean => by
      let first := verifiedXorSiteSlotMatchAndGoodFlagAtIndexCleanComponent p register inputLayout
        selectedSlot slot includePresentOther
      let afterFirst := first.circuit.runBasis reversibleGatePermutation input
      have firstEq : afterFirst = SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot
          slot includePresentOther input := by
        have result := first.runBasis_correct input clean
        dsimp [first, afterFirst, verifiedXorSiteSlotMatchAndGoodFlagAtIndexCleanComponent] at result
        exact result
      have firstClean : MembershipSlotClean (oracleCompareWorkWires p)
          (decoderAndScratchWires p) afterFirst := by
        have result := first.outputCondition_correct input clean
        change MembershipSlotClean (oracleCompareWorkWires p)
          (decoderAndScratchWires p)
            (SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
              includePresentOther input) at result
        rw [← firstEq] at result
        exact result
      have tail := runBasis_foldSiteSlotMatchAndGoodFlagsCircuit p register inputLayout
        selectedSlot includePresentOther slots afterFirst firstClean
      constructor
      · change (foldSiteSlotMatchAndGoodFlagsCircuit p register selectedSlot
            includePresentOther slots).runBasis reversibleGatePermutation afterFirst = _
        rw [tail.1, firstEq]
        rfl
      · exact tail.2

/-- 任意のslot列を一つのslot部品族とfold合成定理で包装したclean component。 -/
def verifiedFoldSiteSlotMatchAndGoodFlagsCleanComponent
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (slots : List (Fin p.K)) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := foldSiteSlotMatchAndGoodFlagsCircuit p register selectedSlot includePresentOther slots
  reference := FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot
    includePresentOther slots
  inputCondition := MembershipSlotClean (oracleCompareWorkWires p)
    (decoderAndScratchWires p)
  outputCondition := MembershipSlotClean (oracleCompareWorkWires p)
    (decoderAndScratchWires p)
  restoration := fun input output => output = FoldedSiteSlotMatchAndGoodFlagsReference p register
    selectedSlot includePresentOther slots input
  runBasis_correct := by
    intro input clean
    exact (runBasis_foldSiteSlotMatchAndGoodFlagsCircuit p register inputLayout
      selectedSlot includePresentOther slots input clean).1
  outputCondition_correct := by
    intro input clean
    rw [← (runBasis_foldSiteSlotMatchAndGoodFlagsCircuit p register inputLayout
      selectedSlot includePresentOther slots input clean).1]
    exact (runBasis_foldSiteSlotMatchAndGoodFlagsCircuit p register inputLayout
      selectedSlot includePresentOther slots input clean).2
  restoration_correct := by intro input _; rfl

/-- 全 membership good flag の AND を absent flag へ書く回路非依存参照作用。 -/
def NoGoodSlotAbsentFlagXorSpec (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  if allWiresTrue (membershipGoodWires p) input then
    xBasisAction (oracleAbsentWire p) input
  else input

/-- absent flag は比較 work と AND scratch の外側にある。 -/
theorem NoGoodSlotAbsentFlagXorSpec_preserves_clean (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input) :
    MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) (NoGoodSlotAbsentFlagXorSpec p input) := by
  unfold NoGoodSlotAbsentFlagXorSpec
  split
  · apply clean.xBasisAction_of_outside
    · let absentSlice := QLayout.oracleSlice
        (OracleWorkLayout.canonical p).absent
      let compareSlice := QLayout.oracleSlice
        (OracleWorkLayout.canonical p).compareWork
      have disjoint :
          (absentSlice.wireList :
            List (Wire p.ancillaWidth p.systemWidth)).Disjoint
            (compareSlice.wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        apply RegisterSlice.wireList_disjoint_of_end_le_start
        simp [absentSlice, compareSlice, QLayout.oracleSlice,
          RegisterSlice.compose, OracleWorkLayout.canonical]
        omega
      intro member
      have absentMember : oracleAbsentWire p ∈
          (absentSlice.wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleAbsentWire, oracleSingletonWire, absentSlice,
          RegisterSlice.wireList]
      have compareMember : oracleAbsentWire p ∈
          (compareSlice.wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
        simpa [oracleCompareWorkWires, compareSlice,
          RegisterSlice.wireList] using member
      exact (List.disjoint_left.mp disjoint absentMember) compareMember
    · have nodup := membershipAbsent_layout_nodup p
      have separated := (List.nodup_append.mp nodup).2.2
      intro member
      exact separated (oracleAbsentWire p)
        (List.mem_append_right _ member) (oracleAbsentWire p) (by simp) rfl
  · exact clean

/-- good flagがすべて0のときだけabsent flagへXORする作用名付き回路。 -/
def xorNoGoodSlotIntoAbsentFlagCircuit (p : QParameters) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  positiveMultiControlledX (membershipGoodWires p)
    (decoderAndScratchWires p) (oracleAbsentWire p)

/-- good flag列から absent を計算する局所 clean 部品。 -/
def verifiedXorNoGoodSlotIntoAbsentFlagCleanComponent (p : QParameters) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorNoGoodSlotIntoAbsentFlagCircuit p
  reference := NoGoodSlotAbsentFlagXorSpec p
  inputCondition := MembershipSlotClean (oracleCompareWorkWires p)
    (decoderAndScratchWires p)
  outputCondition := MembershipSlotClean (oracleCompareWorkWires p)
    (decoderAndScratchWires p)
  restoration := fun input output => output = NoGoodSlotAbsentFlagXorSpec p input
  runBasis_correct := by
    intro input clean
    simpa [xorNoGoodSlotIntoAbsentFlagCircuit, NoGoodSlotAbsentFlagXorSpec] using
      runBasis_positiveMultiControlledX (membershipGoodWires p)
        (decoderAndScratchWires p) (oracleAbsentWire p) input
        (membershipAbsent_enoughScratch p) (membershipAbsent_layout_nodup p)
        clean.scratch_zero
  outputCondition_correct := NoGoodSlotAbsentFlagXorSpec_preserves_clean p
  restoration_correct := by intro input _; rfl

/-- 全slot列とabsent局所部品の公開契約からmembership作用を導く逐次合成定理。 -/
theorem runBasis_xorMembershipMatchGoodAndAbsentFlagsCircuit
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipWorkRestored p input) :
    (xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot includePresentOther).runBasis
        reversibleGatePermutation input =
      MembershipMatchGoodAndAbsentFlagsXorSpec p register selectedSlot includePresentOther input := by
  let slots := verifiedFoldSiteSlotMatchAndGoodFlagsCleanComponent p register inputLayout
    selectedSlot includePresentOther (List.finRange p.K)
  let afterSlots := slots.reference input
  have slotsEq : slots.circuit.runBasis reversibleGatePermutation input =
      afterSlots := slots.runBasis_correct input clean
  have slotsClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) afterSlots :=
    slots.outputCondition_correct input clean
  let absent := verifiedXorNoGoodSlotIntoAbsentFlagCleanComponent p
  have absentEq := absent.runBasis_correct afterSlots slotsClean
  have slotsEq' :
      (Circuit.sequence (siteSlotMatchAndGoodFlagCircuits p register selectedSlot
        includePresentOther)).runBasis reversibleGatePermutation input = afterSlots := by
    simpa [slots, verifiedFoldSiteSlotMatchAndGoodFlagsCleanComponent,
      foldSiteSlotMatchAndGoodFlagsCircuit, siteSlotMatchAndGoodFlagCircuits] using slotsEq
  simp only [xorMembershipMatchGoodAndAbsentFlagsCircuit, runBasis_seq]
  rw [slotsEq']
  exact absentEq

/--
全 slot 列と absent 書込みを子 component の公開契約だけで合成した membership component。
-/
def verifiedXorMembershipMatchGoodAndAbsentFlagsCleanComponent
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot includePresentOther
  reference := MembershipMatchGoodAndAbsentFlagsXorSpec p register selectedSlot includePresentOther
  inputCondition := MembershipWorkRestored p
  outputCondition := MembershipWorkRestored p
  restoration := fun input output => output =
    MembershipMatchGoodAndAbsentFlagsXorSpec p register selectedSlot includePresentOther input
  runBasis_correct := runBasis_xorMembershipMatchGoodAndAbsentFlagsCircuit p register inputLayout
    selectedSlot includePresentOther
  outputCondition_correct := by
    intro input clean
    let slots := verifiedFoldSiteSlotMatchAndGoodFlagsCleanComponent p register inputLayout
      selectedSlot includePresentOther (List.finRange p.K)
    let afterSlots := slots.reference input
    have slotsClean : MembershipSlotClean (oracleCompareWorkWires p)
        (decoderAndScratchWires p) afterSlots :=
      slots.outputCondition_correct input clean
    exact (verifiedXorNoGoodSlotIntoAbsentFlagCleanComponent p).outputCondition_correct
      afterSlots slotsClean
  restoration_correct := by intro input _; rfl

/-- membership componentの回路は既存の型安全な正本回路と定義的に一致する。 -/
@[simp] theorem verifiedXorMembershipMatchGoodAndAbsentFlagsCleanComponent_circuit
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    (verifiedXorMembershipMatchGoodAndAbsentFlagsCleanComponent p register inputLayout selectedSlot
      includePresentOther).circuit =
      xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot includePresentOther := by
  rfl

/-- membership componentの参照作用は既存の回路非依存解析参照と定義的に一致する。 -/
@[simp] theorem verifiedXorMembershipMatchGoodAndAbsentFlagsCleanComponent_reference
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    (verifiedXorMembershipMatchGoodAndAbsentFlagsCleanComponent p register inputLayout selectedSlot
      includePresentOther).reference =
      MembershipMatchGoodAndAbsentFlagsXorSpec p register selectedSlot includePresentOther := by
  rfl

/-- degree decode後のdegree one-hotと、degree列外の全wire復元を表す解析仕様。 -/
structure DelimiterDegreeOneHotXorSpec (p : QParameters)
    (configuration : QConfiguration p)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- degree列はconfigurationの粒子数を表すone-hotになる。 -/
  degree_one_hot : readWires (oracleDegreeWires p) output =
    degreeOneHotFrom p.K configuration.1.card 0
  /-- degree列以外は入力値へ戻る。 -/
  outside_degree_restored : ∀ wire, wire ∉ oracleDegreeWires p →
    output wire = input wire

/-- degree decode解析仕様は全wire上で出力を一意に定める。 -/
theorem DelimiterDegreeOneHotXorSpec.unique
    {p : QParameters} {configuration : QConfiguration p}
    {input left right : JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : DelimiterDegreeOneHotXorSpec p configuration input left)
    (rightSpec : DelimiterDegreeOneHotXorSpec p configuration input right) :
    left = right := by
  funext wire
  by_cases member : wire ∈ oracleDegreeWires p
  · exact readWires_eq_at_of_eq (oracleDegreeWires p) left right
      (leftSpec.degree_one_hot.trans rightSpec.degree_one_hot.symm) member
  · exact (leftSpec.outside_degree_restored wire member).trans
      (rightSpec.outside_degree_restored wire member).symm

/-- degree decodeの回路非依存な解析参照作用。 -/
noncomputable def delimiterDegreeOneHotXorReference (p : QParameters)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (uniqueSpecificationReference fun source output =>
    DelimiterDegreeOneHotXorSpec p configuration source output) input

/-- degree decode正本が回路非依存のdegree仕様を満たす。 -/
theorem xorDelimiterDegreeOneHotIntoTargetsCircuit_componentSpec
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    DelimiterDegreeOneHotXorSpec p configuration input
      ((xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input) := by
  let output := (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires
    (decoderSuffixWires p) (oracleDegreeWires p)).runBasis
      reversibleGatePermutation input
  refine { degree_one_hot := ?_, outside_degree_restored := ?_ }
  · change readWires (oracleDegreeWires p) output = _
    rw [show readWires (oracleDegreeWires p) output =
        degreeBoundaryBits p.wordWidth (readWires inputWires input)
          (suffixOrBits (readWires inputWires input)) 0
          (List.replicate (oracleDegreeWires p).length false) by
      exact readWires_xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires
        (decoderSuffixWires p) (oracleDegreeWires p) input
        (by simp [layout.length_eq]) layout.disjoint_suffix
        layout.disjoint_degree
        (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
        (decoderSuffixWires_nodup p) (oracleDegreeWires_nodup p)
        clean.suffix_zero clean.degree_zero]
    rw [clean.input_bits]
    simpa using degreeBoundaryBits_delimiterEncoding_oneHot configuration p.K 0
  · intro wire outsideDegree
    by_cases inputMember : wire ∈ inputWires
    · exact runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_input_wire p.wordWidth inputWires
        (decoderSuffixWires p) (oracleDegreeWires p) wire input
        layout.disjoint_suffix layout.disjoint_degree
        (oracleDegreeWires_disjoint_decoderSuffixWires p).symm inputMember
    by_cases suffixMember : wire ∈ decoderSuffixWires p
    · have support := runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_support_clean p.wordWidth
        inputWires (decoderSuffixWires p) (oracleDegreeWires p) input
        layout.disjoint_suffix layout.disjoint_degree
        (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
      exact readWires_eq_at_of_eq (inputWires ++ decoderSuffixWires p)
        output input (by simpa [output] using support) (by simp [suffixMember])
    · exact runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
        (decoderSuffixWires p) (oracleDegreeWires p) wire input
        (by simp [layout.length_eq]) layout.disjoint_suffix
        layout.disjoint_degree
        (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
        (decoderSuffixWires_nodup p) inputMember suffixMember outsideDegree

/-- degree decode正本を独立な一意解析仕様へ包装した子component。 -/
noncomputable def verifiedXorDelimiterDegreeOneHotIntoTargetsCleanComponent
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
    (oracleDegreeWires p)
  reference := delimiterDegreeOneHotXorReference p configuration
  inputCondition := CompactDecoderCleanInput p inputWires configuration
  outputCondition := fun _ => True
  restoration := DelimiterDegreeOneHotXorSpec p configuration
  runBasis_correct := by
    intro input clean
    let actual := (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires
      (decoderSuffixWires p) (oracleDegreeWires p)).runBasis
        reversibleGatePermutation input
    have actualSpec := xorDelimiterDegreeOneHotIntoTargetsCircuit_componentSpec p inputWires layout
      configuration input clean
    have uniqueOutput : ∃! output,
        DelimiterDegreeOneHotXorSpec p configuration input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    exact uniqueOutput.unique actualSpec (by
      simpa [delimiterDegreeOneHotXorReference] using
        (uniqueSpecificationReference_spec uniqueOutput))
  outputCondition_correct := by simp
  restoration_correct := by
    intro input clean
    let actual := (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires
      (decoderSuffixWires p) (oracleDegreeWires p)).runBasis
        reversibleGatePermutation input
    have actualSpec := xorDelimiterDegreeOneHotIntoTargetsCircuit_componentSpec p inputWires layout
      configuration input clean
    have uniqueOutput : ∃! output,
        DelimiterDegreeOneHotXorSpec p configuration input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    simpa [delimiterDegreeOneHotXorReference] using
      (uniqueSpecificationReference_spec uniqueOutput)

/-- compact decoderのdegree decode後に実行するlegality compute--use--uncompute回路。 -/
def xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth)) :
    Circuit (ReversibleGate p.ancillaWidth p.systemWidth) :=
  let words := splitSystemWords p.wordWidth p.K inputWires
  let compute := decoderLegalityCompute words (oracleDegreeWires p)
    (decoderLessWires p) (decoderNeedWires p) (decoderGoodWires p)
    (oracleCompareWorkWires p) (decoderAndScratchWires p)
    (decoderDegreeValidWire p) (decoderLegalTemporaryWire p)
  let use := safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p)
  Circuit.computeUseUncompute id compute use

/-- legality phase後のlegal=trueと、legal以外の全wire復元を表す解析仕様。 -/
structure DelimiterAcceptanceLegalFlagXorSpec (p : QParameters)
    (input output : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 保持用legal wireはtrueになる。 -/
  legal_true : output (oracleLegalWire p) = true
  /-- legal wire以外はphase入力値へ戻る。 -/
  outside_legal_restored : ∀ wire, wire ≠ oracleLegalWire p →
    output wire = input wire

/-- legality phase解析仕様は全wire上で出力を一意に定める。 -/
theorem DelimiterAcceptanceLegalFlagXorSpec.unique
    {p : QParameters} {input left right :
      JointBasis p.ancillaWidth p.systemWidth}
    (leftSpec : DelimiterAcceptanceLegalFlagXorSpec p input left)
    (rightSpec : DelimiterAcceptanceLegalFlagXorSpec p input right) : left = right := by
  funext wire
  by_cases equal : wire = oracleLegalWire p
  · subst wire
    exact leftSpec.legal_true.trans rightSpec.legal_true.symm
  · exact (leftSpec.outside_legal_restored wire equal).trans
      (rightSpec.outside_legal_restored wire equal).symm

/-- legality phaseへ許す入力は、degree子componentのclean入力像に限定する。 -/
def DelimiterAcceptanceReachableInput (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p)
    (state : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∃ input, CompactDecoderCleanInput p inputWires configuration input ∧
    state = delimiterDegreeOneHotXorReference p configuration input

/--
reachable入力上でlegality phase正本が独立なphase仕様を満たす。
このcanonical compiled leafの内部だけは既存full compact解析specをbridgeとして再利用し、
上位compact親はこの定理を展開せずphase componentの公開fieldだけを利用する。
-/
theorem xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit_componentSpec
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (state : JointBasis p.ancillaWidth p.systemWidth)
    (reachable : DelimiterAcceptanceReachableInput p inputWires
      configuration state) :
    DelimiterAcceptanceLegalFlagXorSpec p state
      ((xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit p inputWires).runBasis
        reversibleGatePermutation state) := by
  rcases reachable with ⟨input, clean, rfl⟩
  let degree := verifiedXorDelimiterDegreeOneHotIntoTargetsCleanComponent p inputWires layout configuration
  let decoded := degree.reference input
  have degreeEq :
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
        (oracleDegreeWires p)).runBasis reversibleGatePermutation input = decoded :=
    degree.runBasis_correct input clean
  have degreeSpec : DelimiterDegreeOneHotXorSpec p configuration input decoded :=
    degree.restoration_correct input clean
  let final := (xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit p inputWires).runBasis
    reversibleGatePermutation decoded
  have fullEq :
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
          reversibleGatePermutation input = final := by
    change (xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit p inputWires).runBasis
      reversibleGatePermutation
        ((xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
          (oracleDegreeWires p)).runBasis reversibleGatePermutation input) = final
    rw [degreeEq]
  have finalSpec := verifiedDelimiterLegalityAndDegreeOneHotXorSpec p inputWires layout
    configuration input clean
  rw [fullEq] at finalSpec
  refine { legal_true := finalSpec.legal_true, outside_legal_restored := ?_ }
  intro wire notLegal
  by_cases degreeMember : wire ∈ oracleDegreeWires p
  · exact readWires_eq_at_of_eq (oracleDegreeWires p) final decoded
      (finalSpec.degree_one_hot.trans degreeSpec.degree_one_hot.symm) degreeMember
  · exact (finalSpec.outside_restored wire degreeMember notLegal).trans
      (degreeSpec.outside_degree_restored wire degreeMember).symm

/--
legality phaseをreachable部分空間上の独立な一意仕様へ包装したcompiled leaf。
less-than等への内部child辺はこのcontractでは主張しない。
-/
noncomputable def verifiedXorDelimiterAcceptanceIntoLegalAndUncomputeWorkCleanComponent
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p) :
    CleanComponent (reversibleGatePermutation
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) where
  circuit := xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit p inputWires
  reference := uniqueSpecificationReference (DelimiterAcceptanceLegalFlagXorSpec p)
  inputCondition := DelimiterAcceptanceReachableInput p inputWires configuration
  outputCondition := fun _ => True
  restoration := DelimiterAcceptanceLegalFlagXorSpec p
  runBasis_correct := by
    intro input reachable
    let actual := (xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit p inputWires).runBasis
      reversibleGatePermutation input
    have actualSpec := xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit_componentSpec p inputWires
      layout configuration input reachable
    have uniqueOutput : ∃! output, DelimiterAcceptanceLegalFlagXorSpec p input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    exact uniqueOutput.unique actualSpec
      (uniqueSpecificationReference_spec uniqueOutput)
  outputCondition_correct := by simp
  restoration_correct := by
    intro input reachable
    let actual := (xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit p inputWires).runBasis
      reversibleGatePermutation input
    have actualSpec := xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit_componentSpec p inputWires
      layout configuration input reachable
    have uniqueOutput : ∃! output, DelimiterAcceptanceLegalFlagXorSpec p input output :=
      ⟨actual, actualSpec, fun other otherSpec => otherSpec.unique actualSpec⟩
    exact uniqueSpecificationReference_spec uniqueOutput

/-- degree子とlegality子の解析参照を合成すると最終compact仕様を満たす。 -/
theorem delimiterLegalityAndDegreeOneHotChildren_compose_spec
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : CompactDecoderCleanInput p inputWires configuration input) :
    let degree := verifiedXorDelimiterDegreeOneHotIntoTargetsCleanComponent p inputWires layout configuration
    let legality := verifiedXorDelimiterAcceptanceIntoLegalAndUncomputeWorkCleanComponent p inputWires layout
      configuration
    DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration input
      (legality.reference (degree.reference input)) := by
  dsimp only
  let degree := verifiedXorDelimiterDegreeOneHotIntoTargetsCleanComponent p inputWires layout configuration
  let legality := verifiedXorDelimiterAcceptanceIntoLegalAndUncomputeWorkCleanComponent p inputWires layout
    configuration
  have degreeSpec : DelimiterDegreeOneHotXorSpec p configuration input
      (degree.reference input) := degree.restoration_correct input clean
  have legalityClean : legality.inputCondition (degree.reference input) :=
    ⟨input, clean, rfl⟩
  have legalitySpec : DelimiterAcceptanceLegalFlagXorSpec p (degree.reference input)
      (legality.reference (degree.reference input)) :=
    legality.restoration_correct (degree.reference input) legalityClean
  let output := legality.reference (degree.reference input)
  have legalOutsideSupport := oracleLegal_not_mem_decoderLegalitySupportFor
    p inputWires layout
  have legalNotDegree : oracleLegalWire p ∉ oracleDegreeWires p := by
    intro member
    exact legalOutsideSupport (by
      simp [decoderLegalitySupportFor, member])
  have legalNotCompare : oracleLegalWire p ∉ oracleCompareWorkWires p := by
    intro member
    exact legalOutsideSupport (by
      simp [decoderLegalitySupportFor, member])
  have legalNotAnd : oracleLegalWire p ∉ oracleAndWorkWires p := by
    intro member
    exact legalOutsideSupport (by
      simp [decoderLegalitySupportFor, member])
  refine {
    input_preserved := ?_
    degree_one_hot := ?_
    legal_true := legalitySpec.legal_true
    compare_zero := ?_
    and_zero := ?_
    outside_restored := ?_ }
  · calc
      readWires inputWires output = readWires inputWires input := by
        apply List.map_congr_left
        intro wire member
        change legality.reference (degree.reference input) wire = input wire
        rw [legalitySpec.outside_legal_restored wire (by
          intro equal
          subst wire
          exact layout.legal_fresh member)]
        exact degreeSpec.outside_degree_restored wire (by
          intro degreeMember
          exact List.disjoint_left.mp layout.disjoint_degree member degreeMember)
      _ = registerBitList (delimiterEncoding configuration) := clean.input_bits
  · calc
      readWires (oracleDegreeWires p) output =
          readWires (oracleDegreeWires p) (degree.reference input) := by
        apply List.map_congr_left
        intro wire member
        exact legalitySpec.outside_legal_restored wire (by
          intro equal
          subst wire
          exact legalNotDegree member)
      _ = degreeOneHotFrom p.K configuration.1.card 0 :=
        degreeSpec.degree_one_hot
  · intro wire member
    change legality.reference (degree.reference input) wire = false
    rw [legalitySpec.outside_legal_restored wire (by
      intro equal
      subst wire
      exact legalNotCompare member)]
    rw [degreeSpec.outside_degree_restored wire (by
      intro degreeMember
      exact List.disjoint_left.mp (oracleDegreeWires_disjoint_compareWork p)
        degreeMember member)]
    exact pointwise_false_of_readWires_eq_replicate
      (oracleCompareWorkWires p) input clean.compare_zero wire member
  · intro wire member
    change legality.reference (degree.reference input) wire = false
    rw [legalitySpec.outside_legal_restored wire (by
      intro equal
      subst wire
      exact legalNotAnd member)]
    rw [degreeSpec.outside_degree_restored wire (by
      intro degreeMember
      exact List.disjoint_left.mp (oracleDegreeWires_disjoint_andWork p)
        degreeMember member)]
    exact clean.and_zero wire member
  · intro wire outsideDegree notLegal
    change legality.reference (degree.reference input) wire = input wire
    exact (legalitySpec.outside_legal_restored wire notLegal).trans
      (degreeSpec.outside_degree_restored wire outsideDegree)

/--
degree decode子とlegality phase子の公開契約だけを逐次合成したcompact decoder component。
-/
noncomputable def verifiedXorDelimiterLegalityAndDegreeOneHotIntoTargetsCleanComponent
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
    intro input clean
    let degree := verifiedXorDelimiterDegreeOneHotIntoTargetsCleanComponent p inputWires layout configuration
    let legality := verifiedXorDelimiterAcceptanceIntoLegalAndUncomputeWorkCleanComponent p inputWires layout
      configuration
    have degreeEq := degree.runBasis_correct input clean
    have legalityClean : legality.inputCondition (degree.reference input) :=
      ⟨input, clean, rfl⟩
    have legalityEq := legality.runBasis_correct (degree.reference input) legalityClean
    have degreeEq' :
        (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
          (oracleDegreeWires p)).runBasis reversibleGatePermutation input =
          degree.reference input := by
      simpa [degree, verifiedXorDelimiterDegreeOneHotIntoTargetsCleanComponent] using degreeEq
    have legalityEq' :
        (xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit p inputWires).runBasis
            reversibleGatePermutation (degree.reference input) =
          legality.reference (degree.reference input) := by
      simpa [legality, verifiedXorDelimiterAcceptanceIntoLegalAndUncomputeWorkCleanComponent] using legalityEq
    have composedSpec := delimiterLegalityAndDegreeOneHotChildren_compose_spec p inputWires layout
      configuration input clean
    have uniqueOutput : ∃! output,
        DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration input output :=
      ⟨legality.reference (degree.reference input), composedSpec,
        fun other otherSpec => otherSpec.unique composedSpec⟩
    change (xorDelimiterAcceptanceIntoLegalAndUncomputeWorkCircuit p inputWires).runBasis
      reversibleGatePermutation
        ((xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
          (oracleDegreeWires p)).runBasis reversibleGatePermutation input) = _
    rw [degreeEq', legalityEq']
    exact uniqueOutput.unique composedSpec
      (uniqueSpecificationReference_spec uniqueOutput)
  outputCondition_correct := by simp
  restoration_correct := by
    intro input clean
    let degree := verifiedXorDelimiterDegreeOneHotIntoTargetsCleanComponent p inputWires layout configuration
    let legality := verifiedXorDelimiterAcceptanceIntoLegalAndUncomputeWorkCleanComponent p inputWires layout
      configuration
    have composedSpec := delimiterLegalityAndDegreeOneHotChildren_compose_spec p inputWires layout
      configuration input clean
    have uniqueOutput : ∃! output,
        DelimiterLegalityAndDegreeOneHotXorSpec p inputWires configuration input output :=
      ⟨legality.reference (degree.reference input), composedSpec,
        fun other otherSpec => otherSpec.unique composedSpec⟩
    exact uniqueSpecificationReference_spec uniqueOutput

/-- compact decoder componentの回路は既存正本ASTと定義的に一致する。 -/
@[simp] theorem verifiedXorDelimiterLegalityAndDegreeOneHotIntoTargetsCleanComponent_circuit
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (configuration : QConfiguration p) :
    (verifiedXorDelimiterLegalityAndDegreeOneHotIntoTargetsCleanComponent p inputWires layout configuration).circuit =
      xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires := by
  rfl

end ReversibleCircuit

end ProbabilityGeneratorQProof
