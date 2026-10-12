import QLean.Generator.Implementation.QOraclePersistentCorrectness

/-!
# membership回路の一般基底作用

各slotの等値判定を行列へ展開せず、可逆回路の基底作用として証明する。
この局所定理をslot列へ帰納合成し、column/row event branchのmembership判定へ接続する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- membership 回路へ渡す word register の型安全な配置条件。 -/
structure MembershipInputLayout (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth)) : Prop where
  /-- register は compact decoder の入力条件を満たす。 -/
  decoder : CompactDecoderInputLayout p register
  /-- register は membership の等値 flag slice と交わらない。 -/
  disjoint_membershipEqual : register.Disjoint
    ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).membershipEqual).wireList :
      List (Wire p.ancillaWidth p.systemWidth))
  /-- registerはmembershipのgood flag sliceと交わらない。 -/
  disjoint_membershipGood : register.Disjoint
    ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).membershipGood).wireList :
      List (Wire p.ancillaWidth p.systemWidth))
  /-- registerはpresent-other flag sliceと交わらない。 -/
  disjoint_presentOther : register.Disjoint
    ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).presentOther).wireList :
      List (Wire p.ancillaWidth p.systemWidth))

/-- 物理 system register は membership 回路の正しい入力配置である。 -/
theorem systemWires_membershipInputLayout (p : QParameters) :
    MembershipInputLayout p (systemWires p) where
  decoder := systemWires_compactDecoderInputLayout p
  disjoint_membershipEqual := by
    let equalSlice := QLayout.oracleSlice
      (OracleWorkLayout.canonical p).membershipEqual
    simpa [systemWires, QLayout.systemWire, equalSlice] using
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) equalSlice)
  disjoint_membershipGood := by
    let goodSlice := QLayout.oracleSlice
      (OracleWorkLayout.canonical p).membershipGood
    simpa [systemWires, QLayout.systemWire, goodSlice] using
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) goodSlice)
  disjoint_presentOther := by
    let otherSlice := QLayout.oracleSlice
      (OracleWorkLayout.canonical p).presentOther
    simpa [systemWires, QLayout.systemWire, otherSlice] using
      (RegisterSlice.systemWires_disjoint_wireList
        (systemWidth := p.systemWidth) otherSlice)

/-- column-key register は membership 回路の正しい入力配置である。 -/
theorem columnKeyWires_membershipInputLayout (p : QParameters) :
    MembershipInputLayout p (columnKeyWires p) where
  decoder := columnKeyWires_compactDecoderInputLayout p
  disjoint_membershipEqual := by
    simpa using columnKeyWires_disjoint_oracleSlice p
      (OracleWorkLayout.canonical p).membershipEqual
  disjoint_membershipGood := by
    simpa using columnKeyWires_disjoint_oracleSlice p
      (OracleWorkLayout.canonical p).membershipGood
  disjoint_presentOther := by
    simpa using columnKeyWires_disjoint_oracleSlice p
      (OracleWorkLayout.canonical p).presentOther

/-- `systemWidth` bit register の各 `Fin K` word は常に `wordWidth` bit である。 -/
@[simp] theorem registerWordAt_length
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (length_eq : register.length = p.systemWidth) (slot : Fin p.K) :
    (registerWordAt p register slot).length = p.wordWidth := by
  have enough : slot.val * p.wordWidth + p.wordWidth ≤ register.length := by
    rw [length_eq]
    calc
      slot.val * p.wordWidth + p.wordWidth =
          (slot.val + 1) * p.wordWidth := by rw [Nat.succ_mul]
      _ ≤ p.K * p.wordWidth :=
        Nat.mul_le_mul_right p.wordWidth (Nat.succ_le_of_lt slot.isLt)
      _ = p.wordWidth * p.K := Nat.mul_comm _ _
      _ ≤ p.wordWidth * p.K + 1 := Nat.le_succ _
      _ = p.systemWidth := rfl
  simp only [registerWordAt, List.length_take, List.length_drop]
  rw [Nat.min_eq_left]
  exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using enough)

/-- register から切り出した word の wire は元の register に属する。 -/
theorem mem_register_of_mem_registerWordAt
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ registerWordAt p register slot) : wire ∈ register := by
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

/-- membership equal wireはslot添字について単射である。 -/
theorem membershipEqualWireAt_injective (p : QParameters) :
    Function.Injective (membershipEqualWireAt p) := by
  intro left right equal
  let slice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipEqual
  apply slice.ancillaWire_injective
  simpa [membershipEqualWireAt, slice] using equal

/-- membership good wireはslot添字について単射である。 -/
theorem membershipGoodWireAt_injective (p : QParameters) :
    Function.Injective (membershipGoodWireAt p) := by
  intro left right equal
  let slice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipGood
  apply slice.ancillaWire_injective
  simpa [membershipGoodWireAt, slice] using equal

/-- 任意slotのequal wireと任意slotのgood wireは異なる。 -/
theorem membershipEqualWireAt_ne_goodWireAt
    (p : QParameters) (equalSlot goodSlot : Fin p.K) :
    membershipEqualWireAt p equalSlot ≠ membershipGoodWireAt p goodSlot := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [membershipEqualWireAt, membershipGoodWireAt, QLayout.oracleSlice,
    RegisterSlice.compose, OracleWorkLayout.canonical,
    QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
  omega

/-- 任意slotのequal wireはpresent-other wireと異なる。 -/
theorem membershipEqualWireAt_ne_presentOther
    (p : QParameters) (slot : Fin p.K) :
    membershipEqualWireAt p slot ≠ oraclePresentOtherWire p := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [membershipEqualWireAt, oraclePresentOtherWire, oracleSingletonWire,
    QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
    QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
  omega

/-- 任意slotのgood wireはpresent-other wireと異なる。 -/
theorem membershipGoodWireAt_ne_presentOther
    (p : QParameters) (slot : Fin p.K) :
    membershipGoodWireAt p slot ≠ oraclePresentOtherWire p := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [membershipGoodWireAt, oraclePresentOtherWire, oracleSingletonWire,
    QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
    QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
  omega

/-- present wireは任意slotのmembership equal wireと異なる。 -/
theorem oraclePresentWireAt_ne_membershipEqual
    (p : QParameters) (presentSlot equalSlot : Fin p.K) :
    oraclePresentWireAt p presentSlot ≠ membershipEqualWireAt p equalSlot := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [oraclePresentWireAt, membershipEqualWireAt, QLayout.oracleSlice,
    RegisterSlice.compose, OracleWorkLayout.canonical,
    QParameters.presentWidth, QParameters.membershipEqWidth] at numbers
  omega

/-- present wireは任意slotのmembership good wireと異なる。 -/
theorem oraclePresentWireAt_ne_membershipGood
    (p : QParameters) (presentSlot goodSlot : Fin p.K) :
    oraclePresentWireAt p presentSlot ≠ membershipGoodWireAt p goodSlot := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [oraclePresentWireAt, membershipGoodWireAt, QLayout.oracleSlice,
    RegisterSlice.compose, OracleWorkLayout.canonical,
    QParameters.presentWidth, QParameters.membershipEqWidth,
    QParameters.membershipGoodWidth] at numbers
  omega

/-- present wireはpresent-other wireと異なる。 -/
theorem oraclePresentWireAt_ne_presentOther
    (p : QParameters) (slot : Fin p.K) :
    oraclePresentWireAt p slot ≠ oraclePresentOtherWire p := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [oraclePresentWireAt, oraclePresentOtherWire, oracleSingletonWire,
    QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
    QParameters.presentWidth, QParameters.membershipEqWidth,
    QParameters.membershipGoodWidth] at numbers
  omega

/-- membershipの1 slot回路に必要な、wire長と相異性をまとめた配置条件。 -/
structure MembershipSlotLayout
    {ancillaQubits systemQubits : Nat}
    (moved word equalWork andScratch :
      List (Wire ancillaQubits systemQubits))
    (presentFlag equalFlag goodFlag presentOtherFlag :
      Wire ancillaQubits systemQubits) : Prop where
  /-- 左wordと等値workの長さは等しい。 -/
  moved_length : moved.length = equalWork.length
  /-- 右wordと等値workの長さは等しい。 -/
  word_length : word.length = equalWork.length
  /-- moved wordと等値workは交わらない。 -/
  moved_disjoint_equalWork : moved.Disjoint equalWork
  /-- 比較対象wordと等値workは交わらない。 -/
  word_disjoint_equalWork : word.Disjoint equalWork
  /-- 等値workとAND scratchは交わらない。 -/
  equalWork_disjoint_scratch : equalWork.Disjoint andScratch
  /-- 等値workには重複がない。 -/
  equalWork_nodup : equalWork.Nodup
  /-- 等値判定の多重制御配置は重複を持たない。 -/
  equality_layout : (equalWork ++ andScratch ++ [equalFlag]).Nodup
  /-- 等値flagはmoved wordに含まれない。 -/
  equal_absent_moved : equalFlag ∉ moved
  /-- 等値flagは比較対象wordに含まれない。 -/
  equal_absent_word : equalFlag ∉ word
  /-- 等値判定に十分なscratchがある。 -/
  enough_scratch : equalWork.length ≤ andScratch.length + 1
  /-- present flagと等値flagは異なる。 -/
  present_ne_equal : presentFlag ≠ equalFlag
  /-- present flagとgood flagは異なる。 -/
  present_ne_good : presentFlag ≠ goodFlag
  /-- 等値flagとgood flagは異なる。 -/
  equal_ne_good : equalFlag ≠ goodFlag
  /-- present flagとpresent-other flagは異なる。 -/
  present_ne_other : presentFlag ≠ presentOtherFlag
  /-- 等値flagとpresent-other flagは異なる。 -/
  equal_ne_other : equalFlag ≠ presentOtherFlag
  /-- good flagとpresent-other flagは異なる。 -/
  good_ne_other : goodFlag ≠ presentOtherFlag

/-- 正本oracle layoutから任意のmembership slotの局所配置条件が得られる。 -/
theorem membershipSlotLayout_canonical
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register) (slot : Fin p.K) :
    MembershipSlotLayout (oracleMovedWires p) (registerWordAt p register slot)
      (oracleCompareWorkWires p) (decoderAndScratchWires p)
      (oraclePresentWireAt p slot) (membershipEqualWireAt p slot)
      (membershipGoodWireAt p slot) (oraclePresentOtherWire p) := by
  let movedSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).moved
  let equalSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipEqual
  let goodSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipGood
  let presentSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).present
  let otherSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).presentOther
  let compareSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).compareWork
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have movedCompare :
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [movedSlice, compareSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have movedEqual :
      (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (equalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [movedSlice, equalSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have equalCompare :
      (equalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [equalSlice, compareSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have equalAnd :
      (equalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [equalSlice, andSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have presentOtherDisjoint :
      (presentSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (otherSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [presentSlice, otherSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have equalOtherDisjoint :
      (equalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (otherSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [equalSlice, otherSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have equalGoodDisjoint :
      (equalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [equalSlice, goodSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have goodOtherDisjoint :
      (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (otherSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [goodSlice, otherSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have equalMember : membershipEqualWireAt p slot ∈
      (equalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [membershipEqualWireAt, equalSlice, RegisterSlice.wireList]
  have compareScratchNodup :
      (oracleCompareWorkWires p ++ decoderAndScratchWires p).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa [oracleCompareWorkWires, RegisterSlice.wireList, compareSlice] using
        (RegisterSlice.wireList_nodup
          (systemWidth := p.systemWidth) compareSlice)
    · exact List.Nodup.sublist (by simp) (decoderAndScratchFlags_nodup p)
    · intro compareWire compareMember scratchWire scratchMember equal
      subst scratchWire
      exact (List.disjoint_left.mp
        (oracleCompareWorkWires_disjoint_andWork p) compareMember)
        (decoderComparisonAndMember p
          (List.mem_append.mpr (Or.inl scratchMember)))
  refine {
    moved_length := by
      simp [oracleMovedWires, oracleCompareWorkWires,
        QParameters.movedWidth]
    word_length := by
      simpa using registerWordAt_length p register
        inputLayout.decoder.length_eq slot
    moved_disjoint_equalWork := by
      simpa [oracleMovedWires, oracleCompareWorkWires,
        RegisterSlice.wireList, movedSlice, compareSlice] using movedCompare
    word_disjoint_equalWork := by
      rw [List.disjoint_left]
      intro wire wordMember compareMember
      exact (List.disjoint_left.mp inputLayout.decoder.disjoint_compare
        (mem_register_of_mem_registerWordAt p register slot wordMember))
        compareMember
    equalWork_disjoint_scratch := by
      rw [List.disjoint_left]
      intro wire compareMember scratchMember
      exact (List.disjoint_left.mp
        (oracleCompareWorkWires_disjoint_andWork p) compareMember)
        (decoderComparisonAndMember p
          (List.mem_append.mpr (Or.inl scratchMember)))
    equalWork_nodup := by
      simpa [oracleCompareWorkWires, RegisterSlice.wireList, compareSlice] using
        (RegisterSlice.wireList_nodup
          (systemWidth := p.systemWidth) compareSlice)
    equality_layout := by
      apply List.nodup_append.mpr
      refine ⟨compareScratchNodup, by simp, ?_⟩
      intro wire member otherWire equalFlagMember equal
      simp only [List.mem_singleton] at equalFlagMember
      subst otherWire
      subst wire
      rcases List.mem_append.mp member with compareMember | scratchMember
      · have compareFull : membershipEqualWireAt p slot ∈
            (compareSlice.wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
          simpa [oracleCompareWorkWires, RegisterSlice.wireList,
            compareSlice] using compareMember
        exact (List.disjoint_left.mp equalCompare equalMember) compareFull
      · exact (List.disjoint_left.mp equalAnd equalMember)
          (by
            have memberAnd := decoderComparisonAndMember p
              (List.mem_append.mpr (Or.inl scratchMember))
            simpa [oracleAndWorkWires, RegisterSlice.wireList, andSlice] using
              memberAnd)
    equal_absent_moved := by
      intro member
      have movedMember : membershipEqualWireAt p slot ∈
          (movedSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
        simpa [oracleMovedWires, RegisterSlice.wireList, movedSlice] using member
      exact (List.disjoint_left.mp movedEqual movedMember) equalMember
    equal_absent_word := by
      intro member
      exact (List.disjoint_left.mp inputLayout.disjoint_membershipEqual
        (mem_register_of_mem_registerWordAt p register slot member)) equalMember
    enough_scratch := by
      simpa using le_trans (decoderAndScratchWires_wordWidth_le p)
        (Nat.le_succ _)
    present_ne_equal := by
      intro equal
      have numbers := congrArg wireNumber equal
      simp [oraclePresentWireAt, membershipEqualWireAt,
        QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical, QParameters.presentWidth,
        QParameters.membershipEqWidth] at numbers
      omega
    present_ne_good := by
      intro equal
      have numbers := congrArg wireNumber equal
      simp [oraclePresentWireAt, membershipGoodWireAt,
        QLayout.oracleSlice, RegisterSlice.compose,
        OracleWorkLayout.canonical, QParameters.presentWidth,
        QParameters.membershipGoodWidth] at numbers
      omega
    equal_ne_good := by
      intro equal
      have goodMember : membershipGoodWireAt p slot ∈
          (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [membershipGoodWireAt, goodSlice, RegisterSlice.wireList]
      rw [equal] at equalMember
      exact (List.disjoint_left.mp equalGoodDisjoint equalMember) goodMember
    present_ne_other := by
      intro equal
      have presentMember : oraclePresentWireAt p slot ∈
          (presentSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oraclePresentWireAt, presentSlice, RegisterSlice.wireList]
      have otherMember : oraclePresentOtherWire p ∈
          (otherSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oraclePresentOtherWire, oracleSingletonWire, otherSlice,
          RegisterSlice.wireList]
      rw [equal] at presentMember
      exact (List.disjoint_left.mp presentOtherDisjoint presentMember) otherMember
    equal_ne_other := by
      intro equal
      have otherMember : oraclePresentOtherWire p ∈
          (otherSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oraclePresentOtherWire, oracleSingletonWire, otherSlice,
          RegisterSlice.wireList]
      rw [equal] at equalMember
      exact (List.disjoint_left.mp equalOtherDisjoint equalMember) otherMember
    good_ne_other := by
      intro equal
      have goodMember : membershipGoodWireAt p slot ∈
          (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [membershipGoodWireAt, goodSlice, RegisterSlice.wireList]
      have otherMember : oraclePresentOtherWire p ∈
          (otherSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oraclePresentOtherWire, oracleSingletonWire, otherSlice,
          RegisterSlice.wireList]
      rw [equal] at goodMember
      exact (List.disjoint_left.mp goodOtherDisjoint goodMember) otherMember }

/-- membershipの1 slot回路に必要なclean work条件。 -/
structure MembershipSlotClean
    {ancillaQubits systemQubits : Nat}
    (equalWork andScratch : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits) : Prop where
  /-- 等値workは全0である。 -/
  equalWork_zero : readWires equalWork input =
    List.replicate equalWork.length false
  /-- AND scratchは全0である。 -/
  scratch_zero : ∀ wire ∈ andScratch, input wire = false

/-- membershipの1 slot回路を純粋な四つの基底作用へ厳密に展開する。 -/
theorem runBasis_membershipSlotCircuit
    {ancillaQubits systemQubits : Nat}
    (moved word equalWork andScratch :
      List (Wire ancillaQubits systemQubits))
    (presentFlag equalFlag goodFlag presentOtherFlag :
      Wire ancillaQubits systemQubits)
    (recordPresentOther : Bool)
    (input : JointBasis ancillaQubits systemQubits)
    (layout : MembershipSlotLayout moved word equalWork andScratch
      presentFlag equalFlag goodFlag presentOtherFlag)
    (clean : MembershipSlotClean equalWork andScratch input) :
    let afterEqual :=
      if decide (readWires moved input = readWires word input) then
        xBasisAction equalFlag input
      else input
    let afterGood := xBasisAction goodFlag afterEqual
    let afterRemove :=
      toffoliBasisAction presentFlag equalFlag goodFlag afterGood
    let expected := if recordPresentOther then
      toffoliBasisAction presentFlag equalFlag presentOtherFlag afterRemove
    else afterRemove
    (membershipSlotCircuit moved word equalWork andScratch presentFlag equalFlag
      goodFlag presentOtherFlag recordPresentOther).runBasis
        reversibleGatePermutation input = expected := by
  dsimp only
  simp only [membershipSlotCircuit, runBasis_seq]
  rw [runBasis_xorEqualityIntoTargetCircuit moved word equalWork andScratch equalFlag input
    layout.moved_length layout.word_length layout.moved_disjoint_equalWork
    layout.word_disjoint_equalWork layout.equalWork_disjoint_scratch
    layout.equalWork_nodup layout.equality_layout layout.equal_absent_moved
    layout.equal_absent_word clean.equalWork_zero clean.scratch_zero
    layout.enough_scratch]
  simp only [ProbabilityGeneratorQProof.Circuit.runBasis]
  rw [runBasis_x]
  rw [runBasis_core_safeToffoli presentFlag equalFlag goodFlag
    layout.present_ne_equal layout.present_ne_good layout.equal_ne_good]
  split
  · rw [runBasis_core_safeToffoli presentFlag equalFlag presentOtherFlag
      layout.present_ne_equal layout.present_ne_other layout.equal_ne_other]
  · rfl

/-- membershipの1 slot回路は、3本の出力flag以外のwireを変更しない。 -/
theorem runBasis_membershipSlotCircuit_other
    {ancillaQubits systemQubits : Nat}
    (moved word equalWork andScratch :
      List (Wire ancillaQubits systemQubits))
    (presentFlag equalFlag goodFlag presentOtherFlag :
      Wire ancillaQubits systemQubits)
    (recordPresentOther : Bool)
    (input : JointBasis ancillaQubits systemQubits)
    (layout : MembershipSlotLayout moved word equalWork andScratch
      presentFlag equalFlag goodFlag presentOtherFlag)
    (clean : MembershipSlotClean equalWork andScratch input)
    (wire : Wire ancillaQubits systemQubits)
    (wire_ne_equal : wire ≠ equalFlag)
    (wire_ne_good : wire ≠ goodFlag)
    (wire_ne_other : wire ≠ presentOtherFlag) :
    (membershipSlotCircuit moved word equalWork andScratch presentFlag equalFlag
      goodFlag presentOtherFlag recordPresentOther).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [runBasis_membershipSlotCircuit moved word equalWork andScratch presentFlag
    equalFlag goodFlag presentOtherFlag recordPresentOther input layout clean]
  cases recordPresentOther <;>
    by_cases equalWords : readWires moved input = readWires word input <;>
    simp [equalWords, xBasisAction, toffoliBasisAction, wire_ne_equal,
      wire_ne_good, wire_ne_other]

/-- 正本の1 slot membership回路は比較workとAND scratchをcleanなまま保つ。 -/
theorem membershipSlotCircuit_clean_canonical
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register) (slot : Fin p.K)
    (recordPresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input) :
    MembershipSlotClean (oracleCompareWorkWires p) (decoderAndScratchWires p)
      ((membershipSlotCircuit (oracleMovedWires p)
        (registerWordAt p register slot) (oracleCompareWorkWires p)
        (decoderAndScratchWires p) (oraclePresentWireAt p slot)
        (membershipEqualWireAt p slot) (membershipGoodWireAt p slot)
        (oraclePresentOtherWire p) recordPresentOther).runBasis
          reversibleGatePermutation input) := by
  let equalSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipEqual
  let goodSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipGood
  let otherSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).presentOther
  let compareSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).compareWork
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have equalCompare :
      (equalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [equalSlice, compareSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have goodCompare :
      (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [goodSlice, compareSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have otherCompare :
      (otherSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [otherSlice, compareSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have equalAnd :
      (equalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [equalSlice, andSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have goodAnd :
      (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [goodSlice, andSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have otherAnd :
      (otherSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [otherSlice, andSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have equalMember : membershipEqualWireAt p slot ∈
      (equalSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [membershipEqualWireAt, equalSlice, RegisterSlice.wireList]
  have goodMember : membershipGoodWireAt p slot ∈
      (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [membershipGoodWireAt, goodSlice, RegisterSlice.wireList]
  have otherMember : oraclePresentOtherWire p ∈
      (otherSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [oraclePresentOtherWire, oracleSingletonWire, otherSlice,
      RegisterSlice.wireList]
  let circuit := membershipSlotCircuit (oracleMovedWires p)
    (registerWordAt p register slot) (oracleCompareWorkWires p)
    (decoderAndScratchWires p) (oraclePresentWireAt p slot)
    (membershipEqualWireAt p slot) (membershipGoodWireAt p slot)
    (oraclePresentOtherWire p) recordPresentOther
  have preserveCompare : ∀ wire ∈ oracleCompareWorkWires p,
      circuit.runBasis reversibleGatePermutation input wire = input wire := by
    intro wire member
    have memberFull : wire ∈
        (compareSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oracleCompareWorkWires, compareSlice, RegisterSlice.wireList] using
        member
    apply runBasis_membershipSlotCircuit_other
      (oracleMovedWires p) (registerWordAt p register slot)
      (oracleCompareWorkWires p) (decoderAndScratchWires p)
      (oraclePresentWireAt p slot) (membershipEqualWireAt p slot)
      (membershipGoodWireAt p slot) (oraclePresentOtherWire p)
      recordPresentOther input (membershipSlotLayout_canonical p register
        inputLayout slot) clean
    · intro equal
      rw [equal] at memberFull
      exact (List.disjoint_left.mp equalCompare equalMember) memberFull
    · intro equal
      rw [equal] at memberFull
      exact (List.disjoint_left.mp goodCompare goodMember) memberFull
    · intro equal
      rw [equal] at memberFull
      exact (List.disjoint_left.mp otherCompare otherMember) memberFull
  have preserveScratch : ∀ wire ∈ decoderAndScratchWires p,
      circuit.runBasis reversibleGatePermutation input wire = input wire := by
    intro wire member
    have andMember := decoderComparisonAndMember p
      (List.mem_append.mpr (Or.inl member))
    have memberFull : wire ∈
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oracleAndWorkWires, andSlice, RegisterSlice.wireList] using andMember
    apply runBasis_membershipSlotCircuit_other
      (oracleMovedWires p) (registerWordAt p register slot)
      (oracleCompareWorkWires p) (decoderAndScratchWires p)
      (oraclePresentWireAt p slot) (membershipEqualWireAt p slot)
      (membershipGoodWireAt p slot) (oraclePresentOtherWire p)
      recordPresentOther input (membershipSlotLayout_canonical p register
        inputLayout slot) clean
    · intro equal
      rw [equal] at memberFull
      exact (List.disjoint_left.mp equalAnd equalMember) memberFull
    · intro equal
      rw [equal] at memberFull
      exact (List.disjoint_left.mp goodAnd goodMember) memberFull
    · intro equal
      rw [equal] at memberFull
      exact (List.disjoint_left.mp otherAnd otherMember) memberFull
  refine {
    equalWork_zero := ?_
    scratch_zero := ?_ }
  · calc
      readWires (oracleCompareWorkWires p)
          (circuit.runBasis reversibleGatePermutation input) =
          readWires (oracleCompareWorkWires p) input := by
        apply List.map_congr_left
        exact preserveCompare
      _ = List.replicate (oracleCompareWorkWires p).length false :=
        clean.equalWork_zero
  · intro wire member
    rw [preserveScratch wire member]
    exact clean.scratch_zero wire member

/-- 1 slot membership回路の、行列を展開しない純粋な基底作用参照関数。 -/
def SiteSlotMatchAndGoodFlagAtIndexXorSpec
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let afterEqual :=
    if decide (readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input) then
      xBasisAction (membershipEqualWireAt p slot) input
    else input
  let afterGood := xBasisAction (membershipGoodWireAt p slot) afterEqual
  let afterRemove := toffoliBasisAction (oraclePresentWireAt p slot)
    (membershipEqualWireAt p slot) (membershipGoodWireAt p slot) afterGood
  if includePresentOther && slot != selectedSlot then
    toffoliBasisAction (oraclePresentWireAt p slot)
      (membershipEqualWireAt p slot) (oraclePresentOtherWire p) afterRemove
  else afterRemove

/-- 1 slotが「presentかつmoved wordと一致する」という数学的なmembership条件。 -/
def membershipSlotMatches
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (slot : Fin p.K) (input : JointBasis p.ancillaWidth p.systemWidth) : Bool :=
  input (oraclePresentWireAt p slot) &&
    decide (readWires (oracleMovedWires p) input =
      readWires (registerWordAt p register slot) input)

/-- present-otherへ記録すべき、選択slot以外の有効一致条件。 -/
def membershipOtherMatch
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (slot : Fin p.K) (input : JointBasis p.ancillaWidth p.systemWidth) : Bool :=
  includePresentOther && slot != selectedSlot &&
    membershipSlotMatches p register slot input

/-- presentな二つのslotが同じwordを持たないという、合法配置から導く中間不変条件。 -/
def DistinctPresentWords
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ left right : Fin p.K,
    input (oraclePresentWireAt p left) = true →
    input (oraclePresentWireAt p right) = true →
    readWires (registerWordAt p register left) input =
      readWires (registerWordAt p register right) input →
    left = right

/-- 永続decoderは合法clean入力のdelimiter registerを後続回路まで厳密に保存する。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_input_preserved_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input)
    (rowMode : Bool) :
    readWires inputWires
        ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
          reversibleGatePermutation input) =
      registerBitList (delimiterEncoding configuration) := by
  let degree := oracleDegreeWires p
  let present := oraclePresentWires p
  let condition := oracleDegreeConditionWire p
  let one := oracleOneWire p
  let sources := if rowMode then degree.take (p.K - 1) else degree.drop 1
  let decoded := (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
    reversibleGatePermutation input
  let presented := (slotPresenceCircuit degree present).runBasis
    reversibleGatePermutation decoded
  let conditioned := (xorSourceParityIntoTargetCircuit sources condition).runBasis
    reversibleGatePermutation presented
  have outputEq :
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
          reversibleGatePermutation input = xBasisAction one conditioned := by
    simp only [computeSharedDecoderPresenceParityAndOneFlagsCircuit, runBasis_seq, runBasis_x]
    rfl
  have decodedBits : readWires inputWires decoded =
      registerBitList (delimiterEncoding configuration) := by
    simpa [decoded] using
      xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_input_preserved_of_clean p inputWires
        layout.decoder configuration input clean.decoder
  have presentedBits : readWires inputWires presented = readWires inputWires decoded := by
    apply List.map_congr_left
    intro wire member
    apply runBasis_xorDegreeSuffixParityIntoSlotPresenceCircuit_outside degree present 0 wire decoded
      (by simpa [degree, present] using oracleDegreeWires_disjoint_presentWires p)
    exact fun presentMember =>
      (List.disjoint_left.mp layout.disjoint_present member) presentMember
  have conditionAbsentSources : condition ∉ sources := by
    simpa [condition, sources, degree] using
      oracleDegreeConditionWire_not_mem_degreeConditionSources p rowMode
  have conditionAbsentInput : condition ∉ inputWires := by
    intro member
    exact (List.disjoint_left.mp layout.disjoint_special member)
      (by simpa [condition] using oracleDegreeConditionWire_mem_special p)
  have conditionedBits : readWires inputWires conditioned =
      readWires inputWires presented := by
    exact readWires_xorSourceParityIntoTargetCircuit_other sources condition inputWires presented
      conditionAbsentSources conditionAbsentInput
  have oneAbsentInput : one ∉ inputWires := by
    intro member
    exact (List.disjoint_left.mp layout.disjoint_special member)
      (by simpa [one] using oracleOneWire_mem_special p)
  rw [outputEq]
  rw [readWires_xBasisAction_other one inputWires conditioned oneAbsentInput]
  rw [conditionedBits, presentedBits]
  exact decodedBits

/-- presence参照列の任意添字は、範囲内なら`start + index < particleCount`を表す。 -/
theorem presenceBitsFrom_getD
    (particleCount : Nat) :
    ∀ (count start index : Nat),
      (presenceBitsFrom count particleCount start)[index]?.getD false =
        if index < count then decide (start + index < particleCount) else false
  | 0, _, _ => by simp [presenceBitsFrom]
  | count + 1, start, 0 => by simp [presenceBitsFrom]
  | count + 1, start, index + 1 => by
      simp only [presenceBitsFrom, List.getElem?_cons_succ]
      rw [presenceBitsFrom_getD particleCount count (start + 1) index]
      by_cases inRange : index < count
      · simp [inRange]
        omega
      · have outside : ¬index + 1 < count + 1 := by omega
        simp [inRange, outside]

/-- 永続decoder後の各present bitは、slotが配置粒子数未満であることと一致する。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_present_value_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input)
    (rowMode : Bool) (slot : Fin p.K) :
    let output := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
      reversibleGatePermutation input
    output (oraclePresentWireAt p slot) =
      decide (slot.val < configuration.1.card) := by
  dsimp only
  let output := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
    reversibleGatePermutation input
  have specification := computeSharedDecoderPresenceParityAndOneFlagsCircuit_correct_of_clean p inputWires
    layout configuration input clean rowMode
  have point := congrArg (fun values : List Bool =>
    values[slot.val]?.getD false) specification.present
  simpa [output, readWires, oraclePresentWires, oraclePresentWireAt,
    QParameters.presentWidth, presenceBitsFrom_getD, slot.isLt] using point

/-- 永続decoder後のactive register wordは、配置の対応site wordに一致する。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_activeWord_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input)
    (rowMode : Bool) (slot : Fin p.K)
    (active : slot.val < configuration.1.card) :
    let output := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
      reversibleGatePermutation input
    readWires (registerWordAt p inputWires slot) output =
      List.ofFn fun bit =>
        siteBit p (configuration.siteAt ⟨slot.val, active⟩) bit := by
  dsimp only
  let output := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
    reversibleGatePermutation input
  have full := computeSharedDecoderPresenceParityAndOneFlagsCircuit_input_preserved_of_clean p inputWires
    layout configuration input clean rowMode
  calc
    readWires (registerWordAt p inputWires slot) output =
        ((readWires inputWires output).drop (slot.val * p.wordWidth)).take
          p.wordWidth := by
      simp [registerWordAt, readWires]
    _ = ((registerBitList (delimiterEncoding configuration)).drop
          (slot.val * p.wordWidth)).take p.wordWidth := by rw [full]
    _ = List.ofFn fun bit =>
          siteBit p (configuration.siteAt ⟨slot.val, active⟩) bit := by
      exact delimiterEncoding_activeWord configuration ⟨slot.val, active⟩

/-- 合法delimiterを処理した永続decoder出力では、present wordがslot添字について単射である。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_distinctPresentWords_of_clean
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : OraclePersistentInputLayout p inputWires)
    (configuration : QConfiguration p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : OraclePersistentCleanInput p inputWires configuration input)
    (rowMode : Bool) :
    let output := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
      reversibleGatePermutation input
    DistinctPresentWords p inputWires output := by
  dsimp only
  let output := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
    reversibleGatePermutation input
  intro left right leftPresent rightPresent wordsEqual
  have leftValue := computeSharedDecoderPresenceParityAndOneFlagsCircuit_present_value_of_clean p inputWires
    layout configuration input clean rowMode left
  have rightValue := computeSharedDecoderPresenceParityAndOneFlagsCircuit_present_value_of_clean p inputWires
    layout configuration input clean rowMode right
  change output (oraclePresentWireAt p left) =
      decide (left.val < configuration.1.card) at leftValue
  change output (oraclePresentWireAt p right) =
      decide (right.val < configuration.1.card) at rightValue
  change output (oraclePresentWireAt p left) = true at leftPresent
  change output (oraclePresentWireAt p right) = true at rightPresent
  rw [leftPresent] at leftValue
  rw [rightPresent] at rightValue
  have leftActive : left.val < configuration.1.card :=
    of_decide_eq_true leftValue.symm
  have rightActive : right.val < configuration.1.card :=
    of_decide_eq_true rightValue.symm
  have leftWord := computeSharedDecoderPresenceParityAndOneFlagsCircuit_activeWord_of_clean p inputWires
    layout configuration input clean rowMode left leftActive
  have rightWord := computeSharedDecoderPresenceParityAndOneFlagsCircuit_activeWord_of_clean p inputWires
    layout configuration input clean rowMode right rightActive
  change readWires (registerWordAt p inputWires left) output = _ at leftWord
  change readWires (registerWordAt p inputWires right) output = _ at rightWord
  rw [leftWord, rightWord] at wordsEqual
  have sitesEqual :
      configuration.siteAt ⟨left.val, leftActive⟩ =
        configuration.siteAt ⟨right.val, rightActive⟩ := by
    apply siteBit_ext
    intro bit
    have point := congrArg (fun values : List Bool => values[bit.val]?) wordsEqual
    simpa using point
  have activeSlotsEqual := configuration.siteAt_injective sitesEqual
  apply Fin.ext
  exact congrArg (fun slot : Fin configuration.1.card => slot.val) activeSlotsEqual

/-- cleanな局所flag上では、1 slot参照作用のequal flagはword一致条件そのものになる。 -/
theorem membershipSlotReference_equalFlag
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (equalZero : input (membershipEqualWireAt p slot) = false) :
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
        (membershipEqualWireAt p slot) =
      decide (readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input) := by
  have layout := membershipSlotLayout_canonical p register inputLayout slot
  let afterEqual :=
    if decide (readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input) then
      xBasisAction (membershipEqualWireAt p slot) input
    else input
  let afterGood := xBasisAction (membershipGoodWireAt p slot) afterEqual
  let afterRemove := toffoliBasisAction (oraclePresentWireAt p slot)
    (membershipEqualWireAt p slot) (membershipGoodWireAt p slot) afterGood
  have afterGoodValue : afterGood (membershipEqualWireAt p slot) =
      decide (readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input) := by
    dsimp only [afterGood]
    rw [xBasisAction_other _ _ layout.equal_ne_good]
    by_cases same : readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input <;>
      simp [afterEqual, same, equalZero]
  have removePreserves : afterRemove (membershipEqualWireAt p slot) =
      afterGood (membershipEqualWireAt p slot) :=
    toffoliBasisAction_other _ _ _ _ layout.equal_ne_good afterGood
  have otherPreserves :
      toffoliBasisAction (oraclePresentWireAt p slot)
          (membershipEqualWireAt p slot) (oraclePresentOtherWire p) afterRemove
          (membershipEqualWireAt p slot) =
        afterRemove (membershipEqualWireAt p slot) :=
    toffoliBasisAction_other _ _ _ _ layout.equal_ne_other afterRemove
  change (if includePresentOther && slot != selectedSlot then
      toffoliBasisAction (oraclePresentWireAt p slot)
        (membershipEqualWireAt p slot) (oraclePresentOtherWire p) afterRemove
    else afterRemove) (membershipEqualWireAt p slot) = _
  by_cases record : (includePresentOther && slot != selectedSlot) = true
  · simp only [record, if_true, otherPreserves, removePreserves]
    exact afterGoodValue
  · simp only [record, Bool.false_eq_true, if_false, removePreserves]
    exact afterGoodValue

/-- cleanな局所flag上では、1 slot参照作用のgood flagはmembership条件の否定になる。 -/
theorem membershipSlotReference_goodFlag
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (equalZero : input (membershipEqualWireAt p slot) = false)
    (goodZero : input (membershipGoodWireAt p slot) = false) :
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
        (membershipGoodWireAt p slot) =
      !(membershipSlotMatches p register slot input) := by
  have layout := membershipSlotLayout_canonical p register inputLayout slot
  let afterEqual :=
    if decide (readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input) then
      xBasisAction (membershipEqualWireAt p slot) input
    else input
  let afterGood := xBasisAction (membershipGoodWireAt p slot) afterEqual
  let afterRemove := toffoliBasisAction (oraclePresentWireAt p slot)
    (membershipEqualWireAt p slot) (membershipGoodWireAt p slot) afterGood
  have afterGoodPresent : afterGood (oraclePresentWireAt p slot) =
      input (oraclePresentWireAt p slot) := by
    dsimp only [afterGood]
    rw [xBasisAction_other _ _ layout.present_ne_good]
    by_cases same : readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input
    · simp [afterEqual, same, layout.present_ne_equal]
    · simp [afterEqual, same]
  have afterGoodEqual : afterGood (membershipEqualWireAt p slot) =
      decide (readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input) := by
    dsimp only [afterGood]
    rw [xBasisAction_other _ _ layout.equal_ne_good]
    by_cases same : readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input <;>
      simp [afterEqual, same, equalZero]
  have afterGoodGood : afterGood (membershipGoodWireAt p slot) = true := by
    dsimp only [afterGood]
    rw [xBasisAction_target]
    by_cases same : readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input
    · simp [afterEqual, same, goodZero, layout.equal_ne_good.symm]
    · simp [afterEqual, same, goodZero]
  have afterRemoveValue : afterRemove (membershipGoodWireAt p slot) =
      !(membershipSlotMatches p register slot input) := by
    dsimp only [afterRemove]
    rw [toffoliBasisAction_target, afterGoodPresent, afterGoodEqual,
      afterGoodGood]
    unfold membershipSlotMatches
    cases present : input (oraclePresentWireAt p slot) <;>
      cases equalValue : decide (readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input) <;>
      rfl
  have otherPreserves :
      toffoliBasisAction (oraclePresentWireAt p slot)
          (membershipEqualWireAt p slot) (oraclePresentOtherWire p) afterRemove
          (membershipGoodWireAt p slot) =
        afterRemove (membershipGoodWireAt p slot) :=
    toffoliBasisAction_other _ _ _ _ layout.good_ne_other afterRemove
  change (if includePresentOther && slot != selectedSlot then
      toffoliBasisAction (oraclePresentWireAt p slot)
        (membershipEqualWireAt p slot) (oraclePresentOtherWire p) afterRemove
    else afterRemove) (membershipGoodWireAt p slot) = _
  by_cases record : (includePresentOther && slot != selectedSlot) = true
  · simpa only [record, if_true, otherPreserves] using afterRemoveValue
  · simpa only [record, Bool.false_eq_true, if_false] using afterRemoveValue

/-- present-otherを記録するslotでは、局所参照作用が一致条件をXORする。 -/
theorem membershipSlotReference_presentOther
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (equalZero : input (membershipEqualWireAt p slot) = false) :
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
        (oraclePresentOtherWire p) =
      if includePresentOther && slot != selectedSlot then
        if membershipSlotMatches p register slot input then
          !(input (oraclePresentOtherWire p))
        else input (oraclePresentOtherWire p)
      else input (oraclePresentOtherWire p) := by
  have layout := membershipSlotLayout_canonical p register inputLayout slot
  let afterEqual :=
    if decide (readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input) then
      xBasisAction (membershipEqualWireAt p slot) input
    else input
  let afterGood := xBasisAction (membershipGoodWireAt p slot) afterEqual
  let afterRemove := toffoliBasisAction (oraclePresentWireAt p slot)
    (membershipEqualWireAt p slot) (membershipGoodWireAt p slot) afterGood
  have removePreserves : afterRemove (oraclePresentOtherWire p) =
      afterGood (oraclePresentOtherWire p) :=
    toffoliBasisAction_other _ _ _ _ layout.good_ne_other.symm afterGood
  have removePresent : afterRemove (oraclePresentWireAt p slot) =
      afterGood (oraclePresentWireAt p slot) :=
    toffoliBasisAction_other _ _ _ _ layout.present_ne_good afterGood
  have removeEqual : afterRemove (membershipEqualWireAt p slot) =
      afterGood (membershipEqualWireAt p slot) :=
    toffoliBasisAction_other _ _ _ _ layout.equal_ne_good afterGood
  have afterGoodPresent : afterGood (oraclePresentWireAt p slot) =
      input (oraclePresentWireAt p slot) := by
    dsimp only [afterGood]
    rw [xBasisAction_other _ _ layout.present_ne_good]
    by_cases same : readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input
    · simp [afterEqual, same, layout.present_ne_equal]
    · simp [afterEqual, same]
  have afterGoodEqual : afterGood (membershipEqualWireAt p slot) =
      decide (readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input) := by
    dsimp only [afterGood]
    rw [xBasisAction_other _ _ layout.equal_ne_good]
    by_cases same : readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input <;>
      simp [afterEqual, same, equalZero]
  have afterGoodOther : afterGood (oraclePresentOtherWire p) =
      input (oraclePresentOtherWire p) := by
    dsimp only [afterGood]
    rw [xBasisAction_other _ _ layout.good_ne_other.symm]
    by_cases same : readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input
    · simp [afterEqual, same, layout.equal_ne_other.symm]
    · simp [afterEqual, same]
  change (if includePresentOther && slot != selectedSlot then
      toffoliBasisAction (oraclePresentWireAt p slot)
        (membershipEqualWireAt p slot) (oraclePresentOtherWire p) afterRemove
    else afterRemove) (oraclePresentOtherWire p) = _
  by_cases record : includePresentOther && slot != selectedSlot
  · simp only [record, if_true]
    rw [toffoliBasisAction_target]
    rw [removePresent, removeEqual, removePreserves, afterGoodPresent,
      afterGoodEqual, afterGoodOther]
    rfl
  · simp only [record, Bool.false_eq_true, if_false, removePreserves]
    exact afterGoodOther

/-- present-otherの局所作用を、一個のBool条件による反転として正規化する。 -/
theorem membershipSlotReference_presentOther_match
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (equalZero : input (membershipEqualWireAt p slot) = false) :
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
        (oraclePresentOtherWire p) =
      if membershipOtherMatch p register selectedSlot includePresentOther slot input
      then !(input (oraclePresentOtherWire p))
      else input (oraclePresentOtherWire p) := by
  rw [membershipSlotReference_presentOther p register inputLayout selectedSlot
    slot includePresentOther input equalZero]
  unfold membershipOtherMatch
  cases includePresentOther <;> cases slot != selectedSlot <;>
    cases membershipSlotMatches p register slot input <;> rfl

/-- membershipの1 slot参照作用はequal・good・present-other以外を変更しない。 -/
theorem membershipSlotReference_other
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (wireNeEqual : wire ≠ membershipEqualWireAt p slot)
    (wireNeGood : wire ≠ membershipGoodWireAt p slot)
    (wireNeOther : wire ≠ oraclePresentOtherWire p) :
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
        wire = input wire := by
  let afterEqual :=
    if decide (readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input) then
      xBasisAction (membershipEqualWireAt p slot) input
    else input
  let afterGood := xBasisAction (membershipGoodWireAt p slot) afterEqual
  let afterRemove := toffoliBasisAction (oraclePresentWireAt p slot)
    (membershipEqualWireAt p slot) (membershipGoodWireAt p slot) afterGood
  have equalPreserves : afterEqual wire = input wire := by
    by_cases same : readWires (oracleMovedWires p) input =
        readWires (registerWordAt p register slot) input
    · simp [afterEqual, same, xBasisAction_other _ _ wireNeEqual]
    · simp [afterEqual, same]
  have goodPreserves : afterGood wire = afterEqual wire :=
    xBasisAction_other _ _ wireNeGood afterEqual
  have removePreserves : afterRemove wire = afterGood wire :=
    toffoliBasisAction_other _ _ _ _ wireNeGood afterGood
  have otherPreserves :
      toffoliBasisAction (oraclePresentWireAt p slot)
          (membershipEqualWireAt p slot) (oraclePresentOtherWire p) afterRemove
          wire = afterRemove wire :=
    toffoliBasisAction_other _ _ _ _ wireNeOther afterRemove
  change (if includePresentOther && slot != selectedSlot then
      toffoliBasisAction (oraclePresentWireAt p slot)
        (membershipEqualWireAt p slot) (oraclePresentOtherWire p) afterRemove
    else afterRemove) wire = input wire
  by_cases record : (includePresentOther && slot != selectedSlot) = true
  · rw [if_pos record, otherPreserves, removePreserves, goodPreserves,
      equalPreserves]
  · rw [if_neg record, removePreserves, goodPreserves, equalPreserves]

/-- 1 slotのmembership参照作用は入力registerの任意wireを保存する。 -/
theorem membershipSlotReference_register
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth) (member : wire ∈ register) :
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
        wire = input wire := by
  apply membershipSlotReference_other
  · intro equal
    rw [equal] at member
    exact (List.disjoint_left.mp inputLayout.disjoint_membershipEqual member)
      (by simp [membershipEqualWireAt, RegisterSlice.wireList])
  · intro equal
    rw [equal] at member
    exact (List.disjoint_left.mp inputLayout.disjoint_membershipGood member)
      (by simp [membershipGoodWireAt, RegisterSlice.wireList])
  · intro equal
    rw [equal] at member
    exact (List.disjoint_left.mp inputLayout.disjoint_presentOther member)
      (by
        simp [oraclePresentOtherWire, oracleSingletonWire,
          RegisterSlice.wireList])

/-- 1 slotのmembership参照作用は全present flagを保存する。 -/
theorem membershipSlotReference_present
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot presentSlot : Fin p.K)
    (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
        (oraclePresentWireAt p presentSlot) =
      input (oraclePresentWireAt p presentSlot) := by
  apply membershipSlotReference_other
  · exact oraclePresentWireAt_ne_membershipEqual p presentSlot slot
  · exact oraclePresentWireAt_ne_membershipGood p presentSlot slot
  · exact oraclePresentWireAt_ne_presentOther p presentSlot

/-- 1 slotのmembership参照作用はmoved word全体を保存する。 -/
theorem membershipSlotReference_moved
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (oracleMovedWires p)
        (SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
          includePresentOther input) =
      readWires (oracleMovedWires p) input := by
  apply List.map_congr_left
  intro wire member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  apply membershipSlotReference_other
  · intro equal
    have numbers := congrArg wireNumber equal
    simp [membershipEqualWireAt, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical,
      QParameters.movedWidth, QParameters.membershipEqWidth] at numbers
    omega
  · intro equal
    have numbers := congrArg wireNumber equal
    simp [membershipGoodWireAt, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical,
      QParameters.movedWidth, QParameters.membershipEqWidth,
      QParameters.membershipGoodWidth] at numbers
    omega
  · intro equal
    have numbers := congrArg wireNumber equal
    simp [oraclePresentOtherWire, oracleSingletonWire,
      QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
      QParameters.movedWidth, QParameters.membershipEqWidth,
      QParameters.membershipGoodWidth] at numbers
    omega

/-- absent wireは任意slotのmembership equal wireと異なる。 -/
theorem oracleAbsentWire_ne_membershipEqual
    (p : QParameters) (slot : Fin p.K) :
    oracleAbsentWire p ≠ membershipEqualWireAt p slot := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [oracleAbsentWire, oracleSingletonWire, membershipEqualWireAt,
    QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
    QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
  omega

/-- absent wireは任意slotのmembership good wireと異なる。 -/
theorem oracleAbsentWire_ne_membershipGood
    (p : QParameters) (slot : Fin p.K) :
    oracleAbsentWire p ≠ membershipGoodWireAt p slot := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [oracleAbsentWire, oracleSingletonWire, membershipGoodWireAt,
    QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
    QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers
  omega

/-- absent wireはpresent-other wireと異なる。 -/
theorem oracleAbsentWire_ne_presentOther (p : QParameters) :
    oracleAbsentWire p ≠ oraclePresentOtherWire p := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [oracleAbsentWire, oraclePresentOtherWire, oracleSingletonWire,
    QLayout.oracleSlice, RegisterSlice.compose, OracleWorkLayout.canonical,
    QParameters.membershipEqWidth, QParameters.membershipGoodWidth] at numbers

/-- 1 slotのmembership参照作用はabsent wireを保存する。 -/
theorem membershipSlotReference_absent
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
        (oracleAbsentWire p) = input (oracleAbsentWire p) := by
  exact membershipSlotReference_other p register selectedSlot slot
    includePresentOther input (oracleAbsentWire p)
      (oracleAbsentWire_ne_membershipEqual p slot)
      (oracleAbsentWire_ne_membershipGood p slot)
      (oracleAbsentWire_ne_presentOther p)

/-- slot列のmembership参照作用を左から順に合成する。 -/
def FoldedSiteSlotMatchAndGoodFlagsReference
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (slots : List (Fin p.K))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  slots.foldl
    (fun state slot => SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
      includePresentOther state) input

/-- membership slot列全体は入力registerの任意wireを保存する。 -/
theorem membershipSlotsReference_register
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (wire : Wire p.ancillaWidth p.systemWidth), wire ∈ register →
      FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther slots
          input wire = input wire
  | [], _, _, _ => rfl
  | slot :: slots, input, wire, member => by
      change FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
          slots (SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
            includePresentOther input) wire = input wire
      rw [membershipSlotsReference_register p register inputLayout selectedSlot
        includePresentOther slots _ wire member]
      exact membershipSlotReference_register p register inputLayout selectedSlot
        slot includePresentOther input wire member

/-- membership slot列全体は任意のpresent flagを保存する。 -/
theorem membershipSlotsReference_present
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (presentSlot : Fin p.K),
      FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther slots
          input (oraclePresentWireAt p presentSlot) =
        input (oraclePresentWireAt p presentSlot)
  | [], _, _ => rfl
  | slot :: slots, input, presentSlot => by
      change FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
          slots (SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
            includePresentOther input) (oraclePresentWireAt p presentSlot) = _
      rw [membershipSlotsReference_present p register selectedSlot
        includePresentOther slots _ presentSlot]
      exact membershipSlotReference_present p register selectedSlot slot
        presentSlot includePresentOther input

/-- membership slot列全体はmoved wordを保存する。 -/
theorem membershipSlotsReference_moved
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      readWires (oracleMovedWires p)
          (FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
            slots input) =
        readWires (oracleMovedWires p) input
  | [], _ => rfl
  | slot :: slots, input => by
      change readWires (oracleMovedWires p)
          (FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
            slots (SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
              includePresentOther input)) = _
      rw [membershipSlotsReference_moved p register selectedSlot
        includePresentOther slots]
      exact membershipSlotReference_moved p register selectedSlot slot
        includePresentOther input

/-- membership slot列全体はabsent wireを保存する。 -/
theorem membershipSlotsReference_absent
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther slots
          input (oracleAbsentWire p) = input (oracleAbsentWire p)
  | [], _ => rfl
  | slot :: slots, input => by
      change FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
          slots (SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
            includePresentOther input) (oracleAbsentWire p) = _
      rw [membershipSlotsReference_absent p register selectedSlot
        includePresentOther slots]
      exact membershipSlotReference_absent p register selectedSlot slot
        includePresentOther input

/-- 先行slot列は、任意target slotの数学的membership条件を変化させない。 -/
theorem membershipSlotMatches_membershipSlotsReference
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot target : Fin p.K) (includePresentOther : Bool)
    (slots : List (Fin p.K))
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    membershipSlotMatches p register target
        (FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
          slots input) =
      membershipSlotMatches p register target input := by
  unfold membershipSlotMatches
  rw [membershipSlotsReference_present p register selectedSlot
    includePresentOther slots input target]
  rw [membershipSlotsReference_moved p register selectedSlot
    includePresentOther slots input]
  have registerWordPreserved :
      readWires (registerWordAt p register target)
          (FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
            slots input) =
        readWires (registerWordAt p register target) input := by
    apply List.map_congr_left
    intro wire member
    exact membershipSlotsReference_register p register inputLayout selectedSlot
      includePresentOther slots input wire
        (mem_register_of_mem_registerWordAt p register target member)
  rw [registerWordPreserved]

/-- 異なるslotのmembership作用は対象equal flagを保存する。 -/
theorem membershipSlotReference_equal_other_slot
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot target : Fin p.K) (includePresentOther : Bool)
    (different : target ≠ slot)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
        (membershipEqualWireAt p target) =
      input (membershipEqualWireAt p target) := by
  apply membershipSlotReference_other
  · intro equal
    exact different (membershipEqualWireAt_injective p equal)
  · exact membershipEqualWireAt_ne_goodWireAt p target slot
  · exact membershipEqualWireAt_ne_presentOther p target

/-- 異なるslotのmembership作用は対象good flagを保存する。 -/
theorem membershipSlotReference_good_other_slot
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot slot target : Fin p.K) (includePresentOther : Bool)
    (different : target ≠ slot)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot includePresentOther input
        (membershipGoodWireAt p target) =
      input (membershipGoodWireAt p target) := by
  apply membershipSlotReference_other
  · exact (membershipEqualWireAt_ne_goodWireAt p slot target).symm
  · intro equal
    exact different (membershipGoodWireAt_injective p equal)
  · exact membershipGoodWireAt_ne_presentOther p target

/-- 対象slotを含まないslot列は、そのequal flagを保存する。 -/
theorem membershipSlotsReference_equal_of_not_mem
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (target : Fin p.K), target ∉ slots →
      FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther slots
          input (membershipEqualWireAt p target) =
        input (membershipEqualWireAt p target)
  | [], _, _, _ => rfl
  | slot :: slots, input, target, absent => by
      have targetNeSlot : target ≠ slot := by
        intro equal
        subst slot
        exact absent (by simp)
      have targetAbsentTail : target ∉ slots := by
        intro member
        exact absent (by simp [member])
      change FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
          slots (SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
            includePresentOther input) (membershipEqualWireAt p target) = _
      rw [membershipSlotsReference_equal_of_not_mem p register selectedSlot
        includePresentOther slots _ target targetAbsentTail]
      exact membershipSlotReference_equal_other_slot p register selectedSlot slot
        target includePresentOther targetNeSlot input

/-- 対象slotを含まないslot列は、そのgood flagを保存する。 -/
theorem membershipSlotsReference_good_of_not_mem
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (target : Fin p.K), target ∉ slots →
      FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther slots
          input (membershipGoodWireAt p target) =
        input (membershipGoodWireAt p target)
  | [], _, _, _ => rfl
  | slot :: slots, input, target, absent => by
      have targetNeSlot : target ≠ slot := by
        intro equal
        subst slot
        exact absent (by simp)
      have targetAbsentTail : target ∉ slots := by
        intro member
        exact absent (by simp [member])
      change FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
          slots (SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
            includePresentOther input) (membershipGoodWireAt p target) = _
      rw [membershipSlotsReference_good_of_not_mem p register selectedSlot
        includePresentOther slots _ target targetAbsentTail]
      exact membershipSlotReference_good_other_slot p register selectedSlot slot
        target includePresentOther targetNeSlot input

/-- Nodupなslot列では、対象good flagは数学的membership条件の否定になる。 -/
theorem membershipSlotsReference_good
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth)
      (target : Fin p.K), slots.Nodup → target ∈ slots →
      input (membershipEqualWireAt p target) = false →
      input (membershipGoodWireAt p target) = false →
      FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther slots
          input (membershipGoodWireAt p target) =
        !(membershipSlotMatches p register target input)
  | [], _, _, _, member, _, _ => by simp at member
  | slot :: slots, input, target, nodup, member, equalZero, goodZero => by
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rcases List.mem_cons.mp member with targetHead | targetTail
      · subst slot
        change FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
            slots (SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot target
              includePresentOther input) (membershipGoodWireAt p target) = _
        rw [membershipSlotsReference_good_of_not_mem p register selectedSlot
          includePresentOther slots _ target headAbsent]
        exact membershipSlotReference_goodFlag p register inputLayout selectedSlot
          target includePresentOther input equalZero goodZero
      · have targetNeSlot : target ≠ slot := by
          intro equal
          subst slot
          exact headAbsent targetTail
        let afterHead := SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
          includePresentOther input
        change FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
            slots afterHead (membershipGoodWireAt p target) = _
        have equalPreserved := membershipSlotReference_equal_other_slot p register
          selectedSlot slot target includePresentOther targetNeSlot input
        have goodPreserved := membershipSlotReference_good_other_slot p register
          selectedSlot slot target includePresentOther targetNeSlot input
        change afterHead (membershipEqualWireAt p target) =
          input (membershipEqualWireAt p target) at equalPreserved
        change afterHead (membershipGoodWireAt p target) =
          input (membershipGoodWireAt p target) at goodPreserved
        rw [membershipSlotsReference_good p register inputLayout selectedSlot
          includePresentOther slots afterHead target tailNodup targetTail
          (equalPreserved.trans equalZero) (goodPreserved.trans goodZero)]
        have matchPreserved := membershipSlotMatches_membershipSlotsReference p
          register inputLayout selectedSlot target includePresentOther [slot] input
        change membershipSlotMatches p register target afterHead =
          membershipSlotMatches p register target input at matchPreserved
        rw [matchPreserved]

/-- 全要素がfalseなら、Bool列のparityはfalseである。 -/
theorem boolParity_map_eq_false_of_forall_false
    {α : Type} (predicate : α → Bool) :
    ∀ (values : List α),
      (∀ value ∈ values, predicate value = false) →
      boolParity (values.map predicate) = false
  | [], _ => rfl
  | value :: values, allFalse => by
      have headFalse := allFalse value (by simp)
      have tailFalse : ∀ tail ∈ values, predicate tail = false := by
        intro tail member
        exact allFalse tail (by simp [member])
      simp [boolParity, headFalse,
        boolParity_map_eq_false_of_forall_false predicate values tailFalse]

/-- 全要素がfalseなら、Bool列のanyもfalseである。 -/
theorem any_map_eq_false_of_forall_false
    {α : Type} (predicate : α → Bool) :
    ∀ (values : List α),
      (∀ value ∈ values, predicate value = false) →
      (values.map predicate).any id = false
  | [], _ => rfl
  | value :: values, allFalse => by
      have headFalse := allFalse value (by simp)
      have tailFalse : ∀ tail ∈ values, predicate tail = false := by
        intro tail member
        exact allFalse tail (by simp [member])
      simp [headFalse,
        any_map_eq_false_of_forall_false predicate values tailFalse]

/-- trueになる要素が高々一個なら、XOR parityは存在判定anyに一致する。 -/
theorem boolParity_eq_any_of_atMostOne
    {α : Type} (predicate : α → Bool) :
    ∀ (values : List α), values.Nodup →
      (∀ left ∈ values, predicate left = true →
        ∀ right ∈ values, predicate right = true → left = right) →
      boolParity (values.map predicate) = (values.map predicate).any id
  | [], _, _ => rfl
  | value :: values, nodup, atMostOne => by
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      by_cases headFalse : predicate value = false
      · have tailAtMostOne :
            ∀ left ∈ values, predicate left = true →
              ∀ right ∈ values, predicate right = true → left = right := by
          intro left leftMember leftTrue right rightMember rightTrue
          exact atMostOne left (by simp [leftMember]) leftTrue
            right (by simp [rightMember]) rightTrue
        simp [boolParity, headFalse,
          boolParity_eq_any_of_atMostOne predicate values tailNodup tailAtMostOne]
      · have headTrue : predicate value = true :=
          Bool.eq_true_of_not_eq_false headFalse
        have tailFalse : ∀ tail ∈ values, predicate tail = false := by
          intro tail member
          by_cases falseValue : predicate tail = false
          · exact falseValue
          · have tailTrue : predicate tail = true :=
              Bool.eq_true_of_not_eq_false falseValue
            have equal := atMostOne value (by simp) headTrue tail
              (by simp [member]) tailTrue
            subst tail
            exact (headAbsent member).elim
        have tailParity := boolParity_map_eq_false_of_forall_false
          predicate values tailFalse
        have tailAny := any_map_eq_false_of_forall_false
          predicate values tailFalse
        simp [boolParity, headTrue, tailParity, tailAny]

/-- Nodupなslot列では、present-other出力は一致条件列のparityになる。 -/
theorem membershipSlotsReference_presentOther_parity
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth), slots.Nodup →
      (∀ target ∈ slots,
        input (membershipEqualWireAt p target) = false) →
      FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther slots
          input (oraclePresentOtherWire p) =
        if boolParity (slots.map fun slot =>
            membershipOtherMatch p register selectedSlot includePresentOther
              slot input)
        then !(input (oraclePresentOtherWire p))
        else input (oraclePresentOtherWire p)
  | [], _, _, _ => rfl
  | slot :: slots, input, nodup, equalZero => by
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      let afterHead := SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
        includePresentOther input
      have headValue : afterHead (oraclePresentOtherWire p) =
          if membershipOtherMatch p register selectedSlot includePresentOther
              slot input
          then !(input (oraclePresentOtherWire p))
          else input (oraclePresentOtherWire p) := by
        exact membershipSlotReference_presentOther_match p register inputLayout
          selectedSlot slot includePresentOther input
            (equalZero slot (by simp))
      have tailEqualZero : ∀ target ∈ slots,
          afterHead (membershipEqualWireAt p target) = false := by
        intro target member
        have targetNeSlot : target ≠ slot := by
          intro equal
          subst target
          exact headAbsent member
        change SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot slot
            includePresentOther input (membershipEqualWireAt p target) = false
        rw [membershipSlotReference_equal_other_slot p register selectedSlot slot
          target includePresentOther targetNeSlot input]
        exact equalZero target (by simp [member])
      have tailConditions :
          slots.map (fun target =>
            membershipOtherMatch p register selectedSlot includePresentOther
              target afterHead) =
          slots.map (fun target =>
            membershipOtherMatch p register selectedSlot includePresentOther
              target input) := by
        apply List.map_congr_left
        intro target member
        unfold membershipOtherMatch
        have preserved := membershipSlotMatches_membershipSlotsReference p
          register inputLayout selectedSlot target includePresentOther [slot] input
        change membershipSlotMatches p register target afterHead =
          membershipSlotMatches p register target input at preserved
        rw [preserved]
      change FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
          slots afterHead (oraclePresentOtherWire p) = _
      rw [membershipSlotsReference_presentOther_parity p register inputLayout
        selectedSlot includePresentOther slots afterHead tailNodup tailEqualZero]
      rw [tailConditions, headValue]
      simp only [List.map_cons, boolParity]
      cases headMatch : membershipOtherMatch p register selectedSlot
          includePresentOther slot input <;>
        cases tailParity : boolParity (slots.map fun target =>
          membershipOtherMatch p register selectedSlot includePresentOther
            target input) <;> simp

/-- distinctなpresent word上では、二つの異なるslotが同時に一致することはない。 -/
theorem membershipOtherMatch_atMostOne
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (distinct : DistinctPresentWords p register input) :
    ∀ left right : Fin p.K,
      membershipOtherMatch p register selectedSlot includePresentOther left input =
        true →
      membershipOtherMatch p register selectedSlot includePresentOther right input =
        true →
      left = right := by
  intro left right leftMatch rightMatch
  have leftSlotMatch : membershipSlotMatches p register left input = true := by
    unfold membershipOtherMatch at leftMatch
    rw [Bool.and_eq_true] at leftMatch
    exact leftMatch.2
  have rightSlotMatch : membershipSlotMatches p register right input = true := by
    unfold membershipOtherMatch at rightMatch
    rw [Bool.and_eq_true] at rightMatch
    exact rightMatch.2
  unfold membershipSlotMatches at leftSlotMatch rightSlotMatch
  rw [Bool.and_eq_true] at leftSlotMatch rightSlotMatch
  have leftData := leftSlotMatch
  have rightData := rightSlotMatch
  apply distinct left right leftData.1 rightData.1
  have leftWords := of_decide_eq_true leftData.2
  have rightWords := of_decide_eq_true rightData.2
  exact leftWords.symm.trans rightWords

/-- membership計算開始時に要求するequal・good・集約flagの全0条件。 -/
structure MembershipFlagsClean (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- 全equal flagが0である。 -/
  equal_zero : ∀ slot : Fin p.K,
    input (membershipEqualWireAt p slot) = false
  /-- 全good flagが0である。 -/
  good_zero : ∀ slot : Fin p.K,
    input (membershipGoodWireAt p slot) = false
  /-- present-other flagが0である。 -/
  present_other_zero : input (oraclePresentOtherWire p) = false
  /-- absent flagが0である。 -/
  absent_zero : input (oracleAbsentWire p) = false

/-- 全0アンシラ標準入力ではmembership flag領域がcleanである。 -/
theorem zeroAncillaJointBasis_membershipFlagsClean
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    MembershipFlagsClean p (zeroAncillaJointBasis p system) where
  equal_zero := by
    intro slot
    simp [membershipEqualWireAt, RegisterSlice.ancillaWire]
  good_zero := by
    intro slot
    simp [membershipGoodWireAt, RegisterSlice.ancillaWire]
  present_other_zero := by
    simp [oraclePresentOtherWire, oracleSingletonWire,
      RegisterSlice.ancillaWire]
  absent_zero := by
    simp [oracleAbsentWire, oracleSingletonWire, RegisterSlice.ancillaWire]

/-- 選択slot以外にpresentかつmoved wordと一致するslotが存在するかを表す。 -/
def hasMatchingOther
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Bool :=
  ((List.finRange p.K).map fun slot =>
    membershipOtherMatch p register selectedSlot includePresentOther slot input).any id

/-- 合法配置由来のdistinct条件とclean入力の下で、present-otherは存在判定に一致する。 -/
theorem membershipSlotsReference_presentOther_eq_hasMatchingOther
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipFlagsClean p input)
    (distinct : DistinctPresentWords p register input) :
    FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
        (List.finRange p.K) input (oraclePresentOtherWire p) =
      hasMatchingOther p register selectedSlot includePresentOther input := by
  rw [membershipSlotsReference_presentOther_parity p register inputLayout
    selectedSlot includePresentOther (List.finRange p.K) input
      (List.nodup_finRange _) (by
        intro target _
        exact clean.equal_zero target)]
  have atMostOne :
      ∀ left ∈ List.finRange p.K,
        membershipOtherMatch p register selectedSlot includePresentOther left input =
          true →
        ∀ right ∈ List.finRange p.K,
          membershipOtherMatch p register selectedSlot includePresentOther right input =
            true → left = right := by
    intro left _ leftMatch right _ rightMatch
    exact membershipOtherMatch_atMostOne p register selectedSlot
      includePresentOther input distinct left right leftMatch rightMatch
  rw [boolParity_eq_any_of_atMostOne
    (fun slot => membershipOtherMatch p register selectedSlot
      includePresentOther slot input)
    (List.finRange p.K) (List.nodup_finRange _) atMostOne]
  unfold hasMatchingOther
  cases anyMatch : ((List.finRange p.K).map fun slot =>
      membershipOtherMatch p register selectedSlot includePresentOther slot input).any id <;>
    simp [clean.present_other_zero]

/-- 全`Fin K`走査後、任意slotのgood flagはそのmembership条件の否定である。 -/
theorem membershipSlotsReference_all_good
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipFlagsClean p input)
    (target : Fin p.K) :
    FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
        (List.finRange p.K) input (membershipGoodWireAt p target) =
      !(membershipSlotMatches p register target input) := by
  exact membershipSlotsReference_good p register inputLayout selectedSlot
    includePresentOther (List.finRange p.K) input target
      (List.nodup_finRange _) (List.mem_finRange _)
      (clean.equal_zero target) (clean.good_zero target)

/-- 「どのpresent slotにもmoved wordが一致しない」を有限全称のBoolとして定義する。 -/
def noMembershipMatch
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth) : Bool :=
  (List.finRange p.K).all fun slot =>
    !(membershipSlotMatches p register slot input)

/-- 全slot走査後のgood列ANDは、数学的な「一致なし」判定に等しい。 -/
theorem allWiresTrue_membershipGood_eq_noMembershipMatch
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipFlagsClean p input) :
    allWiresTrue (membershipGoodWires p)
        (FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
          (List.finRange p.K) input) =
      noMembershipMatch p register input := by
  unfold allWiresTrue readWires membershipGoodWires noMembershipMatch
  simp only [QParameters.membershipGoodWidth, List.map_map]
  rw [List.all_map]
  apply List.all_congr rfl
  intro slot
  exact membershipSlotsReference_all_good p register inputLayout selectedSlot
    includePresentOther input clean slot

/-- 正本の1 slot回路は純粋なmembership参照関数と厳密に一致する。 -/
theorem runBasis_membershipSlotCircuitTyped
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
  simpa [xorSiteSlotMatchAndGoodFlagAtIndexCircuit, SiteSlotMatchAndGoodFlagAtIndexXorSpec] using
    runBasis_membershipSlotCircuit (oracleMovedWires p)
      (registerWordAt p register slot) (oracleCompareWorkWires p)
      (decoderAndScratchWires p) (oraclePresentWireAt p slot)
      (membershipEqualWireAt p slot) (membershipGoodWireAt p slot)
      (oraclePresentOtherWire p) (includePresentOther && slot != selectedSlot)
      input (membershipSlotLayout_canonical p register inputLayout slot) clean

/-- 任意のslot列について、正本回路列は参照作用に一致しworkをcleanに保つ。 -/
theorem runBasis_membershipSlotSequenceTyped
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool) :
    ∀ (slots : List (Fin p.K))
      (input : JointBasis p.ancillaWidth p.systemWidth),
      MembershipSlotClean (oracleCompareWorkWires p)
        (decoderAndScratchWires p) input →
      let output := (Circuit.sequence <| slots.map fun slot =>
        xorSiteSlotMatchAndGoodFlagAtIndexCircuit p register selectedSlot slot
          includePresentOther).runBasis reversibleGatePermutation input
      output = FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot
          includePresentOther slots input ∧
        MembershipSlotClean (oracleCompareWorkWires p)
          (decoderAndScratchWires p) output
  | [], input, clean => by
      exact ⟨rfl, clean⟩
  | slot :: slots, input, clean => by
      let firstCircuit := xorSiteSlotMatchAndGoodFlagAtIndexCircuit p register selectedSlot slot
        includePresentOther
      let afterFirst := firstCircuit.runBasis reversibleGatePermutation input
      have firstEq : afterFirst = SiteSlotMatchAndGoodFlagAtIndexXorSpec p register selectedSlot
          slot includePresentOther input := by
        simpa [firstCircuit, afterFirst] using
          runBasis_membershipSlotCircuitTyped p register inputLayout selectedSlot
            slot includePresentOther input clean
      have firstClean : MembershipSlotClean (oracleCompareWorkWires p)
          (decoderAndScratchWires p) afterFirst := by
        simpa [firstCircuit, afterFirst, xorSiteSlotMatchAndGoodFlagAtIndexCircuit] using
          membershipSlotCircuit_clean_canonical p register inputLayout slot
            (includePresentOther && slot != selectedSlot) input clean
      have tail := runBasis_membershipSlotSequenceTyped p register inputLayout
        selectedSlot includePresentOther slots afterFirst firstClean
      constructor
      · change (Circuit.sequence (slots.map fun tailSlot =>
            xorSiteSlotMatchAndGoodFlagAtIndexCircuit p register selectedSlot tailSlot
              includePresentOther)).runBasis reversibleGatePermutation afterFirst = _
        rw [tail.1, firstEq]
        rfl
      · exact tail.2

/-- 全`Fin K` slotを走査する正本membership列の完全な基底作用とclean性。 -/
theorem runBasis_membershipSlotCircuitsTyped
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input) :
    let output := (Circuit.sequence <| siteSlotMatchAndGoodFlagCircuits p register
      selectedSlot includePresentOther).runBasis reversibleGatePermutation input
    output = FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot includePresentOther
        (List.finRange p.K) input ∧
      MembershipSlotClean (oracleCompareWorkWires p)
        (decoderAndScratchWires p) output := by
  simpa [siteSlotMatchAndGoodFlagCircuits] using
    runBasis_membershipSlotSequenceTyped p register inputLayout selectedSlot
      includePresentOther (List.finRange p.K) input clean

/-- cleanなmembership workは、その外側の1 wireを反転してもcleanである。 -/
theorem MembershipSlotClean.xBasisAction_of_outside
    {ancillaQubits systemQubits : Nat}
    {equalWork andScratch : List (Wire ancillaQubits systemQubits)}
    {input : JointBasis ancillaQubits systemQubits}
    (clean : MembershipSlotClean equalWork andScratch input)
    (target : Wire ancillaQubits systemQubits)
    (target_not_equalWork : target ∉ equalWork)
    (target_not_scratch : target ∉ andScratch) :
    MembershipSlotClean equalWork andScratch (xBasisAction target input) := by
  refine {
    equalWork_zero := ?_
    scratch_zero := ?_ }
  · rw [readWires_xBasisAction_other target equalWork input]
    · exact clean.equalWork_zero
    · exact target_not_equalWork
  · intro wire member
    rw [xBasisAction_other target wire]
    · exact clean.scratch_zero wire member
    · intro equal
      subst wire
      exact target_not_scratch member

/-- 全slot判定後のgood flagのANDをabsentへ書く純粋参照作用。 -/
def MembershipMatchGoodAndAbsentFlagsXorSpec
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  let afterSlots := FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot
    includePresentOther (List.finRange p.K) input
  if allWiresTrue (membershipGoodWires p) afterSlots then
    xBasisAction (oracleAbsentWire p) afterSlots
  else afterSlots

/-- clean入力では、membership全体のabsent出力は「既存slotとの一致なし」判定に等しい。 -/
theorem membershipComputeReference_absent
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipFlagsClean p input) :
    MembershipMatchGoodAndAbsentFlagsXorSpec p register selectedSlot includePresentOther input
        (oracleAbsentWire p) = noMembershipMatch p register input := by
  let afterSlots := FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot
    includePresentOther (List.finRange p.K) input
  have condition : allWiresTrue (membershipGoodWires p) afterSlots =
      noMembershipMatch p register input := by
    simpa [afterSlots] using
      allWiresTrue_membershipGood_eq_noMembershipMatch p register inputLayout
        selectedSlot includePresentOther input clean
  have absentZero : afterSlots (oracleAbsentWire p) = false := by
    calc
      afterSlots (oracleAbsentWire p) = input (oracleAbsentWire p) := by
        exact membershipSlotsReference_absent p register selectedSlot
          includePresentOther (List.finRange p.K) input
      _ = false := clean.absent_zero
  unfold MembershipMatchGoodAndAbsentFlagsXorSpec
  change (if allWiresTrue (membershipGoodWires p) afterSlots then
      xBasisAction (oracleAbsentWire p) afterSlots else afterSlots)
        (oracleAbsentWire p) = noMembershipMatch p register input
  rw [condition]
  cases noMatch : noMembershipMatch p register input <;>
    simp [absentZero, xBasisAction_target]

/-- distinctな合法入力では、membership全体のpresent-other出力は他slot一致の存在判定になる。 -/
theorem membershipComputeReference_presentOther
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipFlagsClean p input)
    (distinct : DistinctPresentWords p register input) :
    MembershipMatchGoodAndAbsentFlagsXorSpec p register selectedSlot includePresentOther input
        (oraclePresentOtherWire p) =
      hasMatchingOther p register selectedSlot includePresentOther input := by
  let afterSlots := FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot
    includePresentOther (List.finRange p.K) input
  have otherValue : afterSlots (oraclePresentOtherWire p) =
      hasMatchingOther p register selectedSlot includePresentOther input := by
    simpa [afterSlots] using
      membershipSlotsReference_presentOther_eq_hasMatchingOther p register
        inputLayout selectedSlot includePresentOther input clean distinct
  unfold MembershipMatchGoodAndAbsentFlagsXorSpec
  change (if allWiresTrue (membershipGoodWires p) afterSlots then
      xBasisAction (oracleAbsentWire p) afterSlots else afterSlots)
        (oraclePresentOtherWire p) = _
  split
  · rw [xBasisAction_other (oracleAbsentWire p) (oraclePresentOtherWire p)
      (oracleAbsentWire_ne_presentOther p).symm]
    exact otherValue
  · exact otherValue

/-- membership good flag列とabsent用多重制御ANDは正本layoutで重複しない。 -/
theorem membershipAbsent_layout_nodup (p : QParameters) :
    (membershipGoodWires p ++ decoderAndScratchWires p ++
      [oracleAbsentWire p]).Nodup := by
  let goodSlice := QLayout.oracleSlice
    (OracleWorkLayout.canonical p).membershipGood
  let absentSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).absent
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have goodNodup : (membershipGoodWires p).Nodup := by
    simpa [membershipGoodWires, goodSlice, RegisterSlice.wireList] using
      (RegisterSlice.wireList_nodup
        (systemWidth := p.systemWidth) goodSlice)
  have scratchNodup : (decoderAndScratchWires p).Nodup :=
    List.Nodup.sublist (by simp) (decoderAndScratchFlags_nodup p)
  have goodAnd :
      (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [goodSlice, andSlice, QLayout.oracleSlice,
      RegisterSlice.compose, OracleWorkLayout.canonical]
    omega
  have goodScratch :
      (membershipGoodWires p).Disjoint (decoderAndScratchWires p) := by
    rw [List.disjoint_left]
    intro wire goodMember scratchMember
    have goodFull : wire ∈
        (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [membershipGoodWires, goodSlice, RegisterSlice.wireList] using
        goodMember
    have andMember := decoderComparisonAndMember p
      (List.mem_append.mpr (Or.inl scratchMember))
    have andFull : wire ∈
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oracleAndWorkWires, andSlice, RegisterSlice.wireList] using andMember
    exact (List.disjoint_left.mp goodAnd goodFull) andFull
  have goodScratchNodup :
      (membershipGoodWires p ++ decoderAndScratchWires p).Nodup :=
    List.nodup_append.mpr ⟨goodNodup, scratchNodup, by
      intro left leftMember right rightMember equal
      subst right
      exact (List.disjoint_left.mp goodScratch leftMember) rightMember⟩
  have absentMember : oracleAbsentWire p ∈
      (absentSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    simp [oracleAbsentWire, oracleSingletonWire, absentSlice,
      RegisterSlice.wireList]
  have absentGood : oracleAbsentWire p ∉ membershipGoodWires p := by
    have disjoint :
        (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (absentSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      apply RegisterSlice.wireList_disjoint_of_end_le_start
      simp [goodSlice, absentSlice, QLayout.oracleSlice,
        RegisterSlice.compose, OracleWorkLayout.canonical]
      omega
    intro member
    have goodFull : oracleAbsentWire p ∈
        (goodSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [membershipGoodWires, goodSlice, RegisterSlice.wireList] using member
    exact (List.disjoint_left.mp disjoint goodFull) absentMember
  have absentScratch : oracleAbsentWire p ∉ decoderAndScratchWires p := by
    have disjoint :
        (absentSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      apply RegisterSlice.wireList_disjoint_of_end_le_start
      simp [absentSlice, andSlice, QLayout.oracleSlice,
        RegisterSlice.compose, OracleWorkLayout.canonical]
      omega
    intro member
    have andMember := decoderComparisonAndMember p
      (List.mem_append.mpr (Or.inl member))
    have andFull : oracleAbsentWire p ∈
        (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
      simpa [oracleAndWorkWires, andSlice, RegisterSlice.wireList] using andMember
    exact (List.disjoint_left.mp disjoint absentMember) andFull
  apply List.nodup_append.mpr
  refine ⟨goodScratchNodup, by simp, ?_⟩
  intro wire member target targetMember equal
  simp only [List.mem_singleton] at targetMember
  subst target
  subst wire
  rcases List.mem_append.mp member with goodMember | scratchMember
  · exact absentGood goodMember
  · exact absentScratch scratchMember

/-- membership good flag用の多重制御ANDには一般の`q,K`で十分なscratchがある。 -/
theorem membershipAbsent_enoughScratch (p : QParameters) :
    (membershipGoodWires p).length ≤ (decoderAndScratchWires p).length + 1 := by
  simp [membershipGoodWires, decoderAndScratchWires, oracleAndWorkWires,
    QParameters.membershipGoodWidth, QParameters.andWorkWidth,
    QParameters.wordWidth]
  omega

/-- 型安全なmembership正本回路全体は参照作用と一致し、workをcleanに戻す。 -/
theorem runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input) :
    let output := (xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot
      includePresentOther).runBasis reversibleGatePermutation input
    output = MembershipMatchGoodAndAbsentFlagsXorSpec p register selectedSlot
        includePresentOther input ∧
      MembershipSlotClean (oracleCompareWorkWires p)
        (decoderAndScratchWires p) output := by
  dsimp only
  let slotsCircuit := Circuit.sequence <| siteSlotMatchAndGoodFlagCircuits p register
    selectedSlot includePresentOther
  let afterSlots := slotsCircuit.runBasis reversibleGatePermutation input
  have slotsResult := runBasis_membershipSlotCircuitsTyped p register inputLayout
    selectedSlot includePresentOther input clean
  have afterSlotsEq : afterSlots = FoldedSiteSlotMatchAndGoodFlagsReference p register selectedSlot
      includePresentOther (List.finRange p.K) input := by
    simpa [afterSlots, slotsCircuit] using slotsResult.1
  have afterSlotsClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) afterSlots := by
    simpa [afterSlots, slotsCircuit] using slotsResult.2
  have andResult := runBasis_positiveMultiControlledX (membershipGoodWires p)
    (decoderAndScratchWires p) (oracleAbsentWire p) afterSlots
    (membershipAbsent_enoughScratch p) (membershipAbsent_layout_nodup p)
    afterSlotsClean.scratch_zero
  have outputEq :
      (xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot includePresentOther).runBasis
          reversibleGatePermutation input =
        if allWiresTrue (membershipGoodWires p) afterSlots then
          xBasisAction (oracleAbsentWire p) afterSlots
        else afterSlots := by
    simpa [xorMembershipMatchGoodAndAbsentFlagsCircuit, slotsCircuit, afterSlots, runBasis_seq] using
      andResult
  constructor
  · rw [outputEq, afterSlotsEq]
    rfl
  · rw [outputEq]
    split
    · apply afterSlotsClean.xBasisAction_of_outside
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
    · exact afterSlotsClean

/-- 型安全な基本ゲートmembership回路のabsent出力は数学的な一致なし判定に等しい。 -/
theorem runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_absent
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input)
    (flagsClean : MembershipFlagsClean p input) :
    (xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot includePresentOther).runBasis
        reversibleGatePermutation input (oracleAbsentWire p) =
      noMembershipMatch p register input := by
  have result := runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit p register inputLayout
    selectedSlot includePresentOther input slotClean
  dsimp only at result
  rw [result.1]
  exact membershipComputeReference_absent p register inputLayout selectedSlot
    includePresentOther input flagsClean

/-- distinctな合法入力では、型安全な基本ゲートmembership回路もpresent-other存在判定を返す。 -/
theorem runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_presentOther
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (inputLayout : MembershipInputLayout p register)
    (selectedSlot : Fin p.K) (includePresentOther : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (slotClean : MembershipSlotClean (oracleCompareWorkWires p)
      (decoderAndScratchWires p) input)
    (flagsClean : MembershipFlagsClean p input)
    (distinct : DistinctPresentWords p register input) :
    (xorMembershipMatchGoodAndAbsentFlagsCircuit p register selectedSlot includePresentOther).runBasis
        reversibleGatePermutation input (oraclePresentOtherWire p) =
      hasMatchingOther p register selectedSlot includePresentOther input := by
  have result := runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit p register inputLayout
    selectedSlot includePresentOther input slotClean
  dsimp only at result
  rw [result.1]
  exact membershipComputeReference_presentOther p register inputLayout
    selectedSlot includePresentOther input flagsClean distinct

/-- 1 slot回路後の等値flagは、二つのwordの等値判定そのものである。 -/
theorem membershipSlotCircuit_equal_value
    {ancillaQubits systemQubits : Nat}
    (moved word equalWork andScratch :
      List (Wire ancillaQubits systemQubits))
    (presentFlag equalFlag goodFlag presentOtherFlag :
      Wire ancillaQubits systemQubits)
    (recordPresentOther : Bool)
    (input : JointBasis ancillaQubits systemQubits)
    (layout : MembershipSlotLayout moved word equalWork andScratch
      presentFlag equalFlag goodFlag presentOtherFlag)
    (clean : MembershipSlotClean equalWork andScratch input)
    (equal_zero : input equalFlag = false) :
    (membershipSlotCircuit moved word equalWork andScratch presentFlag equalFlag
      goodFlag presentOtherFlag recordPresentOther).runBasis
        reversibleGatePermutation input equalFlag =
      decide (readWires moved input = readWires word input) := by
  rw [runBasis_membershipSlotCircuit moved word equalWork andScratch presentFlag
    equalFlag goodFlag presentOtherFlag recordPresentOther input layout clean]
  cases recordPresentOther <;>
    by_cases equalWords : readWires moved input = readWires word input <;>
    simp [equalWords, equal_zero, toffoliBasisAction, xBasisAction,
      layout.present_ne_equal, layout.present_ne_good, layout.equal_ne_good,
      layout.equal_ne_other]

/-- cleanなgood flagは、presentかつ等値である場合だけ0、それ以外では1になる。 -/
theorem membershipSlotCircuit_good_value
    {ancillaQubits systemQubits : Nat}
    (moved word equalWork andScratch :
      List (Wire ancillaQubits systemQubits))
    (presentFlag equalFlag goodFlag presentOtherFlag :
      Wire ancillaQubits systemQubits)
    (recordPresentOther : Bool)
    (input : JointBasis ancillaQubits systemQubits)
    (layout : MembershipSlotLayout moved word equalWork andScratch
      presentFlag equalFlag goodFlag presentOtherFlag)
    (clean : MembershipSlotClean equalWork andScratch input)
    (equal_zero : input equalFlag = false)
    (good_zero : input goodFlag = false) :
    (membershipSlotCircuit moved word equalWork andScratch presentFlag equalFlag
      goodFlag presentOtherFlag recordPresentOther).runBasis
        reversibleGatePermutation input goodFlag =
      !(input presentFlag &&
        decide (readWires moved input = readWires word input)) := by
  rw [runBasis_membershipSlotCircuit moved word equalWork andScratch presentFlag
    equalFlag goodFlag presentOtherFlag recordPresentOther input layout clean]
  cases recordPresentOther <;>
    by_cases equalWords : readWires moved input = readWires word input <;>
    simp [equalWords, equal_zero, good_zero, toffoliBasisAction, xBasisAction,
      layout.present_ne_equal, layout.present_ne_good, layout.equal_ne_good,
      layout.equal_ne_good.symm, layout.good_ne_other]

/-- present-other flagは、指定時にpresentかつ等値である場合だけ反転する。 -/
theorem membershipSlotCircuit_presentOther_value
    {ancillaQubits systemQubits : Nat}
    (moved word equalWork andScratch :
      List (Wire ancillaQubits systemQubits))
    (presentFlag equalFlag goodFlag presentOtherFlag :
      Wire ancillaQubits systemQubits)
    (recordPresentOther : Bool)
    (input : JointBasis ancillaQubits systemQubits)
    (layout : MembershipSlotLayout moved word equalWork andScratch
      presentFlag equalFlag goodFlag presentOtherFlag)
    (clean : MembershipSlotClean equalWork andScratch input)
    (equal_zero : input equalFlag = false) :
    (membershipSlotCircuit moved word equalWork andScratch presentFlag equalFlag
      goodFlag presentOtherFlag recordPresentOther).runBasis
        reversibleGatePermutation input presentOtherFlag =
      if recordPresentOther && input presentFlag &&
          decide (readWires moved input = readWires word input) then
        !(input presentOtherFlag)
      else input presentOtherFlag := by
  rw [runBasis_membershipSlotCircuit moved word equalWork andScratch presentFlag
    equalFlag goodFlag presentOtherFlag recordPresentOther input layout clean]
  cases recordPresentOther <;>
    by_cases equalWords : readWires moved input = readWires word input <;>
    simp [equalWords, equal_zero, toffoliBasisAction, xBasisAction,
      layout.present_ne_equal, layout.present_ne_good, layout.equal_ne_good,
      layout.equal_ne_other.symm, layout.good_ne_other.symm]

end ReversibleCircuit

end ProbabilityGeneratorQProof
