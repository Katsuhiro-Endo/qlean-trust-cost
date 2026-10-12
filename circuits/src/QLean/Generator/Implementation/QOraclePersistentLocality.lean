import QLean.Generator.Implementation.QOracleEventComputeLocality

/-!
# Q oracle persistent compute の疎な局所性

compact decoder、slot presence、degree 条件を含む persistent compute 全体が、入力 register
と oracle work だけを参照することを回路構文木から証明する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- persistent compute が参照する入力 register と oracle work の support。 -/
def oraclePersistentSupport (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  input ++ diagonalOracleWorkWires p

/-- OR の可逆 XOR 回路は三 wire を含む support 内だけを使う。 -/
theorem circuitUsesOnly_reversibleOrXor_within
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (left right target : Wire ancillaQubits systemQubits)
    (leftMember : left ∈ support) (rightMember : right ∈ support)
    (targetMember : target ∈ support) :
    circuitUsesOnly support (reversibleOrXor left right target) := by
  exact ⟨circuitUsesOnly_safeCnot support left target leftMember targetMember,
    ⟨circuitUsesOnly_safeCnot support right target rightMember targetMember,
      circuitUsesOnly_safeToffoli support left right target leftMember rightMember
        targetMember⟩⟩

/-- suffix OR 回路は入力列と suffix 列を含む support 内だけを使う。 -/
theorem circuitUsesOnly_suffixOrCircuit_within
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits)) :
    ∀ (input suffix : List (Wire ancillaQubits systemQubits)),
      (∀ wire ∈ input, wire ∈ support) →
      (∀ wire ∈ suffix, wire ∈ support) →
      circuitUsesOnly support (suffixOrCircuit input suffix)
  | [], _, _, _ => by simp [suffixOrCircuit, circuitUsesOnly]
  | _ :: _, [], _, _ => by simp [suffixOrCircuit, circuitUsesOnly]
  | [inputLast], [suffixLast], inputMembers, suffixMembers => by
      exact circuitUsesOnly_safeCnot support inputLast suffixLast
        (inputMembers inputLast (by simp)) (suffixMembers suffixLast (by simp))
  | [inputLast], _ :: _ :: _, _, _ => by simp [suffixOrCircuit, circuitUsesOnly]
  | _ :: _ :: _, [_], _, _ => by simp [suffixOrCircuit, circuitUsesOnly]
  | inputHead :: inputNext :: inputTail,
      suffixHead :: suffixNext :: suffixTail, inputMembers, suffixMembers => by
      simp only [suffixOrCircuit, circuitUsesOnly]
      constructor
      · exact circuitUsesOnly_suffixOrCircuit_within support (inputNext :: inputTail)
          (suffixNext :: suffixTail)
          (by intro wire member; exact inputMembers wire (by simp [member]))
          (by intro wire member; exact suffixMembers wire (by simp [member]))
      · exact circuitUsesOnly_reversibleOrXor_within support inputHead suffixNext suffixHead
          (inputMembers inputHead (by simp))
          (suffixMembers suffixNext (by simp))
          (suffixMembers suffixHead (by simp))

/-- 一個の degree 境界回路は入力・suffix・flag の support 内だけを使う。 -/
theorem circuitUsesOnly_degreeBoundaryCircuit
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (wordWidth : Nat)
    (input suffix : List (Wire ancillaQubits systemQubits))
    (degree : Nat) (flag : Wire ancillaQubits systemQubits)
    (inputMembers : ∀ wire ∈ input, wire ∈ support)
    (suffixMembers : ∀ wire ∈ suffix, wire ∈ support)
    (flagMember : flag ∈ support) :
    circuitUsesOnly support
      (degreeBoundaryCircuit wordWidth input suffix degree flag) := by
  unfold degreeBoundaryCircuit
  dsimp only
  split
  · trivial
  · rename_i delimiter delimiterEq
    have delimiterMember : delimiter ∈ input := by
      rcases List.getElem?_eq_some_iff.mp delimiterEq with ⟨inBounds, equal⟩
      rw [← equal]
      exact List.getElem_mem inBounds
    split
    · exact circuitUsesOnly_safeCnot support delimiter flag
        (inputMembers delimiter delimiterMember) flagMember
    · rename_i later laterEq
      have laterMember : later ∈ suffix := by
        rcases List.getElem?_eq_some_iff.mp laterEq with ⟨inBounds, equal⟩
        rw [← equal]
        exact List.getElem_mem inBounds
      exact ⟨circuitUsesOnly_x support later (suffixMembers later laterMember),
        ⟨circuitUsesOnly_safeToffoli support delimiter later flag
            (inputMembers delimiter delimiterMember)
            (suffixMembers later laterMember) flagMember,
          circuitUsesOnly_x support later (suffixMembers later laterMember)⟩⟩

/-- degree 境界列は入力・suffix・全flag の support 内だけを使う。 -/
theorem circuitUsesOnly_degreeBoundarySequence
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (wordWidth : Nat)
    (input suffix : List (Wire ancillaQubits systemQubits)) :
    ∀ (degree : Nat) (flags : List (Wire ancillaQubits systemQubits)),
      (∀ wire ∈ input, wire ∈ support) →
      (∀ wire ∈ suffix, wire ∈ support) →
      (∀ wire ∈ flags, wire ∈ support) →
      circuitUsesOnly support
        (degreeBoundarySequence wordWidth input suffix degree flags)
  | _, [], _, _, _ => by simp [degreeBoundarySequence, circuitUsesOnly]
  | degree, flag :: flags, inputMembers, suffixMembers, flagMembers => by
      exact ⟨circuitUsesOnly_degreeBoundaryCircuit support wordWidth input suffix
          degree flag inputMembers suffixMembers (flagMembers flag (by simp)),
        circuitUsesOnly_degreeBoundarySequence support wordWidth input suffix
          (degree + 1) flags inputMembers suffixMembers
          (by intro wire member; exact flagMembers wire (by simp [member]))⟩

/-- degree decode は入力・suffix・degree flag の support 内だけを使う。 -/
theorem circuitUsesOnly_xorDelimiterDegreeOneHotIntoTargetsCircuit
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (wordWidth : Nat)
    (input suffix flags : List (Wire ancillaQubits systemQubits))
    (inputMembers : ∀ wire ∈ input, wire ∈ support)
    (suffixMembers : ∀ wire ∈ suffix, wire ∈ support)
    (flagMembers : ∀ wire ∈ flags, wire ∈ support) :
    circuitUsesOnly support (xorDelimiterDegreeOneHotIntoTargetsCircuit wordWidth input suffix flags) := by
  apply circuitUsesOnly_computeUseUncompute
  · exact circuitUsesOnly_suffixOrCircuit_within support input suffix
      inputMembers suffixMembers
  · exact circuitUsesOnly_degreeBoundarySequence support wordWidth input suffix 0
      flags inputMembers suffixMembers flagMembers

/-- slot presence の内部再帰は degree・present wire の support 内だけを使う。 -/
theorem circuitUsesOnly_xorDegreeSuffixParityIntoSlotPresenceCircuit
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (degreeFlags : List (Wire ancillaQubits systemQubits)) :
    ∀ (slot : Nat) (presentFlags : List (Wire ancillaQubits systemQubits)),
      (∀ wire ∈ degreeFlags, wire ∈ support) →
      (∀ wire ∈ presentFlags, wire ∈ support) →
      circuitUsesOnly support (xorDegreeSuffixParityIntoSlotPresenceCircuit degreeFlags slot presentFlags)
  | _, [], _, _ => by simp [xorDegreeSuffixParityIntoSlotPresenceCircuit, circuitUsesOnly]
  | slot, present :: presents, degreeMembers, presentMembers => by
      constructor
      · apply circuitUsesOnly_sequence
        intro circuit circuitMember
        rcases List.mem_map.mp circuitMember with ⟨degree, degreeMember, rfl⟩
        exact circuitUsesOnly_safeCnot support degree present
          (degreeMembers degree (List.mem_of_mem_drop degreeMember))
          (presentMembers present (by simp))
      · exact circuitUsesOnly_xorDegreeSuffixParityIntoSlotPresenceCircuit support degreeFlags (slot + 1)
          presents degreeMembers
          (by intro wire member; exact presentMembers wire (by simp [member]))

/-- slot presence 全体は degree・present wire の support 内だけを使う。 -/
theorem circuitUsesOnly_slotPresenceCircuit
    {ancillaQubits systemQubits : Nat}
    (support : List (Wire ancillaQubits systemQubits))
    (degreeFlags presentFlags : List (Wire ancillaQubits systemQubits))
    (degreeMembers : ∀ wire ∈ degreeFlags, wire ∈ support)
    (presentMembers : ∀ wire ∈ presentFlags, wire ∈ support) :
    circuitUsesOnly support (slotPresenceCircuit degreeFlags presentFlags) := by
  exact circuitUsesOnly_xorDegreeSuffixParityIntoSlotPresenceCircuit support degreeFlags 0 presentFlags
    degreeMembers presentMembers

/-- compact decoder の局所 support は persistent support に含まれる。 -/
theorem decoderLegalitySupportFor_subset_persistent
    (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) :
    ∀ wire ∈ decoderLegalitySupportFor p input,
      wire ∈ oraclePersistentSupport p input := by
  intro wire member
  rcases (by
    simpa only [decoderLegalitySupportFor, List.mem_append, or_assoc] using member) with
    inputMember | suffixMember | degreeMember | compareMember | andMember
  · exact List.mem_append_left _ inputMember
  · apply List.mem_append_right input
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).candidate
    simpa [decoderSuffixWires, RegisterSlice.wireList] using
      List.mem_of_mem_take suffixMember
  · apply List.mem_append_right input
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).degree
    simpa [oracleDegreeWires, RegisterSlice.wireList] using degreeMember
  · apply List.mem_append_right input
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).compareWork
    simpa [oracleCompareWorkWires, RegisterSlice.wireList] using compareMember
  · apply List.mem_append_right input
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).andWork
    simpa [oracleAndWorkWires, RegisterSlice.wireList] using andMember

/-- compact decoder 全体は入力 register と oracle work だけを使う。 -/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_usesOnly
    (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) :
    circuitUsesOnly (oraclePersistentSupport p input)
      (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p input) := by
  let support := oraclePersistentSupport p input
  have inputMembers : ∀ wire ∈ input, wire ∈ support := by
    intro wire member
    exact List.mem_append_left _ member
  have workMembers : ∀ wire ∈ diagonalOracleWorkWires p,
      wire ∈ support := by
    intro wire member
    exact List.mem_append_right input member
  have suffixMembers : ∀ wire ∈ decoderSuffixWires p, wire ∈ support := by
    intro wire member
    apply workMembers
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).candidate
    simpa [decoderSuffixWires, RegisterSlice.wireList] using
      List.mem_of_mem_take member
  have degreeMembers : ∀ wire ∈ oracleDegreeWires p, wire ∈ support := by
    intro wire member
    apply workMembers
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).degree
    simpa [oracleDegreeWires, RegisterSlice.wireList] using member
  have degreeDecodeUses : circuitUsesOnly support
      (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth input (decoderSuffixWires p)
        (oracleDegreeWires p)) :=
    circuitUsesOnly_xorDelimiterDegreeOneHotIntoTargetsCircuit support p.wordWidth input
      (decoderSuffixWires p) (oracleDegreeWires p)
      inputMembers suffixMembers degreeMembers
  have legalityComputeUses : circuitUsesOnly support
      (decoderLegalityCompute
        (splitSystemWords p.wordWidth p.K input)
        (oracleDegreeWires p) (decoderLessWires p) (decoderNeedWires p)
        (decoderGoodWires p) (oracleCompareWorkWires p)
        (decoderAndScratchWires p) (decoderDegreeValidWire p)
        (decoderLegalTemporaryWire p)) := by
    apply circuitUsesOnly_mono
      (decoderLegalitySupportFor_subset_persistent p input)
    exact decoderLegalityCompute_usesOnly_input p input
  have temporaryMember : decoderLegalTemporaryWire p ∈ support := by
    apply workMembers
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).andWork
    have member := decoderLegalTemporary_mem_andWork p
    simpa [oracleAndWorkWires, RegisterSlice.wireList] using member
  have legalMember : oracleLegalWire p ∈ support :=
    workMembers _ (oracleLegalWire_mem_diagonalOracleWorkWires p)
  change circuitUsesOnly support
    (.seq (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth input (decoderSuffixWires p)
      (oracleDegreeWires p))
      (Circuit.computeUseUncompute id
        (decoderLegalityCompute
          (splitSystemWords p.wordWidth p.K input)
          (oracleDegreeWires p) (decoderLessWires p) (decoderNeedWires p)
          (decoderGoodWires p) (oracleCompareWorkWires p)
          (decoderAndScratchWires p) (decoderDegreeValidWire p)
          (decoderLegalTemporaryWire p))
        (safeCnot (decoderLegalTemporaryWire p) (oracleLegalWire p))))
  exact ⟨degreeDecodeUses,
    circuitUsesOnly_computeUseUncompute support _ _ legalityComputeUses
      (circuitUsesOnly_safeCnot support _ _ temporaryMember legalMember)⟩

/-- persistent compute 全体は入力 register と oracle work だけを使う。 -/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_usesOnly
    (p : QParameters)
    (input : List (Wire p.ancillaWidth p.systemWidth)) (rowMode : Bool) :
    circuitUsesOnly (oraclePersistentSupport p input)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p input rowMode) := by
  let support := oraclePersistentSupport p input
  have workMembers : ∀ wire ∈ diagonalOracleWorkWires p,
      wire ∈ support := by
    intro wire member
    exact List.mem_append_right input member
  have degreeMembers : ∀ wire ∈ oracleDegreeWires p, wire ∈ support := by
    intro wire member
    apply workMembers
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).degree
    simpa [oracleDegreeWires, RegisterSlice.wireList] using member
  have presentMembers : ∀ wire ∈ oraclePresentWires p, wire ∈ support := by
    intro wire member
    apply workMembers
    apply diagonalOracleSlice_subset_work p (OracleWorkLayout.canonical p).present
    simpa [oraclePresentWires, RegisterSlice.wireList] using member
  have conditionMember : oracleDegreeConditionWire p ∈ support :=
    workMembers _ (by
      apply diagonalOracleSlice_subset_work p
        (OracleWorkLayout.canonical p).degreeCondition
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).degreeCondition).ancillaWire 0 ∈ _
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
  have oneMember : oracleOneWire p ∈ support :=
    workMembers _ (by
      apply diagonalOracleSlice_subset_work p
        (OracleWorkLayout.canonical p).constantOne
      change (QLayout.oracleSlice
        (OracleWorkLayout.canonical p).constantOne).ancillaWire 0 ∈ _
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩)
  change circuitUsesOnly support
    (.seq (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p input)
      (.seq (slotPresenceCircuit (oracleDegreeWires p) (oraclePresentWires p))
        (.seq (Circuit.sequence <|
          (if rowMode then (oracleDegreeWires p).take (p.K - 1)
            else (oracleDegreeWires p).drop 1).map fun flag =>
              safeCnot flag (oracleDegreeConditionWire p))
          (.gate (.x (oracleOneWire p))))))
  refine ⟨xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_usesOnly p input,
    ⟨circuitUsesOnly_slotPresenceCircuit support (oracleDegreeWires p)
        (oraclePresentWires p) degreeMembers presentMembers, ?_⟩⟩
  constructor
  · apply circuitUsesOnly_sequence
    intro circuit circuitMember
    rcases List.mem_map.mp circuitMember with ⟨flag, flagMember, rfl⟩
    apply circuitUsesOnly_safeCnot support flag (oracleDegreeConditionWire p)
    · apply degreeMembers
      split at flagMember
      · exact List.mem_of_mem_take flagMember
      · exact List.mem_of_mem_drop flagMember
    · exact conditionMember
  · exact circuitUsesOnly_x support (oracleOneWire p) oneMember

/-- canonical column persistent compute は column key と oracle work だけを使う。 -/
theorem columnOraclePersistentCompute_usesOnly (p : QParameters) :
    circuitUsesOnly (columnKeyWires p ++ diagonalOracleWorkWires p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false) := by
  exact computeSharedDecoderPresenceParityAndOneFlagsCircuit_usesOnly p (columnKeyWires p) false

/-- canonical row persistent compute は system と oracle work だけを使う。 -/
theorem rowOraclePersistentCompute_usesOnly (p : QParameters) :
    circuitUsesOnly (systemWires p ++ diagonalOracleWorkWires p)
      (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true) := by
  exact computeSharedDecoderPresenceParityAndOneFlagsCircuit_usesOnly p (systemWires p) true

end ReversibleCircuit

end ProbabilityGeneratorQProof
