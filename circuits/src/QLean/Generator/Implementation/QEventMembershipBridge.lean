import QLean.Generator.Implementation.QSortedCandidateBridge

/-!
# event membership と合法配置の橋渡し

membership 回路が保持する slot ごとの Bool 条件を、合法配置上の集合 membership と
`erase source` membership へ接続する。全配置や全基底は列挙しない。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 合法配置を保持した event membership 直前状態の数学的な読出し仕様。 -/
structure ConfigurationMembershipInput (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p) (moved : QSite p)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- present bit は配置の粒子数未満の slot だけで真である。 -/
  present : ∀ slot : Fin p.K,
    input (oraclePresentWireAt p slot) =
      decide (slot.val < configuration.1.card)
  /-- 有効 slot の register word は対応する site word である。 -/
  active_word : ∀ (slot : Fin p.K)
    (active : slot.val < configuration.1.card),
    readWires (registerWordAt p register slot) input =
      siteWordBits p (configuration.siteAt ⟨slot.val, active⟩)
  /-- moved register は物理移動先 site word である。 -/
  moved_word : readWires (oracleMovedWires p) input = siteWordBits p moved

/-- candidate word は data 部分と末尾 marker wire の連結として分解できる。 -/
theorem candidateWordAt_eq_data_append_marker
    (p : QParameters) (word : Fin p.sortWordCount) :
    candidateWordAt p word =
      (candidateWordAt p word).take p.wordWidth ++
        [candidateMarkerWire p word] := by
  apply List.ext_get
  · simp
  · intro index leftBound rightBound
    by_cases dataIndex : index < p.wordWidth
    · simp [dataIndex]
    · have markerIndex : index = p.wordWidth := by
        simp at leftBound
        omega
      subst index
      simp [candidateWordAt, candidateMarkerWire]

/-- candidate の data と marker の読出しから marker 込み自然数値を復元する。 -/
theorem qCandidateValue_eq_of_data_marker
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (word : Fin p.sortWordCount) (data : List Bool) (marker : Bool)
    (dataRead : readWires ((candidateWordAt p word).take p.wordWidth) input = data)
    (markerRead : input (candidateMarkerWire p word) = marker) :
    qCandidateValue p input word = littleEndianNat (data ++ [marker]) := by
  unfold qCandidateValue
  rw [candidateWordAt_eq_data_append_marker, readWires]
  simp only [List.map_append, List.map_singleton]
  change List.map input ((candidateWordAt p word).take p.wordWidth) = data
    at dataRead
  rw [dataRead, markerRead]

/--
合法配置を表す system register と clean candidate 領域から候補生成正本を実行すると、
全 candidate 自然数は配置の canonical candidate 関数に点ごとに一致する。
-/
theorem qCandidateValue_runBasis_prepareCandidates_register_configuration
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CandidateInputLayout p register)
    (configuration : QConfiguration p) (moved : QSite p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p register
      configuration moved input)
    (clean : CandidateRegionClean p input) :
    qCandidateValue p
        ((xorConfigurationIntoCandidateRegisterCircuit p register).runBasis
          reversibleGatePermutation input) =
      configurationCandidateValue p configuration := by
  rw [runBasis_xorConfigurationIntoCandidateRegisterCircuit p register layout input]
  funext word
  by_cases physical : word.val < p.K
  · let slot : Fin p.K := ⟨word.val, physical⟩
    have wordEqual : slotToSortWord p slot = word := by
      apply Fin.ext
      rfl
    by_cases active : word.val < configuration.1.card
    · have presentTrue : input (oraclePresentWireAt p slot) = true := by
        rw [specification.present slot]
        exact decide_eq_true active
      have dataRead := configurationToCandidateRegisterXorSpec_active_data p register
        layout input clean slot
      have markerRead := configurationToCandidateRegisterXorSpec_active_marker p register
        layout input clean slot
      rw [wordEqual] at dataRead markerRead
      rw [presentTrue] at dataRead
      simp at dataRead
      rw [specification.active_word slot active] at dataRead
      rw [presentTrue] at markerRead
      simp only [Bool.not_true] at markerRead
      rw [configurationCandidateValue_active p configuration word active]
      rw [qCandidateValue_eq_of_data_marker p
        (ConfigurationToCandidateRegisterXorSpec p register input) word
        (siteWordBits p (configuration.siteAt ⟨word.val, active⟩)) false
        dataRead markerRead]
      simp [littleEndianNat_append, littleEndianNat_siteWordBits, littleEndianNat]
    · have inactive : configuration.1.card ≤ word.val :=
        Nat.le_of_not_gt active
      have presentFalse : input (oraclePresentWireAt p slot) = false := by
        rw [specification.present slot]
        exact decide_eq_false active
      have dataRead := configurationToCandidateRegisterXorSpec_active_data p register
        layout input clean slot
      have markerRead := configurationToCandidateRegisterXorSpec_active_marker p register
        layout input clean slot
      rw [wordEqual] at dataRead markerRead
      rw [presentFalse] at dataRead
      simp at dataRead
      rw [presentFalse] at markerRead
      simp only [Bool.not_false] at markerRead
      rw [configurationCandidateValue_padding p configuration word inactive]
      rw [qCandidateValue_eq_of_data_marker p
        (ConfigurationToCandidateRegisterXorSpec p register input) word
        (List.replicate p.wordWidth false) true dataRead markerRead]
      simp [littleEndianNat_append, littleEndianNat]
  · have padding : p.K ≤ word.val := Nat.le_of_not_gt physical
    have configurationPadding : configuration.1.card ≤ word.val :=
      le_trans configuration.2.2 padding
    have dataRead := configurationToCandidateRegisterXorSpec_padding_data p register input clean
      word padding
    have markerRead := configurationToCandidateRegisterXorSpec_padding_marker p
      register input clean word padding
    rw [configurationCandidateValue_padding p configuration word
      configurationPadding]
    rw [qCandidateValue_eq_of_data_marker p
      (ConfigurationToCandidateRegisterXorSpec p register input) word
      (List.replicate p.wordWidth false) true dataRead markerRead]
    simp [littleEndianNat_append, littleEndianNat]

/-- system register についての candidate 生成定理は一般 register 版の直接の系である。 -/
theorem qCandidateValue_runBasis_prepareCandidates_configuration
    (p : QParameters) (configuration : QConfiguration p) (moved : QSite p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p (systemWires p)
      configuration moved input)
    (clean : CandidateRegionClean p input) :
    qCandidateValue p
        ((xorConfigurationIntoCandidateRegisterCircuit p (systemWires p)).runBasis
          reversibleGatePermutation input) =
      configurationCandidateValue p configuration := by
  exact qCandidateValue_runBasis_prepareCandidates_register_configuration p
    (systemWires p) (systemWires_candidateInputLayout p) configuration moved input
      specification clean

/-- 合法配置の読出し仕様から、present word の slot 単射性が従う。 -/
theorem ConfigurationMembershipInput.distinctPresentWords
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p) (moved : QSite p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p register configuration moved
      input) :
    DistinctPresentWords p register input := by
  intro left right leftPresent rightPresent wordsEqual
  have leftValue := specification.present left
  have rightValue := specification.present right
  rw [leftPresent] at leftValue
  rw [rightPresent] at rightValue
  have leftActive : left.val < configuration.1.card :=
    of_decide_eq_true leftValue.symm
  have rightActive : right.val < configuration.1.card :=
    of_decide_eq_true rightValue.symm
  rw [specification.active_word left leftActive,
    specification.active_word right rightActive] at wordsEqual
  have sitesEqual :
      configuration.siteAt ⟨left.val, leftActive⟩ =
        configuration.siteAt ⟨right.val, rightActive⟩ :=
    siteWordBits_injective p wordsEqual
  have slotsEqual := configuration.siteAt_injective sitesEqual
  exact Fin.ext
    (congrArg (fun index : Fin configuration.1.card => index.val) slotsEqual)

/-- 合法配置状態では、一 slot の membership 条件は対応 site との一致判定である。 -/
theorem membershipSlotMatches_configuration
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p) (moved : QSite p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p register configuration moved input)
    (slot : Fin p.K) :
    membershipSlotMatches p register slot input =
      decide (∃ active : slot.val < configuration.1.card,
        configuration.siteAt ⟨slot.val, active⟩ = moved) := by
  unfold membershipSlotMatches
  rw [specification.present slot, specification.moved_word]
  by_cases active : slot.val < configuration.1.card
  · have activeDecision : decide (slot.val < configuration.1.card) = true :=
      decide_eq_true active
    rw [activeDecision, Bool.true_and]
    rw [specification.active_word slot active]
    rw [decide_eq_decide]
    constructor
    · intro wordsEqual
      exact ⟨active, (siteWordBits_injective p wordsEqual).symm⟩
    · rintro ⟨otherActive, sitesEqual⟩
      have proofEqual : otherActive = active := Subsingleton.elim _ _
      subst otherActive
      simp [sitesEqual]
  · have inactiveDecision : decide (slot.val < configuration.1.card) = false :=
      decide_eq_false active
    rw [inactiveDecision, Bool.false_and]
    have noWitness : ¬∃ otherActive : slot.val < configuration.1.card,
        configuration.siteAt ⟨slot.val, otherActive⟩ = moved := by
      rintro ⟨otherActive, _⟩
      exact active otherActive
    simp [noWitness]

/-- 配置 membership は `Fin K` 内の有効 slot に site が存在することと同値である。 -/
theorem configuration_mem_iff_exists_physical_slot
    {p : QParameters} (configuration : QConfiguration p) (site : QSite p) :
    site ∈ configuration.1 ↔
      ∃ slot : Fin p.K, ∃ active : slot.val < configuration.1.card,
        configuration.siteAt ⟨slot.val, active⟩ = site := by
  constructor
  · intro member
    let smallSlot :=
      (configuration.1.orderIsoOfFin rfl).symm ⟨site, member⟩
    have belowK : smallSlot.val < p.K :=
      lt_of_lt_of_le smallSlot.isLt configuration.2.2
    refine ⟨⟨smallSlot.val, belowK⟩, smallSlot.isLt, ?_⟩
    exact congrArg Subtype.val
      ((configuration.1.orderIsoOfFin rfl).apply_symm_apply ⟨site, member⟩)
  · rintro ⟨slot, active, equal⟩
    rw [← equal]
    exact ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2

/-- 合法配置状態の absent 条件は、移動先が配置に含まれないことと一致する。 -/
theorem noMembershipMatch_configuration
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p) (moved : QSite p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p register configuration moved input) :
    noMembershipMatch p register input = decide (moved ∉ configuration.1) := by
  by_cases member : moved ∈ configuration.1
  · have witness :=
      (configuration_mem_iff_exists_physical_slot configuration moved).mp member
    rcases witness with ⟨slot, active, siteEqual⟩
    have slotMatches : membershipSlotMatches p register slot input = true := by
      rw [membershipSlotMatches_configuration p register configuration moved input
        specification slot]
      exact decide_eq_true ⟨active, siteEqual⟩
    have noMatchFalse : noMembershipMatch p register input = false := by
      apply Bool.eq_false_of_not_eq_true
      intro allTrue
      have slotFalse := (List.all_eq_true.mp allTrue) slot
        (List.mem_finRange slot)
      simp [slotMatches] at slotFalse
    rw [noMatchFalse]
    simp [member]
  · have noMatchTrue : noMembershipMatch p register input = true := by
      apply List.all_eq_true.mpr
      intro slot _
      rw [membershipSlotMatches_configuration p register configuration moved input
        specification slot]
      have noWitness : ¬∃ active : slot.val < configuration.1.card,
          configuration.siteAt ⟨slot.val, active⟩ = moved := by
        rintro ⟨active, siteEqual⟩
        apply member
        rw [← siteEqual]
        exact ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
      simp [noWitness]
    rw [noMatchTrue]
    simp [member]

/--
選択 source slot が既知なら、present-other 条件は移動先が source 消去後集合に
属することと厳密に一致する。
-/
theorem hasMatchingOther_configuration_erase
    (p : QParameters)
    (register : List (Wire p.ancillaWidth p.systemWidth))
    (configuration : QConfiguration p) (source moved : QSite p)
    (selectedSlot : Fin p.K)
    (selectedActive : selectedSlot.val < configuration.1.card)
    (selectedSite :
      configuration.siteAt ⟨selectedSlot.val, selectedActive⟩ = source)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ConfigurationMembershipInput p register configuration moved input) :
    hasMatchingOther p register selectedSlot true input =
      decide (moved ∈ configuration.1.erase source) := by
  by_cases collision : moved ∈ configuration.1.erase source
  · rcases Finset.mem_erase.mp collision with ⟨movedNeSource, movedMember⟩
    rcases (configuration_mem_iff_exists_physical_slot configuration moved).mp
        movedMember with ⟨slot, active, siteEqual⟩
    have slotNe : slot ≠ selectedSlot := by
      intro equal
      subst slot
      have proofEqual : active = selectedActive := Subsingleton.elim _ _
      subst active
      exact movedNeSource (siteEqual.symm.trans selectedSite)
    have slotMatches : membershipSlotMatches p register slot input = true := by
      rw [membershipSlotMatches_configuration p register configuration moved input
        specification slot]
      exact decide_eq_true ⟨active, siteEqual⟩
    have otherTrue :
        membershipOtherMatch p register selectedSlot true slot input = true := by
      simp [membershipOtherMatch, slotNe, slotMatches]
    have anyTrue : hasMatchingOther p register selectedSlot true input = true := by
      unfold hasMatchingOther
      rw [List.any_eq_true]
      refine ⟨true, ?_, rfl⟩
      exact List.mem_map.mpr ⟨slot, List.mem_finRange slot, otherTrue⟩
    rw [anyTrue]
    exact (decide_eq_true collision).symm
  · have anyFalse : hasMatchingOther p register selectedSlot true input = false := by
      unfold hasMatchingOther
      apply List.any_eq_false.mpr
      intro value valueMember valueTrue
      rcases List.mem_map.mp valueMember with ⟨slot, _, slotValue⟩
      subst value
      have otherTrue :
          membershipOtherMatch p register selectedSlot true slot input = true := by
        exact valueTrue
      have parts : slot ≠ selectedSlot ∧
          membershipSlotMatches p register slot input = true := by
        simpa [membershipOtherMatch] using otherTrue
      rw [membershipSlotMatches_configuration p register configuration moved input
        specification slot] at parts
      have witness := of_decide_eq_true parts.2
      rcases witness with ⟨active, siteEqual⟩
      have movedMember : moved ∈ configuration.1 := by
        rw [← siteEqual]
        exact ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
      have movedNeSource : moved ≠ source := by
        intro movedEqual
        have siteAtEqual :
            configuration.siteAt ⟨slot.val, active⟩ =
              configuration.siteAt ⟨selectedSlot.val, selectedActive⟩ := by
          rw [siteEqual, movedEqual, selectedSite]
        have smallSlotsEqual := configuration.siteAt_injective siteAtEqual
        have valuesEqual : slot.val = selectedSlot.val :=
          congrArg (fun index : Fin configuration.1.card => index.val)
            smallSlotsEqual
        exact parts.1 (Fin.ext valuesEqual)
      exact collision (Finset.mem_erase.mpr ⟨movedNeSource, movedMember⟩)
    rw [anyFalse]
    exact (decide_eq_false collision).symm

end ReversibleCircuit

end ProbabilityGeneratorQProof
