import QLean.Generator.Implementation.QWriteSortedBitlistBridge
import QLean.Generator.Analysis.QOracleReference

/-!
# moved selector と合法配置の接続

合法配置の canonical candidate 列では、moved site と一致する有効 slot はただ一つである。
この事実から、moved-selector の有限 fold 全体を、その slot の selector 定数を一度だけ
XOR する純粋参照式へ簡約する。証明は有限リストの構造帰納法だけを用いる。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- 全 slot が無効なら moved-selector の有限 fold は入力 bit 列を保存する。 -/
theorem xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_eq_self_of_all_disabled
    (p : QParameters) (offset : Nat) (slots : List (Fin p.K))
    (input : JointBasis p.ancillaWidth p.systemWidth) (bits : List Bool)
    (disabled : ∀ slot ∈ slots, movedSelectorSlotEnabled p slot input = false) :
    xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset slots input bits = bits := by
  induction slots with
  | nil => simp
  | cons slot slots inductionHypothesis =>
      rw [xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_cons_disabled p offset slot slots input bits
        (disabled slot (by simp))]
      exact inductionHypothesis (fun tail tailMember =>
        disabled tail (by simp [tailMember]))

/--
`slots` 内で `selected` だけが有効なら、moved-selector の有限 fold はその定数 XOR 一回に
一致する。
-/
theorem xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_eq_single_enabled
    (p : QParameters) (offset : Nat) (slots : List (Fin p.K))
    (input : JointBasis p.ancillaWidth p.systemWidth) (bits : List Bool)
    (selected : Fin p.K) (selectedMember : selected ∈ slots)
    (nodup : slots.Nodup)
    (enabled : ∀ slot ∈ slots,
      movedSelectorSlotEnabled p slot input = decide (slot = selected)) :
    xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom p offset slots input bits =
      controlledXorConstantBits true (6 * selected.val + offset) 0 bits := by
  induction slots with
  | nil => simp at selectedMember
  | cons slot slots inductionHypothesis =>
      have slotEnabled := enabled slot (by simp)
      by_cases headSelected : slot = selected
      · subst slot
        rw [xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_cons]
        rw [slotEnabled]
        simp only [decide_true]
        apply xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_eq_self_of_all_disabled
        intro tail tailMember
        rw [enabled tail (by simp [tailMember])]
        have tailNe : tail ≠ selected := by
          intro equal
          subst tail
          exact (List.nodup_cons.mp nodup).1 tailMember
        simp [tailNe]
      · rw [xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_cons_disabled p offset slot slots input bits]
        · apply inductionHypothesis
          · simp only [List.mem_cons] at selectedMember
            exact selectedMember.resolve_left (fun selectedHead =>
              headSelected selectedHead.symm)
          · exact (List.nodup_cons.mp nodup).2
          · intro tail tailMember
            exact enabled tail (by simp [tailMember])
        · rw [slotEnabled]
          simp [headSelected]

/-- `slotOfMember` が返す slot を配置内で読むと元の site に戻る。 -/
theorem configuration_siteAt_slotOfMember
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (active : (slotOfMember configuration source member).val <
      configuration.1.card) :
    configuration.siteAt
      ⟨(slotOfMember configuration source member).val, active⟩ = source := by
  unfold slotOfMember QConfiguration.siteAt
  simp

/--
合法配置の有効 slot が指す site は、`slotOfMember` が返す物理 slot と同じである。
-/
theorem physicalSlot_eq_slotOfMember_of_siteAt_eq
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (active : slot.val < configuration.1.card)
    (source : QSite p) (member : source ∈ configuration.1)
    (sourceAt : configuration.siteAt ⟨slot.val, active⟩ = source) :
    slot = slotOfMember configuration source member := by
  have canonicalAt := configurationSlot_slotOfMember configuration source member
  unfold configurationSlot? at canonicalAt
  split at canonicalAt
  · rename_i canonicalActive
    have entryEqual := Option.some.inj canonicalAt
    have canonicalSite :
        configuration.siteAt
            ⟨(slotOfMember configuration source member).val, canonicalActive⟩ =
          source := congrArg Subtype.val entryEqual
    have smallSlotsEqual := configuration.siteAt_injective
      (sourceAt.trans canonicalSite.symm)
    apply Fin.ext
    exact congrArg
      (fun index : Fin configuration.1.card => index.val) smallSlotsEqual
  · simp at canonicalAt

/--
canonical candidate 値、branch、moved word が合法配置を表すとき、一つの物理 slot の
moved-selector 制御値は `slotOfMember` との一致判定そのものである。
-/
theorem movedSelectorSlotEnabled_configuration
    (p : QParameters) (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchTrue : input (oracleBranchWire p) = true)
    (candidateValues : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (movedWord : readWires (oracleMovedWires p) input = siteWordBits p source)
    (slot : Fin p.K) :
    movedSelectorSlotEnabled p slot input =
      decide (slot = slotOfMember configuration source member) := by
  by_cases active : slot.val < configuration.1.card
  · have dataWord := candidateData_eq_siteWordBits_of_value_eq p configuration
      input candidateValues (slotToSortWord p slot) (by
        simpa [slotToSortWord] using active)
    have dataWord' :
        readWires
            ((candidateWordAt p (slotToSortWord p slot)).take p.wordWidth) input =
          siteWordBits p (configuration.siteAt ⟨slot.val, active⟩) := by
      simpa [slotToSortWord] using dataWord
    have markerFalse := candidateMarker_false_of_value_eq p configuration input
      candidateValues (slotToSortWord p slot) (by
        simpa [slotToSortWord] using active)
    unfold movedSelectorSlotEnabled
    rw [movedWord, dataWord', branchTrue, markerFalse]
    simp only [Bool.true_and, Bool.not_false, Bool.and_true]
    rw [decide_eq_decide]
    constructor
    · intro wordsEqual
      apply physicalSlot_eq_slotOfMember_of_siteAt_eq configuration slot active
        source member
      exact (siteWordBits_injective p wordsEqual.symm)
    · intro slotsEqual
      subst slot
      exact congrArg (siteWordBits p)
        (configuration_siteAt_slotOfMember configuration source member active).symm
  · have padding : configuration.1.card ≤ (slotToSortWord p slot).val := by
      simpa [slotToSortWord] using Nat.le_of_not_gt active
    have markerTrue := candidateMarker_true_of_value_eq_padding p configuration input
      candidateValues (slotToSortWord p slot) padding
    have slotNe : slot ≠ slotOfMember configuration source member := by
      intro equal
      subst slot
      unfold slotOfMember at active
      exact active ((configuration.1.orderIsoOfFin rfl).symm
        ⟨source, member⟩).isLt
    simp [movedSelectorSlotEnabled, branchTrue, markerTrue, slotNe]

/--
合法配置の canonical candidate 列では、moved-selector 全体は source の canonical slot と
offset からなる selector 定数を一度だけ XOR する。
-/
theorem xorMovedMemberPositionIntoSelectorOutputCircuitBitsReference_configuration
    (p : QParameters) (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (offset : Nat) (outputSelector : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (branchTrue : input (oracleBranchWire p) = true)
    (candidateValues : qCandidateValue p input =
      configurationCandidateValue p configuration)
    (movedWord : readWires (oracleMovedWires p) input = siteWordBits p source) :
    movedMemberPositionSelectorOutputXorReference p offset outputSelector input =
      controlledXorConstantBits true
        (6 * (slotOfMember configuration source member).val + offset) 0
        (readWires outputSelector input) := by
  unfold movedMemberPositionSelectorOutputXorReference
  apply xorMovedMemberPositionIntoSelectorOutputCircuitBitsReferenceFrom_eq_single_enabled p offset
    (List.finRange p.K) input (readWires outputSelector input)
    (slotOfMember configuration source member)
  · exact List.mem_finRange _
  · exact List.nodup_finRange p.K
  · intro slot _
    exact movedSelectorSlotEnabled_configuration p configuration source member input
      branchTrue candidateValues movedWord slot

end ReversibleCircuit

end ProbabilityGeneratorQProof
