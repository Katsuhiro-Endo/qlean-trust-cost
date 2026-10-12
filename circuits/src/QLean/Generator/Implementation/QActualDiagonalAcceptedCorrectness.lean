import QLean.Generator.Implementation.QActualSelectorPathCorrectness
import QLean.Generator.Implementation.QOracleColumnFullCorrectness
import QLean.Generator.Implementation.QOracleRowEventComplete
import QLean.Generator.Implementation.QReferenceOverlapCorrectness
import QLean.Generator.Implementation.QActualPhysicalEventAcceptedCorrectness

/-!
# Q 正本回路の対角受理 path

二つの対角 selector について、row・column oracle の完全な基底作用から最終基底を
逆追跡し、canonical column 初期基底と負号位相へ接続する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

open ReversibleCircuit

/--
非衝突 row predecessor が保持する site 集合を正方向へ更新すると、元の出力配置へ戻る。
-/
theorem eventOutput_replacementPredecessor_eq
    {p : QParameters} (output predecessor : QConfiguration p)
    (arrival source : QSite p) (direction : QDirection)
    (arrivalMember : arrival ∈ output.1) (sourceAbsent : source ∉ output.1)
    (sourceMember : source ∈ predecessor.1)
    (sitesEq : predecessor.1 = insert source (output.1.erase arrival))
    (movedEq : moveSite source direction = arrival) :
    eventOutput predecessor source direction = output := by
  apply Subtype.ext
  rw [eventOutput, updateConfiguration_sites_active predecessor
    (source, direction) sourceMember, sitesEq, movedEq]
  ext site
  simp only [Finset.mem_insert, Finset.mem_erase]
  constructor
  · intro member
    rcases member with equal | ⟨differentSource, member⟩
    · simpa [equal] using arrivalMember
    · rcases member with equal | ⟨differentArrival, outputMember⟩
      · exact (differentSource equal).elim
      · exact outputMember
  · intro outputMember
    by_cases equal : site = arrival
    · exact Or.inl equal
    · exact Or.inr ⟨by
        intro siteSource
        apply sourceAbsent
        simpa [siteSource] using outputMember, Or.inr ⟨equal, outputMember⟩⟩

/--
衝突 row predecessor が保持する site 集合を正方向へ更新すると、元の出力配置へ戻る。
-/
theorem eventOutput_collisionPredecessor_eq
    {p : QParameters} (output predecessor : QConfiguration p)
    (arrival source : QSite p) (direction : QDirection)
    (arrivalMember : arrival ∈ output.1) (sourceAbsent : source ∉ output.1)
    (sourceMember : source ∈ predecessor.1)
    (sitesEq : predecessor.1 = insert source output.1)
    (movedEq : moveSite source direction = arrival) :
    eventOutput predecessor source direction = output := by
  apply Subtype.ext
  rw [eventOutput, updateConfiguration_sites_active predecessor
    (source, direction) sourceMember, sitesEq, movedEq]
  ext site
  simp only [Finset.mem_insert, Finset.mem_erase]
  constructor
  · intro member
    rcases member with equal | ⟨differentSource, member⟩
    · simpa [equal] using arrivalMember
    · rcases member with equal | outputMember
      · exact (differentSource equal).elim
      · exact outputMember
  · intro outputMember
    exact Or.inr ⟨by
      intro siteSource
      apply sourceAbsent
      simpa [siteSource] using outputMember, Or.inr outputMember⟩

/--
物理 event として表せる row 参照値には、既存の event 回路完全性をそのまま適用できる。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_reference_some_of_event
    {p : QParameters} (output predecessor : QConfiguration p)
    (selector columnSelector : QSelector p)
    (source : QSite p) (member : source ∈ predecessor.1)
    (direction : QDirection)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOracleInputSpec p output selector input)
    (outputEq : eventOutput predecessor source direction = output)
    (selectorEq : rowSelectorForEvent predecessor source member direction = selector)
    (columnSelectorEq :
      selectorForEvent predecessor source member direction = columnSelector) :
    RowReferenceBranchResult p predecessor columnSelector input
      ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input) := by
  have eventSpec : RowOracleInputSpec p
      (eventOutput predecessor source direction)
      (rowSelectorForEvent predecessor source member direction) input := by
    simpa [outputEq, selectorEq] using specification
  have result := applyRowOracleReferenceAndRestoreWorkCircuit_physicalEvent_correct predecessor
    source member direction input eventSpec
  simpa [columnSelectorEq] using result

/--
正方向更新先・移動先・event offset が一致すれば、canonical row selector も一致する。
-/
theorem rowSelectorForEvent_eq_of_selected
    {p : QParameters} (output predecessor : QConfiguration p)
    (selector : QSelector p) (arrival source : QSite p)
    (arrivalMember : arrival ∈ output.1) (sourceMember : source ∈ predecessor.1)
    (direction : QDirection)
    (selected : configurationSlot? output (selectorSlot selector) =
      some ⟨arrival, arrivalMember⟩)
    (outputEq : eventOutput predecessor source direction = output)
    (movedEq : moveSite source direction = arrival)
    (offsetEq : eventOffset direction
      (eventCollision predecessor source direction) = selectorOffset selector) :
    rowSelectorForEvent predecessor source sourceMember direction = selector := by
  subst output
  subst arrival
  have slotEq : selectorSlot selector =
      slotOfMember (eventOutput predecessor source direction)
        (moveSite source direction) arrivalMember :=
    selectorSlot_eq_slotOfMember_of_selected
      (eventOutput predecessor source direction) (selectorSlot selector)
        (moveSite source direction) arrivalMember selected
  unfold rowSelectorForEvent
  dsimp only
  rw [offsetEq, ← slotEq]
  exact selectorOfSlotOffset_parts selector

/-- event offset が一致すれば、canonical column selector も一致する。 -/
theorem selectorForEvent_eq_of_offset
    {p : QParameters} (predecessor : QConfiguration p)
    (source : QSite p) (member : source ∈ predecessor.1)
    (direction : QDirection) (offset : Fin 6)
    (offsetEq : eventOffset direction
      (eventCollision predecessor source direction) = offset) :
    selectorForEvent predecessor source member direction =
      selectorOfSlotOffset (slotOfMember predecessor source member) offset := by
  unfold selectorForEvent
  simpa only [eventCollision] using congrArg
    (selectorOfSlotOffset (slotOfMember predecessor source member)) offsetEq

/--
Row 対角分岐は column-key・column-selector・key-signal 以外の任意 wire を入力値へ戻す。
-/
theorem rowDiagonalResultComputeUseUncomputeCircuit_outside_outputs_restored_actual
    (p : QParameters) (slot : Fin p.K) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideKey : wire ∉ columnKeyWires p)
    (outsideSelector : wire ∉ columnSelectorWires p)
    (outsideSignal : wire ≠ keySignalWire p) :
    (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input wire = input wire := by
  let compute := xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
    (6 * slot.val + copy.val)
  let computed := compute.runBasis reversibleGatePermutation input
  let used := (controlledXorRowDiagonalResultIntoOutputsCircuit p slot copy).runBasis
    reversibleGatePermutation computed
  have outputEq :
      (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
          reversibleGatePermutation input =
        restoreSupport (rowDiagonalComputeSupport p) input used := by
    simpa [computed, used, compute] using
      runBasis_rowDiagonalResultComputeUseUncomputeCircuit_restoreSupport p slot copy input
  by_cases supportMember : wire ∈ rowDiagonalComputeSupport p
  · rw [outputEq]
    exact restoreSupport_agrees_input (rowDiagonalComputeSupport p) input used
      wire supportMember
  · have useOutside : used wire = computed wire := by
      have systemDisjointKey :
          (systemWires p).Disjoint (columnKeyWires p) := by
        simpa [systemWires, topSystemWires, QLayout.systemWire,
          columnKeyWires_eq_topColumnKeyWires] using
            topSystemWires_disjoint_topColumnKeyWires p
      dsimp [used]
      simp only [controlledXorRowDiagonalResultIntoOutputsCircuit, runBasis_seq]
      rw [runBasis_safeCnot_outside (oracleBranchWire p) (keySignalWire p) wire
        (oracleBranchWire_ne_keySignalWire p) outsideSignal]
      rw [runBasis_controlledXorConstant_outside (oracleBranchWire p)
        (columnSelectorWires p) (6 * slot.val + copy.val) _
        (oracleBranchWire_not_mem_columnSelectorWires p) wire outsideSelector]
      exact runBasis_validatedControlledXorCopyLists_outside (oracleBranchWire p)
        (systemWires p) (columnKeyWires p) computed
        (systemWires_nodup p) (columnKeyWires_nodup p)
        (by simp) systemDisjointKey
        (oracleBranchWire_not_mem_systemWires p)
        (oracleBranchWire_not_mem_columnKeyWires p) wire outsideKey
    have computedOutside : computed wire = input wire := by
      dsimp [computed, compute]
      exact Circuit.runBasis_outside_of_usesOnly
        (rowDiagonalComputeSupport p)
        (xorSelectorMatchIntoBranchFlagCircuit p (rowSelectorWires p) slot
          (6 * slot.val + copy.val))
        (rowDiagonalCompute_usesOnly p slot copy) input wire supportMember
    rw [outputEq]
    exact (restoreSupport_outside (rowDiagonalComputeSupport p) input used wire
      supportMember).trans (useOutside.trans computedOutside)

/--
合法な active 対角 row 分岐は、同じ配置と selector の row 参照 XOR 仕様を満たす。
-/
theorem rowDiagonalResultComputeUseUncomputeCircuit_active_reference_actual
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (copy : Fin 2)
    (active : slot.val < configuration.1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOraclePersistentConditionsSpec p configuration
      (selectorOfSlotOffset slot
        ⟨copy.val, lt_trans copy.isLt (by decide)⟩) input) :
    let selector := selectorOfSlotOffset slot
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    RowReferenceBranchResult p configuration selector input
      ((rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input) := by
  dsimp only
  let selector := selectorOfSlotOffset slot
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  have selectorMatch : diagonalSelectorMatches (rowSelectorWires p)
      (6 * slot.val + copy.val) input = true := by
    simp [diagonalSelectorMatches, specification.selector_bits,
      selectorOfSlotOffset]
  have diagonalResult := rowDiagonalResultComputeUseUncomputeCircuit_active p slot copy input
    (by simpa [decide_eq_true active] using specification.diagonalClean slot)
    selectorMatch
  have supportRestored : BasisAgreeOn (rowEventBroadSupport p)
      ((rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
        reversibleGatePermutation input) input := by
    intro wire supportMember
    apply rowDiagonalResultComputeUseUncomputeCircuit_outside_outputs_restored_actual p slot copy
      input wire
    · intro keyMember
      exact (List.disjoint_left.mp (rowEventBroadSupport_disjoint_columnKey p))
        supportMember keyMember
    · intro selectorMember
      exact (List.disjoint_left.mp
        (rowEventBroadSupport_disjoint_columnSelector p)) supportMember
          selectorMember
    · intro equal
      subst wire
      exact keySignalWire_not_mem_rowEventBroadSupport p supportMember
  refine {
    column_key := ?_
    column_selector := ?_
    key_signal := ?_
    support_restored := supportRestored
    outside_restored := ?_ }
  · simpa [specification.system_bits] using diagonalResult.column_key
  · simpa [selector, selectorOfSlotOffset] using
      diagonalResult.column_selector
  · simpa using diagonalResult.key_signal
  · intro wire outsideKey outsideSelector outsideSignal
    exact rowDiagonalResultComputeUseUncomputeCircuit_outside_outputs_restored_actual p slot copy
      input wire outsideKey outsideSelector outsideSignal

/--
Canonical 対角 selector では、全 `6K` 分岐列と persistent uncompute を含む row oracle
全体が対角 row 参照仕様を満たす。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_diagonal_correct
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOracleInputSpec p configuration
      (selectorOfSlotOffset (slotOfMember configuration site member)
        ⟨copy.val, lt_trans copy.isLt (by decide)⟩) input) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    RowReferenceBranchResult p configuration selector input
      ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input) := by
  dsimp only
  let slot := slotOfMember configuration site member
  let offset : Fin 6 := ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let selector := selectorOfSlotOffset slot offset
  let persistent := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
    reversibleGatePermutation input
  let branchOutput := (rowDiagonalResultComputeUseUncomputeCircuit p slot copy).runBasis
    reversibleGatePermutation persistent
  have persistentSpec : RowOraclePersistentConditionsSpec p configuration selector
      persistent := by
    simpa [persistent, selector, slot, offset] using specification.afterPersistent
  have active : slot.val < configuration.1.card := by
    dsimp [slot, slotOfMember]
    exact ((configuration.1.orderIsoOfFin rfl).symm ⟨site, member⟩).isLt
  have activeCircuit : dispatchRowSelectorToDiagonalOrEventCircuit p selector =
      rowDiagonalResultComputeUseUncomputeCircuit p slot copy := by
    unfold dispatchRowSelectorToDiagonalOrEventCircuit
    have selectorSlotEq : selectorSlot selector = slot := by
      simp [selector]
    have selectorOffsetEq : selectorOffset selector = offset := by
      simp [selector]
    rw [selectorSlotEq, selectorOffsetEq]
    exact dispatchRowSelectorToDiagonalOrEventCircuitSlotOffset_of_diagonal p slot offset (by
      simpa [offset] using copy.isLt)
  have activeResult : (dispatchRowSelectorToDiagonalOrEventCircuit p selector).runBasis
      reversibleGatePermutation persistent = branchOutput := by
    rw [activeCircuit]
  have branchResult : RowReferenceBranchResult p configuration selector
      persistent branchOutput := by
    simpa [branchOutput, selector, offset] using
      rowDiagonalResultComputeUseUncomputeCircuit_active_reference_actual configuration slot copy
        active persistent persistentSpec
  have branchOutputSpec : RowOraclePersistentConditionsSpec p configuration selector
      branchOutput := persistentSpec.of_broadAgreement branchResult.support_restored
  have inactiveInput : ∀ branch : QSelector p, branch ≠ selector →
      (dispatchRowSelectorToDiagonalOrEventCircuit p branch).runBasis reversibleGatePermutation persistent =
        persistent := by
    intro branch different
    exact dispatchRowSelectorToDiagonalOrEventCircuit_inactive_of_selector_ne configuration selector branch
      persistent persistentSpec different
  have inactiveOutput : ∀ branch : QSelector p, branch ≠ selector →
      (dispatchRowSelectorToDiagonalOrEventCircuit p branch).runBasis reversibleGatePermutation
        branchOutput = branchOutput := by
    intro branch different
    exact dispatchRowSelectorToDiagonalOrEventCircuit_inactive_of_selector_ne configuration selector branch
      branchOutput branchOutputSpec different
  simpa [selector, slot, offset] using
    applyRowOracleReferenceAndRestoreWorkCircuit_correct_of_unique_active p configuration selector
      selector input branchOutput inactiveInput activeResult inactiveOutput
        branchResult

/-- Canonical 対角入力では row oracle を二回実行すると入力基底へ戻る。 -/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_diagonal_involutive
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOracleInputSpec p configuration
      (selectorOfSlotOffset (slotOfMember configuration site member)
        ⟨copy.val, lt_trans copy.isLt (by decide)⟩) input) :
    (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation
        ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input) =
      input := by
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let first := (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
    reversibleGatePermutation input
  let second := (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
    reversibleGatePermutation first
  have firstResult : RowReferenceBranchResult p configuration selector input
      first := by
    simpa [selector, first] using
      applyRowOracleReferenceAndRestoreWorkCircuit_diagonal_correct configuration site member copy
        input specification
  have firstSpec : RowOracleInputSpec p configuration selector first :=
    RowReferenceBranchResult.preservesInputSpec specification firstResult
  have secondResult : RowReferenceBranchResult p configuration selector first
      second := by
    simpa [selector, second] using
      applyRowOracleReferenceAndRestoreWorkCircuit_diagonal_correct configuration site member copy
        first firstSpec
  change second = input
  exact RowReferenceBranchResult.twice_eq_input firstResult secondResult

/-- 対角最終基底の row 逆追跡像は同じ row oracle の正方向実行で表せる。 -/
theorem qActualAfterRowOraclePreimage_diagonal_eq
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterRowOraclePreimage p (delimiterEncoding configuration) selector =
      (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation
        (qActualAfterFinalFlipPreimage p (delimiterEncoding configuration)
          selector) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  apply qActualAfterRowOraclePreimage_eq_of_runBasis
  exact applyRowOracleReferenceAndRestoreWorkCircuit_diagonal_involutive configuration site member
    copy _ (qActualAfterFinalFlipPreimage_rowOracleInputSpec p configuration
      selector)

/-- 対角 row 逆追跡像は同一配置・同一 selector の row 参照 XOR 仕様を満たす。 -/
theorem qActualAfterRowOraclePreimage_diagonal_result
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    RowReferenceBranchResult p configuration selector
      (qActualAfterFinalFlipPreimage p (delimiterEncoding configuration) selector)
      (qActualAfterRowOraclePreimage p (delimiterEncoding configuration)
        selector) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  have result := applyRowOracleReferenceAndRestoreWorkCircuit_diagonal_correct configuration site
    member copy
    (qActualAfterFinalFlipPreimage p (delimiterEncoding configuration) selector)
    (qActualAfterFinalFlipPreimage_rowOracleInputSpec p configuration selector)
  rw [← qActualAfterRowOraclePreimage_diagonal_eq configuration site member copy]
    at result
  simpa [selector] using result

/-- 対角 row 逆追跡後も amplitude signal は真である。 -/
theorem qActualAfterRowOraclePreimage_diagonal_amplitude_true
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterRowOraclePreimage p (delimiterEncoding configuration) selector
        (amplitudeSignalWire p) = true := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  have result := qActualAfterRowOraclePreimage_diagonal_result configuration site
    member copy
  rw [result.outside_restored (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_columnKeyWires p)
    (amplitudeSignalWire_not_mem_columnSelectorWires p)
    (amplitudeSignalWire_ne_keySignalWire p)]
  exact qActualAfterFinalFlipPreimage_amplitudeSignal p _ _

/-- 対角 row 逆追跡後の active bit は偽である。 -/
theorem qActualAfterRowOraclePreimage_diagonal_active_false
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterRowOraclePreimage p (delimiterEncoding configuration) selector
        (activeWire p) = false := by
  dsimp only
  have result := qActualAfterRowOraclePreimage_diagonal_result configuration site
    member copy
  rw [result.outside_restored (activeWire p)
    (qActualActiveWire_not_mem_columnKeyWires p)
    (qActualActiveWire_not_mem_columnSelectorWires p)
    (qActualActiveWire_ne_keySignalWire p)]
  exact qActualAfterFinalFlipPreimage_active_false p _ _

/-- 対角 row 逆追跡後の negative bit は偽である。 -/
theorem qActualAfterRowOraclePreimage_diagonal_negative_false
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterRowOraclePreimage p (delimiterEncoding configuration) selector
        (negativeWire p) = false := by
  dsimp only
  have result := qActualAfterRowOraclePreimage_diagonal_result configuration site
    member copy
  rw [result.outside_restored (negativeWire p)
    (qActualNegativeWire_not_mem_columnKeyWires p)
    (qActualNegativeWire_not_mem_columnSelectorWires p)
    (qActualNegativeWire_ne_keySignalWire p)]
  exact qActualAfterFinalFlipPreimage_negative_false p _ _

/-- 対角 row 逆追跡像は後続 column oracle の一般入力仕様を満たす。 -/
theorem qActualAfterRowOraclePreimage_diagonal_columnInputSpec
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    ColumnOracleInputSpec p configuration selector
      (qActualAfterRowOraclePreimage p (delimiterEncoding configuration)
        selector) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let initial := qActualAfterFinalFlipPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterRowOraclePreimage p
    (delimiterEncoding configuration) selector
  have result : RowReferenceBranchResult p configuration selector initial actual :=
    by
      simpa [selector, initial, actual] using
        qActualAfterRowOraclePreimage_diagonal_result configuration site member
          copy
  refine {
    column_key_bits := ?_
    selector_bits := ?_
    work_zero := ?_ }
  · rw [result.column_key]
    have initialZero : readWires (columnKeyWires p) initial =
        List.replicate (columnKeyWires p).length false := by
      simpa [initial] using qActualAfterFinalFlipPreimage_columnKey_zero p
        (delimiterEncoding configuration) selector
    rw [initialZero]
    simpa [xorRegisterBits, registerBitList] using
      xorRegisterBits_replicate_false
        (registerBitList (delimiterEncoding configuration))
  · rw [result.column_selector]
    have initialZero : readWires (columnSelectorWires p) initial =
        List.replicate (columnSelectorWires p).length false := by
      simpa [initial] using qActualAfterFinalFlipPreimage_columnSelector_zero p
        (delimiterEncoding configuration) selector
    rw [initialZero]
    simpa [constantBits] using
      controlledXorConstantBits_true_replicate_false selector.val 0
        (columnSelectorWires p).length
  · intro wire workMember
    change actual wire = false
    rw [result.support_restored wire (List.mem_append_right _ workMember)]
    exact qActualAfterFinalFlipPreimage_oracleWork_zero p
      (delimiterEncoding configuration) selector workMember

/-- 対角 column 正方向逆追跡像は負号付き対角 column 参照仕様を満たす。 -/
theorem qActualAfterColumnInversePreimage_diagonal_result
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    let reference : ColumnReferenceResult p :=
      ⟨configuration, selector, true⟩
    ColumnReferenceBranchResult p reference
      (qActualAfterRowOraclePreimage p (delimiterEncoding configuration)
        selector)
      (qActualAfterColumnInversePreimage p (delimiterEncoding configuration)
        selector) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p :=
    ⟨configuration, selector, true⟩
  have referenceSome : columnReference configuration selector = some reference := by
    simpa [selector, reference] using
      columnReference_diagonal configuration site member copy
  rw [qActualAfterColumnInversePreimage_eq_runBasis]
  exact applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some configuration selector
    reference _
    (qActualAfterRowOraclePreimage_diagonal_columnInputSpec configuration site
      member copy) referenceSome

/-- 対角 column 逆追跡後も amplitude signal は真である。 -/
theorem qActualAfterColumnInversePreimage_diagonal_amplitude_true
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnInversePreimage p (delimiterEncoding configuration)
        selector (amplitudeSignalWire p) = true := by
  dsimp only
  have result := qActualAfterColumnInversePreimage_diagonal_result configuration
    site member copy
  rw [result.outside_restored (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_rowOutputWires p)
    (amplitudeSignalWire_not_mem_selectorOutputWires p)
    (negativeWire_ne_amplitudeSignalWire p).symm
    (activeWire_ne_amplitudeSignalWire p).symm]
  exact qActualAfterRowOraclePreimage_diagonal_amplitude_true configuration site
    member copy

/-- 対角 column 逆追跡後の active bit は真である。 -/
theorem qActualAfterColumnInversePreimage_diagonal_active_true
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnInversePreimage p (delimiterEncoding configuration)
        selector (activeWire p) = true := by
  dsimp only
  have result := qActualAfterColumnInversePreimage_diagonal_result configuration
    site member copy
  rw [result.active,
    qActualAfterRowOraclePreimage_diagonal_active_false configuration site
      member copy]
  rfl

/-- 対角 column 逆追跡後の negative bit は真である。 -/
theorem qActualAfterColumnInversePreimage_diagonal_negative_true
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnInversePreimage p (delimiterEncoding configuration)
        selector (negativeWire p) = true := by
  dsimp only
  have result := qActualAfterColumnInversePreimage_diagonal_result configuration
    site member copy
  rw [result.negative,
    qActualAfterRowOraclePreimage_diagonal_negative_false configuration site
      member copy]
  rfl

/-- 対角受理 path の discriminator 出力では amplitude signal が真である。 -/
theorem qActualDiscriminatorOutputPreimage_diagonal_amplitude_true
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualDiscriminatorOutputPreimage p (delimiterEncoding configuration)
        selector (amplitudeSignalWire p) = true := by
  dsimp only
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _
    (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_systemWires p)
    (amplitudeSignalWire_not_mem_rowSelectorWires p)
    (amplitudeSignalWire_ne_keySignalWire p)]
  exact qActualAfterColumnInversePreimage_diagonal_amplitude_true configuration
    site member copy

/-- 対角受理 path の discriminator 出力では negative bit が真である。 -/
theorem qActualDiscriminatorOutputPreimage_diagonal_negative_true
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualDiscriminatorOutputPreimage p (delimiterEncoding configuration)
        selector (negativeWire p) = true := by
  dsimp only
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _ (negativeWire p)
    (qActualNegativeWire_not_mem_systemWires p)
    (qActualNegativeWire_not_mem_rowSelectorWires p)
    (qActualNegativeWire_ne_keySignalWire p)]
  exact qActualAfterColumnInversePreimage_diagonal_negative_true configuration
    site member copy

/-- 対角受理 path の位相は厳密に `-1` である。 -/
theorem qActualSelectorPathPhase_diagonal_eq
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualSelectorPathPhase p (delimiterEncoding configuration) selector = -1 := by
  dsimp only
  have phase := qActualSelectorPathPhase_eq_of_signals p
    (delimiterEncoding configuration)
    (selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩) true
    (qActualDiscriminatorOutputPreimage_diagonal_negative_true configuration
      site member copy)
    (qActualDiscriminatorOutputPreimage_diagonal_amplitude_true configuration
      site member copy)
  simpa using phase

/-- 対角 row 逆追跡後も row-output accumulator は全0である。 -/
theorem qActualAfterRowOraclePreimage_diagonal_rowOutput_zero
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    readWires (rowOutputWires p)
        (qActualAfterRowOraclePreimage p (delimiterEncoding configuration)
          selector) = List.replicate (rowOutputWires p).length false := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  have result := qActualAfterRowOraclePreimage_diagonal_result configuration site
    member copy
  calc
    readWires (rowOutputWires p)
        (qActualAfterRowOraclePreimage p (delimiterEncoding configuration)
          selector) =
        readWires (rowOutputWires p)
          (qActualAfterFinalFlipPreimage p (delimiterEncoding configuration)
            selector) := by
      apply List.map_congr_left
      intro wire wireMember
      exact result.outside_restored wire
        ((List.disjoint_left.mp
          (qActualRowOutputWires_disjoint_columnKeyWires p)) wireMember)
        ((List.disjoint_left.mp
          (qActualRowOutputWires_disjoint_columnSelectorWires p)) wireMember)
        (by
          intro equal
          exact qActualKeySignalWire_not_mem_rowOutputWires p
            (equal ▸ wireMember))
    _ = List.replicate (rowOutputWires p).length false := by
      apply qActualAfterFinalFlipPreimage_readWires_zero
      · intro wire wireMember
        rcases List.mem_map.mp wireMember with ⟨index, _, rfl⟩
        exact ⟨_, rfl⟩
      · exact qActualRowOutputWires_disjoint_rowSelectorWires p
      · exact amplitudeSignalWire_not_mem_rowOutputWires p

/-- 対角 row 逆追跡後も selector-output accumulator は全0である。 -/
theorem qActualAfterRowOraclePreimage_diagonal_selectorOutput_zero
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    readWires (selectorOutputWires p)
        (qActualAfterRowOraclePreimage p (delimiterEncoding configuration)
          selector) = List.replicate (selectorOutputWires p).length false := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  have result := qActualAfterRowOraclePreimage_diagonal_result configuration site
    member copy
  calc
    readWires (selectorOutputWires p)
        (qActualAfterRowOraclePreimage p (delimiterEncoding configuration)
          selector) =
        readWires (selectorOutputWires p)
          (qActualAfterFinalFlipPreimage p (delimiterEncoding configuration)
            selector) := by
      apply List.map_congr_left
      intro wire wireMember
      exact result.outside_restored wire
        ((List.disjoint_left.mp
          (qActualSelectorOutputWires_disjoint_columnKeyWires p))
            wireMember)
        ((List.disjoint_left.mp
          (qActualSelectorOutputWires_disjoint_columnSelectorWires p))
            wireMember)
        (by
          intro equal
          exact qActualKeySignalWire_not_mem_selectorOutputWires p
            (equal ▸ wireMember))
    _ = List.replicate (selectorOutputWires p).length false := by
      apply qActualAfterFinalFlipPreimage_readWires_zero
      · intro wire wireMember
        rcases List.mem_map.mp wireMember with ⟨index, _, rfl⟩
        exact ⟨_, rfl⟩
      · exact qTopSelectorOutputWires_disjoint_rowSelectorWires p
      · exact amplitudeSignalWire_not_mem_selectorOutputWires p

/-- 対角 discriminator 逆追跡像も column oracle 入力仕様を満たす。 -/
theorem qActualAfterDiscriminatorPreimage_diagonal_columnInputSpec
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    ColumnOracleInputSpec p configuration selector
      (qActualAfterDiscriminatorPreimage p (delimiterEncoding configuration)
        selector) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p :=
    ⟨configuration, selector, true⟩
  have firstResult := qActualAfterColumnInversePreimage_diagonal_result
    configuration site member copy
  have beforeSpec := qActualAfterRowOraclePreimage_diagonal_columnInputSpec
    configuration site member copy
  have afterColumnSpec :=
    ColumnReferenceBranchResult.preservesInputSpec beforeSpec firstResult
  have afterAlignSpec :=
    ProbabilityGeneratorQProof.ColumnOracleInputSpec.afterAlignDiscriminator
      afterColumnSpec
  change ColumnOracleInputSpec p configuration selector
    (cnotBasisAction (activeWire p) (amplitudeSignalWire p)
      (qActualDiscriminatorOutputPreimage p (delimiterEncoding configuration)
        selector))
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  simpa [selector, reference] using afterAlignSpec

/-- 対角 path の二回目 column oracle も同じ参照 XOR 仕様を満たす。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_result
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    let reference : ColumnReferenceResult p :=
      ⟨configuration, selector, true⟩
    ColumnReferenceBranchResult p reference
      (qActualAfterDiscriminatorPreimage p (delimiterEncoding configuration)
        selector)
      (qActualAfterColumnOraclePreimage p (delimiterEncoding configuration)
        selector) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p :=
    ⟨configuration, selector, true⟩
  let discriminator := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  have referenceSome : columnReference configuration selector = some reference := by
    simpa [selector, reference] using
      columnReference_diagonal configuration site member copy
  have inputSpec : ColumnOracleInputSpec p configuration selector
      discriminator := by
    simpa [selector, discriminator] using
      qActualAfterDiscriminatorPreimage_diagonal_columnInputSpec configuration
        site member copy
  have twice := applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some_involutive
    configuration selector reference discriminator inputSpec referenceSome
  have actualEq : actual =
      (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation
        discriminator := by
    apply qActualAfterColumnOraclePreimage_eq_of_runBasis
    exact twice
  have result := applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some configuration
    selector reference discriminator inputSpec referenceSome
  rw [← actualEq] at result
  simpa [selector, reference, discriminator, actual] using result

/-- 対角 path の二回目 column oracle 後は row-output accumulator が全0へ戻る。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_rowOutput_zero
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    readWires (rowOutputWires p)
        (qActualAfterColumnOraclePreimage p (delimiterEncoding configuration)
          selector) = List.replicate (rowOutputWires p).length false := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p :=
    ⟨configuration, selector, true⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding configuration) selector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding configuration) selector
  let afterDiscriminator := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [selector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_diagonal_result configuration site member
        copy
  have secondResult : ColumnReferenceBranchResult p reference afterDiscriminator
      actual := by
    simpa [selector, reference, afterDiscriminator, actual] using
      qActualAfterColumnOraclePreimage_diagonal_result configuration site member
        copy
  have targetPreserved : readWires (rowOutputWires p) afterDiscriminator =
      readWires (rowOutputWires p) afterColumn := by
    apply qActualAfterDiscriminatorPreimage_readWires_eq_afterColumnInverse
    · exact qTopRowOutputWires_disjoint_systemWires p
    · exact qActualRowOutputWires_disjoint_rowSelectorWires p
    · exact qActualKeySignalWire_not_mem_rowOutputWires p
    · exact amplitudeSignalWire_not_mem_rowOutputWires p
  have restored : readWires (rowOutputWires p) actual =
      readWires (rowOutputWires p) afterRow := by
    rw [secondResult.row_output, targetPreserved, firstResult.row_output]
    apply xorRegisterBits_involutive_of_length
    simp only [readWires, List.length_map, registerBitList]
    simp [rowOutputWires]
  rw [restored]
  exact qActualAfterRowOraclePreimage_diagonal_rowOutput_zero configuration site
    member copy

/-- 対角 path の二回目 column oracle 後は selector-output accumulator が全0へ戻る。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_selectorOutput_zero
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    readWires (selectorOutputWires p)
        (qActualAfterColumnOraclePreimage p (delimiterEncoding configuration)
          selector) = List.replicate (selectorOutputWires p).length false := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p :=
    ⟨configuration, selector, true⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding configuration) selector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding configuration) selector
  let afterDiscriminator := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [selector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_diagonal_result configuration site member
        copy
  have secondResult : ColumnReferenceBranchResult p reference afterDiscriminator
      actual := by
    simpa [selector, reference, afterDiscriminator, actual] using
      qActualAfterColumnOraclePreimage_diagonal_result configuration site member
        copy
  have targetPreserved : readWires (selectorOutputWires p) afterDiscriminator =
      readWires (selectorOutputWires p) afterColumn := by
    apply qActualAfterDiscriminatorPreimage_readWires_eq_afterColumnInverse
    · exact qTopSelectorOutputWires_disjoint_systemWires p
    · exact qTopSelectorOutputWires_disjoint_rowSelectorWires p
    · exact qActualKeySignalWire_not_mem_selectorOutputWires p
    · exact amplitudeSignalWire_not_mem_selectorOutputWires p
  have restored : readWires (selectorOutputWires p) actual =
      readWires (selectorOutputWires p) afterRow := by
    rw [secondResult.selector_output, targetPreserved,
      firstResult.selector_output]
    exact controlledXorConstantBits_true_involutive reference.rowSelector.val 0 _
  rw [restored]
  exact qActualAfterRowOraclePreimage_diagonal_selectorOutput_zero configuration
    site member copy

/--
`rowReference` が値を返す全ての場合について、actual row oracle はその predecessor・
column selector を任意 accumulator へ厳密に XOR し、内部 work を入力へ戻す。
-/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_reference_some
    {p : QParameters} (output : QConfiguration p) (selector : QSelector p)
    (reference : RowReferenceResult p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOracleInputSpec p output selector input)
    (referenceSome : rowReference output selector = some reference) :
    RowReferenceBranchResult p reference.input reference.columnSelector input
      ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input) := by
  cases selected : configurationSlot? output (selectorSlot selector) with
  | none =>
      have impossible := referenceSome
      unfold rowReference at impossible
      rw [selected] at impossible
      contradiction
  | some arrival =>
      by_cases diagonal : (selectorOffset selector).val < 2
      · let copy : Fin 2 := ⟨(selectorOffset selector).val, diagonal⟩
        have slotEq : selectorSlot selector =
            slotOfMember output arrival.1 arrival.2 :=
          selectorSlot_eq_slotOfMember_of_selected output
            (selectorSlot selector) arrival.1 arrival.2 selected
        have selectorEq : selector =
            selectorOfSlotOffset (slotOfMember output arrival.1 arrival.2)
              ⟨copy.val, lt_trans copy.isLt (by decide)⟩ := by
          calc
            selector = selectorOfSlotOffset (selectorSlot selector)
                (selectorOffset selector) :=
              (selectorOfSlotOffset_parts selector).symm
            _ = selectorOfSlotOffset
                (slotOfMember output arrival.1 arrival.2)
                ⟨copy.val, lt_trans copy.isLt (by decide)⟩ := by
              congr 1
        have value : rowReference output selector =
            some ⟨output, selector⟩ := by
          unfold rowReference
          rw [selected]
          simp [diagonal]
        have referenceEq : reference = ⟨output, selector⟩ :=
          Option.some.inj (referenceSome.symm.trans value)
        subst reference
        rw [selectorEq] at specification ⊢
        exact applyRowOracleReferenceAndRestoreWorkCircuit_diagonal_correct output arrival.1
          arrival.2 copy input specification
      · have eventRange : 2 ≤ (selectorOffset selector).val := by omega
        let direction := selectorDirection selector
        let source := moveSiteBackward arrival.1 direction
        have movedEq : moveSite source direction = arrival.1 := by
          simp [source, direction]
        have sourceAbsent : source ∉ output.1 := by
          intro sourceMember
          have impossible := referenceSome
          unfold rowReference at impossible
          rw [selected] at impossible
          simp only [diagonal, dite_false] at impossible
          rw [dif_neg (not_not.mpr sourceMember)] at impossible
          contradiction
        by_cases collision : selectorRequestsCollision selector = true
        · have degreeRoom : output.1.card < p.K := by
            by_contra full
            have impossible := referenceSome
            unfold rowReference at impossible
            rw [selected] at impossible
            simp only [diagonal, dite_false] at impossible
            rw [dif_pos sourceAbsent] at impossible
            simp only [collision, full] at impossible
            contradiction
          let predecessorSites := collisionPredecessorSites output source
          have nonempty : predecessorSites.Nonempty :=
            ⟨source, Finset.mem_insert_self _ _⟩
          have cardBound : predecessorSites.card ≤ p.K := by
            calc
              predecessorSites.card ≤ output.1.card + 1 :=
                Finset.card_insert_le _ _
              _ ≤ p.K := by omega
          let predecessor : QConfiguration p :=
            ⟨predecessorSites, Finset.one_le_card.mpr nonempty, cardBound⟩
          have sourceMember : source ∈ predecessor.1 :=
            Finset.mem_insert_self _ _
          have outputEq : eventOutput predecessor source direction = output := by
            apply eventOutput_collisionPredecessor_eq output predecessor arrival.1
              source direction arrival.2 sourceAbsent sourceMember
            · rfl
            · exact movedEq
          have collisionProperty :
              moveSite source direction ∈ predecessor.1.erase source := by
            rw [movedEq]
            simp [predecessor, predecessorSites, collisionPredecessorSites,
              sourceAbsent, arrival.2]
          have eventCollisionEq : eventCollision predecessor source direction =
              true := by
            simp [eventCollision, collisionProperty]
          have offsetEq : eventOffset direction
              (eventCollision predecessor source direction) =
                selectorOffset selector := by
            rw [eventCollisionEq, ← collision]
            exact eventOffset_selectorParts selector diagonal
          have rowSelectorEq := rowSelectorForEvent_eq_of_selected output
            predecessor selector arrival.1 source arrival.2 sourceMember direction
              selected outputEq movedEq offsetEq
          have columnSelectorEq := selectorForEvent_eq_of_offset predecessor source
            sourceMember direction (selectorOffset selector) offsetEq
          have reduced := referenceSome
          unfold rowReference at reduced
          rw [selected] at reduced
          simp only [diagonal, dite_false] at reduced
          rw [dif_pos sourceAbsent] at reduced
          simp only [collision, degreeRoom] at reduced
          have referenceEq : reference =
              ⟨predecessor,
                selectorOfSlotOffset (slotOfMember predecessor source sourceMember)
                  (selectorOffset selector)⟩ :=
            by
              simpa [predecessor, predecessorSites] using
                (Option.some.inj reduced).symm
          subst reference
          exact applyRowOracleReferenceAndRestoreWorkCircuit_reference_some_of_event output
            predecessor selector _ source sourceMember direction input specification
              outputEq rowSelectorEq columnSelectorEq
        · have collisionFalse : selectorRequestsCollision selector = false :=
            Bool.eq_false_of_not_eq_true collision
          let predecessorSites := replacementPredecessorSites output arrival.1 source
          have nonempty : predecessorSites.Nonempty :=
            ⟨source, Finset.mem_insert_self _ _⟩
          have cardBound : predecessorSites.card ≤ p.K := by
            calc
              predecessorSites.card ≤ (output.1.erase arrival.1).card + 1 :=
                Finset.card_insert_le _ _
              _ = output.1.card := by
                rw [Finset.card_erase_of_mem arrival.2]
                omega
              _ ≤ p.K := output.2.2
          let predecessor : QConfiguration p :=
            ⟨predecessorSites, Finset.one_le_card.mpr nonempty, cardBound⟩
          have sourceMember : source ∈ predecessor.1 :=
            Finset.mem_insert_self _ _
          have outputEq : eventOutput predecessor source direction = output := by
            apply eventOutput_replacementPredecessor_eq output predecessor arrival.1
              source direction arrival.2 sourceAbsent sourceMember
            · rfl
            · exact movedEq
          have noCollisionProperty :
              moveSite source direction ∉ predecessor.1.erase source := by
            rw [movedEq]
            simp [predecessor, predecessorSites, replacementPredecessorSites,
              sourceAbsent]
          have eventCollisionEq : eventCollision predecessor source direction =
              false := by
            simp [eventCollision, noCollisionProperty]
          have offsetEq : eventOffset direction
              (eventCollision predecessor source direction) =
                selectorOffset selector := by
            rw [eventCollisionEq, ← collisionFalse]
            exact eventOffset_selectorParts selector diagonal
          have rowSelectorEq := rowSelectorForEvent_eq_of_selected output
            predecessor selector arrival.1 source arrival.2 sourceMember direction
              selected outputEq movedEq offsetEq
          have columnSelectorEq := selectorForEvent_eq_of_offset predecessor source
            sourceMember direction (selectorOffset selector) offsetEq
          have reduced := referenceSome
          unfold rowReference at reduced
          rw [selected] at reduced
          simp only [diagonal, dite_false] at reduced
          rw [dif_pos sourceAbsent] at reduced
          simp only [collision] at reduced
          have referenceEq : reference =
              ⟨predecessor,
                selectorOfSlotOffset (slotOfMember predecessor source sourceMember)
                  (selectorOffset selector)⟩ := by
            simpa [predecessor, predecessorSites] using
              (Option.some.inj reduced).symm
          subst reference
          exact applyRowOracleReferenceAndRestoreWorkCircuit_reference_some_of_event output
            predecessor selector _ source sourceMember direction input specification
              outputEq rowSelectorEq columnSelectorEq

/--
受理された任意の row 参照は、対角copyまたは一意な正方向物理eventへ戻せる。
-/
theorem rowReference_some_cases
    {p : QParameters} (output : QConfiguration p) (selector : QSelector p)
    (reference : RowReferenceResult p)
    (referenceSome : rowReference output selector = some reference) :
    (∃ (site : QSite p) (member : site ∈ output.1) (copy : Fin 2),
      selector = selectorOfSlotOffset (slotOfMember output site member)
        ⟨copy.val, lt_trans copy.isLt (by decide)⟩ ∧
      reference = ⟨output, selector⟩) ∨
    (∃ (predecessor : QConfiguration p) (source : QSite p)
        (member : source ∈ predecessor.1) (direction : QDirection),
      eventOutput predecessor source direction = output ∧
      rowSelectorForEvent predecessor source member direction = selector ∧
      selectorForEvent predecessor source member direction =
        reference.columnSelector ∧ predecessor = reference.input) := by
  cases selected : configurationSlot? output (selectorSlot selector) with
  | none =>
      have impossible := referenceSome
      unfold rowReference at impossible
      rw [selected] at impossible
      contradiction
  | some arrival =>
      by_cases diagonal : (selectorOffset selector).val < 2
      · let copy : Fin 2 := ⟨(selectorOffset selector).val, diagonal⟩
        have slotEq : selectorSlot selector =
            slotOfMember output arrival.1 arrival.2 :=
          selectorSlot_eq_slotOfMember_of_selected output
            (selectorSlot selector) arrival.1 arrival.2 selected
        have selectorEq : selector =
            selectorOfSlotOffset (slotOfMember output arrival.1 arrival.2)
              ⟨copy.val, lt_trans copy.isLt (by decide)⟩ := by
          calc
            selector = selectorOfSlotOffset (selectorSlot selector)
                (selectorOffset selector) :=
              (selectorOfSlotOffset_parts selector).symm
            _ = selectorOfSlotOffset
                (slotOfMember output arrival.1 arrival.2)
                ⟨copy.val, lt_trans copy.isLt (by decide)⟩ := by
              congr 1
        have value : rowReference output selector =
            some ⟨output, selector⟩ := by
          unfold rowReference
          rw [selected]
          simp [diagonal]
        have referenceEq : reference = ⟨output, selector⟩ :=
          Option.some.inj (referenceSome.symm.trans value)
        exact Or.inl ⟨arrival.1, arrival.2, copy, selectorEq, referenceEq⟩
      · let direction := selectorDirection selector
        let source := moveSiteBackward arrival.1 direction
        have movedEq : moveSite source direction = arrival.1 := by
          simp [source, direction]
        have sourceAbsent : source ∉ output.1 := by
          intro sourceMember
          have impossible := referenceSome
          unfold rowReference at impossible
          rw [selected] at impossible
          simp only [diagonal, dite_false] at impossible
          rw [dif_neg (not_not.mpr sourceMember)] at impossible
          contradiction
        by_cases collision : selectorRequestsCollision selector = true
        · have degreeRoom : output.1.card < p.K := by
            by_contra full
            have impossible := referenceSome
            unfold rowReference at impossible
            rw [selected] at impossible
            simp only [diagonal, dite_false] at impossible
            rw [dif_pos sourceAbsent] at impossible
            simp only [collision, full] at impossible
            contradiction
          let predecessorSites := collisionPredecessorSites output source
          have nonempty : predecessorSites.Nonempty :=
            ⟨source, Finset.mem_insert_self _ _⟩
          have cardBound : predecessorSites.card ≤ p.K := by
            calc
              predecessorSites.card ≤ output.1.card + 1 :=
                Finset.card_insert_le _ _
              _ ≤ p.K := by omega
          let predecessor : QConfiguration p :=
            ⟨predecessorSites, Finset.one_le_card.mpr nonempty, cardBound⟩
          have sourceMember : source ∈ predecessor.1 :=
            Finset.mem_insert_self _ _
          have outputEq : eventOutput predecessor source direction = output := by
            apply eventOutput_collisionPredecessor_eq output predecessor arrival.1
              source direction arrival.2 sourceAbsent sourceMember
            · rfl
            · exact movedEq
          have collisionProperty :
              moveSite source direction ∈ predecessor.1.erase source := by
            rw [movedEq]
            simp [predecessor, predecessorSites, collisionPredecessorSites,
              sourceAbsent, arrival.2]
          have eventCollisionEq : eventCollision predecessor source direction =
              true := by
            simp [eventCollision, collisionProperty]
          have offsetEq : eventOffset direction
              (eventCollision predecessor source direction) =
                selectorOffset selector := by
            rw [eventCollisionEq, ← collision]
            exact eventOffset_selectorParts selector diagonal
          have rowSelectorEq := rowSelectorForEvent_eq_of_selected output
            predecessor selector arrival.1 source arrival.2 sourceMember direction
              selected outputEq movedEq offsetEq
          have columnSelectorEq := selectorForEvent_eq_of_offset predecessor source
            sourceMember direction (selectorOffset selector) offsetEq
          have reduced := referenceSome
          unfold rowReference at reduced
          rw [selected] at reduced
          simp only [diagonal, dite_false] at reduced
          rw [dif_pos sourceAbsent] at reduced
          simp only [collision, degreeRoom] at reduced
          have referenceEq : reference =
              ⟨predecessor,
                selectorOfSlotOffset (slotOfMember predecessor source sourceMember)
                  (selectorOffset selector)⟩ := by
            simpa [predecessor, predecessorSites] using
              (Option.some.inj reduced).symm
          subst reference
          exact Or.inr ⟨predecessor, source, sourceMember, direction, outputEq,
            rowSelectorEq, columnSelectorEq, rfl⟩
        · have collisionFalse : selectorRequestsCollision selector = false :=
            Bool.eq_false_of_not_eq_true collision
          let predecessorSites := replacementPredecessorSites output arrival.1 source
          have nonempty : predecessorSites.Nonempty :=
            ⟨source, Finset.mem_insert_self _ _⟩
          have cardBound : predecessorSites.card ≤ p.K := by
            calc
              predecessorSites.card ≤ (output.1.erase arrival.1).card + 1 :=
                Finset.card_insert_le _ _
              _ = output.1.card := by
                rw [Finset.card_erase_of_mem arrival.2]
                omega
              _ ≤ p.K := output.2.2
          let predecessor : QConfiguration p :=
            ⟨predecessorSites, Finset.one_le_card.mpr nonempty, cardBound⟩
          have sourceMember : source ∈ predecessor.1 :=
            Finset.mem_insert_self _ _
          have outputEq : eventOutput predecessor source direction = output := by
            apply eventOutput_replacementPredecessor_eq output predecessor arrival.1
              source direction arrival.2 sourceAbsent sourceMember
            · rfl
            · exact movedEq
          have noCollisionProperty :
              moveSite source direction ∉ predecessor.1.erase source := by
            rw [movedEq]
            simp [predecessor, predecessorSites, replacementPredecessorSites,
              sourceAbsent]
          have eventCollisionEq : eventCollision predecessor source direction =
              false := by
            simp [eventCollision, noCollisionProperty]
          have offsetEq : eventOffset direction
              (eventCollision predecessor source direction) =
                selectorOffset selector := by
            rw [eventCollisionEq, ← collisionFalse]
            exact eventOffset_selectorParts selector diagonal
          have rowSelectorEq := rowSelectorForEvent_eq_of_selected output
            predecessor selector arrival.1 source arrival.2 sourceMember direction
              selected outputEq movedEq offsetEq
          have columnSelectorEq := selectorForEvent_eq_of_offset predecessor source
            sourceMember direction (selectorOffset selector) offsetEq
          have reduced := referenceSome
          unfold rowReference at reduced
          rw [selected] at reduced
          simp only [diagonal, dite_false] at reduced
          rw [dif_pos sourceAbsent] at reduced
          simp only [collision] at reduced
          have referenceEq : reference =
              ⟨predecessor,
                selectorOfSlotOffset (slotOfMember predecessor source sourceMember)
                  (selectorOffset selector)⟩ := by
            simpa [predecessor, predecessorSites] using
              (Option.some.inj reduced).symm
          subst reference
          exact Or.inr ⟨predecessor, source, sourceMember, direction, outputEq,
            rowSelectorEq, columnSelectorEq, rfl⟩

/-- 受理された row 参照は、その返した predecessor 上で必ず正方向 column 参照を持つ。 -/
theorem rowReference_some_has_inverse
    {p : QParameters} (output : QConfiguration p) (rowSelector : QSelector p)
    (rowResult : RowReferenceResult p)
    (rowAccepted : rowReference output rowSelector = some rowResult) :
    ∃ columnResult : ColumnReferenceResult p,
      columnReference rowResult.input rowResult.columnSelector = some columnResult ∧
      columnResult.output = output ∧ columnResult.rowSelector = rowSelector := by
  rcases rowReference_some_cases output rowSelector rowResult rowAccepted with
    diagonal | event
  · rcases diagonal with ⟨site, member, copy, selectorEq, resultEq⟩
    subst rowSelector
    subst rowResult
    let selector := selectorOfSlotOffset (slotOfMember output site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    refine ⟨⟨output, selector, true⟩, ?_, rfl, rfl⟩
    simpa [selector] using columnReference_diagonal output site member copy
  · rcases event with ⟨predecessor, source, member, direction, outputEq,
      rowSelectorEq, columnSelectorEq, inputEq⟩
    subst output
    subst rowSelector
    rw [← inputEq, ← columnSelectorEq]
    let result : ColumnReferenceResult p :=
      ⟨eventOutput predecessor source direction,
        rowSelectorForEvent predecessor source member direction, false⟩
    refine ⟨result, ?_, rfl, rfl⟩
    simpa [result, columnSelectorEq] using
      columnReference_selectorForEvent_exact predecessor source member direction

/-- 対角整列逆追跡像でも active bit は真である。 -/
theorem qActualDiscriminatorOutputPreimage_diagonal_active_true
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualDiscriminatorOutputPreimage p (delimiterEncoding configuration) selector
        (activeWire p) = true := by
  dsimp only
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _ (activeWire p)
    (qActualActiveWire_not_mem_systemWires p)
    (qActualActiveWire_not_mem_rowSelectorWires p)
    (qActualActiveWire_ne_keySignalWire p)]
  exact qActualAfterColumnInversePreimage_diagonal_active_true configuration site
    member copy

/-- 対角 discriminator CNOT の逆追跡後は amplitude signal が0へ戻る。 -/
theorem qActualAfterDiscriminatorPreimage_diagonal_amplitude_false
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterDiscriminatorPreimage p (delimiterEncoding configuration) selector
        (amplitudeSignalWire p) = false := by
  dsimp only
  unfold qActualAfterDiscriminatorPreimage
  rw [cnotBasisAction_target]
  rw [qActualDiscriminatorOutputPreimage_diagonal_active_true configuration site
    member copy]
  rw [qActualDiscriminatorOutputPreimage_diagonal_amplitude_true configuration site
    member copy]
  rfl

/-- 対角pathの二回目column oracleはnegative accumulatorをrow直後の値へ戻す。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_negative
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnOraclePreimage p (delimiterEncoding configuration) selector
        (negativeWire p) =
      qActualAfterRowOraclePreimage p (delimiterEncoding configuration) selector
        (negativeWire p) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding configuration) selector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding configuration) selector
  let afterDiscriminator := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [selector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_diagonal_result configuration site member copy
  have secondResult : ColumnReferenceBranchResult p reference afterDiscriminator
      actual := by
    simpa [selector, reference, afterDiscriminator, actual] using
      qActualAfterColumnOraclePreimage_diagonal_result configuration site member copy
  have targetPreserved : afterDiscriminator (negativeWire p) =
      afterColumn (negativeWire p) := by
    apply qActualAfterDiscriminatorPreimage_eq_afterColumnInverse_on_wire
    · exact qActualNegativeWire_not_mem_systemWires p
    · exact qActualNegativeWire_not_mem_rowSelectorWires p
    · exact qActualNegativeWire_ne_keySignalWire p
    · exact negativeWire_ne_amplitudeSignalWire p
  change actual (negativeWire p) = afterRow (negativeWire p)
  rw [secondResult.negative, targetPreserved, firstResult.negative]
  simp [reference]

/-- 対角pathの二回目column oracleはactive accumulatorをrow直後の値へ戻す。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_active
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnOraclePreimage p (delimiterEncoding configuration) selector
        (activeWire p) =
      qActualAfterRowOraclePreimage p (delimiterEncoding configuration) selector
        (activeWire p) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding configuration) selector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding configuration) selector
  let afterDiscriminator := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [selector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_diagonal_result configuration site member copy
  have secondResult : ColumnReferenceBranchResult p reference afterDiscriminator
      actual := by
    simpa [selector, reference, afterDiscriminator, actual] using
      qActualAfterColumnOraclePreimage_diagonal_result configuration site member copy
  have targetPreserved : afterDiscriminator (activeWire p) =
      afterColumn (activeWire p) := by
    apply qActualAfterDiscriminatorPreimage_eq_afterColumnInverse_on_wire
    · exact qActualActiveWire_not_mem_systemWires p
    · exact qActualActiveWire_not_mem_rowSelectorWires p
    · exact qActualActiveWire_ne_keySignalWire p
    · exact activeWire_ne_amplitudeSignalWire p
  change actual (activeWire p) = afterRow (activeWire p)
  rw [secondResult.active, targetPreserved, firstResult.active]
  simp

/-- 対角pathの二回目column oracle後はnegative bitが0である。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_negative_false
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnOraclePreimage p (delimiterEncoding configuration) selector
        (negativeWire p) = false := by
  dsimp only
  rw [qActualAfterColumnOraclePreimage_diagonal_negative]
  exact qActualAfterRowOraclePreimage_diagonal_negative_false configuration site
    member copy

/-- 対角pathの二回目column oracle後はactive bitが0である。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_active_false
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnOraclePreimage p (delimiterEncoding configuration) selector
        (activeWire p) = false := by
  dsimp only
  rw [qActualAfterColumnOraclePreimage_diagonal_active]
  exact qActualAfterRowOraclePreimage_diagonal_active_false configuration site member
    copy

/-- 対角 discriminator 逆追跡後はrow-selector accumulatorが全0へ戻る。 -/
theorem qActualAfterDiscriminatorPreimage_diagonal_rowSelector_zero
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    readWires (rowSelectorWires p)
        (qActualAfterDiscriminatorPreimage p (delimiterEncoding configuration)
          selector) = List.replicate (rowSelectorWires p).length false := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding configuration) selector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding configuration) selector
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [selector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_diagonal_result configuration site member copy
  have afterRowSpec : RowOracleInputSpec p configuration selector afterRow :=
    RowReferenceBranchResult.preservesInputSpec
      (qActualAfterFinalFlipPreimage_rowOracleInputSpec p configuration selector)
      (by
        simpa [selector, afterRow] using
          qActualAfterRowOraclePreimage_diagonal_result configuration site member copy)
  have rowSelectorAfterColumn : readWires (rowSelectorWires p) afterColumn =
      constantBits selector.val (rowSelectorWires p).length := by
    calc
      readWires (rowSelectorWires p) afterColumn =
          readWires (rowSelectorWires p) afterRow := by
        apply List.map_congr_left
        intro wire wireMember
        exact firstResult.outside_restored wire
          ((List.disjoint_left.mp
            (qActualRowOutputWires_disjoint_rowSelectorWires p).symm) wireMember)
          ((List.disjoint_left.mp
            (qTopSelectorOutputWires_disjoint_rowSelectorWires p).symm) wireMember)
          (by
            intro equal
            exact qActualNegativeWire_not_mem_rowSelectorWires p
              (equal ▸ wireMember))
          (by
            intro equal
            exact qActualActiveWire_not_mem_rowSelectorWires p
              (equal ▸ wireMember))
      _ = constantBits selector.val (rowSelectorWires p).length :=
        afterRowSpec.selector_bits
  have selectorOutputAfterColumn :
      readWires (selectorOutputWires p) afterColumn =
        constantBits selector.val (selectorOutputWires p).length := by
    rw [firstResult.selector_output]
    rw [show readWires (selectorOutputWires p) afterRow =
        List.replicate (selectorOutputWires p).length false by
      simpa [selector, afterRow] using
        qActualAfterRowOraclePreimage_diagonal_selectorOutput_zero configuration
          site member copy]
    simpa [reference, constantBits, controlledXorConstantBits] using
      controlledXorConstantBits_true_replicate_false selector.val 0
        (selectorOutputWires p).length
  have selectorWidths : (selectorOutputWires p).length =
      (rowSelectorWires p).length := by
    simp [selectorOutputWires, rowSelectorWires]
  rw [selectorWidths] at selectorOutputAfterColumn
  unfold qActualAfterDiscriminatorPreimage
  rw [readWires_cnotBasisAction_of_not_mem (rowSelectorWires p)
    (activeWire p) (amplitudeSignalWire p) _
    (amplitudeSignalWire_not_mem_rowSelectorWires p)]
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis,
    controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readRowSelector]
  rw [qActualAfterColumnInversePreimage_diagonal_amplitude_true configuration site
    member copy]
  rw [selectorOutputAfterColumn, rowSelectorAfterColumn, if_pos rfl]
  rw [xorRegisterBits_self_eq_replicate_false]
  simp [constantBits]

/-- 対角 discriminator 逆追跡後はkey-signal bitが0へ戻る。 -/
theorem qActualAfterDiscriminatorPreimage_diagonal_keySignal_false
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterDiscriminatorPreimage p (delimiterEncoding configuration) selector
        (keySignalWire p) = false := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
  let afterFinal := qActualAfterFinalFlipPreimage p
    (delimiterEncoding configuration) selector
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding configuration) selector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding configuration) selector
  have rowResult : RowReferenceBranchResult p configuration selector afterFinal
      afterRow := by
    simpa [selector, afterFinal, afterRow] using
      qActualAfterRowOraclePreimage_diagonal_result configuration site member copy
  have columnResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [selector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_diagonal_result configuration site member copy
  have afterRowKey : afterRow (keySignalWire p) = true := by
    rw [rowResult.key_signal]
    rw [show afterFinal (keySignalWire p) = false by simp [afterFinal]]
    rfl
  have afterColumnKey : afterColumn (keySignalWire p) = true := by
    rw [columnResult.outside_restored (keySignalWire p)
      (qActualKeySignalWire_not_mem_rowOutputWires p)
      (qActualKeySignalWire_not_mem_selectorOutputWires p)
      (qActualNegativeWire_ne_keySignalWire p).symm
      (qActualActiveWire_ne_keySignalWire p).symm]
    exact afterRowKey
  unfold qActualAfterDiscriminatorPreimage
  rw [cnotBasisAction_control_or_other (activeWire p)
    (amplitudeSignalWire p) (keySignalWire p)
    (amplitudeSignalWire_ne_keySignalWire p).symm]
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis,
    controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_keySignal]
  rw [qActualAfterColumnInversePreimage_diagonal_amplitude_true configuration site
    member copy]
  rw [show qActualAfterColumnInversePreimage p
      (delimiterEncoding configuration) selector (keySignalWire p) = true by
    simpa [afterColumn] using afterColumnKey]
  rw [if_pos rfl]
  rfl

/-- 対角 discriminator 逆追跡後のsystem registerは同じ配置を保持する。 -/
theorem qActualAfterDiscriminatorPreimage_diagonal_readSystem
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    readWires (systemWires p)
        (qActualAfterDiscriminatorPreimage p (delimiterEncoding configuration)
          selector) = registerBitList (delimiterEncoding configuration) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding configuration) selector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding configuration) selector
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [selector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_diagonal_result configuration site member copy
  have afterRowSpec : RowOracleInputSpec p configuration selector afterRow :=
    RowReferenceBranchResult.preservesInputSpec
      (qActualAfterFinalFlipPreimage_rowOracleInputSpec p configuration selector)
      (by
        simpa [selector, afterRow] using
          qActualAfterRowOraclePreimage_diagonal_result configuration site member copy)
  have systemAfterColumn : readWires (systemWires p) afterColumn =
      registerBitList (delimiterEncoding configuration) := by
    calc
      readWires (systemWires p) afterColumn =
          readWires (systemWires p) afterRow := by
        apply List.map_congr_left
        intro wire wireMember
        exact firstResult.outside_restored wire
          ((List.disjoint_left.mp
            (qTopRowOutputWires_disjoint_systemWires p).symm) wireMember)
          ((List.disjoint_left.mp
            (qTopSelectorOutputWires_disjoint_systemWires p).symm) wireMember)
          (by
            intro equal
            exact qActualNegativeWire_not_mem_systemWires p
              (equal ▸ wireMember))
          (by
            intro equal
            exact qActualActiveWire_not_mem_systemWires p
              (equal ▸ wireMember))
      _ = registerBitList (delimiterEncoding configuration) := afterRowSpec.system_bits
  have rowOutputAfterColumn : readWires (rowOutputWires p) afterColumn =
      registerBitList (delimiterEncoding configuration) := by
    rw [firstResult.row_output]
    rw [show readWires (rowOutputWires p) afterRow =
        List.replicate (rowOutputWires p).length false by
      simpa [selector, afterRow] using
        qActualAfterRowOraclePreimage_diagonal_rowOutput_zero configuration site
          member copy]
    simpa [reference, xorRegisterBits, registerBitList, rowOutputWires] using
      xorRegisterBits_replicate_false
        (registerBitList (delimiterEncoding configuration))
  have columnKeyAfterColumn : readWires (columnKeyWires p) afterColumn =
      registerBitList (delimiterEncoding configuration) :=
    (ColumnReferenceBranchResult.preservesInputSpec
      (qActualAfterRowOraclePreimage_diagonal_columnInputSpec configuration site
        member copy) firstResult).column_key_bits
  unfold qActualAfterDiscriminatorPreimage
  rw [readWires_cnotBasisAction_of_not_mem (systemWires p)
    (activeWire p) (amplitudeSignalWire p) _
    (amplitudeSignalWire_not_mem_systemWires p)]
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis,
    controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readSystem]
  rw [qActualAfterColumnInversePreimage_diagonal_amplitude_true configuration site
    member copy]
  rw [rowOutputAfterColumn, columnKeyAfterColumn, systemAfterColumn]
  apply xorRegisterBits_sandwich
  simp [registerBitList]

/-- 対角pathの二回目column oracle後もsystem registerは同じ配置である。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_readSystem
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    readWires (systemWires p)
        (qActualAfterColumnOraclePreimage p (delimiterEncoding configuration)
          selector) = registerBitList (delimiterEncoding configuration) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  have result : ColumnReferenceBranchResult p reference before actual := by
    simpa [selector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_diagonal_result configuration site member copy
  calc
    readWires (systemWires p) actual = readWires (systemWires p) before := by
      apply List.map_congr_left
      intro wire wireMember
      exact result.outside_restored wire
        ((List.disjoint_left.mp
          (qTopRowOutputWires_disjoint_systemWires p).symm) wireMember)
        ((List.disjoint_left.mp
          (qTopSelectorOutputWires_disjoint_systemWires p).symm) wireMember)
        (by
          intro equal
          exact qActualNegativeWire_not_mem_systemWires p (equal ▸ wireMember))
        (by
          intro equal
          exact qActualActiveWire_not_mem_systemWires p (equal ▸ wireMember))
    _ = registerBitList (delimiterEncoding configuration) := by
      simpa [before, selector] using
        qActualAfterDiscriminatorPreimage_diagonal_readSystem configuration site
          member copy

/-- 対角pathの二回目column oracle後もrow-selector accumulatorは全0である。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_rowSelector_zero
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    readWires (rowSelectorWires p)
        (qActualAfterColumnOraclePreimage p (delimiterEncoding configuration)
          selector) = List.replicate (rowSelectorWires p).length false := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  have result : ColumnReferenceBranchResult p reference before actual := by
    simpa [selector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_diagonal_result configuration site member copy
  calc
    readWires (rowSelectorWires p) actual =
        readWires (rowSelectorWires p) before := by
      apply List.map_congr_left
      intro wire wireMember
      exact result.outside_restored wire
        ((List.disjoint_left.mp
          (qActualRowOutputWires_disjoint_rowSelectorWires p).symm) wireMember)
        ((List.disjoint_left.mp
          (qTopSelectorOutputWires_disjoint_rowSelectorWires p).symm) wireMember)
        (by
          intro equal
          exact qActualNegativeWire_not_mem_rowSelectorWires p
            (equal ▸ wireMember))
        (by
          intro equal
          exact qActualActiveWire_not_mem_rowSelectorWires p
            (equal ▸ wireMember))
    _ = List.replicate (rowSelectorWires p).length false := by
      simpa [before, selector] using
        qActualAfterDiscriminatorPreimage_diagonal_rowSelector_zero configuration
          site member copy

/-- 対角pathの二回目column oracle後もkey-signal bitは0である。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_keySignal_false
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnOraclePreimage p (delimiterEncoding configuration) selector
        (keySignalWire p) = false := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  have result : ColumnReferenceBranchResult p reference before actual := by
    simpa [selector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_diagonal_result configuration site member copy
  change actual (keySignalWire p) = false
  rw [result.outside_restored (keySignalWire p)
    (qActualKeySignalWire_not_mem_rowOutputWires p)
    (qActualKeySignalWire_not_mem_selectorOutputWires p)
    (qActualNegativeWire_ne_keySignalWire p).symm
    (qActualActiveWire_ne_keySignalWire p).symm]
  simpa [before, selector] using
    qActualAfterDiscriminatorPreimage_diagonal_keySignal_false configuration site
      member copy

/-- 対角pathの二回目column oracle後もamplitude signalは0である。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_amplitude_false
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnOraclePreimage p (delimiterEncoding configuration) selector
        (amplitudeSignalWire p) = false := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  have result : ColumnReferenceBranchResult p reference before actual := by
    simpa [selector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_diagonal_result configuration site member copy
  change actual (amplitudeSignalWire p) = false
  rw [result.outside_restored (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_rowOutputWires p)
    (amplitudeSignalWire_not_mem_selectorOutputWires p)
    (negativeWire_ne_amplitudeSignalWire p).symm
    (activeWire_ne_amplitudeSignalWire p).symm]
  simpa [before, selector] using
    qActualAfterDiscriminatorPreimage_diagonal_amplitude_false configuration site
      member copy

/-- 二回目column oracle後もcanonical key・selector・clean work仕様を満たす。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_columnInputSpec
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    ColumnOracleInputSpec p configuration selector
      (qActualAfterColumnOraclePreimage p (delimiterEncoding configuration)
        selector) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  exact ColumnReferenceBranchResult.preservesInputSpec
    (qActualAfterDiscriminatorPreimage_diagonal_columnInputSpec configuration site
      member copy)
    (qActualAfterColumnOraclePreimage_diagonal_result configuration site member copy)

/-- 二回目column oracle後はsystem・column-key・column-selector外の全wireが0である。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_outside_zero
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideSystem : wire ∉ systemWires p)
    (outsideColumnKey : wire ∉ columnKeyWires p)
    (outsideColumnSelector : wire ∉ columnSelectorWires p) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnOraclePreimage p (delimiterEncoding configuration) selector
      wire = false := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let reference : ColumnReferenceResult p := ⟨configuration, selector, true⟩
  let afterFinal := qActualAfterFinalFlipPreimage p
    (delimiterEncoding configuration) selector
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding configuration) selector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding configuration) selector
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding configuration) selector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  by_cases rowSelectorMember : wire ∈ rowSelectorWires p
  · exact readWires_eq_replicate_false_at (rowSelectorWires p) actual
      (by simpa [actual, selector] using
        (qActualAfterColumnOraclePreimage_diagonal_rowSelector_zero configuration
          site member copy)) rowSelectorMember
  by_cases rowOutputMember : wire ∈ rowOutputWires p
  · exact readWires_eq_replicate_false_at (rowOutputWires p) actual
      (by simpa [actual, selector] using
        (qActualAfterColumnOraclePreimage_diagonal_rowOutput_zero configuration site
          member copy)) rowOutputMember
  by_cases selectorOutputMember : wire ∈ selectorOutputWires p
  · exact readWires_eq_replicate_false_at (selectorOutputWires p) actual
      (by simpa [actual, selector] using
        (qActualAfterColumnOraclePreimage_diagonal_selectorOutput_zero configuration
          site member copy)) selectorOutputMember
  by_cases keyEqual : wire = keySignalWire p
  · subst wire
    exact qActualAfterColumnOraclePreimage_diagonal_keySignal_false configuration
      site member copy
  by_cases amplitudeEqual : wire = amplitudeSignalWire p
  · subst wire
    exact qActualAfterColumnOraclePreimage_diagonal_amplitude_false configuration
      site member copy
  by_cases negativeEqual : wire = negativeWire p
  · subst wire
    exact qActualAfterColumnOraclePreimage_diagonal_negative_false configuration
      site member copy
  by_cases activeEqual : wire = activeWire p
  · subst wire
    exact qActualAfterColumnOraclePreimage_diagonal_active_false configuration site
      member copy
  have rowResult : RowReferenceBranchResult p configuration selector afterFinal
      afterRow := by
    simpa [selector, afterFinal, afterRow] using
      qActualAfterRowOraclePreimage_diagonal_result configuration site member copy
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [selector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_diagonal_result configuration site member copy
  have secondResult : ColumnReferenceBranchResult p reference before actual := by
    simpa [selector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_diagonal_result configuration site member copy
  change actual wire = false
  rw [secondResult.outside_restored wire rowOutputMember selectorOutputMember
    negativeEqual activeEqual]
  rw [show before wire = afterColumn wire by
    exact qActualAfterDiscriminatorPreimage_eq_afterColumnInverse_on_wire p
      (delimiterEncoding configuration) selector wire outsideSystem
      rowSelectorMember keyEqual amplitudeEqual]
  rw [firstResult.outside_restored wire rowOutputMember selectorOutputMember
    negativeEqual activeEqual]
  rw [rowResult.outside_restored wire outsideColumnKey outsideColumnSelector
    keyEqual]
  apply qActualAfterFinalFlipPreimage_ancilla_zero
  · cases wire with
    | ancilla index => exact ⟨index, rfl⟩
    | system index =>
        exfalso
        apply outsideSystem
        exact List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩
  · exact rowSelectorMember
  · exact amplitudeEqual

/-- 二回目column oracle後の対角基底はcanonical COPY後基底に厳密一致する。 -/
theorem qActualAfterColumnOraclePreimage_diagonal_eq_copied
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualAfterColumnOraclePreimage p (delimiterEncoding configuration) selector =
      qCanonicalColumnCopiedBasis p configuration selector := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding configuration) selector
  let copied := qCanonicalColumnCopiedBasis p configuration selector
  have actualSpec : ColumnOracleInputSpec p configuration selector actual := by
    simpa [selector, actual] using
      qActualAfterColumnOraclePreimage_diagonal_columnInputSpec configuration site
        member copy
  have actualSystem : readWires (systemWires p) actual =
      registerBitList (delimiterEncoding configuration) := by
    simpa [selector, actual] using
      qActualAfterColumnOraclePreimage_diagonal_readSystem configuration site member
        copy
  have copiedSystem : readWires (systemWires p) copied =
      registerBitList (delimiterEncoding configuration) := by
    simpa [copied] using
      qCanonicalColumnCopiedBasis_readSystem p configuration selector
  have copiedKey : readWires (columnKeyWires p) copied =
      registerBitList (delimiterEncoding configuration) := by
    simpa [copied] using
      qCanonicalColumnCopiedBasis_readColumnKey p configuration selector
  have copiedSelector : readWires (columnSelectorWires p) copied =
      constantBits selector.val (columnSelectorWires p).length := by
    simpa [copied] using
      qCanonicalColumnCopiedBasis_readColumnSelector p configuration selector
  change actual = copied
  funext wire
  by_cases systemMember : wire ∈ systemWires p
  · exact readWires_eq_at_of_eq (systemWires p) actual copied
      (actualSystem.trans copiedSystem.symm) systemMember
  by_cases keyMember : wire ∈ columnKeyWires p
  · exact readWires_eq_at_of_eq (columnKeyWires p) actual copied
      (actualSpec.column_key_bits.trans copiedKey.symm) keyMember
  by_cases selectorMember : wire ∈ columnSelectorWires p
  · exact readWires_eq_at_of_eq (columnSelectorWires p) actual copied
      (actualSpec.selector_bits.trans copiedSelector.symm) selectorMember
  rw [show actual wire = false by
    simpa [actual, selector] using
      qActualAfterColumnOraclePreimage_diagonal_outside_zero configuration site
        member copy wire systemMember keyMember selectorMember]
  exact (qCanonicalColumnCopiedBasis_outside_zero p configuration selector wire
    systemMember keyMember selectorMember).symm

/-- 対角pathの全逆追跡preimageはcanonical column初期基底に厳密一致する。 -/
theorem qActualColumnPreparedPreimage_diagonal_eq_canonical
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualColumnPreparedPreimage p (delimiterEncoding configuration) selector =
      qCanonicalColumnInitialBasis p configuration selector := by
  dsimp only
  apply qActualColumnPreparedPreimage_eq_of_copy_runBasis
  exact (qActualAfterColumnOraclePreimage_diagonal_eq_copied configuration site
    member copy).symm

/-- 対角canonical row selectorに対するactual振幅は一様負振幅である。 -/
theorem qActualSelectorAmplitude_diagonal
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualSelectorAmplitude p (delimiterEncoding configuration)
        (delimiterEncoding configuration) selector =
      -((1 / Real.sqrt (p.selectorCount : ℝ)) : ℂ) := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  unfold qActualSelectorAmplitude
  rw [qBeforeRowUniformInverseState_finalSelector_of_canonical_preimage p
    configuration configuration selector selector true
    (qActualColumnPreparedPreimage_diagonal_eq_canonical configuration site member
      copy)
    (qActualSelectorPathPhase_diagonal_eq configuration site member copy)]
  simp

/-- 対角canonical row selectorではactual振幅が参照関数の期待振幅に一致する。 -/
theorem qActualSelectorAmplitude_diagonal_eq_expected
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset (slotOfMember configuration site member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    qActualSelectorAmplitude p (delimiterEncoding configuration)
        (delimiterEncoding configuration) selector =
      PrefixAmplitudeReferenceCaseSpec p (delimiterEncoding configuration)
        (delimiterEncoding configuration) selector := by
  dsimp only
  let selector := selectorOfSlotOffset (slotOfMember configuration site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  let rowResult : RowReferenceResult p := ⟨configuration, selector⟩
  let columnResult : ColumnReferenceResult p :=
    ⟨configuration, selector, true⟩
  have rowAccepted : rowReference configuration selector = some rowResult := by
    simpa [selector, rowResult] using
      rowReference_diagonal configuration site member copy
  have columnAccepted : columnReference configuration selector =
      some columnResult := by
    simpa [selector, columnResult] using
      columnReference_diagonal configuration site member copy
  have expected := PrefixAmplitudeReferenceCaseSpec_of_accepted configuration
    configuration selector rowResult columnResult rowAccepted columnAccepted rfl rfl
      rfl
  rw [qActualSelectorAmplitude_diagonal configuration site member copy]
  simpa [columnResult] using expected.symm

/--
任意の受理row参照について、全actual逆追跡preimageは返却predecessorのcanonical
column初期基底へ一致する。
-/
theorem qActualColumnPreparedPreimage_of_rowReference_some
    {p : QParameters} (output : QConfiguration p) (rowSelector : QSelector p)
    (rowResult : RowReferenceResult p)
    (rowAccepted : rowReference output rowSelector = some rowResult) :
    qActualColumnPreparedPreimage p (delimiterEncoding output) rowSelector =
      qCanonicalColumnInitialBasis p rowResult.input rowResult.columnSelector := by
  rcases rowReference_some_cases output rowSelector rowResult rowAccepted with
    diagonal | event
  · rcases diagonal with ⟨site, member, copy, selectorEq, resultEq⟩
    subst rowSelector
    subst rowResult
    exact qActualColumnPreparedPreimage_diagonal_eq_canonical output site member copy
  · rcases event with ⟨predecessor, source, member, direction, outputEq,
      rowSelectorEq, columnSelectorEq, inputEq⟩
    rw [← inputEq, ← columnSelectorEq]
    rw [← outputEq, ← rowSelectorEq]
    exact qActualColumnPreparedPreimage_physicalEvent_eq_canonical predecessor source
      member direction

/--
任意の受理row/column参照について、actual判別位相はcolumn参照のnegative bitと一致する。
-/
theorem qActualSelectorPathPhase_of_reference_some
    {p : QParameters} (output : QConfiguration p) (rowSelector : QSelector p)
    (rowResult : RowReferenceResult p) (columnResult : ColumnReferenceResult p)
    (rowAccepted : rowReference output rowSelector = some rowResult)
    (columnAccepted : columnReference rowResult.input rowResult.columnSelector =
      some columnResult) :
    qActualSelectorPathPhase p (delimiterEncoding output) rowSelector =
      if columnResult.negative then -1 else 1 := by
  rcases rowReference_some_cases output rowSelector rowResult rowAccepted with
    diagonal | event
  · rcases diagonal with ⟨site, member, copy, selectorEq, resultEq⟩
    subst rowSelector
    subst rowResult
    have value := columnReference_diagonal output site member copy
    have resultEq : columnResult =
        ⟨output,
          selectorOfSlotOffset (slotOfMember output site member)
            ⟨copy.val, lt_trans copy.isLt (by decide)⟩, true⟩ :=
      Option.some.inj (columnAccepted.symm.trans value)
    subst columnResult
    simpa using qActualSelectorPathPhase_diagonal_eq output site member copy
  · rcases event with ⟨predecessor, source, member, direction, outputEq,
      rowSelectorEq, columnSelectorEq, inputEq⟩
    rw [← inputEq, ← columnSelectorEq] at columnAccepted
    have value := columnReference_selectorForEvent_exact predecessor source member
      direction
    have resultEq : columnResult =
        ⟨eventOutput predecessor source direction,
          rowSelectorForEvent predecessor source member direction, false⟩ := by
      apply Option.some.inj
      rw [← columnAccepted]
      exact value
    subst columnResult
    rw [← outputEq, ← rowSelectorEq]
    simpa using qActualSelectorPathPhase_physicalEvent_eq_one predecessor source
      member direction

/--
任意の受理row/column参照では、評価入力をrow参照のpredecessorに取ったactual振幅が
一様振幅と参照符号の積へ厳密に一致する。
-/
theorem qActualSelectorAmplitude_of_reference_some
    {p : QParameters} (output : QConfiguration p) (rowSelector : QSelector p)
    (rowResult : RowReferenceResult p) (columnResult : ColumnReferenceResult p)
    (rowAccepted : rowReference output rowSelector = some rowResult)
    (columnAccepted : columnReference rowResult.input rowResult.columnSelector =
      some columnResult) :
    qActualSelectorAmplitude p (delimiterEncoding output)
        (delimiterEncoding rowResult.input) rowSelector =
      ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
        (if columnResult.negative then -1 else 1) := by
  unfold qActualSelectorAmplitude
  exact qBeforeRowUniformInverseState_finalSelector_of_canonical_preimage p
    rowResult.input output rowSelector rowResult.columnSelector
      columnResult.negative
      (qActualColumnPreparedPreimage_of_rowReference_some output rowSelector
        rowResult rowAccepted)
      (qActualSelectorPathPhase_of_reference_some output rowSelector rowResult
        columnResult rowAccepted columnAccepted)

end

end ProbabilityGeneratorQProof
