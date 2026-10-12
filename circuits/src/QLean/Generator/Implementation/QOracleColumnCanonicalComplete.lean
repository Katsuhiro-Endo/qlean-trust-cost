import QLean.Generator.Implementation.QOracleColumnEventComplete

/-!
# Q column oracle の canonical 入力に対する完全な基底作用

下位moduleで証明したpersistent clean性と一分岐のexact作用を合成し、合法なcanonical
COPY入力についてcolumn referenceと一致するfull oracle作用へ持ち上げる。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- column-key registerのwireは全membership出力wireと異なる。 -/
theorem columnKeyMembershipOutputsSeparated
    (p : QParameters) (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ columnKeyWires p) :
    MembershipOutputsSeparated p wire := by
  let layout := columnKeyWires_membershipInputLayout p
  refine {
    ne_equal := ?_
    ne_good := ?_
    ne_other := ?_
    ne_absent := ?_ }
  · intro slot equal
    exact (List.disjoint_left.mp layout.disjoint_membershipEqual member)
      (equal ▸ membershipEqualWireAt_mem_slice p slot)
  · intro slot equal
    exact (List.disjoint_left.mp layout.disjoint_membershipGood member)
      (equal ▸ membershipGoodWireAt_mem_slice p slot)
  · intro equal
    exact (List.disjoint_left.mp layout.disjoint_presentOther member)
      (equal ▸ oraclePresentOtherWire_mem_slice p)
  · intro equal
    exact (List.disjoint_left.mp
      (columnKeyWires_disjoint_oracleSlice p
        (OracleWorkLayout.canonical p).absent) member)
      (equal ▸ oracleAbsentWire_mem_slice p)

/-- column membership正本はcolumn-key register全体を保存する。 -/
theorem runBasis_columnEventMembership_columnKey
    (p : QParameters) (slot : Fin p.K)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : EventSortCleanInput p input) :
    readWires (columnKeyWires p)
        ((columnEventMembership p slot).runBasis reversibleGatePermutation input) =
      readWires (columnKeyWires p) input := by
  apply List.map_congr_left
  intro wire member
  exact runBasis_compiledXorMembershipMatchGoodAndAbsentFlagsCircuit_other p (columnKeyWires p)
    (columnKeyWires_membershipInputLayout p) slot true input
      {
        equalWork_zero := clean.moved_selector.compare_zero
        scratch_zero := clean.moved_selector.scratch_zero }
      wire (columnKeyMembershipOutputsSeparated p wire member)

/--
candidate準備はcolumn-key・present・movedを保存するので、membership読出し仕様を
candidate準備後へ持ち上げられる。
-/
theorem ConfigurationMembershipInput.of_prepareCandidatesColumn
    {p : QParameters} {configuration : QConfiguration p} {moved : QSite p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ConfigurationMembershipInput p (columnKeyWires p)
      configuration moved input) :
    ConfigurationMembershipInput p (columnKeyWires p) configuration moved
      ((xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
        reversibleGatePermutation input) := by
  let output := (xorConfigurationIntoCandidateRegisterCircuit p (columnKeyWires p)).runBasis
    reversibleGatePermutation input
  have preserve (wire : Wire p.ancillaWidth p.systemWidth)
      (outside : wire ∉ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).candidate).wireList :
          List (Wire p.ancillaWidth p.systemWidth))) :
      output wire = input wire :=
    runBasis_xorConfigurationIntoCandidateRegisterCircuit_outside_candidateSlice p (columnKeyWires p)
      (columnKeyWires_candidateInputLayout p) input wire outside
  refine {
    present := ?_
    active_word := ?_
    moved_word := ?_ }
  · intro slot
    change output (oraclePresentWireAt p slot) = _
    rw [preserve (oraclePresentWireAt p slot)]
    · exact specification.present slot
    · intro candidateMember
      exact (List.disjoint_left.mp
        (oraclePresentWires_disjoint_candidateSlice p)
        (by simp [oraclePresentWireAt, oraclePresentWires,
          QParameters.presentWidth])) candidateMember
  · intro slot active
    calc
      readWires (registerWordAt p (columnKeyWires p) slot) output =
          readWires (registerWordAt p (columnKeyWires p) slot) input := by
        apply List.map_congr_left
        intro wire member
        apply preserve wire
        exact (List.disjoint_left.mp
          (columnKeyWires_candidateInputLayout p).disjoint_candidate)
            (mem_register_of_mem_registerWordAt p (columnKeyWires p) slot member)
      _ = siteWordBits p (configuration.siteAt ⟨slot.val, active⟩) :=
        specification.active_word slot active
  · calc
      readWires (oracleMovedWires p) output =
          readWires (oracleMovedWires p) input := by
        apply List.map_congr_left
        intro wire member
        apply preserve wire
        intro candidateMember
        have movedMember : wire ∈ ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).moved).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
          simpa [oracleMovedWires, RegisterSlice.wireList] using member
        exact (List.disjoint_left.mp
          (RegisterSlice.wireList_disjoint_of_end_le_start
            (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
            (QLayout.oracleSlice (OracleWorkLayout.canonical p).candidate)
            (by simp [QLayout.oracleSlice, RegisterSlice.compose,
              OracleWorkLayout.canonical]; omega)) movedMember) candidateMember
      _ = siteWordBits p moved := specification.moved_word

/-- active slotに対するcolumn event prefixの完全な値仕様。 -/
structure ColumnEventPrefixSpec (p : QParameters)
    (configuration : QConfiguration p) (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  /-- branch直後もevent/sort workはcleanである。 -/
  after_branch_clean : EventSortCleanInput p
    (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
  /-- branch値は純粋membership条件に一致する。 -/
  branch_value : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
    (oracleBranchWire p) = columnEventMembershipCondition configuration
      (configuration.siteAt ⟨slot.val, active⟩) slot offset
  /-- persistent degree one-hotはbranch後も保存される。 -/
  degree_oneHot : ∀ current : Fin p.K,
    (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleDegreeWireAt p current) =
        decide (current.val + 1 = configuration.1.card)
  /-- forward move後のsite wordはbranch後も保存される。 -/
  moved_word : readWires (oracleMovedWires p)
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch =
    siteWordBits p
      (moveSite (configuration.siteAt ⟨slot.val, active⟩)
        (selectorDirection (selectorOfSlotOffset slot offset)))
  /-- candidate生成後もconfiguration membership仕様を保つ。 -/
  candidates_membership : ConfigurationMembershipInput p (columnKeyWires p)
    configuration
      (moveSite (configuration.siteAt ⟨slot.val, active⟩)
        (selectorDirection (selectorOfSlotOffset slot offset)))
    (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates
  /-- candidate生成直後の値関数はcanonical配置列である。 -/
  candidates_values : qCandidateValue p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterCandidates =
    configurationCandidateValue p configuration

/--
合法persistent状態と対応selectorから、selector・move・membership・branch・candidate準備の
実回路prefixを純粋参照仕様へ外部契約なしで接続する。
-/
theorem columnEventPrefix_correct
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : ColumnOraclePersistentConditionsSpec p configuration
      (selectorOfSlotOffset slot offset) input) :
    ColumnEventPrefixSpec p configuration slot offset active input := by
  let states := columnEventCandidateUpdateAndSortExecutionTrace p slot offset input
  let source := configuration.siteAt ⟨slot.val, active⟩
  let moved := moveSite source
    (selectorDirection (selectorOfSlotOffset slot offset))
  have selectorMatches : columnEventSelectorMatches p slot offset input = true := by
    simp [columnEventSelectorMatches, diagonalSelectorMatches,
      specification.selector_bits, selectorOfSlotOffset]
  have selectorClean : EventSortCleanInput p states.afterSelector := by
    rw [states.selector_eq]
    exact EventSortCleanInput.of_columnEventSelectorCompute p slot offset input
      specification.event_clean
  have movedClean : EventSortCleanInput p states.afterMoveForward := by
    have copiedClean : EventSortCleanInput p states.afterMovedCopy := by
      rw [states.movedCopy_eq]
      exact EventSortCleanInput.of_columnEventMovedCopy p slot _ selectorClean
    rw [states.moveForward_eq]
    exact EventSortCleanInput.of_columnEventMoveForward p offset _ copiedClean
  have membershipClean : EventSortCleanInput p states.afterMembership := by
    rw [states.membership_eq]
    exact EventSortCleanInput.of_columnEventMembership p slot _ movedClean
  have afterBranchClean : EventSortCleanInput p states.afterBranch :=
    columnEventCandidateUpdateAndSortExecutionTrace_afterBranch_clean p slot offset input
      specification.event_clean
  have moveMembership :=
    specification.afterMoveForward_membership slot offset active
  have flagsZero := specification.afterMoveForward_membershipZero slot offset
  have movedResult : readWires (oracleMovedWires p) states.afterMoveForward =
      siteWordBits p moved := by
    simpa [moved, source] using moveMembership.moved_word
  have earlierAtMove {width : Nat}
      (earlier : RegisterSlice p.oracleWorkWidth width)
      (beforeSelected : earlier.start + width ≤
        (OracleWorkLayout.canonical p).selected.start)
      (beforeMoved : earlier.start + width ≤
        (OracleWorkLayout.canonical p).moved.start)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ ((QLayout.oracleSlice earlier).wireList :
        List (Wire p.ancillaWidth p.systemWidth))) :
      states.afterMoveForward wire = input wire := by
    have outsideMoved : wire ∉ ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).moved).wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
      intro movedMember
      exact (List.disjoint_left.mp
        (RegisterSlice.wireList_disjoint_of_end_le_start
          (QLayout.oracleSlice earlier)
          (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
          (by simp [QLayout.oracleSlice, RegisterSlice.compose]; omega))
        member) movedMember
    have differentSelected : wire ≠ oracleSelectedWire p := by
      have selectedMember : oracleSelectedWire p ∈
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).selected).wireList :
              List (Wire p.ancillaWidth p.systemWidth)) := by
        simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
      exact oracleSliceMembers_ne_of_end_le_start p earlier
        (OracleWorkLayout.canonical p).selected beforeSelected member selectedMember
    calc
      states.afterMoveForward wire = states.afterSelector wire := by
        rw [states.moveForward_eq, states.movedCopy_eq]
        exact runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
          states.afterSelector selectorClean wire outsideMoved
      _ = input wire := by
        rw [states.selector_eq]
        exact runBasis_columnEventSelectorCompute_other p slot offset input
          specification.event_clean wire differentSelected
  have selectedAfterSelector : states.afterSelector (oracleSelectedWire p) = true := by
    rw [states.selector_eq]
    rw [runBasis_columnEventSelectorCompute_selected p slot offset input
      specification.event_clean.moved_selector.scratch_zero
      specification.selected_zero]
    exact selectorMatches
  have selectedAfterMove : states.afterMoveForward (oracleSelectedWire p) = true := by
    rw [states.moveForward_eq, states.movedCopy_eq]
    exact (runBasis_columnEventMovedCircuit_outside_movedSlice p slot offset
      states.afterSelector selectorClean (oracleSelectedWire p) (by
        intro movedMember
        have selectedMember : oracleSelectedWire p ∈
            ((QLayout.oracleSlice
              (OracleWorkLayout.canonical p).selected).wireList :
                List (Wire p.ancillaWidth p.systemWidth)) := by
          simp [oracleSelectedWire, oracleSingletonWire, RegisterSlice.wireList]
        exact (List.disjoint_left.mp
          (RegisterSlice.wireList_disjoint_of_end_le_start
            (QLayout.oracleSlice (OracleWorkLayout.canonical p).selected)
            (QLayout.oracleSlice (OracleWorkLayout.canonical p).moved)
            (by simp [QLayout.oracleSlice, RegisterSlice.compose,
              OracleWorkLayout.canonical])) selectedMember) movedMember)).trans
        selectedAfterSelector
  have legalAfterMove : states.afterMoveForward (oracleLegalWire p) = true :=
    (earlierAtMove (OracleWorkLayout.canonical p).legal
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (oracleLegalWire p) (by
        simp [oracleLegalWire, RegisterSlice.wireList])).trans specification.legal
  have presentAfterMove : states.afterMoveForward
      (oraclePresentWireAt p slot) = true := by
    rw [earlierAtMove (OracleWorkLayout.canonical p).present
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (oraclePresentWireAt p slot) (by
        simp [oraclePresentWireAt, RegisterSlice.wireList])]
    rw [specification.present slot]
    exact decide_eq_true active
  have degreeConditionAfterMove : states.afterMoveForward
      (oracleDegreeConditionWire p) = decide (1 < configuration.1.card) :=
    (earlierAtMove (OracleWorkLayout.canonical p).degreeCondition
      (by simp [OracleWorkLayout.canonical])
      (by simp [OracleWorkLayout.canonical])
      (oracleDegreeConditionWire p) (by
        simp [oracleDegreeConditionWire, oracleSingletonWire,
          RegisterSlice.wireList])).trans specification.degree_condition
  have branchAfterMove : states.afterMoveForward (oracleBranchWire p) = false := by
    have values := columnEventCandidateUpdateAndSortExecutionTrace_afterMoveForward_laterSlice p slot
      offset input specification.event_clean (OracleWorkLayout.canonical p).branch
        (by simp [OracleWorkLayout.canonical]; omega)
    exact (readWires_eq_at_of_eq _ _ _ values (by
      simp [oracleBranchWire, oracleSingletonWire, RegisterSlice.wireList])).trans
        specification.branch_zero
  have branchValue : states.afterBranch (oracleBranchWire p) =
      columnEventMembershipCondition configuration source slot offset := by
    rw [states.branch_eq, states.membership_eq]
    exact runBasis_columnEventMembership_branch_configuration p configuration
      source slot offset active rfl states.afterMoveForward moveMembership
      {
        equalWork_zero := movedClean.moved_selector.compare_zero
        scratch_zero := movedClean.moved_selector.scratch_zero }
      flagsZero legalAfterMove selectedAfterMove degreeConditionAfterMove
        branchAfterMove
  have degreeAfterBranch : ∀ current : Fin p.K,
      states.afterBranch (oracleDegreeWireAt p current) =
        decide (current.val + 1 = configuration.1.card) := by
    intro current
    have beforeMembership := earlierAtMove
      (OracleWorkLayout.canonical p).degree
      (by simp [OracleWorkLayout.canonical]; omega)
      (by simp [OracleWorkLayout.canonical]; omega)
      (oracleDegreeWireAt p current) (by
        simp [oracleDegreeWireAt, RegisterSlice.wireList])
    have membershipValues := runBasis_columnEventMembership_earlierSlice p slot
      (OracleWorkLayout.canonical p).degree (by
        simp [OracleWorkLayout.canonical]; omega) states.afterMoveForward movedClean
    rw [states.branch_eq, states.membership_eq]
    exact (runBasis_columnEventBranchCompute_other p slot offset
      states.afterMembership membershipClean (oracleDegreeWireAt p current) (by
        simpa [oracleDegreeWireAt, oracleBranchWire, oracleSingletonWire] using
          oracleSlice_ancillaWire_ne_of_localIndex_ne p
            (OracleWorkLayout.canonical p).degree
            (OracleWorkLayout.canonical p).branch current 0 (by
              simp [OracleWorkLayout.canonical]; omega))).trans
        ((readWires_eq_at_of_eq _ _ _ membershipValues (by
          simp [oracleDegreeWireAt, RegisterSlice.wireList])).trans
            (beforeMembership.trans (specification.degree current)))
  have movedAfterBranch : readWires (oracleMovedWires p) states.afterBranch =
      siteWordBits p moved := by
    rw [states.branch_eq]
    calc
      readWires (oracleMovedWires p)
          ((columnEventBranchCompute p slot offset).runBasis
            reversibleGatePermutation states.afterMembership) =
          readWires (oracleMovedWires p) states.afterMembership := by
        apply List.map_congr_left
        intro wire member
        exact runBasis_columnEventBranchCompute_other p slot offset
          states.afterMembership membershipClean wire (by
            have movedMember : wire ∈ ((QLayout.oracleSlice
                (OracleWorkLayout.canonical p).moved).wireList :
                  List (Wire p.ancillaWidth p.systemWidth)) := by
              simpa [oracleMovedWires, RegisterSlice.wireList] using member
            have branchMember : oracleBranchWire p ∈ ((QLayout.oracleSlice
                (OracleWorkLayout.canonical p).branch).wireList :
                  List (Wire p.ancillaWidth p.systemWidth)) := by
              simp [oracleBranchWire, oracleSingletonWire,
                RegisterSlice.wireList]
            exact oracleSliceMembers_ne_of_end_le_start p
              (OracleWorkLayout.canonical p).moved
              (OracleWorkLayout.canonical p).branch (by
                simp [OracleWorkLayout.canonical]; omega) movedMember branchMember)
      _ = readWires (oracleMovedWires p) states.afterMoveForward := by
        rw [states.membership_eq]
        exact runBasis_columnEventMembership_earlierSlice p slot
          (OracleWorkLayout.canonical p).moved (by
            simp [OracleWorkLayout.canonical]; omega) states.afterMoveForward
              movedClean
      _ = siteWordBits p moved := movedResult
  have afterBranchMembership : ConfigurationMembershipInput p
      (columnKeyWires p) configuration moved states.afterBranch := by
    refine {
      present := ?_
      active_word := ?_
      moved_word := movedAfterBranch }
    · intro current
      have beforeMembership := earlierAtMove
        (OracleWorkLayout.canonical p).present
        (by simp [OracleWorkLayout.canonical]; omega)
        (by simp [OracleWorkLayout.canonical]; omega)
        (oraclePresentWireAt p current) (by
          simp [oraclePresentWireAt, RegisterSlice.wireList])
      have membershipValues := runBasis_columnEventMembership_earlierSlice p slot
        (OracleWorkLayout.canonical p).present (by
          simp [OracleWorkLayout.canonical]; omega) states.afterMoveForward movedClean
      rw [states.branch_eq, states.membership_eq]
      exact (runBasis_columnEventBranchCompute_other p slot offset
        states.afterMembership membershipClean (oraclePresentWireAt p current) (by
          simpa [oraclePresentWireAt, oracleBranchWire, oracleSingletonWire] using
            oracleSlice_ancillaWire_ne_of_localIndex_ne p
              (OracleWorkLayout.canonical p).present
              (OracleWorkLayout.canonical p).branch current 0 (by
                simp [OracleWorkLayout.canonical]; omega))).trans
          ((readWires_eq_at_of_eq _ _ _ membershipValues (by
            simp [oraclePresentWireAt, RegisterSlice.wireList])).trans
              (beforeMembership.trans (specification.present current)))
    · intro current currentActive
      rw [states.branch_eq, states.membership_eq]
      calc
        readWires (registerWordAt p (columnKeyWires p) current)
            ((columnEventBranchCompute p slot offset).runBasis
              reversibleGatePermutation states.afterMembership) =
            readWires (registerWordAt p (columnKeyWires p) current)
              states.afterMembership := by
          apply List.map_congr_left
          intro wire member
          exact runBasis_columnEventBranchCompute_other p slot offset
            states.afterMembership membershipClean wire (by
              intro equal
              subst wire
              exact oracleBranchWire_not_mem_columnKeyWires p
                (mem_register_of_mem_registerWordAt p (columnKeyWires p) current
                  member))
        _ = readWires (registerWordAt p (columnKeyWires p) current)
            states.afterMoveForward := by
          have values := runBasis_columnEventMembership_columnKey p slot
            states.afterMoveForward movedClean
          apply List.map_congr_left
          intro wire member
          exact readWires_eq_at_of_eq _ _ _ values
            (mem_register_of_mem_registerWordAt p (columnKeyWires p) current member)
        _ = siteWordBits p
            (configuration.siteAt ⟨current.val, currentActive⟩) :=
          moveMembership.active_word current currentActive
  have candidateZero := specification.afterBranch_candidateZero slot offset
  have candidatesMembership : ConfigurationMembershipInput p (columnKeyWires p)
      configuration moved states.afterCandidates := by
    rw [states.candidates_eq]
    exact afterBranchMembership.of_prepareCandidatesColumn
  have candidatesValues : qCandidateValue p states.afterCandidates =
      configurationCandidateValue p configuration := by
    rw [states.candidates_eq]
    exact qCandidateValue_runBasis_prepareCandidates_register_configuration p
      (columnKeyWires p) (columnKeyWires_candidateInputLayout p) configuration
        moved states.afterBranch afterBranchMembership candidateZero
  refine {
    after_branch_clean := afterBranchClean
    branch_value := by simpa [source] using branchValue
    degree_oneHot := degreeAfterBranch
    moved_word := by simpa [moved] using movedAfterBranch
    candidates_membership := by simpa [moved] using candidatesMembership
    candidates_values := candidatesValues }

/-- 配置に属するsiteのcanonical slotは配置粒子数未満である。 -/
theorem columnSlotOfMember_lt_configurationCard
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) :
    (slotOfMember configuration site member).val < configuration.1.card := by
  unfold slotOfMember
  exact ((configuration.1.orderIsoOfFin rfl).symm ⟨site, member⟩).isLt

/--
prefixの純粋membership条件が真なら、candidate変更・sortを含むcompute末尾は更新配置の
active writer仕様を満たす。
-/
theorem columnEventActiveComputedSpec_of_prefix
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (prefixSpec : ColumnEventPrefixSpec p configuration slot offset active input)
    (conditionTrue : columnEventMembershipCondition configuration
      (configuration.siteAt ⟨slot.val, active⟩) slot offset = true) :
    let source := configuration.siteAt ⟨slot.val, active⟩
    let direction := selectorDirection (selectorOfSlotOffset slot offset)
    let outputConfiguration := updateConfiguration configuration (source, direction)
    let moved := moveSite source direction
    let movedMember : moved ∈ outputConfiguration.1 :=
      moveSite_mem_updateConfiguration configuration (source, direction)
        ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
    ∃ degreeSlot : Fin p.K,
      ColumnEventActiveComputedSpec p outputConfiguration moved movedMember offset
        degreeSlot (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output := by
  dsimp only
  let source := configuration.siteAt ⟨slot.val, active⟩
  let direction := selectorDirection (selectorOfSlotOffset slot offset)
  let outputConfiguration := updateConfiguration configuration (source, direction)
  let moved := moveSite source direction
  have sourceMember : source ∈ configuration.1 :=
    ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
  have movedMember : moved ∈ outputConfiguration.1 :=
    moveSite_mem_updateConfiguration configuration (source, direction) sourceMember
  have inputCardPositive : 0 < configuration.1.card := configuration.2.1
  let degreeSlot : Fin p.K := ⟨configuration.1.card - 1, by omega⟩
  have degreeBoundary : degreeSlot.val + 1 = configuration.1.card := by
    simp [degreeSlot]
    omega
  have degreeOneHot : ∀ current : Fin p.K,
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
        (oracleDegreeWireAt p current) = decide (current = degreeSlot) := by
    intro current
    rw [prefixSpec.degree_oneHot current]
    congr 1
    apply propext
    constructor
    · intro equal
      apply Fin.ext
      simp [degreeSlot]
      omega
    · intro equal
      have values := congrArg Fin.val equal
      simp [degreeSlot] at values
      omega
  have branchTrue : (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).afterBranch
      (oracleBranchWire p) = true := prefixSpec.branch_value.trans conditionTrue
  have candidateValues : qCandidateValue p
      (columnEventCandidateUpdateAndSortExecutionTrace p slot offset input).output =
        configurationCandidateValue p outputConfiguration := by
    by_cases collision : offset.val % 2 = 1
    · have physicalCollision : moved ∈ configuration.1.erase source := by
        have condition := conditionTrue
        simp [columnEventMembershipCondition, collision] at condition
        exact Finset.mem_erase.mpr (by
          simpa [moved, source, direction] using condition.1)
      apply columnEventCandidateUpdateAndSortExecutionTrace_collision_candidateValues configuration
        source sourceMember direction physicalCollision slot offset collision rfl
          active rfl input
      · simpa [moved, source, direction] using prefixSpec.candidates_membership
      · exact prefixSpec.candidates_values
      · exact branchTrue
      · exact prefixSpec.after_branch_clean
    · have noCollisionFull : moved ∉ configuration.1 := by
        have condition := conditionTrue
        simp [columnEventMembershipCondition, collision] at condition
        simpa [moved, source, direction] using condition
      have noCollision : moved ∉ configuration.1.erase source := by
        intro member
        exact noCollisionFull (Finset.mem_of_mem_erase member)
      apply columnEventCandidateUpdateAndSortExecutionTrace_replacement_candidateValues configuration
        source sourceMember direction noCollision slot offset collision active rfl input
      · simpa [moved, source, direction] using prefixSpec.candidates_membership
      · exact prefixSpec.candidates_values
      · exact branchTrue
      · exact prefixSpec.after_branch_clean
  have outputDegree : Int.ofNat (degreeSlot.val + 1) +
      columnEventDegreeChange offset = Int.ofNat outputConfiguration.1.card := by
    by_cases collision : offset.val % 2 = 1
    · have physicalCollision : moved ∈ configuration.1.erase source := by
        have condition := conditionTrue
        simp [columnEventMembershipCondition, collision] at condition
        exact Finset.mem_erase.mpr (by
          simpa [moved, source, direction] using condition.1)
      have cardDrop := updateConfiguration_card_add_one_of_collision
        configuration (source, direction) sourceMember physicalCollision
      change outputConfiguration.1.card + 1 = configuration.1.card at cardDrop
      simp [columnEventDegreeChange, collision, degreeBoundary]
      omega
    · have noCollisionFull : moved ∉ configuration.1 := by
        have condition := conditionTrue
        simp [columnEventMembershipCondition, collision] at condition
        simpa [moved, source, direction] using condition
      have noCollision : moved ∉ configuration.1.erase source := by
        intro member
        exact noCollisionFull (Finset.mem_of_mem_erase member)
      have cardSame := updateConfiguration_card_of_noCollision
        configuration (source, direction) sourceMember noCollision
      change outputConfiguration.1.card = configuration.1.card at cardSame
      simp [columnEventDegreeChange, collision, degreeBoundary]
      omega
  refine ⟨degreeSlot, ColumnEventActiveComputedSpec.of_afterBranch outputDegree
    prefixSpec.after_branch_clean branchTrue degreeOneHot candidateValues ?_⟩
  simpa [moved, source, direction] using prefixSpec.moved_word

/-- active membership条件が偽なら、actual column event branchは厳密な恒等作用である。 -/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_prefix
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (prefixSpec : ColumnEventPrefixSpec p configuration slot offset active input)
    (conditionFalse : columnEventMembershipCondition configuration
      (configuration.siteAt ⟨slot.val, active⟩) slot offset = false) :
    (applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input = input := by
  apply applyColumnEventReferenceAndRestoreWorkCircuit_inactive_of_afterBranch p slot offset input
    prefixSpec.after_branch_clean
  exact prefixSpec.branch_value.trans conditionFalse

/-- active membership条件が真なら、actual branchは更新配置の参照出力を返す。 -/
theorem applyColumnEventReferenceAndRestoreWorkCircuit_active_of_prefix
    {p : QParameters} (configuration : QConfiguration p)
    (slot : Fin p.K) (offset : Fin 6)
    (active : slot.val < configuration.1.card)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (prefixSpec : ColumnEventPrefixSpec p configuration slot offset active input)
    (conditionTrue : columnEventMembershipCondition configuration
      (configuration.siteAt ⟨slot.val, active⟩) slot offset = true) :
    let source := configuration.siteAt ⟨slot.val, active⟩
    let direction := selectorDirection (selectorOfSlotOffset slot offset)
    let outputConfiguration := updateConfiguration configuration (source, direction)
    let moved := moveSite source direction
    let movedMember : moved ∈ outputConfiguration.1 :=
      moveSite_mem_updateConfiguration configuration (source, direction)
        ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2
    ColumnEventActiveBranchResult p outputConfiguration moved movedMember offset input
      ((applyColumnEventReferenceAndRestoreWorkCircuit p slot offset).runBasis
        reversibleGatePermutation input) := by
  dsimp only
  obtain ⟨degreeSlot, computed⟩ :=
    columnEventActiveComputedSpec_of_prefix configuration slot offset active input
      prefixSpec conditionTrue
  exact applyColumnEventReferenceAndRestoreWorkCircuit_active_of_computedSpec p slot offset
    (updateConfiguration configuration
      (configuration.siteAt ⟨slot.val, active⟩,
        selectorDirection (selectorOfSlotOffset slot offset)))
    (moveSite (configuration.siteAt ⟨slot.val, active⟩)
      (selectorDirection (selectorOfSlotOffset slot offset)))
    (moveSite_mem_updateConfiguration configuration
      (configuration.siteAt ⟨slot.val, active⟩,
        selectorDirection (selectorOfSlotOffset slot offset))
      ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, active⟩).2)
    degreeSlot input computed

end ReversibleCircuit

end ProbabilityGeneratorQProof
