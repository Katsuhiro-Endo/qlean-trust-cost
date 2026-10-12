import QLean.Generator.Analysis.ProbabilityGeneratorFullOperator
import QLean.Generator.Analysis.QComponentAnalyticSpecs

/-!
# Human-facing mathematical specifications for Q3, Q7, Q10, and Q11

The row and column oracles are independent mathematical nodes.  Their clean
meaning is expressed on semantic configurations, selectors, and external XOR
accumulators.  The canonical all-wire operators remain separate full-dirty
reversible extensions.  The full probability-generator operator is then a
nine-stage product whose oracle children are not re-expanded here.
-/

namespace ProbabilityGeneratorQProof

open VerifiedCircuitCore

noncomputable section

/-! ## Shared event data exposed at the Q3/Q7 semantic boundary -/

/-- Sites of a legal configuration in the canonical increasing order used by
the mathematical selector convention.  This is a value-level list; it does not
refer to a candidate register or to a sorting circuit. -/
def qConfigurationSitesInCanonicalOrder {p : QParameters}
    (configuration : QConfiguration p) : List (QSite p) :=
  (List.finRange configuration.1.card).map fun slot =>
    ((configuration.1.orderIsoOfFin rfl) slot).1

/-- Human-level candidate array after canonical sorting.  `none` denotes a
padding word.  The physical marker encoding is an implementation detail linked
later by the candidate/sort components. -/
def qOracleSortedCandidateWords {p : QParameters}
    (configuration : QConfiguration p) : List (Option (QSite p)) :=
  (qConfigurationSitesInCanonicalOrder configuration).map some ++
    List.replicate (p.sortWordCount - configuration.1.card) none

@[simp] theorem qConfigurationSitesInCanonicalOrder_length
    {p : QParameters} (configuration : QConfiguration p) :
    (qConfigurationSitesInCanonicalOrder configuration).length =
      configuration.1.card := by
  simp [qConfigurationSitesInCanonicalOrder]

/-- Candidate storage has exactly the shared bitonic array width for every
positive `q,K`; no representative parameter is used. -/
@[simp] theorem qOracleSortedCandidateWords_length {p : QParameters}
    (configuration : QConfiguration p) :
    (qOracleSortedCandidateWords configuration).length = p.sortWordCount := by
  have cardLe : configuration.1.card ≤ p.sortWordCount :=
    le_trans configuration.2.2 p.K_le_sortWordCount
  simp [qOracleSortedCandidateWords, cardLe]

/-- Removing padding from the human candidate array recovers exactly the
canonical configuration-site list. -/
@[simp] theorem qOracleSortedCandidateWords_filterMap
    {p : QParameters} (configuration : QConfiguration p) :
    (qOracleSortedCandidateWords configuration).filterMap id =
      qConfigurationSitesInCanonicalOrder configuration := by
  simp [qOracleSortedCandidateWords]

/--
All mathematical data carried by one accepted physical event.  The candidate
set and its sorted padded list are exposed separately from the two selector
values and the delimiter output written by Q3/Q7.
-/
structure QOracleEventUnderstandingSnapshot (p : QParameters) where
  inputConfiguration : QConfiguration p
  sourceSite : QSite p
  direction : QDirection
  movedSite : QSite p
  collision : Bool
  columnSelector : QSelector p
  outputConfiguration : QConfiguration p
  candidateSet : Finset (QSite p)
  sortedCandidateWords : List (Option (QSite p))
  rowSelector : QSelector p
  outputWord : RegisterBasis p.systemWidth

/-- Canonical semantic snapshot of one source site and one move direction. -/
def qOracleEventUnderstandingSnapshot {p : QParameters}
    (input : QConfiguration p) (source : QSite p) (member : source ∈ input.1)
    (direction : QDirection) : QOracleEventUnderstandingSnapshot p :=
  let output := eventOutput input source direction
  { inputConfiguration := input
    sourceSite := source
    direction := direction
    movedSite := moveSite source direction
    collision := eventCollision input source direction
    columnSelector := selectorForEvent input source member direction
    outputConfiguration := output
    candidateSet := output.1
    sortedCandidateWords := qOracleSortedCandidateWords output
    rowSelector := rowSelectorForEvent input source member direction
    outputWord := delimiterEncoding output }

@[simp] theorem qOracleEventUnderstandingSnapshot_outputConfiguration
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    (qOracleEventUnderstandingSnapshot input source member direction).outputConfiguration =
      eventOutput input source direction := rfl

@[simp] theorem qOracleEventUnderstandingSnapshot_candidateSet
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    (qOracleEventUnderstandingSnapshot input source member direction).candidateSet =
      (eventOutput input source direction).1 := rfl

@[simp] theorem qOracleEventUnderstandingSnapshot_sortedCandidateWords
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    (qOracleEventUnderstandingSnapshot input source member direction).sortedCandidateWords =
      qOracleSortedCandidateWords (eventOutput input source direction) := rfl

@[simp] theorem qOracleEventUnderstandingSnapshot_outputWord
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    (qOracleEventUnderstandingSnapshot input source member direction).outputWord =
      delimiterEncoding (eventOutput input source direction) := rfl

/-! ### Independently reviewable decoder/candidate/writer values -/

/-- Mathematical data computed once by the persistent decoder and reused by
all six branches of a selected slot.  It deliberately contains no physical
work-wire or decoder encoding. -/
structure QOraclePersistentSemanticRecord (p : QParameters) where
  configuration : QConfiguration p
  selector : QSelector p
  selectedSite : Option (QSite p)
  present : Fin p.K → Bool
  degree : Nat
  deriving DecidableEq

/-- Pure persistent information derived from a configuration/selector pair. -/
def qOraclePersistentSemanticRecord {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p) :
    QOraclePersistentSemanticRecord p :=
  { configuration := configuration
    selector := selector
    selectedSite :=
      (configurationSlot? configuration (selectorSlot selector)).map
        Subtype.val
    present := fun slot => (configurationSlot? configuration slot).isSome
    degree := configuration.1.card }

@[simp] theorem qOraclePersistentSemanticRecord_degree {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p) :
    (qOraclePersistentSemanticRecord configuration selector).degree =
      configuration.1.card := rfl

@[simp] theorem qOraclePersistentSemanticRecord_present {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p)
    (slot : Fin p.K) :
    (qOraclePersistentSemanticRecord configuration selector).present slot =
      (configurationSlot? configuration slot).isSome := rfl

/-- Candidate set before physical encoding/sorting. -/
def qOracleEventCandidateSet {p : QParameters}
    (input : QConfiguration p) (source : QSite p) (_member : source ∈ input.1)
    (direction : QDirection) : Finset (QSite p) :=
  (eventOutput input source direction).1

/-- Canonically sorted, padded event words. -/
def qOracleEventSortedCandidateWords {p : QParameters}
    (input : QConfiguration p) (source : QSite p) (_member : source ∈ input.1)
    (direction : QDirection) : List (Option (QSite p)) :=
  qOracleSortedCandidateWords (eventOutput input source direction)

/-- Mathematical moved-selector value written by the column event. -/
def qOracleEventMovedSelector {p : QParameters}
    (input : QConfiguration p) (source : QSite p) (member : source ∈ input.1)
    (direction : QDirection) : QSelector p :=
  rowSelectorForEvent input source member direction

/-- Mathematical delimiter word written by the event output stage. -/
def qOracleEventOutputWord {p : QParameters}
    (input : QConfiguration p) (source : QSite p) (_member : source ∈ input.1)
    (direction : QDirection) : RegisterBasis p.systemWidth :=
  delimiterEncoding (eventOutput input source direction)

@[simp] theorem qOracleEventUnderstandingSnapshot_candidateSet_eq_specification
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    (qOracleEventUnderstandingSnapshot input source member direction).candidateSet =
      qOracleEventCandidateSet input source member direction := rfl

@[simp] theorem qOracleEventUnderstandingSnapshot_sortedWords_eq_specification
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    (qOracleEventUnderstandingSnapshot input source member direction).sortedCandidateWords =
      qOracleEventSortedCandidateWords input source member direction := rfl

@[simp] theorem qOracleEventUnderstandingSnapshot_movedSelector_eq_specification
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    (qOracleEventUnderstandingSnapshot input source member direction).rowSelector =
      qOracleEventMovedSelector input source member direction := rfl

@[simp] theorem qOracleEventUnderstandingSnapshot_outputWord_eq_specification
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    (qOracleEventUnderstandingSnapshot input source member direction).outputWord =
      qOracleEventOutputWord input source member direction := rfl

/-! ## Q3 column-oracle clean semantics -/

/-- Q3 semantic partial reference, named independently from the legacy public
name so that the human-facing record below has a stable endpoint. -/
def q3ColumnSemanticReference {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p) :
    Option (ColumnReferenceResult p) :=
  columnReference configuration selector

/-- Q3b reference restricted to the two diagonal offsets. -/
def q3ColumnDiagonalSemanticReference {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p) :
    Option (ColumnReferenceResult p) :=
  if (selectorOffset selector).val < 2 then
    q3ColumnSemanticReference configuration selector
  else none

/-- Q3c reference restricted to the four event offsets. -/
def q3ColumnEventSemanticReference {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p) :
    Option (ColumnReferenceResult p) :=
  if (selectorOffset selector).val < 2 then none
  else q3ColumnSemanticReference configuration selector

/-- Q3 is the disjoint union of its diagonal and event semantic references. -/
theorem q3ColumnSemanticReference_eq_diagonal_or_event {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p) :
    q3ColumnSemanticReference configuration selector =
      match q3ColumnDiagonalSemanticReference configuration selector with
      | some result => some result
      | none => q3ColumnEventSemanticReference configuration selector := by
  by_cases diagonal : (selectorOffset selector).val < 2
  · simp only [q3ColumnDiagonalSemanticReference,
      q3ColumnEventSemanticReference, diagonal, if_pos]
    cases q3ColumnSemanticReference configuration selector <;> rfl
  · simp [q3ColumnDiagonalSemanticReference,
      q3ColumnEventSemanticReference, diagonal]

theorem q3ColumnSemanticReference_eq_columnReference {p : QParameters} :
    q3ColumnSemanticReference (p := p) = columnReference := rfl

theorem q3ColumnSemanticReference_eq_none_of_missing
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (missing : configurationSlot? configuration (selectorSlot selector) = none) :
    q3ColumnSemanticReference configuration selector = none := by
  unfold q3ColumnSemanticReference columnReference
  rw [missing]

theorem q3ColumnSemanticReference_diagonal
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset
      (slotOfMember configuration source member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    q3ColumnSemanticReference configuration selector =
      some ⟨configuration, selector, true⟩ := by
  dsimp only
  simpa [q3ColumnSemanticReference] using
    (columnReference_diagonal configuration source member copy)

/-- Q3 external accumulator action defined directly from its semantic partial
reference. -/
def q3ColumnSemanticAccumulatorAction {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p)
    (observation : ColumnOracleObservation) : ColumnOracleObservation :=
  match q3ColumnSemanticReference configuration selector with
  | none => observation
  | some reference => applyColumnReference reference observation

/-- Q3 accumulator action displayed as the explicit Q3b/Q3c branch union. -/
def q3ColumnBranchSemanticAccumulatorAction {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p)
    (observation : ColumnOracleObservation) : ColumnOracleObservation :=
  match q3ColumnDiagonalSemanticReference configuration selector with
  | some reference => applyColumnReference reference observation
  | none =>
      match q3ColumnEventSemanticReference configuration selector with
      | some reference => applyColumnReference reference observation
      | none => observation

theorem q3ColumnSemanticAccumulatorAction_eq_branches {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p)
    (observation : ColumnOracleObservation) :
    q3ColumnSemanticAccumulatorAction configuration selector observation =
      q3ColumnBranchSemanticAccumulatorAction
        configuration selector observation := by
  unfold q3ColumnSemanticAccumulatorAction
    q3ColumnBranchSemanticAccumulatorAction
  rw [q3ColumnSemanticReference_eq_diagonal_or_event]
  cases q3ColumnDiagonalSemanticReference configuration selector <;>
    cases q3ColumnEventSemanticReference configuration selector <;> rfl

theorem q3ColumnSemanticAccumulatorAction_eq_established {p : QParameters} :
    q3ColumnSemanticAccumulatorAction (p := p) = columnOracleAnalyticAction := rfl

/-! ### Finite clean computational basis for Q3 -/

/-- Pointwise XOR on a fixed-width mathematical register. -/
def qOracleXorRegister {width : Nat}
    (source target : RegisterBasis width) : RegisterBasis width :=
  fun wire => source wire != target wire

/-- Fixed-width little-endian encoding of a semantic selector. -/
def qOracleSelectorRegister {p : QParameters}
    (selector : QSelector p) : RegisterBasis p.selectorWidth :=
  fun bit => selector.val.testBit bit.val

/-- Pure little-endian value of a fixed-width register.  This local definition
keeps the understanding specification independent of the circuit-side uniform
preparation API. -/
def qOracleSelectorValue : (width : Nat) → RegisterBasis width → Nat
  | 0, _ => 0
  | width + 1, basis =>
      (if basis (Fin.last width) then 2 ^ width else 0) +
        qOracleSelectorValue width (fun index => basis index.castSucc)

/-- A fixed-width selector value is below its binary capacity. -/
theorem qOracleSelectorValue_lt_capacity :
    ∀ (width : Nat) (basis : RegisterBasis width),
      qOracleSelectorValue width basis < 2 ^ width
  | 0, _ => by simp [qOracleSelectorValue]
  | width + 1, basis => by
      rw [qOracleSelectorValue, Nat.pow_succ]
      have lowerBound := qOracleSelectorValue_lt_capacity width
        (fun index => basis index.castSucc)
      split <;> omega

/-- Every in-range bit of the pure selector value is the corresponding
register bit. -/
theorem qOracleSelectorValue_testBit :
    ∀ (width : Nat) (basis : RegisterBasis width) (index : Fin width),
      (qOracleSelectorValue width basis).testBit index.val = basis index
  | 0, _, index => Fin.elim0 index
  | width + 1, basis, index => by
      let lower : RegisterBasis width :=
        fun lowerIndex => basis lowerIndex.castSucc
      have lowerBound : qOracleSelectorValue width lower < 2 ^ width :=
        qOracleSelectorValue_lt_capacity width lower
      have valueShape :
          qOracleSelectorValue (width + 1) basis =
            2 ^ width * (basis (Fin.last width)).toNat +
              qOracleSelectorValue width lower := by
        simp only [qOracleSelectorValue, lower]
        cases basis (Fin.last width) <;> simp
      rw [valueShape]
      refine Fin.lastCases ?_ (fun lowerIndex => ?_) index
      · rw [Nat.testBit_two_pow_mul_add _ lowerBound]
        cases highest : basis (Fin.last width) <;> simp
      · rw [Nat.testBit_two_pow_mul_add _ lowerBound]
        simp only [Fin.val_castSucc, lowerIndex.isLt, if_true]
        exact qOracleSelectorValue_testBit width lower lowerIndex

/-- Decoding the fixed-width semantic selector register recovers the typed
selector value. -/
@[simp] theorem qOracleSelectorValue_qOracleSelectorRegister
    {p : QParameters} (selector : QSelector p) :
    qOracleSelectorValue p.selectorWidth
        (qOracleSelectorRegister selector) = selector.val := by
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases inRange : index < p.selectorWidth
  · let finiteIndex : Fin p.selectorWidth := ⟨index, inRange⟩
    have decoded := qOracleSelectorValue_testBit p.selectorWidth
      (qOracleSelectorRegister selector) finiteIndex
    simpa [qOracleSelectorRegister, finiteIndex] using decoded
  · have widthLe : p.selectorWidth ≤ index := Nat.le_of_not_gt inRange
    have decodedLt : qOracleSelectorValue p.selectorWidth
        (qOracleSelectorRegister selector) < 2 ^ index :=
      lt_of_lt_of_le
        (qOracleSelectorValue_lt_capacity p.selectorWidth
          (qOracleSelectorRegister selector))
        (Nat.pow_le_pow_right (by decide) widthLe)
    have selectorLt : selector.val < 2 ^ index :=
      lt_of_lt_of_le
        (lt_of_lt_of_le selector.isLt p.selectorCount_le_capacity)
        (Nat.pow_le_pow_right (by decide) widthLe)
    rw [Nat.testBit_lt_two_pow decodedLt,
      Nat.testBit_lt_two_pow selectorLt]

theorem analyticRegisterBits_eq_ofFn {width : Nat}
    (basis : RegisterBasis width) :
    analyticRegisterBits basis = List.ofFn basis := by
  rw [List.ofFn_eq_map]
  rfl

private theorem qOracleZipWithXor_ofFn {width : Nat}
    (source target : RegisterBasis width) :
    List.zipWith (fun sourceBit targetBit => sourceBit != targetBit)
        (List.ofFn source) (List.ofFn target) =
      List.ofFn (fun wire => source wire != target wire) := by
  induction width with
  | zero => rfl
  | succ width inductionHypothesis =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [List.zipWith_cons_cons]
      congr 1
      exact inductionHypothesis (source ∘ Fin.succ) (target ∘ Fin.succ)

theorem analyticRegisterBits_qOracleXorRegister {width : Nat}
    (source target : RegisterBasis width) :
    analyticRegisterBits (qOracleXorRegister source target) =
      analyticXorBits (analyticRegisterBits source)
        (analyticRegisterBits target) := by
  rw [analyticRegisterBits_eq_ofFn, analyticRegisterBits_eq_ofFn,
    analyticRegisterBits_eq_ofFn]
  exact (qOracleZipWithXor_ofFn source target).symm

private theorem analyticConstantBitsAux_eq_ofFn
    (constant start width : Nat) :
    analyticConstantBitsAux constant start width =
      List.ofFn (fun bit : Fin width =>
        constant.testBit (start + bit.val)) := by
  induction width generalizing start with
  | zero => rfl
  | succ width inductionHypothesis =>
      rw [analyticConstantBitsAux, List.ofFn_succ]
      congr 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (start + 1)

theorem analyticRegisterBits_qOracleSelectorRegister
    {p : QParameters} (selector : QSelector p) :
    analyticRegisterBits (qOracleSelectorRegister selector) =
      analyticConstantBits selector.val p.selectorWidth := by
  rw [analyticRegisterBits_eq_ofFn, analyticConstantBits,
    analyticConstantBitsAux_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext bit
  simp [qOracleSelectorRegister]

@[simp] theorem analyticRegisterBits_length {width : Nat}
    (basis : RegisterBasis width) :
    (analyticRegisterBits basis).length = width := by
  simp [analyticRegisterBits]

/-- The list-valued constant XOR is the pointwise XOR of the equally wide
little-endian constant-bit list. -/
theorem analyticXorConstant_eq_analyticXorBits
    (constant : Nat) (bits : List Bool) :
    analyticXorConstant constant bits =
      analyticXorBits (analyticConstantBits constant bits.length) bits := by
  have auxiliary : ∀ (start : Nat) (input : List Bool),
      analyticXorConstantAux constant start input =
        analyticXorBits
          (analyticConstantBitsAux constant start input.length) input := by
    intro start input
    induction input generalizing start with
    | nil => rfl
    | cons bit tail inductionHypothesis =>
        simp [analyticXorConstantAux, analyticConstantBitsAux,
          analyticXorBits, inductionHypothesis]
  simpa [analyticXorConstant, analyticConstantBits] using auxiliary 0 bits

/-- Finite clean basis exposed by Q3.  Unlike the compatibility
`ColumnOracleObservation`, all accumulator widths are part of the type. -/
@[ext] structure Q3ColumnOracleCleanBasis (p : QParameters) where
  configuration : QConfiguration p
  selector : QSelector p
  rowOutput : RegisterBasis p.systemWidth
  selectorOutput : RegisterBasis p.selectorWidth
  negative : Bool
  active : Bool
  deriving DecidableEq

private abbrev Q3ColumnOracleCleanBasisProduct (p : QParameters) :=
  (QConfiguration p × QSelector p) ×
    ((RegisterBasis p.systemWidth × RegisterBasis p.selectorWidth) ×
      (Bool × Bool))

private def q3ColumnOracleCleanBasisEquiv (p : QParameters) :
    Q3ColumnOracleCleanBasis p ≃ Q3ColumnOracleCleanBasisProduct p where
  toFun input :=
    ((input.configuration, input.selector),
      ((input.rowOutput, input.selectorOutput), (input.negative, input.active)))
  invFun input :=
    { configuration := input.1.1
      selector := input.1.2
      rowOutput := input.2.1.1
      selectorOutput := input.2.1.2
      negative := input.2.2.1
      active := input.2.2.2 }
  left_inv input := by cases input; rfl
  right_inv input := by
    rcases input with ⟨⟨configuration, selector⟩,
      ⟨⟨rowOutput, selectorOutput⟩, ⟨negative, active⟩⟩⟩
    rfl

noncomputable instance q3ColumnOracleCleanBasisFintype (p : QParameters) :
    Fintype (Q3ColumnOracleCleanBasis p) :=
  Fintype.ofEquiv (Q3ColumnOracleCleanBasisProduct p)
    (q3ColumnOracleCleanBasisEquiv p).symm

/-- Fixed-width extensional Q3 action.  It is a mathematical XOR oracle:
configuration and selector are controls, while the four output registers are
accumulators. -/
def q3ColumnOracleFiniteCleanAction {p : QParameters}
    (input : Q3ColumnOracleCleanBasis p) : Q3ColumnOracleCleanBasis p :=
  match q3ColumnSemanticReference input.configuration input.selector with
  | none => input
  | some reference =>
      { input with
        rowOutput := qOracleXorRegister
          (delimiterEncoding reference.output) input.rowOutput
        selectorOutput := qOracleXorRegister
          (qOracleSelectorRegister reference.rowSelector) input.selectorOutput
        negative := reference.negative != input.negative
        active := !input.active }

/-- Compatibility projection from the finite mathematical basis to the older
list-valued observation interface used by the physical layout proof. -/
def Q3ColumnOracleCleanBasis.toObservation {p : QParameters}
    (input : Q3ColumnOracleCleanBasis p) : ColumnOracleObservation :=
  { rowOutput := analyticRegisterBits input.rowOutput
    selectorOutput := analyticRegisterBits input.selectorOutput
    negative := input.negative
    active := input.active }

/-- The finite clean action and the established list-valued semantic action
have exactly the same observable meaning. -/
theorem q3ColumnOracleFiniteCleanAction_toObservation {p : QParameters}
    (input : Q3ColumnOracleCleanBasis p) :
    (q3ColumnOracleFiniteCleanAction input).toObservation =
      q3ColumnSemanticAccumulatorAction input.configuration input.selector
        input.toObservation := by
  unfold q3ColumnOracleFiniteCleanAction q3ColumnSemanticAccumulatorAction
  split
  · rfl
  · simp only [Q3ColumnOracleCleanBasis.toObservation, applyColumnReference]
    apply ColumnOracleObservation.ext
    · exact analyticRegisterBits_qOracleXorRegister _ _
    · change
        analyticRegisterBits (qOracleXorRegister _ input.selectorOutput) =
          analyticXorConstant _ (analyticRegisterBits input.selectorOutput)
      rw [analyticRegisterBits_qOracleXorRegister,
        analyticRegisterBits_qOracleSelectorRegister]
      simpa using
        (analyticXorConstant_eq_analyticXorBits
          _
          (analyticRegisterBits input.selectorOutput)).symm
    · rfl
    · rfl

/-- The finite Q3 clean action is its own inverse. -/
theorem q3ColumnOracleFiniteCleanAction_involutive {p : QParameters} :
    Function.Involutive (q3ColumnOracleFiniteCleanAction (p := p)) := by
  intro input
  rcases input with
    ⟨configuration, selector, rowOutput, selectorOutput, negative, active⟩
  cases referenceEquation : q3ColumnSemanticReference configuration selector with
  | none => simp [q3ColumnOracleFiniteCleanAction, referenceEquation]
  | some reference =>
      simp only [q3ColumnOracleFiniteCleanAction, referenceEquation]
      apply Q3ColumnOracleCleanBasis.ext
      · rfl
      · rfl
      · funext wire
        simp [qOracleXorRegister]
      · funext wire
        simp [qOracleXorRegister]
      · simp
      · simp

/-- Q3 clean semantics as a finite basis permutation. -/
def q3ColumnOracleFiniteCleanPermutation (p : QParameters) :
    Equiv.Perm (Q3ColumnOracleCleanBasis p) where
  toFun := q3ColumnOracleFiniteCleanAction
  invFun := q3ColumnOracleFiniteCleanAction
  left_inv := q3ColumnOracleFiniteCleanAction_involutive
  right_inv := q3ColumnOracleFiniteCleanAction_involutive

/-- Linear extension of the independently stated finite Q3 clean action. -/
def q3ColumnOracleFiniteCleanOperator (p : QParameters) :
    Operator (Q3ColumnOracleCleanBasis p) :=
  deterministicOperator (q3ColumnOracleFiniteCleanPermutation p)

/-- Exterior normal form of the Q3 clean operator on computational basis
kets. -/
theorem q3ColumnOracleFiniteCleanOperator_apply_basisKet
    (p : QParameters) (input : Q3ColumnOracleCleanBasis p) :
    applyOperator (q3ColumnOracleFiniteCleanOperator p) (basisKet input) =
      basisKet (q3ColumnOracleFiniteCleanAction input) := by
  rw [q3ColumnOracleFiniteCleanOperator,
    applyOperator_deterministicOperator_basisKet]
  rfl

/-- Human-readable input record for the column-oracle semantic action. -/
structure ColumnOracleUnderstandingInput (p : QParameters) where
  configuration : QConfiguration p
  selector : QSelector p
  accumulator : ColumnOracleObservation
  deriving DecidableEq

/--
Q3 clean action.  `columnReference` decides inactive, diagonal, and event
branches; a successful result is XORed into the four external accumulators.
-/
def q3ColumnOracleCleanAction {p : QParameters}
    (input : ColumnOracleUnderstandingInput p) :
    ColumnOracleUnderstandingInput p :=
  ⟨input.configuration, input.selector,
    q3ColumnSemanticAccumulatorAction input.configuration input.selector
      input.accumulator⟩

@[simp] theorem q3ColumnOracleCleanAction_configuration {p : QParameters}
    (input : ColumnOracleUnderstandingInput p) :
    (q3ColumnOracleCleanAction input).configuration = input.configuration := rfl

@[simp] theorem q3ColumnOracleCleanAction_selector {p : QParameters}
    (input : ColumnOracleUnderstandingInput p) :
    (q3ColumnOracleCleanAction input).selector = input.selector := rfl

@[simp] theorem q3ColumnOracleCleanAction_accumulator {p : QParameters}
    (input : ColumnOracleUnderstandingInput p) :
    (q3ColumnOracleCleanAction input).accumulator =
      q3ColumnSemanticAccumulatorAction input.configuration input.selector
        input.accumulator := rfl

/-- An inactive/padding/branch-mismatch column selector is the identity action. -/
theorem q3ColumnOracleCleanAction_eq_self_of_reference_none
    {p : QParameters} (input : ColumnOracleUnderstandingInput p)
    (inactive : columnReference input.configuration input.selector = none) :
    q3ColumnOracleCleanAction input = input := by
  cases input
  simp [q3ColumnOracleCleanAction, q3ColumnSemanticAccumulatorAction,
    q3ColumnSemanticReference, inactive]

/-- An accepted column reference has exactly the advertised external XOR action. -/
theorem q3ColumnOracleCleanAction_accumulator_of_reference_some
    {p : QParameters} (input : ColumnOracleUnderstandingInput p)
    (reference : ColumnReferenceResult p)
    (accepted :
      columnReference input.configuration input.selector = some reference) :
    (q3ColumnOracleCleanAction input).accumulator =
      applyColumnReference reference input.accumulator := by
  simp [q3ColumnOracleCleanAction, q3ColumnSemanticAccumulatorAction,
    q3ColumnSemanticReference, accepted]

/-- Independent full-dirty reversible extension used by the canonical Q circuit. -/
def q3ColumnOracleRecordedOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  OracleCanonicalTotalProgram.columnAnalyticOperator p

/-- Every accepted physical event produces the event output stored in the
human snapshot, including its canonical row selector.  The proof unfolds only
the pure reference function; it does not import the downstream finite-overlap
or circuit-correctness developments. -/
theorem q3ColumnSemanticReference_event_snapshot
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    q3ColumnSemanticReference input
        (qOracleEventUnderstandingSnapshot input source member direction).columnSelector =
      some ⟨(qOracleEventUnderstandingSnapshot input source member direction).outputConfiguration,
        (qOracleEventUnderstandingSnapshot input source member direction).rowSelector,
        false⟩ := by
  let selector := selectorForEvent input source member direction
  have selected : configurationSlot? input (selectorSlot selector) =
      some ⟨source, member⟩ := by
    simp [selector, selectorForEvent]
  have notDiagonal : ¬(selectorOffset selector).val < 2 := by
    simpa [selector, selectorForEvent] using
      eventOffset_not_diagonal direction
        (decide (moveSite source direction ∈ input.1.erase source))
  have branchCorrect :
      (decide (moveSite source (selectorDirection selector) ∈
        input.1.erase source) : Bool) = selectorRequestsCollision selector := by
    simp [selector, selectorForEvent]
  change columnReference input selector =
    some ⟨eventOutput input source direction,
      rowSelectorForEvent input source member direction, false⟩
  unfold columnReference
  rw [selected]
  simp only [notDiagonal, dite_false]
  rw [dif_pos branchCorrect]
  simp [selector, selectorForEvent, rowSelectorForEvent, eventOutput,
    eventCollision]

/-- Existential form retained as a small corollary for clients that do not need
the canonical selector value. -/
theorem q3ColumnSemanticReference_event_snapshot_accepted
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    ∃ rowSelector,
      q3ColumnSemanticReference input
          (qOracleEventUnderstandingSnapshot input source member direction).columnSelector =
        some ⟨(qOracleEventUnderstandingSnapshot input source member direction).outputConfiguration,
          rowSelector, false⟩ := by
  exact ⟨(qOracleEventUnderstandingSnapshot input source member direction).rowSelector,
    q3ColumnSemanticReference_event_snapshot input source member direction⟩

/-! ## Q7 row-oracle clean semantics -/

/-- Q7 semantic partial reference with a stable human-facing name. -/
def q7RowSemanticReference {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p) :
    Option (RowReferenceResult p) :=
  rowReference configuration selector

/-- Q7b reference restricted to the two diagonal offsets. -/
def q7RowDiagonalSemanticReference {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p) :
    Option (RowReferenceResult p) :=
  if (selectorOffset selector).val < 2 then
    q7RowSemanticReference configuration selector
  else none

/-- Q7c reference restricted to the four predecessor-event offsets. -/
def q7RowEventSemanticReference {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p) :
    Option (RowReferenceResult p) :=
  if (selectorOffset selector).val < 2 then none
  else q7RowSemanticReference configuration selector

/-- Q7 is the disjoint union of its diagonal and event semantic references. -/
theorem q7RowSemanticReference_eq_diagonal_or_event {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p) :
    q7RowSemanticReference configuration selector =
      match q7RowDiagonalSemanticReference configuration selector with
      | some result => some result
      | none => q7RowEventSemanticReference configuration selector := by
  by_cases diagonal : (selectorOffset selector).val < 2
  · cases referenceEquation : q7RowSemanticReference configuration selector <;>
      simp [q7RowDiagonalSemanticReference, q7RowEventSemanticReference,
        diagonal, referenceEquation]
  · simp [q7RowDiagonalSemanticReference,
      q7RowEventSemanticReference, diagonal]

theorem q7RowSemanticReference_eq_rowReference {p : QParameters} :
    q7RowSemanticReference (p := p) = rowReference := rfl

theorem q7RowSemanticReference_eq_none_of_missing
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (missing : configurationSlot? configuration (selectorSlot selector) = none) :
    q7RowSemanticReference configuration selector = none := by
  unfold q7RowSemanticReference rowReference
  rw [missing]

theorem q7RowSemanticReference_diagonal
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1) (copy : Fin 2) :
    let selector := selectorOfSlotOffset
      (slotOfMember configuration source member)
      ⟨copy.val, lt_trans copy.isLt (by decide)⟩
    q7RowSemanticReference configuration selector =
      some ⟨configuration, selector⟩ := by
  dsimp only
  simpa [q7RowSemanticReference] using
    (rowReference_diagonal configuration source member copy)

/-- Q7 external accumulator action defined from the semantic predecessor
reference, independently of any physical writer registers. -/
def q7RowSemanticAccumulatorAction {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p)
    (observation : RowOracleObservation) : RowOracleObservation :=
  match q7RowSemanticReference configuration selector with
  | none => observation
  | some reference => applyRowReference reference observation

/-- Q7 accumulator action displayed as the explicit Q7b/Q7c branch union. -/
def q7RowBranchSemanticAccumulatorAction {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p)
    (observation : RowOracleObservation) : RowOracleObservation :=
  match q7RowDiagonalSemanticReference configuration selector with
  | some reference => applyRowReference reference observation
  | none =>
      match q7RowEventSemanticReference configuration selector with
      | some reference => applyRowReference reference observation
      | none => observation

theorem q7RowSemanticAccumulatorAction_eq_branches {p : QParameters}
    (configuration : QConfiguration p) (selector : QSelector p)
    (observation : RowOracleObservation) :
    q7RowSemanticAccumulatorAction configuration selector observation =
      q7RowBranchSemanticAccumulatorAction
        configuration selector observation := by
  unfold q7RowSemanticAccumulatorAction q7RowBranchSemanticAccumulatorAction
  rw [q7RowSemanticReference_eq_diagonal_or_event]
  cases q7RowDiagonalSemanticReference configuration selector <;>
    cases q7RowEventSemanticReference configuration selector <;> rfl

theorem q7RowSemanticAccumulatorAction_eq_established {p : QParameters} :
    q7RowSemanticAccumulatorAction (p := p) = rowOracleAnalyticAction := rfl

/-! ### Finite clean computational basis for Q7 -/

/-- Finite clean basis exposed by Q7. -/
@[ext] structure Q7RowOracleCleanBasis (p : QParameters) where
  configuration : QConfiguration p
  selector : QSelector p
  columnKey : RegisterBasis p.systemWidth
  columnSelector : RegisterBasis p.selectorWidth
  keySignal : Bool
  deriving DecidableEq

private abbrev Q7RowOracleCleanBasisProduct (p : QParameters) :=
  (QConfiguration p × QSelector p) ×
    ((RegisterBasis p.systemWidth × RegisterBasis p.selectorWidth) × Bool)

private def q7RowOracleCleanBasisEquiv (p : QParameters) :
    Q7RowOracleCleanBasis p ≃ Q7RowOracleCleanBasisProduct p where
  toFun input :=
    ((input.configuration, input.selector),
      ((input.columnKey, input.columnSelector), input.keySignal))
  invFun input :=
    { configuration := input.1.1
      selector := input.1.2
      columnKey := input.2.1.1
      columnSelector := input.2.1.2
      keySignal := input.2.2 }
  left_inv input := by cases input; rfl
  right_inv input := by
    rcases input with ⟨⟨configuration, selector⟩,
      ⟨⟨columnKey, columnSelector⟩, keySignal⟩⟩
    rfl

noncomputable instance q7RowOracleCleanBasisFintype (p : QParameters) :
    Fintype (Q7RowOracleCleanBasis p) :=
  Fintype.ofEquiv (Q7RowOracleCleanBasisProduct p)
    (q7RowOracleCleanBasisEquiv p).symm

/-- Fixed-width extensional Q7 action. -/
def q7RowOracleFiniteCleanAction {p : QParameters}
    (input : Q7RowOracleCleanBasis p) : Q7RowOracleCleanBasis p :=
  match q7RowSemanticReference input.configuration input.selector with
  | none => input
  | some reference =>
      { input with
        columnKey := qOracleXorRegister
          (delimiterEncoding reference.input) input.columnKey
        columnSelector := qOracleXorRegister
          (qOracleSelectorRegister reference.columnSelector)
          input.columnSelector
        keySignal := !input.keySignal }

/-- Compatibility projection for the row-oracle clean basis. -/
def Q7RowOracleCleanBasis.toObservation {p : QParameters}
    (input : Q7RowOracleCleanBasis p) : RowOracleObservation :=
  { columnKey := analyticRegisterBits input.columnKey
    columnSelector := analyticRegisterBits input.columnSelector
    keySignal := input.keySignal }

/-- The fixed-width Q7 clean action agrees with the established observable
row action. -/
theorem q7RowOracleFiniteCleanAction_toObservation {p : QParameters}
    (input : Q7RowOracleCleanBasis p) :
    (q7RowOracleFiniteCleanAction input).toObservation =
      q7RowSemanticAccumulatorAction input.configuration input.selector
        input.toObservation := by
  unfold q7RowOracleFiniteCleanAction q7RowSemanticAccumulatorAction
  split
  · rfl
  · simp only [Q7RowOracleCleanBasis.toObservation, applyRowReference]
    apply RowOracleObservation.ext
    · exact analyticRegisterBits_qOracleXorRegister _ _
    · change
        analyticRegisterBits (qOracleXorRegister _ input.columnSelector) =
          analyticXorConstant _ (analyticRegisterBits input.columnSelector)
      rw [analyticRegisterBits_qOracleXorRegister,
        analyticRegisterBits_qOracleSelectorRegister]
      simpa using
        (analyticXorConstant_eq_analyticXorBits
          _
          (analyticRegisterBits input.columnSelector)).symm
    · rfl

/-- The finite Q7 clean action is its own inverse. -/
theorem q7RowOracleFiniteCleanAction_involutive {p : QParameters} :
    Function.Involutive (q7RowOracleFiniteCleanAction (p := p)) := by
  intro input
  rcases input with
    ⟨configuration, selector, columnKey, columnSelector, keySignal⟩
  cases referenceEquation : q7RowSemanticReference configuration selector with
  | none => simp [q7RowOracleFiniteCleanAction, referenceEquation]
  | some reference =>
      simp only [q7RowOracleFiniteCleanAction, referenceEquation]
      apply Q7RowOracleCleanBasis.ext
      · rfl
      · rfl
      · funext wire
        simp [qOracleXorRegister]
      · funext wire
        simp [qOracleXorRegister]
      · simp

/-- Q7 clean semantics as a finite basis permutation. -/
def q7RowOracleFiniteCleanPermutation (p : QParameters) :
    Equiv.Perm (Q7RowOracleCleanBasis p) where
  toFun := q7RowOracleFiniteCleanAction
  invFun := q7RowOracleFiniteCleanAction
  left_inv := q7RowOracleFiniteCleanAction_involutive
  right_inv := q7RowOracleFiniteCleanAction_involutive

/-- Linear extension of the independently stated finite Q7 clean action. -/
def q7RowOracleFiniteCleanOperator (p : QParameters) :
    Operator (Q7RowOracleCleanBasis p) :=
  deterministicOperator (q7RowOracleFiniteCleanPermutation p)

/-- Exterior normal form of the Q7 clean operator on computational basis
kets. -/
theorem q7RowOracleFiniteCleanOperator_apply_basisKet
    (p : QParameters) (input : Q7RowOracleCleanBasis p) :
    applyOperator (q7RowOracleFiniteCleanOperator p) (basisKet input) =
      basisKet (q7RowOracleFiniteCleanAction input) := by
  rw [q7RowOracleFiniteCleanOperator,
    applyOperator_deterministicOperator_basisKet]
  rfl

/-- Human-readable input record for the row-oracle semantic action. -/
structure RowOracleUnderstandingInput (p : QParameters) where
  configuration : QConfiguration p
  selector : QSelector p
  accumulator : RowOracleObservation
  deriving DecidableEq

/--
Q7 clean action.  `rowReference` reconstructs a predecessor for an active
branch and XORs its configuration, selector, and success signal into the
external accumulators.
-/
def q7RowOracleCleanAction {p : QParameters}
    (input : RowOracleUnderstandingInput p) : RowOracleUnderstandingInput p :=
  ⟨input.configuration, input.selector,
    q7RowSemanticAccumulatorAction input.configuration input.selector
      input.accumulator⟩

@[simp] theorem q7RowOracleCleanAction_configuration {p : QParameters}
    (input : RowOracleUnderstandingInput p) :
    (q7RowOracleCleanAction input).configuration = input.configuration := rfl

@[simp] theorem q7RowOracleCleanAction_selector {p : QParameters}
    (input : RowOracleUnderstandingInput p) :
    (q7RowOracleCleanAction input).selector = input.selector := rfl

@[simp] theorem q7RowOracleCleanAction_accumulator {p : QParameters}
    (input : RowOracleUnderstandingInput p) :
    (q7RowOracleCleanAction input).accumulator =
      q7RowSemanticAccumulatorAction input.configuration input.selector
        input.accumulator := rfl

/-- An inactive/padding row selector is the identity action. -/
theorem q7RowOracleCleanAction_eq_self_of_reference_none
    {p : QParameters} (input : RowOracleUnderstandingInput p)
    (inactive : rowReference input.configuration input.selector = none) :
    q7RowOracleCleanAction input = input := by
  cases input
  simp [q7RowOracleCleanAction, q7RowSemanticAccumulatorAction,
    q7RowSemanticReference, inactive]

/-- An accepted row reference has exactly the advertised external XOR action. -/
theorem q7RowOracleCleanAction_accumulator_of_reference_some
    {p : QParameters} (input : RowOracleUnderstandingInput p)
    (reference : RowReferenceResult p)
    (accepted : rowReference input.configuration input.selector = some reference) :
    (q7RowOracleCleanAction input).accumulator =
      applyRowReference reference input.accumulator := by
  simp [q7RowOracleCleanAction, q7RowSemanticAccumulatorAction,
    q7RowSemanticReference, accepted]

/-- Independent full-dirty reversible extension used by the canonical Q circuit. -/
def q7RowOracleRecordedOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  OracleCanonicalTotalProgram.rowAnalyticOperator p

/-- Q7 exactly reconstructs the source-side configuration and canonical column
selector stored in an accepted event snapshot. -/
theorem q7RowSemanticReference_event_snapshot_inverse
    {p : QParameters} (input : QConfiguration p) (source : QSite p)
    (member : source ∈ input.1) (direction : QDirection) :
    q7RowSemanticReference
        (qOracleEventUnderstandingSnapshot input source member direction).outputConfiguration
        (qOracleEventUnderstandingSnapshot input source member direction).rowSelector =
      some ⟨input,
        (qOracleEventUnderstandingSnapshot input source member direction).columnSelector⟩ := by
  simpa [q7RowSemanticReference, qOracleEventUnderstandingSnapshot] using
    (rowReference_rowSelectorForEvent input source member direction)

/-! ## Dirty reversible extensions as linearized basis permutations -/

theorem q3ColumnOracleRecordedOperator_eq_deterministicReference
    (p : QParameters) :
    q3ColumnOracleRecordedOperator p =
      deterministicOperator (OracleCanonicalTotalProgram.columnReference p) := by
  simpa [q3ColumnOracleRecordedOperator,
    OracleCanonicalTotalProgram.columnAnalyticOperator,
    TotalOracleStageChildren.fullAnalyticOperator,
    OracleCanonicalTotalProgram.columnReference,
    TotalOracleStageChildren.fullReference] using
    (TotalReversibleStage.analyticOperator_eq_deterministicReference
      ((OracleCanonicalTotalProgram.columnChildren p).fullStage p))

theorem q7RowOracleRecordedOperator_eq_deterministicReference
    (p : QParameters) :
    q7RowOracleRecordedOperator p =
      deterministicOperator (OracleCanonicalTotalProgram.rowReference p) := by
  simpa [q7RowOracleRecordedOperator,
    OracleCanonicalTotalProgram.rowAnalyticOperator,
    TotalOracleStageChildren.fullAnalyticOperator,
    OracleCanonicalTotalProgram.rowReference,
    TotalOracleStageChildren.fullReference] using
    (TotalReversibleStage.analyticOperator_eq_deterministicReference
      ((OracleCanonicalTotalProgram.rowChildren p).fullStage p))

/-- Dirty Q3 maps every computational basis ket to the ket selected by the
canonical all-wire column permutation. -/
theorem q3ColumnOracleRecordedOperator_apply_basisKet
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    applyOperator (q3ColumnOracleRecordedOperator p) (basisKet input) =
      basisKet (OracleCanonicalTotalProgram.columnReference p input) := by
  rw [q3ColumnOracleRecordedOperator_eq_deterministicReference]
  exact applyOperator_deterministicOperator_basisKet _ _

/-- Dirty Q7 maps every computational basis ket to the ket selected by the
canonical all-wire row permutation. -/
theorem q7RowOracleRecordedOperator_apply_basisKet
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    applyOperator (q7RowOracleRecordedOperator p) (basisKet input) =
      basisKet (OracleCanonicalTotalProgram.rowReference p input) := by
  rw [q7RowOracleRecordedOperator_eq_deterministicReference]
  exact applyOperator_deterministicOperator_basisKet _ _

/-- Human review record for Q3.  The clean semantic reference/action and the
dirty all-wire permutation/operator are deliberately separate fields. -/
structure Q3ColumnOracleUnderstandingSpecification (p : QParameters) where
  persistentRecord :
    QConfiguration p → QSelector p → QOraclePersistentSemanticRecord p
  diagonalReference :
    QConfiguration p → QSelector p → Option (ColumnReferenceResult p)
  eventReference :
    QConfiguration p → QSelector p → Option (ColumnReferenceResult p)
  semanticReference :
    QConfiguration p → QSelector p → Option (ColumnReferenceResult p)
  cleanAccumulatorAction :
    QConfiguration p → QSelector p → ColumnOracleObservation →
      ColumnOracleObservation
  branchAccumulatorAction :
    QConfiguration p → QSelector p → ColumnOracleObservation →
      ColumnOracleObservation
  dirtyBasisAction : Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth)
  dirtyOperator : Operator (JointBasis p.ancillaWidth p.systemWidth)
  finiteCleanBasisAction : Q3ColumnOracleCleanBasis p →
    Q3ColumnOracleCleanBasis p
  finiteCleanOperator : Operator (Q3ColumnOracleCleanBasis p)
  semanticReference_eq_diagonal_or_event :
    ∀ configuration selector,
      semanticReference configuration selector =
        match diagonalReference configuration selector with
        | some result => some result
        | none => eventReference configuration selector
  semanticReference_eq_established : semanticReference = columnReference
  cleanAccumulatorAction_eq_branches :
    ∀ configuration selector observation,
      cleanAccumulatorAction configuration selector observation =
        branchAccumulatorAction configuration selector observation
  cleanAccumulatorAction_eq_established :
    cleanAccumulatorAction = columnOracleAnalyticAction
  dirtyOperator_eq_linearExtension :
    dirtyOperator = deterministicOperator dirtyBasisAction
  finiteCleanOperator_eq_linearExtension :
    finiteCleanOperator = deterministicOperator finiteCleanBasisAction

def q3ColumnOracleUnderstandingSpecification (p : QParameters) :
    Q3ColumnOracleUnderstandingSpecification p where
  persistentRecord := qOraclePersistentSemanticRecord
  diagonalReference := q3ColumnDiagonalSemanticReference
  eventReference := q3ColumnEventSemanticReference
  semanticReference := q3ColumnSemanticReference
  cleanAccumulatorAction := q3ColumnSemanticAccumulatorAction
  branchAccumulatorAction := q3ColumnBranchSemanticAccumulatorAction
  dirtyBasisAction := OracleCanonicalTotalProgram.columnReference p
  dirtyOperator := q3ColumnOracleRecordedOperator p
  finiteCleanBasisAction := q3ColumnOracleFiniteCleanAction
  finiteCleanOperator := q3ColumnOracleFiniteCleanOperator p
  semanticReference_eq_diagonal_or_event :=
    q3ColumnSemanticReference_eq_diagonal_or_event
  semanticReference_eq_established :=
    q3ColumnSemanticReference_eq_columnReference
  cleanAccumulatorAction_eq_branches :=
    q3ColumnSemanticAccumulatorAction_eq_branches
  cleanAccumulatorAction_eq_established :=
    q3ColumnSemanticAccumulatorAction_eq_established
  dirtyOperator_eq_linearExtension :=
    q3ColumnOracleRecordedOperator_eq_deterministicReference p
  finiteCleanOperator_eq_linearExtension := by
    rfl

/-- Human review record for Q7, with the same clean/dirty separation as Q3. -/
structure Q7RowOracleUnderstandingSpecification (p : QParameters) where
  persistentRecord :
    QConfiguration p → QSelector p → QOraclePersistentSemanticRecord p
  diagonalReference :
    QConfiguration p → QSelector p → Option (RowReferenceResult p)
  eventReference :
    QConfiguration p → QSelector p → Option (RowReferenceResult p)
  semanticReference :
    QConfiguration p → QSelector p → Option (RowReferenceResult p)
  cleanAccumulatorAction :
    QConfiguration p → QSelector p → RowOracleObservation → RowOracleObservation
  branchAccumulatorAction :
    QConfiguration p → QSelector p → RowOracleObservation → RowOracleObservation
  dirtyBasisAction : Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth)
  dirtyOperator : Operator (JointBasis p.ancillaWidth p.systemWidth)
  finiteCleanBasisAction : Q7RowOracleCleanBasis p → Q7RowOracleCleanBasis p
  finiteCleanOperator : Operator (Q7RowOracleCleanBasis p)
  semanticReference_eq_diagonal_or_event :
    ∀ configuration selector,
      semanticReference configuration selector =
        match diagonalReference configuration selector with
        | some result => some result
        | none => eventReference configuration selector
  semanticReference_eq_established : semanticReference = rowReference
  cleanAccumulatorAction_eq_branches :
    ∀ configuration selector observation,
      cleanAccumulatorAction configuration selector observation =
        branchAccumulatorAction configuration selector observation
  cleanAccumulatorAction_eq_established :
    cleanAccumulatorAction = rowOracleAnalyticAction
  dirtyOperator_eq_linearExtension :
    dirtyOperator = deterministicOperator dirtyBasisAction
  finiteCleanOperator_eq_linearExtension :
    finiteCleanOperator = deterministicOperator finiteCleanBasisAction

def q7RowOracleUnderstandingSpecification (p : QParameters) :
    Q7RowOracleUnderstandingSpecification p where
  persistentRecord := qOraclePersistentSemanticRecord
  diagonalReference := q7RowDiagonalSemanticReference
  eventReference := q7RowEventSemanticReference
  semanticReference := q7RowSemanticReference
  cleanAccumulatorAction := q7RowSemanticAccumulatorAction
  branchAccumulatorAction := q7RowBranchSemanticAccumulatorAction
  dirtyBasisAction := OracleCanonicalTotalProgram.rowReference p
  dirtyOperator := q7RowOracleRecordedOperator p
  finiteCleanBasisAction := q7RowOracleFiniteCleanAction
  finiteCleanOperator := q7RowOracleFiniteCleanOperator p
  semanticReference_eq_diagonal_or_event :=
    q7RowSemanticReference_eq_diagonal_or_event
  semanticReference_eq_established := q7RowSemanticReference_eq_rowReference
  cleanAccumulatorAction_eq_branches :=
    q7RowSemanticAccumulatorAction_eq_branches
  cleanAccumulatorAction_eq_established :=
    q7RowSemanticAccumulatorAction_eq_established
  dirtyOperator_eq_linearExtension :=
    q7RowOracleRecordedOperator_eq_deterministicReference p
  finiteCleanOperator_eq_linearExtension := by
    rfl

/-! ## Q10 nine-stage full-space operator -/

/--
The nine public operators in source execution order.  Column and row oracle
internals remain behind their Q3 and Q7 specification boundaries.
-/
def q10ProbabilityGeneratorSourceOperators (p : QParameters) :
    List (Operator (JointBasis p.ancillaWidth p.systemWidth)) :=
  [sharedCoreColumnUniformPreparationFullAnalyticOperator p,
   xorSystemIntoColumnKeyFullAnalyticOperator p,
   q3ColumnOracleRecordedOperator p,
   amplitudeSignFullAnalyticOperator p,
   outputAlignmentFullAnalyticOperator p,
   Matrix.conjTranspose (q3ColumnOracleRecordedOperator p),
   q7RowOracleRecordedOperator p,
   amplitudeSignalFlipFullAnalyticOperator p,
   Matrix.conjTranspose (sharedCoreRowUniformPreparationFullAnalyticOperator p)]

@[simp] theorem q10ProbabilityGeneratorSourceOperators_length
    (p : QParameters) :
    (q10ProbabilityGeneratorSourceOperators p).length = 9 := rfl

/-- Pure enumeration of an ancilla register slice.  This is intentionally
defined here instead of importing the implementation-side layout API. -/
def q10RegisterSliceWires {ancillaWidth systemWidth width : Nat}
    (slice : RegisterSlice ancillaWidth width) :
    List (Wire ancillaWidth systemWidth) :=
  (List.finRange width).map (RegisterSlice.ancillaWire slice)

/-- Read a typed register directly from a joint computational basis. -/
def q10ProjectRegisterBasis {p : QParameters} {width : Nat}
    (wires : Fin width → Wire p.ancillaWidth p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : RegisterBasis width :=
  fun index => basis (wires index)

/-- The all-zero basis word, stated without an implementation-side helper. -/
def q10ZeroRegisterBasis (width : Nat) : RegisterBasis width :=
  fun _ => false

/-- Pure typed wire accessors for the Q10 signal registers. -/
def q10ColumnSelectorWire (p : QParameters) :
    Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).columnSelector.ancillaWire

def q10RowSelectorWire (p : QParameters) :
    Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).rowSelector.ancillaWire

def q10SelectorOutputWire (p : QParameters) :
    Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).selectorOutput.ancillaWire

def q10ActiveWire (p : QParameters) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).active.ancillaWire 0

def q10AmplitudeSignalWire (p : QParameters) :
    Wire p.ancillaWidth p.systemWidth :=
  (QLayout.canonical p).amplitudeSignal.ancillaWire 0

/-- The internal oracle-work suffix of Q10 is zero.  This is the clean
input/output boundary shared by Q3 and Q7.  It deliberately excludes the
signal prefix, because Q10 writes amplitude and alignment information there. -/
def q10GeneratorWorkCleanPredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ wire ∈ q10RegisterSliceWires (systemWidth := p.systemWidth)
      (QLayout.canonical p).oracleWork, basis wire = false

/-- The exact prefix of Q's AND-work register borrowed by the shared
arbitrary-width uniform-preparation compiler. -/
def q10UniformScratchPrefixWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.selectorWidth).map
    (analyticSharedUniformScratchWire p)

/-- Every shared uniform scratch wire lies in Q10's internal-work suffix. -/
theorem q10UniformScratchPrefixWires_subset_generatorWork
    (p : QParameters) :
    ∀ wire ∈ q10UniformScratchPrefixWires p,
      wire ∈ q10RegisterSliceWires (systemWidth := p.systemWidth)
        (QLayout.canonical p).oracleWork := by
  intro wire member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  apply List.mem_map.mpr
  refine ⟨(OracleWorkLayout.canonical p).andWork.index
      ⟨index.val, lt_of_lt_of_le index.isLt
        (analyticSelectorWidth_le_andWorkWidth p)⟩,
    List.mem_finRange _, ?_⟩
  unfold analyticSharedUniformScratchWire QLayout.oracleSlice
    RegisterSlice.ancillaWire
  apply congrArg (fun globalIndex : Fin p.ancillaWidth =>
    (Wire.ancilla globalIndex : Wire p.ancillaWidth p.systemWidth))
  apply Fin.ext
  simp only [RegisterSlice.index, RegisterSlice.compose, Nat.add_assoc]

/-- Zero condition on precisely the scratch prefix borrowed by Q1/Q9. -/
def q10UniformScratchCleanPredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ wire ∈ q10UniformScratchPrefixWires p, basis wire = false

/-- Zero condition on the rest of Q10 internal work, excluding the shared
uniform scratch prefix. -/
def q10NonUniformWorkCleanPredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ wire ∈ q10RegisterSliceWires (systemWidth := p.systemWidth)
      (QLayout.canonical p).oracleWork,
    wire ∉ q10UniformScratchPrefixWires p → basis wire = false

/-- Human-facing split of the Q10 internal-work invariant into the scratch
borrowed by uniform preparation and the untouched remainder. -/
theorem q10GeneratorWorkCleanPredicate_iff_uniformScratch_and_remainder
    (p : QParameters) (basis : JointBasis p.ancillaWidth p.systemWidth) :
    q10GeneratorWorkCleanPredicate p basis ↔
      q10UniformScratchCleanPredicate p basis ∧
        q10NonUniformWorkCleanPredicate p basis := by
  constructor
  · intro clean
    constructor
    · intro wire member
      exact clean wire
        (q10UniformScratchPrefixWires_subset_generatorWork p wire member)
    · intro wire member _
      exact clean wire member
  · rintro ⟨scratch, remainder⟩ wire member
    by_cases inScratch : wire ∈ q10UniformScratchPrefixWires p
    · exact scratch wire inScratch
    · exact remainder wire member inScratch

/-- The physical column-selector word is one of the `6*K` active selectors.
This property is independent of the oracle circuit and excludes binary
padding values in the selector register. -/
def q10ColumnSelectorActivePredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  qOracleSelectorValue p.selectorWidth
    (q10ProjectRegisterBasis (q10ColumnSelectorWire p) basis) < p.selectorCount

/-- Row-selector counterpart of `q10ColumnSelectorActivePredicate`. -/
def q10RowSelectorActivePredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  qOracleSelectorValue p.selectorWidth
    (q10ProjectRegisterBasis (q10RowSelectorWire p) basis) < p.selectorCount

/-- Work-clean Q3 sector with an active, non-padding column selector. -/
def q10ColumnOracleCleanPredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  q10GeneratorWorkCleanPredicate p basis ∧
    q10ColumnSelectorActivePredicate p basis

/-- Work-clean Q7 sector with an active, non-padding row selector. -/
def q10RowOracleCleanPredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  q10GeneratorWorkCleanPredicate p basis ∧
    q10RowSelectorActivePredicate p basis

/-- The alignment boundary simultaneously carries an active column selector
and an active row selector, while all borrowed oracle work has been restored.
The column condition is consumed by the reverse Q3 edge and the row condition
is consumed by Q7. -/
def q10AlignedOracleCleanPredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  q10ColumnOracleCleanPredicate p basis ∧
    q10RowSelectorActivePredicate p basis

/-! ### Source-reachable Q3--Q5 alignment predicates

These predicates make the human-visible reason for Q5 selector validity
explicit.  They mention only mathematical basis observations.  In particular,
they do not unfold the column-oracle circuit or use `runBasis`.
-/

/-- A selector register is the all-zero little-endian word. -/
def q10SelectorZeroPredicate (p : QParameters)
    (selectorWire : Fin p.selectorWidth →
      Wire p.ancillaWidth p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ index, basis (selectorWire index) = false

/-- The abstract all-zero selector word has numerical value zero, at every
width.  Keeping the induction independent of `QParameters` avoids a
dependent elimination through `p.selectorWidth` in the Q10 specialization
below. -/
theorem qOracleSelectorValue_zeroRegisterBasis : ∀ width : Nat,
    qOracleSelectorValue width (q10ZeroRegisterBasis width) = 0
  | 0 => rfl
  | width + 1 => by
      rw [qOracleSelectorValue]
      simp only [q10ZeroRegisterBasis]
      rw [if_neg (by decide), Nat.zero_add]
      exact qOracleSelectorValue_zeroRegisterBasis width

/-- The little-endian value of an all-zero selector observation is zero. -/
theorem q10SelectorValue_eq_zero_of_zeroPredicate
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth →
      Wire p.ancillaWidth p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (zero : q10SelectorZeroPredicate p selectorWire basis) :
    qOracleSelectorValue p.selectorWidth
        (q10ProjectRegisterBasis selectorWire basis) = 0 := by
  have basisEq : q10ProjectRegisterBasis selectorWire basis =
      q10ZeroRegisterBasis p.selectorWidth := by
    funext index
    exact zero index
  rw [basisEq]
  exact qOracleSelectorValue_zeroRegisterBasis p.selectorWidth

/-- The Q3 selector-output accumulator encodes an active, non-padding
selector. -/
def q10SelectorOutputActivePredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  qOracleSelectorValue p.selectorWidth
    (q10ProjectRegisterBasis (q10SelectorOutputWire p) basis) < p.selectorCount

/-- Source-reachable Q3 input boundary.  Besides the ordinary clean active
column selector, every accumulator that Q3/Q4/Q5 will consume is initially
zero. -/
structure Q10BeforeColumnOracleReady (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  columnClean : q10ColumnOracleCleanPredicate p basis
  rowSelectorZero : q10SelectorZeroPredicate p (q10RowSelectorWire p) basis
  selectorOutputZero : q10SelectorZeroPredicate p (q10SelectorOutputWire p) basis
  activeZero : basis (q10ActiveWire p) = false
  amplitudeZero : basis (q10AmplitudeSignalWire p) = false

/-- Q3 output boundary.  A rejected branch keeps `active = false`; an accepted
branch writes a typed row selector before setting `active = true`. -/
structure Q10AfterColumnOracleReady (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  columnClean : q10ColumnOracleCleanPredicate p basis
  rowSelectorZero : q10SelectorZeroPredicate p (q10RowSelectorWire p) basis
  amplitudeZero : basis (q10AmplitudeSignalWire p) = false
  selectorOutputActiveOfActive : basis (q10ActiveWire p) = true →
    q10SelectorOutputActivePredicate p basis

/-- Q4 copies the Q3 active bit into the previously-zero amplitude signal.
This is exactly the input contract consumed by Q5 alignment. -/
structure Q10OutputAlignmentReady (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop where
  columnClean : q10ColumnOracleCleanPredicate p basis
  rowSelectorZero : q10SelectorZeroPredicate p (q10RowSelectorWire p) basis
  selectorOutputActiveOfAmplitude : basis (q10AmplitudeSignalWire p) = true →
    q10SelectorOutputActivePredicate p basis

/-- The Q11 success-sector input additionally initializes the complete signal
prefix to zero.  Unlike `q10GeneratorWorkCleanPredicate`, this is an input
observation condition and is not claimed to be restored by Q10. -/
def q10GeneratorSignalZeroInputPredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  ∀ wire ∈ q10RegisterSliceWires (systemWidth := p.systemWidth)
      (QLayout.canonicalGeneratorSourceSlices p).signal, basis wire = false

/-- Human-facing decomposition of the Q11 all-zero ancilla input boundary
into the signal input sector and the restored internal-work sector. -/
def q11AllZeroAncillaInputPredicate (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) : Prop :=
  q10GeneratorSignalZeroInputPredicate p basis ∧
    q10GeneratorWorkCleanPredicate p basis

@[simp] theorem q11AllZeroAncillaInputPredicate_zeroAncillaJointBasis
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    q11AllZeroAncillaInputPredicate p (zeroAncillaJointBasis p system) := by
  constructor <;> intro wire member
  · rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl
  · rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rfl

/-- The Q11 input predicate really covers every ancilla coordinate: the
signal prefix and internal-work suffix are contiguous and exhaust the
canonical Q ancilla register. -/
theorem q11AllZeroAncillaInputPredicate_ancilla_zero
    {p : QParameters} {basis : JointBasis p.ancillaWidth p.systemWidth}
    (inputZero : q11AllZeroAncillaInputPredicate p basis)
    (index : Fin p.ancillaWidth) :
    basis (.ancilla index) = false := by
  by_cases inSignal : index.val < p.generatorSignalWidth
  · apply inputZero.1
    unfold q10RegisterSliceWires
    apply List.mem_map.mpr
    refine ⟨⟨index.val, inSignal⟩, List.mem_finRange _, ?_⟩
    unfold RegisterSlice.ancillaWire
    apply congrArg (fun globalIndex : Fin p.ancillaWidth =>
      (Wire.ancilla globalIndex : Wire p.ancillaWidth p.systemWidth))
    apply Fin.ext
    change (QLayout.canonicalGeneratorSourceSlices p).signal.start + index.val =
      index.val
    rw [(QLayout.canonicalGeneratorSourceSlices p).signal_start]
    exact Nat.zero_add index.val
  · have signalLe : p.generatorSignalWidth ≤ index.val :=
      Nat.le_of_not_gt inSignal
    let localIndex : Fin p.generatorWorkWidth :=
      ⟨index.val - p.generatorSignalWidth, by
        have indexBound := index.isLt
        have partition :=
          p.generatorSignalWidth_add_generatorWorkWidth_eq_ancillaWidth
        omega⟩
    apply inputZero.2
    unfold q10RegisterSliceWires
    apply List.mem_map.mpr
    refine ⟨localIndex, List.mem_finRange _, ?_⟩
    unfold RegisterSlice.ancillaWire
    apply congrArg (fun globalIndex : Fin p.ancillaWidth =>
      (Wire.ancilla globalIndex : Wire p.ancillaWidth p.systemWidth))
    apply Fin.ext
    change (QLayout.canonical p).oracleWork.start + localIndex.val = index.val
    have workStart : (QLayout.canonical p).oracleWork.start =
        p.generatorSignalWidth :=
      (QLayout.canonicalGeneratorSourceSlices p).work_start
    rw [workStart]
    change p.generatorSignalWidth +
      (index.val - p.generatorSignalWidth) = index.val
    exact Nat.add_sub_of_le signalLe

/-- Extensional normal form for the Q11 input basis.  The system word remains
arbitrary, while every ancilla coordinate is the canonical zero basis. -/
theorem q11AllZeroAncillaInputPredicate_eq_zeroAncillaJointBasis
    {p : QParameters} {basis : JointBasis p.ancillaWidth p.systemWidth}
    (inputZero : q11AllZeroAncillaInputPredicate p basis) :
    basis = zeroAncillaJointBasis p (systemPart basis) := by
  funext wire
  cases wire with
  | ancilla index =>
      exact q11AllZeroAncillaInputPredicate_ancilla_zero inputZero index
  | system index =>
      rfl

/-- A human-readable support contract for one operator boundary.  It says
that a basis input satisfying `inputPredicate` has no matrix coefficient on
an output basis violating `outputPredicate`.  This is the extensional form
used to review work-register restoration independently of circuit syntax. -/
def BasisPredicateTransitionSpecification {basis : Type*}
    (operator : Operator basis)
    (inputPredicate outputPredicate : basis → Prop) : Prop :=
  ∀ input output,
    inputPredicate input →
      ¬ outputPredicate output →
    operator output input = 0

/-- Independent mathematical Q5 contract: the alignment operator turns the
source-reachable Q3/Q4 accumulator relation into an active row selector while
preserving the clean active-column boundary. -/
def Q10OutputAlignmentReadySpecification (p : QParameters) : Prop :=
  BasisPredicateTransitionSpecification
    (outputAlignmentFullAnalyticOperator p)
    (Q10OutputAlignmentReady p)
    (q10AlignedOracleCleanPredicate p)

/-- A state has support only on bases satisfying `predicate`.  This is the
right extensional contract for the Q10 path reached from an all-zero ancilla:
padding selector words are not claimed to be impossible inputs to the dirty
operator; rather, their amplitudes are proved to vanish in the reached state.
-/
def StateSupportedOnBasisPredicate {basis : Type*}
    (predicate : basis → Prop) (state : State basis) : Prop :=
  ∀ output, ¬ predicate output → state output = 0

/-- The coordinate-support predicate as an honest linear subspace.  This is
the finite-dimensional object used to transport a clean invariant through
the adjoint of a unitary operator. -/
def basisPredicateSupportSubmodule {basis : Type*}
    (predicate : basis → Prop) : Submodule ℂ (State basis) where
  carrier := { state | StateSupportedOnBasisPredicate predicate state }
  zero_mem' := by
    intro output _
    rfl
  add_mem' := by
    intro left right leftSupported rightSupported output outside
    simp [leftSupported output outside, rightSupported output outside]
  smul_mem' := by
    intro scalar state supported output outside
    simp [supported output outside]

@[simp] theorem mem_basisPredicateSupportSubmodule_iff
    {basis : Type*} {predicate : basis → Prop} {state : State basis} :
    state ∈ basisPredicateSupportSubmodule predicate ↔
      StateSupportedOnBasisPredicate predicate state :=
  Iff.rfl

namespace StateSupportedOnBasisPredicate

/-- Intersect two support descriptions of the same state. -/
theorem and {basis : Type*} {left right : basis → Prop}
    {state : State basis}
    (leftSupported : StateSupportedOnBasisPredicate left state)
    (rightSupported : StateSupportedOnBasisPredicate right state) :
    StateSupportedOnBasisPredicate (fun basis => left basis ∧ right basis)
      state := by
  intro output outside
  by_cases leftInside : left output
  · apply rightSupported output
    intro rightInside
    exact outside ⟨leftInside, rightInside⟩
  · exact leftSupported output leftInside

end StateSupportedOnBasisPredicate

/-- Coordinate locality over an arbitrary finite Boolean wire type.  Core's
`OperatorPreservesOutside` specializes to `Fin n`; Q uses the disjoint-sum
wire type `Wire ancilla system`, so the human specification keeps this
general finite-coordinate form. -/
def BasisOperatorPreservesOutside {wire : Type*} [Fintype wire]
    [DecidableEq wire]
    (support : Finset wire)
    (operator : Operator (wire → Bool)) : Prop :=
  ∀ output input, operator output input ≠ 0 →
    ∀ candidate, candidate ∉ support → output candidate = input candidate

namespace BasisPredicateTransitionSpecification

/-- A basis ket is supported on any predicate satisfied by its basis label. -/
theorem basisKet_supported {basis : Type*} [Fintype basis]
    [DecidableEq basis] {predicate : basis → Prop} {input : basis}
    (inside : predicate input) :
    StateSupportedOnBasisPredicate predicate (basisKet input) := by
  intro output outputOutside
  simp only [basisKet, VerifiedMath.Basis.vector_apply]
  split
  · rename_i equal
    subst output
    exact False.elim (outputOutside inside)
  · rfl

/-- A basis-support transition transports arbitrary states supported on its
input predicate to states supported on its output predicate. -/
theorem applyOperator_supported {basis : Type*} [Fintype basis]
    [DecidableEq basis] {operator : Operator basis}
    {inputPredicate outputPredicate : basis → Prop}
    (maps : BasisPredicateTransitionSpecification operator
      inputPredicate outputPredicate)
    {state : State basis}
    (supported : StateSupportedOnBasisPredicate inputPredicate state) :
    StateSupportedOnBasisPredicate outputPredicate
      (applyOperator operator state) := by
  intro output outputOutside
  unfold applyOperator Matrix.mulVec dotProduct
  apply Finset.sum_eq_zero
  intro input _
  by_cases inputInside : inputPredicate input
  · change operator output input * state input = 0
    rw [maps input output inputInside outputOutside, zero_mul]
  · rw [supported input inputInside, mul_zero]

/-- A unitary operator that preserves a finite coordinate subspace also has
an adjoint preserving the same subspace.  This is the reusable mathematical
reason that reversing a clean compute--use--uncompute circuit does not leak
out of its clean sector; it avoids re-expanding the reversed gate AST.

The proof restricts the unitary action to the invariant finite-dimensional
subspace.  The restriction is injective, hence surjective, and the adjoint is
its inverse. -/
theorem conjTranspose_of_unitary_invariant
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {operator : Operator basis} {predicate : basis → Prop}
    (maps : BasisPredicateTransitionSpecification operator predicate predicate)
    (unitary : operator ∈ Matrix.unitaryGroup basis ℂ) :
    BasisPredicateTransitionSpecification
      (Matrix.conjTranspose operator) predicate predicate := by
  let cleanSpace := basisPredicateSupportSubmodule predicate
  let restricted : cleanSpace →ₗ[ℂ] cleanSpace :=
    { toFun := fun state =>
        ⟨applyOperator operator state.1,
          maps.applyOperator_supported state.2⟩
      map_add' := by
        intro left right
        apply Subtype.ext
        exact applyOperator_add operator left.1 right.1
      map_smul' := by
        intro scalar state
        apply Subtype.ext
        exact applyOperator_smul operator scalar state.1 }
  have leftInverse (state : State basis) :
      applyOperator (Matrix.conjTranspose operator)
          (applyOperator operator state) = state := by
    rw [← applyOperator_mul]
    have unitaryProduct : Matrix.conjTranspose operator * operator = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Matrix.mem_unitaryGroup_iff'.mp unitary)
    rw [unitaryProduct]
    exact Matrix.one_mulVec state
  have restrictedInjective : Function.Injective restricted := by
    intro left right equal
    apply Subtype.ext
    have valueEqual : applyOperator operator left.1 =
        applyOperator operator right.1 := congrArg Subtype.val equal
    calc
      left.1 = applyOperator (Matrix.conjTranspose operator)
          (applyOperator operator left.1) := (leftInverse left.1).symm
      _ = applyOperator (Matrix.conjTranspose operator)
          (applyOperator operator right.1) := congrArg _ valueEqual
      _ = right.1 := leftInverse right.1
  have restrictedSurjective : Function.Surjective restricted :=
    LinearMap.injective_iff_surjective.mp restrictedInjective
  have adjointMapsSupported (state : State basis)
      (supported : StateSupportedOnBasisPredicate predicate state) :
      StateSupportedOnBasisPredicate predicate
        (applyOperator (Matrix.conjTranspose operator) state) := by
    rcases restrictedSurjective ⟨state, supported⟩ with
      ⟨preimage, imageEqual⟩
    have valueEqual : applyOperator operator preimage.1 = state :=
      congrArg Subtype.val imageEqual
    have resultEqual : applyOperator (Matrix.conjTranspose operator) state =
        preimage.1 := by
      rw [← valueEqual]
      exact leftInverse preimage.1
    rw [resultEqual]
    exact preimage.2
  intro input output inputInside outputOutside
  have supportedInput : StateSupportedOnBasisPredicate predicate
      (basisKet input) := basisKet_supported inputInside
  have supportedOutput := adjointMapsSupported (basisKet input) supportedInput
  simpa using supportedOutput output outputOutside

/-- A local basis-support transition lifts through an injective wire
placement.  The outside tensor factor is an identity, so only the restricted
placed basis participates in the predicate. -/
theorem wireLift
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    {operator : Operator (QubitBasis sourceQubits)}
    {inputPredicate outputPredicate : QubitBasis sourceQubits → Prop}
    (maps : BasisPredicateTransitionSpecification operator
      inputPredicate outputPredicate) :
    BasisPredicateTransitionSpecification
      (wireLiftOperator placement operator)
      (fun input => inputPredicate (restrictToPlacedWires placement input))
      (fun output => outputPredicate
        (restrictToPlacedWires placement output)) := by
  intro input output inputInside outputOutside
  rw [wireLiftOperator_apply]
  rw [maps (restrictToPlacedWires placement input)
    (restrictToPlacedWires placement output) inputInside outputOutside,
    zero_mul]

/-- Basis-support transitions are invariant under a bijective renaming of
the finite basis. -/
theorem reindex
    {sourceBasis targetBasis : Type*}
    [Fintype sourceBasis] [DecidableEq sourceBasis]
    [Fintype targetBasis] [DecidableEq targetBasis]
    (equivalence : sourceBasis ≃ targetBasis)
    {operator : Operator sourceBasis}
    {inputPredicate outputPredicate : sourceBasis → Prop}
    (maps : BasisPredicateTransitionSpecification operator
      inputPredicate outputPredicate) :
    BasisPredicateTransitionSpecification
      (Matrix.reindex equivalence equivalence operator)
      (inputPredicate ∘ equivalence.symm)
      (outputPredicate ∘ equivalence.symm) := by
  intro input output inputInside outputOutside
  simpa [Matrix.reindex_apply] using
    maps (equivalence.symm input) (equivalence.symm output)
      inputInside outputOutside

/-- Intersect two invariant basis predicates for the same operator. -/
theorem and
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    {operator : Operator basis} {left right : basis → Prop}
    (leftMaps : BasisPredicateTransitionSpecification operator left left)
    (rightMaps : BasisPredicateTransitionSpecification operator right right) :
    BasisPredicateTransitionSpecification operator
      (fun basis => left basis ∧ right basis)
      (fun basis => left basis ∧ right basis) := by
  intro input output inputInside outputOutside
  by_contra nonzero
  apply outputOutside
  constructor
  · by_contra outsideLeft
    exact nonzero (leftMaps input output inputInside.1 outsideLeft)
  · by_contra outsideRight
    exact nonzero (rightMaps input output inputInside.2 outsideRight)

/-- The identity operator transports every predicate to itself. -/
theorem one {basis : Type*} [Fintype basis] [DecidableEq basis]
    (predicate : basis → Prop) :
    BasisPredicateTransitionSpecification
      (1 : Operator basis) predicate predicate := by
  intro input output inputInside outputOutside
  by_cases equal : output = input
  · subst output
    exact False.elim (outputOutside inputInside)
  · simp [equal]

/-- Basis-support contracts compose in source execution order. -/
theorem mul {basis : Type*} [Fintype basis] [DecidableEq basis]
    {first second : Operator basis}
    {inputPredicate middlePredicate outputPredicate : basis → Prop}
    (firstMaps : BasisPredicateTransitionSpecification first
      inputPredicate middlePredicate)
    (secondMaps : BasisPredicateTransitionSpecification second
      middlePredicate outputPredicate) :
    BasisPredicateTransitionSpecification (second * first)
      inputPredicate outputPredicate := by
  intro input output inputInside outputOutside
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro middle _
  by_cases middleInside : middlePredicate middle
  · rw [secondMaps middle output middleInside outputOutside, zero_mul]
  · rw [firstMaps input middle inputInside middleInside, mul_zero]

/-- Strengthen an invariant support contract with an additional basis
predicate that is preserved on every nonzero matrix entry. -/
theorem strengthenInvariant {basis : Type*} [Fintype basis]
    [DecidableEq basis] {operator : Operator basis}
    {base extra : basis → Prop}
    (baseMaps : BasisPredicateTransitionSpecification operator base base)
    (extraMaps : ∀ output input, operator output input ≠ 0 →
      extra input → extra output) :
    BasisPredicateTransitionSpecification operator
      (fun input => base input ∧ extra input)
      (fun output => base output ∧ extra output) := by
  intro input output inputInside outputOutside
  by_contra nonzero
  apply outputOutside
  constructor
  · by_contra outputBaseOutside
    exact nonzero (baseMaps input output inputInside.1 outputBaseOutside)
  · exact extraMaps output input nonzero inputInside.2

/-- Variant of `strengthenInvariant` where preservation of the extra
predicate may use the base invariant on the input basis. -/
theorem strengthenInvariantWithBase {basis : Type*} [Fintype basis]
    [DecidableEq basis] {operator : Operator basis}
    {base extra : basis → Prop}
    (baseMaps : BasisPredicateTransitionSpecification operator base base)
    (extraMaps : ∀ output input, operator output input ≠ 0 →
      base input → extra input → extra output) :
    BasisPredicateTransitionSpecification operator
      (fun input => base input ∧ extra input)
      (fun output => base output ∧ extra output) := by
  intro input output inputInside outputOutside
  by_contra nonzero
  apply outputOutside
  constructor
  · by_contra outputBaseOutside
    exact nonzero (baseMaps input output inputInside.1 outputBaseOutside)
  · exact extraMaps output input nonzero inputInside.1 inputInside.2

/-- Restrict the admissible input predicate without changing the operator or
its output contract. -/
theorem restrictInput {basis : Type*} [Fintype basis] [DecidableEq basis]
    {operator : Operator basis}
    {inputPredicate strongerInput outputPredicate : basis → Prop}
    (maps : BasisPredicateTransitionSpecification operator
      inputPredicate outputPredicate)
    (stronger : ∀ input, strongerInput input → inputPredicate input) :
    BasisPredicateTransitionSpecification operator
      strongerInput outputPredicate := by
  intro input output inputInside outputOutside
  exact maps input output (stronger input inputInside) outputOutside

/-- Support locality preserves a zero-on-list basis predicate whenever the
operator support is disjoint from the protected wires.  This is the reusable
proof route for Q10 stages that do not borrow internal oracle work. -/
theorem ofPreservesOutsideZeroOnList
    {wire : Type*} [Fintype wire] [DecidableEq wire]
    {operator : Operator (wire → Bool)}
    (support : Finset wire)
    (protectedWires : List wire)
    (locality : BasisOperatorPreservesOutside support operator)
    (disjoint : Disjoint support protectedWires.toFinset) :
    BasisPredicateTransitionSpecification operator
      (fun input => ∀ wire ∈ protectedWires, input wire = false)
      (fun output => ∀ wire ∈ protectedWires, output wire = false) := by
  intro input output inputZero outputDirty
  by_contra nonzero
  apply outputDirty
  intro wire member
  have outsideSupport : wire ∉ support := by
    intro supported
    exact (Finset.disjoint_left.mp disjoint) supported (by simpa using member)
  rw [locality output input nonzero wire outsideSupport]
  exact inputZero wire member

end BasisPredicateTransitionSpecification

/-- Q10 specialization of support locality to the restored internal-work
suffix.  It intentionally does not mention the signal prefix. -/
theorem q10GeneratorWorkCleanTransition_of_preservesOutside
    {p : QParameters}
    {operator : Operator (JointBasis p.ancillaWidth p.systemWidth)}
    (support : Finset (Wire p.ancillaWidth p.systemWidth))
    (locality : BasisOperatorPreservesOutside support operator)
    (disjoint : Disjoint support
      (q10RegisterSliceWires (systemWidth := p.systemWidth)
        (QLayout.canonical p).oracleWork).toFinset) :
    BasisPredicateTransitionSpecification operator
      (q10GeneratorWorkCleanPredicate p)
      (q10GeneratorWorkCleanPredicate p) := by
  exact BasisPredicateTransitionSpecification.ofPreservesOutsideZeroOnList
    support
      (q10RegisterSliceWires (systemWidth := p.systemWidth)
        (QLayout.canonical p).oracleWork)
      locality disjoint

/-- Reviewable nine-edge clean-boundary ledger for Q10.  The first edge uses
the complete all-zero-ancilla input predicate; subsequent edges preserve only
the internal oracle-work suffix.  Thus the signal register may contain the
intended block-encoding output after the first stage. -/
structure Q10AllZeroAncillaWorkCleanStageEvidence (p : QParameters) : Prop where
  columnUniform : BasisPredicateTransitionSpecification
    (sharedCoreColumnUniformPreparationFullAnalyticOperator p)
    (q11AllZeroAncillaInputPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  systemToColumnKey : BasisPredicateTransitionSpecification
    (xorSystemIntoColumnKeyFullAnalyticOperator p)
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  columnOracle : BasisPredicateTransitionSpecification
    (q3ColumnOracleRecordedOperator p)
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  amplitudeSign : BasisPredicateTransitionSpecification
    (amplitudeSignFullAnalyticOperator p)
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  outputAlignment : BasisPredicateTransitionSpecification
    (outputAlignmentFullAnalyticOperator p)
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  columnOracleInverse : BasisPredicateTransitionSpecification
    (Matrix.conjTranspose (q3ColumnOracleRecordedOperator p))
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  rowOracle : BasisPredicateTransitionSpecification
    (q7RowOracleRecordedOperator p)
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  amplitudeSignalFlip : BasisPredicateTransitionSpecification
    (amplitudeSignalFlipFullAnalyticOperator p)
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  rowUniformInverse : BasisPredicateTransitionSpecification
    (Matrix.conjTranspose
      (sharedCoreRowUniformPreparationFullAnalyticOperator p))
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)

/-- The four Q10 stages that preserve internal work solely because their
operator support is disjoint from that work.  These obligations must not be
used for uniform preparation or the row/column oracles, which borrow scratch
and require genuine restoration proofs. -/
structure Q10WorkLocalityEvidence (p : QParameters) where
  systemToColumnKeySupport : Finset (Wire p.ancillaWidth p.systemWidth)
  systemToColumnKeyLocality : BasisOperatorPreservesOutside
    systemToColumnKeySupport (xorSystemIntoColumnKeyFullAnalyticOperator p)
  systemToColumnKeyDisjoint : Disjoint systemToColumnKeySupport
    (q10RegisterSliceWires (systemWidth := p.systemWidth)
      (QLayout.canonical p).oracleWork).toFinset
  amplitudeSignSupport : Finset (Wire p.ancillaWidth p.systemWidth)
  amplitudeSignLocality : BasisOperatorPreservesOutside amplitudeSignSupport
    (amplitudeSignFullAnalyticOperator p)
  amplitudeSignDisjoint : Disjoint amplitudeSignSupport
    (q10RegisterSliceWires (systemWidth := p.systemWidth)
      (QLayout.canonical p).oracleWork).toFinset
  outputAlignmentSupport : Finset (Wire p.ancillaWidth p.systemWidth)
  outputAlignmentLocality : BasisOperatorPreservesOutside outputAlignmentSupport
    (outputAlignmentFullAnalyticOperator p)
  outputAlignmentDisjoint : Disjoint outputAlignmentSupport
    (q10RegisterSliceWires (systemWidth := p.systemWidth)
      (QLayout.canonical p).oracleWork).toFinset
  amplitudeSignalFlipSupport : Finset
    (Wire p.ancillaWidth p.systemWidth)
  amplitudeSignalFlipLocality : BasisOperatorPreservesOutside
    amplitudeSignalFlipSupport (amplitudeSignalFlipFullAnalyticOperator p)
  amplitudeSignalFlipDisjoint : Disjoint amplitudeSignalFlipSupport
    (q10RegisterSliceWires (systemWidth := p.systemWidth)
      (QLayout.canonical p).oracleWork).toFinset

/-- The five Q10 edges whose work-clean guarantees are semantic restoration
claims rather than support-disjointness claims. -/
structure Q10BorrowingStageRestorationEvidence (p : QParameters) : Prop where
  columnUniform : BasisPredicateTransitionSpecification
    (sharedCoreColumnUniformPreparationFullAnalyticOperator p)
    (q11AllZeroAncillaInputPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  columnOracle : BasisPredicateTransitionSpecification
    (q3ColumnOracleRecordedOperator p)
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  columnOracleInverse : BasisPredicateTransitionSpecification
    (Matrix.conjTranspose (q3ColumnOracleRecordedOperator p))
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  rowOracle : BasisPredicateTransitionSpecification
    (q7RowOracleRecordedOperator p)
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  rowUniformInverse : BasisPredicateTransitionSpecification
    (Matrix.conjTranspose
      (sharedCoreRowUniformPreparationFullAnalyticOperator p))
    (q10GeneratorWorkCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)

/-- Assemble the review ledger from the two disjoint proof classes: four
support-local edges and five scratch-borrowing restoration edges. -/
theorem Q10AllZeroAncillaWorkCleanStageEvidence.ofRestorationAndLocality
    {p : QParameters}
    (restoration : Q10BorrowingStageRestorationEvidence p)
    (locality : Q10WorkLocalityEvidence p) :
    Q10AllZeroAncillaWorkCleanStageEvidence p where
  columnUniform := restoration.columnUniform
  systemToColumnKey := q10GeneratorWorkCleanTransition_of_preservesOutside
    locality.systemToColumnKeySupport locality.systemToColumnKeyLocality
      locality.systemToColumnKeyDisjoint
  columnOracle := restoration.columnOracle
  amplitudeSign := q10GeneratorWorkCleanTransition_of_preservesOutside
    locality.amplitudeSignSupport locality.amplitudeSignLocality
      locality.amplitudeSignDisjoint
  outputAlignment := q10GeneratorWorkCleanTransition_of_preservesOutside
    locality.outputAlignmentSupport locality.outputAlignmentLocality
      locality.outputAlignmentDisjoint
  columnOracleInverse := restoration.columnOracleInverse
  rowOracle := restoration.rowOracle
  amplitudeSignalFlip := q10GeneratorWorkCleanTransition_of_preservesOutside
    locality.amplitudeSignalFlipSupport locality.amplitudeSignalFlipLocality
      locality.amplitudeSignalFlipDisjoint
  rowUniformInverse := restoration.rowUniformInverse

/-- Full dirty Q10 operator: execution-order product of the nine children. -/
def q10ProbabilityGeneratorRecordedOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  operatorSequence (q10ProbabilityGeneratorSourceOperators p)

/-- State after the first `stageCount` Q10 source-order children, starting
from one system basis with the complete Q ancilla initialized to zero.  This
is a mathematical prefix state: it depends only on the nine independently
defined operators, not on a circuit execution function. -/
def q10SourceBasisAfterStage (p : QParameters) (stageCount : Nat)
    (system : RegisterBasis p.systemWidth) :
    State (JointBasis p.ancillaWidth p.systemWidth) :=
  applyOperator
    (operatorSequence ((q10ProbabilityGeneratorSourceOperators p).take
      stageCount))
    (basisKet (zeroAncillaJointBasis p system))

/--
Preferred clean-boundary ledger for Q10.

Unlike `Q10AllZeroAncillaWorkCleanStageEvidence`, this record does not claim
that every dirty-basis input with zero oracle work is semantically reachable.
It follows the actual state produced from the all-zero ancilla sector.  The
phase predicates expose exactly the selector validity needed at Q3, reverse
Q3, and Q7; padding words remain in the full-space operator but have zero
amplitude in these reached prefix states.
-/
structure Q10SourceBasisCleanPipelineEvidence (p : QParameters) : Prop where
  afterColumnUniform : ∀ system,
    StateSupportedOnBasisPredicate (q10ColumnOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 1 system)
  afterSystemToColumnKey : ∀ system,
    StateSupportedOnBasisPredicate (q10ColumnOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 2 system)
  afterColumnOracle : ∀ system,
    StateSupportedOnBasisPredicate (q10ColumnOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 3 system)
  afterAmplitudeSign : ∀ system,
    StateSupportedOnBasisPredicate (q10ColumnOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 4 system)
  afterOutputAlignment : ∀ system,
    StateSupportedOnBasisPredicate (q10AlignedOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 5 system)
  afterColumnOracleInverse : ∀ system,
    StateSupportedOnBasisPredicate (q10AlignedOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 6 system)
  afterRowOracle : ∀ system,
    StateSupportedOnBasisPredicate (q10RowOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 7 system)
  afterAmplitudeSignalFlip : ∀ system,
    StateSupportedOnBasisPredicate (q10RowOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 8 system)
  afterRowUniformInverse : ∀ system,
    StateSupportedOnBasisPredicate (q10GeneratorWorkCleanPredicate p)
      (applyOperator (q10ProbabilityGeneratorRecordedOperator p)
        (basisKet (zeroAncillaJointBasis p system)))

/-- The two genuinely remaining semantic obligations after the generic
locality/oracle restoration theorems have been factored out.  Q5 must show
that its reached output carries a valid row selector; Q9 must unprepare that
selector while returning the shared uniform scratch to the work-clean span.
-/
structure Q10RemainingCleanPipelineObligations (p : QParameters) : Prop where
  afterOutputAlignment : ∀ system,
    StateSupportedOnBasisPredicate (q10AlignedOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 5 system)
  rowUniformInverse : BasisPredicateTransitionSpecification
    (Matrix.conjTranspose
      (sharedCoreRowUniformPreparationFullAnalyticOperator p))
    (q10RowOracleCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)

/-- Mathematical clean-boundary obligation for Q10.  Matrix coefficients
from a work-clean basis input to a work-dirty basis output must vanish.  This
is kept separate from both full-space Exact correctness and the Q11 success
block, so neither theorem is used as a substitute for another. -/
def Q10GeneratorWorkRestorationSpecification (p : QParameters) : Prop :=
  ∀ input output,
    q10GeneratorWorkCleanPredicate p input →
      ¬ q10GeneratorWorkCleanPredicate p output →
      q10ProbabilityGeneratorRecordedOperator p output input = 0

/-- The source-faithful boundary actually consumed by H2.  Q10 is entered
with the complete Q ancilla register zero; after Q10 only the internal oracle
work is required to be zero.  The signal prefix is intentionally absent from
the output predicate because it carries the block-encoding signal. -/
def Q10AllZeroAncillaToWorkCleanSpecification (p : QParameters) : Prop :=
  ∀ input output,
    q11AllZeroAncillaInputPredicate p input →
      ¬ q10GeneratorWorkCleanPredicate p output →
      q10ProbabilityGeneratorRecordedOperator p output input = 0

/-- The source-reachable prefix ledger implies the exact Q10 clean boundary.
Only the final support field is needed for this implication; the eight
intermediate fields remain in the record so a reviewer can audit why Q3/Q7
receive active selectors and where those facts are consumed. -/
theorem Q10SourceBasisCleanPipelineEvidence.toSpecification
    {p : QParameters} (evidence : Q10SourceBasisCleanPipelineEvidence p) :
    Q10AllZeroAncillaToWorkCleanSpecification p := by
  intro input output inputZero outputDirty
  have inputEq :=
    q11AllZeroAncillaInputPredicate_eq_zeroAncillaJointBasis inputZero
  rw [inputEq]
  simpa only [applyOperator_basisKet] using
    evidence.afterRowUniformInverse (systemPart input) output outputDirty

/-- The Q10 boundary theorem is exactly the finite composition of the nine
reviewable stage contracts.  No circuit expansion, block-encoding theorem, or
representative parameter value enters this proof. -/
theorem Q10AllZeroAncillaWorkCleanStageEvidence.toSpecification
    {p : QParameters}
    (evidence : Q10AllZeroAncillaWorkCleanStageEvidence p) :
    Q10AllZeroAncillaToWorkCleanSpecification p := by
  have afterCopy := evidence.columnUniform.mul evidence.systemToColumnKey
  have afterColumnOracle := afterCopy.mul evidence.columnOracle
  have afterAmplitudeSign := afterColumnOracle.mul evidence.amplitudeSign
  have afterAlignment := afterAmplitudeSign.mul evidence.outputAlignment
  have afterColumnInverse :=
    afterAlignment.mul evidence.columnOracleInverse
  have afterRowOracle := afterColumnInverse.mul evidence.rowOracle
  have afterSignalFlip := afterRowOracle.mul evidence.amplitudeSignalFlip
  have afterRowInverse := afterSignalFlip.mul evidence.rowUniformInverse
  change BasisPredicateTransitionSpecification
    (q10ProbabilityGeneratorRecordedOperator p)
    (q11AllZeroAncillaInputPredicate p)
    (q10GeneratorWorkCleanPredicate p)
  simpa [q10ProbabilityGeneratorRecordedOperator,
    q10ProbabilityGeneratorSourceOperators, operatorSequence,
    Matrix.mul_assoc] using afterRowInverse

/-- The stronger work-clean invariant implies the exact all-zero-ancilla
boundary used by the history construction.  The converse is not assumed. -/
theorem Q10GeneratorWorkRestorationSpecification.toAllZeroAncilla
    {p : QParameters} (restores : Q10GeneratorWorkRestorationSpecification p) :
    Q10AllZeroAncillaToWorkCleanSpecification p := by
  intro input output inputZero outputDirty
  exact restores input output inputZero.2 outputDirty

/--
The same Q10 definition in operator-product order.  This theorem is kept
separate from the source-order list so a reviewer can check both conventions.
-/
theorem q10ProbabilityGeneratorRecordedOperator_eq_product
    (p : QParameters) :
    q10ProbabilityGeneratorRecordedOperator p =
      Matrix.conjTranspose
          (sharedCoreRowUniformPreparationFullAnalyticOperator p) *
        amplitudeSignalFlipFullAnalyticOperator p *
        q7RowOracleRecordedOperator p *
        Matrix.conjTranspose (q3ColumnOracleRecordedOperator p) *
        outputAlignmentFullAnalyticOperator p *
        amplitudeSignFullAnalyticOperator p *
        q3ColumnOracleRecordedOperator p *
        xorSystemIntoColumnKeyFullAnalyticOperator p *
        sharedCoreColumnUniformPreparationFullAnalyticOperator p := by
  simp [q10ProbabilityGeneratorRecordedOperator,
    q10ProbabilityGeneratorSourceOperators, operatorSequence]

/-- The human-facing nine-stage definition is the established independent target. -/
theorem q10ProbabilityGeneratorRecordedOperator_eq_established
    (p : QParameters) :
    q10ProbabilityGeneratorRecordedOperator p =
      ProbabilityGeneratorFullAnalyticOperator p := by
  simp [q10ProbabilityGeneratorRecordedOperator,
    q10ProbabilityGeneratorSourceOperators, operatorSequence,
    q3ColumnOracleRecordedOperator, q7RowOracleRecordedOperator,
    ProbabilityGeneratorFullAnalyticOperator]

/-! ## Q11 success block and normalization -/

/-- All-zero-ancilla success block of the independently defined Q10 operator. -/
def q11ProbabilityGeneratorSuccessBlock (p : QParameters) :
    Operator (RegisterBasis p.systemWidth) :=
  Matrix.of fun output input =>
    q10ProbabilityGeneratorRecordedOperator p
      (combineBasis (allZeroAncilla p.ancillaWidth) output)
      (combineBasis (allZeroAncilla p.ancillaWidth) input)

/-- The exact normalization used by the report is `alpha_Q = 3K`. -/
def q11ProbabilityGeneratorNormalization (p : QParameters) : Nat :=
  3 * p.K

theorem q11ProbabilityGeneratorNormalization_pos (p : QParameters) :
    0 < q11ProbabilityGeneratorNormalization p := by
  simp [q11ProbabilityGeneratorNormalization, p.K_pos]

/-- Scaled success block that must equal the embedded probability generator. -/
def q11ScaledSuccessBlock (p : QParameters) :
    Operator (RegisterBasis p.systemWidth) :=
  ((q11ProbabilityGeneratorNormalization p : Nat) : ℂ) •
    q11ProbabilityGeneratorSuccessBlock p

/-- Exact, zero-error block-encoding proposition kept separate from Q10 Exact. -/
def Q11ProbabilityGeneratorBlockEncodingSpecification (p : QParameters) : Prop :=
  q11ScaledSuccessBlock p = embeddedProbabilityGenerator p

end

end ProbabilityGeneratorQProof
