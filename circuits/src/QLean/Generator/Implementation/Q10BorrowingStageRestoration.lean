import QLean.Generator.Implementation.Q10WorkLocality
import QLean.Generator.Implementation.UniformPreparationSharedCoreTargetBridge
import QLean.Generator.Implementation.QSelectorBitBridge
import QLean.Generator.Implementation.QVerifiedFullOracleComponents
import QLean.Generator.Implementation.QActualRejectedPathCorrectness
import QLean.Generator.Implementation.ProbabilityGeneratorCoreExactAdapter
import QLean.Circuits.Foundation.WireEmbeddingL2Analytic
import QLean.Circuits.Foundation.UniformPreparationFullOperatorCorrectness

/-!
# Scratch-borrowing Q10 restoration edges

This module contains the five Q10 edges that cannot be justified merely by
disjoint support.  The column-uniform edge is proved first from the all-zero
ancilla normal form and the independently specified lifted selector state.
The remaining row-uniform and Q3/Q7 edges are kept as explicit obligations
until their branch-complete restoration theorems are assembled.
-/

namespace ProbabilityGeneratorQProof

open VerifiedCircuitCore
open ReversibleCircuit

noncomputable section

/-! ## Selector-observation compatibility -/

private theorem q10SelectorValue_eq_selectorValue :
    ∀ (width : Nat) (basis : RegisterBasis width),
      qOracleSelectorValue width basis = selectorValue width basis
  | 0, _ => rfl
  | width + 1, basis => by
      rw [qOracleSelectorValue, selectorValue]
      exact congrArg
        (fun lower =>
          (if basis (Fin.last width) then 2 ^ width else 0) + lower)
        (q10SelectorValue_eq_selectorValue width
          (fun index => basis index.castSucc))

private theorem q10ColumnSelectorObservation_eq_legacy
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    qOracleSelectorValue p.selectorWidth
        (q10ProjectRegisterBasis (q10ColumnSelectorWire p) input) =
      selectorValue p.selectorWidth
        (projectSelectorBasis p (columnSelectorWire p) input) := by
  rw [q10SelectorValue_eq_selectorValue]
  rfl

/-! ## Q1/Q9 shared-uniform scratch invariant -/

/-- Q's human-facing scratch-prefix predicate is exactly the local shared
uniform compiler scratch-zero predicate transported through the canonical row
placement. -/
theorem q10UniformScratchCleanPredicate_iff_restrictedRowPlacement
    (p : QParameters)
    (basis : JointBasis p.ancillaWidth p.systemWidth) :
    q10UniformScratchCleanPredicate p basis ↔
      (∀ wire ∈
        VerifiedCircuitCore.uniformPreparationAnalyticScratchWires
          p.selectorWidth,
        restrictToPlacedWires
          (analyticSharedUniformCorePlacement p
            (sharedUniformAnalyticRowSelectorWire p)
            (sharedUniformAnalyticRowSelectorWire_injective p)
            (sharedUniformAnalyticRowSelector_scratch_disjoint p))
          (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth basis)
          wire = false) := by
  constructor
  · intro clean wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    rw [restrictToPlacedWires_analyticSharedUniformCorePlacement,
      analyticSharedUniformLocalWire_scratch]
    exact clean _ (List.mem_map.mpr
      ⟨index, List.mem_finRange _, rfl⟩)
  · intro clean wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    have localValue := clean
      (VerifiedCircuitCore.uniformPreparationAnalyticScratchWire
        p.selectorWidth index)
      (List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩)
    simpa using localValue

/-- The forward row-uniform target preserves the exact Q scratch prefix.
The proof is a three-step transport: core scratch restoration, wire lift, and
the canonical JointBasis reindexing. -/
theorem q10RowUniformForward_uniformScratch_transition (p : QParameters) :
    BasisPredicateTransitionSpecification
      (sharedCoreRowUniformPreparationFullAnalyticOperator p)
      (q10UniformScratchCleanPredicate p)
      (q10UniformScratchCleanPredicate p) := by
  let parameters := sharedUniformPreparationParameters p
  let placement := analyticSharedUniformCorePlacement p
    (sharedUniformAnalyticRowSelectorWire p)
    (sharedUniformAnalyticRowSelectorWire_injective p)
    (sharedUniformAnalyticRowSelector_scratch_disjoint p)
  let localPredicate : QubitBasis (2 * parameters.width) → Prop :=
    fun basis => ∀ wire ∈
      VerifiedCircuitCore.uniformPreparationScratchWires parameters.width,
        basis wire = false
  have localMaps : BasisPredicateTransitionSpecification
      (VerifiedCircuitCore.uniformPreparationFullAnalyticOperator parameters)
      localPredicate localPredicate := by
    intro input output inputZero outputNotClean
    apply VerifiedCircuitCore.uniformPreparationFullAnalyticOperator_scratchZero_transition
      parameters input output inputZero
    by_contra noDirtyWire
    apply outputNotClean
    intro wire member
    by_cases wireTrue : output wire = true
    · exact False.elim (noDirtyWire ⟨wire, member, wireTrue⟩)
    · exact Bool.eq_false_of_not_eq_true wireTrue
  have lifted := localMaps.wireLift placement
  have reindexed := lifted.reindex
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm
  change BasisPredicateTransitionSpecification
      (analyticReindexCoreOperatorToJoint
        (VerifiedCircuitCore.wireLiftOperator placement
          (VerifiedCircuitCore.uniformPreparationFullAnalyticOperator
            parameters)))
      (q10UniformScratchCleanPredicate p)
      (q10UniformScratchCleanPredicate p)
  have predicateEq :
      (fun basis : JointBasis p.ancillaWidth p.systemWidth =>
        localPredicate
          (restrictToPlacedWires placement
            (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth basis))) =
        q10UniformScratchCleanPredicate p := by
    funext basis
    apply propext
    change
      (∀ wire ∈
        VerifiedCircuitCore.uniformPreparationAnalyticScratchWires
          p.selectorWidth,
        restrictToPlacedWires
          (analyticSharedUniformCorePlacement p
            (sharedUniformAnalyticRowSelectorWire p)
            (sharedUniformAnalyticRowSelectorWire_injective p)
            (sharedUniformAnalyticRowSelector_scratch_disjoint p))
          (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth basis)
          wire = false) ↔ q10UniformScratchCleanPredicate p basis
    exact (q10UniformScratchCleanPredicate_iff_restrictedRowPlacement
      p basis).symm
  change BasisPredicateTransitionSpecification
      (analyticReindexCoreOperatorToJoint
        (VerifiedCircuitCore.wireLiftOperator placement
          (VerifiedCircuitCore.uniformPreparationFullAnalyticOperator
            parameters)))
      (fun basis =>
        localPredicate
          (restrictToPlacedWires placement
            (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth basis)))
      (fun basis =>
        localPredicate
          (restrictToPlacedWires placement
            (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth basis))) at reindexed
  rw [predicateEq] at reindexed
  exact reindexed

/-- Exact Q wires on which row uniform preparation may act: the row selector
and the shared scratch prefix. -/
def q10RowUniformTouchedWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  rowSelectorWires p ++ q10UniformScratchPrefixWires p

/-- Every wire in the local shared-core placement is one of the declared Q
row-uniform touched wires. -/
theorem analyticSharedUniformLocalWire_mem_q10RowUniformTouchedWires
    (p : QParameters) (index : Fin (2 * p.selectorWidth)) :
    analyticSharedUniformLocalWire p
        (sharedUniformAnalyticRowSelectorWire p) index ∈
      q10RowUniformTouchedWires p := by
  by_cases selector : index.val < p.selectorWidth
  · apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨⟨index.val, selector⟩, List.mem_finRange _, ?_⟩
    simp [analyticSharedUniformLocalWire, selector, rowSelectorWire,
      sharedUniformAnalyticRowSelectorWire]
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨⟨index.val - p.selectorWidth, by omega⟩,
      List.mem_finRange _, ?_⟩
    simp [analyticSharedUniformLocalWire, selector]

/-- The independently defined row-uniform operator has no matrix support
outside the row selector plus shared scratch prefix. -/
theorem sharedCoreRowUniformPreparation_preservesOutside (p : QParameters) :
    BasisOperatorPreservesOutside
      (q10RowUniformTouchedWires p).toFinset
      (sharedCoreRowUniformPreparationFullAnalyticOperator p) := by
  let parameters := sharedUniformPreparationParameters p
  let placement := analyticSharedUniformCorePlacement p
    (sharedUniformAnalyticRowSelectorWire p)
    (sharedUniformAnalyticRowSelectorWire_injective p)
    (sharedUniformAnalyticRowSelector_scratch_disjoint p)
  intro output input nonzero candidate outside
  have coreNonzero :
      VerifiedCircuitCore.wireLiftOperator placement
        (VerifiedCircuitCore.uniformPreparationFullAnalyticOperator parameters)
        (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth output)
        (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input) ≠ 0 := by
    simpa [sharedCoreRowUniformPreparationFullAnalyticOperator,
      analyticReindexCoreOperatorToJoint, parameters, placement,
      Matrix.reindex_apply] using nonzero
  have candidateOutside : analyticWireToCanonicalFin candidate ∉
      Finset.univ.image placement := by
    intro member
    rcases Finset.mem_image.mp member with ⟨placedIndex, _, equal⟩
    have wireEqual : analyticSharedUniformLocalWire p
          (sharedUniformAnalyticRowSelectorWire p) placedIndex = candidate := by
      apply analyticWireToCanonicalFin_injective
      simpa [placement, analyticSharedUniformCorePlacement] using equal
    apply outside
    exact List.mem_toFinset.mpr
      (wireEqual ▸
        analyticSharedUniformLocalWire_mem_q10RowUniformTouchedWires p placedIndex)
  have same := VerifiedCircuitCore.wireLiftOperator_preservesOutsidePlacement
    placement
    (VerifiedCircuitCore.uniformPreparationFullAnalyticOperator parameters)
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth output)
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth input)
    coreNonzero (analyticWireToCanonicalFin candidate) candidateOutside
  simpa [analyticJointBasisCoreEquiv] using same

/-- Row uniform preparation leaves every internal-work wire outside its
shared scratch prefix unchanged. -/
theorem q10RowUniformForward_nonUniformWork_transition (p : QParameters) :
    BasisPredicateTransitionSpecification
      (sharedCoreRowUniformPreparationFullAnalyticOperator p)
      (q10NonUniformWorkCleanPredicate p)
      (q10NonUniformWorkCleanPredicate p) := by
  intro input output inputClean outputDirty
  by_contra nonzero
  apply outputDirty
  intro wire workMember notScratch
  rw [sharedCoreRowUniformPreparation_preservesOutside p output input
    nonzero wire]
  · exact inputClean wire workMember notScratch
  · intro touched
    rcases List.mem_toFinset.mp touched with touched
    rcases List.mem_append.mp touched with rowMember | scratchMember
    · exact (List.disjoint_left.mp
        (rowSelectorWires_disjoint_q10GeneratorWork p))
        rowMember workMember
    · exact notScratch scratchMember

/-- The full Q-layout row-uniform target is unitary for every positive
`q,K`, inherited from the arbitrary-width shared core, wire lift, and basis
reindexing. -/
theorem sharedCoreRowUniformPreparation_mem_unitaryGroup (p : QParameters) :
    sharedCoreRowUniformPreparationFullAnalyticOperator p ∈
      Matrix.unitaryGroup
        (JointBasis p.ancillaWidth p.systemWidth) ℂ := by
  let parameters := sharedUniformPreparationParameters p
  let placement := analyticSharedUniformCorePlacement p
    (sharedUniformAnalyticRowSelectorWire p)
    (sharedUniformAnalyticRowSelectorWire_injective p)
    (sharedUniformAnalyticRowSelector_scratch_disjoint p)
  unfold sharedCoreRowUniformPreparationFullAnalyticOperator
    analyticReindexCoreOperatorToJoint
  apply VerifiedCircuitCore.reindex_mem_unitaryGroup
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm
  apply VerifiedCircuitCore.wireLiftOperator_mem_unitaryGroup placement
  exact VerifiedCircuitCore.uniformPreparationFullAnalyticOperator_mem_unitaryGroup
    parameters

/-- Q9 clean transition.  Forward scratch/remainder invariants are carried
through the unitary adjoint independently and recombined into the complete
Q10 internal-work predicate. -/
theorem q10RowUniformInverse_workClean_transition (p : QParameters) :
    BasisPredicateTransitionSpecification
      (Matrix.conjTranspose
        (sharedCoreRowUniformPreparationFullAnalyticOperator p))
      (q10GeneratorWorkCleanPredicate p)
      (q10GeneratorWorkCleanPredicate p) := by
  have unitary := sharedCoreRowUniformPreparation_mem_unitaryGroup p
  have scratchInverse :=
    BasisPredicateTransitionSpecification.conjTranspose_of_unitary_invariant
      (q10RowUniformForward_uniformScratch_transition p) unitary
  have remainderInverse :=
    BasisPredicateTransitionSpecification.conjTranspose_of_unitary_invariant
      (q10RowUniformForward_nonUniformWork_transition p) unitary
  have combined :=
    BasisPredicateTransitionSpecification.and scratchInverse remainderInverse
  intro input output inputClean outputDirty
  apply combined input output
  · exact
      (q10GeneratorWorkCleanPredicate_iff_uniformScratch_and_remainder
        p input).mp inputClean
  · intro outputClean
    exact outputDirty
      ((q10GeneratorWorkCleanPredicate_iff_uniformScratch_and_remainder
        p output).mpr outputClean)

/-- Q9 consumes the stronger active-row-selector boundary but only promises
restored internal work. -/
theorem q10RowUniformInverse_rowCleanToWorkClean_transition
    (p : QParameters) :
    BasisPredicateTransitionSpecification
      (Matrix.conjTranspose
        (sharedCoreRowUniformPreparationFullAnalyticOperator p))
      (q10RowOracleCleanPredicate p)
      (q10GeneratorWorkCleanPredicate p) := by
  apply (q10RowUniformInverse_workClean_transition p).restrictInput
  intro input clean
  exact clean.1

/-- A lifted column-selector state vanishes on a basis whose internal oracle
work is dirty, because that work lies outside the selector slice and the
background ancilla is all zero. -/
theorem liftColumnSelectorStateOver_zero_of_q10GeneratorWorkDirty
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (state : AbstractSelectorBasis p.selectorWidth → ℂ)
    (output : JointBasis p.ancillaWidth p.systemWidth)
    (outputDirty : ¬ q10GeneratorWorkCleanPredicate p output) :
    liftSelectorStateOver p (columnSelectorWire p)
      (zeroAncillaJointBasis p system) state output = 0 := by
  unfold liftSelectorStateOver
  rw [if_neg]
  intro outsideMatches
  apply outputDirty
  intro wire workMember
  rw [outsideMatches wire]
  · rcases List.mem_map.mp workMember with ⟨index, _, rfl⟩
    rfl
  · intro selectorMember
    exact (List.disjoint_left.mp
      (columnSelectorWires_disjoint_q10GeneratorWork p))
      (by simpa [selectorSliceWires, columnSelectorWires] using selectorMember)
      workMember

/-- The first Q10 edge maps the complete all-zero Q ancilla sector into the
internal-work-clean sector.  The signal/selector output is intentionally left
unconstrained. -/
theorem q10ColumnUniform_allZeroToWorkClean
    (p : QParameters) :
    BasisPredicateTransitionSpecification
      (sharedCoreColumnUniformPreparationFullAnalyticOperator p)
      (q11AllZeroAncillaInputPredicate p)
      (q10GeneratorWorkCleanPredicate p) := by
  intro input output inputZero outputDirty
  have inputEq :=
    q11AllZeroAncillaInputPredicate_eq_zeroAncillaJointBasis inputZero
  have prepared :
      applyOperator
          (sharedCoreColumnUniformPreparationFullAnalyticOperator p)
          (basisKet (zeroAncillaJointBasis p (systemPart input))) =
        liftSelectorStateOver p (columnSelectorWire p)
          (zeroAncillaJointBasis p (systemPart input))
          (idealUniformSelectorState p.selectorWidth p.selectorCount) := by
    rw [← prepareUniformColumnSelectorFullExactOperatorComponent_target p,
      ← (prepareUniformColumnSelectorFullExactOperatorComponent p).correct]
    exact prepareUniformColumnSelectorCircuit_systemBasis_correct_sharedCore
      p (systemPart input)
  rw [inputEq]
  have coefficient := congrFun prepared output
  rw [applyOperator_basisKet] at coefficient
  rw [coefficient]
  exact liftColumnSelectorStateOver_zero_of_q10GeneratorWorkDirty
    p (systemPart input)
      (idealUniformSelectorState p.selectorWidth p.selectorCount)
      output outputDirty

/-- The first Q10 prefix has support only on active column-selector values,
not merely on work-clean bases.  Padding selector words are present in the
ambient dirty space but receive zero uniform-preparation amplitude. -/
theorem q10ColumnUniform_allZeroToColumnOracleClean
    (p : QParameters) :
    BasisPredicateTransitionSpecification
      (sharedCoreColumnUniformPreparationFullAnalyticOperator p)
      (q11AllZeroAncillaInputPredicate p)
      (q10ColumnOracleCleanPredicate p) := by
  intro input output inputZero outputOutside
  have inputEq :=
    q11AllZeroAncillaInputPredicate_eq_zeroAncillaJointBasis inputZero
  have prepared :
      applyOperator
          (sharedCoreColumnUniformPreparationFullAnalyticOperator p)
          (basisKet (zeroAncillaJointBasis p (systemPart input))) =
        qColumnPreparedState p (systemPart input) := by
    rw [← prepareUniformColumnSelectorFullExactOperatorComponent_target p,
      ← (prepareUniformColumnSelectorFullExactOperatorComponent p).correct]
    exact prepareUniformColumnSelectorCircuit_systemBasis_correct_sharedCore
      p (systemPart input)
  rw [inputEq]
  have coefficient := congrFun prepared output
  rw [applyOperator_basisKet] at coefficient
  rw [coefficient]
  by_cases workClean : q10GeneratorWorkCleanPredicate p output
  · apply qColumnPreparedState_eq_zero_of_projected_padding
    exact Nat.le_of_not_gt (fun active => outputOutside ⟨workClean, by
      unfold q10ColumnSelectorActivePredicate
      rw [q10ColumnSelectorObservation_eq_legacy]
      exact active⟩)
  · exact liftColumnSelectorStateOver_zero_of_q10GeneratorWorkDirty
      p (systemPart input)
        (idealUniformSelectorState p.selectorWidth p.selectorCount)
        output workClean

/-- Prefix-state form of the active-selector Q1 support theorem. -/
theorem q10SourceBasisAfterColumnUniform_supported
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (q10ColumnOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 1 system) := by
  have initial := BasisPredicateTransitionSpecification.basisKet_supported
    (q11AllZeroAncillaInputPredicate_zeroAncillaJointBasis p system)
  have supported :=
    (q10ColumnUniform_allZeroToColumnOracleClean p).applyOperator_supported
      initial
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence] using supported

/-- The first mathematical Q10 prefix is exactly the established sparse
column-uniform state. -/
theorem q10SourceBasisAfterColumnUniform_eq_qColumnPreparedState
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    q10SourceBasisAfterStage p 1 system = qColumnPreparedState p system := by
  simp [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence]
  rw [← prepareUniformColumnSelectorFullExactOperatorComponent_target p,
    ← (prepareUniformColumnSelectorFullExactOperatorComponent p).correct]
  exact prepareUniformColumnSelectorCircuit_systemBasis_correct_sharedCore
    p system

/-- Q1 initializes every Q3/Q4/Q5 accumulator outside the prepared column
selector to zero. -/
theorem q10SourceBasisAfterColumnUniform_ready
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (Q10BeforeColumnOracleReady p)
      (q10SourceBasisAfterStage p 1 system) := by
  intro output outsideReady
  by_cases clean : q10ColumnOracleCleanPredicate p output
  · by_cases outside : OutsideSelectorMatches p (columnSelectorWire p)
        (zeroAncillaJointBasis p system) output
    · exfalso
      apply outsideReady
      refine {
        columnClean := clean
        rowSelectorZero := ?_
        selectorOutputZero := ?_
        activeZero := ?_
        amplitudeZero := ?_ }
      · intro index
        apply outside (rowSelectorWire p index)
        intro member
        exact (List.disjoint_left.mp
          (qActualColumnSelectorWires_disjoint_rowSelectorWires p))
            member (by simp [rowSelectorWires])
      · intro index
        apply outside (selectorOutputWire p index)
        intro member
        exact (List.disjoint_left.mp
          (qActualSelectorOutputWires_disjoint_columnSelectorWires p))
            (by simp [selectorOutputWires]) member
      · apply outside (activeWire p)
        exact qActualActiveWire_not_mem_columnSelectorWires p
      · apply outside (amplitudeSignalWire p)
        exact amplitudeSignalWire_not_mem_columnSelectorWires p
    · rw [q10SourceBasisAfterColumnUniform_eq_qColumnPreparedState]
      exact qColumnPreparedState_eq_zero_of_outside_mismatch
        p system output outside
  · exact q10SourceBasisAfterColumnUniform_supported p system output clean

/-! ## Active-selector Q3/Q7 restoration -/

private theorem q10RowSelectorObservation_eq_legacy
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    qOracleSelectorValue p.selectorWidth
        (q10ProjectRegisterBasis (q10RowSelectorWire p) input) =
      selectorValue p.selectorWidth
        (projectSelectorBasis p (rowSelectorWire p) input) := by
  rw [q10SelectorValue_eq_selectorValue]
  rfl

private theorem q10SelectorOutputObservation_eq_legacy
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    qOracleSelectorValue p.selectorWidth
        (q10ProjectRegisterBasis (q10SelectorOutputWire p) input) =
      selectorValue p.selectorWidth
        (projectSelectorBasis p (selectorOutputWire p) input) := by
  rw [q10SelectorValue_eq_selectorValue]
  rfl

private theorem q10RegisterSliceWires_eq_wireList
    {ancillaWidth systemWidth width : Nat}
    (slice : RegisterSlice ancillaWidth width) :
    q10RegisterSliceWires (systemWidth := systemWidth) slice =
      slice.wireList := by
  rfl

/-- Read the physical column-key register as a typed system-width basis. -/
def q10ColumnKeyBasis (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    RegisterBasis p.systemWidth :=
  fun index => input (columnKeyWire p index)

theorem readWires_columnKey_eq_registerBitList_q10ColumnKeyBasis
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    ReversibleCircuit.readWires (columnKeyWires p) input =
      registerBitList (q10ColumnKeyBasis p input) := by
  simp [ReversibleCircuit.readWires, columnKeyWires, registerBitList,
    q10ColumnKeyBasis, columnKeyWire]

/-- The source-level pure total stage and the established reversible circuit
give exactly the same all-basis column permutation. -/
theorem columnReference_eq_runBasis (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    OracleCanonicalTotalProgram.columnReference p input =
      (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input := by
  have compiled := TotalReversibleStage.compiledStage_runBasis_eq_reference
    ((OracleCanonicalTotalProgram.columnChildren p).fullStage p) input
  rw [OracleCanonicalTotalProgram.compile_columnFullStage] at compiled
  simpa [OracleCanonicalTotalProgram.columnReference,
    TotalOracleStageChildren.fullReference] using compiled.symm

/-- Row counterpart of `columnReference_eq_runBasis`. -/
theorem rowReference_eq_runBasis (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    OracleCanonicalTotalProgram.rowReference p input =
      (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input := by
  have compiled := TotalReversibleStage.compiledStage_runBasis_eq_reference
    ((OracleCanonicalTotalProgram.rowChildren p).fullStage p) input
  rw [OracleCanonicalTotalProgram.compile_rowFullStage] at compiled
  simpa [OracleCanonicalTotalProgram.rowReference,
    TotalOracleStageChildren.fullReference] using compiled.symm

/-- Build the canonical column input contract from the mathematical
work-clean/active-selector predicate and a successful delimiter decode. -/
theorem q10ColumnOracleInputSpec
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10ColumnOracleCleanPredicate p input)
    (configuration : QConfiguration p)
    (decoded : decodeDelimiter (q10ColumnKeyBasis p input) =
      some configuration) :
    ColumnOracleInputSpec p configuration
      ⟨qOracleSelectorValue p.selectorWidth
        (q10ProjectRegisterBasis (q10ColumnSelectorWire p) input), clean.2⟩ input where
  column_key_bits := by
    rw [readWires_columnKey_eq_registerBitList_q10ColumnKeyBasis]
    rw [(decodeDelimiter_eq_some_iff.mp decoded)]
  selector_bits := by
    rw [columnSelectorWires_eq_selectorSliceWires]
    have bits := (readWires_selectorSlice_eq_constantBits_iff p
      (columnSelectorWire p) input _
      (qSelector_lt_capacity p
        ⟨qOracleSelectorValue p.selectorWidth
          (q10ProjectRegisterBasis (q10ColumnSelectorWire p) input), clean.2⟩)).2
        (by simpa using (q10ColumnSelectorObservation_eq_legacy p input).symm)
    simpa [selectorSliceWires] using bits
  work_zero := by
    simpa [diagonalOracleWorkWires, q10GeneratorWorkCleanPredicate,
      q10RegisterSliceWires_eq_wireList]
      using clean.1

/-- Illegal-delimiter version of `q10ColumnOracleInputSpec`. -/
theorem q10ColumnOracleIllegalInputSpec
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10ColumnOracleCleanPredicate p input) :
    ColumnOracleIllegalInputSpec p (q10ColumnKeyBasis p input)
      ⟨qOracleSelectorValue p.selectorWidth
        (q10ProjectRegisterBasis (q10ColumnSelectorWire p) input), clean.2⟩ input where
  column_key_bits :=
    readWires_columnKey_eq_registerBitList_q10ColumnKeyBasis p input
  selector_bits := by
    rw [columnSelectorWires_eq_selectorSliceWires]
    have bits := (readWires_selectorSlice_eq_constantBits_iff p
      (columnSelectorWire p) input _
      (qSelector_lt_capacity p
        ⟨qOracleSelectorValue p.selectorWidth
          (q10ProjectRegisterBasis (q10ColumnSelectorWire p) input), clean.2⟩)).2
        (by simpa using (q10ColumnSelectorObservation_eq_legacy p input).symm)
    simpa [selectorSliceWires] using bits
  work_zero := by
    simpa [diagonalOracleWorkWires, q10GeneratorWorkCleanPredicate,
      q10RegisterSliceWires_eq_wireList]
      using clean.1

/-- Q3 preserves the work-clean active-column-selector sector on every
physical system word, splitting only on whether the delimiter is legal. -/
theorem q10ColumnReference_preserves_clean
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10ColumnOracleCleanPredicate p input) :
    q10ColumnOracleCleanPredicate p
      (OracleCanonicalTotalProgram.columnReference p input) := by
  let selector : QSelector p :=
    ⟨qOracleSelectorValue p.selectorWidth
      (q10ProjectRegisterBasis (q10ColumnSelectorWire p) input), clean.2⟩
  cases decoded : decodeDelimiter (q10ColumnKeyBasis p input) with
  | none =>
      have identity := applyColumnOracleReferenceAndRestoreWorkCircuit_illegal_identity
        p (q10ColumnKeyBasis p input) selector input
          (q10ColumnOracleIllegalInputSpec p input clean) decoded
      rw [columnReference_eq_runBasis, identity]
      exact clean
  | some configuration =>
      let specification := q10ColumnOracleInputSpec p input clean
        configuration decoded
      have result := q3CompiledColumnOracle_clean_reference
        configuration selector input specification
      have preserved := result.preservesInputSpec specification
      rw [columnReference_eq_runBasis]
      constructor
      · simpa [q10GeneratorWorkCleanPredicate, diagonalOracleWorkWires,
          q10RegisterSliceWires_eq_wireList]
          using preserved.work_zero
      · have selectorBits := preserved.selector_bits
        rw [columnSelectorWires_eq_selectorSliceWires] at selectorBits
        have selectorBits' : ReversibleCircuit.readWires
            (selectorSliceWires p (columnSelectorWire p))
            ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
              reversibleGatePermutation input) =
            constantBits selector.val p.selectorWidth := by
          simpa [selectorSliceWires] using selectorBits
        have valueEq := (readWires_selectorSlice_eq_constantBits_iff p
          (columnSelectorWire p)
          ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
            reversibleGatePermutation input)
          selector.val (qSelector_lt_capacity p selector)).mp selectorBits'
        unfold q10ColumnSelectorActivePredicate
        rw [q10ColumnSelectorObservation_eq_legacy, valueEq]
        exact selector.isLt

/-- Q3 maps the initialized accumulator boundary to the precise relation
consumed by Q4/Q5.  Accepted branches write a typed row selector before
raising `active`; rejected and illegal branches are the identity. -/
theorem q10ColumnReference_maps_beforeToAfterReady
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (ready : Q10BeforeColumnOracleReady p input) :
    Q10AfterColumnOracleReady p
      (OracleCanonicalTotalProgram.columnReference p input) := by
  let selector : QSelector p :=
    ⟨qOracleSelectorValue p.selectorWidth
      (q10ProjectRegisterBasis (q10ColumnSelectorWire p) input),
      ready.columnClean.2⟩
  cases decoded : decodeDelimiter (q10ColumnKeyBasis p input) with
  | none =>
      have identity := applyColumnOracleReferenceAndRestoreWorkCircuit_illegal_identity
        p (q10ColumnKeyBasis p input) selector input
          (q10ColumnOracleIllegalInputSpec p input ready.columnClean) decoded
      rw [columnReference_eq_runBasis, identity]
      refine {
        columnClean := ready.columnClean
        rowSelectorZero := ready.rowSelectorZero
        amplitudeZero := ready.amplitudeZero
        selectorOutputActiveOfActive := ?_ }
      intro active
      rw [ready.activeZero] at active
      contradiction
  | some configuration =>
      let specification := q10ColumnOracleInputSpec p input
        ready.columnClean configuration decoded
      cases referenceSome : columnReference configuration selector with
      | none =>
          have identity :=
            applyColumnOracleReferenceAndRestoreWorkCircuit_reference_none
              configuration selector input specification referenceSome
          rw [columnReference_eq_runBasis, identity]
          refine {
            columnClean := ready.columnClean
            rowSelectorZero := ready.rowSelectorZero
            amplitudeZero := ready.amplitudeZero
            selectorOutputActiveOfActive := ?_ }
          intro active
          rw [ready.activeZero] at active
          contradiction
      | some reference =>
          have result := q3CompiledColumnOracle_clean_reference
            configuration selector input specification
          let output :=
            (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
              reversibleGatePermutation input
          have outputClean : q10ColumnOracleCleanPredicate p output := by
            change q10ColumnOracleCleanPredicate p
              ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
                reversibleGatePermutation input)
            rw [← columnReference_eq_runBasis p input]
            exact q10ColumnReference_preserves_clean p input ready.columnClean
          have rowZero : q10SelectorZeroPredicate p (q10RowSelectorWire p)
              output := by
            intro index
            exact (result.outside_restored (rowSelectorWire p index)
              (by
                intro member
                exact (List.disjoint_left.mp
                  (qActualRowOutputWires_disjoint_rowSelectorWires p))
                    member (by simp [rowSelectorWires]))
              (by
                intro member
                exact (List.disjoint_left.mp
                  (qTopSelectorOutputWires_disjoint_rowSelectorWires p))
                    member (by simp [rowSelectorWires]))
              (by
                intro equal
                exact qActualNegativeWire_not_mem_rowSelectorWires p
                  (equal ▸ (by simp [rowSelectorWires])))
              (by
                intro equal
                exact qActualActiveWire_not_mem_rowSelectorWires p
                  (equal ▸ (by simp [rowSelectorWires])))).trans
                (ready.rowSelectorZero index)
          have amplitudeZero : output (amplitudeSignalWire p) = false := by
            exact (result.outside_restored (amplitudeSignalWire p)
              (amplitudeSignalWire_not_mem_rowOutputWires p)
              (amplitudeSignalWire_not_mem_selectorOutputWires p)
              (negativeWire_ne_amplitudeSignalWire p).symm
              (activeWire_ne_amplitudeSignalWire p).symm).trans
                ready.amplitudeZero
          have selectorInputZero :
              readWires (selectorOutputWires p) input =
                List.replicate (selectorOutputWires p).length false := by
            apply readWires_eq_replicate_false_of_forall
            intro wire member
            rcases List.mem_map.mp member with ⟨index, _, rfl⟩
            exact ready.selectorOutputZero index
          have observation := result.observation
          simp only [columnOracleAnalyticAction, referenceSome] at observation
          have selectorBits :=
            congrArg ColumnOracleObservation.selectorOutput observation
          simp only [observeColumnOracle, applyColumnReference] at selectorBits
          rw [selectorInputZero, analyticXorConstant_eq_reference,
            controlledXorConstantBits_true_replicate_false] at selectorBits
          have selectorValueEq :
              selectorValue p.selectorWidth
                (projectSelectorBasis p (selectorOutputWire p) output) =
                  reference.rowSelector.val := by
            apply (readWires_selectorSlice_eq_constantBits_iff p
              (selectorOutputWire p) output reference.rowSelector.val
              (qSelector_lt_capacity p reference.rowSelector)).mp
            simpa [selectorOutputWires, selectorSliceWires, constantBits]
              using selectorBits
          rw [columnReference_eq_runBasis]
          refine {
            columnClean := outputClean
            rowSelectorZero := rowZero
            amplitudeZero := amplitudeZero
            selectorOutputActiveOfActive := ?_ }
          intro _
          unfold q10SelectorOutputActivePredicate
          rw [q10SelectorOutputObservation_eq_legacy, selectorValueEq]
          exact reference.rowSelector.isLt

/-- Matrix-support form of the source-reachable Q3 accumulator transition. -/
theorem q10ColumnOracle_beforeToAfterReady_transition (p : QParameters) :
    BasisPredicateTransitionSpecification
      (q3ColumnOracleRecordedOperator p)
      (Q10BeforeColumnOracleReady p)
      (Q10AfterColumnOracleReady p) := by
  intro input output inputReady outputOutside
  rw [q3ColumnOracleRecordedOperator_eq_deterministicReference]
  rw [deterministicOperator_apply]
  split
  · rename_i equal
    exfalso
    apply outputOutside
    rw [equal]
    exact q10ColumnReference_maps_beforeToAfterReady p input inputReady
  · rfl

/-- Q3 does not touch the row-selector register.  This is stated separately
from the Q3 accumulator observation because it is the cross-stage invariant
needed after output alignment. -/
theorem q10ColumnReference_preserves_rowSelectorBasis
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10ColumnOracleCleanPredicate p input) :
    q10ProjectRegisterBasis (q10RowSelectorWire p)
        (OracleCanonicalTotalProgram.columnReference p input) =
      q10ProjectRegisterBasis (q10RowSelectorWire p) input := by
  rw [columnReference_eq_runBasis]
  cases decoded : decodeDelimiter (q10ColumnKeyBasis p input) with
  | none =>
      have identity := applyColumnOracleReferenceAndRestoreWorkCircuit_illegal_identity
        p (q10ColumnKeyBasis p input)
          ⟨qOracleSelectorValue p.selectorWidth
            (q10ProjectRegisterBasis (q10ColumnSelectorWire p) input), clean.2⟩
          input (q10ColumnOracleIllegalInputSpec p input clean) decoded
      rw [identity]
  | some configuration =>
      let selector : QSelector p :=
        ⟨qOracleSelectorValue p.selectorWidth
          (q10ProjectRegisterBasis (q10ColumnSelectorWire p) input), clean.2⟩
      let specification := q10ColumnOracleInputSpec p input clean
        configuration decoded
      have result := q3CompiledColumnOracle_clean_reference
        configuration selector input specification
      funext index
      apply result.outside_restored
      · intro member
        exact (List.disjoint_left.mp
          (qActualRowOutputWires_disjoint_rowSelectorWires p)) member
            (by simp [q10RowSelectorWire, rowSelectorWire, rowSelectorWires])
      · intro member
        exact (List.disjoint_left.mp
          (qTopSelectorOutputWires_disjoint_rowSelectorWires p)) member
            (by simp [q10RowSelectorWire, rowSelectorWire, rowSelectorWires])
      · intro equal
        apply qActualNegativeWire_not_mem_rowSelectorWires p
        rw [← equal]
        simp [q10RowSelectorWire, rowSelectorWire, rowSelectorWires]
      · intro equal
        apply qActualActiveWire_not_mem_rowSelectorWires p
        rw [← equal]
        simp [q10RowSelectorWire, rowSelectorWire, rowSelectorWires]

/-- Consequently Q3 preserves the active-row-selector observation whenever
its own active-column clean contract holds. -/
theorem q10ColumnReference_preserves_rowSelectorActive
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10ColumnOracleCleanPredicate p input)
    (rowActive : q10RowSelectorActivePredicate p input) :
    q10RowSelectorActivePredicate p
      (OracleCanonicalTotalProgram.columnReference p input) := by
  unfold q10RowSelectorActivePredicate at rowActive ⊢
  rw [q10ColumnReference_preserves_rowSelectorBasis p input clean]
  exact rowActive

/-- On the active clean sector, the full dirty column permutation is an
involution.  Legal accepted, legal rejected, and illegal delimiter inputs are
handled separately by the already verified branch-complete oracle theorems. -/
theorem q10ColumnReference_involutive_of_clean
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10ColumnOracleCleanPredicate p input) :
    OracleCanonicalTotalProgram.columnReference p
        (OracleCanonicalTotalProgram.columnReference p input) = input := by
  let selector : QSelector p :=
    ⟨qOracleSelectorValue p.selectorWidth
      (q10ProjectRegisterBasis (q10ColumnSelectorWire p) input), clean.2⟩
  have actualTwice :
      (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
          reversibleGatePermutation
          ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
            reversibleGatePermutation input) = input := by
    cases decoded : decodeDelimiter (q10ColumnKeyBasis p input) with
    | none =>
        have identity :=
          applyColumnOracleReferenceAndRestoreWorkCircuit_illegal_identity
            p (q10ColumnKeyBasis p input) selector input
              (q10ColumnOracleIllegalInputSpec p input clean) decoded
        simp [identity]
    | some configuration =>
        let specification := q10ColumnOracleInputSpec p input clean
          configuration decoded
        cases referenceSome : columnReference configuration selector with
        | none =>
            have identity :=
              applyColumnOracleReferenceAndRestoreWorkCircuit_reference_none
                configuration selector input specification referenceSome
            simp [identity]
        | some reference =>
            exact
              applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some_involutive
                configuration selector reference input specification
                  referenceSome
  rw [columnReference_eq_runBasis p input]
  rw [columnReference_eq_runBasis p
    ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
      reversibleGatePermutation input)]
  exact actualTwice

/-- The inverse column permutation agrees with the forward permutation on the
active clean sector. -/
theorem q10ColumnReference_symm_eq_of_clean
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10ColumnOracleCleanPredicate p input) :
    (OracleCanonicalTotalProgram.columnReference p).symm input =
      OracleCanonicalTotalProgram.columnReference p input := by
  apply (OracleCanonicalTotalProgram.columnReference p).injective
  rw [(OracleCanonicalTotalProgram.columnReference p).apply_symm_apply]
  exact (q10ColumnReference_involutive_of_clean p input clean).symm

/-- Matrix-support form of the active-selector Q3 restoration theorem. -/
theorem q10ColumnOracle_activeSelector_transition (p : QParameters) :
    BasisPredicateTransitionSpecification
      (q3ColumnOracleRecordedOperator p)
      (q10ColumnOracleCleanPredicate p)
      (q10ColumnOracleCleanPredicate p) := by
  intro input output inputClean outputDirty
  rw [q3ColumnOracleRecordedOperator_eq_deterministicReference]
  rw [deterministicOperator_apply]
  split
  · rename_i equal
    exfalso
    apply outputDirty
    rw [equal]
    exact q10ColumnReference_preserves_clean p input inputClean
  · rfl

/-- Matrix-support form of the inverse Q3 occurrence on the active clean
sector.  The adjoint deterministic operator is first identified with the
inverse basis permutation and then with the forward involution on this
sector. -/
theorem q10ColumnOracleInverse_activeSelector_transition (p : QParameters) :
    BasisPredicateTransitionSpecification
      (Matrix.conjTranspose (q3ColumnOracleRecordedOperator p))
      (q10ColumnOracleCleanPredicate p)
      (q10ColumnOracleCleanPredicate p) := by
  intro input output inputClean outputDirty
  rw [q3ColumnOracleRecordedOperator_eq_deterministicReference]
  rw [deterministicOperator_conjTranspose_of_inverse
    (OracleCanonicalTotalProgram.columnReference p)
    (OracleCanonicalTotalProgram.columnReference p).symm
    (OracleCanonicalTotalProgram.columnReference p).symm_apply_apply
    (OracleCanonicalTotalProgram.columnReference p).apply_symm_apply]
  rw [deterministicOperator_apply]
  split
  · rename_i equal
    exfalso
    apply outputDirty
    rw [equal, q10ColumnReference_symm_eq_of_clean p input inputClean]
    exact q10ColumnReference_preserves_clean p input inputClean
  · rfl

/-- Reverse Q3 preserves the aligned boundary: its active-column clean base
is preserved by involution, and the row selector is an untouched external
register. -/
theorem q10ColumnOracleInverse_preserves_alignedClean (p : QParameters) :
    BasisPredicateTransitionSpecification
      (Matrix.conjTranspose (q3ColumnOracleRecordedOperator p))
      (q10AlignedOracleCleanPredicate p)
      (q10AlignedOracleCleanPredicate p) := by
  apply BasisPredicateTransitionSpecification.strengthenInvariantWithBase
    (q10ColumnOracleInverse_activeSelector_transition p)
  intro output input nonzero clean rowActive
  rw [q3ColumnOracleRecordedOperator_eq_deterministicReference] at nonzero
  rw [deterministicOperator_conjTranspose_of_inverse
    (OracleCanonicalTotalProgram.columnReference p)
    (OracleCanonicalTotalProgram.columnReference p).symm
    (OracleCanonicalTotalProgram.columnReference p).symm_apply_apply
    (OracleCanonicalTotalProgram.columnReference p).apply_symm_apply]
      at nonzero
  rw [deterministicOperator_apply] at nonzero
  split at nonzero
  · rename_i equal
    rw [equal, q10ColumnReference_symm_eq_of_clean p input clean]
    exact q10ColumnReference_preserves_rowSelectorActive
      p input clean rowActive
  · simp at nonzero

/-- Q1--Q2 prefix support. -/
theorem q10SourceBasisAfterSystemToColumnKey_supported
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (q10ColumnOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 2 system) := by
  have supported := BasisPredicateTransitionSpecification.applyOperator_supported
    (q10SystemToColumnKey_preserves_columnOracleClean p)
      (q10SourceBasisAfterColumnUniform_supported p system)
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul] using supported

/-- Q1--Q2 preserve the complete Q3 accumulator-ready boundary. -/
theorem q10SourceBasisAfterSystemToColumnKey_ready
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (Q10BeforeColumnOracleReady p)
      (q10SourceBasisAfterStage p 2 system) := by
  have supported := BasisPredicateTransitionSpecification.applyOperator_supported
    (q10SystemToColumnKey_preserves_beforeColumnOracleReady p)
      (q10SourceBasisAfterColumnUniform_ready p system)
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul] using supported

/-- Q1--Q3 prefix support. -/
theorem q10SourceBasisAfterColumnOracle_supported
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (q10ColumnOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 3 system) := by
  have supported := BasisPredicateTransitionSpecification.applyOperator_supported
    (q10ColumnOracle_activeSelector_transition p)
      (q10SourceBasisAfterSystemToColumnKey_supported p system)
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul, Matrix.mul_assoc] using supported

/-- Q1--Q3 source support with the accepted-selector relation exposed. -/
theorem q10SourceBasisAfterColumnOracle_ready
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (Q10AfterColumnOracleReady p)
      (q10SourceBasisAfterStage p 3 system) := by
  have supported := BasisPredicateTransitionSpecification.applyOperator_supported
    (q10ColumnOracle_beforeToAfterReady_transition p)
      (q10SourceBasisAfterSystemToColumnKey_ready p system)
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul, Matrix.mul_assoc] using supported

/-- Q1--Q4 prefix support. -/
theorem q10SourceBasisAfterAmplitudeSign_supported
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (q10ColumnOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 4 system) := by
  have supported := BasisPredicateTransitionSpecification.applyOperator_supported
    (q10AmplitudeSign_preserves_columnOracleClean p)
      (q10SourceBasisAfterColumnOracle_supported p system)
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul, Matrix.mul_assoc] using supported

/-- Q1--Q4 source support in the exact mathematical form consumed by Q5. -/
theorem q10SourceBasisAfterAmplitudeSign_ready
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (Q10OutputAlignmentReady p)
      (q10SourceBasisAfterStage p 4 system) := by
  have supported := BasisPredicateTransitionSpecification.applyOperator_supported
    (q10AmplitudeSign_afterToAlignmentReady_transition p)
      (q10SourceBasisAfterColumnOracle_ready p system)
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul, Matrix.mul_assoc] using supported

/-- The first five independent Q10 operators reproduce the established sparse
state-pipeline state immediately after output alignment. -/
theorem q10SourceBasisAfterOutputAlignment_eq_qAfterAlignState
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    q10SourceBasisAfterStage p 5 system = qAfterAlignState p system := by
  have xorSystemIntoColumnKey_correct :
      (xorSystemIntoColumnKeyPrimitiveCircuit p).denote
          (primitiveGateOperator :
            PrimitiveGate p.ancillaWidth p.systemWidth →
              Operator (JointBasis p.ancillaWidth p.systemWidth)) =
        xorSystemIntoColumnKeyFullAnalyticOperator p := by
    calc
      _ = (xorSystemIntoColumnKeyExactOperatorComponent p).target :=
        (xorSystemIntoColumnKeyExactOperatorComponent p).correct
      _ = XorSystemIntoColumnKeyTargetOperator p := rfl
      _ = xorSystemIntoColumnKeyFullAnalyticOperator p :=
        XorSystemIntoColumnKeyTargetOperator_eq_fullAnalytic p
  have columnOracleCorrect :
      (applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p).denote
          (primitiveGateOperator :
            PrimitiveGate p.ancillaWidth p.systemWidth →
              Operator (JointBasis p.ancillaWidth p.systemWidth)) =
        q3ColumnOracleRecordedOperator p := by
    rw [← OracleCanonicalTotalProgram.columnExactOperatorComponent_circuit p]
    calc
      _ = (OracleCanonicalTotalProgram.columnExactOperatorComponent p).target :=
        (OracleCanonicalTotalProgram.columnExactOperatorComponent p).correct
      _ = q3ColumnOracleRecordedOperator p := by
        change ((OracleCanonicalTotalProgram.columnChildren p).fullExactOperatorComponent p).target =
          (OracleCanonicalTotalProgram.columnChildren p).fullAnalyticOperator p
        exact TotalOracleStageChildren.fullExactOperatorComponent_target
          p (OracleCanonicalTotalProgram.columnChildren p)
  have amplitudeSignCorrect :
      (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).denote
          (primitiveGateOperator :
            PrimitiveGate p.ancillaWidth p.systemWidth →
              Operator (JointBasis p.ancillaWidth p.systemWidth)) =
        amplitudeSignFullAnalyticOperator p := by
    calc
      _ = (activeCopyNegativePhaseExactOperatorComponent p).target :=
        (activeCopyNegativePhaseExactOperatorComponent p).correct
      _ = ActiveCopyNegativePhaseTargetOperator p := rfl
      _ = amplitudeSignFullAnalyticOperator p :=
        ActiveCopyNegativePhaseTargetOperator_eq_fullAnalytic p
  have outputAlignmentCorrect :
      (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p).denote
          (primitiveGateOperator :
            PrimitiveGate p.ancillaWidth p.systemWidth →
              Operator (JointBasis p.ancillaWidth p.systemWidth)) =
        outputAlignmentFullAnalyticOperator p := by
    calc
      _ = (controlledOracleOutputAlignmentExactOperatorComponent p).target :=
        (controlledOracleOutputAlignmentExactOperatorComponent p).correct
      _ = ControlledOracleOutputAlignmentTargetOperator p := rfl
      _ = outputAlignmentFullAnalyticOperator p :=
        ControlledOracleOutputAlignmentTargetOperator_eq_fullAnalytic p
  have columnUniformStateCorrect :
      applyOperator
          (Circuit.denote primitiveGateOperator
            (prepareUniformColumnSelectorCircuit p))
          (basisKet (zeroAncillaJointBasis p system)) =
        qColumnPreparedState p system := by
    exact prepareUniformColumnSelectorCircuit_systemBasis_correct_sharedCore
      p system
  simp [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul]
  rw [← prepareUniformColumnSelectorFullExactOperatorComponent_target p,
    ← (prepareUniformColumnSelectorFullExactOperatorComponent p).correct]
  rw [← xorSystemIntoColumnKey_correct]
  rw [← columnOracleCorrect]
  rw [← amplitudeSignCorrect]
  rw [← outputAlignmentCorrect]
  rw [prepareUniformColumnSelectorFullExactOperatorComponent_circuit]
  calc
    _ = applyOperator
          (Circuit.denote primitiveGateOperator
            (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p))
          (applyOperator
            (Circuit.denote primitiveGateOperator
              (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p))
            (applyOperator
              (Circuit.denote primitiveGateOperator
                (applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p))
              (applyOperator
                (Circuit.denote primitiveGateOperator
                  (xorSystemIntoColumnKeyPrimitiveCircuit p))
                (qColumnPreparedState p system)))) := by
      exact congrArg
        (fun state =>
          applyOperator
            (Circuit.denote primitiveGateOperator
              (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p))
            (applyOperator
              (Circuit.denote primitiveGateOperator
                (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p))
              (applyOperator
                (Circuit.denote primitiveGateOperator
                  (applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p))
                (applyOperator
                  (Circuit.denote primitiveGateOperator
                    (xorSystemIntoColumnKeyPrimitiveCircuit p)) state))))
        columnUniformStateCorrect
    _ = qAfterAlignState p system := by
      rw [xorSystemIntoColumnKeyPrimitiveCircuit_applyOperator]
      rw [applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit_applyOperator]
      rw [copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_applyOperator_eq]
      rw [controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_applyOperator]
      rfl

/-- Q5 support already has restored work and an active column selector; only
the active-row part remains to establish the full aligned predicate. -/
theorem qAfterAlignState_supported_on_columnOracleClean
    (p : QParameters) (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (q10ColumnOracleCleanPredicate p)
      (qAfterAlignState p system) := by
  have supported := BasisPredicateTransitionSpecification.applyOperator_supported
    (q10OutputAlignment_preserves_columnOracleClean p)
      (q10SourceBasisAfterAmplitudeSign_supported p system)
  rw [← q10SourceBasisAfterOutputAlignment_eq_qAfterAlignState]
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul, Matrix.mul_assoc] using supported

/-- Read the Q system register of an arbitrary joint basis. -/
def q10SystemBasis (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    RegisterBasis p.systemWidth :=
  systemPart input

theorem readWires_system_eq_registerBitList_q10SystemBasis
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    ReversibleCircuit.readWires (systemWires p) input =
      registerBitList (q10SystemBasis p input) := by
  simp [ReversibleCircuit.readWires, systemWires, registerBitList,
    q10SystemBasis, systemPart, QLayout.systemWire]

/-- Canonical row input contract from the active-selector clean sector. -/
theorem q10RowOracleInputSpec
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10RowOracleCleanPredicate p input)
    (configuration : QConfiguration p)
    (decoded : decodeDelimiter (q10SystemBasis p input) =
      some configuration) :
    RowOracleInputSpec p configuration
      ⟨qOracleSelectorValue p.selectorWidth
        (q10ProjectRegisterBasis (q10RowSelectorWire p) input), clean.2⟩ input where
  system_bits := by
    rw [readWires_system_eq_registerBitList_q10SystemBasis]
    rw [(decodeDelimiter_eq_some_iff.mp decoded)]
  selector_bits := by
    rw [rowSelectorWires_eq_selectorSliceWires]
    have bits := (readWires_selectorSlice_eq_constantBits_iff p
      (rowSelectorWire p) input _
      (qSelector_lt_capacity p
        ⟨qOracleSelectorValue p.selectorWidth
          (q10ProjectRegisterBasis (q10RowSelectorWire p) input), clean.2⟩)).2
        (by simpa using (q10RowSelectorObservation_eq_legacy p input).symm)
    simpa [selectorSliceWires] using bits
  work_zero := by
    simpa [diagonalOracleWorkWires, q10GeneratorWorkCleanPredicate,
      q10RegisterSliceWires_eq_wireList]
      using clean.1

/-- Illegal-delimiter row input contract from the same clean sector. -/
theorem q10RowOracleIllegalInputSpec
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10RowOracleCleanPredicate p input) :
    RowOracleIllegalInputSpec p (q10SystemBasis p input)
      ⟨qOracleSelectorValue p.selectorWidth
        (q10ProjectRegisterBasis (q10RowSelectorWire p) input), clean.2⟩ input where
  system_bits := readWires_system_eq_registerBitList_q10SystemBasis p input
  selector_bits := by
    rw [rowSelectorWires_eq_selectorSliceWires]
    have bits := (readWires_selectorSlice_eq_constantBits_iff p
      (rowSelectorWire p) input _
      (qSelector_lt_capacity p
        ⟨qOracleSelectorValue p.selectorWidth
          (q10ProjectRegisterBasis (q10RowSelectorWire p) input), clean.2⟩)).2
        (by simpa using (q10RowSelectorObservation_eq_legacy p input).symm)
    simpa [selectorSliceWires] using bits
  work_zero := by
    simpa [diagonalOracleWorkWires, q10GeneratorWorkCleanPredicate,
      q10RegisterSliceWires_eq_wireList]
      using clean.1

/-- Q7 preserves the work-clean active-row-selector sector for both legal and
illegal system words. -/
theorem q10RowReference_preserves_clean
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10RowOracleCleanPredicate p input) :
    q10RowOracleCleanPredicate p
      (OracleCanonicalTotalProgram.rowReference p input) := by
  let selector : QSelector p :=
    ⟨qOracleSelectorValue p.selectorWidth
      (q10ProjectRegisterBasis (q10RowSelectorWire p) input), clean.2⟩
  cases decoded : decodeDelimiter (q10SystemBasis p input) with
  | none =>
      have identity := applyRowOracleReferenceAndRestoreWorkCircuit_illegal_identity
        p (q10SystemBasis p input) selector input
          (q10RowOracleIllegalInputSpec p input clean) decoded
      rw [rowReference_eq_runBasis, identity]
      exact clean
  | some configuration =>
      let specification := q10RowOracleInputSpec p input clean
        configuration decoded
      have result := q7CompiledRowOracle_clean_reference
        configuration selector input specification
      have preserved := result.preservesInputSpec specification
      rw [rowReference_eq_runBasis]
      constructor
      · simpa [q10GeneratorWorkCleanPredicate, diagonalOracleWorkWires,
          q10RegisterSliceWires_eq_wireList]
          using preserved.work_zero
      · have selectorBits := preserved.selector_bits
        rw [rowSelectorWires_eq_selectorSliceWires] at selectorBits
        have selectorBits' : ReversibleCircuit.readWires
            (selectorSliceWires p (rowSelectorWire p))
            ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
              reversibleGatePermutation input) =
            constantBits selector.val p.selectorWidth := by
          simpa [selectorSliceWires] using selectorBits
        have valueEq := (readWires_selectorSlice_eq_constantBits_iff p
          (rowSelectorWire p)
          ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
            reversibleGatePermutation input)
          selector.val (qSelector_lt_capacity p selector)).mp selectorBits'
        unfold q10RowSelectorActivePredicate
        rw [q10RowSelectorObservation_eq_legacy, valueEq]
        exact selector.isLt

/-- The active clean Q7 permutation is also an involution, including legal
accepted, legal rejected, and illegal system encodings. -/
theorem q10RowReference_involutive_of_clean
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : q10RowOracleCleanPredicate p input) :
    OracleCanonicalTotalProgram.rowReference p
        (OracleCanonicalTotalProgram.rowReference p input) = input := by
  let selector : QSelector p :=
    ⟨qOracleSelectorValue p.selectorWidth
      (q10ProjectRegisterBasis (q10RowSelectorWire p) input), clean.2⟩
  have actualTwice :
      (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
          reversibleGatePermutation
          ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
            reversibleGatePermutation input) = input := by
    cases decoded : decodeDelimiter (q10SystemBasis p input) with
    | none =>
        have identity :=
          applyRowOracleReferenceAndRestoreWorkCircuit_illegal_identity
            p (q10SystemBasis p input) selector input
              (q10RowOracleIllegalInputSpec p input clean) decoded
        simp [identity]
    | some configuration =>
        let specification := q10RowOracleInputSpec p input clean
          configuration decoded
        cases referenceSome : rowReference configuration selector with
        | none =>
            have identity :=
              applyRowOracleReferenceAndRestoreWorkCircuit_reference_none
                configuration selector input specification referenceSome
            simp [identity]
        | some reference =>
            exact
              applyRowOracleReferenceAndRestoreWorkCircuit_reference_some_involutive_actual
                configuration selector reference input specification
                  referenceSome
  rw [rowReference_eq_runBasis p input]
  rw [rowReference_eq_runBasis p
    ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
      reversibleGatePermutation input)]
  exact actualTwice

/-- Matrix-support form of active-selector Q7 restoration. -/
theorem q10RowOracle_activeSelector_transition (p : QParameters) :
    BasisPredicateTransitionSpecification
      (q7RowOracleRecordedOperator p)
      (q10RowOracleCleanPredicate p)
      (q10RowOracleCleanPredicate p) := by
  intro input output inputClean outputDirty
  rw [q7RowOracleRecordedOperator_eq_deterministicReference]
  rw [deterministicOperator_apply]
  split
  · rename_i equal
    exfalso
    apply outputDirty
    rw [equal]
    exact q10RowReference_preserves_clean p input inputClean
  · rfl

/-- At Q7 the aligned boundary may forget the no-longer-needed active column
selector.  Work cleanliness and the active row selector are exactly Q7's
input/output contract. -/
theorem q10RowOracle_alignedToRowClean_transition (p : QParameters) :
    BasisPredicateTransitionSpecification
      (q7RowOracleRecordedOperator p)
      (q10AlignedOracleCleanPredicate p)
      (q10RowOracleCleanPredicate p) := by
  apply (q10RowOracle_activeSelector_transition p).restrictInput
  intro input aligned
  exact ⟨aligned.1.1, aligned.2⟩

/-! ## Source-reachable pipeline assembly -/

/-- Implementation-side normal form of the last two Q10 obligations.  The Q5
field refers to the established sparse state adapter, while the independent
pure boundary remains `Q10RemainingCleanPipelineObligations`. -/
structure Q10FinalSemanticObligations (p : QParameters) : Prop where
  beforeOutputAlignmentReady : ∀ system,
    StateSupportedOnBasisPredicate (Q10OutputAlignmentReady p)
      (q10SourceBasisAfterStage p 4 system)
  rowUniformInverse : BasisPredicateTransitionSpecification
    (Matrix.conjTranspose
      (sharedCoreRowUniformPreparationFullAnalyticOperator p))
    (q10RowOracleCleanPredicate p)
    (q10GeneratorWorkCleanPredicate p)

/-- After Q1--Q5 have been discharged, only the Q9 reverse-uniform clean
transition remains as an independent semantic input. -/
theorem Q10FinalSemanticObligations.ofRowUniformInverse
    {p : QParameters}
    (rowUniformInverse : BasisPredicateTransitionSpecification
      (Matrix.conjTranspose
        (sharedCoreRowUniformPreparationFullAnalyticOperator p))
      (q10RowOracleCleanPredicate p)
      (q10GeneratorWorkCleanPredicate p)) :
    Q10FinalSemanticObligations p where
  beforeOutputAlignmentReady :=
    q10SourceBasisAfterAmplitudeSign_ready p
  rowUniformInverse := rowUniformInverse

/-- Build the final two-obligation record from the established sparse Q5
state and an independent Q9 reverse-uniform transition theorem. -/
theorem Q10RemainingCleanPipelineObligations.ofAlignedStateSupport
    {p : QParameters}
    (aligned : ∀ system,
      StateSupportedOnBasisPredicate (q10AlignedOracleCleanPredicate p)
        (qAfterAlignState p system))
    (rowUniformInverse : BasisPredicateTransitionSpecification
      (Matrix.conjTranspose
        (sharedCoreRowUniformPreparationFullAnalyticOperator p))
      (q10RowOracleCleanPredicate p)
      (q10GeneratorWorkCleanPredicate p)) :
    Q10RemainingCleanPipelineObligations p where
  afterOutputAlignment := by
    intro system
    rw [q10SourceBasisAfterOutputAlignment_eq_qAfterAlignState]
    exact aligned system
  rowUniformInverse := rowUniformInverse

/-- Q5 maps the source-reachable Q3/Q4 relation to the complete aligned
support boundary. -/
theorem q10SourceBasisAfterOutputAlignment_supported_of_ready
    (p : QParameters)
    (ready : ∀ system,
      StateSupportedOnBasisPredicate (Q10OutputAlignmentReady p)
        (q10SourceBasisAfterStage p 4 system))
    (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (q10AlignedOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 5 system) := by
  have supported :=
    (q10OutputAlignment_ready_transition p).applyOperator_supported
      (ready system)
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul, Matrix.mul_assoc] using supported

/-- The minimal adapter obligations imply the two independent pure remaining
obligations.  Q5 itself is discharged by its mathematical alignment
specification, rather than being accepted as a whole-state premise. -/
theorem Q10RemainingCleanPipelineObligations.ofFinalSemantic
    {p : QParameters} (final : Q10FinalSemanticObligations p) :
    Q10RemainingCleanPipelineObligations p where
  afterOutputAlignment :=
    q10SourceBasisAfterOutputAlignment_supported_of_ready p
      final.beforeOutputAlignmentReady
  rowUniformInverse := final.rowUniformInverse

/-- Q1--Q6 prefix support, assuming only the source-reachable Q5 alignment
obligation. -/
theorem q10SourceBasisAfterColumnOracleInverse_supported
    (p : QParameters)
    (alignment : ∀ system,
      StateSupportedOnBasisPredicate (q10AlignedOracleCleanPredicate p)
        (q10SourceBasisAfterStage p 5 system))
    (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (q10AlignedOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 6 system) := by
  have supported :=
    BasisPredicateTransitionSpecification.applyOperator_supported
      (q10ColumnOracleInverse_preserves_alignedClean p) (alignment system)
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul, Matrix.mul_assoc] using supported

/-- Q1--Q7 prefix support. -/
theorem q10SourceBasisAfterRowOracle_supported
    (p : QParameters)
    (alignment : ∀ system,
      StateSupportedOnBasisPredicate (q10AlignedOracleCleanPredicate p)
        (q10SourceBasisAfterStage p 5 system))
    (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (q10RowOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 7 system) := by
  have supported :=
    (q10RowOracle_alignedToRowClean_transition p).applyOperator_supported
      (q10SourceBasisAfterColumnOracleInverse_supported p alignment system)
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul, Matrix.mul_assoc] using supported

/-- Q1--Q8 prefix support. -/
theorem q10SourceBasisBeforeRowUniformInverse_supported
    (p : QParameters)
    (alignment : ∀ system,
      StateSupportedOnBasisPredicate (q10AlignedOracleCleanPredicate p)
        (q10SourceBasisAfterStage p 5 system))
    (system : RegisterBasis p.systemWidth) :
    StateSupportedOnBasisPredicate (q10RowOracleCleanPredicate p)
      (q10SourceBasisAfterStage p 8 system) := by
  have supported :=
    BasisPredicateTransitionSpecification.applyOperator_supported
      (q10AmplitudeSignalFlip_preserves_rowOracleClean p)
      (q10SourceBasisAfterRowOracle_supported p alignment system)
  simpa [q10SourceBasisAfterStage, q10ProbabilityGeneratorSourceOperators,
    operatorSequence, applyOperator_mul, Matrix.mul_assoc] using supported

/-- All seven already discharged prefix fields and the two explicit
remaining obligations assemble the preferred source-reachable Q10 ledger. -/
theorem Q10SourceBasisCleanPipelineEvidence.ofRemaining
    {p : QParameters}
    (remaining : Q10RemainingCleanPipelineObligations p) :
    Q10SourceBasisCleanPipelineEvidence p where
  afterColumnUniform := q10SourceBasisAfterColumnUniform_supported p
  afterSystemToColumnKey :=
    q10SourceBasisAfterSystemToColumnKey_supported p
  afterColumnOracle := q10SourceBasisAfterColumnOracle_supported p
  afterAmplitudeSign := q10SourceBasisAfterAmplitudeSign_supported p
  afterOutputAlignment := remaining.afterOutputAlignment
  afterColumnOracleInverse :=
    q10SourceBasisAfterColumnOracleInverse_supported p
      remaining.afterOutputAlignment
  afterRowOracle := q10SourceBasisAfterRowOracle_supported p
    remaining.afterOutputAlignment
  afterAmplitudeSignalFlip :=
    q10SourceBasisBeforeRowUniformInverse_supported p
      remaining.afterOutputAlignment
  afterRowUniformInverse := by
    intro system
    have supported := remaining.rowUniformInverse.applyOperator_supported
      (q10SourceBasisBeforeRowUniformInverse_supported p
        remaining.afterOutputAlignment system)
    simpa [q10SourceBasisAfterStage,
      q10ProbabilityGeneratorRecordedOperator,
      q10ProbabilityGeneratorSourceOperators, operatorSequence,
      applyOperator_mul, Matrix.mul_assoc] using supported

/-- The source-reachable nine-stage clean ledger for the actual Q10 operator.
All obligations are discharged from the independently stated Q1--Q9
transitions; no block-encoding conclusion or representative parameter value
is used. -/
theorem q10SourceBasisCleanPipelineEvidence (p : QParameters) :
    Q10SourceBasisCleanPipelineEvidence p :=
  Q10SourceBasisCleanPipelineEvidence.ofRemaining
    (Q10RemainingCleanPipelineObligations.ofFinalSemantic
      (Q10FinalSemanticObligations.ofRowUniformInverse
        (q10RowUniformInverse_rowCleanToWorkClean_transition p)))

/-- The complete Q10 recorded operator maps the all-zero ancilla sector into
the internal-work-clean sector for every well-formed positive `q,K`. -/
theorem q10ProbabilityGenerator_allZeroToWorkClean (p : QParameters) :
    Q10AllZeroAncillaToWorkCleanSpecification p :=
  (q10SourceBasisCleanPipelineEvidence p).toSpecification

/-- Preferred coherent Q10 component with no caller-supplied semantic
premise.  Its proof follows the actual source-reachable prefix states and
keeps the signal output unrestricted. -/
def probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
    (p : QParameters) :
    SubspaceMapComponent (primitiveGateOperator
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  let child := probabilityGeneratorFullExactOperatorComponent p
  SubspaceMapComponent.ofBasisSpan
    (primitiveGateOperator
      (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth))
    child.circuit
    (q10ProbabilityGeneratorRecordedOperator p)
    (q11AllZeroAncillaInputPredicate p)
    (q10GeneratorWorkCleanPredicate p)
    (by
      intro input _inputClean
      have targetEq : child.target = q10ProbabilityGeneratorRecordedOperator p :=
        (probabilityGeneratorFullExactOperatorComponent_target p).trans
          (q10ProbabilityGeneratorRecordedOperator_eq_established p).symm
      rw [child.correct, targetEq])
    (by
      intro input inputClean
      apply SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_entry_support
      intro output outputDirty
      exact q10ProbabilityGenerator_allZeroToWorkClean p
        input output inputClean outputDirty)

@[simp] theorem
    probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified_circuit
    (p : QParameters) :
    (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
      p).circuit =
      (probabilityGeneratorFullExactOperatorComponent p).circuit := by
  rfl

@[simp] theorem
    probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified_target
    (p : QParameters) :
    (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
      p).target = q10ProbabilityGeneratorRecordedOperator p := by
  rfl

theorem
    probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified_spaces
    (p : QParameters) :
    (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
        p).inputSubspace =
        SubspaceMapComponent.basisSpan
          (q11AllZeroAncillaInputPredicate p) ∧
      (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
        p).outputSubspace =
        SubspaceMapComponent.basisSpan
          (q10GeneratorWorkCleanPredicate p) := by
  constructor <;> rfl

/-- Named coherent target-map boundary for the verified full-space Q10 clean
component.  This is a public projection of the component contract, so later
catalog layers need not unfold the component constructor. -/
theorem
    probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified_target_maps
    (p : QParameters)
    (state : State (JointBasis p.ancillaWidth p.systemWidth))
    (inside : state ∈
      (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
        p).inputSubspace) :
    applyOperator
        (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
          p).target state ∈
      (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
        p).outputSubspace := by
  exact
    (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
      p).target_maps state inside

/-- Named actual-circuit map boundary paired with the full-space Q10 target
map above. -/
theorem
    probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified_actual_maps
    (p : QParameters)
    (state : State (JointBasis p.ancillaWidth p.systemWidth))
    (inside : state ∈
      (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
        p).inputSubspace) :
    applyOperator
        ((probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
          p).circuit.denote
            (primitiveGateOperator
              (ancillaQubits := p.ancillaWidth)
              (systemQubits := p.systemWidth))) state ∈
      (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
        p).outputSubspace := by
  exact
    (probabilityGeneratorFullAllZeroToWorkCleanSubspaceMapComponentVerified
      p).actual_maps state inside

/-! ## Canonical-core Q10 boundary for the H2 controlled placement -/

/-- All-zero Q ancilla predicate after the canonical JointBasis-to-Fin
renaming used by the shared controlled-subcircuit compiler. -/
def q10CanonicalCoreAllZeroInputPredicate (p : QParameters)
    (basis : VerifiedCircuitCore.QubitBasis
      (p.ancillaWidth + p.systemWidth)) : Prop :=
  q11AllZeroAncillaInputPredicate p
    ((jointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm basis)

/-- Restored Q internal-work predicate in canonical core wire order. -/
def q10CanonicalCoreWorkCleanPredicate (p : QParameters)
    (basis : VerifiedCircuitCore.QubitBasis
      (p.ancillaWidth + p.systemWidth)) : Prop :=
  q10GeneratorWorkCleanPredicate p
    ((jointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm basis)

/-- The source-reachable Q10 transition transported to the canonical core
basis.  This is the exact source component consumed by H2 before its wire
placement and external-control lift. -/
theorem q10CanonicalCore_allZeroToWorkClean_transition (p : QParameters) :
    BasisPredicateTransitionSpecification
      (reindexJointOperatorToCanonicalCore
        (q10ProbabilityGeneratorRecordedOperator p))
      (q10CanonicalCoreAllZeroInputPredicate p)
      (q10CanonicalCoreWorkCleanPredicate p) := by
  have source : BasisPredicateTransitionSpecification
      (q10ProbabilityGeneratorRecordedOperator p)
      (q11AllZeroAncillaInputPredicate p)
      (q10GeneratorWorkCleanPredicate p) :=
    q10ProbabilityGenerator_allZeroToWorkClean p
  change BasisPredicateTransitionSpecification
    (reindexJointOperatorToCanonicalCore
      (q10ProbabilityGeneratorRecordedOperator p))
    (q11AllZeroAncillaInputPredicate p ∘
      (jointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm)
    (q10GeneratorWorkCleanPredicate p ∘
      (jointBasisCoreEquiv p.ancillaWidth p.systemWidth).symm)
  simpa [reindexJointOperatorToCanonicalCore] using
    source.reindex (jointBasisCoreEquiv p.ancillaWidth p.systemWidth)

theorem q10CanonicalCoreAllZeroInputPredicate_implies_workClean
    (p : QParameters) (basis : VerifiedCircuitCore.QubitBasis
      (p.ancillaWidth + p.systemWidth)) :
    q10CanonicalCoreAllZeroInputPredicate p basis →
      q10CanonicalCoreWorkCleanPredicate p basis := by
  intro inputZero
  exact inputZero.2

/-- Canonical-core coherent Q10 component with the asymmetric all-zero-input
to work-clean-output boundary. -/
def probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
    (p : QParameters) :
    SubspaceMapComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := p.ancillaWidth + p.systemWidth) internalZeroSymbolEnvironment) :=
  let child := probabilityGeneratorCanonicalCoreExactOperatorComponent p
  let cleanTarget := reindexJointOperatorToCanonicalCore
    (q10ProbabilityGeneratorRecordedOperator p)
  SubspaceMapComponent.ofBasisSpan
    (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
      (qubits := p.ancillaWidth + p.systemWidth) internalZeroSymbolEnvironment)
    child.circuit cleanTarget
    (q10CanonicalCoreAllZeroInputPredicate p)
    (q10CanonicalCoreWorkCleanPredicate p)
    (by
      intro input _inputClean
      have targetEq : child.target = cleanTarget :=
        congrArg reindexJointOperatorToCanonicalCore
          (q10ProbabilityGeneratorRecordedOperator_eq_established p).symm
      rw [child.correct, targetEq])
    (by
      intro input inputClean
      apply SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_entry_support
      intro output outputDirty
      exact q10CanonicalCore_allZeroToWorkClean_transition p
        input output inputClean outputDirty)

@[simp] theorem
    probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent_circuit
    (p : QParameters) :
    (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
      p).circuit =
      (probabilityGeneratorCanonicalCoreExactOperatorComponent p).circuit := by
  rfl

@[simp] theorem
    probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent_target
    (p : QParameters) :
    (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
      p).target =
      reindexJointOperatorToCanonicalCore
        (q10ProbabilityGeneratorRecordedOperator p) := by
  rfl

theorem
    probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent_spaces
    (p : QParameters) :
    (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
        p).inputSubspace =
        SubspaceMapComponent.basisSpan
          (q10CanonicalCoreAllZeroInputPredicate p) ∧
      (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
        p).outputSubspace =
        SubspaceMapComponent.basisSpan
          (q10CanonicalCoreWorkCleanPredicate p) := by
  constructor <;> rfl

/-- Named coherent target-map boundary in canonical core wire order. -/
theorem
    probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent_target_maps
    (p : QParameters)
    (state : State (VerifiedCircuitCore.QubitBasis
      (p.ancillaWidth + p.systemWidth)))
    (inside : state ∈
      (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
        p).inputSubspace) :
    applyOperator
        (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
          p).target state ∈
      (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
        p).outputSubspace := by
  exact
    (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
      p).target_maps state inside

/-- Named actual-circuit map boundary in canonical core wire order. -/
theorem
    probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent_actual_maps
    (p : QParameters)
    (state : State (VerifiedCircuitCore.QubitBasis
      (p.ancillaWidth + p.systemWidth)))
    (inside : state ∈
      (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
        p).inputSubspace) :
    applyOperator
        ((probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
          p).circuit.denote
            (VerifiedCircuitCore.primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)) state ∈
      (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
        p).outputSubspace := by
  exact
    (probabilityGeneratorCanonicalCoreAllZeroToWorkCleanSubspaceMapComponent
      p).actual_maps state inside

end

end ProbabilityGeneratorQProof
