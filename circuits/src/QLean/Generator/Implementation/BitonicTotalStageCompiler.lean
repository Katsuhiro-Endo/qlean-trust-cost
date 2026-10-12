import QLean.Generator.Analysis.BitonicTotalStage
import QLean.Generator.Implementation.BitonicSortLayout
import QLean.Generator.Implementation.BitonicSortCorrectness
import QLean.Generator.Implementation.PrimitiveCoreSemanticsAdapter
import QLean.Generator.Implementation.ReversibleLogicSharedCoreAdapter
import QLean.Generator.Implementation.TotalReversibleProgramsCompiler

/-!
# Shared bitonic schedule adapter and frozen compiler transport

The layout-independent schedule is the shared core schedule.  Only the Q wire
layout and the frozen compare--exchange compiler remain in this module.
-/

namespace ProbabilityGeneratorQProof

namespace BitonicTotalProgram

/-- The implementation and pure analytic canonical basis equivalences are the
same bit layout. -/
theorem jointBasisCoreEquiv_eq_analyticJointBasisCoreEquiv
    (ancillaQubits systemQubits : Nat) :
    jointBasisCoreEquiv ancillaQubits systemQubits =
      analyticJointBasisCoreEquiv ancillaQubits systemQubits := by
  apply Equiv.ext
  intro input
  funext index
  simp [jointBasisCoreEquiv, jointBasisToCore, analyticJointBasisCoreEquiv,
    canonicalFinToWire, analyticCanonicalFinToWire]

theorem candidateWordAt_implementation_eq (p : QParameters)
    (word : Fin p.sortWordCount) :
    OracleEventTotalProgram.candidateWordAt p word =
      ProbabilityGeneratorQProof.candidateWordAt p word := rfl

/-- A candidate word as a validated fixed-width Q register. -/
def candidateValidatedRegister (p : QParameters)
    (word : Fin p.sortWordCount) :
    ValidatedQRegister p.ancillaWidth p.systemWidth (p.wordWidth + 1) where
  wire := candidateWordWire p word
  injective := by
    intro left right equal
    have pairEqual : (word, left) = (word, right) := by
      apply ReversibleCircuit.sortCandidateWordWire_pair_injective p
      exact equal
    exact congrArg Prod.snd pairEqual

/-- The swap portion of one bitonic instruction satisfies the shared strict layout. -/
def controlledSwapValidatedLayout (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (different : instruction.left ≠ instruction.right) :
    ValidatedControlledRegisterSwapLayout p.ancillaWidth p.systemWidth
      (p.wordWidth + 1) where
  control :=
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).sortFlags).ancillaWire
      instruction.history
  left := candidateValidatedRegister p instruction.left
  right := candidateValidatedRegister p instruction.right
  leftRightDisjoint := by
    intro leftIndex rightIndex equal
    have pairEqual : (instruction.left, leftIndex) =
        (instruction.right, rightIndex) := by
      apply ReversibleCircuit.sortCandidateWordWire_pair_injective p
      exact equal
    exact different (congrArg Prod.fst pairEqual)
  controlLeftDifferent := by
    intro index equal
    exact ReversibleCircuit.sortHistoryWire_not_mem_candidate
      p instruction.history instruction.left <| by
      rw [candidateWordAt]
      apply List.mem_map.mpr
      exact ⟨index, List.mem_finRange _, equal.symm⟩
  controlRightDifferent := by
    intro index equal
    exact ReversibleCircuit.sortHistoryWire_not_mem_candidate
      p instruction.history instruction.right <| by
      rw [candidateWordAt]
      apply List.mem_map.mpr
      exact ⟨index, List.mem_finRange _, equal.symm⟩

/-- The comparison child transported from Q `JointBasis` to canonical core basis. -/
noncomputable def comparisonCanonicalCoreExactComponent (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :=
  reindexJointExactOperatorComponentToCanonicalCore
    ((comparisonStage p instruction).primitiveExactOperatorComponent)

theorem comparisonCanonicalCoreExactComponent_circuit (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    (comparisonCanonicalCoreExactComponent p instruction).circuit =
      compileReversibleCircuitToCanonicalCore
        (comparisonStage p instruction).compile := by
  unfold comparisonCanonicalCoreExactComponent
    reindexJointExactOperatorComponentToCanonicalCore
    TotalReversibleStage.primitiveExactOperatorComponent
  change
    (((comparisonStage p instruction).permutationComponent.circuit.mapGates
      ReversibleGate.toPrimitive).mapGates PrimitiveGate.toCanonicalCore) =
      compileReversibleCircuitToCanonicalCore
        (comparisonStage p instruction).compile
  rw [VerifiedCircuitCore.Circuit.mapGates_mapGates,
    primitiveGateToCanonicalCore_comp_toPrimitive]
  unfold compileReversibleCircuitToCanonicalCore
  rw [(comparisonStage p instruction).permutationComponent_circuit]

/-- The comparison child's target is the independently defined pure Q stage
operator, transported to canonical core basis. -/
theorem comparisonCanonicalCoreExactComponent_target_independent (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    (comparisonCanonicalCoreExactComponent p instruction).target =
      Matrix.reindex (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)
        (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)
        (comparisonStage p instruction).analyticOperator := by
  change reindexJointOperatorToCanonicalCore
      (comparisonStage p instruction).primitiveExactOperatorComponent.target = _
  rw [TotalReversibleStage.primitiveExactOperatorComponent_target]
  unfold reindexJointOperatorToCanonicalCore
  rw [jointBasisCoreEquiv_eq_analyticJointBasisCoreEquiv]

/-- The swap child is the shared controlled-register-swap component at the Q layout. -/
noncomputable def controlledSwapCanonicalCoreExactComponent (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (different : instruction.left ≠ instruction.right) :=
  validatedSwapRegistersWhenControlFrozenCompilerExactComponent internalZeroSymbolEnvironment
    (controlledSwapValidatedLayout p instruction different)

theorem controlledSwapCanonicalCoreExactComponent_circuit (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (different : instruction.left ≠ instruction.right) :
    (controlledSwapCanonicalCoreExactComponent p instruction different).circuit =
      compileReversibleCircuitToCanonicalCore
        (ReversibleCircuit.controlledSwapWord
          ((QLayout.oracleSlice
            (OracleWorkLayout.canonical p).sortFlags).ancillaWire
              instruction.history)
          (candidateWordAt p instruction.left)
          (candidateWordAt p instruction.right)) := by
  rfl

/-- The shared swap child's target is the independently defined Q pure stage
operator transported to canonical core basis. -/
theorem controlledSwapCanonicalCoreExactComponent_target_independent
    (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (different : instruction.left ≠ instruction.right) :
    (controlledSwapCanonicalCoreExactComponent p instruction different).target =
      Matrix.reindex (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)
        (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)
        (controlledSwapStage p instruction).analyticOperator := by
  change VerifiedCircuitCore.controlledRegisterSwapPureOperator
      (controlledSwapValidatedLayout p instruction different).toCore = _
  rw [TotalReversibleStage.reindex_analyticOperator_eq_toCore]
  rw [show (controlledSwapStage p instruction).toCore =
      TotalReversibleStage.controlledSwapWordCore
        (controlledSwapValidatedLayout p instruction different).control
        (controlledSwapValidatedLayout p instruction different).left.wires
        (controlledSwapValidatedLayout p instruction different).right.wires by
    unfold controlledSwapStage
    rw [TotalReversibleStage.toCore_controlledSwapWord]
    rfl]
  exact (controlledSwapWordCore_analyticOperator_eq_pure
    (controlledSwapValidatedLayout p instruction different)).symm

/-- The two child targets compose to the independent pure compare--exchange
operator.  This proof uses only pure target transports and matrix reindexing. -/
theorem compareExchangeChildrenTarget_eq_independent (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (different : instruction.left ≠ instruction.right) :
    (controlledSwapCanonicalCoreExactComponent p instruction different).target *
        (comparisonCanonicalCoreExactComponent p instruction).target =
      compareExchangeCanonicalCoreAnalyticOperator p instruction := by
  rw [controlledSwapCanonicalCoreExactComponent_target_independent,
    comparisonCanonicalCoreExactComponent_target_independent]
  unfold compareExchangeCanonicalCoreAnalyticOperator
    compareExchangeAnalyticOperator compareExchange
  rw [TotalReversibleStage.analyticOperator_seq]
  exact ((Matrix.reindexRingEquiv ℂ
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)).map_mul
      (controlledSwapStage p instruction).analyticOperator
      (comparisonStage p instruction).analyticOperator).symm

/--
One compare--exchange implementation composed only from the comparison child and
the validated shared-core swap child.  The shared swap child's `correct` field is
used by `ExactOperatorComponent.seq`.
-/
noncomputable def compareExchangeCanonicalCoreExactComponent (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (different : instruction.left ≠ instruction.right) :
    VerifiedCircuitCore.ExactOperatorComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := p.ancillaWidth + p.systemWidth) internalZeroSymbolEnvironment) := by
  let composed := VerifiedCircuitCore.ExactOperatorComponent.seq
    (comparisonCanonicalCoreExactComponent p instruction)
    (controlledSwapCanonicalCoreExactComponent p instruction different)
  exact
    { circuit := composed.circuit
      target := compareExchangeCanonicalCoreAnalyticOperator p instruction
      correct := composed.correct.trans
        (compareExchangeChildrenTarget_eq_independent p instruction different) }

theorem compareExchangeCanonicalCoreExactComponent_circuit (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (different : instruction.left ≠ instruction.right) :
    (compareExchangeCanonicalCoreExactComponent p instruction different).circuit =
      compileReversibleCircuitToCanonicalCore
        (compareExchange p instruction).compile := by
  change VerifiedCircuitCore.Circuit.seq
      (comparisonCanonicalCoreExactComponent p instruction).circuit
      (controlledSwapCanonicalCoreExactComponent p instruction different).circuit =
    compileReversibleCircuitToCanonicalCore
      (compareExchange p instruction).compile
  rw [comparisonCanonicalCoreExactComponent_circuit,
    controlledSwapCanonicalCoreExactComponent_circuit]
  unfold compareExchange comparisonStage controlledSwapStage
  split <;>
    simp only [TotalReversibleStage.compile,
      TotalReversibleStage.compile_controlledSwapWord,
      compileReversibleCircuitToCanonicalCore,
      VerifiedCircuitCore.Circuit.mapGates,
      candidateWordAt_implementation_eq]

theorem compareExchangeCanonicalCoreExactComponent_target (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (different : instruction.left ≠ instruction.right) :
    (compareExchangeCanonicalCoreExactComponent p instruction different).target =
      compareExchangeCanonicalCoreAnalyticOperator p instruction := by
  rfl

/-- The Q schedule is definitionally the shared schedule used by the frozen compiler. -/
theorem qSchedule_eq (p : QParameters) :
    qSchedule p = qTypedBitonicSchedule p := rfl

/-- Every instruction selected by the shared Q schedule has distinct operands. -/
theorem qSchedule_left_ne_right (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth)
    (member : instruction ∈ qSchedule p) :
    instruction.left ≠ instruction.right := by
  rw [qSchedule_eq] at member
  exact ReversibleCircuit.qTypedBitonicSchedule_left_ne_right p instruction member

/-- The exact compare--exchange children indexed by the complete shared schedule. -/
noncomputable def compareExchangeCanonicalCoreExactComponents (p : QParameters) :=
  (qSchedule p).attach.map fun entry =>
    compareExchangeCanonicalCoreExactComponent p entry.1
      (qSchedule_left_ne_right p entry.1 entry.2)

/-- The child circuit list is exactly the frozen compare--exchange compilation. -/
theorem compareExchangeCanonicalCoreExactComponents_circuits (p : QParameters) :
    (compareExchangeCanonicalCoreExactComponents p).map
        (fun component => component.circuit) =
      (qSchedule p).map fun instruction =>
        compileReversibleCircuitToCanonicalCore
          (compareExchange p instruction).compile := by
  unfold compareExchangeCanonicalCoreExactComponents
  rw [List.map_map]
  trans (qSchedule p).attach.map fun entry =>
      compileReversibleCircuitToCanonicalCore
        (compareExchange p entry.1).compile
  · apply List.map_congr_left
    intro entry _
    exact compareExchangeCanonicalCoreExactComponent_circuit p entry.1
      (qSchedule_left_ne_right p entry.1 entry.2)
  · exact List.attach_map_val (l := qSchedule p)
      (f := fun instruction =>
        compileReversibleCircuitToCanonicalCore
          (compareExchange p instruction).compile)

/-- The child target list is exactly the schedule's independent pure
compare--exchange operator list. -/
theorem compareExchangeCanonicalCoreExactComponents_targets (p : QParameters) :
    (compareExchangeCanonicalCoreExactComponents p).map
        (fun component => component.target) =
      (qSchedule p).map (compareExchangeCanonicalCoreAnalyticOperator p) := by
  unfold compareExchangeCanonicalCoreExactComponents
  rw [List.map_map]
  trans (qSchedule p).attach.map fun entry =>
      compareExchangeCanonicalCoreAnalyticOperator p entry.1
  · apply List.map_congr_left
    intro entry _
    exact compareExchangeCanonicalCoreExactComponent_target p entry.1
      (qSchedule_left_ne_right p entry.1 entry.2)
  · exact List.attach_map_val (l := qSchedule p)
      (f := compareExchangeCanonicalCoreAnalyticOperator p)

/-- The finite child sequence target transports to the independent pure sort
operator by the shared monoid-homomorphism law. -/
theorem sortChildrenTarget_eq_independent (p : QParameters) :
    VerifiedCircuitCore.operatorSequence
        ((compareExchangeCanonicalCoreExactComponents p).map
          (fun component => component.target)) =
      sortCanonicalCoreAnalyticOperator p := by
  rw [compareExchangeCanonicalCoreExactComponents_targets]
  unfold sortCanonicalCoreAnalyticOperator
  rw [sortAnalyticOperator_eq_operatorSequence]
  let reindexHom := (Matrix.reindexRingEquiv ℂ
    (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)).toMonoidHom
  have mapped := VerifiedCircuitCore.MonoidHom.map_operatorSequence reindexHom
    ((qSchedule p).map (compareExchangeAnalyticOperator p))
  calc
    VerifiedCircuitCore.operatorSequence
        ((qSchedule p).map (compareExchangeCanonicalCoreAnalyticOperator p)) =
      VerifiedCircuitCore.operatorSequence
        (((qSchedule p).map (compareExchangeAnalyticOperator p)).map
          reindexHom) := by
            apply congrArg VerifiedCircuitCore.operatorSequence
            rw [List.map_map]
            apply List.map_congr_left
            intro instruction _
            rfl
    _ = reindexHom (VerifiedCircuitCore.operatorSequence
        ((qSchedule p).map (compareExchangeAnalyticOperator p))) := mapped.symm
    _ = Matrix.reindex
        (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)
        (analyticJointBasisCoreEquiv p.ancillaWidth p.systemWidth)
        (VerifiedCircuitCore.operatorSequence
          ((qSchedule p).map (compareExchangeAnalyticOperator p))) := rfl

/-- The complete shared schedule composed only through child exact contracts. -/
noncomputable def sortCanonicalCoreExactComponent (p : QParameters) :
    VerifiedCircuitCore.ExactOperatorComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := p.ancillaWidth + p.systemWidth) internalZeroSymbolEnvironment) := by
  let children := compareExchangeCanonicalCoreExactComponents p
  let composed := VerifiedCircuitCore.ExactOperatorComponent.sequenceComponents
    (VerifiedCircuitCore.primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment) children
  exact
    { circuit := composed.circuit
      target := sortCanonicalCoreAnalyticOperator p
      correct := composed.correct.trans
        ((VerifiedCircuitCore.ExactOperatorComponent.sequence_target_eq_operatorSequence
          children).trans (sortChildrenTarget_eq_independent p)) }

/-- The complete exact component preserves the frozen Q sort circuit. -/
theorem sortCanonicalCoreExactComponent_circuit (p : QParameters) :
    (sortCanonicalCoreExactComponent p).circuit =
      compileReversibleCircuitToCanonicalCore (sort p).compile := by
  unfold sortCanonicalCoreExactComponent
  rw [VerifiedCircuitCore.ExactOperatorComponent.sequenceComponents_circuit,
    compareExchangeCanonicalCoreExactComponents_circuits]
  unfold compileReversibleCircuitToCanonicalCore
  rw [sort, TotalReversibleStage.compile_sequence,
    VerifiedCircuitCore.Circuit.mapGates_sequence]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  simp only [List.map_map]
  apply List.map_congr_left
  intro instruction _
  rfl

/-- The public sort target is the independent pure sort operator. -/
theorem sortCanonicalCoreExactComponent_target (p : QParameters) :
    (sortCanonicalCoreExactComponent p).target =
      sortCanonicalCoreAnalyticOperator p := by
  rfl

/-- The pure candidate-word layout is the existing Q sort layout. -/
theorem candidateWordAt_eq (p : QParameters) (word : Fin p.sortWordCount) :
    OracleEventTotalProgram.candidateWordAt p word =
      ProbabilityGeneratorQProof.candidateWordAt p word := rfl

/-- The pure comparison-work layout is the existing Q sort layout. -/
theorem compareWorkWires_eq (p : QParameters) :
    compareWorkWires p = ProbabilityGeneratorQProof.sortCompareWorkWires p := rfl

/-- The pure AND-scratch layout is the existing Q sort layout. -/
theorem andScratchWires_eq (p : QParameters) :
    andScratchWires p = ProbabilityGeneratorQProof.sortAndScratchWires p := rfl

/-- One shared schedule instruction compiles to the frozen Q compare--exchange circuit. -/
theorem compile_compareExchange (p : QParameters)
    (instruction : TypedBitonicCompareExchange p.sortWordCount p.sortFlagWidth) :
    (compareExchange p instruction).compile =
      emitTypedBitonicCompareExchange (ProbabilityGeneratorQProof.candidateWordAt p)
        (ProbabilityGeneratorQProof.sortCompareWorkWires p)
        (ProbabilityGeneratorQProof.sortAndScratchWires p)
        ((QLayout.oracleSlice (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) instruction := by
  unfold compareExchange comparisonStage controlledSwapStage
    emitTypedBitonicCompareExchange
  split <;>
    simp_all [candidateWordAt_eq, compareWorkWires_eq, andScratchWires_eq,
      TotalReversibleStage.compile,
      TotalReversibleStage.compile_xorLessThanIntoTarget,
      TotalReversibleStage.compile_controlledSwapWord]

/-- The shared schedule instance preserves the complete frozen Q sort AST. -/
theorem compile_sort (p : QParameters) :
    (sort p).compile = reversiblySortCandidateWordsAndRestoreHistoryCircuit p := by
  rw [sort, TotalReversibleStage.compile_sequence,
    reversiblySortCandidateWordsAndRestoreHistoryCircuit, emitTypedBitonicSort,
    qSchedule_eq]
  apply congrArg VerifiedCircuitCore.Circuit.sequence
  rw [List.map_map]
  apply List.map_congr_left
  intro instruction _
  exact compile_compareExchange p instruction

/-- The full-basis permutation component for the Q bitonic sort stage. -/
def sortPermutationComponent (p : QParameters) :=
  (sort p).permutationComponent

end BitonicTotalProgram

end ProbabilityGeneratorQProof
