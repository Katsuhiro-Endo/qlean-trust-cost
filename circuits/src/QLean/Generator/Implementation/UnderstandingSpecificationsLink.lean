import QLean.Generator.Analysis.UnderstandingSpecifications
import QLean.Generator.Implementation.QVerifiedFullOracleComponents

/-!
# Actual clean-oracle links for the human-facing Q3/Q7 specifications

This implementation-side module exposes the already verified column and row
`CleanComponent`s without importing circuit vocabulary into the pure
`Analytic` specification.  In particular, it keeps four facts separate:

* the projected circuit is the recorded implementation circuit;
* the component input and output conditions are the physical clean contracts;
* the component reference satisfies the independent semantic accumulator
  action; and
* every non-output wire, hence every internal work wire, is restored.

The Q10 coherent-subspace assembly is intentionally a later checkpoint.  It
must not obscure whether the two oracle boundary links themselves are sound.
-/

namespace ProbabilityGeneratorQProof

open VerifiedCircuitCore

noncomputable section

/-! ## Q3: column oracle -/

/-- The Q3 clean component is a refinement of the actual
compute--branch-fold--uncompute child, with no replacement circuit. -/
@[simp] theorem q3ColumnOracleCleanComponent_circuit
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    (ReversibleCircuit.verifiedApplyColumnOracleReferenceAndRestoreWorkCleanComponent
      p configuration selector).circuit =
      applyColumnOracleReferenceAndRestoreWorkCircuit p := rfl

/-- The direct implementation child of Q3 has the same recorded circuit. -/
@[simp] theorem q3ColumnOracleCleanComponent_directChild_circuit
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    (ReversibleCircuit.verifiedApplyColumnOracleReferenceAndRestoreWorkCleanComponent
      p configuration selector).circuit =
    (ReversibleCircuit.verifiedColumnOraclePersistentComputeBranchFoldUncomputeCleanComponent
      p configuration selector).circuit := rfl

/-- Q3 accepts exactly the physical column-oracle clean predicate. -/
@[simp] theorem q3ColumnOracleCleanComponent_inputCondition
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    (ReversibleCircuit.verifiedApplyColumnOracleReferenceAndRestoreWorkCleanComponent
      p configuration selector).inputCondition =
      ReversibleCircuit.ColumnOracleInputSpec p configuration selector := rfl

/-- Q3 re-establishes the same clean predicate after using its work wires. -/
@[simp] theorem q3ColumnOracleCleanComponent_outputCondition
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    (ReversibleCircuit.verifiedApplyColumnOracleReferenceAndRestoreWorkCleanComponent
      p configuration selector).outputCondition =
      ReversibleCircuit.ColumnOracleInputSpec p configuration selector := rfl

/-- The refined reference of the actual Q3 component satisfies the canonical
observation-and-restoration specification. -/
theorem q3ColumnOracleCleanComponent_reference_spec
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ReversibleCircuit.ColumnOracleInputSpec
      p configuration selector input) :
    ReversibleCircuit.ColumnOracleRestoredReferenceSpec
      p configuration selector input
      ((ReversibleCircuit.verifiedApplyColumnOracleReferenceAndRestoreWorkCleanComponent
        p configuration selector).reference input) :=
  (ReversibleCircuit.verifiedApplyColumnOracleReferenceAndRestoreWorkCleanComponent
    p configuration selector).restoration_correct input clean

/-- The compiled Q3 circuit satisfies the established physical clean
reference, now obtained through the actual public `CleanComponent`. -/
theorem q3CompiledColumnOracle_clean_reference
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ReversibleCircuit.ColumnOracleInputSpec
      p configuration selector input) :
    ReversibleCircuit.ColumnOracleRestoredReferenceIdentification
      p configuration selector input
      ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input) := by
  let component :=
    ReversibleCircuit.verifiedApplyColumnOracleReferenceAndRestoreWorkCleanComponent
      p configuration selector
  change ReversibleCircuit.ColumnOracleRestoredReferenceIdentification
    p configuration selector input
      (component.circuit.runBasis reversibleGatePermutation input)
  rw [component.runBasis_correct input clean]
  exact (q3ColumnOracleCleanComponent_reference_spec
    configuration selector input clean).toPhysical

/-- The actual Q3 output again satisfies its complete input condition.  This
includes zero restoration of all temporary and persistent work wires. -/
theorem q3CompiledColumnOracle_clean_outputCondition
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ReversibleCircuit.ColumnOracleInputSpec
      p configuration selector input) :
    ReversibleCircuit.ColumnOracleInputSpec p configuration selector
      ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input) :=
  (q3CompiledColumnOracle_clean_reference
    configuration selector input clean).preservesInputSpec clean

/-- The Q3 observation is the independently reviewable semantic accumulator
action, while every non-output wire is restored. -/
theorem q3CompiledColumnOracle_clean_understanding_action
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ReversibleCircuit.ColumnOracleInputSpec
      p configuration selector input) :
    let output :=
      (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input
    ReversibleCircuit.observeColumnOracle p output =
        q3ColumnSemanticAccumulatorAction configuration selector
          (ReversibleCircuit.observeColumnOracle p input) ∧
      (∀ wire,
        wire ∉ rowOutputWires p →
        wire ∉ selectorOutputWires p →
        wire ≠ negativeWire p →
        wire ≠ activeWire p →
        output wire = input wire) := by
  dsimp only
  have restored := q3CompiledColumnOracle_clean_reference
    configuration selector input clean
  constructor
  · rw [q3ColumnSemanticAccumulatorAction_eq_established]
    exact restored.observation
  · exact restored.outside_restored

/-- The same implementation law with the diagonal/event split left visible. -/
theorem q3CompiledColumnOracle_clean_understanding_branches
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ReversibleCircuit.ColumnOracleInputSpec
      p configuration selector input) :
    let output :=
      (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input
    ReversibleCircuit.observeColumnOracle p output =
        q3ColumnBranchSemanticAccumulatorAction configuration selector
          (ReversibleCircuit.observeColumnOracle p input) ∧
      (∀ wire,
        wire ∉ rowOutputWires p →
        wire ∉ selectorOutputWires p →
        wire ≠ negativeWire p →
        wire ≠ activeWire p →
        output wire = input wire) := by
  have linked := q3CompiledColumnOracle_clean_understanding_action
    configuration selector input clean
  dsimp only at linked ⊢
  rw [q3ColumnSemanticAccumulatorAction_eq_branches] at linked
  exact linked

/-! ## Q7: row oracle -/

/-- The Q7 clean component projects to the actual recorded row-oracle
circuit. -/
@[simp] theorem q7RowOracleCleanComponent_circuit
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    (ReversibleCircuit.verifiedApplyRowOracleReferenceAndRestoreWorkCleanComponent
      p configuration selector).circuit =
      applyRowOracleReferenceAndRestoreWorkCircuit p := rfl

/-- The direct implementation child of Q7 has the same recorded circuit. -/
@[simp] theorem q7RowOracleCleanComponent_directChild_circuit
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    (ReversibleCircuit.verifiedApplyRowOracleReferenceAndRestoreWorkCleanComponent
      p configuration selector).circuit =
    (ReversibleCircuit.verifiedRowOraclePersistentComputeBranchFoldUncomputeCleanComponent
      p configuration selector).circuit := rfl

/-- Q7 accepts exactly the physical row-oracle clean predicate. -/
@[simp] theorem q7RowOracleCleanComponent_inputCondition
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    (ReversibleCircuit.verifiedApplyRowOracleReferenceAndRestoreWorkCleanComponent
      p configuration selector).inputCondition =
      ReversibleCircuit.RowOracleInputSpec p configuration selector := rfl

/-- Q7 re-establishes the same clean predicate after using its work wires. -/
@[simp] theorem q7RowOracleCleanComponent_outputCondition
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    (ReversibleCircuit.verifiedApplyRowOracleReferenceAndRestoreWorkCleanComponent
      p configuration selector).outputCondition =
      ReversibleCircuit.RowOracleInputSpec p configuration selector := rfl

/-- The refined reference of the actual Q7 component satisfies the canonical
observation-and-restoration specification. -/
theorem q7RowOracleCleanComponent_reference_spec
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ReversibleCircuit.RowOracleInputSpec
      p configuration selector input) :
    ReversibleCircuit.RowOracleRestoredReferenceSpec
      p configuration selector input
      ((ReversibleCircuit.verifiedApplyRowOracleReferenceAndRestoreWorkCleanComponent
        p configuration selector).reference input) :=
  (ReversibleCircuit.verifiedApplyRowOracleReferenceAndRestoreWorkCleanComponent
    p configuration selector).restoration_correct input clean

/-- The compiled Q7 circuit satisfies the established physical clean
reference, obtained through the actual public `CleanComponent`. -/
theorem q7CompiledRowOracle_clean_reference
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ReversibleCircuit.RowOracleInputSpec
      p configuration selector input) :
    ReversibleCircuit.RowOracleRestoredReferenceIdentification
      p configuration selector input
      ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input) := by
  let component :=
    ReversibleCircuit.verifiedApplyRowOracleReferenceAndRestoreWorkCleanComponent
      p configuration selector
  change ReversibleCircuit.RowOracleRestoredReferenceIdentification
    p configuration selector input
      (component.circuit.runBasis reversibleGatePermutation input)
  rw [component.runBasis_correct input clean]
  exact (q7RowOracleCleanComponent_reference_spec
    configuration selector input clean).toPhysical

/-- The actual Q7 output again satisfies its complete input condition. -/
theorem q7CompiledRowOracle_clean_outputCondition
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ReversibleCircuit.RowOracleInputSpec
      p configuration selector input) :
    ReversibleCircuit.RowOracleInputSpec p configuration selector
      ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input) :=
  (q7CompiledRowOracle_clean_reference
    configuration selector input clean).preservesInputSpec clean

/-- The Q7 observation is the independent predecessor accumulator action,
while every non-output wire is restored. -/
theorem q7CompiledRowOracle_clean_understanding_action
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ReversibleCircuit.RowOracleInputSpec
      p configuration selector input) :
    let output :=
      (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input
    ReversibleCircuit.observeRowOracle p output =
        q7RowSemanticAccumulatorAction configuration selector
          (ReversibleCircuit.observeRowOracle p input) ∧
      (∀ wire,
        wire ∉ columnKeyWires p →
        wire ∉ columnSelectorWires p →
        wire ≠ keySignalWire p →
        output wire = input wire) := by
  dsimp only
  have restored := q7CompiledRowOracle_clean_reference
    configuration selector input clean
  constructor
  · rw [q7RowSemanticAccumulatorAction_eq_established]
    exact restored.observation
  · exact restored.outside_restored

/-- The same implementation law with the diagonal/event predecessor split
left visible. -/
theorem q7CompiledRowOracle_clean_understanding_branches
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (clean : ReversibleCircuit.RowOracleInputSpec
      p configuration selector input) :
    let output :=
      (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
        reversibleGatePermutation input
    ReversibleCircuit.observeRowOracle p output =
        q7RowBranchSemanticAccumulatorAction configuration selector
          (ReversibleCircuit.observeRowOracle p input) ∧
      (∀ wire,
        wire ∉ columnKeyWires p →
        wire ∉ columnSelectorWires p →
        wire ≠ keySignalWire p →
        output wire = input wire) := by
  have linked := q7CompiledRowOracle_clean_understanding_action
    configuration selector input clean
  dsimp only at linked ⊢
  rw [q7RowSemanticAccumulatorAction_eq_branches] at linked
  exact linked

end

end ProbabilityGeneratorQProof
