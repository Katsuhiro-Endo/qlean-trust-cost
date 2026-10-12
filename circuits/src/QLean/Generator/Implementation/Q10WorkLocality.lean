import QLean.Generator.Implementation.UnderstandingSpecificationsLink
import QLean.Generator.Implementation.ProbabilityGeneratorFullOperatorCorrectness
import QLean.Generator.Implementation.AlignCircuitCorrectness
import QLean.Generator.Implementation.AmplitudeDiscriminatorCorrectness
import QLean.Generator.Implementation.QActualSelectorPathCorrectness

/-!
# The four support-local Q10 edges

This implementation module proves the part of the Q10 work-clean ledger that
does not borrow oracle scratch.  Uniform preparation and Q3/Q7 are
deliberately absent; their five edges require semantic restoration theorems.
-/

namespace ProbabilityGeneratorQProof

open VerifiedCircuitCore

noncomputable section

private theorem finsetDisjoint_of_listDisjoint
    {α : Type*} [DecidableEq α] {left right : List α}
    (disjoint : left.Disjoint right) :
    Disjoint left.toFinset right.toFinset := by
  rw [Finset.disjoint_left]
  intro value leftMember rightMember
  exact (List.disjoint_left.mp disjoint)
    (by simpa using leftMember) (by simpa using rightMember)

def q10SystemToColumnKeySupport (p : QParameters) :
    Finset (Wire p.ancillaWidth p.systemWidth) :=
  (topColumnKeyWires p).toFinset

def q10AmplitudeSignalSupport (p : QParameters) :
    Finset (Wire p.ancillaWidth p.systemWidth) :=
  {amplitudeSignalWire p}

def q10OutputAlignmentSupport (p : QParameters) :
    Finset (Wire p.ancillaWidth p.systemWidth) :=
  (systemWires p ++ rowSelectorWires p ++ [keySignalWire p]).toFinset

theorem topColumnKeyWires_disjoint_q10GeneratorWork (p : QParameters) :
    (topColumnKeyWires p).Disjoint
      (QLayout.canonical p).oracleWork.wireList := by
  change (QLayout.canonical p).columnKey.wireList.Disjoint
    (QLayout.canonical p).oracleWork.wireList
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.canonical]
  omega

theorem systemWires_disjoint_q10GeneratorWork (p : QParameters) :
    (systemWires p).Disjoint
      (QLayout.canonical p).oracleWork.wireList := by
  simpa [systemWires, QLayout.systemWire] using
    (RegisterSlice.systemWires_disjoint_wireList
      (systemWidth := p.systemWidth) (QLayout.canonical p).oracleWork)

theorem rowSelectorWires_disjoint_q10GeneratorWork (p : QParameters) :
    (rowSelectorWires p).Disjoint
      (QLayout.canonical p).oracleWork.wireList := by
  change (QLayout.canonical p).rowSelector.wireList.Disjoint
    (QLayout.canonical p).oracleWork.wireList
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.canonical]
  omega

theorem columnSelectorWires_disjoint_q10GeneratorWork (p : QParameters) :
    (columnSelectorWires p).Disjoint
      (QLayout.canonical p).oracleWork.wireList := by
  change (QLayout.canonical p).columnSelector.wireList.Disjoint
    (QLayout.canonical p).oracleWork.wireList
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.canonical]
  omega

theorem rowOutputWires_disjoint_q10GeneratorWork (p : QParameters) :
    (rowOutputWires p).Disjoint
      (QLayout.canonical p).oracleWork.wireList := by
  change (QLayout.canonical p).rowOutput.wireList.Disjoint
    (QLayout.canonical p).oracleWork.wireList
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.canonical]
  omega

theorem selectorOutputWires_disjoint_q10GeneratorWork (p : QParameters) :
    (selectorOutputWires p).Disjoint
      (QLayout.canonical p).oracleWork.wireList := by
  change (QLayout.canonical p).selectorOutput.wireList.Disjoint
    (QLayout.canonical p).oracleWork.wireList
  apply RegisterSlice.wireList_disjoint_of_end_le_start
  simp [QLayout.canonical]
  omega

theorem negativeWire_not_mem_q10GeneratorWork (p : QParameters) :
    negativeWire p ∉ (QLayout.canonical p).oracleWork.wireList := by
  have separated :
      ((QLayout.canonical p).negative.wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.canonical p).oracleWork.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [QLayout.canonical]
  exact List.disjoint_left.mp separated (by
    simp [negativeWire, RegisterSlice.wireList])

theorem activeWire_not_mem_q10GeneratorWork (p : QParameters) :
    activeWire p ∉ (QLayout.canonical p).oracleWork.wireList := by
  have separated :
      ((QLayout.canonical p).active.wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.canonical p).oracleWork.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [QLayout.canonical]
  exact List.disjoint_left.mp separated (by
    simp [activeWire, RegisterSlice.wireList])

theorem keySignalWire_not_mem_q10GeneratorWork (p : QParameters) :
    keySignalWire p ∉ (QLayout.canonical p).oracleWork.wireList := by
  have separated :
      ((QLayout.canonical p).keySignal.wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.canonical p).oracleWork.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [QLayout.canonical]
    omega
  exact List.disjoint_left.mp separated (by
    simp [keySignalWire, RegisterSlice.wireList])

theorem amplitudeSignalWire_not_mem_q10GeneratorWork (p : QParameters) :
    amplitudeSignalWire p ∉ (QLayout.canonical p).oracleWork.wireList := by
  have separated :
      ((QLayout.canonical p).amplitudeSignal.wireList :
          List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        ((QLayout.canonical p).oracleWork.wireList :
          List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [QLayout.canonical]
    omega
  exact List.disjoint_left.mp separated (by
    simp [amplitudeSignalWire, RegisterSlice.wireList])

theorem q10SystemToColumnKeySupport_disjoint_work (p : QParameters) :
    Disjoint (q10SystemToColumnKeySupport p)
      (QLayout.canonical p).oracleWork.wireList.toFinset := by
  exact finsetDisjoint_of_listDisjoint
    (topColumnKeyWires_disjoint_q10GeneratorWork p)

theorem q10AmplitudeSignalSupport_disjoint_work (p : QParameters) :
    Disjoint (q10AmplitudeSignalSupport p)
      (QLayout.canonical p).oracleWork.wireList.toFinset := by
  rw [Finset.disjoint_left]
  intro wire supported workMember
  have equal : wire = amplitudeSignalWire p := by
    simpa [q10AmplitudeSignalSupport] using supported
  subst wire
  exact amplitudeSignalWire_not_mem_q10GeneratorWork p (by
    simpa using workMember)

theorem q10OutputAlignmentSupport_disjoint_work (p : QParameters) :
    Disjoint (q10OutputAlignmentSupport p)
      (QLayout.canonical p).oracleWork.wireList.toFinset := by
  apply finsetDisjoint_of_listDisjoint
  rw [List.disjoint_left]
  intro wire supportMember workMember
  simp only [List.mem_append, List.mem_singleton] at supportMember
  rcases supportMember with (systemMember | rowMember) | keyEqual
  · exact (List.disjoint_left.mp (systemWires_disjoint_q10GeneratorWork p))
      systemMember workMember
  · exact (List.disjoint_left.mp
      (rowSelectorWires_disjoint_q10GeneratorWork p)) rowMember workMember
  · subst wire
    exact keySignalWire_not_mem_q10GeneratorWork p workMember

theorem xorSystemIntoColumnKeyFullAnalyticOperator_preservesOutside
    (p : QParameters) :
    BasisOperatorPreservesOutside (q10SystemToColumnKeySupport p)
      (xorSystemIntoColumnKeyFullAnalyticOperator p) := by
  intro output input nonzero wire outside
  have circuitNonzero := nonzero
  rw [← XorSystemIntoColumnKeyTargetOperator_eq_fullAnalytic p] at circuitNonzero
  have circuitCorrect :
      (xorSystemIntoColumnKeyPrimitiveCircuit p).toIdealOperator
          primitiveGateOperator = XorSystemIntoColumnKeyTargetOperator p := by
    exact (xorSystemIntoColumnKeyExactOperatorComponent p).correct
  rw [← circuitCorrect] at circuitNonzero
  change (xorSystemIntoColumnKeyPrimitiveCircuit p).toIdealOperator
    primitiveGateOperator output input ≠ 0 at circuitNonzero
  rw [xorSystemIntoColumnKey_basisAmplitude] at circuitNonzero
  by_cases equal : output =
      (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
        reversibleGatePermutation input
  · subst output
    apply xorSystemIntoColumnKey_runBasis_outside p input wire
    intro member
    apply outside
    simpa [q10SystemToColumnKeySupport] using member
  · simp [equal] at circuitNonzero

theorem amplitudeSignFullAnalyticOperator_preservesOutside
    (p : QParameters) :
    BasisOperatorPreservesOutside (q10AmplitudeSignalSupport p)
      (amplitudeSignFullAnalyticOperator p) := by
  intro output input nonzero wire outside
  have circuitNonzero := nonzero
  rw [← ActiveCopyNegativePhaseTargetOperator_eq_fullAnalytic p]
      at circuitNonzero
  have circuitCorrect :
      (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).toIdealOperator
          primitiveGateOperator = ActiveCopyNegativePhaseTargetOperator p := by
    exact (activeCopyNegativePhaseExactOperatorComponent p).correct
  rw [← circuitCorrect] at circuitNonzero
  change (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).toIdealOperator
    primitiveGateOperator output input ≠ 0 at circuitNonzero
  rw [copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_apply_sparse]
      at circuitNonzero
  let moved := cnotBasisAction (activeWire p) (amplitudeSignalWire p) input
  by_cases equal : output = moved
  · subst output
    exact cnotBasisAction_control_or_other _ _ _
      (by
        intro wireEqual
        apply outside
        simp [q10AmplitudeSignalSupport, wireEqual]) input
  · simp [moved, equal] at circuitNonzero

theorem outputAlignmentFullAnalyticOperator_preservesOutside
    (p : QParameters) :
    BasisOperatorPreservesOutside (q10OutputAlignmentSupport p)
      (outputAlignmentFullAnalyticOperator p) := by
  intro output input nonzero wire outside
  have circuitNonzero := nonzero
  rw [← ControlledOracleOutputAlignmentTargetOperator_eq_fullAnalytic p]
      at circuitNonzero
  have circuitCorrect :
      Circuit.toIdealOperator primitiveGateOperator
          (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p) =
        ControlledOracleOutputAlignmentTargetOperator p := by
    exact (controlledOracleOutputAlignmentExactOperatorComponent p).correct
  rw [← circuitCorrect] at circuitNonzero
  change Circuit.toIdealOperator primitiveGateOperator
    (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p)
      output input ≠ 0 at circuitNonzero
  rw [controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_basisAmplitude]
      at circuitNonzero
  have equal : output = Circuit.runBasis reversibleGatePermutation
      (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p)
        input := by
    simpa using circuitNonzero
  rw [equal]
  apply controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets
  · intro member
    apply outside
    simp [q10OutputAlignmentSupport, member]
  · intro member
    apply outside
    simp [q10OutputAlignmentSupport, member]
  · intro wireEqual
    subst wire
    apply outside
    simp [q10OutputAlignmentSupport]

theorem amplitudeSignalFlipFullAnalyticOperator_preservesOutside
    (p : QParameters) :
    BasisOperatorPreservesOutside (q10AmplitudeSignalSupport p)
      (amplitudeSignalFlipFullAnalyticOperator p) := by
  intro output input nonzero wire outside
  have circuitNonzero := nonzero
  rw [← FlipAmplitudeSignalTargetOperator_eq_fullAnalytic p] at circuitNonzero
  have circuitCorrect :
      (flipAmplitudeSignalPrimitiveCircuit p).toIdealOperator
          primitiveGateOperator = FlipAmplitudeSignalTargetOperator p := by
    exact (flipAmplitudeSignalExactOperatorComponent p).correct
  rw [← circuitCorrect] at circuitNonzero
  change (flipAmplitudeSignalPrimitiveCircuit p).toIdealOperator
    primitiveGateOperator output input ≠ 0 at circuitNonzero
  rw [flipAmplitudeSignalPrimitiveCircuit_basisAmplitude] at circuitNonzero
  by_cases equal : output =
      (flipAmplitudeSignalReversibleCircuit p).runBasis
        reversibleGatePermutation input
  · subst output
    apply flipAmplitudeSignal_runBasis_other p input wire
    intro wireEqual
    apply outside
    simp [q10AmplitudeSignalSupport, wireEqual]
  · simp [equal] at circuitNonzero

private theorem q10ColumnKeyWires_eq_topColumnKeyWires (p : QParameters) :
    columnKeyWires p = topColumnKeyWires p := by
  rfl

private theorem q10ColumnKeyWires_disjoint_columnSelectorWires
    (p : QParameters) :
    (columnKeyWires p).Disjoint (columnSelectorWires p) := by
  let left := (QLayout.canonical p).columnKey
  let right := (QLayout.canonical p).columnSelector
  have disjoint :
      (left.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    left.wireList_disjoint_of_end_le_start right
      (by simp [left, right, QLayout.canonical])
  simpa [columnKeyWires, columnKeyWire, columnSelectorWires,
    columnSelectorWire, left, right, RegisterSlice.wireList] using disjoint

private theorem q10KeySignalWire_not_mem_columnSelectorWires
    (p : QParameters) :
    keySignalWire p ∉ columnSelectorWires p := by
  let left := (QLayout.canonical p).columnSelector
  let right := (QLayout.canonical p).keySignal
  have disjoint :
      (left.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    left.wireList_disjoint_of_end_le_start right
      (by simp [left, right, QLayout.canonical]; omega)
  have member : keySignalWire p ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    change right.ancillaWire 0 ∈
      (right.wireList : List (Wire p.ancillaWidth p.systemWidth))
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  exact fun leftMember => (List.disjoint_left.mp disjoint)
    (by simpa [columnSelectorWires, columnSelectorWire, left,
      RegisterSlice.wireList] using leftMember) member

private theorem q10Alignment_runBasis_projectRowSelector
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    q10ProjectRegisterBasis (q10RowSelectorWire p)
        (Circuit.runBasis reversibleGatePermutation
          (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p)
          input) =
      if input (amplitudeSignalWire p) then
        fun index =>
          input (selectorOutputWire p index) !=
            input (rowSelectorWire p index)
      else q10ProjectRegisterBasis (q10RowSelectorWire p) input := by
  funext index
  have readout := congrArg (fun bits => bits[index.val]?)
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readRowSelector
      p input)
  by_cases enabled : input (amplitudeSignalWire p) = true
  · rw [if_pos enabled]
    have readout' :
        some ((controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
          reversibleGatePermutation input (rowSelectorWire p index)) =
          some (if input (selectorOutputWire p index) = true then
            !input (rowSelectorWire p index)
          else input (rowSelectorWire p index)) := by
      simpa [ReversibleCircuit.readWires, rowSelectorWires, selectorOutputWires,
        xorRegisterBits, enabled, index.isLt] using readout
    have pointwise := Option.some.inj readout'
    cases source : input (selectorOutputWire p index) <;>
      cases target : input ((QLayout.canonical p).rowSelector.ancillaWire index) <;>
      simpa [q10ProjectRegisterBasis, q10RowSelectorWire, rowSelectorWire,
        source, target] using pointwise
  · rw [if_neg enabled]
    have readout' :
        some ((controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
          reversibleGatePermutation input (rowSelectorWire p index)) =
          some (input (rowSelectorWire p index)) := by
      simpa [ReversibleCircuit.readWires, rowSelectorWires, selectorOutputWires,
        xorRegisterBits, enabled, index.isLt] using readout
    simpa [q10ProjectRegisterBasis, q10RowSelectorWire, rowSelectorWire] using
      Option.some.inj readout'

/-- Locality outside a selector slice preserves the decoded selector value,
and therefore preserves the active/non-padding predicate. -/
theorem q10SelectorActive_preserved_of_locality
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth →
      Wire p.ancillaWidth p.systemWidth)
    (support : Finset (Wire p.ancillaWidth p.systemWidth))
    (operator : Operator (JointBasis p.ancillaWidth p.systemWidth))
    (locality : BasisOperatorPreservesOutside support operator)
    (outsideSelector : ∀ index, selectorWire index ∉ support)
    (output input : JointBasis p.ancillaWidth p.systemWidth)
    (nonzero : operator output input ≠ 0)
    (active : qOracleSelectorValue p.selectorWidth
      (q10ProjectRegisterBasis selectorWire input) < p.selectorCount) :
    qOracleSelectorValue p.selectorWidth
      (q10ProjectRegisterBasis selectorWire output) < p.selectorCount := by
  have projected : q10ProjectRegisterBasis selectorWire output =
      q10ProjectRegisterBasis selectorWire input := by
    funext index
    exact locality output input nonzero (selectorWire index)
      (outsideSelector index)
  rw [projected]
  exact active

/-- Q2 preserves both restored oracle work and the active column selector. -/
theorem q10SystemToColumnKey_preserves_columnOracleClean (p : QParameters) :
    BasisPredicateTransitionSpecification
      (xorSystemIntoColumnKeyFullAnalyticOperator p)
      (q10ColumnOracleCleanPredicate p)
      (q10ColumnOracleCleanPredicate p) := by
  apply BasisPredicateTransitionSpecification.strengthenInvariant
    (q10GeneratorWorkCleanTransition_of_preservesOutside
      (q10SystemToColumnKeySupport p)
      (xorSystemIntoColumnKeyFullAnalyticOperator_preservesOutside p)
      (q10SystemToColumnKeySupport_disjoint_work p))
  intro output input nonzero active
  apply q10SelectorActive_preserved_of_locality p (q10ColumnSelectorWire p)
    (q10SystemToColumnKeySupport p)
    (xorSystemIntoColumnKeyFullAnalyticOperator p)
    (xorSystemIntoColumnKeyFullAnalyticOperator_preservesOutside p)
    _ output input nonzero active
  intro index supported
  have keyMember : q10ColumnSelectorWire p index ∈ columnSelectorWires p := by
    simp [q10ColumnSelectorWire, columnSelectorWires, columnSelectorWire]
  have targetMember : q10ColumnSelectorWire p index ∈ columnKeyWires p := by
    simpa [q10SystemToColumnKeySupport,
      q10ColumnKeyWires_eq_topColumnKeyWires] using supported
  exact (List.disjoint_left.mp
    (q10ColumnKeyWires_disjoint_columnSelectorWires p))
      targetMember keyMember

/-- Q2 preserves the complete source-reachable Q3 input boundary, not only
its work-clean/active-column projection. -/
theorem q10SystemToColumnKey_preserves_beforeColumnOracleReady
    (p : QParameters) :
    BasisPredicateTransitionSpecification
      (xorSystemIntoColumnKeyFullAnalyticOperator p)
      (Q10BeforeColumnOracleReady p)
      (Q10BeforeColumnOracleReady p) := by
  intro input output ready outputOutside
  by_contra nonzero
  apply outputOutside
  have outsideSupport_of_not_mem_columnKey : ∀ wire,
      wire ∉ columnKeyWires p → wire ∉ q10SystemToColumnKeySupport p := by
    intro wire absent supported
    apply absent
    simpa [q10SystemToColumnKeySupport,
      q10ColumnKeyWires_eq_topColumnKeyWires] using supported
  refine {
    columnClean := ?_
    rowSelectorZero := ?_
    selectorOutputZero := ?_
    activeZero := ?_
    amplitudeZero := ?_ }
  · by_contra dirty
    exact nonzero ((q10SystemToColumnKey_preserves_columnOracleClean p)
      input output ready.columnClean dirty)
  · intro index
    rw [xorSystemIntoColumnKeyFullAnalyticOperator_preservesOutside p
      output input nonzero (q10RowSelectorWire p index)]
    · exact ready.rowSelectorZero index
    · apply outsideSupport_of_not_mem_columnKey
      intro member
      exact (List.disjoint_left.mp
        (qActualColumnKeyWires_disjoint_rowSelectorWires p))
          member (by simp [q10RowSelectorWire, rowSelectorWires, rowSelectorWire])
  · intro index
    rw [xorSystemIntoColumnKeyFullAnalyticOperator_preservesOutside p
      output input nonzero (q10SelectorOutputWire p index)]
    · exact ready.selectorOutputZero index
    · apply outsideSupport_of_not_mem_columnKey
      intro member
      exact (List.disjoint_left.mp
        (qActualSelectorOutputWires_disjoint_columnKeyWires p))
          (by simp [q10SelectorOutputWire, selectorOutputWires,
            selectorOutputWire]) member
  · rw [xorSystemIntoColumnKeyFullAnalyticOperator_preservesOutside p
      output input nonzero (q10ActiveWire p)]
    · exact ready.activeZero
    · exact outsideSupport_of_not_mem_columnKey _
        (by simpa [q10ActiveWire, activeWire] using
          qActualActiveWire_not_mem_columnKeyWires p)
  · rw [xorSystemIntoColumnKeyFullAnalyticOperator_preservesOutside p
      output input nonzero (q10AmplitudeSignalWire p)]
    · exact ready.amplitudeZero
    · exact outsideSupport_of_not_mem_columnKey _
        (by simpa [q10AmplitudeSignalWire, amplitudeSignalWire] using
          amplitudeSignalWire_not_mem_columnKeyWires p)

/-- Q4 changes only the amplitude signal, so it preserves the active column
selector in addition to the restored work suffix. -/
theorem q10AmplitudeSign_preserves_columnOracleClean (p : QParameters) :
    BasisPredicateTransitionSpecification
      (amplitudeSignFullAnalyticOperator p)
      (q10ColumnOracleCleanPredicate p)
      (q10ColumnOracleCleanPredicate p) := by
  apply BasisPredicateTransitionSpecification.strengthenInvariant
    (q10GeneratorWorkCleanTransition_of_preservesOutside
      (q10AmplitudeSignalSupport p)
      (amplitudeSignFullAnalyticOperator_preservesOutside p)
      (q10AmplitudeSignalSupport_disjoint_work p))
  intro output input nonzero active
  apply q10SelectorActive_preserved_of_locality p (q10ColumnSelectorWire p)
    (q10AmplitudeSignalSupport p) (amplitudeSignFullAnalyticOperator p)
    (amplitudeSignFullAnalyticOperator_preservesOutside p)
    _ output input nonzero active
  intro index supported
  have equal : q10ColumnSelectorWire p index = amplitudeSignalWire p := by
    simpa [q10AmplitudeSignalSupport] using supported
  apply amplitudeSignalWire_not_mem_columnSelectorWires p
  rw [← equal]
  simp [q10ColumnSelectorWire, columnSelectorWire, columnSelectorWires]

/-- Q4 turns the Q3 `active`/selector-output relation into the amplitude-
controlled relation consumed by Q5.  Its controlled phase changes no basis
label, so only the CNOT target requires inspection. -/
theorem q10AmplitudeSign_afterToAlignmentReady_transition
    (p : QParameters) :
    BasisPredicateTransitionSpecification
      (amplitudeSignFullAnalyticOperator p)
      (Q10AfterColumnOracleReady p)
      (Q10OutputAlignmentReady p) := by
  intro input output ready outputOutside
  by_contra nonzero
  apply outputOutside
  refine {
    columnClean := ?_
    rowSelectorZero := ?_
    selectorOutputActiveOfAmplitude := ?_ }
  · by_contra dirty
    exact nonzero ((q10AmplitudeSign_preserves_columnOracleClean p)
      input output ready.columnClean dirty)
  · intro index
    rw [amplitudeSignFullAnalyticOperator_preservesOutside p
      output input nonzero (q10RowSelectorWire p index)]
    · exact ready.rowSelectorZero index
    · intro supported
      have equal : q10RowSelectorWire p index = amplitudeSignalWire p := by
        simpa [q10AmplitudeSignalSupport] using supported
      exact amplitudeSignalWire_not_mem_rowSelectorWires p
        (equal ▸ (by simp [q10RowSelectorWire, rowSelectorWire,
          rowSelectorWires]))
  · intro outputAmplitude
    have circuitNonzero := nonzero
    rw [← ActiveCopyNegativePhaseTargetOperator_eq_fullAnalytic p]
        at circuitNonzero
    have circuitCorrect :
        (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).toIdealOperator
            primitiveGateOperator = ActiveCopyNegativePhaseTargetOperator p := by
      exact (activeCopyNegativePhaseExactOperatorComponent p).correct
    rw [← circuitCorrect] at circuitNonzero
    change (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).toIdealOperator
      primitiveGateOperator output input ≠ 0 at circuitNonzero
    rw [copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_apply_sparse]
        at circuitNonzero
    let moved := cnotBasisAction (activeWire p) (amplitudeSignalWire p) input
    by_cases equal : output = moved
    · subst output
      have inputActive : input (activeWire p) = true := by
        change moved (amplitudeSignalWire p) = true at outputAmplitude
        have inputAmplitudeZero : input (amplitudeSignalWire p) = false := by
          simpa [q10AmplitudeSignalWire, amplitudeSignalWire] using
            ready.amplitudeZero
        by_cases active : input (activeWire p) = true
        · exact active
        · have activeFalse : input (activeWire p) = false :=
            Bool.eq_false_of_not_eq_true active
          simp [moved, activeFalse, inputAmplitudeZero]
            at outputAmplitude
      apply q10SelectorActive_preserved_of_locality p (q10SelectorOutputWire p)
        (q10AmplitudeSignalSupport p) (amplitudeSignFullAnalyticOperator p)
        (amplitudeSignFullAnalyticOperator_preservesOutside p)
        _ moved input nonzero
        (ready.selectorOutputActiveOfActive inputActive)
      intro index supported
      have equalWire : q10SelectorOutputWire p index = amplitudeSignalWire p := by
        simpa [q10AmplitudeSignalSupport] using supported
      exact amplitudeSignalWire_not_mem_selectorOutputWires p
        (equalWire ▸ (by simp [q10SelectorOutputWire, selectorOutputWire,
          selectorOutputWires]))
    · simp [moved, equal] at circuitNonzero

/-- Q5 preserves the work-clean active-column part of its input.  Generation
of the active row selector is a separate source-reachable semantic theorem. -/
theorem q10OutputAlignment_preserves_columnOracleClean (p : QParameters) :
    BasisPredicateTransitionSpecification
      (outputAlignmentFullAnalyticOperator p)
      (q10ColumnOracleCleanPredicate p)
      (q10ColumnOracleCleanPredicate p) := by
  apply BasisPredicateTransitionSpecification.strengthenInvariant
    (q10GeneratorWorkCleanTransition_of_preservesOutside
      (q10OutputAlignmentSupport p)
      (outputAlignmentFullAnalyticOperator_preservesOutside p)
      (q10OutputAlignmentSupport_disjoint_work p))
  intro output input nonzero active
  apply q10SelectorActive_preserved_of_locality p (q10ColumnSelectorWire p)
    (q10OutputAlignmentSupport p) (outputAlignmentFullAnalyticOperator p)
    (outputAlignmentFullAnalyticOperator_preservesOutside p)
    _ output input nonzero active
  intro index supported
  have selectorMember : q10ColumnSelectorWire p index ∈
      columnSelectorWires p := by
    simp [q10ColumnSelectorWire, columnSelectorWire, columnSelectorWires]
  simp only [q10OutputAlignmentSupport, List.mem_toFinset,
    List.mem_append, List.mem_singleton] at supported
  rcases supported with systemOrRow | keyEqual
  · rcases systemOrRow with systemMember | rowMember
    · exact (List.disjoint_left.mp
        (qActualColumnSelectorWires_disjoint_systemWires p))
          selectorMember systemMember
    · exact (List.disjoint_left.mp
        (qActualColumnSelectorWires_disjoint_rowSelectorWires p))
          selectorMember rowMember
  · apply q10KeySignalWire_not_mem_columnSelectorWires p
    rw [← keyEqual]
    exact selectorMember

/-- Q5's independent alignment specification.  The proof uses only the
reviewable row-selector basis action and the Q3/Q4 accumulator relation; the
column-oracle implementation remains behind its own boundary. -/
theorem q10OutputAlignment_ready_transition (p : QParameters) :
    Q10OutputAlignmentReadySpecification p := by
  intro input output ready outputOutside
  by_contra nonzero
  apply outputOutside
  constructor
  · by_contra columnDirty
    exact nonzero
      ((q10OutputAlignment_preserves_columnOracleClean p)
        input output ready.columnClean columnDirty)
  · have circuitNonzero := nonzero
    rw [← ControlledOracleOutputAlignmentTargetOperator_eq_fullAnalytic p]
        at circuitNonzero
    have circuitCorrect :
        Circuit.toIdealOperator primitiveGateOperator
            (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p) =
          ControlledOracleOutputAlignmentTargetOperator p := by
      exact (controlledOracleOutputAlignmentExactOperatorComponent p).correct
    rw [← circuitCorrect] at circuitNonzero
    change Circuit.toIdealOperator primitiveGateOperator
      (controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit p)
        output input ≠ 0 at circuitNonzero
    rw [controlledXorOracleOutputsIntoAlignedRegistersPrimitiveCircuit_basisAmplitude]
        at circuitNonzero
    have equal : output = Circuit.runBasis reversibleGatePermutation
        (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p)
          input := by
      simpa using circuitNonzero
    rw [equal]
    unfold q10RowSelectorActivePredicate
    rw [q10Alignment_runBasis_projectRowSelector]
    by_cases enabled : input (amplitudeSignalWire p) = true
    · rw [if_pos enabled]
      have projected :
          (fun index => input (selectorOutputWire p index) !=
            input (rowSelectorWire p index)) =
            q10ProjectRegisterBasis (q10SelectorOutputWire p) input := by
        funext index
        have rowZero : input (rowSelectorWire p index) = false := by
          simpa [q10RowSelectorWire, rowSelectorWire] using
            ready.rowSelectorZero index
        rw [rowZero]
        simp [q10ProjectRegisterBasis, q10SelectorOutputWire,
          selectorOutputWire]
      rw [projected]
      exact ready.selectorOutputActiveOfAmplitude enabled
    · have disabled : input (amplitudeSignalWire p) = false :=
        Bool.eq_false_of_not_eq_true enabled
      rw [if_neg enabled]
      rw [q10SelectorValue_eq_zero_of_zeroPredicate p
        (q10RowSelectorWire p) input ready.rowSelectorZero]
      exact p.selectorCount_pos

/-- Q8 changes only the amplitude signal, so it preserves the active row
selector in addition to the restored work suffix. -/
theorem q10AmplitudeSignalFlip_preserves_rowOracleClean (p : QParameters) :
    BasisPredicateTransitionSpecification
      (amplitudeSignalFlipFullAnalyticOperator p)
      (q10RowOracleCleanPredicate p)
      (q10RowOracleCleanPredicate p) := by
  apply BasisPredicateTransitionSpecification.strengthenInvariant
    (q10GeneratorWorkCleanTransition_of_preservesOutside
      (q10AmplitudeSignalSupport p)
      (amplitudeSignalFlipFullAnalyticOperator_preservesOutside p)
      (q10AmplitudeSignalSupport_disjoint_work p))
  intro output input nonzero active
  apply q10SelectorActive_preserved_of_locality p (q10RowSelectorWire p)
    (q10AmplitudeSignalSupport p) (amplitudeSignalFlipFullAnalyticOperator p)
    (amplitudeSignalFlipFullAnalyticOperator_preservesOutside p)
    _ output input nonzero active
  intro index supported
  have equal : q10RowSelectorWire p index = amplitudeSignalWire p := by
    simpa [q10AmplitudeSignalSupport] using supported
  apply amplitudeSignalWire_not_mem_rowSelectorWires p
  rw [← equal]
  simp [q10RowSelectorWire, rowSelectorWire, rowSelectorWires]

/-- Concrete support-local half of the Q10 clean-boundary proof. -/
def q10WorkLocalityEvidence (p : QParameters) :
    Q10WorkLocalityEvidence p where
  systemToColumnKeySupport := q10SystemToColumnKeySupport p
  systemToColumnKeyLocality :=
    xorSystemIntoColumnKeyFullAnalyticOperator_preservesOutside p
  systemToColumnKeyDisjoint :=
    q10SystemToColumnKeySupport_disjoint_work p
  amplitudeSignSupport := q10AmplitudeSignalSupport p
  amplitudeSignLocality := amplitudeSignFullAnalyticOperator_preservesOutside p
  amplitudeSignDisjoint := q10AmplitudeSignalSupport_disjoint_work p
  outputAlignmentSupport := q10OutputAlignmentSupport p
  outputAlignmentLocality := outputAlignmentFullAnalyticOperator_preservesOutside p
  outputAlignmentDisjoint := q10OutputAlignmentSupport_disjoint_work p
  amplitudeSignalFlipSupport := q10AmplitudeSignalSupport p
  amplitudeSignalFlipLocality :=
    amplitudeSignalFlipFullAnalyticOperator_preservesOutside p
  amplitudeSignalFlipDisjoint := q10AmplitudeSignalSupport_disjoint_work p

end

end ProbabilityGeneratorQProof
