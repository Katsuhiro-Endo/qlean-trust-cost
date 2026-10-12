import QLean.Generator.Implementation.QActualSelectorPathCorrectness
import QLean.Generator.Implementation.QActualDiagonalAcceptedCorrectness
import QLean.Generator.Implementation.QOracleRowIllegalInputCorrectness
import QLean.Generator.Implementation.QOracleColumnIllegalInputCorrectness

/-!
# Q正本回路の拒否path振幅

Row oracleが拒否または非合法入力を固定する場合を、full oracleの厳密な基底作用から
逆追跡する。Column oracle、整列、振幅判別、COPYを通して残る非零ancillaを用い、
一様準備のsupport外であることから振幅が0になることを示す。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

open ReversibleCircuit

/-- 全bitが0である物理register基底。 -/
def qZeroRegisterBasis (p : QParameters) : RegisterBasis p.systemWidth :=
  fun _ => false

/-- 有効selector集合の先頭にあるselector。 -/
def qZeroSelector (p : QParameters) : QSelector p :=
  ⟨0, p.selectorCount_pos⟩

/-- 全0物理registerのbit列は同じ幅のfalse反復列である。 -/
theorem registerBitList_qZeroRegisterBasis (p : QParameters) :
    registerBitList (qZeroRegisterBasis p) =
      List.replicate p.systemWidth false := by
  unfold registerBitList qZeroRegisterBasis
  have mapFalse : ∀ values : List (Fin p.systemWidth),
      values.map (fun _ => false) = List.replicate values.length false := by
    intro values
    induction values with
    | nil => rfl
    | cons value values inductionHypothesis =>
        rw [List.map_cons, inductionHypothesis]
        change false :: List.replicate values.length false =
          List.replicate (Nat.succ values.length) false
        rw [List.replicate_succ]
  rw [mapFalse]
  simp

/-- 定数0のlittle-endian bit列はfalse反復列である。 -/
theorem constantBits_zero (width : Nat) :
    constantBits 0 width = List.replicate width false := by
  unfold constantBits
  have auxiliary : ∀ start width,
      constantBitsAux 0 start width = List.replicate width false := by
    intro start count
    induction count generalizing start with
    | zero => rfl
    | succ count inductionHypothesis =>
        rw [constantBitsAux, show count + 1 = Nat.succ count by omega,
          List.replicate_succ, inductionHypothesis]
        have zeroBit : Nat.testBit 0 start = false := by simp
        rw [zeroBit]
  exact auxiliary 0 width

/-- 全0物理registerはdelimiter符号として復号できない。 -/
theorem decodeDelimiter_qZeroRegisterBasis (p : QParameters) :
    decodeDelimiter (qZeroRegisterBasis p) = none := by
  apply decodeDelimiter_eq_none_iff.mpr
  rintro ⟨configuration, encoded⟩
  have delimiter := delimiterEncoding_delimiter configuration
  rw [encoded] at delimiter
  simp [qZeroRegisterBasis] at delimiter

/-- 終端X逆追跡像は全0 column-keyに対する非合法column入力仕様を満たす。 -/
theorem qActualAfterFinalFlipPreimage_columnIllegalInputSpec
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    ColumnOracleIllegalInputSpec p (qZeroRegisterBasis p) (qZeroSelector p)
      (qActualAfterFinalFlipPreimage p output rowSelector) := by
  refine {
    column_key_bits := ?_
    selector_bits := ?_
    work_zero := ?_ }
  · rw [registerBitList_qZeroRegisterBasis]
    simpa [columnKeyWires] using
      qActualAfterFinalFlipPreimage_columnKey_zero p output rowSelector
  · rw [show (qZeroSelector p).val = 0 by rfl, constantBits_zero]
    simpa [columnSelectorWires] using
      qActualAfterFinalFlipPreimage_columnSelector_zero p output rowSelector
  · intro wire member
    exact qActualAfterFinalFlipPreimage_oracleWork_zero p output rowSelector member

/-- 非合法column入力仕様は整列とdiscriminator CNOTの逆追跡後も保存される。 -/
theorem ReversibleCircuit.ColumnOracleIllegalInputSpec.afterAlignDiscriminator
    {p : QParameters} {basis : RegisterBasis p.systemWidth}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleIllegalInputSpec p basis selector input) :
    ColumnOracleIllegalInputSpec p basis selector
      (cnotBasisAction (activeWire p) (amplitudeSignalWire p)
        ((controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input)) := by
  let aligned := (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
    reversibleGatePermutation input
  refine {
    column_key_bits := ?_
    selector_bits := ?_
    work_zero := ?_ }
  · rw [readWires_cnotBasisAction_of_not_mem (columnKeyWires p)
      (activeWire p) (amplitudeSignalWire p) aligned
      (amplitudeSignalWire_not_mem_columnKeyWires p)]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readWires_outside_targets p input
      (columnKeyWires p) (qTopColumnKeyWires_disjoint_systemWires p)
      (qActualColumnKeyWires_disjoint_rowSelectorWires p)
      (keySignalWire_not_mem_columnKeyWires p)]
    exact specification.column_key_bits
  · rw [readWires_cnotBasisAction_of_not_mem (columnSelectorWires p)
      (activeWire p) (amplitudeSignalWire p) aligned
      (amplitudeSignalWire_not_mem_columnSelectorWires p)]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readWires_outside_targets p input
      (columnSelectorWires p) (qActualColumnSelectorWires_disjoint_systemWires p)
      (qActualColumnSelectorWires_disjoint_rowSelectorWires p)
      (keySignalWire_not_mem_columnSelectorWires p)]
    exact specification.selector_bits
  · intro wire member
    rw [cnotBasisAction_control_or_other (activeWire p)
      (amplitudeSignalWire p) wire
      (diagonalOracleWorkWire_ne_amplitudeSignal p member)]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p input wire]
    · exact specification.work_zero wire member
    · exact (List.disjoint_left.mp
        (systemWires_disjoint_diagonalOracleWorkWires p).symm) member
    · simpa only [← rowSelectorWires_eq_selectorSliceWires] using
        diagonalOracleWorkWire_not_mem_rowSelectorSlice p member
    · intro equal
      exact qActualKeySignalWire_not_mem_diagonalOracleWorkWires p
        (equal ▸ member)

/-- 合法column入力仕様も整列とdiscriminator CNOTの逆追跡後に保存される。 -/
theorem columnOracleInputSpec_afterAlignDiscriminator
    {p : QParameters} {configuration : QConfiguration p}
    {selector : QSelector p}
    {input : JointBasis p.ancillaWidth p.systemWidth}
    (specification : ColumnOracleInputSpec p configuration selector input) :
    ColumnOracleInputSpec p configuration selector
      (cnotBasisAction (activeWire p) (amplitudeSignalWire p)
        ((controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input)) := by
  let aligned := (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
    reversibleGatePermutation input
  refine {
    column_key_bits := ?_
    selector_bits := ?_
    work_zero := ?_ }
  · rw [readWires_cnotBasisAction_of_not_mem (columnKeyWires p)
      (activeWire p) (amplitudeSignalWire p) aligned
      (amplitudeSignalWire_not_mem_columnKeyWires p)]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readWires_outside_targets p input
      (columnKeyWires p) (qTopColumnKeyWires_disjoint_systemWires p)
      (qActualColumnKeyWires_disjoint_rowSelectorWires p)
      (keySignalWire_not_mem_columnKeyWires p)]
    exact specification.column_key_bits
  · rw [readWires_cnotBasisAction_of_not_mem (columnSelectorWires p)
      (activeWire p) (amplitudeSignalWire p) aligned
      (amplitudeSignalWire_not_mem_columnSelectorWires p)]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readWires_outside_targets p input
      (columnSelectorWires p) (qActualColumnSelectorWires_disjoint_systemWires p)
      (qActualColumnSelectorWires_disjoint_rowSelectorWires p)
      (keySignalWire_not_mem_columnSelectorWires p)]
    exact specification.selector_bits
  · intro wire member
    rw [cnotBasisAction_control_or_other (activeWire p)
      (amplitudeSignalWire p) wire
      (diagonalOracleWorkWire_ne_amplitudeSignal p member)]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p input wire]
    · exact specification.work_zero wire member
    · exact (List.disjoint_left.mp
        (systemWires_disjoint_diagonalOracleWorkWires p).symm) member
    · simpa only [← rowSelectorWires_eq_selectorSliceWires] using
        diagonalOracleWorkWire_not_mem_rowSelectorSlice p member
    · intro equal
      exact qActualKeySignalWire_not_mem_diagonalOracleWorkWires p
        (equal ▸ member)

/--
Row oracle逆追跡像が終端X逆追跡像のままなら、一回目のcolumn oracleも非合法な
全0 column-keyを検出して同じ基底を固定する。
-/
theorem qActualAfterColumnInversePreimage_eq_of_row_inactive
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (rowInactive : qActualAfterRowOraclePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector) :
    qActualAfterColumnInversePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector := by
  rw [qActualAfterColumnInversePreimage_eq_runBasis, rowInactive]
  exact applyColumnOracleReferenceAndRestoreWorkCircuit_illegal_identity p
    (qZeroRegisterBasis p) (qZeroSelector p) _
    (qActualAfterFinalFlipPreimage_columnIllegalInputSpec p output rowSelector)
    (decodeDelimiter_qZeroRegisterBasis p)

/-- Row不受理pathではdiscriminator逆追跡像も非合法column入力仕様を満たす。 -/
theorem qActualAfterDiscriminatorPreimage_columnIllegalInputSpec_of_row_inactive
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (rowInactive : qActualAfterRowOraclePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector) :
    ColumnOracleIllegalInputSpec p (qZeroRegisterBasis p) (qZeroSelector p)
      (qActualAfterDiscriminatorPreimage p output rowSelector) := by
  have afterColumn : qActualAfterColumnInversePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector :=
    qActualAfterColumnInversePreimage_eq_of_row_inactive p output rowSelector
      rowInactive
  have beforeSpec : ColumnOracleIllegalInputSpec p (qZeroRegisterBasis p)
      (qZeroSelector p)
      (qActualAfterColumnInversePreimage p output rowSelector) := by
    rw [afterColumn]
    exact qActualAfterFinalFlipPreimage_columnIllegalInputSpec p output rowSelector
  change ColumnOracleIllegalInputSpec p (qZeroRegisterBasis p) (qZeroSelector p)
    (cnotBasisAction (activeWire p) (amplitudeSignalWire p)
      (qActualDiscriminatorOutputPreimage p output rowSelector))
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  exact beforeSpec.afterAlignDiscriminator

/-- Row不受理pathでは二回目のcolumn oracle逆追跡も判別直後の基底を固定する。 -/
theorem qActualAfterColumnOraclePreimage_eq_of_row_inactive
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (rowInactive : qActualAfterRowOraclePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector) :
    qActualAfterColumnOraclePreimage p output rowSelector =
      qActualAfterDiscriminatorPreimage p output rowSelector := by
  apply qActualAfterColumnOraclePreimage_eq_of_runBasis
  exact applyColumnOracleReferenceAndRestoreWorkCircuit_illegal_identity p
    (qZeroRegisterBasis p) (qZeroSelector p) _
    (qActualAfterDiscriminatorPreimage_columnIllegalInputSpec_of_row_inactive p
      output rowSelector rowInactive)
    (decodeDelimiter_qZeroRegisterBasis p)

/-- Row不受理pathでは整列逆追跡後もamplitude signalが真である。 -/
theorem qActualDiscriminatorOutputPreimage_amplitude_true_of_row_inactive
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (rowInactive : qActualAfterRowOraclePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector) :
    qActualDiscriminatorOutputPreimage p output rowSelector
        (amplitudeSignalWire p) = true := by
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _
    (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_systemWires p)
    (amplitudeSignalWire_not_mem_rowSelectorWires p)
    (amplitudeSignalWire_ne_keySignalWire p)]
  rw [qActualAfterColumnInversePreimage_eq_of_row_inactive p output rowSelector
    rowInactive]
  exact qActualAfterFinalFlipPreimage_amplitudeSignal p output rowSelector

/-- Row不受理pathでは整列逆追跡後のactive bitが偽である。 -/
theorem qActualDiscriminatorOutputPreimage_active_false_of_row_inactive
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (rowInactive : qActualAfterRowOraclePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector) :
    qActualDiscriminatorOutputPreimage p output rowSelector
        (activeWire p) = false := by
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _ (activeWire p)
    (qActualActiveWire_not_mem_systemWires p)
    (qActualActiveWire_not_mem_rowSelectorWires p)
    (qActualActiveWire_ne_keySignalWire p)]
  rw [qActualAfterColumnInversePreimage_eq_of_row_inactive p output rowSelector
    rowInactive]
  exact qActualAfterFinalFlipPreimage_active_false p output rowSelector

/-- Row不受理pathではdiscriminator CNOT後もamplitude signalが真である。 -/
theorem qActualAfterDiscriminatorPreimage_amplitude_true_of_row_inactive
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (rowInactive : qActualAfterRowOraclePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector) :
    qActualAfterDiscriminatorPreimage p output rowSelector
        (amplitudeSignalWire p) = true := by
  unfold qActualAfterDiscriminatorPreimage
  rw [cnotBasisAction_target,
    qActualDiscriminatorOutputPreimage_active_false_of_row_inactive p output
      rowSelector rowInactive,
    qActualDiscriminatorOutputPreimage_amplitude_true_of_row_inactive p output
      rowSelector rowInactive]
  rfl

/-- Row不受理pathではcolumn一様準備逆像に真のamplitude ancillaが残る。 -/
theorem qActualColumnPreparedPreimage_amplitude_true_of_row_inactive
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (rowInactive : qActualAfterRowOraclePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector) :
    qActualColumnPreparedPreimage p output rowSelector
        (amplitudeSignalWire p) = true := by
  rw [qActualColumnPreparedPreimage_eq_stages,
    copyToBasisPermutation_amplitudeSignal,
    qActualAfterColumnOraclePreimage_eq_of_row_inactive p output rowSelector
      rowInactive]
  exact qActualAfterDiscriminatorPreimage_amplitude_true_of_row_inactive p output
    rowSelector rowInactive

/-- Row oracleが基底を固定するpathのactual selector振幅は0である。 -/
theorem qActualSelectorAmplitude_eq_zero_of_row_inactive
    (p : QParameters) (output input : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (rowInactive : qActualAfterRowOraclePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector) :
    qActualSelectorAmplitude p output input rowSelector = 0 := by
  unfold qActualSelectorAmplitude
  apply qBeforeRowUniformInverseState_finalSelector_eq_zero p input output
    rowSelector
  exact qColumnPreparedState_eq_zero_of_amplitude_true p input _
    (qActualColumnPreparedPreimage_amplitude_true_of_row_inactive p output
      rowSelector rowInactive)

/-- decode不能な最終出力基底に対するactual selector振幅は常に0である。 -/
theorem qActualSelectorAmplitude_eq_zero_of_illegal_output
    (p : QParameters) (output input : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (illegal : decodeDelimiter output = none) :
    qActualSelectorAmplitude p output input rowSelector = 0 := by
  apply qActualSelectorAmplitude_eq_zero_of_row_inactive p output input rowSelector
  exact qActualAfterRowOraclePreimage_eq_of_illegal p output rowSelector illegal

/-- 合法出力でもrowReferenceが拒否したselectorのactual振幅は0である。 -/
theorem qActualSelectorAmplitude_eq_zero_of_rowReference_none
    (p : QParameters) (output : QConfiguration p)
    (input : RegisterBasis p.systemWidth) (rowSelector : QSelector p)
    (referenceNone : rowReference output rowSelector = none) :
    qActualSelectorAmplitude p (delimiterEncoding output) input rowSelector = 0 := by
  apply qActualSelectorAmplitude_eq_zero_of_row_inactive p
    (delimiterEncoding output) input rowSelector
  exact qActualAfterRowOraclePreimage_eq_of_reference_none p output rowSelector
    referenceNone

/-- `rowReference`受理時もactual row oracleを二回実行すると入力基底へ戻る。 -/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_reference_some_involutive_actual
    {p : QParameters} (output : QConfiguration p) (selector : QSelector p)
    (reference : RowReferenceResult p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (specification : RowOracleInputSpec p output selector input)
    (referenceSome : rowReference output selector = some reference) :
    (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation
        ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input) =
      input := by
  let first := (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
    reversibleGatePermutation input
  let second := (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
    reversibleGatePermutation first
  have firstResult : RowReferenceBranchResult p reference.input
      reference.columnSelector input first := by
    simpa [first] using applyRowOracleReferenceAndRestoreWorkCircuit_reference_some output selector
      reference input specification referenceSome
  have firstSpecification : RowOracleInputSpec p output selector first :=
    RowReferenceBranchResult.preservesInputSpec specification firstResult
  have secondResult : RowReferenceBranchResult p reference.input
      reference.columnSelector first second := by
    simpa [second] using applyRowOracleReferenceAndRestoreWorkCircuit_reference_some output selector
      reference first firstSpecification referenceSome
  change second = input
  exact RowReferenceBranchResult.twice_eq_input firstResult secondResult

/-- `rowReference`受理時のactual row逆追跡像は参照XOR仕様を満たす。 -/
theorem qActualAfterRowOraclePreimage_reference_some_result
    {p : QParameters} (output : QConfiguration p) (selector : QSelector p)
    (reference : RowReferenceResult p)
    (referenceSome : rowReference output selector = some reference) :
    RowReferenceBranchResult p reference.input reference.columnSelector
      (qActualAfterFinalFlipPreimage p (delimiterEncoding output) selector)
      (qActualAfterRowOraclePreimage p (delimiterEncoding output) selector) := by
  let initial := qActualAfterFinalFlipPreimage p
    (delimiterEncoding output) selector
  let actual := qActualAfterRowOraclePreimage p
    (delimiterEncoding output) selector
  have specification : RowOracleInputSpec p output selector initial := by
    simpa [initial] using
      qActualAfterFinalFlipPreimage_rowOracleInputSpec p output selector
  have actualEqual : actual =
      (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation initial := by
    apply qActualAfterRowOraclePreimage_eq_of_runBasis
    exact applyRowOracleReferenceAndRestoreWorkCircuit_reference_some_involutive_actual output
      selector reference initial specification referenceSome
  have result := applyRowOracleReferenceAndRestoreWorkCircuit_reference_some output selector
    reference initial specification referenceSome
  rw [← actualEqual] at result
  simpa [initial, actual] using result

/-- `rowReference`受理後のactual基底は後続column oracleの入力仕様を満たす。 -/
theorem qActualAfterRowOraclePreimage_reference_some_columnInputSpec
    {p : QParameters} (output : QConfiguration p) (selector : QSelector p)
    (reference : RowReferenceResult p)
    (referenceSome : rowReference output selector = some reference) :
    ColumnOracleInputSpec p reference.input reference.columnSelector
      (qActualAfterRowOraclePreimage p (delimiterEncoding output) selector) := by
  let initial := qActualAfterFinalFlipPreimage p
    (delimiterEncoding output) selector
  let actual := qActualAfterRowOraclePreimage p
    (delimiterEncoding output) selector
  have result : RowReferenceBranchResult p reference.input
      reference.columnSelector initial actual := by
    simpa [initial, actual] using
      qActualAfterRowOraclePreimage_reference_some_result output selector reference
        referenceSome
  refine {
    column_key_bits := ?_
    selector_bits := ?_
    work_zero := ?_ }
  · rw [result.column_key]
    have initialZero : readWires (columnKeyWires p) initial =
        List.replicate (columnKeyWires p).length false := by
      simpa [initial] using qActualAfterFinalFlipPreimage_columnKey_zero p
        (delimiterEncoding output) selector
    rw [initialZero]
    simpa [xorRegisterBits, registerBitList] using
      xorRegisterBits_replicate_false
        (registerBitList (delimiterEncoding reference.input))
  · rw [result.column_selector]
    have initialZero : readWires (columnSelectorWires p) initial =
        List.replicate (columnSelectorWires p).length false := by
      simpa [initial] using qActualAfterFinalFlipPreimage_columnSelector_zero p
        (delimiterEncoding output) selector
    rw [initialZero]
    simpa [constantBits] using
      controlledXorConstantBits_true_replicate_false reference.columnSelector.val
        0 (columnSelectorWires p).length
  · intro wire workMember
    change actual wire = false
    rw [result.support_restored wire (List.mem_append_right _ workMember)]
    exact qActualAfterFinalFlipPreimage_oracleWork_zero p
      (delimiterEncoding output) selector workMember

/-- `rowReference`受理後もamplitude signalは真のままである。 -/
theorem qActualAfterRowOraclePreimage_reference_some_amplitude_true
    {p : QParameters} (output : QConfiguration p) (selector : QSelector p)
    (reference : RowReferenceResult p)
    (referenceSome : rowReference output selector = some reference) :
    qActualAfterRowOraclePreimage p (delimiterEncoding output) selector
        (amplitudeSignalWire p) = true := by
  have result := qActualAfterRowOraclePreimage_reference_some_result output
    selector reference referenceSome
  rw [result.outside_restored (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_columnKeyWires p)
    (amplitudeSignalWire_not_mem_columnSelectorWires p)
    (amplitudeSignalWire_ne_keySignalWire p)]
  exact qActualAfterFinalFlipPreimage_amplitudeSignal p
    (delimiterEncoding output) selector

/-- `rowReference`受理後もactive bitは偽のままである。 -/
theorem qActualAfterRowOraclePreimage_reference_some_active_false
    {p : QParameters} (output : QConfiguration p) (selector : QSelector p)
    (reference : RowReferenceResult p)
    (referenceSome : rowReference output selector = some reference) :
    qActualAfterRowOraclePreimage p (delimiterEncoding output) selector
        (activeWire p) = false := by
  have result := qActualAfterRowOraclePreimage_reference_some_result output
    selector reference referenceSome
  rw [result.outside_restored (activeWire p)
    (qActualActiveWire_not_mem_columnKeyWires p)
    (qActualActiveWire_not_mem_columnSelectorWires p)
    (qActualActiveWire_ne_keySignalWire p)]
  exact qActualAfterFinalFlipPreimage_active_false p
    (delimiterEncoding output) selector

/--
Row逆追跡像が合法column入力仕様を満たしてcolumnReferenceが拒否するなら、一回目の
column oracleはその基底を固定する。
-/
theorem qActualAfterColumnInversePreimage_eq_of_columnReference_none_of_row_state
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (configuration : QConfiguration p)
    (columnSelector : QSelector p)
    (rowSpecification : ColumnOracleInputSpec p configuration columnSelector
      (qActualAfterRowOraclePreimage p output rowSelector))
    (referenceNone : columnReference configuration columnSelector = none) :
    qActualAfterColumnInversePreimage p output rowSelector =
      qActualAfterRowOraclePreimage p output rowSelector := by
  rw [qActualAfterColumnInversePreimage_eq_runBasis]
  exact applyColumnOracleReferenceAndRestoreWorkCircuit_reference_none configuration columnSelector _
    rowSpecification referenceNone

/-- Column拒否pathのdiscriminator逆追跡像も同じ合法column入力仕様を保つ。 -/
theorem qActualAfterDiscriminatorPreimage_columnInputSpec_of_reference_none
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (configuration : QConfiguration p)
    (columnSelector : QSelector p)
    (rowSpecification : ColumnOracleInputSpec p configuration columnSelector
      (qActualAfterRowOraclePreimage p output rowSelector))
    (referenceNone : columnReference configuration columnSelector = none) :
    ColumnOracleInputSpec p configuration columnSelector
      (qActualAfterDiscriminatorPreimage p output rowSelector) := by
  have afterColumn : qActualAfterColumnInversePreimage p output rowSelector =
      qActualAfterRowOraclePreimage p output rowSelector :=
    qActualAfterColumnInversePreimage_eq_of_columnReference_none_of_row_state p
      output rowSelector configuration columnSelector rowSpecification referenceNone
  have beforeSpec : ColumnOracleInputSpec p configuration columnSelector
      (qActualAfterColumnInversePreimage p output rowSelector) := by
    rw [afterColumn]
    exact rowSpecification
  change ColumnOracleInputSpec p configuration columnSelector
    (cnotBasisAction (activeWire p) (amplitudeSignalWire p)
      (qActualDiscriminatorOutputPreimage p output rowSelector))
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  exact columnOracleInputSpec_afterAlignDiscriminator beforeSpec

/-- Column拒否pathでは二回目のcolumn oracle逆追跡も判別直後の基底を固定する。 -/
theorem qActualAfterColumnOraclePreimage_eq_of_columnReference_none_of_row_state
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (configuration : QConfiguration p)
    (columnSelector : QSelector p)
    (rowSpecification : ColumnOracleInputSpec p configuration columnSelector
      (qActualAfterRowOraclePreimage p output rowSelector))
    (referenceNone : columnReference configuration columnSelector = none) :
    qActualAfterColumnOraclePreimage p output rowSelector =
      qActualAfterDiscriminatorPreimage p output rowSelector := by
  apply qActualAfterColumnOraclePreimage_eq_of_runBasis
  exact applyColumnOracleReferenceAndRestoreWorkCircuit_reference_none configuration columnSelector _
    (qActualAfterDiscriminatorPreimage_columnInputSpec_of_reference_none p output
      rowSelector configuration columnSelector rowSpecification referenceNone)
    referenceNone

/-- Column拒否pathでrow逆追跡時のamplitudeが真なら整列後も真である。 -/
theorem qActualDiscriminatorOutputPreimage_amplitude_true_of_columnReference_none
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (configuration : QConfiguration p)
    (columnSelector : QSelector p)
    (rowSpecification : ColumnOracleInputSpec p configuration columnSelector
      (qActualAfterRowOraclePreimage p output rowSelector))
    (referenceNone : columnReference configuration columnSelector = none)
    (rowAmplitudeTrue : qActualAfterRowOraclePreimage p output rowSelector
      (amplitudeSignalWire p) = true) :
    qActualDiscriminatorOutputPreimage p output rowSelector
        (amplitudeSignalWire p) = true := by
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _
    (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_systemWires p)
    (amplitudeSignalWire_not_mem_rowSelectorWires p)
    (amplitudeSignalWire_ne_keySignalWire p)]
  rw [qActualAfterColumnInversePreimage_eq_of_columnReference_none_of_row_state p
    output rowSelector configuration columnSelector rowSpecification referenceNone]
  exact rowAmplitudeTrue

/-- Column拒否pathでrow逆追跡時のactiveが偽なら整列後も偽である。 -/
theorem qActualDiscriminatorOutputPreimage_active_false_of_columnReference_none
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (configuration : QConfiguration p)
    (columnSelector : QSelector p)
    (rowSpecification : ColumnOracleInputSpec p configuration columnSelector
      (qActualAfterRowOraclePreimage p output rowSelector))
    (referenceNone : columnReference configuration columnSelector = none)
    (rowActiveFalse : qActualAfterRowOraclePreimage p output rowSelector
      (activeWire p) = false) :
    qActualDiscriminatorOutputPreimage p output rowSelector
        (activeWire p) = false := by
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _ (activeWire p)
    (qActualActiveWire_not_mem_systemWires p)
    (qActualActiveWire_not_mem_rowSelectorWires p)
    (qActualActiveWire_ne_keySignalWire p)]
  rw [qActualAfterColumnInversePreimage_eq_of_columnReference_none_of_row_state p
    output rowSelector configuration columnSelector rowSpecification referenceNone]
  exact rowActiveFalse

/-- Column拒否pathでは判別CNOT後にも真のamplitude ancillaが残る。 -/
theorem qActualAfterDiscriminatorPreimage_amplitude_true_of_columnReference_none
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (configuration : QConfiguration p)
    (columnSelector : QSelector p)
    (rowSpecification : ColumnOracleInputSpec p configuration columnSelector
      (qActualAfterRowOraclePreimage p output rowSelector))
    (referenceNone : columnReference configuration columnSelector = none)
    (rowAmplitudeTrue : qActualAfterRowOraclePreimage p output rowSelector
      (amplitudeSignalWire p) = true)
    (rowActiveFalse : qActualAfterRowOraclePreimage p output rowSelector
      (activeWire p) = false) :
    qActualAfterDiscriminatorPreimage p output rowSelector
        (amplitudeSignalWire p) = true := by
  unfold qActualAfterDiscriminatorPreimage
  rw [cnotBasisAction_target,
    qActualDiscriminatorOutputPreimage_active_false_of_columnReference_none p
      output rowSelector configuration columnSelector rowSpecification
      referenceNone rowActiveFalse,
    qActualDiscriminatorOutputPreimage_amplitude_true_of_columnReference_none p
      output rowSelector configuration columnSelector rowSpecification
      referenceNone rowAmplitudeTrue]
  rfl

/--
Row逆追跡像のcanonical column仕様と二つのsignal値から、columnReference拒否pathの
actual selector振幅が0になる。
-/
theorem qActualSelectorAmplitude_eq_zero_of_columnReference_none_of_row_state
    (p : QParameters) (output input : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (configuration : QConfiguration p)
    (columnSelector : QSelector p)
    (rowSpecification : ColumnOracleInputSpec p configuration columnSelector
      (qActualAfterRowOraclePreimage p output rowSelector))
    (referenceNone : columnReference configuration columnSelector = none)
    (rowAmplitudeTrue : qActualAfterRowOraclePreimage p output rowSelector
      (amplitudeSignalWire p) = true)
    (rowActiveFalse : qActualAfterRowOraclePreimage p output rowSelector
      (activeWire p) = false) :
    qActualSelectorAmplitude p output input rowSelector = 0 := by
  have preparedAmplitude : qActualColumnPreparedPreimage p output rowSelector
      (amplitudeSignalWire p) = true := by
    rw [qActualColumnPreparedPreimage_eq_stages,
      copyToBasisPermutation_amplitudeSignal,
      qActualAfterColumnOraclePreimage_eq_of_columnReference_none_of_row_state p
        output rowSelector configuration columnSelector rowSpecification
        referenceNone]
    exact qActualAfterDiscriminatorPreimage_amplitude_true_of_columnReference_none
      p output rowSelector configuration columnSelector rowSpecification
      referenceNone rowAmplitudeTrue rowActiveFalse
  unfold qActualSelectorAmplitude
  apply qBeforeRowUniformInverseState_finalSelector_eq_zero p input output
    rowSelector
  exact qColumnPreparedState_eq_zero_of_amplitude_true p input _ preparedAmplitude

/--
合法row参照がpredecessorを返しても、そのcolumn参照が拒否するpathのactual振幅は0である。
-/
theorem qActualSelectorAmplitude_eq_zero_of_columnReference_none_of_input_eq
    (p : QParameters) (output input : QConfiguration p)
    (rowSelector : QSelector p) (rowResult : RowReferenceResult p)
    (rowAccepted : rowReference output rowSelector = some rowResult)
    (columnRejected : columnReference input rowResult.columnSelector = none)
    (inputEqual : rowResult.input = input) :
    qActualSelectorAmplitude p (delimiterEncoding output)
      (delimiterEncoding input) rowSelector = 0 := by
  subst input
  apply qActualSelectorAmplitude_eq_zero_of_columnReference_none_of_row_state p
    (delimiterEncoding output) (delimiterEncoding rowResult.input) rowSelector
    rowResult.input
    rowResult.columnSelector
  · exact qActualAfterRowOraclePreimage_reference_some_columnInputSpec output
      rowSelector rowResult rowAccepted
  · exact columnRejected
  · exact qActualAfterRowOraclePreimage_reference_some_amplitude_true output
      rowSelector rowResult rowAccepted
  · exact qActualAfterRowOraclePreimage_reference_some_active_false output
      rowSelector rowResult rowAccepted

/--
非合法な物理system基底は、どの合法配置から作るcanonical column基底ともselector外で
一致しない。
-/
theorem not_outsideColumnSelectorMatches_of_illegal_system_canonical
    (p : QParameters) (input : RegisterBasis p.systemWidth)
    (configuration : QConfiguration p) (columnSelector : QSelector p)
    (illegal : decodeDelimiter input = none) :
    ¬OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p input)
      (qCanonicalColumnInitialBasis p configuration columnSelector) := by
  intro inputMatches
  have canonicalMatches :=
    qCanonicalColumnInitialBasis_outsideMatches p configuration columnSelector
  have inputEqual : input = delimiterEncoding configuration := by
    funext index
    let wire : Wire p.ancillaWidth p.systemWidth := .system index
    have outsideSelector : wire ∉
        selectorSliceWires p (columnSelectorWire p) := by
      simp [wire, selectorSliceWires, columnSelectorWire,
        RegisterSlice.ancillaWire]
    have inputAt := inputMatches wire outsideSelector
    have canonicalAt := canonicalMatches wire outsideSelector
    change qCanonicalColumnInitialBasis p configuration columnSelector wire =
      zeroAncillaJointBasis p input wire at inputAt
    change qCanonicalColumnInitialBasis p configuration columnSelector wire =
      zeroAncillaJointBasis p (delimiterEncoding configuration) wire at canonicalAt
    simpa [wire] using inputAt.symm.trans canonicalAt
  rw [inputEqual, decodeDelimiter_encoding] at illegal
  contradiction

/--
actual逆追跡像が合法配置のcanonical column基底なら、非合法な物理入力に対する振幅は
selector外不一致により0である。
-/
theorem qActualSelectorAmplitude_eq_zero_of_illegal_input_of_canonical_preimage
    (p : QParameters) (output input : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (configuration : QConfiguration p)
    (columnSelector : QSelector p)
    (preimageEqual : qActualColumnPreparedPreimage p output rowSelector =
      qCanonicalColumnInitialBasis p configuration columnSelector)
    (illegal : decodeDelimiter input = none) :
    qActualSelectorAmplitude p output input rowSelector = 0 := by
  unfold qActualSelectorAmplitude
  apply qBeforeRowUniformInverseState_finalSelector_eq_zero_of_outside_mismatch
  rw [preimageEqual]
  exact not_outsideColumnSelectorMatches_of_illegal_system_canonical p input
    configuration columnSelector illegal

/-- 異なる二つの合法配置に対応するcanonical背景はselector外で一致しない。 -/
theorem not_outsideColumnSelectorMatches_of_configuration_ne_canonical
    (p : QParameters) (input configuration : QConfiguration p)
    (columnSelector : QSelector p) (different : configuration ≠ input) :
    ¬OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding input))
      (qCanonicalColumnInitialBasis p configuration columnSelector) := by
  intro inputMatches
  have canonicalMatches :=
    qCanonicalColumnInitialBasis_outsideMatches p configuration columnSelector
  have encodingEqual : delimiterEncoding input = delimiterEncoding configuration := by
    funext index
    let wire : Wire p.ancillaWidth p.systemWidth := .system index
    have outsideSelector : wire ∉
        selectorSliceWires p (columnSelectorWire p) := by
      simp [wire, selectorSliceWires, columnSelectorWire,
        RegisterSlice.ancillaWire]
    have inputAt := inputMatches wire outsideSelector
    have canonicalAt := canonicalMatches wire outsideSelector
    change qCanonicalColumnInitialBasis p configuration columnSelector wire =
      zeroAncillaJointBasis p (delimiterEncoding input) wire at inputAt
    change qCanonicalColumnInitialBasis p configuration columnSelector wire =
      zeroAncillaJointBasis p (delimiterEncoding configuration) wire at canonicalAt
    simpa [wire] using inputAt.symm.trans canonicalAt
  exact different (delimiterEncoding_injective encodingEqual).symm

/--
actual逆追跡像がある合法配置のcanonical column基底であり、入力配置がそれと異なるなら
selector外不一致により振幅は0である。
-/
theorem qActualSelectorAmplitude_eq_zero_of_configuration_ne_of_canonical_preimage
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (input configuration : QConfiguration p) (rowSelector : QSelector p)
    (columnSelector : QSelector p)
    (preimageEqual : qActualColumnPreparedPreimage p output rowSelector =
      qCanonicalColumnInitialBasis p configuration columnSelector)
    (different : configuration ≠ input) :
    qActualSelectorAmplitude p output (delimiterEncoding input) rowSelector = 0 := by
  unfold qActualSelectorAmplitude
  apply qBeforeRowUniformInverseState_finalSelector_eq_zero_of_outside_mismatch
  rw [preimageEqual]
  exact not_outsideColumnSelectorMatches_of_configuration_ne_canonical p input
    configuration columnSelector different

end

end ProbabilityGeneratorQProof
