import QLean.Generator.Implementation.QActualSelectorPathCorrectness

/-!
# Q正本回路の物理event受理path完全性

物理eventのcanonical selectorについて、row oracle、column oracle、整列回路、
discriminator、column uncompute、COPYを逆順に追跡し、最終selector振幅を厳密に求める。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

open ReversibleCircuit

/-- 同じbit列同士のXORは同じ長さの全0列になる。 -/
theorem xorRegisterBits_self_eq_replicate_false (bits : List Bool) :
    xorRegisterBits bits bits = List.replicate bits.length false := by
  induction bits with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      change (if bit then !bit else bit) :: xorRegisterBits bits bits =
        false :: List.replicate bits.length false
      rw [inductionHypothesis]
      cases bit <;> rfl

/-- register読出しが全0列なら、そのregister中の各wireも0である。 -/
theorem readWires_eq_replicate_false_at
    {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (input : JointBasis ancillaQubits systemQubits)
    (values : readWires wires input = List.replicate wires.length false)
    {wire : Wire ancillaQubits systemQubits} (member : wire ∈ wires) :
    input wire = false := by
  let zero : JointBasis ancillaQubits systemQubits := fun _ => false
  have readsEqual : readWires wires input = readWires wires zero := by
    rw [values]
    simp [zero, readWires]
  exact readWires_eq_at_of_eq wires input zero readsEqual member

/-- 物理eventのdiscriminator逆追跡後はamplitude signalが0へ戻る。 -/
theorem qActualAfterDiscriminatorPreimage_physicalEvent_amplitude_false
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualAfterDiscriminatorPreimage p (delimiterEncoding output) rowSelector
        (amplitudeSignalWire p) = false := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  have referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference := by
    simpa [output, rowSelector, reference] using
      columnReference_selectorForEvent_exact configuration source member direction
  unfold qActualAfterDiscriminatorPreimage
  rw [cnotBasisAction_target]
  rw [qActualDiscriminatorOutputPreimage_physicalEvent_active_true
    configuration source member direction reference referenceSome]
  rw [qActualDiscriminatorOutputPreimage_physicalEvent_amplitude_true
    configuration source member direction reference referenceSome]
  rfl

/-- 物理eventのdiscriminator逆追跡後はrow-selector accumulatorが全0へ戻る。 -/
theorem qActualAfterDiscriminatorPreimage_physicalEvent_rowSelector_zero
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    readWires (rowSelectorWires p)
        (qActualAfterDiscriminatorPreimage p (delimiterEncoding output)
          rowSelector) = List.replicate (rowSelectorWires p).length false := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding output) rowSelector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding output) rowSelector
  have referenceSome : columnReference configuration columnSelector =
      some reference := by
    simpa [output, rowSelector, columnSelector, reference] using
      columnReference_selectorForEvent_exact configuration source member direction
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [output, rowSelector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_physicalEvent_result configuration source
        member direction reference referenceSome
  have afterRowSpec : RowOracleInputSpec p output rowSelector afterRow := by
    have rowResult := qActualAfterRowOraclePreimage_physicalEvent_result
      configuration source member direction
    exact RowReferenceBranchResult.preservesInputSpec
      (qActualAfterFinalFlipPreimage_rowOracleInputSpec p output rowSelector)
      rowResult
  have rowSelectorAfterColumn : readWires (rowSelectorWires p) afterColumn =
      constantBits rowSelector.val (rowSelectorWires p).length := by
    calc
      readWires (rowSelectorWires p) afterColumn =
          readWires (rowSelectorWires p) afterRow := by
        apply List.map_congr_left
        intro wire wireMember
        exact firstResult.outside_restored wire
          ((List.disjoint_left.mp
            (qActualRowOutputWires_disjoint_rowSelectorWires p).symm)
              wireMember)
          ((List.disjoint_left.mp
            (qTopSelectorOutputWires_disjoint_rowSelectorWires p).symm)
              wireMember)
          (by
            intro equal
            exact qActualNegativeWire_not_mem_rowSelectorWires p
              (equal ▸ wireMember))
          (by
            intro equal
            exact qActualActiveWire_not_mem_rowSelectorWires p
              (equal ▸ wireMember))
      _ = constantBits rowSelector.val (rowSelectorWires p).length :=
        afterRowSpec.selector_bits
  have selectorOutputAfterColumn :
      readWires (selectorOutputWires p) afterColumn =
        constantBits rowSelector.val (selectorOutputWires p).length := by
    rw [firstResult.selector_output,
      qActualAfterRowOraclePreimage_physicalEvent_selectorOutput_zero
        configuration source member direction]
    simpa [reference, constantBits, controlledXorConstantBits] using
      controlledXorConstantBits_true_replicate_false rowSelector.val 0
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
  rw [qActualAfterColumnInversePreimage_physicalEvent_amplitude_true
    configuration source member direction reference referenceSome]
  rw [selectorOutputAfterColumn, rowSelectorAfterColumn]
  rw [if_pos rfl]
  rw [xorRegisterBits_self_eq_replicate_false]
  simp [constantBits]

/-- 物理eventのdiscriminator逆追跡後はkey-signal bitが0へ戻る。 -/
theorem qActualAfterDiscriminatorPreimage_physicalEvent_keySignal_false
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualAfterDiscriminatorPreimage p (delimiterEncoding output) rowSelector
        (keySignalWire p) = false := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let afterFinal := qActualAfterFinalFlipPreimage p
    (delimiterEncoding output) rowSelector
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding output) rowSelector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding output) rowSelector
  have referenceSome : columnReference configuration columnSelector =
      some reference := by
    simpa [output, rowSelector, columnSelector, reference] using
      columnReference_selectorForEvent_exact configuration source member direction
  have rowResult : RowReferenceBranchResult p configuration columnSelector
      afterFinal afterRow := by
    simpa [output, rowSelector, columnSelector, afterFinal, afterRow] using
      qActualAfterRowOraclePreimage_physicalEvent_result configuration source
        member direction
  have columnResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [output, rowSelector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_physicalEvent_result configuration source
        member direction reference referenceSome
  have afterRowKey : afterRow (keySignalWire p) = true := by
    rw [rowResult.key_signal]
    rw [show afterFinal (keySignalWire p) = false by
      simp [afterFinal]]
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
  rw [qActualAfterColumnInversePreimage_physicalEvent_amplitude_true
    configuration source member direction reference referenceSome]
  rw [show qActualAfterColumnInversePreimage p
      (delimiterEncoding (eventOutput configuration source direction))
      (rowSelectorForEvent configuration source member direction)
      (keySignalWire p) = true by
    simpa [afterColumn, output, rowSelector] using afterColumnKey]
  rw [if_pos rfl]
  rfl

/-- 物理eventの二回目column oracle後もsystem registerはpredecessor配置である。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_readSystem
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    readWires (systemWires p)
        (qActualAfterColumnOraclePreimage p (delimiterEncoding output)
          rowSelector) = registerBitList (delimiterEncoding configuration) := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding output) rowSelector
  have result : ColumnReferenceBranchResult p reference before actual := by
    simpa [output, rowSelector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_result configuration source
        member direction
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
          exact qActualNegativeWire_not_mem_systemWires p
            (equal ▸ wireMember))
        (by
          intro equal
          exact qActualActiveWire_not_mem_systemWires p
            (equal ▸ wireMember))
    _ = registerBitList (delimiterEncoding configuration) := by
      simpa [before, output, rowSelector] using
        qActualAfterDiscriminatorPreimage_physicalEvent_readSystem configuration
          source member direction

/-- 物理eventの二回目column oracle後もrow-selector accumulatorは全0である。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_rowSelector_zero
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    readWires (rowSelectorWires p)
        (qActualAfterColumnOraclePreimage p (delimiterEncoding output)
          rowSelector) = List.replicate (rowSelectorWires p).length false := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding output) rowSelector
  have result : ColumnReferenceBranchResult p reference before actual := by
    simpa [output, rowSelector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_result configuration source
        member direction
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
      simpa [before, output, rowSelector] using
        qActualAfterDiscriminatorPreimage_physicalEvent_rowSelector_zero
          configuration source member direction

/-- 物理eventの二回目column oracle後もkey-signal bitは0である。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_keySignal_false
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualAfterColumnOraclePreimage p (delimiterEncoding output) rowSelector
        (keySignalWire p) = false := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding output) rowSelector
  have result : ColumnReferenceBranchResult p reference before actual := by
    simpa [output, rowSelector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_result configuration source
        member direction
  change actual (keySignalWire p) = false
  rw [result.outside_restored (keySignalWire p)
    (qActualKeySignalWire_not_mem_rowOutputWires p)
    (qActualKeySignalWire_not_mem_selectorOutputWires p)
    (qActualNegativeWire_ne_keySignalWire p).symm
    (qActualActiveWire_ne_keySignalWire p).symm]
  simpa [before, output, rowSelector] using
    qActualAfterDiscriminatorPreimage_physicalEvent_keySignal_false configuration
      source member direction

/-- 物理eventの二回目column oracle後もamplitude signalは0である。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_amplitude_false
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualAfterColumnOraclePreimage p (delimiterEncoding output) rowSelector
        (amplitudeSignalWire p) = false := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding output) rowSelector
  have result : ColumnReferenceBranchResult p reference before actual := by
    simpa [output, rowSelector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_result configuration source
        member direction
  change actual (amplitudeSignalWire p) = false
  rw [result.outside_restored (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_rowOutputWires p)
    (amplitudeSignalWire_not_mem_selectorOutputWires p)
    (negativeWire_ne_amplitudeSignalWire p).symm
    (activeWire_ne_amplitudeSignalWire p).symm]
  simpa [before, output, rowSelector] using
    qActualAfterDiscriminatorPreimage_physicalEvent_amplitude_false configuration
      source member direction

/-- 二回目column oracle後もpredecessor column-key・selector・clean work仕様を満たす。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_columnInputSpec
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    ColumnOracleInputSpec p configuration
      (selectorForEvent configuration source member direction)
      (qActualAfterColumnOraclePreimage p (delimiterEncoding output)
        rowSelector) := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding output) rowSelector
  have inputSpec : ColumnOracleInputSpec p configuration columnSelector before := by
    simpa [output, rowSelector, columnSelector, before] using
      qActualAfterDiscriminatorPreimage_physicalEvent_columnInputSpec
        configuration source member direction
  have result : ColumnReferenceBranchResult p reference before actual := by
    simpa [output, rowSelector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_result configuration source
        member direction
  exact ColumnReferenceBranchResult.preservesInputSpec inputSpec result

/-- 二回目column oracle後はsystem・column-key・column-selector外の全wireが0である。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_outside_zero
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideSystem : wire ∉ systemWires p)
    (outsideColumnKey : wire ∉ columnKeyWires p)
    (outsideColumnSelector : wire ∉ columnSelectorWires p) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualAfterColumnOraclePreimage p (delimiterEncoding output) rowSelector wire =
      false := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let afterFinal := qActualAfterFinalFlipPreimage p
    (delimiterEncoding output) rowSelector
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding output) rowSelector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding output) rowSelector
  let before := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding output) rowSelector
  by_cases rowSelectorMember : wire ∈ rowSelectorWires p
  · exact readWires_eq_replicate_false_at (rowSelectorWires p)
      (qActualAfterColumnOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction))
      (qActualAfterColumnOraclePreimage_physicalEvent_rowSelector_zero
        configuration source member direction) rowSelectorMember
  by_cases rowOutputMember : wire ∈ rowOutputWires p
  · exact readWires_eq_replicate_false_at (rowOutputWires p)
      (qActualAfterColumnOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction))
      (qActualAfterColumnOraclePreimage_physicalEvent_rowOutput_zero
        configuration source member direction) rowOutputMember
  by_cases selectorOutputMember : wire ∈ selectorOutputWires p
  · exact readWires_eq_replicate_false_at (selectorOutputWires p)
      (qActualAfterColumnOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction))
      (qActualAfterColumnOraclePreimage_physicalEvent_selectorOutput_zero
        configuration source member direction) selectorOutputMember
  by_cases keyEqual : wire = keySignalWire p
  · subst wire
    exact qActualAfterColumnOraclePreimage_physicalEvent_keySignal_false
      configuration source member direction
  by_cases amplitudeEqual : wire = amplitudeSignalWire p
  · subst wire
    exact qActualAfterColumnOraclePreimage_physicalEvent_amplitude_false
      configuration source member direction
  by_cases negativeEqual : wire = negativeWire p
  · subst wire
    exact qActualAfterColumnOraclePreimage_physicalEvent_negative_false
      configuration source member direction
  by_cases activeEqual : wire = activeWire p
  · subst wire
    exact qActualAfterColumnOraclePreimage_physicalEvent_active_false
      configuration source member direction
  have referenceSome : columnReference configuration columnSelector =
      some reference := by
    simpa [output, rowSelector, columnSelector, reference] using
      columnReference_selectorForEvent_exact configuration source member direction
  have rowResult : RowReferenceBranchResult p configuration columnSelector
      afterFinal afterRow := by
    simpa [output, rowSelector, columnSelector, afterFinal, afterRow] using
      qActualAfterRowOraclePreimage_physicalEvent_result configuration source
        member direction
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [output, rowSelector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_physicalEvent_result configuration source
        member direction reference referenceSome
  have secondResult : ColumnReferenceBranchResult p reference before actual := by
    simpa [output, rowSelector, reference, before, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_result configuration source
        member direction
  change actual wire = false
  rw [secondResult.outside_restored wire rowOutputMember selectorOutputMember
    negativeEqual activeEqual]
  rw [show before wire = afterColumn wire by
    exact qActualAfterDiscriminatorPreimage_eq_afterColumnInverse_on_wire p
      (delimiterEncoding output) rowSelector wire outsideSystem rowSelectorMember
      keyEqual amplitudeEqual]
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

/-- canonical column初期基底へCOPYを適用した基底。 -/
def qCanonicalColumnCopiedBasis (p : QParameters)
    (configuration : QConfiguration p) (selector : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
    reversibleGatePermutation
    (qCanonicalColumnInitialBasis p configuration selector)

/-- canonical column初期基底のsystem読出しはdelimiter符号である。 -/
theorem qCanonicalColumnInitialBasis_readSystem
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    readWires (systemWires p)
        (qCanonicalColumnInitialBasis p configuration selector) =
      registerBitList (delimiterEncoding configuration) := by
  unfold qCanonicalColumnInitialBasis qColumnInitialBasisOfNat
  rw [readWires_selectorBasisOver_of_disjoint p (columnSelectorWire p)
    (zeroAncillaJointBasis p (delimiterEncoding configuration))
    (selectorBasisOfNat p.selectorWidth selector.val) (systemWires p)]
  · exact readWires_systemWires_zeroAncilla p
      (delimiterEncoding configuration)
  · simpa only [← columnSelectorWires_eq_selectorSliceWires] using
      (qActualColumnSelectorWires_disjoint_systemWires p).symm

/-- canonical column初期基底のcolumn-selector読出しは指定定数である。 -/
theorem qCanonicalColumnInitialBasis_readColumnSelector
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    readWires (columnSelectorWires p)
        (qCanonicalColumnInitialBasis p configuration selector) =
      constantBits selector.val (columnSelectorWires p).length := by
  rw [columnSelectorWires_eq_selectorSliceWires]
  simp only [selectorSliceWires, List.length_map, List.length_finRange]
  apply (readWires_selectorSlice_eq_constantBits_iff p (columnSelectorWire p)
    (qCanonicalColumnInitialBasis p configuration selector) selector.val
    (qSelector_lt_capacity p selector)).2
  rw [projectColumnSelector_qCanonicalColumnInitialBasis]
  exact selectorValue_selectorBasisOfNat p.selectorWidth selector.val
    (qSelector_lt_capacity p selector)

/-- canonical column初期基底はsystem・column-selector外で全0である。 -/
theorem qCanonicalColumnInitialBasis_outside_zero
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideSystem : wire ∉ systemWires p)
    (outsideSelector : wire ∉ columnSelectorWires p) :
    qCanonicalColumnInitialBasis p configuration selector wire = false := by
  unfold qCanonicalColumnInitialBasis qColumnInitialBasisOfNat
  rw [selectorBasisOver_apply_outside p (columnSelectorWire p)
    (zeroAncillaJointBasis p (delimiterEncoding configuration))
    (selectorBasisOfNat p.selectorWidth selector.val) wire]
  · cases wire with
    | ancilla index => rfl
    | system index =>
        exfalso
        apply outsideSystem
        exact List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩
  · simpa only [← columnSelectorWires_eq_selectorSliceWires] using
      outsideSelector

/-- canonical COPY後基底のsystem読出しはdelimiter符号のままである。 -/
theorem qCanonicalColumnCopiedBasis_readSystem
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    readWires (systemWires p)
        (qCanonicalColumnCopiedBasis p configuration selector) =
      registerBitList (delimiterEncoding configuration) := by
  unfold qCanonicalColumnCopiedBasis
  rw [show systemWires p = topSystemWires p by rfl]
  rw [xorSystemIntoColumnKey_runBasis_readSystem]
  exact qCanonicalColumnInitialBasis_readSystem p configuration selector

/-- canonical COPY後基底のcolumn-key読出しはdelimiter符号になる。 -/
theorem qCanonicalColumnCopiedBasis_readColumnKey
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    readWires (columnKeyWires p)
        (qCanonicalColumnCopiedBasis p configuration selector) =
      registerBitList (delimiterEncoding configuration) := by
  unfold qCanonicalColumnCopiedBasis
  rw [show columnKeyWires p = topColumnKeyWires p by rfl]
  rw [copy_qCanonicalColumnInitialBasis_readColumnKey_eq_system]
  exact qCanonicalColumnInitialBasis_readSystem p configuration selector

/-- canonical COPY後基底のcolumn-selector読出しは指定定数のままである。 -/
theorem qCanonicalColumnCopiedBasis_readColumnSelector
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p) :
    readWires (columnSelectorWires p)
        (qCanonicalColumnCopiedBasis p configuration selector) =
      constantBits selector.val (columnSelectorWires p).length := by
  unfold qCanonicalColumnCopiedBasis
  rw [xorSystemIntoColumnKey_runBasis_readWires_outside p _
    (columnSelectorWires p)]
  · exact qCanonicalColumnInitialBasis_readColumnSelector p configuration
      selector
  · rw [← columnKeyWires_eq_topColumnKeyWires]
    rw [List.disjoint_left]
    intro wire selectorMember keyMember
    rcases List.mem_map.mp selectorMember with
      ⟨selectorIndex, _, selectorEqual⟩
    rcases List.mem_map.mp keyMember with ⟨keyIndex, _, keyEqual⟩
    have numbers := congrArg wireNumber (selectorEqual.trans keyEqual.symm)
    simp [columnSelectorWire, columnKeyWire, QLayout.canonical,
      RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
    omega

/-- canonical COPY後基底はsystem・column-key・column-selector外で全0である。 -/
theorem qCanonicalColumnCopiedBasis_outside_zero
    (p : QParameters) (configuration : QConfiguration p)
    (selector : QSelector p)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideSystem : wire ∉ systemWires p)
    (outsideKey : wire ∉ columnKeyWires p)
    (outsideSelector : wire ∉ columnSelectorWires p) :
    qCanonicalColumnCopiedBasis p configuration selector wire = false := by
  unfold qCanonicalColumnCopiedBasis
  rw [xorSystemIntoColumnKey_runBasis_outside p _ wire]
  · exact qCanonicalColumnInitialBasis_outside_zero p configuration selector
      wire outsideSystem outsideSelector
  · simpa only [← columnKeyWires_eq_topColumnKeyWires] using outsideKey

/-- 二回目column oracle後の物理event基底はcanonical COPY後基底に厳密一致する。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_eq_copied
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    let columnSelector := selectorForEvent configuration source member direction
    qActualAfterColumnOraclePreimage p (delimiterEncoding output) rowSelector =
      qCanonicalColumnCopiedBasis p configuration columnSelector := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding output) rowSelector
  let copied := qCanonicalColumnCopiedBasis p configuration columnSelector
  have actualSpec : ColumnOracleInputSpec p configuration columnSelector actual := by
    simpa [output, rowSelector, columnSelector, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_columnInputSpec
        configuration source member direction
  have actualSystem : readWires (systemWires p) actual =
      registerBitList (delimiterEncoding configuration) := by
    simpa [output, rowSelector, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_readSystem configuration
        source member direction
  have copiedSystem : readWires (systemWires p) copied =
      registerBitList (delimiterEncoding configuration) := by
    simpa [copied, columnSelector] using
      qCanonicalColumnCopiedBasis_readSystem p configuration columnSelector
  have copiedKey : readWires (columnKeyWires p) copied =
      registerBitList (delimiterEncoding configuration) := by
    simpa [copied, columnSelector] using
      qCanonicalColumnCopiedBasis_readColumnKey p configuration columnSelector
  have copiedSelector : readWires (columnSelectorWires p) copied =
      constantBits columnSelector.val (columnSelectorWires p).length := by
    simpa [copied] using
      qCanonicalColumnCopiedBasis_readColumnSelector p configuration
        columnSelector
  change actual = copied
  funext wire
  by_cases systemMember : wire ∈ systemWires p
  · apply readWires_eq_at_of_eq (systemWires p) actual copied
    · exact actualSystem.trans copiedSystem.symm
    · exact systemMember
  by_cases keyMember : wire ∈ columnKeyWires p
  · apply readWires_eq_at_of_eq (columnKeyWires p) actual copied
    · exact actualSpec.column_key_bits.trans copiedKey.symm
    · exact keyMember
  by_cases selectorMember : wire ∈ columnSelectorWires p
  · apply readWires_eq_at_of_eq (columnSelectorWires p) actual copied
    · exact actualSpec.selector_bits.trans copiedSelector.symm
    · exact selectorMember
  rw [show actual wire = false by
    simpa [output, rowSelector, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_outside_zero configuration
        source member direction wire systemMember keyMember selectorMember]
  exact (qCanonicalColumnCopiedBasis_outside_zero p configuration
    columnSelector wire systemMember keyMember selectorMember).symm

/-- 物理eventの全逆追跡preimageはcanonical column初期基底に厳密一致する。 -/
theorem qActualColumnPreparedPreimage_physicalEvent_eq_canonical
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    let columnSelector := selectorForEvent configuration source member direction
    qActualColumnPreparedPreimage p (delimiterEncoding output) rowSelector =
      qCanonicalColumnInitialBasis p configuration columnSelector := by
  dsimp only
  apply qActualColumnPreparedPreimage_eq_of_copy_runBasis
  exact (qActualAfterColumnOraclePreimage_physicalEvent_eq_copied configuration
    source member direction).symm

/-- 物理event受理pathの位相は正である。 -/
theorem qActualSelectorPathPhase_physicalEvent_eq_one
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualSelectorPathPhase p (delimiterEncoding output) rowSelector = 1 := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  have referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference := by
    simpa [output, rowSelector, reference] using
      columnReference_selectorForEvent_exact configuration source member direction
  have phase := qActualSelectorPathPhase_eq_of_signals p
    (delimiterEncoding output) rowSelector false
    (by
      simpa [reference] using
        qActualDiscriminatorOutputPreimage_physicalEvent_negative_eq
          configuration source member direction reference referenceSome)
    (qActualDiscriminatorOutputPreimage_physicalEvent_amplitude_true
      configuration source member direction reference referenceSome)
  simpa using phase

/-- 物理eventのcanonical row selectorに対するactual振幅は一様正振幅である。 -/
theorem qActualSelectorAmplitude_physicalEvent
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualSelectorAmplitude p (delimiterEncoding output)
        (delimiterEncoding configuration) rowSelector =
      ((1 / Real.sqrt (p.selectorCount : ℝ)) : ℂ) := by
  dsimp only
  unfold qActualSelectorAmplitude
  rw [qBeforeRowUniformInverseState_finalSelector_of_canonical_preimage p
    configuration (eventOutput configuration source direction)
    (rowSelectorForEvent configuration source member direction)
    (selectorForEvent configuration source member direction) false
    (qActualColumnPreparedPreimage_physicalEvent_eq_canonical configuration
      source member direction)
    (qActualSelectorPathPhase_physicalEvent_eq_one configuration source member
      direction)]
  simp

/-- 物理イベントの canonical row selector では、actual 振幅が参照関数の期待振幅に一致する。 -/
theorem qActualSelectorAmplitude_physicalEvent_eq_expected
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualSelectorAmplitude p (delimiterEncoding output)
        (delimiterEncoding configuration) rowSelector =
      PrefixAmplitudeReferenceCaseSpec p (delimiterEncoding output)
        (delimiterEncoding configuration) rowSelector := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let rowResult : RowReferenceResult p :=
    { input := configuration, columnSelector := columnSelector }
  let columnResult : ColumnReferenceResult p :=
    { output := output, rowSelector := rowSelector, negative := false }
  have rowAccepted : rowReference output rowSelector = some rowResult := by
    simpa [output, rowSelector, columnSelector, rowResult] using
      rowReference_rowSelectorForEvent configuration source member direction
  have columnAccepted : columnReference configuration columnSelector =
      some columnResult := by
    simpa [output, rowSelector, columnSelector, columnResult] using
      columnReference_selectorForEvent_exact configuration source member direction
  have expected := PrefixAmplitudeReferenceCaseSpec_of_accepted
    output configuration rowSelector rowResult columnResult rowAccepted
      columnAccepted (by rfl) (by rfl) (by rfl)
  rw [qActualSelectorAmplitude_physicalEvent configuration source member direction]
  simpa [columnResult] using expected.symm

end

end ProbabilityGeneratorQProof
