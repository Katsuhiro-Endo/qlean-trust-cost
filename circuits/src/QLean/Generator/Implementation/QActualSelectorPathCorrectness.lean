import QLean.Generator.Implementation.QTopLevelBasisPipeline
import QLean.Generator.Implementation.QEndToEndSelectorAssembly
import QLean.Generator.Implementation.QOracleEventComputeLocality
import QLean.Generator.Implementation.QOracleRowEventComplete
import QLean.Generator.Implementation.QOracleColumnFullCorrectness
import QLean.Generator.Implementation.QOracleRowIllegalInputCorrectness

/-!
# Q正本回路のselector一本ごとの実path合成

最終row selector基底から正本回路を逆追跡した基底を明示し、初期column一様準備の
振幅へ戻す一般補題をまとめる。column/row oracleの完全な基底作用定理は、完成後に
この層へ接続する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

open ReversibleCircuit

/-- selector sliceと交わらないwire列は、selector上書き後も背景と同じbit列を保持する。 -/
theorem readWires_selectorBasisOver_of_disjoint
    (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (background : JointBasis p.ancillaWidth p.systemWidth)
    (selectorBasis : AbstractSelectorBasis p.selectorWidth)
    (wires : List (Wire p.ancillaWidth p.systemWidth))
    (disjoint : wires.Disjoint (selectorSliceWires p selectorWire)) :
    readWires wires
        (selectorBasisOver p selectorWire background selectorBasis) =
      readWires wires background := by
  apply List.map_congr_left
  intro wire member
  exact selectorBasisOver_apply_outside p selectorWire background selectorBasis
    wire ((List.disjoint_left.mp disjoint) member)

/-- canonical最終row-selector基底のsystem読出しは指定物理system基底に一致する。 -/
theorem qFinalRowSelectorBasis_readSystem
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    readWires (systemWires p) (qFinalRowSelectorBasis p output rowSelector) =
      registerBitList output := by
  unfold qFinalRowSelectorBasis
  rw [readWires_selectorBasisOver_of_disjoint p (rowSelectorWire p)
    (zeroAncillaJointBasis p output)
    (selectorBasisOfNat p.selectorWidth rowSelector.val)
    (systemWires p)]
  · exact readWires_systemWires_zeroAncilla p output
  · simpa only [← rowSelectorWires_eq_selectorSliceWires] using
      qTopSystemWires_disjoint_rowSelectorWires p

/-- canonical最終row-selector基底のselector読出しは指定定数bit列に一致する。 -/
theorem qFinalRowSelectorBasis_readRowSelector
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    readWires (rowSelectorWires p)
        (qFinalRowSelectorBasis p output rowSelector) =
      constantBits rowSelector.val (rowSelectorWires p).length := by
  rw [rowSelectorWires_eq_selectorSliceWires]
  simp only [selectorSliceWires, List.length_map, List.length_finRange]
  apply (readWires_selectorSlice_eq_constantBits_iff p (rowSelectorWire p)
    (qFinalRowSelectorBasis p output rowSelector) rowSelector.val
    (qSelector_lt_capacity p rowSelector)).2
  rw [qFinalRowSelectorBasis,
    projectSelectorBasis_selectorBasisOver p (rowSelectorWire p)
      (sharedRowSelectorWire_injective p)]
  exact selectorValue_selectorBasisOfNat p.selectorWidth rowSelector.val
    (qSelector_lt_capacity p rowSelector)

/-- oracle workの各wireはrow selector sliceには属さない。 -/
theorem diagonalOracleWorkWire_not_mem_rowSelectorSlice
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ diagonalOracleWorkWires p) :
    wire ∉ selectorSliceWires p (rowSelectorWire p) := by
  intro selectorMember
  rcases List.mem_map.mp selectorMember with ⟨selectorIndex, _, selectorEqual⟩
  rcases List.mem_map.mp member with ⟨workIndex, _, workEqual⟩
  have numbers := congrArg wireNumber (selectorEqual.trans workEqual.symm)
  simp [rowSelectorWire, QLayout.canonical, RegisterSlice.ancillaWire,
    RegisterSlice.index, wireNumber] at numbers
  omega

/-- oracle workの各wireはamplitude signalとは異なる。 -/
theorem diagonalOracleWorkWire_ne_amplitudeSignal
    (p : QParameters) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ diagonalOracleWorkWires p) :
    wire ≠ amplitudeSignalWire p := by
  intro equal
  rcases List.mem_map.mp member with ⟨workIndex, _, workEqual⟩
  have numbers := congrArg wireNumber (workEqual.trans equal)
  simp [amplitudeSignalWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- canonical最終row-selector基底ではoracle work全体が0のままである。 -/
theorem qFinalRowSelectorBasis_oracleWork_zero
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ diagonalOracleWorkWires p) :
    qFinalRowSelectorBasis p output rowSelector wire = false := by
  unfold qFinalRowSelectorBasis
  rw [selectorBasisOver_apply_outside p (rowSelectorWire p)
    (zeroAncillaJointBasis p output)
    (selectorBasisOfNat p.selectorWidth rowSelector.val) wire
    (diagonalOracleWorkWire_not_mem_rowSelectorSlice p member)]
  rcases List.mem_map.mp member with ⟨workIndex, _, rfl⟩
  rfl

/-- 正方向の厳密な基底作用等式を、状態作用で使う逆置換の等式へ変換する。 -/
theorem toBasisPermutation_apply_of_runBasis_eq
    {p : QParameters}
    (circuit : Circuit (ReversibleGate p.ancillaWidth p.systemWidth))
    (input output : JointBasis p.ancillaWidth p.systemWidth)
    (executed : circuit.runBasis reversibleGatePermutation input = output) :
    circuit.toBasisPermutation reversibleGatePermutation output = input := by
  rw [Circuit.toBasisPermutation_eq_execution_inverse reversibleGatePermutation
    (by intro gate; cases gate <;> rfl)]
  rw [← executed]
  exact Equiv.symm_apply_apply _ _

/-- 正方向実行があるwireを常に保存するなら、逆基底置換も同じwireを保存する。 -/
theorem toBasisPermutation_apply_preserves_wire
    {p : QParameters}
    (circuit : Circuit (ReversibleGate p.ancillaWidth p.systemWidth))
    (wire : Wire p.ancillaWidth p.systemWidth)
    (preserves : ∀ input, circuit.runBasis reversibleGatePermutation input wire =
      input wire)
    (output : JointBasis p.ancillaWidth p.systemWidth) :
    circuit.toBasisPermutation reversibleGatePermutation output wire =
      output wire := by
  rw [Circuit.toBasisPermutation_eq_execution_inverse reversibleGatePermutation
    (by intro gate; cases gate <;> rfl)]
  let input := (circuit.toExecutionPermutation reversibleGatePermutation)⁻¹ output
  have executed : circuit.runBasis reversibleGatePermutation input = output := by
    exact Equiv.apply_symm_apply _ output
  calc
    input wire = circuit.runBasis reversibleGatePermutation input wire :=
      (preserves input).symm
    _ = output wire := congrFun executed wire

/-- alignの正方向・逆方向はいずれもamplitude signalを保存する。 -/
theorem alignToBasisPermutation_amplitudeSignal
    (p : QParameters) (output : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).toBasisPermutation reversibleGatePermutation output
        (amplitudeSignalWire p) = output (amplitudeSignalWire p) := by
  apply toBasisPermutation_apply_preserves_wire
  intro input
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_eq]
  rw [cnotBasisAction_control_or_other (amplitudeSignalWire p)
    (keySignalWire p) (amplitudeSignalWire p)
    (amplitudeSignalWire_ne_keySignalWire p)]
  exact qAlignAfterSelectorBasis_amplitudeSignal p input

/-- system→column-key COPYの逆基底置換はamplitude signalを保存する。 -/
theorem copyToBasisPermutation_amplitudeSignal
    (p : QParameters) (output : JointBasis p.ancillaWidth p.systemWidth) :
    (xorSystemIntoColumnKeyReversibleCircuit p).toBasisPermutation
        reversibleGatePermutation output (amplitudeSignalWire p) =
      output (amplitudeSignalWire p) := by
  apply toBasisPermutation_apply_preserves_wire
  intro input
  change (xorCopy (topSystemWires p) (topColumnKeyWires p)).runBasis
      reversibleGatePermutation input (amplitudeSignalWire p) =
    input (amplitudeSignalWire p)
  exact xorSystemIntoColumnKey_runBasis_outside p input
    (amplitudeSignalWire p) (by
      simpa only [← columnKeyWires_eq_topColumnKeyWires] using
        amplitudeSignalWire_not_mem_columnKeyWires p)

/-- 最終Xを逆に通した直後の基底。 -/
def qActualAfterFinalFlipPreimage (p : QParameters)
    (output : RegisterBasis p.systemWidth) (rowSelector : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (flipAmplitudeSignalReversibleCircuit p).toBasisPermutation
    reversibleGatePermutation (qFinalRowSelectorBasis p output rowSelector)

/-- 終端Xを逆追跡した基底は、同じamplitude signalを一度反転した基底そのものである。 -/
theorem qActualAfterFinalFlipPreimage_eq
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    qActualAfterFinalFlipPreimage p output rowSelector =
      xBasisAction (amplitudeSignalWire p)
        (qFinalRowSelectorBasis p output rowSelector) := by
  apply toBasisPermutation_apply_of_runBasis_eq
  rw [flipAmplitudeSignal_runBasis, xBasisAction_involutive]

/-- 終端X逆追跡後のamplitude signalは真である。 -/
@[simp] theorem qActualAfterFinalFlipPreimage_amplitudeSignal
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    qActualAfterFinalFlipPreimage p output rowSelector
        (amplitudeSignalWire p) = true := by
  rw [qActualAfterFinalFlipPreimage_eq, xBasisAction_target]
  have outside : amplitudeSignalWire p ∉
      selectorSliceWires p (rowSelectorWire p) := by
    simpa only [← rowSelectorWires_eq_selectorSliceWires] using
      amplitudeSignalWire_not_mem_rowSelectorWires p
  unfold qFinalRowSelectorBasis
  rw [selectorBasisOver_apply_outside p (rowSelectorWire p)
    (zeroAncillaJointBasis p output)
    (selectorBasisOfNat p.selectorWidth rowSelector.val)
    (amplitudeSignalWire p) outside]
  rfl

/-- 終端X逆追跡後もsystem registerは最終出力基底を保持する。 -/
theorem qActualAfterFinalFlipPreimage_readSystem
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    readWires (systemWires p)
        (qActualAfterFinalFlipPreimage p output rowSelector) =
      registerBitList output := by
  rw [qActualAfterFinalFlipPreimage_eq,
    readWires_xBasisAction_of_not_mem (systemWires p)
      (amplitudeSignalWire p) _ (amplitudeSignalWire_not_mem_systemWires p)]
  exact qFinalRowSelectorBasis_readSystem p output rowSelector

/-- 終端X逆追跡後もrow selectorは指定定数bit列を保持する。 -/
theorem qActualAfterFinalFlipPreimage_readRowSelector
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    readWires (rowSelectorWires p)
        (qActualAfterFinalFlipPreimage p output rowSelector) =
      constantBits rowSelector.val (rowSelectorWires p).length := by
  rw [qActualAfterFinalFlipPreimage_eq,
    readWires_xBasisAction_of_not_mem (rowSelectorWires p)
      (amplitudeSignalWire p) _
      (amplitudeSignalWire_not_mem_rowSelectorWires p)]
  exact qFinalRowSelectorBasis_readRowSelector p output rowSelector

/-- 終端X逆追跡後もoracle work全体は0のままである。 -/
theorem qActualAfterFinalFlipPreimage_oracleWork_zero
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) {wire : Wire p.ancillaWidth p.systemWidth}
    (member : wire ∈ diagonalOracleWorkWires p) :
    qActualAfterFinalFlipPreimage p output rowSelector wire = false := by
  rw [qActualAfterFinalFlipPreimage_eq,
    xBasisAction_other (amplitudeSignalWire p) wire
      (diagonalOracleWorkWire_ne_amplitudeSignal p member)]
  exact qFinalRowSelectorBasis_oracleWork_zero p output rowSelector member

/-- column-key registerとrow-selector registerはcanonical layout上で互いに素である。 -/
theorem qActualColumnKeyWires_disjoint_rowSelectorWires (p : QParameters) :
    (columnKeyWires p).Disjoint (rowSelectorWires p) := by
  let key := (QLayout.canonical p).columnKey
  let selector := (QLayout.canonical p).rowSelector
  have separated :
      (key.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (selector.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    key.wireList_disjoint_of_end_le_start selector
      (by simp [key, selector, QLayout.canonical])
  simpa [columnKeyWires, columnKeyWire, rowSelectorWires, rowSelectorWire,
    key, selector, RegisterSlice.wireList] using separated

/-- column-selector registerとrow-selector registerはcanonical layout上で互いに素である。 -/
theorem qActualColumnSelectorWires_disjoint_rowSelectorWires (p : QParameters) :
    (columnSelectorWires p).Disjoint (rowSelectorWires p) := by
  let rowSelector := (QLayout.canonical p).rowSelector
  let columnSelector := (QLayout.canonical p).columnSelector
  have separated :
      (rowSelector.wireList : List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (columnSelector.wireList : List (Wire p.ancillaWidth p.systemWidth)) :=
    rowSelector.wireList_disjoint_of_end_le_start columnSelector
      (by simp [rowSelector, columnSelector, QLayout.canonical])
  simpa [columnSelectorWires, columnSelectorWire, rowSelectorWires,
    rowSelectorWire, rowSelector, columnSelector, RegisterSlice.wireList] using
      separated.symm

/-- amplitude signalはcolumn-selector registerに含まれない。 -/
theorem amplitudeSignalWire_not_mem_columnSelectorWires (p : QParameters) :
    amplitudeSignalWire p ∉ columnSelectorWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [columnSelectorWire, amplitudeSignalWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/--
全要素がアンシラでrow selectorと交わらずamplitude signalも含まないwire列は、
終端X逆追跡後も全0である。
-/
theorem qActualAfterFinalFlipPreimage_readWires_zero
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (wires : List (Wire p.ancillaWidth p.systemWidth))
    (allAncilla : ∀ wire ∈ wires, ∃ index, wire = Wire.ancilla index)
    (disjoint : wires.Disjoint (rowSelectorWires p))
    (amplitudeAbsent : amplitudeSignalWire p ∉ wires) :
    readWires wires (qActualAfterFinalFlipPreimage p output rowSelector) =
      List.replicate wires.length false := by
  apply readWires_eq_replicate_false_of_forall
  intro wire member
  rw [qActualAfterFinalFlipPreimage_eq,
    xBasisAction_other (amplitudeSignalWire p) wire]
  · unfold qFinalRowSelectorBasis
    rw [selectorBasisOver_apply_outside p (rowSelectorWire p)
      (zeroAncillaJointBasis p output)
      (selectorBasisOfNat p.selectorWidth rowSelector.val) wire]
    · rcases allAncilla wire member with ⟨index, rfl⟩
      rfl
    · simpa only [← rowSelectorWires_eq_selectorSliceWires] using
        (List.disjoint_left.mp disjoint) member
  · intro equal
    apply amplitudeAbsent
    exact equal ▸ member

/-- row-selector外のamplitudeでないancilla wireは、終端X逆追跡直後も0である。 -/
theorem qActualAfterFinalFlipPreimage_ancilla_zero
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (isAncilla : ∃ index, wire = Wire.ancilla index)
    (outsideRowSelector : wire ∉ rowSelectorWires p)
    (differentAmplitude : wire ≠ amplitudeSignalWire p) :
    qActualAfterFinalFlipPreimage p output rowSelector wire = false := by
  have values := qActualAfterFinalFlipPreimage_readWires_zero p output
    rowSelector [wire]
      (by
        intro candidate member
        simp only [List.mem_singleton] at member
        subst candidate
        exact isAncilla)
      (by simpa [List.disjoint_left] using outsideRowSelector)
      (by simpa using differentAmplitude.symm)
  simpa [readWires] using values

/-- active wireはrow-selector registerに含まれない。 -/
theorem qActualActiveWire_not_mem_rowSelectorWires (p : QParameters) :
    activeWire p ∉ rowSelectorWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [activeWire, rowSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- negative wireはrow-selector registerに含まれない。 -/
theorem qActualNegativeWire_not_mem_rowSelectorWires (p : QParameters) :
    negativeWire p ∉ rowSelectorWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [negativeWire, rowSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- active wireはcolumn-key registerに含まれない。 -/
theorem qActualActiveWire_not_mem_columnKeyWires (p : QParameters) :
    activeWire p ∉ columnKeyWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [activeWire, columnKeyWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- active wireはcolumn-selector registerに含まれない。 -/
theorem qActualActiveWire_not_mem_columnSelectorWires (p : QParameters) :
    activeWire p ∉ columnSelectorWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [activeWire, columnSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- negative wireはcolumn-key registerに含まれない。 -/
theorem qActualNegativeWire_not_mem_columnKeyWires (p : QParameters) :
    negativeWire p ∉ columnKeyWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [negativeWire, columnKeyWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- negative wireはcolumn-selector registerに含まれない。 -/
theorem qActualNegativeWire_not_mem_columnSelectorWires (p : QParameters) :
    negativeWire p ∉ columnSelectorWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [negativeWire, columnSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- active wireとkey-signal wireは異なる。 -/
theorem qActualActiveWire_ne_keySignalWire (p : QParameters) :
    activeWire p ≠ keySignalWire p := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [activeWire, keySignalWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- negative wireとkey-signal wireは異なる。 -/
theorem qActualNegativeWire_ne_keySignalWire (p : QParameters) :
    negativeWire p ≠ keySignalWire p := by
  intro equal
  have numbers := congrArg wireNumber equal
  simp [negativeWire, keySignalWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- active wireはsystem registerに含まれない。 -/
theorem qActualActiveWire_not_mem_systemWires (p : QParameters) :
    activeWire p ∉ systemWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  cases equal

/-- negative wireはsystem registerに含まれない。 -/
theorem qActualNegativeWire_not_mem_systemWires (p : QParameters) :
    negativeWire p ∉ systemWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  cases equal

/-- 終端X逆追跡直後のactive bitは0である。 -/
@[simp] theorem qActualAfterFinalFlipPreimage_active_false
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    qActualAfterFinalFlipPreimage p output rowSelector (activeWire p) = false := by
  apply qActualAfterFinalFlipPreimage_ancilla_zero
  · exact ⟨_, rfl⟩
  · exact qActualActiveWire_not_mem_rowSelectorWires p
  · exact activeWire_ne_amplitudeSignalWire p

/-- 終端X逆追跡直後のnegative bitは0である。 -/
@[simp] theorem qActualAfterFinalFlipPreimage_negative_false
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    qActualAfterFinalFlipPreimage p output rowSelector (negativeWire p) = false := by
  apply qActualAfterFinalFlipPreimage_ancilla_zero
  · exact ⟨_, rfl⟩
  · exact qActualNegativeWire_not_mem_rowSelectorWires p
  · exact negativeWire_ne_amplitudeSignalWire p

/-- 終端X逆追跡直後のkey-signal bitは0である。 -/
@[simp] theorem qActualAfterFinalFlipPreimage_keySignal_false
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    qActualAfterFinalFlipPreimage p output rowSelector (keySignalWire p) = false := by
  apply qActualAfterFinalFlipPreimage_ancilla_zero
  · exact ⟨_, rfl⟩
  · exact keySignalWire_not_mem_rowSelectorWires p
  · exact (amplitudeSignalWire_ne_keySignalWire p).symm

/-- 終端X逆追跡直後のcolumn-key accumulatorは全0である。 -/
theorem qActualAfterFinalFlipPreimage_columnKey_zero
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    readWires (columnKeyWires p)
        (qActualAfterFinalFlipPreimage p output rowSelector) =
      List.replicate (columnKeyWires p).length false := by
  apply qActualAfterFinalFlipPreimage_readWires_zero
  · intro wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    exact ⟨_, rfl⟩
  · exact qActualColumnKeyWires_disjoint_rowSelectorWires p
  · exact amplitudeSignalWire_not_mem_columnKeyWires p

/-- 終端X逆追跡直後のcolumn-selector accumulatorは全0である。 -/
theorem qActualAfterFinalFlipPreimage_columnSelector_zero
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    readWires (columnSelectorWires p)
        (qActualAfterFinalFlipPreimage p output rowSelector) =
      List.replicate (columnSelectorWires p).length false := by
  apply qActualAfterFinalFlipPreimage_readWires_zero
  · intro wire member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    exact ⟨_, rfl⟩
  · exact qActualColumnSelectorWires_disjoint_rowSelectorWires p
  · exact amplitudeSignalWire_not_mem_columnSelectorWires p

/-- amplitude signalが真なら、その基底は全0背景とcolumn selector外で一致できない。 -/
theorem not_outsideColumnSelectorMatches_of_amplitude_true
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (amplitudeTrue : basis (amplitudeSignalWire p) = true) :
    ¬OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p system) basis := by
  intro outside
  have amplitudeOutside : amplitudeSignalWire p ∉
      selectorSliceWires p (columnSelectorWire p) := by
    simpa only [← columnSelectorWires_eq_selectorSliceWires] using
      amplitudeSignalWire_not_mem_columnSelectorWires p
  have equal := outside (amplitudeSignalWire p) amplitudeOutside
  rw [amplitudeTrue] at equal
  simp [amplitudeSignalWire, RegisterSlice.ancillaWire] at equal

/-- column一様準備の逆像でamplitude signalが真なら、そのpath振幅は0である。 -/
theorem qColumnPreparedState_eq_zero_of_amplitude_true
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (amplitudeTrue : basis (amplitudeSignalWire p) = true) :
    qColumnPreparedState p system basis = 0 :=
  qColumnPreparedState_eq_zero_of_outside_mismatch p system basis
    (not_outsideColumnSelectorMatches_of_amplitude_true p system basis amplitudeTrue)

/-- 合法な最終delimiter基底を終端Xから逆追跡すると、row oracleのcanonical入力仕様を満たす。 -/
theorem qActualAfterFinalFlipPreimage_rowOracleInputSpec
    (p : QParameters) (output : QConfiguration p)
    (rowSelector : QSelector p) :
    RowOracleInputSpec p output rowSelector
      (qActualAfterFinalFlipPreimage p (delimiterEncoding output) rowSelector) := by
  refine {
    system_bits := qActualAfterFinalFlipPreimage_readSystem p
      (delimiterEncoding output) rowSelector
    selector_bits := qActualAfterFinalFlipPreimage_readRowSelector p
      (delimiterEncoding output) rowSelector
    work_zero := ?_ }
  intro wire member
  exact qActualAfterFinalFlipPreimage_oracleWork_zero p
    (delimiterEncoding output) rowSelector member

/-- 終端X逆追跡後のrow入力をpersistent computeへ通すと、全branch共通仕様を満たす。 -/
theorem qActualAfterFinalFlipPreimage_rowPersistentInputSpec
    (p : QParameters) (output : QConfiguration p)
    (rowSelector : QSelector p) :
    RowOraclePersistentConditionsSpec p output rowSelector
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (systemWires p) true).runBasis
        reversibleGatePermutation
        (qActualAfterFinalFlipPreimage p (delimiterEncoding output)
          rowSelector)) :=
  (qActualAfterFinalFlipPreimage_rowOracleInputSpec p output rowSelector).afterPersistent

/-- 同じsource bit列によるregister XORを二回行うと元のtarget bit列へ戻る。 -/
theorem xorRegisterBits_involutive_of_length
    (source target : List Bool) (sameLength : source.length = target.length) :
    xorRegisterBits source (xorRegisterBits source target) = target := by
  induction source generalizing target with
  | nil =>
      cases target with
      | nil => rfl
      | cons targetBit targetBits => simp at sameLength
  | cons sourceBit sourceBits inductionHypothesis =>
      cases target with
      | nil => simp at sameLength
      | cons targetBit targetBits =>
          have tailLength : sourceBits.length = targetBits.length := by
            simpa using Nat.succ.inj sameLength
          change
            (if sourceBit then
                !(if sourceBit then !targetBit else targetBit)
              else if sourceBit then !targetBit else targetBit) ::
                xorRegisterBits sourceBits
                  (xorRegisterBits sourceBits targetBits) =
              targetBit :: targetBits
          rw [inductionHypothesis targetBits tailLength]
          cases sourceBit <;> simp

/-- 全0のtarget registerへsourceをXORするとsource bit列そのものになる。 -/
theorem xorRegisterBits_replicate_false (source : List Bool) :
    xorRegisterBits source (List.replicate source.length false) = source := by
  induction source with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      change (if bit then !false else false) ::
          xorRegisterBits bits (List.replicate bits.length false) = bit :: bits
      rw [inductionHypothesis]
      cases bit <;> rfl

/-- 二つの同長sourceを同じ順で二巡XORすると元のtargetへ戻る。 -/
theorem xorRegisterBits_two_sources_involutive
    (first second target : List Bool)
    (firstLength : first.length = target.length)
    (secondLength : second.length = target.length) :
    xorRegisterBits second
        (xorRegisterBits first
          (xorRegisterBits second (xorRegisterBits first target))) = target := by
  induction first generalizing second target with
  | nil =>
      cases target with
      | nil =>
          have secondEmpty : second = [] := by
            cases second with
            | nil => rfl
            | cons bit bits => simp at secondLength
          subst second
          rfl
      | cons bit bits => simp at firstLength
  | cons firstBit firstBits inductionHypothesis =>
      cases target with
      | nil => simp at firstLength
      | cons targetBit targetBits =>
          cases second with
          | nil => simp at secondLength
          | cons secondBit secondBits =>
              have firstTailLength : firstBits.length = targetBits.length := by
                simpa using Nat.succ.inj firstLength
              have secondTailLength : secondBits.length = targetBits.length := by
                simpa using Nat.succ.inj secondLength
              change
                (if secondBit then
                    !(if firstBit then
                        !(if secondBit then
                            !(if firstBit then !targetBit else targetBit)
                          else if firstBit then !targetBit else targetBit)
                      else if secondBit then
                        !(if firstBit then !targetBit else targetBit)
                      else if firstBit then !targetBit else targetBit)
                  else if firstBit then
                    !(if secondBit then
                        !(if firstBit then !targetBit else targetBit)
                      else if firstBit then !targetBit else targetBit)
                  else if secondBit then
                    !(if firstBit then !targetBit else targetBit)
                  else if firstBit then !targetBit else targetBit) ::
                    xorRegisterBits secondBits
                      (xorRegisterBits firstBits
                        (xorRegisterBits secondBits
                          (xorRegisterBits firstBits targetBits))) =
                  targetBit :: targetBits
              rw [inductionHypothesis secondBits targetBits firstTailLength
                secondTailLength]
              cases firstBit <;> cases secondBit <;> cases targetBit <;> rfl

/-- 同じ外側bit列で二重にXORすると中央のbit列だけが残る。 -/
theorem xorRegisterBits_sandwich
    (outer middle : List Bool) (sameLength : outer.length = middle.length) :
    xorRegisterBits outer (xorRegisterBits middle outer) = middle := by
  induction outer generalizing middle with
  | nil =>
      cases middle with
      | nil => rfl
      | cons bit bits => simp at sameLength
  | cons outerBit outerBits inductionHypothesis =>
      cases middle with
      | nil => simp at sameLength
      | cons middleBit middleBits =>
          have tailLength : outerBits.length = middleBits.length := by
            simpa using Nat.succ.inj sameLength
          change
            (if outerBit then
                !(if middleBit then !outerBit else outerBit)
              else if middleBit then !outerBit else outerBit) ::
                xorRegisterBits outerBits
                  (xorRegisterBits middleBits outerBits) =
              middleBit :: middleBits
          rw [inductionHypothesis middleBits tailLength]
          cases outerBit <;> cases middleBit <;> rfl

/-- 整列回路はsystem・row-selector・key-signal以外のwireを保存する。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideSystem : wire ∉ systemWires p)
    (outsideRowSelector : wire ∉ rowSelectorWires p)
    (differentKeySignal : wire ≠ keySignalWire p) :
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input wire =
      input wire := by
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_eq]
  rw [cnotBasisAction_control_or_other (amplitudeSignalWire p)
    (keySignalWire p) wire differentKeySignal]
  unfold qAlignAfterSelectorBasis qAlignAfterRowBasis qAlignAfterColumnBasis
  rw [alignSelectorOutputIntoRow_runBasis_outside p _ wire outsideRowSelector]
  rw [alignRowOutputIntoSystem_runBasis_outside p _ wire outsideSystem]
  exact alignColumnKeyIntoSystem_runBasis_outside p input wire outsideSystem

/-- 整列回路は二つの更新対象とkey-signalから離れたregister読出しを保存する。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readWires_outside_targets
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (wires : List (Wire p.ancillaWidth p.systemWidth))
    (outsideSystem : wires.Disjoint (systemWires p))
    (outsideRowSelector : wires.Disjoint (rowSelectorWires p))
    (keySignalAbsent : keySignalWire p ∉ wires) :
    readWires wires
        ((controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input) =
      readWires wires input := by
  apply List.map_congr_left
  intro wire member
  apply controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p input wire
  · exact (List.disjoint_left.mp outsideSystem) member
  · exact (List.disjoint_left.mp outsideRowSelector) member
  · intro equal
    exact keySignalAbsent (equal ▸ member)

/-- row-output registerとrow-selector registerはcanonical layout上で交わらない。 -/
theorem qActualRowOutputWires_disjoint_rowSelectorWires (p : QParameters) :
    (rowOutputWires p).Disjoint (rowSelectorWires p) := by
  rw [List.disjoint_left]
  intro wire rowOutputMember rowSelectorMember
  rcases List.mem_map.mp rowOutputMember with ⟨outputIndex, _, outputEqual⟩
  rcases List.mem_map.mp rowSelectorMember with
    ⟨selectorIndex, _, selectorEqual⟩
  have numbers := congrArg wireNumber (outputEqual.trans selectorEqual.symm)
  simp [rowOutputWire, rowSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- row-output registerとcolumn-key registerはcanonical layout上で交わらない。 -/
theorem qActualRowOutputWires_disjoint_columnKeyWires (p : QParameters) :
    (rowOutputWires p).Disjoint (columnKeyWires p) := by
  rw [List.disjoint_left]
  intro wire rowOutputMember columnKeyMember
  rcases List.mem_map.mp rowOutputMember with ⟨outputIndex, _, outputEqual⟩
  rcases List.mem_map.mp columnKeyMember with ⟨keyIndex, _, keyEqual⟩
  have numbers := congrArg wireNumber (outputEqual.trans keyEqual.symm)
  simp [rowOutputWire, columnKeyWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- row-output registerとcolumn-selector registerはcanonical layout上で交わらない。 -/
theorem qActualRowOutputWires_disjoint_columnSelectorWires (p : QParameters) :
    (rowOutputWires p).Disjoint (columnSelectorWires p) := by
  rw [List.disjoint_left]
  intro wire rowOutputMember columnSelectorMember
  rcases List.mem_map.mp rowOutputMember with ⟨outputIndex, _, outputEqual⟩
  rcases List.mem_map.mp columnSelectorMember with
    ⟨selectorIndex, _, selectorEqual⟩
  have numbers := congrArg wireNumber (outputEqual.trans selectorEqual.symm)
  simp [rowOutputWire, columnSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- selector-output registerとcolumn-key registerはcanonical layout上で交わらない。 -/
theorem qActualSelectorOutputWires_disjoint_columnKeyWires (p : QParameters) :
    (selectorOutputWires p).Disjoint (columnKeyWires p) := by
  rw [List.disjoint_left]
  intro wire outputMember keyMember
  rcases List.mem_map.mp outputMember with ⟨outputIndex, _, outputEqual⟩
  rcases List.mem_map.mp keyMember with ⟨keyIndex, _, keyEqual⟩
  have numbers := congrArg wireNumber (outputEqual.trans keyEqual.symm)
  simp [selectorOutputWire, columnKeyWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- selector-output registerとcolumn-selector registerはcanonical layout上で交わらない。 -/
theorem qActualSelectorOutputWires_disjoint_columnSelectorWires
    (p : QParameters) :
    (selectorOutputWires p).Disjoint (columnSelectorWires p) := by
  rw [List.disjoint_left]
  intro wire outputMember selectorMember
  rcases List.mem_map.mp outputMember with ⟨outputIndex, _, outputEqual⟩
  rcases List.mem_map.mp selectorMember with
    ⟨selectorIndex, _, selectorEqual⟩
  have numbers := congrArg wireNumber (outputEqual.trans selectorEqual.symm)
  simp [selectorOutputWire, columnSelectorWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- key-signal wireはrow-output registerに含まれない。 -/
theorem qActualKeySignalWire_not_mem_rowOutputWires (p : QParameters) :
    keySignalWire p ∉ rowOutputWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [keySignalWire, rowOutputWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- key-signal wireはselector-output registerに含まれない。 -/
theorem qActualKeySignalWire_not_mem_selectorOutputWires (p : QParameters) :
    keySignalWire p ∉ selectorOutputWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [keySignalWire, selectorOutputWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- column-selector registerとsystem registerはwire種別が異なるため交わらない。 -/
theorem qActualColumnSelectorWires_disjoint_systemWires (p : QParameters) :
    (columnSelectorWires p).Disjoint (systemWires p) := by
  rw [List.disjoint_left]
  intro wire selectorMember systemMember
  rcases List.mem_map.mp selectorMember with ⟨selectorIndex, _, rfl⟩
  rcases List.mem_map.mp systemMember with ⟨systemIndex, _, equal⟩
  cases equal

/-- key-signal wireはoracle-work registerに含まれない。 -/
theorem qActualKeySignalWire_not_mem_diagonalOracleWorkWires (p : QParameters) :
    keySignalWire p ∉ diagonalOracleWorkWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [keySignalWire, QLayout.canonical,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- column oracle入力仕様は整列回路とdiscriminator CNOTを逆追跡しても保存される。 -/
theorem ColumnOracleInputSpec.afterAlignDiscriminator
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

/-- 整列回路は計算基底上で自己逆である。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_involutive
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation
        ((controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input) =
      input := by
  let first := (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
    reversibleGatePermutation input
  let second := (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
    reversibleGatePermutation first
  have amplitudeFirst : first (amplitudeSignalWire p) =
      input (amplitudeSignalWire p) := by
    change (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input
        (amplitudeSignalWire p) = input (amplitudeSignalWire p)
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_eq]
    rw [cnotBasisAction_control_or_other (amplitudeSignalWire p)
      (keySignalWire p) (amplitudeSignalWire p)
      (amplitudeSignalWire_ne_keySignalWire p)]
    exact qAlignAfterSelectorBasis_amplitudeSignal p input
  have columnKeyFirst : readWires (columnKeyWires p) first =
      readWires (columnKeyWires p) input := by
    apply controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readWires_outside_targets
    · exact qTopColumnKeyWires_disjoint_systemWires p
    · exact qActualColumnKeyWires_disjoint_rowSelectorWires p
    · exact keySignalWire_not_mem_columnKeyWires p
  have rowOutputFirst : readWires (rowOutputWires p) first =
      readWires (rowOutputWires p) input := by
    apply controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readWires_outside_targets
    · exact qTopRowOutputWires_disjoint_systemWires p
    · exact qActualRowOutputWires_disjoint_rowSelectorWires p
    · exact qActualKeySignalWire_not_mem_rowOutputWires p
  have selectorOutputFirst : readWires (selectorOutputWires p) first =
      readWires (selectorOutputWires p) input := by
    apply controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readWires_outside_targets
    · exact qTopSelectorOutputWires_disjoint_systemWires p
    · exact qTopSelectorOutputWires_disjoint_rowSelectorWires p
    · exact qActualKeySignalWire_not_mem_selectorOutputWires p
  have systemSecond : readWires (systemWires p) second =
      readWires (systemWires p) input := by
    rw [show second = (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
      reversibleGatePermutation first by rfl]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readSystem, amplitudeFirst,
      columnKeyFirst, rowOutputFirst]
    rw [show first = (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
      reversibleGatePermutation input by rfl]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readSystem]
    cases input (amplitudeSignalWire p)
    · rfl
    ·
      apply xorRegisterBits_two_sources_involutive
      · simp only [readWires, List.length_map]
        simp [columnKeyWires, systemWires]
      · simp only [readWires, List.length_map]
        simp [rowOutputWires, systemWires]
  have rowSelectorSecond : readWires (rowSelectorWires p) second =
      readWires (rowSelectorWires p) input := by
    rw [show second = (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
      reversibleGatePermutation first by rfl]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readRowSelector, amplitudeFirst,
      selectorOutputFirst]
    rw [show first = (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
      reversibleGatePermutation input by rfl]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readRowSelector]
    cases input (amplitudeSignalWire p)
    · rfl
    ·
      apply xorRegisterBits_involutive_of_length
      simp only [readWires, List.length_map]
      simp [selectorOutputWires, rowSelectorWires]
  have keySignalSecond : second (keySignalWire p) = input (keySignalWire p) := by
    rw [show second = (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
      reversibleGatePermutation first by rfl]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_keySignal, amplitudeFirst]
    rw [show first = (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
      reversibleGatePermutation input by rfl]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_keySignal]
    cases input (amplitudeSignalWire p)
    · rfl
    · cases input (keySignalWire p) <;> rfl
  change second = input
  funext wire
  by_cases systemMember : wire ∈ systemWires p
  · exact readWires_eq_at_of_eq (systemWires p) second input systemSecond
      systemMember
  by_cases rowSelectorMember : wire ∈ rowSelectorWires p
  · exact readWires_eq_at_of_eq (rowSelectorWires p) second input
      rowSelectorSecond rowSelectorMember
  by_cases keySignalEqual : wire = keySignalWire p
  · subst wire
    exact keySignalSecond
  · rw [show second = (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis
      reversibleGatePermutation first by rfl]
    rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p first wire systemMember
      rowSelectorMember keySignalEqual]
    exact controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p input wire systemMember
      rowSelectorMember keySignalEqual

/-- 同じlittle-endian定数XORを二回行うと任意のbit列が元へ戻る。 -/
theorem controlledXorConstantBits_true_involutive
    (constant start : Nat) (bits : List Bool) :
    controlledXorConstantBits true constant start
        (controlledXorConstantBits true constant start bits) = bits := by
  induction bits generalizing start with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      by_cases enabled : constant.testBit start = true
      · simp [controlledXorConstantBits, enabled, inductionHypothesis]
      · have disabled : constant.testBit start = false :=
          Bool.eq_false_of_not_eq_true enabled
        simp [controlledXorConstantBits, disabled, inductionHypothesis]

/-- 全0の固定幅targetへ定数XORすると、そのlittle-endian定数bit列になる。 -/
theorem controlledXorConstantBits_true_replicate_false
    (constant start width : Nat) :
    controlledXorConstantBits true constant start
        (List.replicate width false) =
      constantBitsAux constant start width := by
  induction width generalizing start with
  | zero => rfl
  | succ width inductionHypothesis =>
      change (if true && constant.testBit start then !false else false) ::
          controlledXorConstantBits true constant (start + 1)
            (List.replicate width false) =
        constant.testBit start :: constantBitsAux constant (start + 1) width
      rw [inductionHypothesis]
      cases constant.testBit start <;> rfl

/-- row参照結果はsystem・row-selector・oracle-work上の入力仕様を保存する。 -/
theorem RowReferenceBranchResult.preservesInputSpec
    {p : QParameters} {inputConfiguration predecessor : QConfiguration p}
    {rowSelector columnSelector : QSelector p}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (inputSpec : RowOracleInputSpec p inputConfiguration rowSelector input)
    (result : RowReferenceBranchResult p predecessor columnSelector input output) :
    RowOracleInputSpec p inputConfiguration rowSelector output := by
  refine {
    system_bits := ?_
    selector_bits := ?_
    work_zero := ?_ }
  · calc
      readWires (systemWires p) output = readWires (systemWires p) input := by
        apply List.map_congr_left
        intro wire member
        exact result.support_restored wire
          (List.mem_append_left (diagonalOracleWorkWires p)
            (List.mem_append_right (rowSelectorWires p) member))
      _ = registerBitList (delimiterEncoding inputConfiguration) :=
        inputSpec.system_bits
  · calc
      readWires (rowSelectorWires p) output =
          readWires (rowSelectorWires p) input := by
        apply List.map_congr_left
        intro wire member
        exact result.support_restored wire
          (List.mem_append_left (diagonalOracleWorkWires p)
            (List.mem_append_left (systemWires p) member))
      _ = constantBits rowSelector.val (rowSelectorWires p).length :=
        inputSpec.selector_bits
  · intro wire member
    rw [result.support_restored wire (List.mem_append_right _ member)]
    exact inputSpec.work_zero wire member

/-- 同じrow参照XOR仕様を二回適用した二つの結果基底は元の入力基底に一致する。 -/
theorem RowReferenceBranchResult.twice_eq_input
    {p : QParameters} {predecessor : QConfiguration p}
    {columnSelector : QSelector p}
    {input middle output : JointBasis p.ancillaWidth p.systemWidth}
    (firstResult : RowReferenceBranchResult p predecessor columnSelector input middle)
    (secondResult : RowReferenceBranchResult p predecessor columnSelector middle output) :
    output = input := by
  have keyTwice : readWires (columnKeyWires p) output =
      readWires (columnKeyWires p) input := by
    rw [secondResult.column_key, firstResult.column_key]
    apply xorRegisterBits_involutive_of_length
    simp [registerBitList, readWires]
  have selectorTwice : readWires (columnSelectorWires p) output =
      readWires (columnSelectorWires p) input := by
    rw [secondResult.column_selector, firstResult.column_selector]
    exact controlledXorConstantBits_true_involutive columnSelector.val 0 _
  funext wire
  by_cases keyMember : wire ∈ columnKeyWires p
  · exact readWires_eq_at_of_eq (columnKeyWires p) output input keyTwice keyMember
  by_cases selectorMember : wire ∈ columnSelectorWires p
  · exact readWires_eq_at_of_eq (columnSelectorWires p) output input selectorTwice
      selectorMember
  by_cases signalEqual : wire = keySignalWire p
  · subst wire
    rw [secondResult.key_signal, firstResult.key_signal]
    simp
  · rw [secondResult.outside_restored wire keyMember selectorMember signalEqual]
    exact firstResult.outside_restored wire keyMember selectorMember signalEqual

/-- column参照結果はcolumn-key・column-selector・oracle-work上の入力仕様を保存する。 -/
theorem ColumnReferenceBranchResult.preservesInputSpec
    {p : QParameters} {inputConfiguration : QConfiguration p}
    {inputSelector : QSelector p} {reference : ColumnReferenceResult p}
    {input output : JointBasis p.ancillaWidth p.systemWidth}
    (inputSpec : ColumnOracleInputSpec p inputConfiguration inputSelector input)
    (result : ColumnReferenceBranchResult p reference input output) :
    ColumnOracleInputSpec p inputConfiguration inputSelector output := by
  refine {
    column_key_bits := ?_
    selector_bits := ?_
    work_zero := ?_ }
  · calc
      readWires (columnKeyWires p) output =
          readWires (columnKeyWires p) input := by
        apply List.map_congr_left
        intro wire member
        exact result.support_restored wire
          (columnKeyWire_mem_columnEventCandidateUpdateAndSortSupport p member)
      _ = registerBitList (delimiterEncoding inputConfiguration) :=
        inputSpec.column_key_bits
  · calc
      readWires (columnSelectorWires p) output =
          readWires (columnSelectorWires p) input := by
        apply List.map_congr_left
        intro wire member
        exact result.support_restored wire
          (columnSelectorWire_mem_columnEventCandidateUpdateAndSortSupport p member)
      _ = constantBits inputSelector.val (columnSelectorWires p).length :=
        inputSpec.selector_bits
  · intro wire member
    rw [result.support_restored wire
      (oracleWorkWire_mem_columnEventCandidateUpdateAndSortSupport p member)]
    exact inputSpec.work_zero wire member

/-- 同じcolumn参照XOR仕様を二回適用した二つの結果基底は元の入力基底に一致する。 -/
theorem ColumnReferenceBranchResult.twice_eq_input
    {p : QParameters} {reference : ColumnReferenceResult p}
    {input middle output : JointBasis p.ancillaWidth p.systemWidth}
    (firstResult : ColumnReferenceBranchResult p reference input middle)
    (secondResult : ColumnReferenceBranchResult p reference middle output) :
    output = input := by
  have rowOutputTwice : readWires (rowOutputWires p) output =
      readWires (rowOutputWires p) input := by
    rw [secondResult.row_output, firstResult.row_output]
    apply xorRegisterBits_involutive_of_length
    simp [registerBitList, readWires]
  have selectorOutputTwice : readWires (selectorOutputWires p) output =
      readWires (selectorOutputWires p) input := by
    rw [secondResult.selector_output, firstResult.selector_output]
    exact controlledXorConstantBits_true_involutive reference.rowSelector.val 0 _
  funext wire
  by_cases rowOutputMember : wire ∈ rowOutputWires p
  · exact readWires_eq_at_of_eq (rowOutputWires p) output input rowOutputTwice
      rowOutputMember
  by_cases selectorOutputMember : wire ∈ selectorOutputWires p
  · exact readWires_eq_at_of_eq (selectorOutputWires p) output input
      selectorOutputTwice selectorOutputMember
  by_cases negativeEqual : wire = negativeWire p
  · subst wire
    rw [secondResult.negative, firstResult.negative]
    cases reference.negative <;> simp
  by_cases activeEqual : wire = activeWire p
  · subst wire
    rw [secondResult.active, firstResult.active]
    simp
  · rw [secondResult.outside_restored wire rowOutputMember selectorOutputMember
      negativeEqual activeEqual]
    exact firstResult.outside_restored wire rowOutputMember selectorOutputMember
      negativeEqual activeEqual

/-- columnReferenceが受理する一般入力では、actual column oracleを二回実行すると元へ戻る。 -/
theorem applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some_involutive
    {p : QParameters} (configuration : QConfiguration p)
    (selector : QSelector p) (reference : ColumnReferenceResult p)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (inputSpec : ColumnOracleInputSpec p configuration selector input)
    (referenceSome : columnReference configuration selector = some reference) :
    (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation
        ((applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input) =
      input := by
  let first := (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
    reversibleGatePermutation input
  let second := (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
    reversibleGatePermutation first
  have firstResult : ColumnReferenceBranchResult p reference input first := by
    simpa [first] using applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some configuration
      selector reference input inputSpec referenceSome
  have firstSpec : ColumnOracleInputSpec p configuration selector first :=
    ColumnReferenceBranchResult.preservesInputSpec inputSpec firstResult
  have secondResult : ColumnReferenceBranchResult p reference first second := by
    simpa [second] using applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some configuration
      selector reference first firstSpec referenceSome
  change second = input
  exact ColumnReferenceBranchResult.twice_eq_input firstResult secondResult

/-- canonical物理event入力ではactual row oracleを二回実行すると基底全体が元へ戻る。 -/
theorem applyRowOracleReferenceAndRestoreWorkCircuit_physicalEvent_involutive
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (inputSpec : RowOracleInputSpec p
      (eventOutput configuration source direction)
      (rowSelectorForEvent configuration source member direction) input) :
    (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation
        ((applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation input) =
      input := by
  let first := (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
    reversibleGatePermutation input
  let second := (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
    reversibleGatePermutation first
  let columnSelector := selectorForEvent configuration source member direction
  have firstResult : RowReferenceBranchResult p configuration columnSelector
      input first := by
    simpa [first, columnSelector] using
      applyRowOracleReferenceAndRestoreWorkCircuit_physicalEvent_correct configuration source member
        direction input inputSpec
  have firstSpec : RowOracleInputSpec p
      (eventOutput configuration source direction)
      (rowSelectorForEvent configuration source member direction) first :=
    RowReferenceBranchResult.preservesInputSpec inputSpec firstResult
  have secondResult : RowReferenceBranchResult p configuration columnSelector
      first second := by
    simpa [second, columnSelector] using
      applyRowOracleReferenceAndRestoreWorkCircuit_physicalEvent_correct configuration source member
        direction first firstSpec
  have keyTwice : readWires (columnKeyWires p) second =
      readWires (columnKeyWires p) input := by
    rw [secondResult.column_key, firstResult.column_key]
    apply xorRegisterBits_involutive_of_length
    simp [registerBitList, readWires]
  have selectorTwice : readWires (columnSelectorWires p) second =
      readWires (columnSelectorWires p) input := by
    rw [secondResult.column_selector, firstResult.column_selector]
    exact controlledXorConstantBits_true_involutive columnSelector.val 0 _
  change second = input
  funext wire
  by_cases keyMember : wire ∈ columnKeyWires p
  · exact readWires_eq_at_of_eq (columnKeyWires p) second input keyTwice keyMember
  by_cases selectorMember : wire ∈ columnSelectorWires p
  · exact readWires_eq_at_of_eq (columnSelectorWires p) second input selectorTwice
      selectorMember
  by_cases signalEqual : wire = keySignalWire p
  · subst wire
    rw [secondResult.key_signal, firstResult.key_signal]
    simp
  · rw [secondResult.outside_restored wire keyMember selectorMember signalEqual]
    exact firstResult.outside_restored wire keyMember selectorMember signalEqual

/-- row oracleを逆に通した直後の基底。 -/
def qActualAfterRowOraclePreimage (p : QParameters)
    (output : RegisterBasis p.systemWidth) (rowSelector : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (applyRowOracleReferenceAndRestoreWorkCircuit p).toBasisPermutation reversibleGatePermutation
    (qActualAfterFinalFlipPreimage p output rowSelector)

/-- row oracleの候補入力が終端X逆像へ実行されるなら、逆追跡基底はその候補に一致する。 -/
theorem qActualAfterRowOraclePreimage_eq_of_runBasis
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (candidate : JointBasis p.ancillaWidth p.systemWidth)
    (executed : (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis
      reversibleGatePermutation candidate =
        qActualAfterFinalFlipPreimage p output rowSelector) :
    qActualAfterRowOraclePreimage p output rowSelector = candidate := by
  unfold qActualAfterRowOraclePreimage
  exact toBasisPermutation_apply_of_runBasis_eq _ candidate _ executed

/-- row参照が拒否する合法出力では、row oracle逆追跡は終端X逆像をそのまま返す。 -/
theorem qActualAfterRowOraclePreimage_eq_of_reference_none
    (p : QParameters) (output : QConfiguration p)
    (rowSelector : QSelector p)
    (referenceNone : rowReference output rowSelector = none) :
    qActualAfterRowOraclePreimage p (delimiterEncoding output) rowSelector =
      qActualAfterFinalFlipPreimage p (delimiterEncoding output) rowSelector := by
  apply qActualAfterRowOraclePreimage_eq_of_runBasis
  exact applyRowOracleReferenceAndRestoreWorkCircuit_reference_none output rowSelector _
    (qActualAfterFinalFlipPreimage_rowOracleInputSpec p output rowSelector)
    referenceNone

/-- decode不能な最終system基底でも、row oracleのillegal入力仕様を満たす。 -/
theorem qActualAfterFinalFlipPreimage_rowIllegalInputSpec
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    RowOracleIllegalInputSpec p output rowSelector
      (qActualAfterFinalFlipPreimage p output rowSelector) := by
  refine {
    system_bits := qActualAfterFinalFlipPreimage_readSystem p output rowSelector
    selector_bits := qActualAfterFinalFlipPreimage_readRowSelector p output
      rowSelector
    work_zero := ?_ }
  intro wire member
  exact qActualAfterFinalFlipPreimage_oracleWork_zero p output rowSelector member

/-- decode不能な最終system基底では、row oracle逆追跡は終端X逆追跡像を固定する。 -/
theorem qActualAfterRowOraclePreimage_eq_of_illegal
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (illegal : decodeDelimiter output = none) :
    qActualAfterRowOraclePreimage p output rowSelector =
      qActualAfterFinalFlipPreimage p output rowSelector := by
  apply qActualAfterRowOraclePreimage_eq_of_runBasis
  exact applyRowOracleReferenceAndRestoreWorkCircuit_illegal_identity p output rowSelector _
    (qActualAfterFinalFlipPreimage_rowIllegalInputSpec p output rowSelector)
    illegal

/-- 物理eventの受理row pathでは、row逆追跡基底は同じoracleの正方向出力に一致する。 -/
theorem qActualAfterRowOraclePreimage_physicalEvent_eq
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    qActualAfterRowOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction) =
      (applyRowOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation
        (qActualAfterFinalFlipPreimage p
          (delimiterEncoding (eventOutput configuration source direction))
          (rowSelectorForEvent configuration source member direction)) := by
  apply qActualAfterRowOraclePreimage_eq_of_runBasis
  exact applyRowOracleReferenceAndRestoreWorkCircuit_physicalEvent_involutive configuration source
    member direction _
      (qActualAfterFinalFlipPreimage_rowOracleInputSpec p
        (eventOutput configuration source direction)
        (rowSelectorForEvent configuration source member direction))

/-- 物理eventのrow逆追跡基底はpredecessorとcolumn selectorの参照XOR仕様を満たす。 -/
theorem qActualAfterRowOraclePreimage_physicalEvent_result
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    RowReferenceBranchResult p configuration
      (selectorForEvent configuration source member direction)
      (qActualAfterFinalFlipPreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction))
      (qActualAfterRowOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)) := by
  have result := applyRowOracleReferenceAndRestoreWorkCircuit_physicalEvent_correct configuration
    source member direction
    (qActualAfterFinalFlipPreimage p
      (delimiterEncoding (eventOutput configuration source direction))
      (rowSelectorForEvent configuration source member direction))
    (qActualAfterFinalFlipPreimage_rowOracleInputSpec p
      (eventOutput configuration source direction)
      (rowSelectorForEvent configuration source member direction))
  rw [← qActualAfterRowOraclePreimage_physicalEvent_eq configuration source
    member direction] at result
  exact result

/-- 物理eventのrow逆追跡後もamplitude signalは1のままである。 -/
theorem qActualAfterRowOraclePreimage_physicalEvent_amplitude_true
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    qActualAfterRowOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)
        (amplitudeSignalWire p) = true := by
  have result := qActualAfterRowOraclePreimage_physicalEvent_result configuration
    source member direction
  rw [result.outside_restored (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_columnKeyWires p)
    (amplitudeSignalWire_not_mem_columnSelectorWires p)
    (amplitudeSignalWire_ne_keySignalWire p)]
  exact qActualAfterFinalFlipPreimage_amplitudeSignal p _ _

/-- 物理eventのrow逆追跡後のactive bitは0である。 -/
theorem qActualAfterRowOraclePreimage_physicalEvent_active_false
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    qActualAfterRowOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)
        (activeWire p) = false := by
  have result := qActualAfterRowOraclePreimage_physicalEvent_result configuration
    source member direction
  rw [result.outside_restored (activeWire p)
    (qActualActiveWire_not_mem_columnKeyWires p)
    (qActualActiveWire_not_mem_columnSelectorWires p)
    (qActualActiveWire_ne_keySignalWire p)]
  exact qActualAfterFinalFlipPreimage_active_false p _ _

/-- 物理eventのrow逆追跡後のnegative bitは0である。 -/
theorem qActualAfterRowOraclePreimage_physicalEvent_negative_false
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    qActualAfterRowOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)
        (negativeWire p) = false := by
  have result := qActualAfterRowOraclePreimage_physicalEvent_result configuration
    source member direction
  rw [result.outside_restored (negativeWire p)
    (qActualNegativeWire_not_mem_columnKeyWires p)
    (qActualNegativeWire_not_mem_columnSelectorWires p)
    (qActualNegativeWire_ne_keySignalWire p)]
  exact qActualAfterFinalFlipPreimage_negative_false p _ _

/-- 物理eventのrow逆追跡後もrow-output accumulatorは全0である。 -/
theorem qActualAfterRowOraclePreimage_physicalEvent_rowOutput_zero
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    readWires (rowOutputWires p)
        (qActualAfterRowOraclePreimage p
          (delimiterEncoding (eventOutput configuration source direction))
          (rowSelectorForEvent configuration source member direction)) =
      List.replicate (rowOutputWires p).length false := by
  have result := qActualAfterRowOraclePreimage_physicalEvent_result configuration
    source member direction
  calc
    readWires (rowOutputWires p)
        (qActualAfterRowOraclePreimage p
          (delimiterEncoding (eventOutput configuration source direction))
          (rowSelectorForEvent configuration source member direction)) =
        readWires (rowOutputWires p)
          (qActualAfterFinalFlipPreimage p
            (delimiterEncoding (eventOutput configuration source direction))
            (rowSelectorForEvent configuration source member direction)) := by
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

/-- 物理eventのrow逆追跡後もselector-output accumulatorは全0である。 -/
theorem qActualAfterRowOraclePreimage_physicalEvent_selectorOutput_zero
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    readWires (selectorOutputWires p)
        (qActualAfterRowOraclePreimage p
          (delimiterEncoding (eventOutput configuration source direction))
          (rowSelectorForEvent configuration source member direction)) =
      List.replicate (selectorOutputWires p).length false := by
  have result := qActualAfterRowOraclePreimage_physicalEvent_result configuration
    source member direction
  calc
    readWires (selectorOutputWires p)
        (qActualAfterRowOraclePreimage p
          (delimiterEncoding (eventOutput configuration source direction))
          (rowSelectorForEvent configuration source member direction)) =
        readWires (selectorOutputWires p)
          (qActualAfterFinalFlipPreimage p
            (delimiterEncoding (eventOutput configuration source direction))
            (rowSelectorForEvent configuration source member direction)) := by
      apply List.map_congr_left
      intro wire wireMember
      exact result.outside_restored wire
        ((List.disjoint_left.mp
          (qActualSelectorOutputWires_disjoint_columnKeyWires p)) wireMember)
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

/-- 物理eventのrow逆追跡基底は、続くcolumn oracleの一般canonical入力仕様を満たす。 -/
theorem qActualAfterRowOraclePreimage_physicalEvent_columnInputSpec
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    ColumnOracleInputSpec p configuration
      (selectorForEvent configuration source member direction)
      (qActualAfterRowOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)) := by
  let outputConfiguration := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let initial := qActualAfterFinalFlipPreimage p
    (delimiterEncoding outputConfiguration) rowSelector
  let actual := qActualAfterRowOraclePreimage p
    (delimiterEncoding outputConfiguration) rowSelector
  have result : RowReferenceBranchResult p configuration columnSelector
      initial actual := by
    simpa [initial, actual, outputConfiguration, rowSelector, columnSelector] using
      qActualAfterRowOraclePreimage_physicalEvent_result configuration source
        member direction
  refine {
    column_key_bits := ?_
    selector_bits := ?_
    work_zero := ?_ }
  · rw [result.column_key]
    have initialZero : readWires (columnKeyWires p) initial =
        List.replicate (columnKeyWires p).length false := by
      simpa [initial] using qActualAfterFinalFlipPreimage_columnKey_zero p
        (delimiterEncoding outputConfiguration) rowSelector
    rw [initialZero]
    simpa [xorRegisterBits, registerBitList] using
      xorRegisterBits_replicate_false
        (registerBitList (delimiterEncoding configuration))
  · rw [result.column_selector]
    have initialZero : readWires (columnSelectorWires p) initial =
        List.replicate (columnSelectorWires p).length false := by
      simpa [initial] using qActualAfterFinalFlipPreimage_columnSelector_zero p
        (delimiterEncoding outputConfiguration) rowSelector
    rw [initialZero]
    simpa [constantBits] using
      controlledXorConstantBits_true_replicate_false columnSelector.val 0
        (columnSelectorWires p).length
  · intro wire workMember
    change actual wire = false
    rw [result.support_restored wire (List.mem_append_right _ workMember)]
    exact qActualAfterFinalFlipPreimage_oracleWork_zero p
      (delimiterEncoding outputConfiguration) rowSelector workMember

/-- 物理eventのrow逆追跡基底をcolumn persistent computeへ通した状態は全branch共通仕様を満たす。 -/
theorem qActualAfterRowOraclePreimage_physicalEvent_columnPersistentSpec
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    ColumnOraclePersistentConditionsSpec p configuration
      (selectorForEvent configuration source member direction)
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p (columnKeyWires p) false).runBasis
        reversibleGatePermutation
        (qActualAfterRowOraclePreimage p
          (delimiterEncoding (eventOutput configuration source direction))
          (rowSelectorForEvent configuration source member direction))) :=
  (qActualAfterRowOraclePreimage_physicalEvent_columnInputSpec configuration
    source member direction).afterPersistent

/-- column inverse回路を逆追跡し、正方向column実行を終えた直後の基底。 -/
def qActualAfterColumnInversePreimage (p : QParameters)
    (output : RegisterBasis p.systemWidth) (rowSelector : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (applyColumnOracleReferenceAndRestoreWorkCircuit p).toExecutionPermutation
    reversibleGatePermutation (qActualAfterRowOraclePreimage p output rowSelector)

/-- column逆回路を逆追跡する段は、正方向column oracleの基底実行そのものである。 -/
theorem qActualAfterColumnInversePreimage_eq_runBasis
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    qActualAfterColumnInversePreimage p output rowSelector =
      (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation
        (qActualAfterRowOraclePreimage p output rowSelector) := by
  rfl

/-- 物理eventのcolumn参照受理pathでは、column正方向逆追跡像が参照XOR仕様を満たす。 -/
theorem qActualAfterColumnInversePreimage_physicalEvent_result
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) (reference : ColumnReferenceResult p)
    (referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference) :
    ColumnReferenceBranchResult p reference
      (qActualAfterRowOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction))
      (qActualAfterColumnInversePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)) := by
  rw [qActualAfterColumnInversePreimage_eq_runBasis]
  exact applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some configuration
    (selectorForEvent configuration source member direction) reference _
    (qActualAfterRowOraclePreimage_physicalEvent_columnInputSpec configuration
      source member direction) referenceSome

/-- 物理eventのcolumn参照拒否pathでは、column正方向逆追跡段は入力基底を固定する。 -/
theorem qActualAfterColumnInversePreimage_physicalEvent_eq_of_reference_none
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection)
    (referenceNone : columnReference configuration
      (selectorForEvent configuration source member direction) = none) :
    qActualAfterColumnInversePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction) =
      qActualAfterRowOraclePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction) := by
  rw [qActualAfterColumnInversePreimage_eq_runBasis]
  exact applyColumnOracleReferenceAndRestoreWorkCircuit_reference_none configuration
    (selectorForEvent configuration source member direction) _
    (qActualAfterRowOraclePreimage_physicalEvent_columnInputSpec configuration
      source member direction) referenceNone

/-- 受理された物理eventのcolumn逆追跡後もamplitude signalは1である。 -/
theorem qActualAfterColumnInversePreimage_physicalEvent_amplitude_true
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) (reference : ColumnReferenceResult p)
    (referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference) :
    qActualAfterColumnInversePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)
        (amplitudeSignalWire p) = true := by
  have result := qActualAfterColumnInversePreimage_physicalEvent_result
    configuration source member direction reference referenceSome
  rw [result.outside_restored (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_rowOutputWires p)
    (amplitudeSignalWire_not_mem_selectorOutputWires p)
    (negativeWire_ne_amplitudeSignalWire p).symm
    (activeWire_ne_amplitudeSignalWire p).symm]
  exact qActualAfterRowOraclePreimage_physicalEvent_amplitude_true configuration
    source member direction

/-- 受理された物理eventのcolumn逆追跡後のactive bitは1である。 -/
theorem qActualAfterColumnInversePreimage_physicalEvent_active_true
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) (reference : ColumnReferenceResult p)
    (referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference) :
    qActualAfterColumnInversePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)
        (activeWire p) = true := by
  have result := qActualAfterColumnInversePreimage_physicalEvent_result
    configuration source member direction reference referenceSome
  rw [result.active,
    qActualAfterRowOraclePreimage_physicalEvent_active_false configuration
      source member direction]
  rfl

/-- 受理された物理eventのcolumn逆追跡後のnegative bitは参照符号に一致する。 -/
theorem qActualAfterColumnInversePreimage_physicalEvent_negative_eq
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) (reference : ColumnReferenceResult p)
    (referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference) :
    qActualAfterColumnInversePreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)
        (negativeWire p) = reference.negative := by
  have result := qActualAfterColumnInversePreimage_physicalEvent_result
    configuration source member direction reference referenceSome
  rw [result.negative,
    qActualAfterRowOraclePreimage_physicalEvent_negative_false configuration
      source member direction]
  cases reference.negative <;> rfl

/-- align回路を逆に通し、振幅判別直後へ戻した基底。 -/
def qActualDiscriminatorOutputPreimage (p : QParameters)
    (output : RegisterBasis p.systemWidth) (rowSelector : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).toBasisPermutation reversibleGatePermutation
    (qActualAfterColumnInversePreimage p output rowSelector)

/-- align候補入力がcolumn逆回路の逆追跡像へ実行されるなら、align逆像はその候補に一致する。 -/
theorem qActualDiscriminatorOutputPreimage_eq_of_runBasis
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (candidate : JointBasis p.ancillaWidth p.systemWidth)
    (executed : (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation
      candidate = qActualAfterColumnInversePreimage p output rowSelector) :
    qActualDiscriminatorOutputPreimage p output rowSelector = candidate := by
  unfold qActualDiscriminatorOutputPreimage
  exact toBasisPermutation_apply_of_runBasis_eq _ candidate _ executed

/-- 整列回路の自己逆性により、整列逆追跡像は同じ回路の正方向実行で表せる。 -/
theorem qActualDiscriminatorOutputPreimage_eq_alignRunBasis
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    qActualDiscriminatorOutputPreimage p output rowSelector =
      (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation
        (qActualAfterColumnInversePreimage p output rowSelector) := by
  apply qActualDiscriminatorOutputPreimage_eq_of_runBasis
  exact controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_involutive p
    (qActualAfterColumnInversePreimage p output rowSelector)

/-- 受理された物理eventの整列逆追跡像ではamplitude signalが1である。 -/
theorem qActualDiscriminatorOutputPreimage_physicalEvent_amplitude_true
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) (reference : ColumnReferenceResult p)
    (referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference) :
    qActualDiscriminatorOutputPreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)
        (amplitudeSignalWire p) = true := by
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _
    (amplitudeSignalWire p)
    (amplitudeSignalWire_not_mem_systemWires p)
    (amplitudeSignalWire_not_mem_rowSelectorWires p)
    (amplitudeSignalWire_ne_keySignalWire p)]
  exact qActualAfterColumnInversePreimage_physicalEvent_amplitude_true
    configuration source member direction reference referenceSome

/-- 受理された物理eventの整列逆追跡像ではactive bitが1である。 -/
theorem qActualDiscriminatorOutputPreimage_physicalEvent_active_true
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) (reference : ColumnReferenceResult p)
    (referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference) :
    qActualDiscriminatorOutputPreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)
        (activeWire p) = true := by
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _ (activeWire p)
    (qActualActiveWire_not_mem_systemWires p)
    (qActualActiveWire_not_mem_rowSelectorWires p)
    (qActualActiveWire_ne_keySignalWire p)]
  exact qActualAfterColumnInversePreimage_physicalEvent_active_true
    configuration source member direction reference referenceSome

/-- 受理された物理eventの整列逆追跡像ではnegative bitが参照符号に一致する。 -/
theorem qActualDiscriminatorOutputPreimage_physicalEvent_negative_eq
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) (reference : ColumnReferenceResult p)
    (referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference) :
    qActualDiscriminatorOutputPreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)
        (negativeWire p) = reference.negative := by
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _ (negativeWire p)
    (qActualNegativeWire_not_mem_systemWires p)
    (qActualNegativeWire_not_mem_rowSelectorWires p)
    (qActualNegativeWire_ne_keySignalWire p)]
  exact qActualAfterColumnInversePreimage_physicalEvent_negative_eq
    configuration source member direction reference referenceSome

/-- 明示した逆追跡stage列は、状態pipelineの振幅判別出力preimageと定義的に一致する。 -/
theorem qActualDiscriminatorOutputPreimage_eq
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    qActualDiscriminatorOutputPreimage p output rowSelector =
      qDiscriminatorOutputPreimage p
        (qFinalRowSelectorBasis p output rowSelector) := by
  simp only [qActualDiscriminatorOutputPreimage,
    qActualAfterColumnInversePreimage, qActualAfterRowOraclePreimage,
    qActualAfterFinalFlipPreimage, qDiscriminatorOutputPreimage]

/-- 振幅判別CNOTを逆に通し、column oracle出力へ戻した基底。 -/
def qActualAfterDiscriminatorPreimage (p : QParameters)
    (output : RegisterBasis p.systemWidth) (rowSelector : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth :=
  cnotBasisAction (activeWire p) (amplitudeSignalWire p)
    (qActualDiscriminatorOutputPreimage p output rowSelector)

/-- 受理された物理eventのdiscriminator逆追跡像はcolumn oracle入力仕様を保つ。 -/
theorem qActualAfterDiscriminatorPreimage_physicalEvent_columnInputSpec
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    ColumnOracleInputSpec p configuration
      (selectorForEvent configuration source member direction)
      (qActualAfterDiscriminatorPreimage p
        (delimiterEncoding (eventOutput configuration source direction))
        (rowSelectorForEvent configuration source member direction)) := by
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  have referenceSome : columnReference configuration columnSelector =
      some reference := by
    simpa [output, rowSelector, columnSelector, reference] using
      columnReference_selectorForEvent_exact configuration source member direction
  have firstResult :=
    qActualAfterColumnInversePreimage_physicalEvent_result configuration source
      member direction reference referenceSome
  have beforeSpec :=
    qActualAfterRowOraclePreimage_physicalEvent_columnInputSpec configuration
      source member direction
  have afterColumnSpec :=
    ColumnReferenceBranchResult.preservesInputSpec beforeSpec firstResult
  have afterAlignSpec :=
    ProbabilityGeneratorQProof.ColumnOracleInputSpec.afterAlignDiscriminator
      afterColumnSpec
  change ColumnOracleInputSpec p configuration columnSelector
    (cnotBasisAction (activeWire p) (amplitudeSignalWire p)
      (qActualDiscriminatorOutputPreimage p (delimiterEncoding output)
        rowSelector))
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  simpa [output, rowSelector, columnSelector] using afterAlignSpec

/-- discriminator逆追跡像は整列対象とamplitude以外ではcolumn逆追跡像を保存する。 -/
theorem qActualAfterDiscriminatorPreimage_eq_afterColumnInverse_on_wire
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outsideSystem : wire ∉ systemWires p)
    (outsideRowSelector : wire ∉ rowSelectorWires p)
    (differentKeySignal : wire ≠ keySignalWire p)
    (differentAmplitude : wire ≠ amplitudeSignalWire p) :
    qActualAfterDiscriminatorPreimage p output rowSelector wire =
      qActualAfterColumnInversePreimage p output rowSelector wire := by
  unfold qActualAfterDiscriminatorPreimage
  rw [cnotBasisAction_control_or_other (activeWire p)
    (amplitudeSignalWire p) wire differentAmplitude]
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis]
  exact controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_outside_targets p _ wire outsideSystem
    outsideRowSelector differentKeySignal

/-- discriminator逆追跡像は対象外registerの読出しをcolumn逆追跡像と同じに保つ。 -/
theorem qActualAfterDiscriminatorPreimage_readWires_eq_afterColumnInverse
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (wires : List (Wire p.ancillaWidth p.systemWidth))
    (outsideSystem : wires.Disjoint (systemWires p))
    (outsideRowSelector : wires.Disjoint (rowSelectorWires p))
    (keySignalAbsent : keySignalWire p ∉ wires)
    (amplitudeAbsent : amplitudeSignalWire p ∉ wires) :
    readWires wires (qActualAfterDiscriminatorPreimage p output rowSelector) =
      readWires wires
        (qActualAfterColumnInversePreimage p output rowSelector) := by
  apply List.map_congr_left
  intro wire member
  apply qActualAfterDiscriminatorPreimage_eq_afterColumnInverse_on_wire
  · exact (List.disjoint_left.mp outsideSystem) member
  · exact (List.disjoint_left.mp outsideRowSelector) member
  · intro equal
    exact keySignalAbsent (equal ▸ member)
  · intro equal
    exact amplitudeAbsent (equal ▸ member)

/-- column oracleを逆に通し、COPY直後へ戻した基底。 -/
def qActualAfterColumnOraclePreimage (p : QParameters)
    (output : RegisterBasis p.systemWidth) (rowSelector : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (applyColumnOracleReferenceAndRestoreWorkCircuit p).toBasisPermutation
    reversibleGatePermutation
    (qActualAfterDiscriminatorPreimage p output rowSelector)

/-- column oracle候補入力が判別逆像へ実行されるなら、column逆追跡基底はその候補に一致する。 -/
theorem qActualAfterColumnOraclePreimage_eq_of_runBasis
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (candidate : JointBasis p.ancillaWidth p.systemWidth)
    (executed : (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis
      reversibleGatePermutation candidate =
        qActualAfterDiscriminatorPreimage p output rowSelector) :
    qActualAfterColumnOraclePreimage p output rowSelector = candidate := by
  unfold qActualAfterColumnOraclePreimage
  exact toBasisPermutation_apply_of_runBasis_eq _ candidate _ executed

/-- 受理された物理eventでは、二回目のcolumn oracleも同じ参照XOR仕様を満たす。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_result
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
    ColumnReferenceBranchResult p reference
      (qActualAfterDiscriminatorPreimage p (delimiterEncoding output) rowSelector)
      (qActualAfterColumnOraclePreimage p (delimiterEncoding output) rowSelector) := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let discriminator := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding output) rowSelector
  have referenceSome : columnReference configuration columnSelector =
      some reference := by
    simpa [output, rowSelector, columnSelector, reference] using
      columnReference_selectorForEvent_exact configuration source member direction
  have inputSpec : ColumnOracleInputSpec p configuration columnSelector
      discriminator := by
    simpa [output, rowSelector, columnSelector, discriminator] using
      qActualAfterDiscriminatorPreimage_physicalEvent_columnInputSpec
        configuration source member direction
  have twice := applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some_involutive
    configuration columnSelector reference discriminator inputSpec referenceSome
  have actualEq : actual =
      (applyColumnOracleReferenceAndRestoreWorkCircuit p).runBasis reversibleGatePermutation
        discriminator := by
    apply qActualAfterColumnOraclePreimage_eq_of_runBasis
    exact twice
  have result := applyColumnOracleReferenceAndRestoreWorkCircuit_reference_some configuration
    columnSelector reference discriminator inputSpec referenceSome
  rw [← actualEq] at result
  simpa [output, rowSelector, columnSelector, reference, discriminator, actual]
    using result

/-- 物理eventの二回目column oracleはrow-output accumulatorをrow前の値へ戻す。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_readRowOutput
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    readWires (rowOutputWires p)
        (qActualAfterColumnOraclePreimage p (delimiterEncoding output)
          rowSelector) =
      readWires (rowOutputWires p)
        (qActualAfterRowOraclePreimage p (delimiterEncoding output)
          rowSelector) := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding output) rowSelector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding output) rowSelector
  let afterDiscriminator := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
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
  have secondResult : ColumnReferenceBranchResult p reference afterDiscriminator
      actual := by
    simpa [output, rowSelector, reference, afterDiscriminator, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_result configuration source
        member direction
  have targetPreserved : readWires (rowOutputWires p) afterDiscriminator =
      readWires (rowOutputWires p) afterColumn := by
    apply qActualAfterDiscriminatorPreimage_readWires_eq_afterColumnInverse
    · exact qTopRowOutputWires_disjoint_systemWires p
    · exact qActualRowOutputWires_disjoint_rowSelectorWires p
    · exact qActualKeySignalWire_not_mem_rowOutputWires p
    · exact amplitudeSignalWire_not_mem_rowOutputWires p
  change readWires (rowOutputWires p) actual =
    readWires (rowOutputWires p) afterRow
  rw [secondResult.row_output, targetPreserved, firstResult.row_output]
  apply xorRegisterBits_involutive_of_length
  simp only [readWires, List.length_map, registerBitList]
  simp [rowOutputWires]

/-- 物理eventの二回目column oracleはselector-output accumulatorをrow前の値へ戻す。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_readSelectorOutput
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    readWires (selectorOutputWires p)
        (qActualAfterColumnOraclePreimage p (delimiterEncoding output)
          rowSelector) =
      readWires (selectorOutputWires p)
        (qActualAfterRowOraclePreimage p (delimiterEncoding output)
          rowSelector) := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let columnSelector := selectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding output) rowSelector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding output) rowSelector
  let afterDiscriminator := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
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
  have secondResult : ColumnReferenceBranchResult p reference afterDiscriminator
      actual := by
    simpa [output, rowSelector, reference, afterDiscriminator, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_result configuration source
        member direction
  have targetPreserved : readWires (selectorOutputWires p) afterDiscriminator =
      readWires (selectorOutputWires p) afterColumn := by
    apply qActualAfterDiscriminatorPreimage_readWires_eq_afterColumnInverse
    · exact qTopSelectorOutputWires_disjoint_systemWires p
    · exact qTopSelectorOutputWires_disjoint_rowSelectorWires p
    · exact qActualKeySignalWire_not_mem_selectorOutputWires p
    · exact amplitudeSignalWire_not_mem_selectorOutputWires p
  change readWires (selectorOutputWires p) actual =
    readWires (selectorOutputWires p) afterRow
  rw [secondResult.selector_output, targetPreserved, firstResult.selector_output]
  exact controlledXorConstantBits_true_involutive reference.rowSelector.val 0 _

/-- 物理eventの二回目column oracleはnegative accumulatorをrow前の値へ戻す。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_negative
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualAfterColumnOraclePreimage p (delimiterEncoding output) rowSelector
        (negativeWire p) =
      qActualAfterRowOraclePreimage p (delimiterEncoding output) rowSelector
        (negativeWire p) := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding output) rowSelector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding output) rowSelector
  let afterDiscriminator := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding output) rowSelector
  have referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference := by
    simpa [output, rowSelector, reference] using
      columnReference_selectorForEvent_exact configuration source member direction
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [output, rowSelector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_physicalEvent_result configuration source
        member direction reference referenceSome
  have secondResult : ColumnReferenceBranchResult p reference afterDiscriminator
      actual := by
    simpa [output, rowSelector, reference, afterDiscriminator, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_result configuration source
        member direction
  have targetPreserved : afterDiscriminator (negativeWire p) =
      afterColumn (negativeWire p) := by
    apply qActualAfterDiscriminatorPreimage_eq_afterColumnInverse_on_wire
    · exact qActualNegativeWire_not_mem_systemWires p
    · exact qActualNegativeWire_not_mem_rowSelectorWires p
    · exact qActualNegativeWire_ne_keySignalWire p
    · exact negativeWire_ne_amplitudeSignalWire p
  change actual (negativeWire p) = afterRow (negativeWire p)
  rw [secondResult.negative, targetPreserved, firstResult.negative]
  rfl

/-- 物理eventの二回目column oracleはactive accumulatorをrow前の値へ戻す。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_active
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualAfterColumnOraclePreimage p (delimiterEncoding output) rowSelector
        (activeWire p) =
      qActualAfterRowOraclePreimage p (delimiterEncoding output) rowSelector
        (activeWire p) := by
  dsimp only
  let output := eventOutput configuration source direction
  let rowSelector := rowSelectorForEvent configuration source member direction
  let reference : ColumnReferenceResult p := ⟨output, rowSelector, false⟩
  let afterRow := qActualAfterRowOraclePreimage p
    (delimiterEncoding output) rowSelector
  let afterColumn := qActualAfterColumnInversePreimage p
    (delimiterEncoding output) rowSelector
  let afterDiscriminator := qActualAfterDiscriminatorPreimage p
    (delimiterEncoding output) rowSelector
  let actual := qActualAfterColumnOraclePreimage p
    (delimiterEncoding output) rowSelector
  have referenceSome : columnReference configuration
      (selectorForEvent configuration source member direction) = some reference := by
    simpa [output, rowSelector, reference] using
      columnReference_selectorForEvent_exact configuration source member direction
  have firstResult : ColumnReferenceBranchResult p reference afterRow
      afterColumn := by
    simpa [output, rowSelector, reference, afterRow, afterColumn] using
      qActualAfterColumnInversePreimage_physicalEvent_result configuration source
        member direction reference referenceSome
  have secondResult : ColumnReferenceBranchResult p reference afterDiscriminator
      actual := by
    simpa [output, rowSelector, reference, afterDiscriminator, actual] using
      qActualAfterColumnOraclePreimage_physicalEvent_result configuration source
        member direction
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

/-- 物理eventの二回目column oracle後のrow-output accumulatorは全0である。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_rowOutput_zero
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    readWires (rowOutputWires p)
        (qActualAfterColumnOraclePreimage p (delimiterEncoding output)
          rowSelector) = List.replicate (rowOutputWires p).length false := by
  dsimp only
  rw [qActualAfterColumnOraclePreimage_physicalEvent_readRowOutput]
  exact qActualAfterRowOraclePreimage_physicalEvent_rowOutput_zero configuration
    source member direction

/-- 物理eventの二回目column oracle後のselector-output accumulatorは全0である。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_selectorOutput_zero
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    readWires (selectorOutputWires p)
        (qActualAfterColumnOraclePreimage p (delimiterEncoding output)
          rowSelector) = List.replicate (selectorOutputWires p).length false := by
  dsimp only
  rw [qActualAfterColumnOraclePreimage_physicalEvent_readSelectorOutput]
  exact qActualAfterRowOraclePreimage_physicalEvent_selectorOutput_zero
    configuration source member direction

/-- 物理eventの二回目column oracle後のnegative bitは0である。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_negative_false
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualAfterColumnOraclePreimage p (delimiterEncoding output) rowSelector
        (negativeWire p) = false := by
  dsimp only
  rw [qActualAfterColumnOraclePreimage_physicalEvent_negative]
  exact qActualAfterRowOraclePreimage_physicalEvent_negative_false configuration
    source member direction

/-- 物理eventの二回目column oracle後のactive bitは0である。 -/
theorem qActualAfterColumnOraclePreimage_physicalEvent_active_false
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    qActualAfterColumnOraclePreimage p (delimiterEncoding output) rowSelector
        (activeWire p) = false := by
  dsimp only
  rw [qActualAfterColumnOraclePreimage_physicalEvent_active]
  exact qActualAfterRowOraclePreimage_physicalEvent_active_false configuration
    source member direction

/-- 物理eventのdiscriminator逆追跡後のsystem registerはpredecessor配置になる。 -/
theorem qActualAfterDiscriminatorPreimage_physicalEvent_readSystem
    {p : QParameters} (configuration : QConfiguration p)
    (source : QSite p) (member : source ∈ configuration.1)
    (direction : QDirection) :
    let output := eventOutput configuration source direction
    let rowSelector := rowSelectorForEvent configuration source member direction
    readWires (systemWires p)
        (qActualAfterDiscriminatorPreimage p (delimiterEncoding output)
          rowSelector) = registerBitList (delimiterEncoding configuration) := by
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
  have systemAfterColumn : readWires (systemWires p) afterColumn =
      registerBitList (delimiterEncoding output) := by
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
      _ = registerBitList (delimiterEncoding output) := afterRowSpec.system_bits
  have rowOutputAfterColumn : readWires (rowOutputWires p) afterColumn =
      registerBitList (delimiterEncoding output) := by
    rw [firstResult.row_output,
      qActualAfterRowOraclePreimage_physicalEvent_rowOutput_zero configuration
        source member direction]
    simpa [reference, xorRegisterBits, registerBitList, rowOutputWires] using
      xorRegisterBits_replicate_false
        (registerBitList (delimiterEncoding output))
  have columnKeyAfterColumn : readWires (columnKeyWires p) afterColumn =
      registerBitList (delimiterEncoding configuration) := by
    exact (ColumnReferenceBranchResult.preservesInputSpec
      (qActualAfterRowOraclePreimage_physicalEvent_columnInputSpec configuration
        source member direction) firstResult).column_key_bits
  unfold qActualAfterDiscriminatorPreimage
  rw [readWires_cnotBasisAction_of_not_mem (systemWires p)
    (activeWire p) (amplitudeSignalWire p) _
    (amplitudeSignalWire_not_mem_systemWires p)]
  rw [qActualDiscriminatorOutputPreimage_eq_alignRunBasis,
    controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readSystem]
  rw [qActualAfterColumnInversePreimage_physicalEvent_amplitude_true
    configuration source member direction reference referenceSome]
  rw [rowOutputAfterColumn, columnKeyAfterColumn, systemAfterColumn]
  apply xorRegisterBits_sandwich
  simp [registerBitList]

/-- 最終row selector基底を全可逆回路へ逆向きに通して得るcolumn準備直後のpreimage。 -/
def qActualColumnPreparedPreimage (p : QParameters)
    (output : RegisterBasis p.systemWidth) (rowSelector : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth :=
  qColumnPreparedPreimage p (qFinalRowSelectorBasis p output rowSelector)

/-- 明示した全逆追跡stage列をCOPYまで戻すと、column準備preimageそのものになる。 -/
theorem qActualColumnPreparedPreimage_eq_stages
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    qActualColumnPreparedPreimage p output rowSelector =
      (xorSystemIntoColumnKeyReversibleCircuit p).toBasisPermutation
        reversibleGatePermutation
        (qActualAfterColumnOraclePreimage p output rowSelector) := by
  unfold qActualColumnPreparedPreimage qColumnPreparedPreimage
  unfold qActualAfterColumnOraclePreimage qActualAfterDiscriminatorPreimage
  rw [qActualDiscriminatorOutputPreimage_eq]

/-- COPY候補入力がcolumn逆追跡像へ実行されるなら、最初の一様基底逆像はその候補である。 -/
theorem qActualColumnPreparedPreimage_eq_of_copy_runBasis
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (candidate : JointBasis p.ancillaWidth p.systemWidth)
    (executed : (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
      reversibleGatePermutation candidate =
        qActualAfterColumnOraclePreimage p output rowSelector) :
    qActualColumnPreparedPreimage p output rowSelector = candidate := by
  rw [qActualColumnPreparedPreimage_eq_stages]
  exact toBasisPermutation_apply_of_runBasis_eq _ candidate _ executed

/-- 最終row selector基底の逆追跡pathに付く振幅判別回路の符号。 -/
def qActualSelectorPathPhase (p : QParameters)
    (output : RegisterBasis p.systemWidth) (rowSelector : QSelector p) : ℂ :=
  let preimage := qDiscriminatorOutputPreimage p
    (qFinalRowSelectorBasis p output rowSelector)
  if preimage (negativeWire p) && preimage (amplitudeSignalWire p) then -1 else 1

/-- 判別出力逆像のnegative・amplitude bitが既知なら、path位相をその符号へ簡約できる。 -/
theorem qActualSelectorPathPhase_eq_of_signals
    (p : QParameters) (output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) (negative : Bool)
    (negativeEq : qActualDiscriminatorOutputPreimage p output rowSelector
      (negativeWire p) = negative)
    (amplitudeEq : qActualDiscriminatorOutputPreimage p output rowSelector
      (amplitudeSignalWire p) = true) :
    qActualSelectorPathPhase p output rowSelector =
      if negative then -1 else 1 := by
  have negativeEq' : qDiscriminatorOutputPreimage p
      (qFinalRowSelectorBasis p output rowSelector) (negativeWire p) =
      negative := by
    rw [← qActualDiscriminatorOutputPreimage_eq]
    exact negativeEq
  have amplitudeEq' : qDiscriminatorOutputPreimage p
      (qFinalRowSelectorBasis p output rowSelector) (amplitudeSignalWire p) =
      true := by
    rw [← qActualDiscriminatorOutputPreimage_eq]
    exact amplitudeEq
  simp [qActualSelectorPathPhase, negativeEq', amplitudeEq']

/-- 最終row selector基底上の振幅は、逆追跡preimage上のcolumn準備振幅とpath符号の積である。 -/
theorem qBeforeRowUniformInverseState_finalSelector_eq
    (p : QParameters) (input output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    qBeforeRowUniformInverseState p input
        (qFinalRowSelectorBasis p output rowSelector) =
      qActualSelectorPathPhase p output rowSelector *
        qColumnPreparedState p input
          (qActualColumnPreparedPreimage p output rowSelector) := by
  simpa [qActualSelectorPathPhase, qActualColumnPreparedPreimage] using
    qBeforeRowUniformInverseState_apply p input
      (qFinalRowSelectorBasis p output rowSelector)

/-- 逆追跡preimageのcolumn準備振幅が0なら、最終selector pathの振幅も0である。 -/
theorem qBeforeRowUniformInverseState_finalSelector_eq_zero
    (p : QParameters) (input output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (preparedZero : qColumnPreparedState p input
      (qActualColumnPreparedPreimage p output rowSelector) = 0) :
    qBeforeRowUniformInverseState p input
        (qFinalRowSelectorBasis p output rowSelector) = 0 := by
  rw [qBeforeRowUniformInverseState_finalSelector_eq, preparedZero, mul_zero]

/-- selector外が初期背景と一致しない逆追跡pathは振幅0になる。 -/
theorem qBeforeRowUniformInverseState_finalSelector_eq_zero_of_outside_mismatch
    (p : QParameters) (input output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (mismatch : ¬OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p input)
      (qActualColumnPreparedPreimage p output rowSelector)) :
    qBeforeRowUniformInverseState p input
        (qFinalRowSelectorBasis p output rowSelector) = 0 := by
  apply qBeforeRowUniformInverseState_finalSelector_eq_zero p input output rowSelector
  exact qColumnPreparedState_eq_zero_of_outside_mismatch p input _ mismatch

/-- 逆追跡されたcolumn selectorがpadding領域なら、そのpath振幅は0になる。 -/
theorem qBeforeRowUniformInverseState_finalSelector_eq_zero_of_padding
    (p : QParameters) (input output : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p)
    (padding : p.selectorCount ≤ selectorValue p.selectorWidth
      (projectSelectorBasis p (columnSelectorWire p)
        (qActualColumnPreparedPreimage p output rowSelector))) :
    qBeforeRowUniformInverseState p input
        (qFinalRowSelectorBasis p output rowSelector) = 0 := by
  apply qBeforeRowUniformInverseState_finalSelector_eq_zero p input output rowSelector
  exact qColumnPreparedState_eq_zero_of_projected_padding p input _ padding

/-- canonical column preimageとpath符号が分かれば、実path振幅を厳密に計算できる。 -/
theorem qBeforeRowUniformInverseState_finalSelector_of_canonical_preimage
    (p : QParameters) (input output : QConfiguration p)
    (rowSelector columnSelector : QSelector p) (negative : Bool)
    (preimageEq : qActualColumnPreparedPreimage p
      (delimiterEncoding output) rowSelector =
        qCanonicalColumnInitialBasis p input columnSelector)
    (phaseEq : qActualSelectorPathPhase p
      (delimiterEncoding output) rowSelector =
        if negative then -1 else 1) :
    qBeforeRowUniformInverseState p (delimiterEncoding input)
        (qFinalRowSelectorBasis p (delimiterEncoding output) rowSelector) =
      ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
        (if negative then -1 else 1) := by
  rw [qBeforeRowUniformInverseState_finalSelector_eq, preimageEq,
    qColumnPreparedState_qCanonicalColumnInitialBasis, phaseEq]
  exact mul_comm _ _

/-- row・column参照が同じ物理pathを受理するとき、期待selector振幅は一様振幅と符号の積になる。 -/
theorem PrefixAmplitudeReferenceCaseSpec_of_accepted
    {p : QParameters} (output input : QConfiguration p)
    (rowSelector : QSelector p) (rowResult : RowReferenceResult p)
    (columnResult : ColumnReferenceResult p)
    (rowAccepted : rowReference output rowSelector = some rowResult)
    (columnAccepted : columnReference input rowResult.columnSelector =
      some columnResult)
    (rowSelectorEq : columnResult.rowSelector = rowSelector)
    (outputEq : columnResult.output = output)
    (inputEq : rowResult.input = input) :
    PrefixAmplitudeReferenceCaseSpec p
        (delimiterEncoding output) (delimiterEncoding input) rowSelector =
      ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
        (if columnResult.negative then -1 else 1) := by
  simp [PrefixAmplitudeReferenceCaseSpec,
    reverseReferenceAcceptedRowSelectorWeight, rowAccepted, columnAccepted,
    rowSelectorEq, outputEq, inputEq]
  cases columnResult.negative <;> simp

/-- canonical実pathのpreimage・符号仕様から、そのselector振幅が期待値に一致する。 -/
theorem qBeforeRowUniformInverseState_finalSelector_of_accepted_path
    (p : QParameters) (output input : QConfiguration p)
    (rowSelector : QSelector p) (rowResult : RowReferenceResult p)
    (columnResult : ColumnReferenceResult p)
    (rowAccepted : rowReference output rowSelector = some rowResult)
    (columnAccepted : columnReference input rowResult.columnSelector =
      some columnResult)
    (rowSelectorEq : columnResult.rowSelector = rowSelector)
    (outputEq : columnResult.output = output)
    (inputEq : rowResult.input = input)
    (preimageEq : qActualColumnPreparedPreimage p
      (delimiterEncoding output) rowSelector =
        qCanonicalColumnInitialBasis p input rowResult.columnSelector)
    (phaseEq : qActualSelectorPathPhase p
      (delimiterEncoding output) rowSelector =
        if columnResult.negative then -1 else 1) :
    qBeforeRowUniformInverseState p (delimiterEncoding input)
        (qFinalRowSelectorBasis p (delimiterEncoding output) rowSelector) =
      PrefixAmplitudeReferenceCaseSpec p
        (delimiterEncoding output) (delimiterEncoding input) rowSelector := by
  rw [qBeforeRowUniformInverseState_finalSelector_of_canonical_preimage p input
    output rowSelector rowResult.columnSelector columnResult.negative preimageEq
    phaseEq]
  symm
  exact PrefixAmplitudeReferenceCaseSpec_of_accepted output input rowSelector
    rowResult columnResult rowAccepted columnAccepted rowSelectorEq outputEq inputEq

/-- actual回路の最終row selector一本に対応する振幅。 -/
def qActualSelectorAmplitude (p : QParameters)
    (output input : RegisterBasis p.systemWidth) (rowSelector : QSelector p) : ℂ :=
  qBeforeRowUniformInverseState p input
    (qFinalRowSelectorBasis p output rowSelector)

/--
illegal・拒否・不整合・受理の局所path定理が揃えば、全物理入出力と全row selectorについて
actual振幅と参照振幅の一致を、外側へcase仮定を残さず一度に合成できる。
-/
theorem qActualSelectorAmplitude_eq_expected_of_reference_cases
    (p : QParameters)
    (illegalOutput : ∀ output input rowSelector,
      decodeDelimiter output = none →
        qActualSelectorAmplitude p output input rowSelector = 0)
    (illegalInput : ∀ (output : QConfiguration p) input rowSelector,
      decodeDelimiter input = none →
        qActualSelectorAmplitude p (delimiterEncoding output) input rowSelector = 0)
    (rowRejected : ∀ (output input : QConfiguration p) rowSelector,
      rowReference output rowSelector = none →
        qActualSelectorAmplitude p (delimiterEncoding output)
          (delimiterEncoding input) rowSelector = 0)
    (columnRejected : ∀ (output input : QConfiguration p) rowSelector rowResult,
      rowReference output rowSelector = some rowResult →
      columnReference input rowResult.columnSelector = none →
        qActualSelectorAmplitude p (delimiterEncoding output)
          (delimiterEncoding input) rowSelector = 0)
    (inconsistent : ∀ (output input : QConfiguration p) rowSelector rowResult
        columnResult,
      rowReference output rowSelector = some rowResult →
      columnReference input rowResult.columnSelector = some columnResult →
      ¬(columnResult.rowSelector = rowSelector ∧
        columnResult.output = output ∧ rowResult.input = input) →
        qActualSelectorAmplitude p (delimiterEncoding output)
          (delimiterEncoding input) rowSelector = 0)
    (accepted : ∀ (output input : QConfiguration p) rowSelector rowResult
        columnResult,
      rowReference output rowSelector = some rowResult →
      columnReference input rowResult.columnSelector = some columnResult →
      columnResult.rowSelector = rowSelector →
      columnResult.output = output → rowResult.input = input →
        qActualSelectorAmplitude p (delimiterEncoding output)
          (delimiterEncoding input) rowSelector =
        ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
          (if columnResult.negative then -1 else 1)) :
    ∀ output input rowSelector,
      qActualSelectorAmplitude p output input rowSelector =
        PrefixAmplitudeReferenceCaseSpec p output input rowSelector := by
  intro output input rowSelector
  cases outputDecoded : decodeDelimiter output with
  | none =>
      rw [illegalOutput output input rowSelector outputDecoded]
      simp [PrefixAmplitudeReferenceCaseSpec, outputDecoded]
  | some outputConfiguration =>
      have outputEncoding : delimiterEncoding outputConfiguration = output :=
        decodeDelimiter_eq_some_iff.mp outputDecoded
      subst output
      cases inputDecoded : decodeDelimiter input with
      | none =>
          rw [illegalInput outputConfiguration input rowSelector inputDecoded]
          simp [PrefixAmplitudeReferenceCaseSpec, inputDecoded]
      | some inputConfiguration =>
          have inputEncoding : delimiterEncoding inputConfiguration = input :=
            decodeDelimiter_eq_some_iff.mp inputDecoded
          subst input
          cases rowAccepted : rowReference outputConfiguration rowSelector with
          | none =>
              rw [rowRejected outputConfiguration inputConfiguration rowSelector
                rowAccepted]
              simp [PrefixAmplitudeReferenceCaseSpec,
                reverseReferenceAcceptedRowSelectorWeight, rowAccepted]
          | some rowResult =>
              cases columnAccepted :
                  columnReference inputConfiguration rowResult.columnSelector with
              | none =>
                  rw [columnRejected outputConfiguration inputConfiguration
                    rowSelector rowResult rowAccepted columnAccepted]
                  simp [PrefixAmplitudeReferenceCaseSpec,
                    reverseReferenceAcceptedRowSelectorWeight, rowAccepted,
                    columnAccepted]
              | some columnResult =>
                  by_cases lands : columnResult.rowSelector = rowSelector ∧
                      columnResult.output = outputConfiguration ∧
                        rowResult.input = inputConfiguration
                  · rcases lands with ⟨rowSelectorEq, outputEq, inputEq⟩
                    rw [accepted outputConfiguration inputConfiguration rowSelector
                      rowResult columnResult rowAccepted columnAccepted rowSelectorEq
                      outputEq inputEq]
                    symm
                    exact PrefixAmplitudeReferenceCaseSpec_of_accepted
                      outputConfiguration inputConfiguration rowSelector rowResult
                      columnResult rowAccepted columnAccepted rowSelectorEq outputEq
                      inputEq
                  · rw [inconsistent outputConfiguration inputConfiguration
                      rowSelector rowResult columnResult rowAccepted columnAccepted
                      lands]
                    simp [PrefixAmplitudeReferenceCaseSpec,
                      reverseReferenceAcceptedRowSelectorWeight, rowAccepted,
                      columnAccepted, lands]

/-- 全selectorのactual振幅定理から、最終の無仮定block-encoding定理を得る。 -/
theorem uqCircuit_correct_of_actual_selector_amplitudes
    (p : QParameters)
    (selectorValues : ∀ output input rowSelector,
      qActualSelectorAmplitude p output input rowSelector =
        PrefixAmplitudeReferenceCaseSpec p output input rowSelector) :
    IsApproxQubitBlockEncoding
      (allZeroAncilla p.ancillaWidth)
      ((uqCircuit p).toIdealOperator primitiveGateOperator)
      (embeddedProbabilityGenerator p)
      (3 * p.K)
      0 := by
  apply uqCircuit_correct_of_reverse_selector_values p
  intro output input rowSelector
  exact selectorValues output input rowSelector

end

end ProbabilityGeneratorQProof
