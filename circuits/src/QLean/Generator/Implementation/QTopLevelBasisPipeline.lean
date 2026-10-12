import QLean.Generator.Implementation.QSelectorBasisFiniteSumBridge
import QLean.Generator.Implementation.QOracleEndToEnd
import QLean.Generator.Implementation.ReversibleLogicSharedCoreReadoutAdapter
import Mathlib.Tactic

/-!
# Q最上位回路の厳密な基底作用

column一様準備、COPY、振幅判別、整列、終端Xについて、巨大行列を展開せずに
計算基底と型安全なwire読出しだけで利用できる仕様をまとめる。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

open ReversibleCircuit

/-- 任意の自然数selector値をcolumn selectorへ埋め込んだ初期基底。 -/
def qColumnInitialBasisOfNat (p : QParameters)
    (system : RegisterBasis p.systemWidth) (value : Nat) :
    JointBasis p.ancillaWidth p.systemWidth :=
  selectorBasisOver p (columnSelectorWire p)
    (zeroAncillaJointBasis p system)
    (selectorBasisOfNat p.selectorWidth value)

/-- 合法delimiter入力と有効selectorから作るcanonical column初期基底。 -/
def qCanonicalColumnInitialBasis (p : QParameters)
    (input : QConfiguration p) (selector : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth :=
  qColumnInitialBasisOfNat p (delimiterEncoding input) selector.val

/-- canonical column初期基底のcolumn selector読出しは指定selectorのbit表現である。 -/
@[simp] theorem projectColumnSelector_qCanonicalColumnInitialBasis
    (p : QParameters) (input : QConfiguration p) (selector : QSelector p) :
    projectSelectorBasis p (columnSelectorWire p)
        (qCanonicalColumnInitialBasis p input selector) =
      selectorBasisOfNat p.selectorWidth selector.val := by
  exact projectSelectorBasis_selectorBasisOver p (columnSelectorWire p)
    (sharedColumnSelectorWire_injective p) _ _

/-- canonical column初期基底はselector外で全0ancilla付きdelimiter背景を保存する。 -/
theorem qCanonicalColumnInitialBasis_outsideMatches
    (p : QParameters) (input : QConfiguration p) (selector : QSelector p) :
    OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p (delimiterEncoding input))
      (qCanonicalColumnInitialBasis p input selector) :=
  selectorBasisOver_outsideMatches p (columnSelectorWire p) _ _

/-- column一様準備状態は有効なcanonical selector基底上で厳密に`1 / sqrt(6K)`である。 -/
theorem qColumnPreparedState_qCanonicalColumnInitialBasis
    (p : QParameters) (input : QConfiguration p) (selector : QSelector p) :
    qColumnPreparedState p (delimiterEncoding input)
        (qCanonicalColumnInitialBasis p input selector) =
      ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) := by
  unfold qColumnPreparedState liftSelectorStateOver
  rw [if_pos (qCanonicalColumnInitialBasis_outsideMatches p input selector)]
  rw [projectColumnSelector_qCanonicalColumnInitialBasis]
  change (if selectorValue p.selectorWidth
      (selectorBasisOfNat p.selectorWidth selector.val) < p.selectorCount then
        ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) else 0) = _
  rw [selectorValue_selectorBasisOfNat p.selectorWidth selector.val
    (qSelector_lt_capacity p selector)]
  simp [selector.isLt]

/-- selector外で背景と一致しない基底ではcolumn一様準備振幅は0である。 -/
theorem qColumnPreparedState_eq_zero_of_outside_mismatch
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (mismatch : ¬OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p system) basis) :
    qColumnPreparedState p system basis = 0 := by
  simp [qColumnPreparedState, liftSelectorStateOver, mismatch]

/-- 容量内だが`selectorCount`以上のpadding値を持つcanonical背景基底の振幅は0である。 -/
theorem qColumnPreparedState_eq_zero_of_padding
    (p : QParameters) (system : RegisterBasis p.systemWidth) (value : Nat)
    (inCapacity : value < 2 ^ p.selectorWidth)
    (padding : p.selectorCount ≤ value) :
    qColumnPreparedState p system (qColumnInitialBasisOfNat p system value) = 0 := by
  unfold qColumnPreparedState liftSelectorStateOver qColumnInitialBasisOfNat
  rw [if_pos (selectorBasisOver_outsideMatches p (columnSelectorWire p)
    (zeroAncillaJointBasis p system) (selectorBasisOfNat p.selectorWidth value))]
  rw [projectSelectorBasis_selectorBasisOver p (columnSelectorWire p)
    (sharedColumnSelectorWire_injective p)]
  change (if selectorValue p.selectorWidth
      (selectorBasisOfNat p.selectorWidth value) < p.selectorCount then
        ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) else 0) = 0
  rw [selectorValue_selectorBasisOfNat p.selectorWidth value inCapacity]
  simp [Nat.not_lt_of_ge padding]

/-- 任意基底のcolumn selector復号値がpadding域なら、column一様準備振幅は0である。 -/
theorem qColumnPreparedState_eq_zero_of_projected_padding
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (basis : JointBasis p.ancillaWidth p.systemWidth)
    (padding : p.selectorCount ≤ selectorValue p.selectorWidth
      (projectSelectorBasis p (columnSelectorWire p) basis)) :
    qColumnPreparedState p system basis = 0 := by
  unfold qColumnPreparedState liftSelectorStateOver
  by_cases outside : OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p system) basis
  · rw [if_pos outside]
    change (if selectorValue p.selectorWidth
        (projectSelectorBasis p (columnSelectorWire p) basis) < p.selectorCount then
          ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) else 0) = 0
    rw [if_neg (Nat.not_lt_of_ge padding)]
  · simp [outside]

/-- 最終基底から得たcolumn逆像がselector外不一致なら、そのpath振幅は0である。 -/
theorem qColumnPreparedState_preimage_eq_zero_of_outside_mismatch
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (output : JointBasis p.ancillaWidth p.systemWidth)
    (mismatch : ¬OutsideSelectorMatches p (columnSelectorWire p)
      (zeroAncillaJointBasis p system) (qColumnPreparedPreimage p output)) :
    qColumnPreparedState p system (qColumnPreparedPreimage p output) = 0 :=
  qColumnPreparedState_eq_zero_of_outside_mismatch p system _ mismatch

/-- 最終基底から得たcolumn逆像のselector値がpadding域なら、そのpath振幅は0である。 -/
theorem qColumnPreparedState_preimage_eq_zero_of_padding
    (p : QParameters) (system : RegisterBasis p.systemWidth)
    (output : JointBasis p.ancillaWidth p.systemWidth)
    (padding : p.selectorCount ≤ selectorValue p.selectorWidth
      (projectSelectorBasis p (columnSelectorWire p)
        (qColumnPreparedPreimage p output))) :
    qColumnPreparedState p system (qColumnPreparedPreimage p output) = 0 :=
  qColumnPreparedState_eq_zero_of_projected_padding p system _ padding

/-- canonical column初期基底ではCOPY前のcolumn keyは全0である。 -/
theorem readColumnKey_qCanonicalColumnInitialBasis_eq_zero
    (p : QParameters) (input : QConfiguration p) (selector : QSelector p) :
    readWires (topColumnKeyWires p)
        (qCanonicalColumnInitialBasis p input selector) =
      List.replicate p.systemWidth false := by
  rw [← columnKeyWires_eq_topColumnKeyWires]
  unfold readWires
  rw [show List.replicate p.systemWidth false =
      (columnKeyWires p).map (fun _ => false) by
    simp [columnKeyWires]]
  apply List.map_congr_left
  intro wire member
  unfold qCanonicalColumnInitialBasis qColumnInitialBasisOfNat
  rw [selectorBasisOver_apply_outside]
  · rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    exact zeroAncillaJointBasis_ancilla p (delimiterEncoding input) _
  · exact List.disjoint_left.mp
      (columnSelectorSlice_disjoint_columnKeyWires p).symm member

/-- canonical初期基底へのCOPY後、column key読出しはCOPY前のsystem読出しに一致する。 -/
theorem copy_qCanonicalColumnInitialBasis_readColumnKey_eq_system
    (p : QParameters) (input : QConfiguration p) (selector : QSelector p) :
    readWires (topColumnKeyWires p)
        ((xorSystemIntoColumnKeyReversibleCircuit p).runBasis
          reversibleGatePermutation
          (qCanonicalColumnInitialBasis p input selector)) =
      readWires (topSystemWires p)
        (qCanonicalColumnInitialBasis p input selector) := by
  exact xorSystemIntoColumnKey_runBasis_key p _
    (readColumnKey_qCanonicalColumnInitialBasis_eq_zero p input selector)

/-- COPYはcolumn key標的列の外にある任意wireを保存する。 -/
theorem xorSystemIntoColumnKey_runBasis_outside
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ topColumnKeyWires p) :
    (xorSystemIntoColumnKeyReversibleCircuit p).runBasis
        reversibleGatePermutation input wire = input wire := by
  unfold xorSystemIntoColumnKeyReversibleCircuit
  exact runBasis_validatedXorCopyLists_outside
    (topSystemWires p) (topColumnKeyWires p) input
    (topSystemWires_nodup p) (topColumnKeyWires_nodup p) (by simp)
    (topSystemWires_disjoint_topColumnKeyWires p) wire outside

/-- COPYはcolumn key標的列と互いに素な任意registerの読出しを保存する。 -/
theorem xorSystemIntoColumnKey_runBasis_readWires_outside
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (wires : List (Wire p.ancillaWidth p.systemWidth))
    (disjoint : wires.Disjoint (topColumnKeyWires p)) :
    readWires wires
        ((xorSystemIntoColumnKeyReversibleCircuit p).runBasis
          reversibleGatePermutation input) =
      readWires wires input := by
  apply List.map_congr_left
  intro wire member
  exact xorSystemIntoColumnKey_runBasis_outside p input wire
    (List.disjoint_left.mp disjoint member)

/-- COPYはsourceであるsystem registerの読出しを保存する。 -/
theorem xorSystemIntoColumnKey_runBasis_readSystem
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (topSystemWires p)
        ((xorSystemIntoColumnKeyReversibleCircuit p).runBasis
          reversibleGatePermutation input) =
      readWires (topSystemWires p) input :=
  xorSystemIntoColumnKey_runBasis_readWires_outside p input (topSystemWires p)
    (topSystemWires_disjoint_topColumnKeyWires p)

/-- 振幅判別CNOTの出力基底を、入力基底から明示的に構成する。 -/
def qDiscriminatorOutputBasis (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  cnotBasisAction (activeWire p) (amplitudeSignalWire p) input

/-- 振幅判別の出力基底をCNOTで逆に追うと、厳密に元の入力基底へ戻る。 -/
@[simp] theorem qDiscriminatorOutputBasis_preimage (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    cnotBasisAction (activeWire p) (amplitudeSignalWire p)
      (qDiscriminatorOutputBasis p input) = input := by
  exact cnotBasisAction_involutive (activeWire p) (amplitudeSignalWire p)
    (activeWire_ne_amplitudeSignalWire p) input

/-- amplitude入力が0なら、振幅判別出力のamplitude signalはactive bitに一致する。 -/
theorem qDiscriminatorOutputBasis_amplitude_of_zero
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (amplitudeZero : input (amplitudeSignalWire p) = false) :
    qDiscriminatorOutputBasis p input (amplitudeSignalWire p) =
      input (activeWire p) := by
  unfold qDiscriminatorOutputBasis
  rw [cnotBasisAction_target]
  cases active : input (activeWire p) <;> simp [amplitudeZero]

/-- 振幅判別はnegative wireを変更しない。 -/
theorem qDiscriminatorOutputBasis_negative (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    qDiscriminatorOutputBasis p input (negativeWire p) = input (negativeWire p) := by
  unfold qDiscriminatorOutputBasis
  exact cnotBasisAction_other (activeWire p) (amplitudeSignalWire p)
    (negativeWire p) (negativeWire_ne_amplitudeSignalWire p) input

/-- amplitude入力が0なら、振幅判別位相は`negative ∧ active`に応じた符号である。 -/
theorem qDiscriminatorOutputBasis_phase_of_zero
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (amplitudeZero : input (amplitudeSignalWire p) = false) :
    (if qDiscriminatorOutputBasis p input (negativeWire p) &&
        qDiscriminatorOutputBasis p input (amplitudeSignalWire p)
      then (-1 : ℂ) else 1) =
      if input (negativeWire p) && input (activeWire p) then -1 else 1 := by
  rw [qDiscriminatorOutputBasis_negative,
    qDiscriminatorOutputBasis_amplitude_of_zero p input amplitudeZero]

/-- amplitude入力が0なら、実際の振幅判別回路は明示出力基底へ`negative ∧ active`の符号を与える。 -/
theorem copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_qDiscriminatorOutputBasis
    (p : QParameters) (input : JointBasis p.ancillaWidth p.systemWidth)
    (amplitudeZero : input (amplitudeSignalWire p) = false) :
    (copyActiveIntoAmplitudeAndPhaseByNegativeCircuit p).toIdealOperator primitiveGateOperator
        (qDiscriminatorOutputBasis p input) input =
      if input (negativeWire p) && input (activeWire p) then -1 else 1 := by
  rw [copyActiveIntoAmplitudeAndPhaseByNegativeCircuit_apply_sparse]
  simp only [qDiscriminatorOutputBasis, if_true]
  rw [cnotBasisAction_target]
  cases active : input (activeWire p) <;> simp [amplitudeZero]

/-- column keyからsystemへの整列回路は、対応register間のcontrolled XOR copyである。 -/
theorem alignColumnKeyIntoSystem_eq_controlledXorCopy (p : QParameters) :
    controlledXorColumnKeyIntoSystemReversibleCircuit p =
      controlledXorCopy (amplitudeSignalWire p)
        (columnKeyWires p) (systemWires p) := by
  let indices := List.finRange p.systemWidth
  change Circuit.fromList (indices.map fun index =>
      ReversibleGate.toffoli (amplitudeSignalWire p) (columnKeyWire p index)
        (.system index) _ _ _) =
    controlledXorCopy (amplitudeSignalWire p)
      (indices.map (columnKeyWire p)) (indices.map Wire.system)
  induction indices with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      have amplitudeNeSystem : amplitudeSignalWire p ≠ (.system index) := by
        intro equal
        cases equal
      have keyNeSystem : columnKeyWire p index ≠ (.system index) := by
        intro equal
        cases equal
      simp [Circuit.fromList, VerifiedCircuitCore.Circuit.fromList,
        controlledXorCopy, Circuit.sequence,
        ReversibleCircuit.safeToffoli,
        amplitudeSignalWire_ne_columnKeyWire p index,
        amplitudeNeSystem, keyNeSystem,
        inductionHypothesis]

/-- row outputからsystemへの整列回路は、対応register間のcontrolled XOR copyである。 -/
theorem alignRowOutputIntoSystem_eq_controlledXorCopy (p : QParameters) :
    controlledXorRowOutputIntoSystemReversibleCircuit p =
      controlledXorCopy (amplitudeSignalWire p)
        (rowOutputWires p) (systemWires p) := by
  let indices := List.finRange p.systemWidth
  change Circuit.fromList (indices.map fun index =>
      ReversibleGate.toffoli (amplitudeSignalWire p) (rowOutputWire p index)
        (.system index) _ _ _) =
    controlledXorCopy (amplitudeSignalWire p)
      (indices.map (rowOutputWire p)) (indices.map Wire.system)
  induction indices with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      have amplitudeNeSystem : amplitudeSignalWire p ≠ (.system index) := by
        intro equal
        cases equal
      have outputNeSystem : rowOutputWire p index ≠ (.system index) := by
        intro equal
        cases equal
      simp [Circuit.fromList, VerifiedCircuitCore.Circuit.fromList,
        controlledXorCopy, Circuit.sequence,
        ReversibleCircuit.safeToffoli,
        amplitudeSignalWire_ne_rowOutputWire p index,
        amplitudeNeSystem, outputNeSystem,
        inductionHypothesis]

/-- selector outputからrow selectorへの整列回路は、対応register間のcontrolled XOR copyである。 -/
theorem alignSelectorOutputIntoRow_eq_controlledXorCopy (p : QParameters) :
    controlledXorSelectorOutputIntoRowSelectorReversibleCircuit p =
      controlledXorCopy (amplitudeSignalWire p)
        (selectorOutputWires p) (rowSelectorWires p) := by
  let indices := List.finRange p.selectorWidth
  change Circuit.fromList (indices.map fun index =>
      ReversibleGate.toffoli (amplitudeSignalWire p) (selectorOutputWire p index)
        (rowSelectorWire p index) _ _ _) =
    controlledXorCopy (amplitudeSignalWire p)
      (indices.map (selectorOutputWire p)) (indices.map (rowSelectorWire p))
  induction indices with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      simp [Circuit.fromList, VerifiedCircuitCore.Circuit.fromList,
        controlledXorCopy, Circuit.sequence,
        ReversibleCircuit.safeToffoli,
        amplitudeSignalWire_ne_selectorOutputWire p index,
        amplitudeSignalWire_ne_rowSelectorWire p index,
        selectorOutputWire_ne_rowSelectorWire p index,
        inductionHypothesis]

/-- 二つの同長bit列を、第一引数をsource、第二引数をtargetとするbitwise XORで合成する。 -/
def xorRegisterBits (source target : List Bool) : List Bool :=
  List.zipWith (fun sourceBit targetBit =>
    if sourceBit then !targetBit else targetBit) source target

/-- system wire列には重複がない。 -/
theorem qTopSystemWires_nodup (p : QParameters) : (systemWires p).Nodup := by
  unfold systemWires
  exact List.Nodup.map (by
    intro left right equal
    exact Wire.system.inj equal) (List.nodup_finRange _)

/-- row selector wire列には重複がない。 -/
theorem qTopRowSelectorWires_nodup (p : QParameters) :
    (rowSelectorWires p).Nodup := by
  unfold rowSelectorWires
  exact List.Nodup.map (sharedRowSelectorWire_injective p) (List.nodup_finRange _)

/-- row output wire列には重複がない。 -/
theorem qTopRowOutputWires_nodup (p : QParameters) :
    (rowOutputWires p).Nodup := by
  let slice := (QLayout.canonical p).rowOutput
  simpa [rowOutputWires, rowOutputWire, slice, RegisterSlice.wireList] using
    (slice.wireList_nodup :
      (slice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Nodup)

/-- selector output wire列には重複がない。 -/
theorem qTopSelectorOutputWires_nodup (p : QParameters) :
    (selectorOutputWires p).Nodup := by
  let slice := (QLayout.canonical p).selectorOutput
  simpa [selectorOutputWires, selectorOutputWire, slice,
    RegisterSlice.wireList] using
    (slice.wireList_nodup :
      (slice.wireList : List (Wire p.ancillaWidth p.systemWidth)).Nodup)

/-- column keyとsystemは異なる種類のwireからなり互いに素である。 -/
theorem qTopColumnKeyWires_disjoint_systemWires (p : QParameters) :
    (columnKeyWires p).Disjoint (systemWires p) := by
  rw [List.disjoint_left]
  intro wire keyMember systemMember
  rcases List.mem_map.mp keyMember with ⟨keyIndex, _, rfl⟩
  rcases List.mem_map.mp systemMember with ⟨systemIndex, _, equal⟩
  cases equal

/-- row outputとsystemは異なる種類のwireからなり互いに素である。 -/
theorem qTopRowOutputWires_disjoint_systemWires (p : QParameters) :
    (rowOutputWires p).Disjoint (systemWires p) := by
  rw [List.disjoint_left]
  intro wire outputMember systemMember
  rcases List.mem_map.mp outputMember with ⟨outputIndex, _, rfl⟩
  rcases List.mem_map.mp systemMember with ⟨systemIndex, _, equal⟩
  cases equal

/-- selector outputとrow selectorは配置上分離されたsliceなので互いに素である。 -/
theorem qTopSelectorOutputWires_disjoint_rowSelectorWires (p : QParameters) :
    (selectorOutputWires p).Disjoint (rowSelectorWires p) := by
  rw [List.disjoint_left]
  intro wire outputMember rowMember
  rcases List.mem_map.mp outputMember with ⟨outputIndex, _, rfl⟩
  rcases List.mem_map.mp rowMember with ⟨rowIndex, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [selectorOutputWire, rowSelectorWire, QLayout.canonical] at numbers
  omega

/-- amplitude signalはcolumn key wire列に含まれない。 -/
theorem amplitudeSignalWire_not_mem_columnKeyWires (p : QParameters) :
    amplitudeSignalWire p ∉ columnKeyWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  exact amplitudeSignalWire_ne_columnKeyWire p index equal.symm

/-- amplitude signalはrow output wire列に含まれない。 -/
theorem amplitudeSignalWire_not_mem_rowOutputWires (p : QParameters) :
    amplitudeSignalWire p ∉ rowOutputWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  exact amplitudeSignalWire_ne_rowOutputWire p index equal.symm

/-- amplitude signalはselector output wire列に含まれない。 -/
theorem amplitudeSignalWire_not_mem_selectorOutputWires (p : QParameters) :
    amplitudeSignalWire p ∉ selectorOutputWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  exact amplitudeSignalWire_ne_selectorOutputWire p index equal.symm

/-- amplitude signalはsystem wire列に含まれない。 -/
theorem amplitudeSignalWire_not_mem_systemWires (p : QParameters) :
    amplitudeSignalWire p ∉ systemWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  cases equal

/-- amplitude signalはrow selector wire列に含まれない。 -/
theorem amplitudeSignalWire_not_mem_rowSelectorWires (p : QParameters) :
    amplitudeSignalWire p ∉ rowSelectorWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  exact amplitudeSignalWire_ne_rowSelectorWire p index equal.symm

/-- column key整列段のsystem読出しは、amplitude signalに応じた厳密なXORである。 -/
theorem alignColumnKeyIntoSystem_runBasis_readSystem (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (systemWires p)
        ((controlledXorColumnKeyIntoSystemReversibleCircuit p).runBasis
          reversibleGatePermutation input) =
      if input (amplitudeSignalWire p) then
        xorRegisterBits (readWires (columnKeyWires p) input)
          (readWires (systemWires p) input)
      else readWires (systemWires p) input := by
  rw [alignColumnKeyIntoSystem_eq_controlledXorCopy]
  simpa [xorRegisterBits] using
    readWires_validatedControlledXorCopyLists_target (amplitudeSignalWire p)
      (columnKeyWires p) (systemWires p) input
      (columnKeyWires_nodup p)
      (qTopSystemWires_nodup p)
      (by simp [columnKeyWires, systemWires])
      (qTopColumnKeyWires_disjoint_systemWires p)
      (amplitudeSignalWire_not_mem_columnKeyWires p)
      (amplitudeSignalWire_not_mem_systemWires p)

/-- row output整列段のsystem読出しは、amplitude signalに応じた厳密なXORである。 -/
theorem alignRowOutputIntoSystem_runBasis_readSystem (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (systemWires p)
        ((controlledXorRowOutputIntoSystemReversibleCircuit p).runBasis
          reversibleGatePermutation input) =
      if input (amplitudeSignalWire p) then
        xorRegisterBits (readWires (rowOutputWires p) input)
          (readWires (systemWires p) input)
      else readWires (systemWires p) input := by
  rw [alignRowOutputIntoSystem_eq_controlledXorCopy]
  simpa [xorRegisterBits] using
    readWires_validatedControlledXorCopyLists_target (amplitudeSignalWire p)
      (rowOutputWires p) (systemWires p) input
      (qTopRowOutputWires_nodup p)
      (qTopSystemWires_nodup p)
      (by simp [rowOutputWires, systemWires])
      (qTopRowOutputWires_disjoint_systemWires p)
      (amplitudeSignalWire_not_mem_rowOutputWires p)
      (amplitudeSignalWire_not_mem_systemWires p)

/-- selector整列段のrow selector読出しは、amplitude signalに応じた厳密なXORである。 -/
theorem alignSelectorOutputIntoRow_runBasis_readRowSelector (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (rowSelectorWires p)
        ((controlledXorSelectorOutputIntoRowSelectorReversibleCircuit p).runBasis
          reversibleGatePermutation input) =
      if input (amplitudeSignalWire p) then
        xorRegisterBits (readWires (selectorOutputWires p) input)
          (readWires (rowSelectorWires p) input)
      else readWires (rowSelectorWires p) input := by
  rw [alignSelectorOutputIntoRow_eq_controlledXorCopy]
  simpa [xorRegisterBits] using
    readWires_validatedControlledXorCopyLists_target (amplitudeSignalWire p)
      (selectorOutputWires p) (rowSelectorWires p) input
      (qTopSelectorOutputWires_nodup p)
      (qTopRowSelectorWires_nodup p)
      (by simp [selectorOutputWires, rowSelectorWires])
      (qTopSelectorOutputWires_disjoint_rowSelectorWires p)
      (amplitudeSignalWire_not_mem_selectorOutputWires p)
      (amplitudeSignalWire_not_mem_rowSelectorWires p)

/-- The validated column-key alignment preserves one wire outside system. -/
theorem alignColumnKeyIntoSystem_runBasis_outside (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth) (outside : wire ∉ systemWires p) :
    (controlledXorColumnKeyIntoSystemReversibleCircuit p).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [alignColumnKeyIntoSystem_eq_controlledXorCopy]
  exact runBasis_validatedControlledXorCopyLists_outside
    (amplitudeSignalWire p) (columnKeyWires p) (systemWires p) input
    (columnKeyWires_nodup p) (qTopSystemWires_nodup p)
    (by simp [columnKeyWires, systemWires])
    (qTopColumnKeyWires_disjoint_systemWires p)
    (amplitudeSignalWire_not_mem_columnKeyWires p)
    (amplitudeSignalWire_not_mem_systemWires p) wire outside

/-- The validated row-output alignment preserves one wire outside system. -/
theorem alignRowOutputIntoSystem_runBasis_outside (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth) (outside : wire ∉ systemWires p) :
    (controlledXorRowOutputIntoSystemReversibleCircuit p).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [alignRowOutputIntoSystem_eq_controlledXorCopy]
  exact runBasis_validatedControlledXorCopyLists_outside
    (amplitudeSignalWire p) (rowOutputWires p) (systemWires p) input
    (qTopRowOutputWires_nodup p) (qTopSystemWires_nodup p)
    (by simp [rowOutputWires, systemWires])
    (qTopRowOutputWires_disjoint_systemWires p)
    (amplitudeSignalWire_not_mem_rowOutputWires p)
    (amplitudeSignalWire_not_mem_systemWires p) wire outside

/-- The validated selector alignment preserves one wire outside row selector. -/
theorem alignSelectorOutputIntoRow_runBasis_outside (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (outside : wire ∉ rowSelectorWires p) :
    (controlledXorSelectorOutputIntoRowSelectorReversibleCircuit p).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [alignSelectorOutputIntoRow_eq_controlledXorCopy]
  exact runBasis_validatedControlledXorCopyLists_outside
    (amplitudeSignalWire p) (selectorOutputWires p) (rowSelectorWires p) input
    (qTopSelectorOutputWires_nodup p) (qTopRowSelectorWires_nodup p)
    (by simp [selectorOutputWires, rowSelectorWires])
    (qTopSelectorOutputWires_disjoint_rowSelectorWires p)
    (amplitudeSignalWire_not_mem_selectorOutputWires p)
    (amplitudeSignalWire_not_mem_rowSelectorWires p) wire outside

/-- The validated column-key alignment preserves a readout outside system. -/
theorem alignColumnKeyIntoSystem_runBasis_readOutside (p : QParameters)
    (wires : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (outside : wires.Disjoint (systemWires p)) :
    readWires wires
        ((controlledXorColumnKeyIntoSystemReversibleCircuit p).runBasis
          reversibleGatePermutation input) = readWires wires input := by
  rw [alignColumnKeyIntoSystem_eq_controlledXorCopy]
  exact readWires_validatedControlledXorCopyLists_outside
    (amplitudeSignalWire p) (columnKeyWires p) (systemWires p) wires input
    (columnKeyWires_nodup p) (qTopSystemWires_nodup p)
    (by simp [columnKeyWires, systemWires])
    (qTopColumnKeyWires_disjoint_systemWires p)
    (amplitudeSignalWire_not_mem_columnKeyWires p)
    (amplitudeSignalWire_not_mem_systemWires p) outside

/-- The validated row-output alignment preserves a readout outside system. -/
theorem alignRowOutputIntoSystem_runBasis_readOutside (p : QParameters)
    (wires : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (outside : wires.Disjoint (systemWires p)) :
    readWires wires
        ((controlledXorRowOutputIntoSystemReversibleCircuit p).runBasis
          reversibleGatePermutation input) = readWires wires input := by
  rw [alignRowOutputIntoSystem_eq_controlledXorCopy]
  exact readWires_validatedControlledXorCopyLists_outside
    (amplitudeSignalWire p) (rowOutputWires p) (systemWires p) wires input
    (qTopRowOutputWires_nodup p) (qTopSystemWires_nodup p)
    (by simp [rowOutputWires, systemWires])
    (qTopRowOutputWires_disjoint_systemWires p)
    (amplitudeSignalWire_not_mem_rowOutputWires p)
    (amplitudeSignalWire_not_mem_systemWires p) outside

/-- The validated selector alignment preserves a readout outside row selector. -/
theorem alignSelectorOutputIntoRow_runBasis_readOutside (p : QParameters)
    (wires : List (Wire p.ancillaWidth p.systemWidth))
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (outside : wires.Disjoint (rowSelectorWires p)) :
    readWires wires
        ((controlledXorSelectorOutputIntoRowSelectorReversibleCircuit p).runBasis
          reversibleGatePermutation input) = readWires wires input := by
  rw [alignSelectorOutputIntoRow_eq_controlledXorCopy]
  exact readWires_validatedControlledXorCopyLists_outside
    (amplitudeSignalWire p) (selectorOutputWires p) (rowSelectorWires p) wires input
    (qTopSelectorOutputWires_nodup p) (qTopRowSelectorWires_nodup p)
    (by simp [selectorOutputWires, rowSelectorWires])
    (qTopSelectorOutputWires_disjoint_rowSelectorWires p)
    (amplitudeSignalWire_not_mem_selectorOutputWires p)
    (amplitudeSignalWire_not_mem_rowSelectorWires p) outside

/-- systemとrow selectorは物理・アンシラwireに分離され互いに素である。 -/
theorem qTopSystemWires_disjoint_rowSelectorWires (p : QParameters) :
    (systemWires p).Disjoint (rowSelectorWires p) := by
  rw [List.disjoint_left]
  intro wire systemMember rowMember
  rcases List.mem_map.mp systemMember with ⟨systemIndex, _, rfl⟩
  rcases List.mem_map.mp rowMember with ⟨rowIndex, _, equal⟩
  cases equal

/-- selector outputとsystemはアンシラ・物理wireに分離され互いに素である。 -/
theorem qTopSelectorOutputWires_disjoint_systemWires (p : QParameters) :
    (selectorOutputWires p).Disjoint (systemWires p) := by
  rw [List.disjoint_left]
  intro wire outputMember systemMember
  rcases List.mem_map.mp outputMember with ⟨outputIndex, _, rfl⟩
  rcases List.mem_map.mp systemMember with ⟨systemIndex, _, equal⟩
  cases equal

/-- key signalはsystem wire列に含まれない。 -/
theorem keySignalWire_not_mem_systemWires (p : QParameters) :
    keySignalWire p ∉ systemWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  cases equal

/-- key signalはrow selector sliceに含まれない。 -/
theorem keySignalWire_not_mem_rowSelectorWires (p : QParameters) :
    keySignalWire p ∉ rowSelectorWires p := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  have numbers := congrArg wireNumber equal
  simp [keySignalWire, rowSelectorWire, QLayout.canonical] at numbers
  omega

/-- 整列回路のcolumn key段直後の基底。 -/
def qAlignAfterColumnBasis (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (controlledXorColumnKeyIntoSystemReversibleCircuit p).runBasis
    reversibleGatePermutation input

/-- 整列回路のrow output段直後の基底。 -/
def qAlignAfterRowBasis (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (controlledXorRowOutputIntoSystemReversibleCircuit p).runBasis
    reversibleGatePermutation (qAlignAfterColumnBasis p input)

/-- 整列回路のselector output段直後の基底。 -/
def qAlignAfterSelectorBasis (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    JointBasis p.ancillaWidth p.systemWidth :=
  (controlledXorSelectorOutputIntoRowSelectorReversibleCircuit p).runBasis
    reversibleGatePermutation (qAlignAfterRowBasis p input)

/-- 整列回路全体の`runBasis`は、三つのregister XORと終端key CNOTの明示合成である。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_eq (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input =
      cnotBasisAction (amplitudeSignalWire p) (keySignalWire p)
        (qAlignAfterSelectorBasis p input) := by
  rfl

/-- column key整列段はamplitude signalを保存する。 -/
theorem qAlignAfterColumnBasis_amplitudeSignal (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    qAlignAfterColumnBasis p input (amplitudeSignalWire p) =
      input (amplitudeSignalWire p) := by
  unfold qAlignAfterColumnBasis
  exact alignColumnKeyIntoSystem_runBasis_outside p input _
    (amplitudeSignalWire_not_mem_systemWires p)

/-- row output整列段までamplitude signalは保存される。 -/
theorem qAlignAfterRowBasis_amplitudeSignal (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    qAlignAfterRowBasis p input (amplitudeSignalWire p) =
      input (amplitudeSignalWire p) := by
  unfold qAlignAfterRowBasis
  rw [alignRowOutputIntoSystem_runBasis_outside p
    (qAlignAfterColumnBasis p input) _
    (amplitudeSignalWire_not_mem_systemWires p)]
  exact qAlignAfterColumnBasis_amplitudeSignal p input

/-- selector整列段までamplitude signalは保存される。 -/
theorem qAlignAfterSelectorBasis_amplitudeSignal (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    qAlignAfterSelectorBasis p input (amplitudeSignalWire p) =
      input (amplitudeSignalWire p) := by
  unfold qAlignAfterSelectorBasis
  rw [alignSelectorOutputIntoRow_runBasis_outside p
    (qAlignAfterRowBasis p input) _
    (amplitudeSignalWire_not_mem_rowSelectorWires p)]
  exact qAlignAfterRowBasis_amplitudeSignal p input

/-- column key整列段はrow outputの読出しを保存する。 -/
theorem qAlignAfterColumnBasis_readRowOutput (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (rowOutputWires p) (qAlignAfterColumnBasis p input) =
      readWires (rowOutputWires p) input := by
  unfold qAlignAfterColumnBasis
  exact alignColumnKeyIntoSystem_runBasis_readOutside p (rowOutputWires p) input
    (qTopRowOutputWires_disjoint_systemWires p)

/-- row整列段まではrow selector読出しが保存される。 -/
theorem qAlignAfterRowBasis_readRowSelector (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (rowSelectorWires p) (qAlignAfterRowBasis p input) =
      readWires (rowSelectorWires p) input := by
  unfold qAlignAfterRowBasis
  rw [alignRowOutputIntoSystem_runBasis_readOutside p (rowSelectorWires p)
    (qAlignAfterColumnBasis p input)
    (qTopSystemWires_disjoint_rowSelectorWires p).symm]
  unfold qAlignAfterColumnBasis
  exact alignColumnKeyIntoSystem_runBasis_readOutside p (rowSelectorWires p) input
    (qTopSystemWires_disjoint_rowSelectorWires p).symm

/-- row整列段まではselector output読出しが保存される。 -/
theorem qAlignAfterRowBasis_readSelectorOutput (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (selectorOutputWires p) (qAlignAfterRowBasis p input) =
      readWires (selectorOutputWires p) input := by
  unfold qAlignAfterRowBasis
  rw [alignRowOutputIntoSystem_runBasis_readOutside p (selectorOutputWires p)
    (qAlignAfterColumnBasis p input)
    (qTopSelectorOutputWires_disjoint_systemWires p)]
  unfold qAlignAfterColumnBasis
  exact alignColumnKeyIntoSystem_runBasis_readOutside p
    (selectorOutputWires p) input (qTopSelectorOutputWires_disjoint_systemWires p)

/-- 整列回路全体のsystem読出しはcolumn keyとrow outputを順にXORした値である。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readSystem (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (systemWires p)
        ((controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input) =
      if input (amplitudeSignalWire p) then
        xorRegisterBits (readWires (rowOutputWires p) input)
          (xorRegisterBits (readWires (columnKeyWires p) input)
            (readWires (systemWires p) input))
      else readWires (systemWires p) input := by
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_eq]
  rw [readWires_cnotBasisAction_of_not_mem (systemWires p)
    (amplitudeSignalWire p) (keySignalWire p) _
    (keySignalWire_not_mem_systemWires p)]
  unfold qAlignAfterSelectorBasis
  rw [alignSelectorOutputIntoRow_runBasis_readOutside p (systemWires p)
    (qAlignAfterRowBasis p input) (qTopSystemWires_disjoint_rowSelectorWires p)]
  · unfold qAlignAfterRowBasis
    rw [alignRowOutputIntoSystem_runBasis_readSystem]
    rw [qAlignAfterColumnBasis_amplitudeSignal,
      qAlignAfterColumnBasis_readRowOutput]
    unfold qAlignAfterColumnBasis
    rw [alignColumnKeyIntoSystem_runBasis_readSystem]
    cases enabled : input (amplitudeSignalWire p) <;> simp

/-- 整列回路全体のrow selector読出しはselector outputをXORした値である。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_readRowSelector (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    readWires (rowSelectorWires p)
        ((controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input) =
      if input (amplitudeSignalWire p) then
        xorRegisterBits (readWires (selectorOutputWires p) input)
          (readWires (rowSelectorWires p) input)
      else readWires (rowSelectorWires p) input := by
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_eq]
  rw [readWires_cnotBasisAction_of_not_mem (rowSelectorWires p)
    (amplitudeSignalWire p) (keySignalWire p) _
    (keySignalWire_not_mem_rowSelectorWires p)]
  unfold qAlignAfterSelectorBasis
  rw [alignSelectorOutputIntoRow_runBasis_readRowSelector]
  rw [qAlignAfterRowBasis_amplitudeSignal,
    qAlignAfterRowBasis_readSelectorOutput,
    qAlignAfterRowBasis_readRowSelector]

/-- 整列回路全体のkey signalはamplitude signalとのCNOTで厳密に更新される。 -/
theorem controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_keySignal (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit p).runBasis reversibleGatePermutation input
        (keySignalWire p) =
      if input (amplitudeSignalWire p) then !(input (keySignalWire p))
      else input (keySignalWire p) := by
  have keyPreserved : qAlignAfterSelectorBasis p input (keySignalWire p) =
      input (keySignalWire p) := by
    unfold qAlignAfterSelectorBasis qAlignAfterRowBasis qAlignAfterColumnBasis
    rw [alignSelectorOutputIntoRow_runBasis_outside p _ _
      (keySignalWire_not_mem_rowSelectorWires p)]
    rw [alignRowOutputIntoSystem_runBasis_outside p _ _
      (keySignalWire_not_mem_systemWires p)]
    exact alignColumnKeyIntoSystem_runBasis_outside p input _
      (keySignalWire_not_mem_systemWires p)
  rw [controlledXorOracleOutputsIntoAlignedRegistersReversibleCircuit_runBasis_eq, cnotBasisAction_target,
    qAlignAfterSelectorBasis_amplitudeSignal, keyPreserved]

/-- 終端Xの`runBasis`はamplitude signal一ビットの反転に厳密一致する。 -/
theorem flipAmplitudeSignal_runBasis (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (flipAmplitudeSignalReversibleCircuit p).runBasis
        reversibleGatePermutation input =
      xBasisAction (amplitudeSignalWire p) input := by
  rfl

/-- 終端X後のamplitude signalは入力bitの否定である。 -/
@[simp] theorem flipAmplitudeSignal_runBasis_amplitudeSignal (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth) :
    (flipAmplitudeSignalReversibleCircuit p).runBasis reversibleGatePermutation input
        (amplitudeSignalWire p) = !(input (amplitudeSignalWire p)) := by
  rw [flipAmplitudeSignal_runBasis]
  exact xBasisAction_target _ _

/-- 終端Xはamplitude signal以外の任意wireを保存する。 -/
theorem flipAmplitudeSignal_runBasis_other (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (different : wire ≠ amplitudeSignalWire p) :
    (flipAmplitudeSignalReversibleCircuit p).runBasis reversibleGatePermutation input wire =
      input wire := by
  rw [flipAmplitudeSignal_runBasis]
  exact xBasisAction_other _ _ different _

end

end ProbabilityGeneratorQProof
