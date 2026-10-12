import QLean.Generator.Analysis.ClassicalReversibleStageAdapter
import QLean.Generator.Analysis.OracleTotalPrograms
import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.ReversibleLogicClassicalStageAnalytic

/-!
# 共有 reversible logic 用の検証済み Q register 配置

任意長・wire衝突退避を含む旧total helperとは分離し、共有coreの正常layout契約を
満たす同幅・injective・disjointなQ registerだけを表す。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 所属付きQ wireからなる固定幅injective register。 -/
structure ValidatedQRegister (ancillaQubits systemQubits width : Nat) where
  /-- register内添字から所属付きwireへの写像。 -/
  wire : Fin width → Wire ancillaQubits systemQubits
  /-- register内wireは重複しない。 -/
  injective : Function.Injective wire

namespace ValidatedQRegister

/-- A duplicate-free Q wire list viewed as a typed register. -/
def ofList {ancillaQubits systemQubits : Nat}
    (wires : List (Wire ancillaQubits systemQubits))
    (nodup : wires.Nodup) :
    ValidatedQRegister ancillaQubits systemQubits wires.length where
  wire := wires.get
  injective := fun _ _ equal => nodup.get_inj_iff.mp equal

/-- 実行順のQ wire列。 -/
def wires {ancillaQubits systemQubits width : Nat}
    (register : ValidatedQRegister ancillaQubits systemQubits width) :
    List (Wire ancillaQubits systemQubits) :=
  (List.finRange width).map register.wire

/-- Enumerating the typed register made from a list recovers that list. -/
@[simp] theorem wires_ofList {ancillaQubits systemQubits : Nat}
    (values : List (Wire ancillaQubits systemQubits))
    (nodup : values.Nodup) :
    (ofList values nodup).wires = values := by
  simp [wires, ofList]

/-- A duplicate-free list transported to an explicitly chosen equal width. -/
def ofListWithLength {ancillaQubits systemQubits width : Nat}
    (values : List (Wire ancillaQubits systemQubits))
    (nodup : values.Nodup) (length_eq : values.length = width) :
    ValidatedQRegister ancillaQubits systemQubits width :=
  length_eq ▸ ofList values nodup

/-- Enumerating an explicitly width-transported register recovers its list. -/
@[simp] theorem wires_ofListWithLength
    {ancillaQubits systemQubits width : Nat}
    (values : List (Wire ancillaQubits systemQubits))
    (nodup : values.Nodup) (length_eq : values.length = width) :
    (ofListWithLength values nodup length_eq).wires = values := by
  cases length_eq
  exact wires_ofList values nodup

/-- 標準数値wireへ移した共有core register。 -/
def toCore {ancillaQubits systemQubits width : Nat}
    (register : ValidatedQRegister ancillaQubits systemQubits width) :
    VerifiedCircuitCore.Register (ancillaQubits + systemQubits) width where
  wire := fun index => analyticCanonicalWireEquiv ancillaQubits systemQubits
    (register.wire index)
  injective :=
    (analyticCanonicalWireEquiv ancillaQubits systemQubits).injective.comp
      register.injective

end ValidatedQRegister

/-- 同幅register XOR copyの正常Q layout。 -/
structure ValidatedRegisterXorCopyLayout
    (ancillaQubits systemQubits width : Nat) where
  source : ValidatedQRegister ancillaQubits systemQubits width
  target : ValidatedQRegister ancillaQubits systemQubits width
  disjoint : ∀ sourceIndex targetIndex,
    source.wire sourceIndex ≠ target.wire targetIndex

namespace ValidatedRegisterXorCopyLayout

/-- Raw duplicate-free equal-length lists packaged as a validated copy layout. -/
def ofLists {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target) :
    ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits source.length where
  source := ValidatedQRegister.ofList source sourceNodup
  target :=
    { wire := fun index => target.get (Fin.cast sameLength index)
      injective := fun first second equal => by
        have castEqual := targetNodup.get_inj_iff.mp equal
        simpa using castEqual }
  disjoint := fun sourceIndex targetIndex equal =>
    (List.disjoint_left.mp sourceTargetDisjoint
      (List.get_mem source sourceIndex))
      (by
        change source.get sourceIndex =
          target.get (Fin.cast sameLength targetIndex) at equal
        exact equal.symm ▸
          List.get_mem target (Fin.cast sameLength targetIndex))

/-- The source enumeration of `ofLists` is the original source list. -/
@[simp] theorem ofLists_source_wires
    {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target) :
    (ofLists source target sourceNodup targetNodup sameLength
      sourceTargetDisjoint).source.wires = source := by
  simp [ofLists]

/-- The target enumeration of `ofLists` is the original target list. -/
@[simp] theorem ofLists_target_wires
    {ancillaQubits systemQubits : Nat}
    (source target : List (Wire ancillaQubits systemQubits))
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target) :
    (ofLists source target sourceNodup targetNodup sameLength
      sourceTargetDisjoint).target.wires = target := by
  apply List.ext_get
  · simp [ValidatedQRegister.wires, sameLength]
  · intro index leftBound rightBound
    simp [ValidatedQRegister.wires, ofLists]

/-- 共有coreのregister XOR copy spec。 -/
def toCore {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width) :
    VerifiedCircuitCore.RegisterXorCopySpec
      (ancillaQubits + systemQubits) width where
  source := layout.source.toCore
  target := layout.target.toCore
  disjoint := fun sourceIndex targetIndex equal =>
    layout.disjoint sourceIndex targetIndex
      ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal)

/-- The Q-owned pure copy action is the shared basis action after reindexing. -/
def basisAction {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  (analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm
    (VerifiedCircuitCore.registerXorCopyBasisAction layout.toCore
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits input))

/-- Reindexing the Q copy action gives the shared pure basis action. -/
theorem basisAction_toCore {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    analyticJointBasisCoreEquiv ancillaQubits systemQubits
        (layout.basisAction input) =
      VerifiedCircuitCore.registerXorCopyBasisAction layout.toCore
        (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) := by
  simp [basisAction]

/-- The shared copy action commutes with X on a Q wire outside both registers. -/
theorem basisAction_commutes_xBasisAction_outside
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (wire : Wire ancillaQubits systemQubits)
    (input : JointBasis ancillaQubits systemQubits)
    (outsideSource : ∀ index, wire ≠ layout.source.wire index)
    (outsideTarget : ∀ index, wire ≠ layout.target.wire index) :
    layout.basisAction (xBasisAction wire input) =
      xBasisAction wire (layout.basisAction input) := by
  apply (analyticJointBasisCoreEquiv ancillaQubits systemQubits).injective
  rw [basisAction_toCore, analyticJointBasisCoreEquiv_xBasisAction,
    analyticJointBasisCoreEquiv_xBasisAction, basisAction_toCore]
  exact VerifiedCircuitCore.registerXorCopyBasisAction_commutes_xorWire_outside
    layout.toCore
    (analyticCanonicalWireEquiv ancillaQubits systemQubits wire) true
    (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)
    (fun index equal => outsideSource index
      ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))
    (fun index equal => outsideTarget index
      ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))

private theorem xorCopyStage_toCore_indices
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (indices : List (Fin width)) :
    (TotalReversibleStage.xorCopy
      (indices.map layout.source.wire)
      (indices.map layout.target.wire)).toCore =
      VerifiedCircuitCore.ClassicalReversibleStage.sequence
        (indices.map fun index =>
          .instruction (.xorControlled
            (layout.toCore.source.wire index)
            (layout.toCore.target.wire index)
            (layout.toCore.disjoint index index))) := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp only [List.map_cons, TotalReversibleStage.xorCopy,
        TotalReversibleStage.toCore,
        VerifiedCircuitCore.ClassicalReversibleStage.sequence]
      rw [inductionHypothesis]
      simp [TotalReversibleStage.safeXorControlled,
        VerifiedCircuitCore.ClassicalReversibleStage.safeXorControlled,
        ValidatedRegisterXorCopyLayout.toCore, ValidatedQRegister.toCore,
        layout.disjoint index index]

/-- The validated Q copy stage is exactly the shared typed copy stage. -/
theorem xorCopyStage_toCore
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width) :
    (TotalReversibleStage.xorCopy
      layout.source.wires layout.target.wires).toCore =
      VerifiedCircuitCore.ClassicalReversibleStage.registerXorCopyStage
        layout.toCore := by
  rw [ValidatedQRegister.wires, ValidatedQRegister.wires,
    VerifiedCircuitCore.ClassicalReversibleStage.registerXorCopyStage]
  exact xorCopyStage_toCore_indices layout (List.finRange width)

/-- The validated Q copy reference is the transported shared pure action. -/
theorem xorCopyStage_reference_eq_basisAction
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    (TotalReversibleStage.xorCopy
      layout.source.wires layout.target.wires).reference input =
      layout.basisAction input := by
  apply (analyticJointBasisCoreEquiv ancillaQubits systemQubits).injective
  rw [← TotalReversibleStage.toCore_reference_apply,
    layout.xorCopyStage_toCore,
    VerifiedCircuitCore.ClassicalReversibleStage.registerXorCopyStage_reference_apply,
    layout.basisAction_toCore]

/-- The validated copy preserves every source bit. -/
theorem basisAction_readSource {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) (index : Fin width) :
    layout.basisAction input (layout.source.wire index) =
      input (layout.source.wire index) := by
  have result := VerifiedCircuitCore.registerXorCopyBasisAction_readSource
    layout.toCore
    (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) index
  simpa [basisAction, analyticJointBasisCoreEquiv, toCore,
    ValidatedQRegister.toCore, analyticCanonicalWireEquiv] using result

/-- Each target bit is XORed with the corresponding source bit. -/
theorem basisAction_readTarget {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) (index : Fin width) :
    layout.basisAction input (layout.target.wire index) =
      (input (layout.target.wire index) !=
        input (layout.source.wire index)) := by
  have result := VerifiedCircuitCore.registerXorCopyBasisAction_readTarget
    layout.toCore
    (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) index
  simpa [basisAction, analyticJointBasisCoreEquiv, toCore,
    ValidatedQRegister.toCore, analyticCanonicalWireEquiv] using result

/-- Wires outside the target register are preserved pointwise. -/
theorem basisAction_applyOutside {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits)
    (outsideTarget : ∀ index, wire ≠ layout.target.wire index) :
    layout.basisAction input wire = input wire := by
  have result := VerifiedCircuitCore.registerXorCopyBasisAction_applyOutside
    layout.toCore
    (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)
    (analyticCanonicalWireEquiv ancillaQubits systemQubits wire)
    (fun index equal => outsideTarget index
      ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))
  simpa [basisAction, analyticJointBasisCoreEquiv, toCore,
    ValidatedQRegister.toCore, analyticCanonicalWireEquiv] using result

end ValidatedRegisterXorCopyLayout

/-- A validated equal-width controlled XOR-copy layout on Q-owned wires. -/
structure ValidatedControlledRegisterXorCopyLayout
    (ancillaQubits systemQubits width : Nat) where
  control : Wire ancillaQubits systemQubits
  source : ValidatedQRegister ancillaQubits systemQubits width
  target : ValidatedQRegister ancillaQubits systemQubits width
  sourceTargetDisjoint : ∀ sourceIndex targetIndex,
    source.wire sourceIndex ≠ target.wire targetIndex
  controlSourceDifferent : ∀ index, control ≠ source.wire index
  controlTargetDifferent : ∀ index, control ≠ target.wire index

namespace ValidatedControlledRegisterXorCopyLayout

/-- Forget the external control while retaining the validated copy registers. -/
def toRegisterXorCopyLayout
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width) :
    ValidatedRegisterXorCopyLayout ancillaQubits systemQubits width where
  source := layout.source
  target := layout.target
  disjoint := layout.sourceTargetDisjoint

/-- Raw duplicate-free lists packaged as a validated equal-width layout. -/
def ofLists {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target) :
    ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits source.length where
  control := control
  source := ValidatedQRegister.ofList source sourceNodup
  target :=
    { wire := fun index => target.get (Fin.cast sameLength index)
      injective := fun first second equal => by
        have castEqual := targetNodup.get_inj_iff.mp equal
        simpa using castEqual }
  sourceTargetDisjoint := fun sourceIndex targetIndex equal =>
    (List.disjoint_left.mp sourceTargetDisjoint
      (List.get_mem source sourceIndex))
      (by
        change source.get sourceIndex =
          target.get (Fin.cast sameLength targetIndex) at equal
        exact equal.symm ▸
          List.get_mem target (Fin.cast sameLength targetIndex))
  controlSourceDifferent := fun index equal =>
    controlAbsentSource (equal.symm ▸ List.get_mem source index)
  controlTargetDifferent := fun index equal =>
    controlAbsentTarget
      (equal.symm ▸ List.get_mem target (Fin.cast sameLength index))

/-- The control of `ofLists` is the supplied control wire. -/
@[simp] theorem ofLists_control
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target) :
    (ofLists control source target sourceNodup targetNodup sameLength
      sourceTargetDisjoint controlAbsentSource controlAbsentTarget).control =
        control := rfl

/-- The source enumeration of `ofLists` is the original source list. -/
@[simp] theorem ofLists_source_wires
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target) :
    (ofLists control source target sourceNodup targetNodup sameLength
      sourceTargetDisjoint controlAbsentSource controlAbsentTarget).source.wires =
        source := by
  simp [ofLists]

/-- The target enumeration of `ofLists` is the original target list. -/
@[simp] theorem ofLists_target_wires
    {ancillaQubits systemQubits : Nat}
    (control : Wire ancillaQubits systemQubits)
    (source target : List (Wire ancillaQubits systemQubits))
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sameLength : source.length = target.length)
    (sourceTargetDisjoint : source.Disjoint target)
    (controlAbsentSource : control ∉ source)
    (controlAbsentTarget : control ∉ target) :
    (ofLists control source target sourceNodup targetNodup sameLength
      sourceTargetDisjoint controlAbsentSource controlAbsentTarget).target.wires =
        target := by
  apply List.ext_get
  · simp [ValidatedQRegister.wires, sameLength]
  · intro index leftBound rightBound
    simp [ValidatedQRegister.wires, ofLists]

/-- The shared-core controlled XOR-copy specification for a validated Q layout. -/
def toCore {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width) :
    VerifiedCircuitCore.ControlledRegisterXorCopySpec
      (ancillaQubits + systemQubits) width where
  control := analyticCanonicalWireEquiv ancillaQubits systemQubits layout.control
  source := layout.source.toCore
  target := layout.target.toCore
  sourceTargetDisjoint := fun sourceIndex targetIndex equal =>
    layout.sourceTargetDisjoint sourceIndex targetIndex
      ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal)
  controlSourceDifferent := fun index equal =>
    layout.controlSourceDifferent index
      ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal)
  controlTargetDifferent := fun index equal =>
    layout.controlTargetDifferent index
      ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal)

/--
The Q-owned pure action is the basis reindex of the shared controlled-copy
action. It is independent of any compiler and records only wire placement.
-/
def basisAction {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  (analyticJointBasisCoreEquiv ancillaQubits systemQubits).symm
    (VerifiedCircuitCore.controlledRegisterXorCopyBasisAction layout.toCore
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits input))

/-- Reindexing the Q action gives exactly the shared pure basis action. -/
theorem basisAction_toCore {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    analyticJointBasisCoreEquiv ancillaQubits systemQubits
        (layout.basisAction input) =
      VerifiedCircuitCore.controlledRegisterXorCopyBasisAction layout.toCore
        (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) := by
  simp [basisAction]

/-- The controlled shared action is conditional application of the same copy layout. -/
theorem basisAction_eq_if
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    layout.basisAction input =
      if input layout.control then
        layout.toRegisterXorCopyLayout.basisAction input
      else input := by
  apply (analyticJointBasisCoreEquiv ancillaQubits systemQubits).injective
  rw [basisAction_toCore,
    VerifiedCircuitCore.controlledRegisterXorCopyBasisAction_eq_if]
  have controlValue :
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)
          layout.toCore.control = input layout.control := by
    simp [analyticJointBasisCoreEquiv, toCore, analyticCanonicalWireEquiv]
  rw [controlValue]
  rw [show layout.toCore.toRegisterXorCopySpec =
      layout.toRegisterXorCopyLayout.toCore by rfl]
  rw [← ValidatedRegisterXorCopyLayout.basisAction_toCore]
  cases input layout.control <;> rfl

/-- The validated Q controlled-copy stage is the shared typed stage after reindexing. -/
theorem controlledXorCopyStage_toCore
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width) :
    (OracleTotalProgram.controlledXorCopy layout.control
        layout.source.wires layout.target.wires).toCore =
      VerifiedCircuitCore.ClassicalReversibleStage.controlledRegisterXorCopyStage
        layout.toCore := by
  have zipped :
      layout.source.wires.zip layout.target.wires =
        (List.finRange width).map fun index =>
          (layout.source.wire index, layout.target.wire index) := by
    unfold ValidatedQRegister.wires
    induction List.finRange width with
    | nil => rfl
    | cons first rest inductionHypothesis =>
        simp [inductionHypothesis]
  rw [OracleTotalProgram.controlledXorCopy,
    TotalReversibleStage.toCore_sequence,
    VerifiedCircuitCore.ClassicalReversibleStage.controlledRegisterXorCopyStage,
    zipped, List.map_map]
  apply congrArg VerifiedCircuitCore.ClassicalReversibleStage.sequence
  rw [List.map_map]
  apply List.map_congr_left
  intro index _
  simp only [Function.comp_apply,
    TotalReversibleStage.safeXorDoublyControlled,
    TotalReversibleStage.toCore_ofCore]
  change VerifiedCircuitCore.ClassicalReversibleStage.safeXorDoublyControlled
      layout.toCore.control (layout.toCore.source.wire index)
        (layout.toCore.target.wire index) =
    .instruction (.xorDoublyControlled layout.toCore.control
      (layout.toCore.source.wire index) (layout.toCore.target.wire index)
      (layout.toCore.controlSourceDifferent index)
      (layout.toCore.controlTargetDifferent index)
      (layout.toCore.sourceTargetDisjoint index index))
  rw [VerifiedCircuitCore.ClassicalReversibleStage.safeXorDoublyControlled,
    dif_pos (layout.toCore.controlSourceDifferent index),
    dif_pos (layout.toCore.controlTargetDifferent index),
    dif_pos (layout.toCore.sourceTargetDisjoint index index)]

/-- The validated Q stage reference is the transported shared pure action. -/
theorem controlledXorCopyStage_reference_eq_basisAction
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    (OracleTotalProgram.controlledXorCopy layout.control
        layout.source.wires layout.target.wires).reference input =
      layout.basisAction input := by
  apply (analyticJointBasisCoreEquiv ancillaQubits systemQubits).injective
  rw [← TotalReversibleStage.toCore_reference_apply,
    layout.controlledXorCopyStage_toCore,
    VerifiedCircuitCore.ClassicalReversibleStage.controlledRegisterXorCopyStage_reference_apply,
    layout.basisAction_toCore]

/-- The validated controlled copy preserves its Q control wire. -/
theorem basisAction_readControl {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) :
    layout.basisAction input layout.control = input layout.control := by
  have result :=
    VerifiedCircuitCore.controlledRegisterXorCopyBasisAction_readControl
      layout.toCore
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)
  simpa [basisAction, analyticJointBasisCoreEquiv, toCore,
    ValidatedQRegister.toCore, analyticCanonicalWireEquiv] using result

/-- The validated controlled copy preserves every source bit. -/
theorem basisAction_readSource {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) (index : Fin width) :
    layout.basisAction input (layout.source.wire index) =
      input (layout.source.wire index) := by
  have result :=
    VerifiedCircuitCore.controlledRegisterXorCopyBasisAction_readSource
      layout.toCore
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) index
  simpa [basisAction, analyticJointBasisCoreEquiv, toCore,
    ValidatedQRegister.toCore, analyticCanonicalWireEquiv] using result

/-- Each target bit is XORed with the conjunction of control and source. -/
theorem basisAction_readTarget {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits) (index : Fin width) :
    layout.basisAction input (layout.target.wire index) =
      (input (layout.target.wire index) !=
        (input layout.control && input (layout.source.wire index))) := by
  have result :=
    VerifiedCircuitCore.controlledRegisterXorCopyBasisAction_readTarget
      layout.toCore
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits input) index
  simpa [basisAction, analyticJointBasisCoreEquiv, toCore,
    ValidatedQRegister.toCore, analyticCanonicalWireEquiv] using result

/-- Wires outside the target register are preserved pointwise. -/
theorem basisAction_applyOutside {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (input : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits)
    (outsideTarget : ∀ index, wire ≠ layout.target.wire index) :
    layout.basisAction input wire = input wire := by
  have result :=
    VerifiedCircuitCore.controlledRegisterXorCopyBasisAction_applyOutside
      layout.toCore
      (analyticJointBasisCoreEquiv ancillaQubits systemQubits input)
      (analyticCanonicalWireEquiv ancillaQubits systemQubits wire)
      (fun index equal =>
        outsideTarget index
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))
  simpa [basisAction, analyticJointBasisCoreEquiv, toCore,
    ValidatedQRegister.toCore, analyticCanonicalWireEquiv] using result

end ValidatedControlledRegisterXorCopyLayout

/-- 同幅register controlled swapの正常Q layout。 -/
structure ValidatedControlledRegisterSwapLayout
    (ancillaQubits systemQubits width : Nat) where
  control : Wire ancillaQubits systemQubits
  left : ValidatedQRegister ancillaQubits systemQubits width
  right : ValidatedQRegister ancillaQubits systemQubits width
  leftRightDisjoint : ∀ leftIndex rightIndex,
    left.wire leftIndex ≠ right.wire rightIndex
  controlLeftDifferent : ∀ index, control ≠ left.wire index
  controlRightDifferent : ∀ index, control ≠ right.wire index

namespace ValidatedControlledRegisterSwapLayout

/-- 共有coreのcontrolled register swap spec。 -/
def toCore {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width) :
    VerifiedCircuitCore.ControlledRegisterSwapSpec
      (ancillaQubits + systemQubits) width where
  control := analyticCanonicalWireEquiv ancillaQubits systemQubits layout.control
  left := layout.left.toCore
  right := layout.right.toCore
  leftRightDisjoint := fun leftIndex rightIndex equal =>
    layout.leftRightDisjoint leftIndex rightIndex
      ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal)
  controlLeftDifferent := fun index equal =>
    layout.controlLeftDifferent index
      ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal)
  controlRightDifferent := fun index equal =>
    layout.controlRightDifferent index
      ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal)

end ValidatedControlledRegisterSwapLayout

end

end ProbabilityGeneratorQProof
