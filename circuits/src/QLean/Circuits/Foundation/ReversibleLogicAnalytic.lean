import QLean.Circuits.Foundation.PrimitiveOperatorSemantics

/-!
# 可逆 register 論理の回路非依存な解析仕様

register XOR copy、制御付き copy、制御付き swap の wire layout と
厳密な基底置換作用素積を定義する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Toffoli の回路非依存な基底置換作用素。 -/
def analyticToffoliOperator {qubits : Nat}
    (control₀ control₁ target : Fin qubits) : Operator (QubitBasis qubits) :=
  deterministicOperator fun input =>
    xorWire target (input control₀ && input control₁) input

/-- CNOT の回路非依存な基底置換作用素。 -/
def reversibleAnalyticCnotOperator {qubits : Nat}
    (control target : Fin qubits) : Operator (QubitBasis qubits) :=
  deterministicOperator fun input => xorWire target (input control) input

/-- 同じ幅の source register を target register へ XOR copy する layout。 -/
structure RegisterXorCopySpec (qubits width : Nat) where
  /-- 読み取り専用 source register。 -/
  source : Register qubits width
  /-- XOR 更新する target register。 -/
  target : Register qubits width
  /-- 全 source wire と全 target wire は相異なる。 -/
  disjoint : ∀ sourceIndex targetIndex,
    source.wire sourceIndex ≠ target.wire targetIndex

/-- source bitを対応target bitへ順にXORする回路非依存な基底関数。 -/
def registerXorCopyBasisAction {qubits width : Nat}
    (spec : RegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  (List.finRange width).foldl
    (fun state index =>
      xorWire (spec.target.wire index) (state (spec.source.wire index)) state)
    input

/-- XOR更新foldは全targetと異なる任意wireの値を保存する。 -/
theorem foldl_xorWire_preserves
    {Index : Type*} {qubits : Nat}
    (indices : List Index) (target : Index → Fin qubits)
    (value : QubitBasis qubits → Index → Bool)
    (wire : Fin qubits)
    (different : ∀ index, index ∈ indices → target index ≠ wire)
    (input : QubitBasis qubits) :
    (indices.foldl
      (fun state index => xorWire (target index) (value state index) state)
      input) wire = input wire := by
  induction indices generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis (fun index membership =>
        different index (by simp [membership]))]
      have firstDifferent := different first (by simp)
      simp [xorWire, Ne.symm firstDifferent]

/-- injective target列を一度ずつXOR更新したときの指定target値。 -/
theorem foldl_registerXorCopy_readTarget
    {Index : Type*} {qubits : Nat}
    (indices : List Index) (source target : Index → Fin qubits)
    (sourceTargetDisjoint : ∀ sourceIndex targetIndex,
      source sourceIndex ≠ target targetIndex)
    (targetInjective : Function.Injective target)
    (chosen : Index) (chosenMembership : chosen ∈ indices)
    (indicesNodup : indices.Nodup) (input : QubitBasis qubits) :
    (indices.foldl
      (fun state index => xorWire (target index) (state (source index)) state)
      input) (target chosen) =
      (input (target chosen) != input (source chosen)) := by
  induction indices generalizing input with
  | nil => simp at chosenMembership
  | cons first rest inductionHypothesis =>
      have restNodup := indicesNodup.tail
      by_cases firstChosen : first = chosen
      · subst first
        have chosenNotInRest : chosen ∉ rest :=
          (List.nodup_cons.mp indicesNodup).1
        simp only [List.foldl_cons]
        rw [foldl_xorWire_preserves rest target
          (fun state index => state (source index)) (target chosen)
          (fun index membership equal => by
            have indexChosen := targetInjective equal
            subst index
            exact chosenNotInRest membership)]
        simp [xorWire]
      · have chosenInRest : chosen ∈ rest := by
          have cases : chosen = first ∨ chosen ∈ rest := by
            simpa only [List.mem_cons] using chosenMembership
          exact cases.resolve_left (Ne.symm firstChosen)
        simp only [List.foldl_cons]
        rw [inductionHypothesis chosenInRest restNodup]
        have targetDifferent : target first ≠ target chosen := by
          intro equal
          exact firstChosen (targetInjective equal)
        simp [xorWire, Ne.symm targetDifferent,
          sourceTargetDisjoint chosen first]

/-- register XOR copyはsource registerの各bitを保存する。 -/
theorem registerXorCopyBasisAction_readSource
    {qubits width : Nat} (spec : RegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) (index : Fin width) :
    registerXorCopyBasisAction spec input (spec.source.wire index) =
      input (spec.source.wire index) := by
  unfold registerXorCopyBasisAction
  exact foldl_xorWire_preserves (List.finRange width) spec.target.wire
    (fun state targetIndex => state (spec.source.wire targetIndex))
    (spec.source.wire index)
    (fun targetIndex _ => Ne.symm (spec.disjoint index targetIndex)) input

/-- register XOR copy後のtarget bitは元targetと対応sourceのXORである。 -/
theorem registerXorCopyBasisAction_readTarget
    {qubits width : Nat} (spec : RegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) (index : Fin width) :
    registerXorCopyBasisAction spec input (spec.target.wire index) =
      (input (spec.target.wire index) != input (spec.source.wire index)) := by
  unfold registerXorCopyBasisAction
  exact foldl_registerXorCopy_readTarget (List.finRange width)
    spec.source.wire spec.target.wire spec.disjoint spec.target.injective index
    (List.mem_finRange index) (List.nodup_finRange width) input

/-- register XOR copyはtarget外の指定wireを保存する。 -/
theorem registerXorCopyBasisAction_applyOutside
    {qubits width : Nat} (spec : RegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outsideTarget : ∀ index, wire ≠ spec.target.wire index) :
    registerXorCopyBasisAction spec input wire = input wire := by
  unfold registerXorCopyBasisAction
  exact foldl_xorWire_preserves (List.finRange width) spec.target.wire
    (fun state targetIndex => state (spec.source.wire targetIndex)) wire
    (fun index _ => Ne.symm (outsideTarget index)) input

/-- XOR copy commutes with toggling a wire outside both registers. -/
theorem registerXorCopyBasisAction_commutes_xorWire_outside
    {qubits width : Nat} (spec : RegisterXorCopySpec qubits width)
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (outsideSource : ∀ index, wire ≠ spec.source.wire index)
    (outsideTarget : ∀ index, wire ≠ spec.target.wire index) :
    registerXorCopyBasisAction spec (xorWire wire value input) =
      xorWire wire value (registerXorCopyBasisAction spec input) := by
  funext observed
  by_cases isTarget : ∃ index, observed = spec.target.wire index
  · obtain ⟨index, rfl⟩ := isTarget
    rw [registerXorCopyBasisAction_readTarget]
    simp only [
      xorWire_apply_other wire (spec.target.wire index)
        (Ne.symm (outsideTarget index)),
      xorWire_apply_other wire (spec.source.wire index)
        (Ne.symm (outsideSource index))]
    rw [registerXorCopyBasisAction_readTarget]
  · have outsideObserved : ∀ index, observed ≠ spec.target.wire index := by
      intro index equal
      exact isTarget ⟨index, equal⟩
    rw [registerXorCopyBasisAction_applyOutside spec
        (xorWire wire value input) observed outsideObserved]
    by_cases equal : observed = wire
    · subst observed
      rw [xorWire_apply_same, xorWire_apply_same,
        registerXorCopyBasisAction_applyOutside spec input wire outsideTarget]
    · rw [xorWire_apply_other wire observed equal,
        xorWire_apply_other wire observed equal,
        registerXorCopyBasisAction_applyOutside spec input observed
          outsideObserved]

/-- register XOR copyの主要意味を直接表す0-1作用素。 -/
def registerXorCopyPureOperator {qubits width : Nat}
    (spec : RegisterXorCopySpec qubits width) : Operator (QubitBasis qubits) :=
  deterministicOperator (registerXorCopyBasisAction spec)

/-- register XOR copy の実行順 CNOT 作用素列。 -/
def registerXorCopyAnalyticOperator {qubits width : Nat}
    (spec : RegisterXorCopySpec qubits width) : Operator (QubitBasis qubits) :=
  operatorSequence <|
    (List.finRange width).map fun index =>
      reversibleAnalyticCnotOperator (spec.source.wire index) (spec.target.wire index)

/-- 一つの外部 control が一のときだけ source を target へ XOR copy する layout。 -/
structure ControlledRegisterXorCopySpec (qubits width : Nat) where
  /-- 外部 control wire。 -/
  control : Fin qubits
  /-- 読み取り専用 source register。 -/
  source : Register qubits width
  /-- XOR 更新する target register。 -/
  target : Register qubits width
  /-- source と target は互いに素。 -/
  sourceTargetDisjoint : ∀ sourceIndex targetIndex,
    source.wire sourceIndex ≠ target.wire targetIndex
  /-- control は全 source wire と相異なる。 -/
  controlSourceDifferent : ∀ index, control ≠ source.wire index
  /-- control は全 target wire と相異なる。 -/
  controlTargetDifferent : ∀ index, control ≠ target.wire index

/-- Forget the external control while retaining the same register layout. -/
def ControlledRegisterXorCopySpec.toRegisterXorCopySpec
    {qubits width : Nat} (spec : ControlledRegisterXorCopySpec qubits width) :
    RegisterXorCopySpec qubits width where
  source := spec.source
  target := spec.target
  disjoint := spec.sourceTargetDisjoint

/-- controlが一のときだけsource bitをtargetへXORする直接基底関数。 -/
def controlledRegisterXorCopyBasisAction {qubits width : Nat}
    (spec : ControlledRegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  (List.finRange width).foldl
    (fun state index =>
      xorWire (spec.target.wire index)
        (state spec.control && state (spec.source.wire index)) state)
    input

/-- injective target列を制御付きXOR更新したときの指定target値。 -/
theorem foldl_controlledRegisterXorCopy_readTarget
    {Index : Type*} {qubits : Nat}
    (indices : List Index) (control : Fin qubits)
    (source target : Index → Fin qubits)
    (sourceTargetDisjoint : ∀ sourceIndex targetIndex,
      source sourceIndex ≠ target targetIndex)
    (controlTargetDifferent : ∀ index, control ≠ target index)
    (targetInjective : Function.Injective target)
    (chosen : Index) (chosenMembership : chosen ∈ indices)
    (indicesNodup : indices.Nodup) (input : QubitBasis qubits) :
    (indices.foldl
      (fun state index => xorWire (target index)
        (state control && state (source index)) state) input) (target chosen) =
      (input (target chosen) !=
        (input control && input (source chosen))) := by
  induction indices generalizing input with
  | nil => simp at chosenMembership
  | cons first rest inductionHypothesis =>
      have restNodup := indicesNodup.tail
      by_cases firstChosen : first = chosen
      · subst first
        have chosenNotInRest : chosen ∉ rest :=
          (List.nodup_cons.mp indicesNodup).1
        simp only [List.foldl_cons]
        rw [foldl_xorWire_preserves rest target
          (fun state index => state control && state (source index))
          (target chosen)
          (fun index membership equal => by
            have indexChosen := targetInjective equal
            subst index
            exact chosenNotInRest membership)]
        simp [xorWire]
      · have chosenInRest : chosen ∈ rest := by
          have cases : chosen = first ∨ chosen ∈ rest := by
            simpa only [List.mem_cons] using chosenMembership
          exact cases.resolve_left (Ne.symm firstChosen)
        simp only [List.foldl_cons]
        rw [inductionHypothesis chosenInRest restNodup]
        have targetDifferent : target first ≠ target chosen := by
          intro equal
          exact firstChosen (targetInjective equal)
        simp [xorWire, Ne.symm targetDifferent,
          controlTargetDifferent first, sourceTargetDisjoint chosen first]

/-- 制御付きregister XOR copyは外部control bitを保存する。 -/
theorem controlledRegisterXorCopyBasisAction_readControl
    {qubits width : Nat} (spec : ControlledRegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) :
    controlledRegisterXorCopyBasisAction spec input spec.control =
      input spec.control := by
  unfold controlledRegisterXorCopyBasisAction
  exact foldl_xorWire_preserves (List.finRange width) spec.target.wire
    (fun state index => state spec.control && state (spec.source.wire index))
    spec.control (fun index _ => Ne.symm (spec.controlTargetDifferent index)) input

/-- 制御付きregister XOR copyはsource registerの各bitを保存する。 -/
theorem controlledRegisterXorCopyBasisAction_readSource
    {qubits width : Nat} (spec : ControlledRegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) (index : Fin width) :
    controlledRegisterXorCopyBasisAction spec input (spec.source.wire index) =
      input (spec.source.wire index) := by
  unfold controlledRegisterXorCopyBasisAction
  exact foldl_xorWire_preserves (List.finRange width) spec.target.wire
    (fun state targetIndex => state spec.control &&
      state (spec.source.wire targetIndex))
    (spec.source.wire index)
    (fun targetIndex _ => Ne.symm (spec.sourceTargetDisjoint index targetIndex)) input

/-- 制御付きcopy後のtarget bitはcontrol AND sourceを元targetへXORした値である。 -/
theorem controlledRegisterXorCopyBasisAction_readTarget
    {qubits width : Nat} (spec : ControlledRegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) (index : Fin width) :
    controlledRegisterXorCopyBasisAction spec input (spec.target.wire index) =
      (input (spec.target.wire index) !=
        (input spec.control && input (spec.source.wire index))) := by
  unfold controlledRegisterXorCopyBasisAction
  exact foldl_controlledRegisterXorCopy_readTarget (List.finRange width)
    spec.control spec.source.wire spec.target.wire spec.sourceTargetDisjoint
    spec.controlTargetDifferent spec.target.injective index
    (List.mem_finRange index) (List.nodup_finRange width) input

/-- 制御付きregister XOR copyはtarget外の指定wireを保存する。 -/
theorem controlledRegisterXorCopyBasisAction_applyOutside
    {qubits width : Nat} (spec : ControlledRegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outsideTarget : ∀ index, wire ≠ spec.target.wire index) :
    controlledRegisterXorCopyBasisAction spec input wire = input wire := by
  unfold controlledRegisterXorCopyBasisAction
  exact foldl_xorWire_preserves (List.finRange width) spec.target.wire
    (fun state index => state spec.control && state (spec.source.wire index)) wire
    (fun index _ => Ne.symm (outsideTarget index)) input

/-- The controlled pure action is the corresponding unconditional copy when
the control is set, and the identity otherwise. -/
theorem controlledRegisterXorCopyBasisAction_eq_if
    {qubits width : Nat} (spec : ControlledRegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) :
    controlledRegisterXorCopyBasisAction spec input =
      if input spec.control then
        registerXorCopyBasisAction spec.toRegisterXorCopySpec input
      else input := by
  by_cases enabled : input spec.control
  · simp only [enabled, if_true]
    funext observed
    by_cases isTarget : ∃ index, observed = spec.target.wire index
    · obtain ⟨index, rfl⟩ := isTarget
      rw [controlledRegisterXorCopyBasisAction_readTarget,
        show
          registerXorCopyBasisAction spec.toRegisterXorCopySpec input
              (spec.target.wire index) =
            (input (spec.target.wire index) !=
              input (spec.source.wire index)) by
          simpa only [ControlledRegisterXorCopySpec.toRegisterXorCopySpec]
            using registerXorCopyBasisAction_readTarget
              spec.toRegisterXorCopySpec input index]
      simp only [enabled, Bool.true_and]
    · have outsideObserved : ∀ index,
          observed ≠ spec.target.wire index := by
        intro index equal
        exact isTarget ⟨index, equal⟩
      rw [controlledRegisterXorCopyBasisAction_applyOutside spec input
          observed outsideObserved,
        registerXorCopyBasisAction_applyOutside
          spec.toRegisterXorCopySpec input observed outsideObserved]
  · simp only [enabled]
    funext observed
    by_cases isTarget : ∃ index, observed = spec.target.wire index
    · obtain ⟨index, rfl⟩ := isTarget
      rw [controlledRegisterXorCopyBasisAction_readTarget]
      simp [enabled]
    · exact controlledRegisterXorCopyBasisAction_applyOutside spec input
        observed (by
          intro index equal
          exact isTarget ⟨index, equal⟩)

/-- Controlled XOR copy commutes with toggling a wire outside the control,
source, and target registers. -/
theorem controlledRegisterXorCopyBasisAction_commutes_xorWire_outside
    {qubits width : Nat} (spec : ControlledRegisterXorCopySpec qubits width)
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (outsideControl : wire ≠ spec.control)
    (outsideSource : ∀ index, wire ≠ spec.source.wire index)
    (outsideTarget : ∀ index, wire ≠ spec.target.wire index) :
    controlledRegisterXorCopyBasisAction spec (xorWire wire value input) =
      xorWire wire value
        (controlledRegisterXorCopyBasisAction spec input) := by
  funext observed
  by_cases isTarget : ∃ index, observed = spec.target.wire index
  · obtain ⟨index, rfl⟩ := isTarget
    rw [controlledRegisterXorCopyBasisAction_readTarget]
    simp only [
      xorWire_apply_other wire (spec.target.wire index)
        (Ne.symm (outsideTarget index)),
      xorWire_apply_other wire spec.control (Ne.symm outsideControl),
      xorWire_apply_other wire (spec.source.wire index)
        (Ne.symm (outsideSource index))]
    rw [controlledRegisterXorCopyBasisAction_readTarget]
  · have outsideObserved : ∀ index, observed ≠ spec.target.wire index := by
      intro index equal
      exact isTarget ⟨index, equal⟩
    rw [controlledRegisterXorCopyBasisAction_applyOutside spec
        (xorWire wire value input) observed outsideObserved]
    by_cases equal : observed = wire
    · subst observed
      rw [xorWire_apply_same, xorWire_apply_same,
        controlledRegisterXorCopyBasisAction_applyOutside spec input wire
          outsideTarget]
    · rw [xorWire_apply_other wire observed equal,
        xorWire_apply_other wire observed equal,
        controlledRegisterXorCopyBasisAction_applyOutside spec input observed
          outsideObserved]

/-- 制御付きregister XOR copyの主要意味を直接表す0-1作用素。 -/
def controlledRegisterXorCopyPureOperator {qubits width : Nat}
    (spec : ControlledRegisterXorCopySpec qubits width) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (controlledRegisterXorCopyBasisAction spec)

/-- 制御付き register XOR copy の実行順 Toffoli 作用素列。 -/
def controlledRegisterXorCopyAnalyticOperator {qubits width : Nat}
    (spec : ControlledRegisterXorCopySpec qubits width) :
    Operator (QubitBasis qubits) :=
  operatorSequence <|
    (List.finRange width).map fun index =>
      analyticToffoliOperator spec.control (spec.source.wire index)
        (spec.target.wire index)

/-- 一つの外部 control により二 register を条件付き交換する layout。 -/
structure ControlledRegisterSwapSpec (qubits width : Nat) where
  /-- 外部 control wire。 -/
  control : Fin qubits
  /-- 交換する左 register。 -/
  left : Register qubits width
  /-- 交換する右 register。 -/
  right : Register qubits width
  /-- 左右 register は互いに素。 -/
  leftRightDisjoint : ∀ leftIndex rightIndex,
    left.wire leftIndex ≠ right.wire rightIndex
  /-- control は全左 wire と相異なる。 -/
  controlLeftDifferent : ∀ index, control ≠ left.wire index
  /-- control は全右 wire と相異なる。 -/
  controlRightDifferent : ∀ index, control ≠ right.wire index

/-- controlが一のときだけ一組のleft/right bitを交換する直接基底関数。 -/
def fredkinBasisAction {qubits : Nat} (control left right : Fin qubits)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  if input control then
    Function.update (Function.update input left (input right)) right (input left)
  else input

/-- register各bit対を順に条件付き交換する回路非依存な基底関数。 -/
def controlledRegisterSwapBasisAction {qubits width : Nat}
    (spec : ControlledRegisterSwapSpec qubits width)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  (List.finRange width).foldl
    (fun state index =>
      fredkinBasisAction spec.control (spec.left.wire index)
        (spec.right.wire index) state)
    input

/-- 一bit Fredkinはleft/right以外のwireを保存する。 -/
theorem fredkinBasisAction_applyOutside {qubits : Nat}
    (control left right : Fin qubits) (input : QubitBasis qubits)
    (wire : Fin qubits) (leftDifferent : wire ≠ left)
    (rightDifferent : wire ≠ right) :
    fredkinBasisAction control left right input wire = input wire := by
  unfold fredkinBasisAction
  by_cases enabled : input control <;>
    simp [enabled, leftDifferent, rightDifferent]

/-- 有効な一bit Fredkin後のleft値は元right、無効時は元leftである。 -/
theorem fredkinBasisAction_readLeft {qubits : Nat}
    (control left right : Fin qubits) (input : QubitBasis qubits)
    (different : left ≠ right) :
    fredkinBasisAction control left right input left =
      if input control then input right else input left := by
  unfold fredkinBasisAction
  by_cases enabled : input control <;>
    simp [enabled, different]

/-- 有効な一bit Fredkin後のright値は元left、無効時は元rightである。 -/
theorem fredkinBasisAction_readRight {qubits : Nat}
    (control left right : Fin qubits) (input : QubitBasis qubits) :
    fredkinBasisAction control left right input right =
      if input control then input left else input right := by
  unfold fredkinBasisAction
  by_cases enabled : input control <;>
    simp [enabled]

/-- Fredkin foldは全left/right targetと異なる指定wireを保存する。 -/
theorem foldl_fredkin_preserves
    {Index : Type*} {qubits : Nat}
    (indices : List Index) (control : Fin qubits)
    (left right : Index → Fin qubits) (wire : Fin qubits)
    (outsideLeft : ∀ index, index ∈ indices → wire ≠ left index)
    (outsideRight : ∀ index, index ∈ indices → wire ≠ right index)
    (input : QubitBasis qubits) :
    (indices.foldl
      (fun state index => fredkinBasisAction control (left index) (right index) state)
      input) wire = input wire := by
  induction indices generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis
        (fun index membership => outsideLeft index (by simp [membership]))
        (fun index membership => outsideRight index (by simp [membership]))]
      exact fredkinBasisAction_applyOutside control (left first) (right first)
        input wire (outsideLeft first (by simp)) (outsideRight first (by simp))

/-- register Fredkin fold後の指定left bitを解析する。 -/
theorem foldl_controlledRegisterSwap_readLeft
    {Index : Type*} {qubits : Nat}
    (indices : List Index) (control : Fin qubits)
    (left right : Index → Fin qubits)
    (leftRightDisjoint : ∀ leftIndex rightIndex,
      left leftIndex ≠ right rightIndex)
    (controlLeftDifferent : ∀ index, control ≠ left index)
    (controlRightDifferent : ∀ index, control ≠ right index)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (chosen : Index) (chosenMembership : chosen ∈ indices)
    (indicesNodup : indices.Nodup) (input : QubitBasis qubits) :
    (indices.foldl
      (fun state index => fredkinBasisAction control (left index) (right index) state)
      input) (left chosen) =
      if input control then input (right chosen) else input (left chosen) := by
  induction indices generalizing input with
  | nil => simp at chosenMembership
  | cons first rest inductionHypothesis =>
      have restNodup := indicesNodup.tail
      by_cases firstChosen : first = chosen
      · subst first
        have chosenNotInRest : chosen ∉ rest :=
          (List.nodup_cons.mp indicesNodup).1
        simp only [List.foldl_cons]
        rw [foldl_fredkin_preserves rest control left right (left chosen)
          (fun index membership equal => by
            have indexChosen := leftInjective equal.symm
            subst index
            exact chosenNotInRest membership)
          (fun index _ => leftRightDisjoint chosen index)]
        exact fredkinBasisAction_readLeft control (left chosen) (right chosen)
          input (leftRightDisjoint chosen chosen)
      · have chosenInRest : chosen ∈ rest := by
          have cases : chosen = first ∨ chosen ∈ rest := by
            simpa only [List.mem_cons] using chosenMembership
          exact cases.resolve_left (Ne.symm firstChosen)
        simp only [List.foldl_cons]
        rw [inductionHypothesis chosenInRest restNodup]
        rw [fredkinBasisAction_applyOutside control (left first) (right first)
          input control (controlLeftDifferent first) (controlRightDifferent first)]
        rw [fredkinBasisAction_applyOutside control (left first) (right first)
          input (right chosen) (Ne.symm (leftRightDisjoint first chosen))
          (fun equal => firstChosen (rightInjective equal).symm)]
        rw [fredkinBasisAction_applyOutside control (left first) (right first)
          input (left chosen) (fun equal => firstChosen (leftInjective equal).symm)
          (leftRightDisjoint chosen first)]

/-- register Fredkin fold後の指定right bitを解析する。 -/
theorem foldl_controlledRegisterSwap_readRight
    {Index : Type*} {qubits : Nat}
    (indices : List Index) (control : Fin qubits)
    (left right : Index → Fin qubits)
    (leftRightDisjoint : ∀ leftIndex rightIndex,
      left leftIndex ≠ right rightIndex)
    (controlLeftDifferent : ∀ index, control ≠ left index)
    (controlRightDifferent : ∀ index, control ≠ right index)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (chosen : Index) (chosenMembership : chosen ∈ indices)
    (indicesNodup : indices.Nodup) (input : QubitBasis qubits) :
    (indices.foldl
      (fun state index => fredkinBasisAction control (left index) (right index) state)
      input) (right chosen) =
      if input control then input (left chosen) else input (right chosen) := by
  induction indices generalizing input with
  | nil => simp at chosenMembership
  | cons first rest inductionHypothesis =>
      have restNodup := indicesNodup.tail
      by_cases firstChosen : first = chosen
      · subst first
        have chosenNotInRest : chosen ∉ rest :=
          (List.nodup_cons.mp indicesNodup).1
        simp only [List.foldl_cons]
        rw [foldl_fredkin_preserves rest control left right (right chosen)
          (fun index _ => Ne.symm (leftRightDisjoint index chosen))
          (fun index membership equal => by
            have indexChosen := rightInjective equal.symm
            subst index
            exact chosenNotInRest membership)]
        exact fredkinBasisAction_readRight control (left chosen) (right chosen) input
      · have chosenInRest : chosen ∈ rest := by
          have cases : chosen = first ∨ chosen ∈ rest := by
            simpa only [List.mem_cons] using chosenMembership
          exact cases.resolve_left (Ne.symm firstChosen)
        simp only [List.foldl_cons]
        rw [inductionHypothesis chosenInRest restNodup]
        rw [fredkinBasisAction_applyOutside control (left first) (right first)
          input control (controlLeftDifferent first) (controlRightDifferent first)]
        rw [fredkinBasisAction_applyOutside control (left first) (right first)
          input (left chosen) (fun equal => firstChosen (leftInjective equal).symm)
          (leftRightDisjoint chosen first)]
        rw [fredkinBasisAction_applyOutside control (left first) (right first)
          input (right chosen) (Ne.symm (leftRightDisjoint first chosen))
          (fun equal => firstChosen (rightInjective equal).symm)]

/-- register Fredkin foldは左右register外の指定wireを保存する。 -/
theorem controlledRegisterSwapBasisAction_applyOutside
    {qubits width : Nat} (spec : ControlledRegisterSwapSpec qubits width)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outsideLeft : ∀ index, wire ≠ spec.left.wire index)
    (outsideRight : ∀ index, wire ≠ spec.right.wire index) :
    controlledRegisterSwapBasisAction spec input wire = input wire := by
  unfold controlledRegisterSwapBasisAction
  induction List.finRange width generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      exact fredkinBasisAction_applyOutside spec.control
        (spec.left.wire first) (spec.right.wire first) input wire
        (outsideLeft first) (outsideRight first)

/-- register Fredkin foldは外部control bitを保存する。 -/
theorem controlledRegisterSwapBasisAction_readControl
    {qubits width : Nat} (spec : ControlledRegisterSwapSpec qubits width)
    (input : QubitBasis qubits) :
    controlledRegisterSwapBasisAction spec input spec.control = input spec.control := by
  exact controlledRegisterSwapBasisAction_applyOutside spec input spec.control
    spec.controlLeftDifferent spec.controlRightDifferent

/-- register Fredkin後のleft registerはcontrol時に元right、非control時に元leftである。 -/
theorem controlledRegisterSwapBasisAction_readLeft
    {qubits width : Nat} (spec : ControlledRegisterSwapSpec qubits width)
    (input : QubitBasis qubits) (index : Fin width) :
    controlledRegisterSwapBasisAction spec input (spec.left.wire index) =
      if input spec.control then input (spec.right.wire index)
      else input (spec.left.wire index) := by
  unfold controlledRegisterSwapBasisAction
  exact foldl_controlledRegisterSwap_readLeft (List.finRange width) spec.control
    spec.left.wire spec.right.wire spec.leftRightDisjoint
    spec.controlLeftDifferent spec.controlRightDifferent spec.left.injective
    spec.right.injective index (List.mem_finRange index)
    (List.nodup_finRange width) input

/-- register Fredkin後のright registerはcontrol時に元left、非control時に元rightである。 -/
theorem controlledRegisterSwapBasisAction_readRight
    {qubits width : Nat} (spec : ControlledRegisterSwapSpec qubits width)
    (input : QubitBasis qubits) (index : Fin width) :
    controlledRegisterSwapBasisAction spec input (spec.right.wire index) =
      if input spec.control then input (spec.left.wire index)
      else input (spec.right.wire index) := by
  unfold controlledRegisterSwapBasisAction
  exact foldl_controlledRegisterSwap_readRight (List.finRange width) spec.control
    spec.left.wire spec.right.wire spec.leftRightDisjoint
    spec.controlLeftDifferent spec.controlRightDifferent spec.left.injective
    spec.right.injective index (List.mem_finRange index)
    (List.nodup_finRange width) input

/-- 制御付きregister swapの主要意味を直接表す0-1作用素。 -/
def controlledRegisterSwapPureOperator {qubits width : Nat}
    (spec : ControlledRegisterSwapSpec qubits width) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (controlledRegisterSwapBasisAction spec)

/-- 一 bit Fredkin compiler の厳密な CNOT-Toffoli-CNOT 作用素積。 -/
def analyticFredkinOperator {qubits : Nat}
    (control left right : Fin qubits) : Operator (QubitBasis qubits) :=
  (reversibleAnalyticCnotOperator left right *
      analyticToffoliOperator control right left) *
    reversibleAnalyticCnotOperator left right

/-- 制御付き register swap の実行順 Fredkin 作用素列。 -/
def controlledRegisterSwapAnalyticOperator {qubits width : Nat}
    (spec : ControlledRegisterSwapSpec qubits width) :
    Operator (QubitBasis qubits) :=
  operatorSequence <|
    (List.finRange width).map fun index =>
      analyticFredkinOperator spec.control (spec.left.wire index)
        (spec.right.wire index)

/-- 同じ幅の2つのunsigned registerを比較し、結果を1 bitへXORするlayout。 -/
structure UnsignedLessThanXorSpec (qubits width : Nat) where
  /-- 幅0では最終borrow wireが存在しないため、幅は正とする。 -/
  widthPositive : 0 < width
  /-- little-endianの左operand。 -/
  lhs : Register qubits width
  /-- little-endianの右operand。 -/
  rhs : Register qubits width
  /-- 各桁のborrow-outを格納するsame-width work register。 -/
  borrow : Register qubits width
  /-- 比較結果をXORするtarget bit。 -/
  target : Fin qubits
  /-- 左右operandは互いに交わらない。 -/
  lhsRhsDifferent : ∀ lhsIndex rhsIndex,
    lhs.wire lhsIndex ≠ rhs.wire rhsIndex
  /-- lhsとborrow workは互いに交わらない。 -/
  lhsBorrowDifferent : ∀ lhsIndex borrowIndex,
    lhs.wire lhsIndex ≠ borrow.wire borrowIndex
  /-- rhsとborrow workは互いに交わらない。 -/
  rhsBorrowDifferent : ∀ rhsIndex borrowIndex,
    rhs.wire rhsIndex ≠ borrow.wire borrowIndex
  /-- targetは全lhs wireと異なる。 -/
  targetLhsDifferent : ∀ index, target ≠ lhs.wire index
  /-- targetは全rhs wireと異なる。 -/
  targetRhsDifferent : ∀ index, target ≠ rhs.wire index
  /-- targetは全borrow wireと異なる。 -/
  targetBorrowDifferent : ∀ index, target ≠ borrow.wire index

/-- All operand, work, and target wires touched by the comparison action. -/
def UnsignedLessThanXorSpec.supportWires {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) : Finset (Fin qubits) :=
  {spec.target} ∪
    Finset.univ.image spec.lhs.wire ∪
    Finset.univ.image spec.rhs.wire ∪
    Finset.univ.image spec.borrow.wire

/-- 1桁のunsigned subtractionで次のborrowを計算するBoolean式。 -/
def unsignedBorrowStep (lhsBit rhsBit previousBorrow : Bool) : Bool :=
  ((!lhsBit) && rhsBit) !=
    (((!lhsBit) && previousBorrow) != (rhsBit && previousBorrow))

/-- little-endian bit列を下位bitからfoldして得る最終borrow、すなわちunsigned less-than。 -/
def unsignedLessThanBits {width : Nat}
    (lhs rhs : QubitBasis width) : Bool :=
  (List.finRange width).foldl
    (fun previousBorrow index =>
      unsignedBorrowStep (lhs index) (rhs index) previousBorrow)
    false

/-- 正の添字の直前の添字を同じ有限幅の中で返す。 -/
def previousIndex {width : Nat} (index : Fin width) (positive : 0 < index.val) :
    Fin width :=
  ⟨index.val - 1, by omega⟩

/-- 1桁のborrow stepがborrow-outへXORするBoolean値。 -/
private abbrev unsignedBorrowStepValue {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (index : Fin width) (input : QubitBasis qubits) : Bool :=
  let previousBorrow :=
    if previous : 0 < index.val then
      input (spec.borrow.wire (previousIndex index previous))
    else false
  unsignedBorrowStep (input (spec.lhs.wire index))
    (input (spec.rhs.wire index)) previousBorrow

/-- 1桁のborrow-out wireを、現在のoperandと直前borrowに従ってXOR更新する。 -/
def unsignedBorrowStepBasisAction {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (index : Fin width) (input : QubitBasis qubits) : QubitBasis qubits :=
  let previousBorrow :=
    if previous : 0 < index.val then
      input (spec.borrow.wire (previousIndex index previous))
    else false
  xorWire (spec.borrow.wire index)
    (unsignedBorrowStep (input (spec.lhs.wire index))
      (input (spec.rhs.wire index)) previousBorrow) input

/-- 全borrow-outを下位bitから順に計算する直接基底関数。 -/
def unsignedBorrowComputeBasisAction {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  (List.finRange width).foldl
    (fun state index => unsignedBorrowStepBasisAction spec index state) input

/-- borrow計算の各stepを逆順に適用する直接uncompute関数。 -/
def unsignedBorrowUncomputeBasisAction {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  (List.finRange width).reverse.foldl
    (fun state index => unsignedBorrowStepBasisAction spec index state) input

/-- 最終borrowをtargetへXORする独立なuse基底作用。 -/
def unsignedLessThanUseBasisAction {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire spec.target
    (input (spec.borrow.wire ⟨width - 1,
      Nat.sub_lt spec.widthPositive Nat.zero_lt_one⟩)) input

/-- same-width ripple-borrow回路のdirty全入力上の直接解析作用。 -/
def unsignedLessThanXorDirtyBasisAction {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  let computed := unsignedBorrowComputeBasisAction spec input
  let used := unsignedLessThanUseBasisAction spec computed
  unsignedBorrowUncomputeBasisAction spec used

/-- dirty全入力上の直接基底作用を表す0-1置換作用素。 -/
def unsignedLessThanXorDirtyBasisOperator {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (unsignedLessThanXorDirtyBasisAction spec)

/-- borrow computeの独立な直接基底作用素。 -/
def unsignedBorrowComputeOperator {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (unsignedBorrowComputeBasisAction spec)

/-- 最終borrowをtargetへXORする独立なuse作用素。 -/
def unsignedLessThanUseOperator {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (unsignedLessThanUseBasisAction spec)

/-- dirty全入力上のstrict full operator targetをpure compute/useから解析的に定める。 -/
def unsignedLessThanXorDirtyOperator {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    Operator (QubitBasis qubits) :=
  Matrix.conjTranspose (unsignedBorrowComputeOperator spec) *
    unsignedLessThanUseOperator spec * unsignedBorrowComputeOperator spec

/-- clean borrow入力でtargetだけをunsigned comparison結果によりXORする直接作用。 -/
def unsignedLessThanXorCleanBasisAction {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire spec.target
    (unsignedLessThanBits (spec.lhs.read input) (spec.rhs.read input)) input

/-- clean borrow 部分空間上の公開 target として使う、直接比較作用の決定的作用素。 -/
def unsignedLessThanXorCleanOperator {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (unsignedLessThanXorCleanBasisAction spec)

/-- 全borrow workが0であるclean入力条件。 -/
def UnsignedLessThanXorSpec.cleanInput {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) : Prop :=
  ∀ index, input (spec.borrow.wire index) = false

/-- 比較後にも全borrow workが0である出力条件。 -/
def UnsignedLessThanXorSpec.cleanOutput {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (output : QubitBasis qubits) : Prop :=
  ∀ index, output (spec.borrow.wire index) = false

/-- 比較回路がborrowを復元しoperandを保存してtargetだけを更新したという関係。 -/
def UnsignedLessThanXorSpec.restored {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (input output : QubitBasis qubits) : Prop :=
  output = unsignedLessThanXorCleanBasisAction spec input

end

end VerifiedCircuitCore
