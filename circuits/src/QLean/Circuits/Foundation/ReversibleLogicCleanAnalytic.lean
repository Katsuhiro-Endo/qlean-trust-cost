import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.QubitBasisEncoding
import QLean.Circuits.Foundation.OperatorLocalityAnalytic

/-!
# 可逆比較器の回路非依存clean解析意味論

same-width ripple-borrow比較器について、各stepの局所保存、自己逆性、target XORとの可換性を
実装ASTやその意味論をimportせず、純粋基底作用と局所作用素だけから証明する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 初期 borrow を明示した little-endian bit 列の純粋比較 fold。 -/
private def unsignedLessThanBitsWithBorrow {width : Nat}
    (initialBorrow : Bool) (lhs rhs : QubitBasis width) : Bool :=
  (List.finRange width).foldl
    (fun previousBorrow index =>
      unsignedBorrowStep (lhs index) (rhs index) previousBorrow)
    initialBorrow

/-- 初期 borrow 付き純粋 fold は、対応する little-endian 自然数不等式に一致する。 -/
private theorem unsignedLessThanBitsWithBorrow_eq_decide {width : Nat}
    (initialBorrow : Bool) (lhs rhs : QubitBasis width) :
    unsignedLessThanBitsWithBorrow initialBorrow lhs rhs =
      decide (qubitBasisLittleEndianIndex width lhs <
        qubitBasisLittleEndianIndex width rhs + if initialBorrow then 1 else 0) := by
  induction width generalizing initialBorrow with
  | zero =>
      cases initialBorrow <;>
        simp [unsignedLessThanBitsWithBorrow, qubitBasisLittleEndianIndex]
  | succ width inductionHypothesis =>
      let lhsTail : QubitBasis width := fun index => lhs index.succ
      let rhsTail : QubitBasis width := fun index => rhs index.succ
      let nextBorrow := unsignedBorrowStep (lhs 0) (rhs 0) initialBorrow
      rw [show unsignedLessThanBitsWithBorrow initialBorrow lhs rhs =
          unsignedLessThanBitsWithBorrow nextBorrow lhsTail rhsTail by
        simp [unsignedLessThanBitsWithBorrow, List.finRange_succ,
          List.foldl_map, lhsTail, rhsTail, nextBorrow]]
      rw [inductionHypothesis nextBorrow lhsTail rhsTail]
      cases lhsValue : lhs 0 <;> cases rhsValue : rhs 0 <;>
        cases initialBorrow <;>
        simp [qubitBasisLittleEndianIndex, lhsTail, rhsTail, nextBorrow,
          unsignedBorrowStep, lhsValue, rhsValue, Nat.bit] <;> omega

/-- 初期 borrow 0 の公開 bit 比較は little-endian 自然数の通常の `<` と一致する。 -/
theorem unsignedLessThanBits_eq_decide_lt {width : Nat}
    (lhs rhs : QubitBasis width) :
    unsignedLessThanBits lhs rhs =
      decide (qubitBasisLittleEndianIndex width lhs <
        qubitBasisLittleEndianIndex width rhs) := by
  simpa [unsignedLessThanBits, unsignedLessThanBitsWithBorrow] using
    unsignedLessThanBitsWithBorrow_eq_decide false lhs rhs

/-- 1 桁の borrow step が現在の operand と直前の borrow から読む Boolean 値。 -/
private abbrev cleanUnsignedBorrowStepValue {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (index : Fin width) (input : QubitBasis qubits) : Bool :=
  let previousBorrow :=
    if previous : 0 < index.val then
      input (spec.borrow.wire (previousIndex index previous))
    else false
  unsignedBorrowStep (input (spec.lhs.wire index))
    (input (spec.rhs.wire index)) previousBorrow

/-- 解析的な borrow step は、読取値を現在桁の borrow wire へ XOR する。 -/
theorem unsignedBorrowStepBasisAction_eq_xorWire {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (index : Fin width) (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index input =
      xorWire (spec.borrow.wire index)
        (cleanUnsignedBorrowStepValue spec index input) input := by
  rfl

/-- borrow stepはlhs registerを保存する。 -/
@[simp] theorem unsignedBorrowStepBasisAction_lhs {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index lhsIndex : Fin width)
    (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index input (spec.lhs.wire lhsIndex) =
      input (spec.lhs.wire lhsIndex) := by
  apply xorWire_apply_other
  exact spec.lhsBorrowDifferent lhsIndex index

/-- borrow stepはrhs registerを保存する。 -/
@[simp] theorem unsignedBorrowStepBasisAction_rhs {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index rhsIndex : Fin width)
    (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index input (spec.rhs.wire rhsIndex) =
      input (spec.rhs.wire rhsIndex) := by
  apply xorWire_apply_other
  exact spec.rhsBorrowDifferent rhsIndex index

/-- borrow stepはcomparison targetを保存する。 -/
@[simp] theorem unsignedBorrowStepBasisAction_target {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width)
    (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index input spec.target = input spec.target := by
  apply xorWire_apply_other
  exact spec.targetBorrowDifferent index

/-- borrow stepは現在桁以外のborrow wireを保存する。 -/
@[simp] theorem unsignedBorrowStepBasisAction_otherBorrow {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index other : Fin width)
    (different : other ≠ index) (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index input (spec.borrow.wire other) =
      input (spec.borrow.wire other) := by
  apply xorWire_apply_other
  exact fun equal => different (spec.borrow.injective equal)

/-- borrow stepが読むBoolean値は、そのstep自身によって変化しない。 -/
theorem cleanUnsignedBorrowStepValue_preserved {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width)
    (input : QubitBasis qubits) :
    cleanUnsignedBorrowStepValue spec index
        (unsignedBorrowStepBasisAction spec index input) =
      cleanUnsignedBorrowStepValue spec index input := by
  rw [unsignedBorrowStepBasisAction_eq_xorWire]
  by_cases positive : 0 < index.val
  · have previousDifferent : previousIndex index positive ≠ index := by
      intro equal
      have valueEqual := congrArg Fin.val equal
      simp [previousIndex] at valueEqual
      omega
    have previousWireDifferent :
        spec.borrow.wire (previousIndex index positive) ≠
          spec.borrow.wire index :=
      fun equal => previousDifferent (spec.borrow.injective equal)
    simp only [cleanUnsignedBorrowStepValue, dif_pos positive]
    simp [xorWire, spec.lhsBorrowDifferent index index,
      spec.rhsBorrowDifferent index index, previousWireDifferent]
  · simp only [cleanUnsignedBorrowStepValue, dif_neg positive]
    simp [xorWire, spec.lhsBorrowDifferent index index,
      spec.rhsBorrowDifferent index index]

/-- 1桁borrow-stepは同じ作用を2回適用すると元へ戻る。 -/
theorem unsignedBorrowStepBasisAction_involutive {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width) :
    Function.Involutive (unsignedBorrowStepBasisAction spec index) := by
  intro input
  rw [unsignedBorrowStepBasisAction_eq_xorWire,
    cleanUnsignedBorrowStepValue_preserved]
  exact xorWire_involutive (spec.borrow.wire index)
    (cleanUnsignedBorrowStepValue spec index input) input

/-- target XORはborrow stepが読む値を変化させない。 -/
theorem cleanUnsignedBorrowStepValue_targetXor {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width)
    (value : Bool) (input : QubitBasis qubits) :
    cleanUnsignedBorrowStepValue spec index (xorWire spec.target value input) =
      cleanUnsignedBorrowStepValue spec index input := by
  by_cases positive : 0 < index.val
  · let previous := previousIndex index positive
    simp [cleanUnsignedBorrowStepValue, positive, previous,
      xorWire_apply_other spec.target (spec.lhs.wire index)
        (Ne.symm (spec.targetLhsDifferent index)),
      xorWire_apply_other spec.target (spec.rhs.wire index)
        (Ne.symm (spec.targetRhsDifferent index)),
      xorWire_apply_other spec.target (spec.borrow.wire previous)
        (Ne.symm (spec.targetBorrowDifferent previous))]
  · simp [cleanUnsignedBorrowStepValue, positive,
      xorWire_apply_other spec.target (spec.lhs.wire index)
        (Ne.symm (spec.targetLhsDifferent index)),
      xorWire_apply_other spec.target (spec.rhs.wire index)
        (Ne.symm (spec.targetRhsDifferent index))]

/-- comparison targetのXORは各borrow-stepと可換である。 -/
theorem unsignedBorrowStepBasisAction_commutes_targetXor
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (index : Fin width) (value : Bool) (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index (xorWire spec.target value input) =
      xorWire spec.target value (unsignedBorrowStepBasisAction spec index input) := by
  rw [unsignedBorrowStepBasisAction_eq_xorWire,
    unsignedBorrowStepBasisAction_eq_xorWire,
    cleanUnsignedBorrowStepValue_targetXor]
  exact xorWire_commute (spec.borrow.wire index) spec.target
    (Ne.symm (spec.targetBorrowDifferent index)) _ _ input

/-- A borrow step commutes with XOR on a wire outside every comparator register. -/
theorem unsignedBorrowStepBasisAction_commutes_xorWire_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (index : Fin width) (wire : Fin qubits) (value : Bool)
    (input : QubitBasis qubits) (outside : wire ∉ spec.supportWires) :
    unsignedBorrowStepBasisAction spec index (xorWire wire value input) =
      xorWire wire value (unsignedBorrowStepBasisAction spec index input) := by
  have wire_ne_lhs : wire ≠ spec.lhs.wire index := by
    intro equal
    subst wire
    exact outside (by simp [UnsignedLessThanXorSpec.supportWires])
  have wire_ne_rhs : wire ≠ spec.rhs.wire index := by
    intro equal
    subst wire
    exact outside (by simp [UnsignedLessThanXorSpec.supportWires])
  have wire_ne_borrow : ∀ borrowIndex, wire ≠ spec.borrow.wire borrowIndex := by
    intro borrowIndex equal
    subst wire
    exact outside (by simp [UnsignedLessThanXorSpec.supportWires])
  have stepValue :
      cleanUnsignedBorrowStepValue spec index (xorWire wire value input) =
        cleanUnsignedBorrowStepValue spec index input := by
    by_cases positive : 0 < index.val
    · simp [cleanUnsignedBorrowStepValue, positive, xorWire,
        Ne.symm wire_ne_lhs, Ne.symm wire_ne_rhs,
        Ne.symm (wire_ne_borrow (previousIndex index positive))]
    · simp [cleanUnsignedBorrowStepValue, positive, xorWire,
        Ne.symm wire_ne_lhs, Ne.symm wire_ne_rhs]
  rw [unsignedBorrowStepBasisAction_eq_xorWire,
    unsignedBorrowStepBasisAction_eq_xorWire, stepValue]
  exact xorWire_commute (spec.borrow.wire index) wire
    (Ne.symm (wire_ne_borrow index)) _ _ input

/-- 自己逆な作用列は、逆順foldにより一般にuncomputeできる。 -/
theorem foldl_reverse_involutive {α : Type*} (actions : List (α → α))
    (involutive : ∀ action ∈ actions, Function.Involutive action)
    (input : α) :
    actions.reverse.foldl (fun state action => action state)
        (actions.foldl (fun state action => action state) input) = input := by
  induction actions generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.foldl_cons, List.reverse_cons, List.foldl_append]
      change first
          (rest.reverse.foldl (fun state action => action state)
            (rest.foldl (fun state action => action state) (first input))) = input
      rw [inductionHypothesis]
      · exact involutive first (by simp) input
      · intro action member
        exact involutive action (by simp [member])

/-- 添字付き自己逆作用を順方向と逆方向へ fold すると元へ戻る。 -/
theorem foldl_reverse_involutive_indexed {ι α : Type*}
    (indices : List ι) (action : ι → α → α)
    (involutive : ∀ index ∈ indices, Function.Involutive (action index))
    (input : α) :
    indices.reverse.foldl (fun state index => action index state)
        (indices.foldl (fun state index => action index state) input) = input := by
  induction indices generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.foldl_cons, List.reverse_cons, List.foldl_append]
      change action first
          (rest.reverse.foldl (fun state index => action index state)
            (rest.foldl (fun state index => action index state)
              (action first input))) = input
      rw [inductionHypothesis]
      · exact involutive first (by simp) input
      · intro index member
        exact involutive index (by simp [member])

/-- 同じ外部変換と可換な作用列の fold も、その外部変換と可換である。 -/
theorem foldl_commutes
    {α : Type*} (actions : List (α → α)) (outer : α → α)
    (commutes : ∀ action ∈ actions, ∀ input,
      action (outer input) = outer (action input)) (input : α) :
    actions.foldl (fun state action => action state) (outer input) =
      outer (actions.foldl (fun state action => action state) input) := by
  induction actions generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [commutes first (by simp)]
      apply inductionHypothesis
      intro action member state
      exact commutes action (by simp [member]) state

/-- 同じ外部変換と可換な添字付き作用列の fold も、その外部変換と可換である。 -/
theorem foldl_indexed_commutes
    {ι α : Type*} (indices : List ι) (action : ι → α → α)
    (outer : α → α)
    (commutes : ∀ index ∈ indices, ∀ input,
      action index (outer input) = outer (action index input)) (input : α) :
    indices.foldl (fun state index => action index state) (outer input) =
      outer (indices.foldl (fun state index => action index state) input) := by
  induction indices generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [commutes first (by simp)]
      apply inductionHypothesis
      intro index member state
      exact commutes index (by simp [member]) state

/-- The forward borrow fold commutes with XOR outside comparator support. -/
theorem unsignedBorrowComputeBasisAction_commutes_xorWire_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (outside : wire ∉ spec.supportWires) :
    unsignedBorrowComputeBasisAction spec (xorWire wire value input) =
      xorWire wire value (unsignedBorrowComputeBasisAction spec input) := by
  exact foldl_indexed_commutes (List.finRange width)
    (unsignedBorrowStepBasisAction spec) (xorWire wire value)
    (fun index _ state =>
      unsignedBorrowStepBasisAction_commutes_xorWire_outside
        spec index wire value state outside) input

/-- The reverse borrow fold commutes with XOR outside comparator support. -/
theorem unsignedBorrowUncomputeBasisAction_commutes_xorWire_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (outside : wire ∉ spec.supportWires) :
    unsignedBorrowUncomputeBasisAction spec (xorWire wire value input) =
      xorWire wire value (unsignedBorrowUncomputeBasisAction spec input) := by
  exact foldl_indexed_commutes (List.finRange width).reverse
    (unsignedBorrowStepBasisAction spec) (xorWire wire value)
    (fun index _ state =>
      unsignedBorrowStepBasisAction_commutes_xorWire_outside
        spec index wire value state outside) input

/-- The final-borrow use action commutes with XOR outside comparator support. -/
theorem unsignedLessThanUseBasisAction_commutes_xorWire_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (outside : wire ∉ spec.supportWires) :
    unsignedLessThanUseBasisAction spec (xorWire wire value input) =
      xorWire wire value (unsignedLessThanUseBasisAction spec input) := by
  have wire_ne_target : wire ≠ spec.target := by
    intro equal
    subst wire
    exact outside (by simp [UnsignedLessThanXorSpec.supportWires])
  let finalBorrow : Fin width :=
    ⟨width - 1, Nat.sub_lt spec.widthPositive Nat.zero_lt_one⟩
  have wire_ne_borrow : wire ≠ spec.borrow.wire finalBorrow := by
    intro equal
    subst wire
    exact outside (by simp [UnsignedLessThanXorSpec.supportWires])
  unfold unsignedLessThanUseBasisAction
  rw [xorWire_apply_other wire (spec.borrow.wire finalBorrow)
    (Ne.symm wire_ne_borrow)]
  exact xorWire_commute spec.target wire (Ne.symm wire_ne_target) _ _ input

/-- The complete dirty compute-use-uncompute comparison commutes with every
wire outside its explicitly declared support. -/
theorem unsignedLessThanXorDirtyBasisAction_commutes_xorWire_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (outside : wire ∉ spec.supportWires) :
    unsignedLessThanXorDirtyBasisAction spec (xorWire wire value input) =
      xorWire wire value (unsignedLessThanXorDirtyBasisAction spec input) := by
  unfold unsignedLessThanXorDirtyBasisAction
  change unsignedBorrowUncomputeBasisAction spec
      (unsignedLessThanUseBasisAction spec
        (unsignedBorrowComputeBasisAction spec (xorWire wire value input))) =
    xorWire wire value
      (unsignedBorrowUncomputeBasisAction spec
        (unsignedLessThanUseBasisAction spec
          (unsignedBorrowComputeBasisAction spec input)))
  rw [unsignedBorrowComputeBasisAction_commutes_xorWire_outside
      spec wire value input outside,
    unsignedLessThanUseBasisAction_commutes_xorWire_outside
      spec wire value (unsignedBorrowComputeBasisAction spec input) outside,
    unsignedBorrowUncomputeBasisAction_commutes_xorWire_outside
      spec wire value
      (unsignedLessThanUseBasisAction spec
        (unsignedBorrowComputeBasisAction spec input)) outside]

/-- borrow compute の逆向き fold は compute 後の状態を厳密に元へ戻す。 -/
theorem unsignedBorrowUncompute_compute {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) :
    unsignedBorrowUncomputeBasisAction spec
        (unsignedBorrowComputeBasisAction spec input) = input := by
  exact foldl_reverse_involutive_indexed (List.finRange width)
    (unsignedBorrowStepBasisAction spec)
    (fun index _ => unsignedBorrowStepBasisAction_involutive spec index) input

/-- borrow uncompute 後に compute を行っても元の状態へ戻る。 -/
theorem unsignedBorrowCompute_uncompute {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) :
    unsignedBorrowComputeBasisAction spec
        (unsignedBorrowUncomputeBasisAction spec input) = input := by
  simpa [unsignedBorrowComputeBasisAction,
    unsignedBorrowUncomputeBasisAction] using
    foldl_reverse_involutive_indexed (List.finRange width).reverse
      (unsignedBorrowStepBasisAction spec)
      (fun index _ => unsignedBorrowStepBasisAction_involutive spec index)
      input

/--
Mutually inverse compute/uncompute actions conjugate an involutive use action to
an involutive compute--use--uncompute action.
-/
theorem computeUseUncomputeBasisAction_involutive {basis : Type*}
    (compute use uncompute : basis → basis)
    (uncomputeCompute : Function.LeftInverse uncompute compute)
    (computeUncompute : Function.LeftInverse compute uncompute)
    (useInvolutive : Function.Involutive use) :
    Function.Involutive (fun input => uncompute (use (compute input))) := by
  intro input
  change uncompute (use (compute (uncompute (use (compute input))))) = input
  rw [computeUncompute, useInvolutive, uncomputeCompute]

/-- The final-borrow use action is self-inverse on every (possibly dirty) basis. -/
theorem unsignedLessThanUseBasisAction_involutive {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    Function.Involutive (unsignedLessThanUseBasisAction spec) := by
  intro input
  unfold unsignedLessThanUseBasisAction
  let finalBorrow : Fin width :=
    ⟨width - 1, Nat.sub_lt spec.widthPositive Nat.zero_lt_one⟩
  have borrowPreserved :
      xorWire spec.target (input (spec.borrow.wire finalBorrow)) input
          (spec.borrow.wire finalBorrow) =
        input (spec.borrow.wire finalBorrow) := by
    exact xorWire_apply_other spec.target (spec.borrow.wire finalBorrow)
      (Ne.symm (spec.targetBorrowDifferent finalBorrow)) _ input
  rw [borrowPreserved]
  exact xorWire_involutive spec.target
    (input (spec.borrow.wire finalBorrow)) input

/--
The dirty ripple-borrow comparison action is the conjugation of the use action
by mutually inverse borrow compute/uncompute actions, hence is self-inverse on
the full basis (no clean-work hypothesis is needed).
-/
theorem unsignedLessThanXorDirtyBasisAction_involutive {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    Function.Involutive (unsignedLessThanXorDirtyBasisAction spec) := by
  change Function.Involutive (fun input =>
    unsignedBorrowUncomputeBasisAction spec
      (unsignedLessThanUseBasisAction spec
        (unsignedBorrowComputeBasisAction spec input)))
  exact computeUseUncomputeBasisAction_involutive
    (unsignedBorrowComputeBasisAction spec)
    (unsignedLessThanUseBasisAction spec)
    (unsignedBorrowUncomputeBasisAction spec)
    (unsignedBorrowUncompute_compute spec)
    (unsignedBorrowCompute_uncompute spec)
    (unsignedLessThanUseBasisAction_involutive spec)

/-- 互いに逆な決定的基底作用では、転置共役作用素が逆作用の決定的作用素になる。 -/
theorem deterministicOperator_conjTranspose_of_inverse
    {basis : Type*} [DecidableEq basis]
    (forward backward : basis → basis)
    (leftInverse : Function.LeftInverse backward forward)
    (rightInverse : Function.RightInverse backward forward) :
    Matrix.conjTranspose (deterministicOperator forward) =
      deterministicOperator backward := by
  ext output input
  have equivalence : input = forward output ↔ output = backward input := by
    constructor
    · intro equal
      rw [equal, leftInverse]
    · intro equal
      rw [equal, rightInverse]
  simp [Matrix.conjTranspose_apply, deterministicOperator, equivalence]

/-- borrow compute 作用素の転置共役は解析的 uncompute 作用素である。 -/
theorem unsignedBorrowComputeOperator_conjTranspose
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width) :
    Matrix.conjTranspose (unsignedBorrowComputeOperator spec) =
      deterministicOperator (unsignedBorrowUncomputeBasisAction spec) := by
  apply deterministicOperator_conjTranspose_of_inverse
  · exact unsignedBorrowUncompute_compute spec
  · exact unsignedBorrowCompute_uncompute spec

/-- borrow uncompute は comparison target の定数 XOR と可換である。 -/
theorem unsignedBorrowUncompute_commutes_targetXor {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (value : Bool) (input : QubitBasis qubits) :
    unsignedBorrowUncomputeBasisAction spec
        (xorWire spec.target value input) =
      xorWire spec.target value
        (unsignedBorrowUncomputeBasisAction spec input) := by
  exact foldl_indexed_commutes (List.finRange width).reverse
    (unsignedBorrowStepBasisAction spec) (xorWire spec.target value)
    (fun index _ state =>
      unsignedBorrowStepBasisAction_commutes_targetXor
        spec index value state) input

/-- dirty 全入力での compute-use-uncompute 作用は、計算された最終 borrow だけを target へ XOR する。 -/
theorem unsignedLessThanXorDirtyBasisAction_eq_finalBorrowXor
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) :
    unsignedLessThanXorDirtyBasisAction spec input =
      xorWire spec.target
        ((unsignedBorrowComputeBasisAction spec input)
          (spec.borrow.wire ⟨width - 1,
            Nat.sub_lt spec.widthPositive Nat.zero_lt_one⟩)) input := by
  unfold unsignedLessThanXorDirtyBasisAction unsignedLessThanUseBasisAction
  rw [unsignedBorrowUncompute_commutes_targetXor,
    unsignedBorrowUncompute_compute]

/-- `Fin` 添字列が指定した自然数から一つずつ増えることを表す。 -/
def FinListStartsAt {width : Nat} (start : Nat)
    (indices : List (Fin width)) : Prop :=
  ∀ position (inside : position < indices.length),
    (indices[position]'inside).val = start + position

/-- `List.finRange width` は 0 から始まる連続添字列である。 -/
theorem finRange_startsAt_zero (width : Nat) :
    FinListStartsAt 0 (List.finRange width) := by
  intro position inside
  have element := List.getElem_finRange inside
  have value := congrArg Fin.val element
  rw [value]
  simp

/-- 連続添字列の先頭要素は開始値を持つ。 -/
theorem FinListStartsAt.head_value {width start : Nat}
    {head : Fin width} {tail : List (Fin width)}
    (chain : FinListStartsAt start (head :: tail)) : head.val = start := by
  have value := chain 0 (by simp)
  change head.val = start + 0 at value
  omega

/-- 連続添字列の tail は開始値を一つ増やした連続添字列である。 -/
theorem FinListStartsAt.tail {width start : Nat}
    {head : Fin width} {tail : List (Fin width)}
    (chain : FinListStartsAt start (head :: tail)) :
    FinListStartsAt (start + 1) tail := by
  intro position inside
  have value := chain (position + 1) (by simp [inside])
  change (tail[position]'inside).val = start + (position + 1) at value
  omega

/-- 連続 borrow fold の先頭が読む直前値についての帰納的不変条件。 -/
def BorrowPreviousReady {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (start : Nat) (initialBorrow : Bool) (state : QubitBasis qubits) : Prop :=
  (start = 0 ∧ initialBorrow = false) ∨
    ∃ previous : Fin width,
      previous.val + 1 = start ∧
      state (spec.borrow.wire previous) = initialBorrow

/-- 基準入力の operand bit を使って連続添字列上で計算する純粋な borrow fold。 -/
def unsignedBorrowFoldValue {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (baseline : QubitBasis qubits) (initialBorrow : Bool)
    (indices : List (Fin width)) : Bool :=
  indices.foldl
    (fun previousBorrow index =>
      unsignedBorrowStep (baseline (spec.lhs.wire index))
        (baseline (spec.rhs.wire index)) previousBorrow)
    initialBorrow

/-- 連続列の現在桁が読む borrow 値は、帰納不変条件が保持する値に一致する。 -/
theorem cleanUnsignedBorrowStepValue_eq_of_ready
    {qubits width start : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (index : Fin width) (baseline state : QubitBasis qubits)
    (initialBorrow : Bool) (indexValue : index.val = start)
    (lhsReady : ∀ operand,
      state (spec.lhs.wire operand) = baseline (spec.lhs.wire operand))
    (rhsReady : ∀ operand,
      state (spec.rhs.wire operand) = baseline (spec.rhs.wire operand))
    (previousReady : BorrowPreviousReady spec start initialBorrow state) :
    cleanUnsignedBorrowStepValue spec index state =
      unsignedBorrowStep (baseline (spec.lhs.wire index))
        (baseline (spec.rhs.wire index)) initialBorrow := by
  rcases previousReady with ⟨startZero, initialZero⟩ |
    ⟨previous, previousValue, previousReady⟩
  · have notPositive : ¬ 0 < index.val := by omega
    simp [cleanUnsignedBorrowStepValue, notPositive, lhsReady, rhsReady,
      initialZero]
  · have positive : 0 < index.val := by omega
    have previousIndexEq : previousIndex index positive = previous := by
      apply Fin.ext
      simp [previousIndex]
      omega
    simp [cleanUnsignedBorrowStepValue, positive, previousIndexEq,
      lhsReady, rhsReady, previousReady]

/-- 連続・重複なし・未使用 borrow が 0 という条件下で、回路 fold の最終 borrow は純粋 fold 値に一致する。 -/
theorem unsignedBorrowFold_final
    {qubits width start : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (indices : List (Fin width)) (baseline state : QubitBasis qubits)
    (initialBorrow : Bool)
    (chain : FinListStartsAt start indices)
    (nodup : indices.Nodup)
    (lhsReady : ∀ operand,
      state (spec.lhs.wire operand) = baseline (spec.lhs.wire operand))
    (rhsReady : ∀ operand,
      state (spec.rhs.wire operand) = baseline (spec.rhs.wire operand))
    (borrowClean : ∀ index ∈ indices,
      state (spec.borrow.wire index) = false)
    (previousReady : BorrowPreviousReady spec start initialBorrow state) :
    ∀ last, indices.getLast? = some last →
      (indices.foldl
          (fun current index => unsignedBorrowStepBasisAction spec index current)
          state) (spec.borrow.wire last) =
        unsignedBorrowFoldValue spec baseline initialBorrow indices := by
  induction indices generalizing start initialBorrow state with
  | nil => simp
  | cons head tail inductionHypothesis =>
      have headValue := chain.head_value
      have tailChain := chain.tail
      have nodupParts := List.nodup_cons.mp nodup
      let nextBorrow := unsignedBorrowStep
        (baseline (spec.lhs.wire head))
        (baseline (spec.rhs.wire head)) initialBorrow
      let nextState := unsignedBorrowStepBasisAction spec head state
      have readValue : cleanUnsignedBorrowStepValue spec head state = nextBorrow := by
        exact cleanUnsignedBorrowStepValue_eq_of_ready spec head baseline state
          initialBorrow headValue lhsReady rhsReady previousReady
      have headOutput : nextState (spec.borrow.wire head) = nextBorrow := by
        rw [show nextState = unsignedBorrowStepBasisAction spec head state from rfl,
          unsignedBorrowStepBasisAction_eq_xorWire, xorWire_apply_same,
          borrowClean head (by simp), readValue]
        simp
      have tailLhsReady : ∀ operand,
          nextState (spec.lhs.wire operand) =
            baseline (spec.lhs.wire operand) := by
        intro operand
        rw [show nextState = unsignedBorrowStepBasisAction spec head state from rfl,
          unsignedBorrowStepBasisAction_lhs, lhsReady]
      have tailRhsReady : ∀ operand,
          nextState (spec.rhs.wire operand) =
            baseline (spec.rhs.wire operand) := by
        intro operand
        rw [show nextState = unsignedBorrowStepBasisAction spec head state from rfl,
          unsignedBorrowStepBasisAction_rhs, rhsReady]
      have tailBorrowClean : ∀ index ∈ tail,
          nextState (spec.borrow.wire index) = false := by
        intro index member
        rw [show nextState = unsignedBorrowStepBasisAction spec head state from rfl,
          unsignedBorrowStepBasisAction_otherBorrow spec head index
            (fun equal => nodupParts.1 (equal ▸ member))]
        exact borrowClean index (by simp [member])
      have tailPreviousReady :
          BorrowPreviousReady spec (start + 1) nextBorrow nextState := by
        right
        exact ⟨head, by omega, headOutput⟩
      intro last lastValue
      cases tail with
      | nil =>
          simp only [List.foldl_cons, List.foldl_nil]
          simp only [List.getLast?_singleton] at lastValue
          cases lastValue
          exact headOutput
      | cons next rest =>
          simp only [List.foldl_cons]
          apply inductionHypothesis (start := start + 1)
            (initialBorrow := nextBorrow) (state := nextState)
            tailChain nodupParts.2 tailLhsReady tailRhsReady
            tailBorrowClean tailPreviousReady last lastValue

/-- 正の幅の `finRange` の末尾は自然数値 `width - 1` を持つ。 -/
theorem finRange_getLast?_eq_last {width : Nat} (positive : 0 < width) :
    (List.finRange width).getLast? =
      some ⟨width - 1, Nat.sub_lt positive Nat.zero_lt_one⟩ := by
  rw [List.getLast?_eq_getElem?]
  simp only [List.length_finRange]
  have inside : width - 1 < (List.finRange width).length := by
    simp
    omega
  rw [List.getElem?_eq_getElem inside]
  congr 1
  apply Fin.ext
  have element := List.getElem_finRange inside
  have value := congrArg Fin.val element
  rw [value]
  simp

/-- clean borrow 入力では compute 後の最終 borrow が純粋な bit 列比較結果に一致する。 -/
theorem unsignedBorrowCompute_final_eq_unsignedLessThanBits
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) (clean : spec.cleanInput input) :
    (unsignedBorrowComputeBasisAction spec input)
        (spec.borrow.wire ⟨width - 1,
          Nat.sub_lt spec.widthPositive Nat.zero_lt_one⟩) =
      unsignedLessThanBits (spec.lhs.read input) (spec.rhs.read input) := by
  have result := unsignedBorrowFold_final spec (List.finRange width)
    input input false (finRange_startsAt_zero width)
    (List.nodup_finRange width) (fun _ => rfl) (fun _ => rfl)
    (fun index _ => clean index) (by left; exact ⟨rfl, rfl⟩)
    ⟨width - 1, Nat.sub_lt spec.widthPositive Nat.zero_lt_one⟩
    (finRange_getLast?_eq_last spec.widthPositive)
  simpa [unsignedBorrowComputeBasisAction, unsignedBorrowFoldValue,
    unsignedLessThanBits, Register.read] using result

/-- dirty strict target は各計算基底 ket 上で dirty 基底作用を実行する。 -/
theorem applyOperator_unsignedLessThanXorDirtyOperator_basisKet
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) :
    applyOperator (unsignedLessThanXorDirtyOperator spec) (basisKet input) =
      basisKet (unsignedLessThanXorDirtyBasisAction spec input) := by
  unfold unsignedLessThanXorDirtyOperator
  rw [unsignedBorrowComputeOperator_conjTranspose]
  unfold unsignedBorrowComputeOperator unsignedLessThanUseOperator
  rw [applyOperator_mul, applyOperator_mul,
    applyOperator_deterministicOperator_basisKet,
    applyOperator_deterministicOperator_basisKet,
    applyOperator_deterministicOperator_basisKet]
  rfl

/-- dirty strict作用素は直接のdirty基底作用を持つ決定的作用素に一致する。 -/
theorem unsignedLessThanXorDirtyOperator_eq_deterministicOperator
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width) :
    unsignedLessThanXorDirtyOperator spec =
      deterministicOperator (unsignedLessThanXorDirtyBasisAction spec) := by
  ext output input
  calc
    unsignedLessThanXorDirtyOperator spec output input =
        applyOperator (unsignedLessThanXorDirtyOperator spec)
          (basisKet input) output := by rw [applyOperator_basisKet]
    _ = basisKet (unsignedLessThanXorDirtyBasisAction spec input) output := by
      rw [applyOperator_unsignedLessThanXorDirtyOperator_basisKet]
    _ = deterministicOperator
        (unsignedLessThanXorDirtyBasisAction spec) output input := rfl

/-- One borrow step leaves every wire outside the complete comparator support
pointwise unchanged. -/
theorem unsignedBorrowStepBasisAction_apply_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (index : Fin width) (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : wire ∉ spec.supportWires) :
    unsignedBorrowStepBasisAction spec index input wire = input wire := by
  unfold unsignedBorrowStepBasisAction
  apply xorWire_apply_other
  intro equal
  subst wire
  exact outside (by simp [UnsignedLessThanXorSpec.supportWires])

private theorem unsignedBorrowFoldBasisAction_apply_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (indices : List (Fin width)) (input : QubitBasis qubits)
    (wire : Fin qubits) (outside : wire ∉ spec.supportWires) :
    indices.foldl
        (fun state index => unsignedBorrowStepBasisAction spec index state)
        input wire = input wire := by
  induction indices generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis]
      exact unsignedBorrowStepBasisAction_apply_outside
        spec first input wire outside

/-- The forward borrow fold is pointwise identity outside comparator support. -/
theorem unsignedBorrowComputeBasisAction_apply_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : wire ∉ spec.supportWires) :
    unsignedBorrowComputeBasisAction spec input wire = input wire := by
  exact unsignedBorrowFoldBasisAction_apply_outside spec
    (List.finRange width) input wire outside

/-- The reverse borrow fold is pointwise identity outside comparator support. -/
theorem unsignedBorrowUncomputeBasisAction_apply_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : wire ∉ spec.supportWires) :
    unsignedBorrowUncomputeBasisAction spec input wire = input wire := by
  exact unsignedBorrowFoldBasisAction_apply_outside spec
    (List.finRange width).reverse input wire outside

/-- The final borrow-to-target use step is pointwise identity outside the same
declared comparator support. -/
theorem unsignedLessThanUseBasisAction_apply_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : wire ∉ spec.supportWires) :
    unsignedLessThanUseBasisAction spec input wire = input wire := by
  unfold unsignedLessThanUseBasisAction
  apply xorWire_apply_other
  intro equal
  subst wire
  exact outside (by simp [UnsignedLessThanXorSpec.supportWires])

/-- The full dirty compute-use-uncompute basis action cannot change any wire
outside the comparator's explicit support. -/
theorem unsignedLessThanXorDirtyBasisAction_apply_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : wire ∉ spec.supportWires) :
    unsignedLessThanXorDirtyBasisAction spec input wire = input wire := by
  unfold unsignedLessThanXorDirtyBasisAction
  calc
    unsignedBorrowUncomputeBasisAction spec
        (unsignedLessThanUseBasisAction spec
          (unsignedBorrowComputeBasisAction spec input)) wire =
        unsignedLessThanUseBasisAction spec
          (unsignedBorrowComputeBasisAction spec input) wire :=
      unsignedBorrowUncomputeBasisAction_apply_outside spec _ wire outside
    _ = unsignedBorrowComputeBasisAction spec input wire :=
      unsignedLessThanUseBasisAction_apply_outside spec _ wire outside
    _ = input wire :=
      unsignedBorrowComputeBasisAction_apply_outside spec input wire outside

/-- The full dirty less-than operator is local to the operands, borrow word,
and XOR target named by `UnsignedLessThanXorSpec.supportWires`. -/
theorem unsignedLessThanXorDirtyOperator_preservesOutside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width) :
    OperatorPreservesOutside spec.supportWires
      (unsignedLessThanXorDirtyOperator spec) := by
  rw [unsignedLessThanXorDirtyOperator_eq_deterministicOperator]
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  exact unsignedLessThanXorDirtyBasisAction_apply_outside
    spec input wire outside

/-- clean borrow 入力では dirty 基底作用が直接の unsigned less-than XOR 作用へ簡約される。 -/
theorem unsignedLessThanXorDirtyBasisAction_eq_clean
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) (clean : spec.cleanInput input) :
    unsignedLessThanXorDirtyBasisAction spec input =
      unsignedLessThanXorCleanBasisAction spec input := by
  rw [unsignedLessThanXorDirtyBasisAction_eq_finalBorrowXor,
    unsignedBorrowCompute_final_eq_unsignedLessThanBits spec input clean]
  rfl

/-- 直接の clean comparison 作用は全 borrow wire を 0 のまま保存する。 -/
theorem unsignedLessThanXorCleanBasisAction_cleanOutput
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) (clean : spec.cleanInput input) :
    spec.cleanOutput (unsignedLessThanXorCleanBasisAction spec input) := by
  intro index
  unfold unsignedLessThanXorCleanBasisAction
  rw [xorWire_apply_other spec.target (spec.borrow.wire index)
    (Ne.symm (spec.targetBorrowDifferent index))]
  exact clean index

/-- clean comparison の出力は公開 restoration 仕様に一致する。 -/
theorem unsignedLessThanXorCleanBasisAction_restored
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) :
    spec.restored input (unsignedLessThanXorCleanBasisAction spec input) := rfl

/-- The direct clean unsigned-comparison action changes no wire outside the
declared operand/work/target support. -/
theorem unsignedLessThanXorCleanBasisAction_apply_outside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : wire ∉ spec.supportWires) :
    unsignedLessThanXorCleanBasisAction spec input wire = input wire := by
  unfold unsignedLessThanXorCleanBasisAction
  rw [xorWire_apply_other]
  intro equal
  subst wire
  exact outside (by simp [UnsignedLessThanXorSpec.supportWires])

/-- The independently specified clean comparison operator is support-local;
this is distinct from locality of the full-dirty compute/use/uncompute word. -/
theorem unsignedLessThanXorCleanOperator_preservesOutside
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width) :
    OperatorPreservesOutside spec.supportWires
      (unsignedLessThanXorCleanOperator spec) := by
  unfold unsignedLessThanXorCleanOperator
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  exact unsignedLessThanXorCleanBasisAction_apply_outside
    spec input wire outside

end

end VerifiedCircuitCore
