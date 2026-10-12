import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.ReversibleLogicAnalytic

/-!
# 可逆 register 論理の基本 gate 実装

register XOR copy、制御付き copy、および Fredkin fold による制御付き swap を
X/CNOT/Toffoli のみで構成し、回路非依存な解析作用素積との厳密等式を証明する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- gate 列の `sequence` 意味論は各 gate 解析作用素の実行順積である。 -/
theorem denote_gate_sequence_eq_operatorSequence
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) :
    ∀ gates : List Gate,
      Circuit.denote gateOperator
          (Circuit.sequence (gates.map Circuit.gate)) =
        operatorSequence (gates.map gateOperator)
  | [] => rfl
  | first :: rest => by
      simp [Circuit.sequence, Circuit.denote, operatorSequence,
        denote_gate_sequence_eq_operatorSequence gateOperator rest]

/-- Primitive CNOT の意味論は回路非依存な CNOT 作用素である。 -/
@[simp] theorem primitiveCnotOperator_eq_reversibleAnalyticCnotOperator
    {qubits : Nat} (symbolValue : String → ℝ) (control target : Fin qubits)
    (different : control ≠ target) :
    primitiveGateOperatorWithSymbols symbolValue (.cnot control target different) =
      reversibleAnalyticCnotOperator control target := rfl

/-- Primitive Toffoli の意味論は回路非依存な Toffoli 作用素である。 -/
@[simp] theorem primitiveToffoliOperator_eq_analyticToffoliOperator
    {qubits : Nat} (symbolValue : String → ℝ)
    (control₀ control₁ target : Fin qubits)
    (controlsDifferent : control₀ ≠ control₁)
    (firstDifferent : control₀ ≠ target)
    (secondDifferent : control₁ ≠ target) :
    primitiveGateOperatorWithSymbols symbolValue
        (.toffoli control₀ control₁ target controlsDifferent
          firstDifferent secondDifferent) =
      analyticToffoliOperator control₀ control₁ target := rfl

/-- register XOR copy の CNOT gate 列。 -/
/- 上の古い説明を消費する非公開anchor。 -/
private def registerXorCopyCommentAnchor : Unit := ()

/-- `xorWire`後の基底一致を、target外保存とtarget bit値へ分解する。 -/
theorem eq_xorWire_iff {qubits : Nat} (target : Fin qubits) (value : Bool)
    (output input : QubitBasis qubits) :
    output = xorWire target value input ↔
      agreesExcept target output input ∧
        output target = (input target != value) := by
  constructor
  · intro equal
    subst output
    constructor
    · intro wire different
      simp [xorWire, different]
    · simp [xorWire]
  · rintro ⟨outside, targetValue⟩
    funext wire
    by_cases equal : wire = target
    · subst wire
      simpa [xorWire] using targetValue
    · simpa [xorWire, equal] using outside wire equal

/-- Primitive Xの作用素意味論はtarget bitの直接XOR基底作用である。 -/
@[simp] theorem primitiveXOperator_eq_deterministicOperator
    {qubits : Nat} (symbolValue : String → ℝ) (target : Fin qubits) :
    primitiveGateOperatorWithSymbols symbolValue (.x target) =
      deterministicOperator (xorWire target true) := by
  ext output input
  rw [primitiveGateOperatorWithSymbols, embedSingleQubitOperator_apply]
  by_cases outside : agreesExcept target output input
  · by_cases bitValue : output target = !input target
    · have fullEqual : output = xorWire target true input :=
        (eq_xorWire_iff target true output input).2
          ⟨outside, by simpa using bitValue⟩
      subst output
      rw [if_pos outside]
      simp [deterministicOperator, localX, xorWire]
    · have fullDifferent : output ≠ xorWire target true input := by
        intro fullEqual
        have targetEqual := ((eq_xorWire_iff target true output input).1 fullEqual).2
        exact bitValue (by simpa using targetEqual)
      simp [deterministicOperator, localX, outside, bitValue, fullDifferent]
  · have fullDifferent : output ≠ xorWire target true input := by
      intro fullEqual
      exact outside ((eq_xorWire_iff target true output input).1 fullEqual).1
    simp [deterministicOperator, outside, fullDifferent]

/-- register XOR copy の CNOT gate 列。 -/
def registerXorCopyGates {qubits width : Nat}
    (spec : RegisterXorCopySpec qubits width) : List (PrimitiveGate qubits) :=
  (List.finRange width).map fun index =>
    .cnot (spec.source.wire index) (spec.target.wire index)
      (spec.disjoint index index)

/-- register XOR copy の基本 gate AST。 -/
def registerXorCopyCircuit {qubits width : Nat}
    (spec : RegisterXorCopySpec qubits width) : Circuit (PrimitiveGate qubits) :=
  Circuit.sequence (registerXorCopyGates spec |>.map Circuit.gate)

/-- register XOR copy AST は独立な CNOT 解析作用素積に厳密一致する。 -/
theorem registerXorCopyCircuit_correct {qubits width : Nat}
    (symbolValue : String → ℝ) (spec : RegisterXorCopySpec qubits width) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (registerXorCopyCircuit spec) =
      registerXorCopyAnalyticOperator spec := by
  rw [registerXorCopyCircuit,
    denote_gate_sequence_eq_operatorSequence]
  unfold registerXorCopyGates registerXorCopyAnalyticOperator
  simp only [List.map_map]
  induction List.finRange width with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp only [List.map_cons, Function.comp_apply, operatorSequence]
      rw [primitiveCnotOperator_eq_reversibleAnalyticCnotOperator,
        inductionHypothesis]

/-- register XOR copyのstrict gate積targetは直接basis-map targetに一致する。 -/
theorem registerXorCopyAnalyticOperator_eq_pure {qubits width : Nat}
    (spec : RegisterXorCopySpec qubits width) :
    registerXorCopyAnalyticOperator spec =
      registerXorCopyPureOperator spec := by
  unfold registerXorCopyAnalyticOperator registerXorCopyPureOperator
    registerXorCopyBasisAction
  simpa [reversibleAnalyticCnotOperator, List.map_map, List.foldl_map,
    Function.comp_def] using
    (operatorSequence_deterministicOperator
      ((List.finRange width).map fun index state =>
        xorWire (spec.target.wire index) (state (spec.source.wire index)) state))

/-- register XOR copyを直接basis-map targetを持つsemantic exact componentとして公開する。 -/
def registerXorCopyComponent {qubits width : Nat}
    (symbolValue : String → ℝ) (spec : RegisterXorCopySpec qubits width) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := registerXorCopyCircuit spec
  target := registerXorCopyPureOperator spec
  correct := by
    rw [registerXorCopyCircuit_correct,
      registerXorCopyAnalyticOperator_eq_pure]

/-- register XOR copy を exact component として公開する。 -/
def registerXorCopyStrictCompilerComponent {qubits width : Nat}
    (symbolValue : String → ℝ) (spec : RegisterXorCopySpec qubits width) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := registerXorCopyCircuit spec
  target := registerXorCopyAnalyticOperator spec
  correct := registerXorCopyCircuit_correct symbolValue spec

/-- 制御付き register XOR copy の Toffoli gate 列。 -/
def controlledRegisterXorCopyGates {qubits width : Nat}
    (spec : ControlledRegisterXorCopySpec qubits width) :
    List (PrimitiveGate qubits) :=
  (List.finRange width).map fun index =>
    .toffoli spec.control (spec.source.wire index) (spec.target.wire index)
      (spec.controlSourceDifferent index)
      (spec.controlTargetDifferent index)
      (spec.sourceTargetDisjoint index index)

/-- 制御付き register XOR copy の基本 gate AST。 -/
def controlledRegisterXorCopyCircuit {qubits width : Nat}
    (spec : ControlledRegisterXorCopySpec qubits width) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence (controlledRegisterXorCopyGates spec |>.map Circuit.gate)

/-- 制御付き register XOR copy AST は独立な Toffoli 解析作用素積に一致する。 -/
theorem controlledRegisterXorCopyCircuit_correct {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : ControlledRegisterXorCopySpec qubits width) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledRegisterXorCopyCircuit spec) =
      controlledRegisterXorCopyAnalyticOperator spec := by
  rw [controlledRegisterXorCopyCircuit,
    denote_gate_sequence_eq_operatorSequence]
  unfold controlledRegisterXorCopyGates
    controlledRegisterXorCopyAnalyticOperator
  simp only [List.map_map]
  induction List.finRange width with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp only [List.map_cons, Function.comp_apply, operatorSequence]
      rw [primitiveToffoliOperator_eq_analyticToffoliOperator,
        inductionHypothesis]

/-- 制御付きcopyのstrict gate積targetは直接basis-map targetに一致する。 -/
theorem controlledRegisterXorCopyAnalyticOperator_eq_pure
    {qubits width : Nat} (spec : ControlledRegisterXorCopySpec qubits width) :
    controlledRegisterXorCopyAnalyticOperator spec =
      controlledRegisterXorCopyPureOperator spec := by
  unfold controlledRegisterXorCopyAnalyticOperator
    controlledRegisterXorCopyPureOperator controlledRegisterXorCopyBasisAction
  simpa [analyticToffoliOperator, List.map_map, List.foldl_map,
    Function.comp_def] using
    (operatorSequence_deterministicOperator
      ((List.finRange width).map fun index state =>
        xorWire (spec.target.wire index)
          (state spec.control && state (spec.source.wire index)) state))

/-- 制御付きcopyを直接basis-map targetを持つsemantic exact componentとして公開する。 -/
def controlledRegisterXorCopyComponent {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : ControlledRegisterXorCopySpec qubits width) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := controlledRegisterXorCopyCircuit spec
  target := controlledRegisterXorCopyPureOperator spec
  correct := by
    rw [controlledRegisterXorCopyCircuit_correct,
      controlledRegisterXorCopyAnalyticOperator_eq_pure]

/-- 制御付き register XOR copy を exact component として公開する。 -/
def controlledRegisterXorCopyStrictCompilerComponent {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : ControlledRegisterXorCopySpec qubits width) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := controlledRegisterXorCopyCircuit spec
  target := controlledRegisterXorCopyAnalyticOperator spec
  correct := controlledRegisterXorCopyCircuit_correct symbolValue spec

/-- 一 bit Fredkin を CNOT-Toffoli-CNOT で実装する gate 列。 -/
def fredkinGates {qubits : Nat} (control left right : Fin qubits)
    (controlLeftDifferent : control ≠ left)
    (controlRightDifferent : control ≠ right)
    (leftRightDifferent : left ≠ right) : List (PrimitiveGate qubits) := [
  .cnot left right leftRightDifferent,
  .toffoli control right left controlRightDifferent controlLeftDifferent
    (Ne.symm leftRightDifferent),
  .cnot left right leftRightDifferent
]

/-- register 全体の制御付き swap を実装する Fredkin gate 列。 -/
def controlledRegisterSwapGates {qubits width : Nat}
    (spec : ControlledRegisterSwapSpec qubits width) :
    List (PrimitiveGate qubits) :=
  (List.finRange width).flatMap fun index =>
    fredkinGates spec.control (spec.left.wire index) (spec.right.wire index)
      (spec.controlLeftDifferent index)
      (spec.controlRightDifferent index)
      (spec.leftRightDisjoint index index)

/-- 制御付き register swap の基本 gate AST。 -/
def controlledRegisterSwapCircuit {qubits width : Nat}
    (spec : ControlledRegisterSwapSpec qubits width) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence (controlledRegisterSwapGates spec |>.map Circuit.gate)

/-- 一 bit Fredkin gate 列の意味論は独立な Fredkin 解析作用素積に一致する。 -/
theorem denote_fredkinGates {qubits : Nat} (symbolValue : String → ℝ)
    (control left right : Fin qubits)
    (controlLeftDifferent : control ≠ left)
    (controlRightDifferent : control ≠ right)
    (leftRightDifferent : left ≠ right) :
    operatorSequence
      ((fredkinGates control left right controlLeftDifferent
        controlRightDifferent leftRightDifferent).map
        (primitiveGateOperatorWithSymbols symbolValue)) =
      analyticFredkinOperator control left right := by
  simp [fredkinGates, operatorSequence, analyticFredkinOperator,
    reversibleAnalyticCnotOperator, analyticToffoliOperator,
    primitiveGateOperatorWithSymbols]

/-- 制御付き register swap AST は Fredkin 解析作用素列に厳密一致する。 -/
theorem controlledRegisterSwapCircuit_correct {qubits width : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRegisterSwapSpec qubits width) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledRegisterSwapCircuit spec) =
      controlledRegisterSwapAnalyticOperator spec := by
  rw [controlledRegisterSwapCircuit,
    denote_gate_sequence_eq_operatorSequence]
  simp only [controlledRegisterSwapGates, List.map_flatMap,
    controlledRegisterSwapAnalyticOperator]
  induction List.finRange width with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp only [List.flatMap_cons,
        operatorSequence, List.map_cons]
      rw [operatorSequence_append,
        denote_fredkinGates symbolValue spec.control (spec.left.wire index)
          (spec.right.wire index) (spec.controlLeftDifferent index)
          (spec.controlRightDifferent index) (spec.leftRightDisjoint index index)]
      rw [inductionHypothesis]

/-- 制御付き register swap を exact component として公開する。 -/
/- 1 bit Fredkin の3ゲート積は、制御付き交換という直接基底作用に一致する。 -/
theorem analyticFredkinOperator_eq_pure {qubits : Nat}
    (control left right : Fin qubits)
    (_controlLeftDifferent : control ≠ left)
    (controlRightDifferent : control ≠ right)
    (leftRightDifferent : left ≠ right) :
    analyticFredkinOperator control left right =
      deterministicOperator (fredkinBasisAction control left right) := by
  rw [show analyticFredkinOperator control left right =
      operatorSequence
        ([fun input => xorWire right (input left) input,
          fun input => xorWire left (input control && input right) input,
          fun input => xorWire right (input left) input].map
            deterministicOperator) by
    simp [analyticFredkinOperator, operatorSequence,
      reversibleAnalyticCnotOperator, analyticToffoliOperator]]
  rw [operatorSequence_deterministicOperator]
  congr 1
  funext input
  apply funext
  intro wire
  by_cases controlValue : input control
  · by_cases wireIsLeft : wire = left
    · subst wire
      cases leftValue : input left <;> cases rightValue : input right <;>
        simp [fredkinBasisAction, controlValue, xorWire, Function.update_apply,
          leftValue, rightValue, controlRightDifferent, leftRightDifferent]
    · by_cases wireIsRight : wire = right
      · subst wire
        cases leftValue : input left <;> cases rightValue : input right <;>
          simp [fredkinBasisAction, controlValue, xorWire,
            leftValue, rightValue, controlRightDifferent, leftRightDifferent,
            Ne.symm leftRightDifferent]
      · simp [fredkinBasisAction, controlValue, xorWire, Function.update_apply,
          wireIsLeft, wireIsRight]
  · have controlFalse : input control = false :=
      Bool.eq_false_of_not_eq_true controlValue
    by_cases wireIsLeft : wire = left
    · subst wire
      cases leftValue : input left <;> cases rightValue : input right <;>
        simp [fredkinBasisAction, controlFalse, xorWire, Function.update_apply,
          leftValue, rightValue, controlRightDifferent, leftRightDifferent]
    · by_cases wireIsRight : wire = right
      · subst wire
        cases leftValue : input left <;> cases rightValue : input right <;>
          simp [fredkinBasisAction, controlFalse, xorWire,
            leftValue, rightValue, controlRightDifferent, leftRightDifferent,
            Ne.symm leftRightDifferent]
      · simp [fredkinBasisAction, controlFalse, xorWire, Function.update_apply,
          wireIsLeft, wireIsRight]

/-- register Fredkin のstrict gate積targetは、直接の制御付き交換targetに一致する。 -/
theorem controlledRegisterSwapAnalyticOperator_eq_pure
    {qubits width : Nat} (spec : ControlledRegisterSwapSpec qubits width) :
    controlledRegisterSwapAnalyticOperator spec =
      controlledRegisterSwapPureOperator spec := by
  unfold controlledRegisterSwapAnalyticOperator controlledRegisterSwapPureOperator
    controlledRegisterSwapBasisAction
  rw [show
      (List.map
        (fun index =>
          analyticFredkinOperator spec.control (spec.left.wire index)
            (spec.right.wire index))
        (List.finRange width)) =
      (List.map
        (fun index =>
          deterministicOperator
            (fredkinBasisAction spec.control (spec.left.wire index)
              (spec.right.wire index)))
        (List.finRange width)) by
    apply List.map_congr_left
    intro index indexMembership
    exact analyticFredkinOperator_eq_pure spec.control
      (spec.left.wire index) (spec.right.wire index)
      (spec.controlLeftDifferent index) (spec.controlRightDifferent index)
      (spec.leftRightDisjoint index index)]
  simpa [List.map_map, List.foldl_map, Function.comp_def] using
    (operatorSequence_deterministicOperator
      ((List.finRange width).map fun index state =>
        fredkinBasisAction spec.control (spec.left.wire index)
          (spec.right.wire index) state))

/-- 制御付きregister交換を直接basis-map targetで公開するsemantic component。 -/
def controlledRegisterSwapComponent {qubits width : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRegisterSwapSpec qubits width) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := controlledRegisterSwapCircuit spec
  target := controlledRegisterSwapPureOperator spec
  correct := by
    rw [controlledRegisterSwapCircuit_correct,
      controlledRegisterSwapAnalyticOperator_eq_pure]

/-- 制御付きregister交換のstrict compiler component。 -/
def controlledRegisterSwapStrictCompilerComponent {qubits width : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRegisterSwapSpec qubits width) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := controlledRegisterSwapCircuit spec
  target := controlledRegisterSwapAnalyticOperator spec
  correct := controlledRegisterSwapCircuit_correct symbolValue spec

/-- 正の桁で直前borrow wireと現在borrow-out wireが異なる。 -/
theorem previousBorrowWire_ne_current {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width)
    (positive : 0 < index.val) :
    spec.borrow.wire (previousIndex index positive) ≠ spec.borrow.wire index := by
  intro equal
  have indexEqual := spec.borrow.injective equal
  have valueEqual := congrArg Fin.val indexEqual
  simp [previousIndex] at valueEqual
  omega

/-- 1桁のborrow-out XOR更新を実装するX/Toffoli gate列。 -/
def unsignedBorrowStepGates {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width) :
    List (PrimitiveGate qubits) :=
  if positive : 0 < index.val then
    let previous := previousIndex index positive
    [
      .x (spec.lhs.wire index),
      .toffoli (spec.lhs.wire index) (spec.rhs.wire index)
        (spec.borrow.wire index)
        (spec.lhsRhsDifferent index index)
        (spec.lhsBorrowDifferent index index)
        (spec.rhsBorrowDifferent index index),
      .toffoli (spec.lhs.wire index) (spec.borrow.wire previous)
        (spec.borrow.wire index)
        (spec.lhsBorrowDifferent index previous)
        (spec.lhsBorrowDifferent index index)
        (previousBorrowWire_ne_current spec index positive),
      .toffoli (spec.rhs.wire index) (spec.borrow.wire previous)
        (spec.borrow.wire index)
        (spec.rhsBorrowDifferent index previous)
        (spec.rhsBorrowDifferent index index)
        (previousBorrowWire_ne_current spec index positive),
      .x (spec.lhs.wire index)
    ]
  else
    [
      .x (spec.lhs.wire index),
      .toffoli (spec.lhs.wire index) (spec.rhs.wire index)
        (spec.borrow.wire index)
        (spec.lhsRhsDifferent index index)
        (spec.lhsBorrowDifferent index index)
        (spec.rhsBorrowDifferent index index),
      .x (spec.lhs.wire index)
    ]

/-- 1桁のborrow更新gate列を回路ASTにしたもの。 -/
def unsignedBorrowStepCircuit {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence ((unsignedBorrowStepGates spec index).map Circuit.gate)

/-- 1桁compilerを構成する各基本gateの直接基底作用列。 -/
def unsignedBorrowStepCompilerActions {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width) :
    List (QubitBasis qubits → QubitBasis qubits) :=
  if positive : 0 < index.val then
    let previous := previousIndex index positive
    [
      fun input => xorWire (spec.lhs.wire index) true input,
      fun input => xorWire (spec.borrow.wire index)
        (input (spec.lhs.wire index) && input (spec.rhs.wire index)) input,
      fun input => xorWire (spec.borrow.wire index)
        (input (spec.lhs.wire index) && input (spec.borrow.wire previous)) input,
      fun input => xorWire (spec.borrow.wire index)
        (input (spec.rhs.wire index) && input (spec.borrow.wire previous)) input,
      fun input => xorWire (spec.lhs.wire index) true input
    ]
  else
    [
      fun input => xorWire (spec.lhs.wire index) true input,
      fun input => xorWire (spec.borrow.wire index)
        (input (spec.lhs.wire index) && input (spec.rhs.wire index)) input,
      fun input => xorWire (spec.lhs.wire index) true input
    ]

/-- 1桁gate列の各作用素は対応する直接決定的基底作用素である。 -/
theorem unsignedBorrowStep_gateOperators {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width) :
    (unsignedBorrowStepGates spec index).map
        (primitiveGateOperatorWithSymbols symbolValue) =
      (unsignedBorrowStepCompilerActions spec index).map
        deterministicOperator := by
  by_cases positive : 0 < index.val
  · simp [unsignedBorrowStepGates, unsignedBorrowStepCompilerActions, positive,
      primitiveXOperator_eq_deterministicOperator,
      primitiveToffoliOperator_eq_analyticToffoliOperator,
      analyticToffoliOperator]
  · simp [unsignedBorrowStepGates, unsignedBorrowStepCompilerActions, positive,
      primitiveXOperator_eq_deterministicOperator,
      primitiveToffoliOperator_eq_analyticToffoliOperator,
      analyticToffoliOperator]

set_option linter.unusedSimpArgs false in
/-- 1桁compiler action列のfoldは独立に定義したborrow-step作用である。 -/
theorem unsignedBorrowStepCompilerActions_fold {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width)
    (input : QubitBasis qubits) :
    (unsignedBorrowStepCompilerActions spec index).foldl
        (fun state action => action state) input =
      unsignedBorrowStepBasisAction spec index input := by
  by_cases positive : 0 < index.val
  · let previous := previousIndex index positive
    have lhsRhs := spec.lhsRhsDifferent index index
    have rhsLhs := Ne.symm lhsRhs
    have lhsPrevious := spec.lhsBorrowDifferent index previous
    have previousLhs := Ne.symm lhsPrevious
    have rhsPrevious := spec.rhsBorrowDifferent index previous
    have previousRhs := Ne.symm rhsPrevious
    have lhsOutput := spec.lhsBorrowDifferent index index
    have outputLhs := Ne.symm lhsOutput
    have rhsOutput := spec.rhsBorrowDifferent index index
    have outputRhs := Ne.symm rhsOutput
    have previousOutput := previousBorrowWire_ne_current spec index positive
    have outputPrevious := Ne.symm previousOutput
    funext wire
    by_cases wireLhs : wire = spec.lhs.wire index
    · subst wire
      cases lhsValue : input (spec.lhs.wire index) <;>
        cases rhsValue : input (spec.rhs.wire index) <;>
        cases previousValue : input (spec.borrow.wire previous) <;>
        cases outputValue : input (spec.borrow.wire index) <;>
        simp_all [unsignedBorrowStepCompilerActions, positive,
          unsignedBorrowStepBasisAction, previous, unsignedBorrowStep,
          xorWire, Function.update_apply, lhsValue, rhsValue, previousValue,
          outputValue, spec.lhsBorrowDifferent index index,
          spec.lhsBorrowDifferent index previous,
          spec.lhsRhsDifferent index index]
    · by_cases wireRhs : wire = spec.rhs.wire index
      · subst wire
        cases lhsValue : input (spec.lhs.wire index) <;>
          cases rhsValue : input (spec.rhs.wire index) <;>
          cases previousValue : input (spec.borrow.wire previous) <;>
          cases outputValue : input (spec.borrow.wire index) <;>
          simp_all [unsignedBorrowStepCompilerActions, positive,
            unsignedBorrowStepBasisAction, previous, unsignedBorrowStep,
            xorWire, Function.update_apply, lhsValue, rhsValue, previousValue,
            outputValue, spec.lhsRhsDifferent index index,
            spec.rhsBorrowDifferent index index,
            spec.rhsBorrowDifferent index previous,
            Ne.symm (spec.lhsRhsDifferent index index)]
      · by_cases wirePrevious : wire = spec.borrow.wire previous
        · subst wire
          cases lhsValue : input (spec.lhs.wire index) <;>
            cases rhsValue : input (spec.rhs.wire index) <;>
            cases previousValue : input (spec.borrow.wire previous) <;>
            cases outputValue : input (spec.borrow.wire index) <;>
            simp_all [unsignedBorrowStepCompilerActions, positive,
              unsignedBorrowStepBasisAction, previous, unsignedBorrowStep,
              xorWire, Function.update_apply, lhsValue, rhsValue, previousValue,
              outputValue, previousBorrowWire_ne_current spec index positive,
              spec.lhsBorrowDifferent index previous,
              spec.rhsBorrowDifferent index previous]
        · by_cases wireOutput : wire = spec.borrow.wire index
          · subst wire
            cases lhsValue : input (spec.lhs.wire index) <;>
              cases rhsValue : input (spec.rhs.wire index) <;>
              cases previousValue : input (spec.borrow.wire previous) <;>
              cases outputValue : input (spec.borrow.wire index) <;>
              simp_all [unsignedBorrowStepCompilerActions, positive,
                unsignedBorrowStepBasisAction, previous, unsignedBorrowStep,
                xorWire, Function.update_apply, lhsValue, rhsValue,
                previousValue, outputValue,
                previousBorrowWire_ne_current spec index positive,
                spec.lhsBorrowDifferent index index,
                spec.rhsBorrowDifferent index index]
          · simp_all [unsignedBorrowStepCompilerActions, positive,
              unsignedBorrowStepBasisAction, previous, unsignedBorrowStep,
              xorWire, Function.update_apply, wireLhs, wireRhs, wirePrevious,
              wireOutput]
  · have lhsRhs := spec.lhsRhsDifferent index index
    have rhsLhs := Ne.symm lhsRhs
    have lhsOutput := spec.lhsBorrowDifferent index index
    have outputLhs := Ne.symm lhsOutput
    have rhsOutput := spec.rhsBorrowDifferent index index
    have outputRhs := Ne.symm rhsOutput
    funext wire
    by_cases wireLhs : wire = spec.lhs.wire index
    · subst wire
      cases lhsValue : input (spec.lhs.wire index) <;>
        cases rhsValue : input (spec.rhs.wire index) <;>
        cases outputValue : input (spec.borrow.wire index) <;>
        simp_all [unsignedBorrowStepCompilerActions, positive,
          unsignedBorrowStepBasisAction, unsignedBorrowStep, xorWire,
          Function.update_apply, lhsValue, rhsValue, outputValue,
          spec.lhsBorrowDifferent index index,
          spec.lhsRhsDifferent index index]
    · by_cases wireRhs : wire = spec.rhs.wire index
      · subst wire
        cases lhsValue : input (spec.lhs.wire index) <;>
          cases rhsValue : input (spec.rhs.wire index) <;>
          cases outputValue : input (spec.borrow.wire index) <;>
          simp_all [unsignedBorrowStepCompilerActions, positive,
            unsignedBorrowStepBasisAction, unsignedBorrowStep, xorWire,
            Function.update_apply, lhsValue, rhsValue, outputValue,
            spec.lhsRhsDifferent index index,
            spec.rhsBorrowDifferent index index,
            Ne.symm (spec.lhsRhsDifferent index index)]
      · by_cases wireOutput : wire = spec.borrow.wire index
        · subst wire
          cases lhsValue : input (spec.lhs.wire index) <;>
            cases rhsValue : input (spec.rhs.wire index) <;>
            cases outputValue : input (spec.borrow.wire index) <;>
            simp_all [unsignedBorrowStepCompilerActions, positive,
              unsignedBorrowStepBasisAction, unsignedBorrowStep, xorWire,
              Function.update_apply, lhsValue, rhsValue, outputValue,
              spec.lhsBorrowDifferent index index,
              spec.rhsBorrowDifferent index index]
        · simp_all [unsignedBorrowStepCompilerActions, positive,
            unsignedBorrowStepBasisAction, unsignedBorrowStep, xorWire,
            Function.update_apply, wireLhs, wireRhs, wireOutput]

/-- 1桁borrow compilerは独立なborrow-step作用素targetに厳密一致する。 -/
theorem unsignedBorrowStepCircuit_correct {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (unsignedBorrowStepCircuit spec index) =
      deterministicOperator (unsignedBorrowStepBasisAction spec index) := by
  rw [unsignedBorrowStepCircuit,
    denote_gate_sequence_eq_operatorSequence,
    unsignedBorrowStep_gateOperators,
    operatorSequence_deterministicOperator]
  congr 1
  funext input
  exact unsignedBorrowStepCompilerActions_fold spec index input

/-
/-- borrow stepはlhs registerを保存する。 -/
@[simp] theorem unsignedBorrowStepBasisAction_lhs {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index lhsIndex : Fin width)
    (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index input (spec.lhs.wire lhsIndex) =
      input (spec.lhs.wire lhsIndex) := by
  simp [unsignedBorrowStepBasisAction, xorWire,
    spec.lhsBorrowDifferent lhsIndex index]

/-- borrow stepはrhs registerを保存する。 -/
@[simp] theorem unsignedBorrowStepBasisAction_rhs {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index rhsIndex : Fin width)
    (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index input (spec.rhs.wire rhsIndex) =
      input (spec.rhs.wire rhsIndex) := by
  simp [unsignedBorrowStepBasisAction, xorWire,
    spec.rhsBorrowDifferent rhsIndex index]

/-- borrow stepはcomparison targetを保存する。 -/
@[simp] theorem unsignedBorrowStepBasisAction_target {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width)
    (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index input spec.target =
      input spec.target := by
  simp [unsignedBorrowStepBasisAction, xorWire,
    spec.targetBorrowDifferent index]

/-- borrow stepは現在桁以外のborrow wireを保存する。 -/
@[simp] theorem unsignedBorrowStepBasisAction_otherBorrow {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index other : Fin width)
    (different : other ≠ index) (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index input (spec.borrow.wire other) =
      input (spec.borrow.wire other) := by
  have wireDifferent : spec.borrow.wire other ≠ spec.borrow.wire index :=
    fun equal => different (spec.borrow.injective equal)
  simp [unsignedBorrowStepBasisAction, xorWire, wireDifferent]

/-- 1桁borrow-stepは同じ作用を2回適用すると元へ戻る。 -/
theorem unsignedBorrowStepBasisAction_involutive {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (index : Fin width) :
    Function.Involutive (unsignedBorrowStepBasisAction spec index) := by
  intro input
  funext wire
  by_cases wireOutput : wire = spec.borrow.wire index
  · subst wire
    have lhsOutput := spec.lhsBorrowDifferent index index
    have outputLhs := Ne.symm lhsOutput
    have rhsOutput := spec.rhsBorrowDifferent index index
    have outputRhs := Ne.symm rhsOutput
    by_cases positive : 0 < index.val
    · let previous := previousIndex index positive
      have previousDifferent : previous ≠ index := by
        intro equal
        have valueEqual := congrArg Fin.val equal
        simp [previousIndex] at valueEqual
        omega
      have previousOutput := previousBorrowWire_ne_current spec index positive
      have outputPrevious := Ne.symm previousOutput
      cases lhsValue : input (spec.lhs.wire index) <;>
        cases rhsValue : input (spec.rhs.wire index) <;>
        cases previousValue : input (spec.borrow.wire previous) <;>
        cases outputValue : input (spec.borrow.wire index) <;>
        simp_all [unsignedBorrowStepBasisAction, positive, previous,
          unsignedBorrowStep, xorWire, lhsValue, rhsValue, previousValue,
          outputValue, previousDifferent]
    · cases lhsValue : input (spec.lhs.wire index) <;>
        cases rhsValue : input (spec.rhs.wire index) <;>
        cases outputValue : input (spec.borrow.wire index) <;>
        simp_all [unsignedBorrowStepBasisAction, positive, unsignedBorrowStep,
          xorWire, lhsValue, rhsValue, outputValue]
  · simp [unsignedBorrowStepBasisAction, xorWire, wireOutput]

/-- comparison targetのXORは各borrow-stepと可換である。 -/
theorem unsignedBorrowStepBasisAction_commutes_targetXor
    {qubits width : Nat} (spec : UnsignedLessThanXorSpec qubits width)
    (index : Fin width) (value : Bool) (input : QubitBasis qubits) :
    unsignedBorrowStepBasisAction spec index
        (xorWire spec.target value input) =
      xorWire spec.target value
        (unsignedBorrowStepBasisAction spec index input) := by
  have targetLhs := spec.targetLhsDifferent index
  have lhsTarget := Ne.symm targetLhs
  have targetRhs := spec.targetRhsDifferent index
  have rhsTarget := Ne.symm targetRhs
  have targetOutput := spec.targetBorrowDifferent index
  have outputTarget := Ne.symm targetOutput
  funext wire
  by_cases wireTarget : wire = spec.target
  · subst wire
    cases value <;> cases targetValue : input spec.target <;>
      simp_all [unsignedBorrowStepBasisAction, xorWire, targetValue,
        spec.targetLhsDifferent, spec.targetRhsDifferent,
        spec.targetBorrowDifferent]
  · by_cases wireOutput : wire = spec.borrow.wire index
    · subst wire
      by_cases positive : 0 < index.val
      · let previous := previousIndex index positive
        have targetPrevious := spec.targetBorrowDifferent previous
        have previousTarget := Ne.symm targetPrevious
        cases value <;>
          cases lhsValue : input (spec.lhs.wire index) <;>
          cases rhsValue : input (spec.rhs.wire index) <;>
          cases previousValue : input (spec.borrow.wire previous) <;>
          cases outputValue : input (spec.borrow.wire index) <;>
          simp_all [unsignedBorrowStepBasisAction, positive, previous,
            unsignedBorrowStep, xorWire, lhsValue, rhsValue, previousValue,
            outputValue, spec.targetLhsDifferent,
            spec.targetRhsDifferent, spec.targetBorrowDifferent]
      · cases value <;>
          cases lhsValue : input (spec.lhs.wire index) <;>
          cases rhsValue : input (spec.rhs.wire index) <;>
          cases outputValue : input (spec.borrow.wire index) <;>
          simp_all [unsignedBorrowStepBasisAction, positive, unsignedBorrowStep,
            xorWire, lhsValue, rhsValue, outputValue,
            spec.targetLhsDifferent, spec.targetRhsDifferent,
            spec.targetBorrowDifferent]
    · simp_all [unsignedBorrowStepBasisAction, xorWire, wireTarget, wireOutput]

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
      simp only [List.foldl]
      rw [inductionHypothesis]
      · exact involutive first (by simp) input
      · intro action member
        exact involutive action (by simp [member])

-/
/-- 全桁を下位bitから計算するsame-width ripple-borrow回路。 -/
def unsignedBorrowComputeCircuit {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.sequence <|
    (List.finRange width).map (unsignedBorrowStepCircuit spec)

/-- 最終borrowをtargetへXORするuse回路。 -/
def unsignedLessThanUseCircuit {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    Circuit (PrimitiveGate qubits) :=
  .gate (.cnot
    (spec.borrow.wire ⟨width - 1,
      Nat.sub_lt spec.widthPositive Nat.zero_lt_one⟩)
    spec.target (Ne.symm (spec.targetBorrowDifferent _)))

/-- compute-use-uncomputeでunsigned less-thanをtargetへXORする正本AST。 -/
def unsignedLessThanXorCircuit {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    Circuit (PrimitiveGate qubits) :=
  Circuit.computeUseUncompute PrimitiveGate.inverse
    (unsignedBorrowComputeCircuit spec) (unsignedLessThanUseCircuit spec)

/-- 全桁borrow compute回路はpure step familyのfold作用素に厳密一致する。 -/
theorem unsignedBorrowComputeCircuit_correct {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : UnsignedLessThanXorSpec qubits width) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (unsignedBorrowComputeCircuit spec) =
      unsignedBorrowComputeOperator spec := by
  rw [unsignedBorrowComputeCircuit,
    Circuit.denote_sequence_eq_operatorSequence]
  simp only [List.map_map, Function.comp_def]
  rw [show
      (List.map
        (fun index => Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (unsignedBorrowStepCircuit spec index))
        (List.finRange width)) =
      (List.map
        (fun index => deterministicOperator
          (unsignedBorrowStepBasisAction spec index))
        (List.finRange width)) by
    apply List.map_congr_left
    intro index indexMembership
    exact unsignedBorrowStepCircuit_correct symbolValue spec index]
  rw [show
      (List.map
        (fun index => deterministicOperator
          (unsignedBorrowStepBasisAction spec index))
        (List.finRange width)) =
      (List.map (fun index => unsignedBorrowStepBasisAction spec index)
        (List.finRange width)).map deterministicOperator by
    simp [List.map_map, Function.comp_def]]
  rw [operatorSequence_deterministicOperator]
  unfold unsignedBorrowComputeOperator unsignedBorrowComputeBasisAction
  congr 1
  funext input
  simp [List.foldl_map]

/-- 最終borrow CNOT use回路は独立なtarget-XOR作用素に厳密一致する。 -/
theorem unsignedLessThanUseCircuit_correct {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : UnsignedLessThanXorSpec qubits width) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (unsignedLessThanUseCircuit spec) =
      unsignedLessThanUseOperator spec := rfl

/-- same-width ripple-borrow ASTはdirty全入力上の独立strict operator targetに一致する。 -/
theorem unsignedLessThanXorCircuit_correct {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : UnsignedLessThanXorSpec qubits width) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (unsignedLessThanXorCircuit spec) =
      unsignedLessThanXorDirtyOperator spec := by
  unfold unsignedLessThanXorCircuit Circuit.computeUseUncompute
    unsignedLessThanXorDirtyOperator
  simp only [Circuit.denote_seq]
  rw [Circuit.denote_reverse PrimitiveGate.inverse
    (primitiveGateOperatorWithSymbols symbolValue)
    (primitiveGateOperatorWithSymbols_inverse symbolValue),
    unsignedBorrowComputeCircuit_correct,
    unsignedLessThanUseCircuit_correct]

/-- dirty全入力上のfull operator等式を公開するstrict compiler component。 -/
def unsignedLessThanXorExactComponent {qubits width : Nat}
    (symbolValue : String → ℝ)
    (spec : UnsignedLessThanXorSpec qubits width) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := unsignedLessThanXorCircuit spec
  target := unsignedLessThanXorDirtyOperator spec
  correct := unsignedLessThanXorCircuit_correct symbolValue spec

end

end VerifiedCircuitCore
