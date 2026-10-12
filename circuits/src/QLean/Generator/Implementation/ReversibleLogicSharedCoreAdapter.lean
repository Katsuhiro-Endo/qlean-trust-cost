import QLean.Generator.Analysis.ValidatedReversibleLogicLayouts
import QLean.Generator.Analysis.TotalReversiblePrograms
import QLean.Generator.Implementation.CoreCircuitEmbedding
import QLean.Generator.Implementation.ReversibleArithmetic
import QLean.Circuits.Foundation.ReversibleLogic

/-!
# 共有 reversible logic と凍結Q基本gate列のadapter

正常な同幅・disjoint layoutだけを受け取り、共有core componentのgate列と凍結Q正本の
gate列が一致することを証明する。任意List長やwire衝突時退避はこの公開adapterの仕様に
含めない。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- Q reversible gateを標準幅の共有core primitive gateへ写す。 -/
def reversibleGateToCanonicalCore {ancillaQubits systemQubits : Nat} :
    ReversibleGate ancillaQubits systemQubits →
      VerifiedCircuitCore.PrimitiveGate (ancillaQubits + systemQubits)
  | .x target =>
      .x (analyticCanonicalWireEquiv ancillaQubits systemQubits target)
  | .cnot control target different =>
      .cnot (analyticCanonicalWireEquiv ancillaQubits systemQubits control)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits target)
        (fun equal => different
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))
  | .toffoli control₁ control₂ target controlsDifferent firstDifferent
      secondDifferent =>
      .toffoli (analyticCanonicalWireEquiv ancillaQubits systemQubits control₁)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits control₂)
        (analyticCanonicalWireEquiv ancillaQubits systemQubits target)
        (fun equal => controlsDifferent
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))
        (fun equal => firstDifferent
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))
        (fun equal => secondDifferent
          ((analyticCanonicalWireEquiv ancillaQubits systemQubits).injective equal))

/-- Both Q gate conversion paths induce the same canonical core primitive gate. -/
theorem primitiveGateToCanonicalCore_comp_toPrimitive
    {ancillaQubits systemQubits : Nat} :
    PrimitiveGate.toCanonicalCore ∘ ReversibleGate.toPrimitive =
      (reversibleGateToCanonicalCore :
        ReversibleGate ancillaQubits systemQubits →
          VerifiedCircuitCore.PrimitiveGate (ancillaQubits + systemQubits)) := by
  funext gate
  cases gate <;> rfl

/-- Q reversible circuitを標準幅の共有core primitive circuitへ写す。 -/
def compileReversibleCircuitToCanonicalCore
    {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (ReversibleGate ancillaQubits systemQubits)) :
    VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate (ancillaQubits + systemQubits)) :=
  circuit.mapGates reversibleGateToCanonicalCore

/-- compilerはreversible gate列の順序と個数を変えない。 -/
theorem compileReversibleCircuitToCanonicalCore_flatten
    {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (ReversibleGate ancillaQubits systemQubits)) :
    (compileReversibleCircuitToCanonicalCore circuit).flatten =
      circuit.flatten.map reversibleGateToCanonicalCore :=
  VerifiedCircuitCore.Circuit.flatten_mapGates _ circuit

/-- 検証済みcopy layoutのQ CNOT列。 -/
def validatedRegisterXorCopyQGates
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width) :
    List (ReversibleGate ancillaQubits systemQubits) :=
  (List.finRange width).map fun index =>
    .cnot (layout.source.wire index) (layout.target.wire index)
      (layout.disjoint index index)

private theorem validatedRegisterXorCopy_flatten_indices
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width)
    (indices : List (Fin width)) :
    (ReversibleCircuit.xorCopy
      (indices.map layout.source.wire)
      (indices.map layout.target.wire)).flatten =
      indices.map fun index =>
        .cnot (layout.source.wire index) (layout.target.wire index)
          (layout.disjoint index index) := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp only [List.map_cons, ReversibleCircuit.xorCopy,
        VerifiedCircuitCore.Circuit.flatten]
      rw [ReversibleCircuit.safeCnot,
        dif_pos (layout.disjoint index index)]
      simp only [VerifiedCircuitCore.Circuit.flatten, inductionHypothesis]
      rfl

/-- 正常layoutでは旧total copyのflattenが検証済みCNOT列になる。 -/
theorem validatedRegisterXorCopy_flatten
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width) :
    (ReversibleCircuit.xorCopy layout.source.wires layout.target.wires).flatten =
      validatedRegisterXorCopyQGates layout := by
  exact validatedRegisterXorCopy_flatten_indices layout (List.finRange width)

/-- 検証済みcopyの凍結Q gate列は共有core strict compilerのgate列と一致する。 -/
theorem validatedRegisterXorCopy_compile_flatten
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width) :
    (compileReversibleCircuitToCanonicalCore
      (ReversibleCircuit.xorCopy layout.source.wires layout.target.wires)).flatten =
      (VerifiedCircuitCore.registerXorCopyCircuit layout.toCore).flatten := by
  rw [compileReversibleCircuitToCanonicalCore_flatten,
    validatedRegisterXorCopy_flatten]
  rw [VerifiedCircuitCore.registerXorCopyCircuit]
  rw [VerifiedCircuitCore.Circuit.flatten_sequence_map_gate]
  simp [validatedRegisterXorCopyQGates,
    VerifiedCircuitCore.registerXorCopyGates,
    ValidatedRegisterXorCopyLayout.toCore,
    ValidatedQRegister.toCore,
    reversibleGateToCanonicalCore]

/--
検証済みcopy layoutについて、凍結Q compiler ASTを共有coreの独立copy targetへ結ぶExact部品。
親証明はflatten transportと共有componentの`correct` fieldだけを使用する。
-/
def validatedXorSourceRegisterIntoTargetFrozenCompilerExactComponent
    {ancillaQubits systemQubits width : Nat}
    (symbolValue : String → ℝ)
    (layout : ValidatedRegisterXorCopyLayout
      ancillaQubits systemQubits width) :
    VerifiedCircuitCore.ExactOperatorComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := ancillaQubits + systemQubits) symbolValue) where
  circuit := compileReversibleCircuitToCanonicalCore
    (ReversibleCircuit.xorCopy layout.source.wires layout.target.wires)
  target := (VerifiedCircuitCore.registerXorCopyComponent
    (qubits := ancillaQubits + systemQubits) (width := width)
    symbolValue layout.toCore).target
  correct := calc
    VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
          (qubits := ancillaQubits + systemQubits) symbolValue)
        (compileReversibleCircuitToCanonicalCore
          (ReversibleCircuit.xorCopy
            layout.source.wires layout.target.wires)) =
      VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
          (qubits := ancillaQubits + systemQubits) symbolValue)
        (VerifiedCircuitCore.registerXorCopyCircuit layout.toCore) :=
      VerifiedCircuitCore.Circuit.denote_eq_of_flatten
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
          (qubits := ancillaQubits + systemQubits) symbolValue) _ _
        (validatedRegisterXorCopy_compile_flatten layout)
    _ = (VerifiedCircuitCore.registerXorCopyComponent
        (qubits := ancillaQubits + systemQubits) (width := width)
        symbolValue layout.toCore).target :=
      (VerifiedCircuitCore.registerXorCopyComponent
        (qubits := ancillaQubits + systemQubits) (width := width)
        symbolValue layout.toCore).correct

/-- 検証済みcontrolled swap layoutのQ側Fredkin gate列。 -/
def validatedControlledRegisterSwapQGates
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width) :
    List (ReversibleGate ancillaQubits systemQubits) :=
  (List.finRange width).flatMap fun index => [
    .cnot (layout.left.wire index) (layout.right.wire index)
      (layout.leftRightDisjoint index index),
    .toffoli layout.control (layout.right.wire index)
      (layout.left.wire index)
      (layout.controlRightDifferent index)
      (layout.controlLeftDifferent index)
      (Ne.symm (layout.leftRightDisjoint index index)),
    .cnot (layout.left.wire index) (layout.right.wire index)
      (layout.leftRightDisjoint index index)
  ]

private theorem validatedControlledRegisterSwap_flatten_indices
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width)
    (indices : List (Fin width)) :
    (ReversibleCircuit.controlledSwapWord layout.control
      (indices.map layout.left.wire)
      (indices.map layout.right.wire)).flatten =
      indices.flatMap fun index => [
        .cnot (layout.left.wire index) (layout.right.wire index)
          (layout.leftRightDisjoint index index),
        .toffoli layout.control (layout.right.wire index)
          (layout.left.wire index)
          (layout.controlRightDifferent index)
          (layout.controlLeftDifferent index)
          (Ne.symm (layout.leftRightDisjoint index index)),
        .cnot (layout.left.wire index) (layout.right.wire index)
          (layout.leftRightDisjoint index index)
      ] := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      rw [List.flatMap_cons]
      change
        (ReversibleCircuit.controlledSwapBit layout.control
          (layout.left.wire index) (layout.right.wire index)).flatten ++
            (ReversibleCircuit.controlledSwapWord layout.control
              (rest.map layout.left.wire)
              (rest.map layout.right.wire)).flatten = _
      rw [inductionHypothesis]
      congr 1
      simp [ReversibleCircuit.controlledSwapBit,
        ReversibleCircuit.safeCnot, ReversibleCircuit.safeToffoli,
        VerifiedCircuitCore.Circuit.flatten,
        layout.leftRightDisjoint index index,
        Ne.symm (layout.leftRightDisjoint index index),
        layout.controlLeftDifferent index,
        layout.controlRightDifferent index]

/-- 正常layoutでは旧total controlled swapのflattenが検証済みFredkin列になる。 -/
theorem validatedControlledRegisterSwap_flatten
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width) :
    (ReversibleCircuit.controlledSwapWord layout.control
      layout.left.wires layout.right.wires).flatten =
      validatedControlledRegisterSwapQGates layout := by
  exact validatedControlledRegisterSwap_flatten_indices layout
    (List.finRange width)

/-- 正常layoutのQ controlled swapと共有core strict compilerは同じgate列を持つ。 -/
theorem validatedControlledRegisterSwap_compile_flatten
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width) :
    (compileReversibleCircuitToCanonicalCore
      (ReversibleCircuit.controlledSwapWord layout.control
        layout.left.wires layout.right.wires)).flatten =
      (VerifiedCircuitCore.controlledRegisterSwapCircuit layout.toCore).flatten := by
  rw [compileReversibleCircuitToCanonicalCore_flatten,
    validatedControlledRegisterSwap_flatten]
  rw [VerifiedCircuitCore.controlledRegisterSwapCircuit]
  rw [VerifiedCircuitCore.Circuit.flatten_sequence_map_gate]
  simp [validatedControlledRegisterSwapQGates,
    VerifiedCircuitCore.controlledRegisterSwapGates,
    VerifiedCircuitCore.fredkinGates,
    List.map_flatMap,
    ValidatedControlledRegisterSwapLayout.toCore,
    ValidatedQRegister.toCore,
    reversibleGateToCanonicalCore]

/-- The Q controlled-swap word adapter enumerates exactly the validated
register indices used by the shared pure specification. -/
theorem controlledSwapWordCore_eq_validatedIndexSequence
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width) :
    TotalReversibleStage.controlledSwapWordCore layout.control
        layout.left.wires layout.right.wires =
      VerifiedCircuitCore.ClassicalReversibleStage.sequence
        ((List.finRange width).map fun index =>
          TotalReversibleStage.controlledSwapBitCore layout.control
            (layout.left.wire index) (layout.right.wire index)) := by
  have zipped :
      ((List.finRange width).map layout.left.wire).zip
          ((List.finRange width).map layout.right.wire) =
        (List.finRange width).map fun index =>
          (layout.left.wire index, layout.right.wire index) := by
    induction List.finRange width with
    | nil => rfl
    | cons first rest inductionHypothesis =>
        simp [inductionHypothesis]
  unfold TotalReversibleStage.controlledSwapWordCore
    ValidatedQRegister.wires
  rw [zipped, List.map_map]
  rfl

/-- One validated Q swap-bit stage has the shared pure Fredkin operator. -/
theorem controlledSwapBitCore_analyticOperator_eq_fredkin
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width) (index : Fin width) :
    (TotalReversibleStage.controlledSwapBitCore layout.control
      (layout.left.wire index) (layout.right.wire index)).analyticOperator =
      VerifiedCircuitCore.analyticFredkinOperator layout.toCore.control
        (layout.toCore.left.wire index) (layout.toCore.right.wire index) := by
  change (TotalReversibleStage.controlledSwapBitCore layout.control
      (layout.left.wire index) (layout.right.wire index)).analyticOperator =
    VerifiedCircuitCore.analyticFredkinOperator
      (analyticCanonicalWireEquiv ancillaQubits systemQubits layout.control)
      (analyticCanonicalWireEquiv ancillaQubits systemQubits
        (layout.left.wire index))
      (analyticCanonicalWireEquiv ancillaQubits systemQubits
        (layout.right.wire index))
  have leftRight :
      analyticCanonicalWireEquiv ancillaQubits systemQubits
          (layout.left.wire index) ≠
        analyticCanonicalWireEquiv ancillaQubits systemQubits
          (layout.right.wire index) :=
    (analyticCanonicalWireEquiv ancillaQubits systemQubits).injective.ne
      (layout.leftRightDisjoint index index)
  have controlLeft :
      analyticCanonicalWireEquiv ancillaQubits systemQubits layout.control ≠
        analyticCanonicalWireEquiv ancillaQubits systemQubits
          (layout.left.wire index) :=
    (analyticCanonicalWireEquiv ancillaQubits systemQubits).injective.ne
      (layout.controlLeftDifferent index)
  have controlRight :
      analyticCanonicalWireEquiv ancillaQubits systemQubits layout.control ≠
        analyticCanonicalWireEquiv ancillaQubits systemQubits
          (layout.right.wire index) :=
    (analyticCanonicalWireEquiv ancillaQubits systemQubits).injective.ne
      (layout.controlRightDifferent index)
  unfold TotalReversibleStage.controlledSwapBitCore
  simp only [VerifiedCircuitCore.ClassicalReversibleStage.safeXorControlled,
    VerifiedCircuitCore.ClassicalReversibleStage.safeXorDoublyControlled,
    dif_pos leftRight, dif_pos controlRight, dif_pos controlLeft,
    dif_pos (Ne.symm leftRight)]
  rw [VerifiedCircuitCore.ClassicalReversibleStage.analyticOperator_seq,
    VerifiedCircuitCore.ClassicalReversibleStage.analyticOperator_seq]
  simp only [VerifiedCircuitCore.ClassicalReversibleStage.analyticOperator_eq_deterministicReference]
  rfl

/-- A validated Q controlled-swap word has exactly the shared independent
controlled-register-swap target. -/
theorem controlledSwapWordCore_analyticOperator_eq_pure
    {ancillaQubits systemQubits width : Nat}
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width) :
    (TotalReversibleStage.controlledSwapWordCore layout.control
      layout.left.wires layout.right.wires).analyticOperator =
      VerifiedCircuitCore.controlledRegisterSwapPureOperator layout.toCore := by
  rw [controlledSwapWordCore_eq_validatedIndexSequence,
    VerifiedCircuitCore.ClassicalReversibleStage.analyticOperator_sequence]
  rw [List.map_map]
  have mapped :
      (List.finRange width).map
          (VerifiedCircuitCore.ClassicalReversibleStage.analyticOperator ∘
            fun index =>
              TotalReversibleStage.controlledSwapBitCore layout.control
                (layout.left.wire index) (layout.right.wire index)) =
        (List.finRange width).map
          (fun index => VerifiedCircuitCore.analyticFredkinOperator
            layout.toCore.control (layout.toCore.left.wire index)
              (layout.toCore.right.wire index)) := by
    apply List.map_congr_left
    intro index _
    simpa only [Function.comp_apply] using
      controlledSwapBitCore_analyticOperator_eq_fredkin layout index
  rw [mapped]
  exact VerifiedCircuitCore.controlledRegisterSwapAnalyticOperator_eq_pure
    layout.toCore

/--
検証済みcontrolled-swap layoutについて、凍結Q compiler ASTを共有coreの独立swap targetへ
結ぶExact部品。親証明はflatten transportと共有componentの`correct` fieldだけを使用する。
-/
def validatedSwapRegistersWhenControlFrozenCompilerExactComponent
    {ancillaQubits systemQubits width : Nat}
    (symbolValue : String → ℝ)
    (layout : ValidatedControlledRegisterSwapLayout
      ancillaQubits systemQubits width) :
    VerifiedCircuitCore.ExactOperatorComponent
      (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
        (qubits := ancillaQubits + systemQubits) symbolValue) where
  circuit := compileReversibleCircuitToCanonicalCore
    (ReversibleCircuit.controlledSwapWord layout.control
      layout.left.wires layout.right.wires)
  target := (VerifiedCircuitCore.controlledRegisterSwapComponent
    (qubits := ancillaQubits + systemQubits) (width := width)
    symbolValue layout.toCore).target
  correct := calc
    VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
          (qubits := ancillaQubits + systemQubits) symbolValue)
        (compileReversibleCircuitToCanonicalCore
          (ReversibleCircuit.controlledSwapWord layout.control
            layout.left.wires layout.right.wires)) =
      VerifiedCircuitCore.Circuit.denote
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
          (qubits := ancillaQubits + systemQubits) symbolValue)
        (VerifiedCircuitCore.controlledRegisterSwapCircuit layout.toCore) :=
      VerifiedCircuitCore.Circuit.denote_eq_of_flatten
        (VerifiedCircuitCore.primitiveGateOperatorWithSymbols
          (qubits := ancillaQubits + systemQubits) symbolValue) _ _
        (validatedControlledRegisterSwap_compile_flatten layout)
    _ = (VerifiedCircuitCore.controlledRegisterSwapComponent
        (qubits := ancillaQubits + systemQubits) (width := width)
        symbolValue layout.toCore).target :=
      (VerifiedCircuitCore.controlledRegisterSwapComponent
        (qubits := ancillaQubits + systemQubits) (width := width)
        symbolValue layout.toCore).correct

end

end ProbabilityGeneratorQProof
