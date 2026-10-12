import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.WireEmbeddingAnalytic
import QLean.Circuits.Foundation.PhaseShiftMacros
import QLean.Circuits.Foundation.ControlledRotationMacros
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2

/-!
# injective wire 埋込みの回路意味論とcomponent lift

基本gateをinjectiveなwire配置へ写した回路が、回路非依存な`wireLiftOperator`を
厳密に実装することを証明する。巨大行列は展開せず、局所gateの行列要素補題と
Kronecker積・reindexの一般代数則だけを用いる。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- mapped single wire以外の一致を、内部一致と外部一致へ分解する。 -/
theorem agreesExcept_mapWires_iff {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (target : Fin sourceQubits)
    (output input : QubitBasis targetQubits) :
    agreesExcept (placement target) output input ↔
      agreesExcept target
          (restrictToPlacedWires placement output)
          (restrictToPlacedWires placement input) ∧
        restrictToOutsideWires placement output =
          restrictToOutsideWires placement input := by
  constructor
  · intro agrees
    constructor
    · intro wire different
      exact agrees (placement wire) (fun equal =>
        different (placement.injective equal))
    · funext wire
      exact agrees wire.1 (fun equal => wire.2 target equal.symm)
  · rintro ⟨internalAgrees, outsideAgrees⟩ wire different
    by_cases inside : ∃ source, placement source = wire
    · let source := Classical.choose inside
      have sourceAt : placement source = wire := Classical.choose_spec inside
      have sourceDifferent : source ≠ target := by
        intro equal
        apply different
        exact sourceAt.symm.trans (congrArg placement equal)
      simpa [restrictToPlacedWires, sourceAt] using
        internalAgrees source sourceDifferent
    · let outside : OutsideWire placement :=
        ⟨wire, fun source equal => inside ⟨source, equal⟩⟩
      exact congrFun outsideAgrees outside

/-- mapped two wires以外の一致を、内部一致と外部一致へ分解する。 -/
theorem agreesExceptTwo_mapWires_iff {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (first second : Fin sourceQubits)
    (output input : QubitBasis targetQubits) :
    agreesExceptTwo (placement first) (placement second) output input ↔
      agreesExceptTwo first second
          (restrictToPlacedWires placement output)
          (restrictToPlacedWires placement input) ∧
        restrictToOutsideWires placement output =
          restrictToOutsideWires placement input := by
  constructor
  · intro agrees
    constructor
    · intro wire firstDifferent secondDifferent
      exact agrees (placement wire)
        (fun equal => firstDifferent (placement.injective equal))
        (fun equal => secondDifferent (placement.injective equal))
    · funext wire
      exact agrees wire.1
        (fun equal => wire.2 first equal.symm)
        (fun equal => wire.2 second equal.symm)
  · rintro ⟨internalAgrees, outsideAgrees⟩ wire firstDifferent secondDifferent
    by_cases inside : ∃ source, placement source = wire
    · let source := Classical.choose inside
      have sourceAt : placement source = wire := Classical.choose_spec inside
      have sourceFirstDifferent : source ≠ first := by
        intro equal
        apply firstDifferent
        exact sourceAt.symm.trans (congrArg placement equal)
      have sourceSecondDifferent : source ≠ second := by
        intro equal
        apply secondDifferent
        exact sourceAt.symm.trans (congrArg placement equal)
      simpa [restrictToPlacedWires, sourceAt] using
        internalAgrees source sourceFirstDifferent sourceSecondDifferent
    · let outside : OutsideWire placement :=
        ⟨wire, fun source equal => inside ⟨source, equal⟩⟩
      exact congrFun outsideAgrees outside

/-- 一量子ビット局所作用素のwire-liftはmapped wireへの局所埋込みと一致する。 -/
theorem wireLiftOperator_embedSingleQubitOperator
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (target : Fin sourceQubits) (localOperator : Matrix Bool Bool ℂ) :
    wireLiftOperator placement (embedSingleQubitOperator target localOperator) =
      embedSingleQubitOperator (placement target) localOperator := by
  classical
  ext output input
  rw [wireLiftOperator_apply, embedSingleQubitOperator_apply,
    embedSingleQubitOperator_apply]
  have agreesIff := agreesExcept_mapWires_iff placement target output input
  by_cases internalAgrees : agreesExcept target
      (restrictToPlacedWires placement output)
      (restrictToPlacedWires placement input)
  · by_cases outsideAgrees : restrictToOutsideWires placement output =
        restrictToOutsideWires placement input
    · have mappedAgrees := agreesIff.2 ⟨internalAgrees, outsideAgrees⟩
      simp [internalAgrees, outsideAgrees, mappedAgrees, restrictToPlacedWires]
    · have mappedDifferent :
          ¬ agreesExcept (placement target) output input := by
        intro mappedAgrees
        exact outsideAgrees (agreesIff.1 mappedAgrees).2
      simp [internalAgrees, outsideAgrees, mappedDifferent]
  · have mappedDifferent : ¬ agreesExcept (placement target) output input := by
      intro mappedAgrees
      exact internalAgrees (agreesIff.1 mappedAgrees).1
    simp [internalAgrees, mappedDifferent]

/-- 二量子ビット局所作用素のwire-liftはmapped wiresへの局所埋込みと一致する。 -/
theorem wireLiftOperator_embedTwoQubitOperator
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (first second : Fin sourceQubits) (different : first ≠ second)
    (localOperator : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    wireLiftOperator placement
        (embedTwoQubitOperator first second different localOperator) =
      embedTwoQubitOperator (placement first) (placement second)
        (fun equal => different (placement.injective equal)) localOperator := by
  classical
  ext output input
  rw [wireLiftOperator_apply, embedTwoQubitOperator_apply,
    embedTwoQubitOperator_apply]
  have agreesIff :=
    agreesExceptTwo_mapWires_iff placement first second output input
  by_cases internalAgrees : agreesExceptTwo first second
      (restrictToPlacedWires placement output)
      (restrictToPlacedWires placement input)
  · by_cases outsideAgrees : restrictToOutsideWires placement output =
        restrictToOutsideWires placement input
    · have mappedAgrees := agreesIff.2 ⟨internalAgrees, outsideAgrees⟩
      simp [internalAgrees, outsideAgrees, mappedAgrees, restrictToPlacedWires]
    · have mappedDifferent :
          ¬ agreesExceptTwo (placement first) (placement second) output input := by
        intro mappedAgrees
        exact outsideAgrees (agreesIff.1 mappedAgrees).2
      simp [internalAgrees, outsideAgrees, mappedDifferent]
  · have mappedDifferent :
        ¬ agreesExceptTwo (placement first) (placement second) output input := by
      intro mappedAgrees
      exact internalAgrees (agreesIff.1 mappedAgrees).1
    simp [internalAgrees, mappedDifferent]

/-- 一個のprimitive gateのmapped意味論は解析的wire-liftに一致する。 -/
theorem primitiveGateOperatorWithSymbols_mapWires
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (placement : Fin sourceQubits ↪ Fin targetQubits) :
    ∀ gate : PrimitiveGate sourceQubits,
      primitiveGateOperatorWithSymbols symbolValue (gate.mapWires placement) =
        wireLiftOperator placement (primitiveGateOperatorWithSymbols symbolValue gate)
  | .x target =>
      (wireLiftOperator_embedSingleQubitOperator placement target localX).symm
  | .h target =>
      (wireLiftOperator_embedSingleQubitOperator placement target localH).symm
  | .ry angle target =>
      (wireLiftOperator_embedSingleQubitOperator placement target
        (localRy (angle.eval symbolValue))).symm
  | .phaseShift angle target =>
      (wireLiftOperator_embedSingleQubitOperator placement target
        (localPhaseShift (angle.eval symbolValue))).symm
  | .cnot control target different => by
      change deterministicOperator
          (fun input => xorWire (placement target)
            (input (placement control)) input) =
        wireLiftOperator placement
          (deterministicOperator
            (fun input => xorWire target (input control) input))
      rw [wireLiftOperator_deterministic]
      congr 1
      funext input
      simpa [restrictToPlacedWires] using
        (liftBasisAction_xorWire placement target
          (fun internal => internal control) input).symm
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent => by
      change deterministicOperator
          (fun input => xorWire (placement target)
            (input (placement control₀) && input (placement control₁)) input) =
        wireLiftOperator placement
          (deterministicOperator
            (fun input => xorWire target
              (input control₀ && input control₁) input))
      rw [wireLiftOperator_deterministic]
      congr 1
      funext input
      simpa [restrictToPlacedWires] using
        (liftBasisAction_xorWire placement target
          (fun internal => internal control₀ && internal control₁) input).symm

/-- primitive回路をmapped wiresへ移したdenotationは全回路のwire-liftである。 -/
theorem denote_mapPrimitiveWires_eq_wireLiftOperator
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (placement : Fin sourceQubits ↪ Fin targetQubits) :
    ∀ circuit : Circuit (PrimitiveGate sourceQubits),
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (circuit.mapGates (PrimitiveGate.mapWires placement)) =
        wireLiftOperator placement
          (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) circuit)
  | .identity => wireLiftOperator_one placement |>.symm
  | .gate gate => primitiveGateOperatorWithSymbols_mapWires symbolValue placement gate
  | .seq first second => by
      rw [Circuit.mapGates, Circuit.denote_seq,
        denote_mapPrimitiveWires_eq_wireLiftOperator symbolValue placement first,
        denote_mapPrimitiveWires_eq_wireLiftOperator symbolValue placement second,
        Circuit.denote_seq, wireLiftOperator_mul]
  | .repeat count body => by
      rw [Circuit.mapGates, Circuit.denote_repeat,
        denote_mapPrimitiveWires_eq_wireLiftOperator symbolValue placement body,
        Circuit.denote_repeat, wireLiftOperator_pow]

namespace ExactOperatorComponent

/-- primitive厳密componentをinjective wire配置へ解析targetごと持ち上げる。 -/
def mapPrimitiveWires {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue)) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) where
  circuit := component.circuit.mapGates (PrimitiveGate.mapWires placement)
  target := wireLiftOperator placement component.target
  correct := by
    rw [denote_mapPrimitiveWires_eq_wireLiftOperator]
    exact congrArg (wireLiftOperator placement) component.correct

end ExactOperatorComponent

/-- 指定外部基底以外には振幅を持たない状態全体のcoherent部分空間。 -/
def fixedOutsideStateSubspace {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool) :
    Submodule ℂ (State (QubitBasis targetQubits)) where
  carrier := {state | ∀ basis,
    restrictToOutsideWires placement basis ≠ outside → state basis = 0}
  zero_mem' basis _ := rfl
  add_mem' {left right} leftInside rightInside basis different := by
    simp [leftInside basis different, rightInside basis different]
  smul_mem' scalar state stateInside basis different := by
    simp [stateInside basis different]

/-- 固定外部基底の計算基底ketは対応するcoherent部分空間に属する。 -/
theorem basisKet_mem_fixedOutsideStateSubspace
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (internal : QubitBasis sourceQubits) :
    basisKet (fixedOutsideBasisEmbedding placement outside internal) ∈
      fixedOutsideStateSubspace placement outside := by
  intro basis different
  unfold basisKet
  rw [VerifiedMath.Basis.vector_apply]
  split
  next equal =>
    subst basis
    exact False.elim (different
      (fixedOutsideBasisEmbedding_hasFixedOutsideBasis placement outside internal))
  next _ => rfl

/-- 任意の内部作用素のwire-liftは各固定外部基底部分空間を保存する。 -/
theorem wireLiftOperator_preserves_fixedOutsideStateSubspace
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (operator : Operator (QubitBasis sourceQubits))
    (state : State (QubitBasis targetQubits))
    (stateInside : state ∈ fixedOutsideStateSubspace placement outside) :
    applyOperator (wireLiftOperator placement operator) state ∈
      fixedOutsideStateSubspace placement outside := by
  intro output outputDifferent
  unfold applyOperator Matrix.mulVec dotProduct
  apply Finset.sum_eq_zero
  intro input _
  change wireLiftOperator placement operator output input * state input = 0
  by_cases inputOutside :
      restrictToOutsideWires placement input = outside
  · have outsideDifferent :
        restrictToOutsideWires placement output ≠
          restrictToOutsideWires placement input := by
      intro equal
      exact outputDifferent (equal.trans inputOutside)
    rw [wireLiftOperator_apply]
    simp [outsideDifferent]
  · rw [stateInside input inputOutside]
    simp

/-- mapped回路の固定外部基底blockは元回路の全行列要素と厳密一致する。 -/
theorem denote_mapPrimitiveWires_fixedOutsideBlock
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (circuit : Circuit (PrimitiveGate sourceQubits))
    (output input : QubitBasis sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (circuit.mapGates (PrimitiveGate.mapWires placement))
        (fixedOutsideBasisEmbedding placement outside output)
        (fixedOutsideBasisEmbedding placement outside input) =
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) circuit output input := by
  rw [denote_mapPrimitiveWires_eq_wireLiftOperator,
    wireLiftOperator_apply]
  simp [fixedOutsideBasisEmbedding]

/-- wire-lift作用素を固定外部基底ketへ作用させると、内部作用後の状態埋込みになる。 -/
theorem applyOperator_wireLiftOperator_fixedOutsideBasisKet
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (operator : Operator (QubitBasis sourceQubits))
    (input : QubitBasis sourceQubits) :
    applyOperator (wireLiftOperator placement operator)
        (basisKet (fixedOutsideBasisEmbedding placement outside input)) =
      fixedOutsideStateEmbedding placement outside
        (applyOperator operator (basisKet input)) := by
  funext output
  rw [applyOperator_basisKet, wireLiftOperator_apply]
  simp [fixedOutsideBasisEmbedding, fixedOutsideStateEmbedding]

namespace StatePreparationComponent

/--
計算基底ketから始まる状態準備componentをinjectiveなwire配置へ写し、
外部wireを指定計算基底に固定した全幅状態準備componentを得る。
-/
def mapPrimitiveWiresAtFixedOutsideBasis
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (initialBasis : QubitBasis sourceQubits)
    (component : StatePreparationComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (initialState_eq : component.initialState = basisKet initialBasis) :
    StatePreparationComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) where
  circuit := component.circuit.mapGates (PrimitiveGate.mapWires placement)
  initialState := basisKet
    (fixedOutsideBasisEmbedding placement outside initialBasis)
  targetState := fixedOutsideStateEmbedding placement outside component.targetState
  correct := by
    rw [denote_mapPrimitiveWires_eq_wireLiftOperator,
      applyOperator_wireLiftOperator_fixedOutsideBasisKet]
    rw [← component.correct, initialState_eq]

end StatePreparationComponent

namespace ExactOperatorComponent

/-- wire-liftした厳密componentを指定外部基底のcoherent部分空間契約として読む。 -/
def mapPrimitiveWiresToFixedOutsideSubspace
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (component : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue)) :
    SubspaceOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) := by
  let lifted := component.mapPrimitiveWires symbolValue placement
  exact {
    circuit := lifted.circuit
    target := lifted.target
    subspace := fixedOutsideStateSubspace placement outside
    correct := fun state _ =>
      congrArg (fun operator => applyOperator operator state) lifted.correct
    target_preserves := by
      intro state stateInside
      exact wireLiftOperator_preserves_fixedOutsideStateSubspace
        placement outside component.target state stateInside
  }

end ExactOperatorComponent

namespace ApproxOperatorComponent

/--
異なる基底上の誤差modelについてwire-lift保存則を明示的に受け取り、近似componentを
injective wire配置へ移す。full-space norm保存を無条件には仮定しない設計境界である。
-/
def mapPrimitiveWiresWithModel
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    {sourceModel : OperatorErrorModel (QubitBasis sourceQubits)}
    {targetModel : OperatorErrorModel (QubitBasis targetQubits)}
    (liftContraction : ∀ operator,
      sourceModel.isContraction operator →
        targetModel.isContraction (wireLiftOperator placement operator))
    (liftApprox : ∀ actual target error,
      sourceModel.approx actual target error →
        targetModel.approx (wireLiftOperator placement actual)
          (wireLiftOperator placement target) error)
    (component : ApproxOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue) sourceModel) :
    ApproxOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) targetModel where
  circuit := component.circuit.mapGates (PrimitiveGate.mapWires placement)
  target := wireLiftOperator placement component.target
  error := component.error
  error_nonnegative := component.error_nonnegative
  actual_contraction := by
    rw [denote_mapPrimitiveWires_eq_wireLiftOperator]
    exact liftContraction _ component.actual_contraction
  target_contraction := liftContraction _ component.target_contraction
  correct := by
    rw [denote_mapPrimitiveWires_eq_wireLiftOperator]
    exact liftApprox _ _ _ component.correct

end ApproxOperatorComponent

/-!
## Parallel normalized-macro wire-embedding bridge

The legacy `PrimitiveGate` embedding theorem above remains the compatibility
surface.  The definitions below package the exact phase-shift and
controlled-rotation macros as `ControlledCircuitCompilerV2.NormalizedCircuit`
inputs, so the v2 control compiler can re-control them without admitting a
legacy leaf.  Each result keeps a separately specified semantic target and
uses the pre-existing strict wire-lift theorem; no denotation is used as a
target definition.
-/

namespace PhaseShiftRzSpec

def mapWires {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : PhaseShiftRzSpec sourceQubits) : PhaseShiftRzSpec targetQubits :=
  { angle := spec.angle, target := placement spec.target }

end PhaseShiftRzSpec

namespace PhaseShiftGlobalPhaseSpec

def mapWires {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : PhaseShiftGlobalPhaseSpec sourceQubits) :
    PhaseShiftGlobalPhaseSpec targetQubits :=
  { angle := spec.angle, witness := placement spec.witness }

end PhaseShiftGlobalPhaseSpec

namespace ControlledRySpec

def mapWires {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : ControlledRySpec sourceQubits) : ControlledRySpec targetQubits :=
  { angle := spec.angle
    control := placement spec.control
    target := placement spec.target
    different := fun equal => spec.different (placement.injective equal) }

end ControlledRySpec

namespace ControlledRzSpec

def mapWires {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : ControlledRzSpec sourceQubits) : ControlledRzSpec targetQubits :=
  { angle := spec.angle
    control := placement spec.control
    target := placement spec.target
    different := fun equal => spec.different (placement.injective equal) }

end ControlledRzSpec

/-- The global and v2 normal-form predicates recognize the same six leaves. -/
theorem isNormalizedPrimitive_iff_controlledCircuitCompilerV2 {qubits : Nat}
    (gate : PrimitiveGate qubits) :
    IsNormalizedPrimitive gate ↔
      ControlledCircuitCompilerV2.IsNormalizedPrimitive gate := by
  cases gate <;> rfl

/-- `Rz` is an admissible v2 source circuit through its exact phase-shift macro. -/
def phaseShiftRzNormalizedCircuit {qubits : Nat}
    (spec : PhaseShiftRzSpec qubits) :
    ControlledCircuitCompilerV2.NormalizedCircuit qubits where
  circuit := phaseShiftRzCircuit spec
  normalized := by
    intro gate member
    apply (isNormalizedPrimitive_iff_controlledCircuitCompilerV2 gate).mp
    exact phaseShiftRzCircuit_usesOnlyNormalizedPrimitives spec gate member

/-- An exact global-phase macro remains a normalized v2 circuit, with its
nonempty witness represented by the typed source specification. -/
def phaseShiftGlobalPhaseNormalizedCircuit {qubits : Nat}
    (spec : PhaseShiftGlobalPhaseSpec qubits) :
    ControlledCircuitCompilerV2.NormalizedCircuit qubits where
  circuit := phaseShiftGlobalPhaseCircuit spec
  normalized := by
    intro gate member
    apply (isNormalizedPrimitive_iff_controlledCircuitCompilerV2 gate).mp
    exact phaseShiftGlobalPhaseCircuit_usesOnlyNormalizedPrimitives spec gate member

/-- The exact four-leaf controlled-Ry macro is an admissible v2 source circuit. -/
def controlledRyMacroNormalizedCircuit {qubits : Nat}
    (spec : ControlledRySpec qubits) :
    ControlledCircuitCompilerV2.NormalizedCircuit qubits where
  circuit := controlledRyMacroCircuit spec
  normalized := by
    intro gate member
    apply (isNormalizedPrimitive_iff_controlledCircuitCompilerV2 gate).mp
    exact controlledRyMacroCircuit_usesOnlyNormalizedPrimitives spec gate member

/-- The exact four-leaf controlled-Rz macro is an admissible v2 source circuit. -/
def controlledRzMacroNormalizedCircuit {qubits : Nat}
    (spec : ControlledRzSpec qubits) :
    ControlledCircuitCompilerV2.NormalizedCircuit qubits where
  circuit := controlledRzMacroCircuit spec
  normalized := by
    intro gate member
    apply (isNormalizedPrimitive_iff_controlledCircuitCompilerV2 gate).mp
    exact controlledRzMacroCircuit_usesOnlyNormalizedPrimitives spec gate member

theorem phaseShiftRzNormalizedCircuit_source_order {qubits : Nat}
    (spec : PhaseShiftRzSpec qubits) :
    (phaseShiftRzNormalizedCircuit spec).circuit = phaseShiftRzCircuit spec := rfl

theorem phaseShiftGlobalPhaseNormalizedCircuit_source_order {qubits : Nat}
    (spec : PhaseShiftGlobalPhaseSpec qubits) :
    (phaseShiftGlobalPhaseNormalizedCircuit spec).circuit =
      phaseShiftGlobalPhaseCircuit spec := rfl

theorem controlledRyMacroNormalizedCircuit_source_order {qubits : Nat}
    (spec : ControlledRySpec qubits) :
    (controlledRyMacroNormalizedCircuit spec).circuit =
      controlledRyMacroCircuit spec := rfl

theorem controlledRzMacroNormalizedCircuit_source_order {qubits : Nat}
    (spec : ControlledRzSpec qubits) :
    (controlledRzMacroNormalizedCircuit spec).circuit =
      controlledRzMacroCircuit spec := rfl

theorem phaseShiftRzNormalizedCircuit_mapWires_source_order
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : PhaseShiftRzSpec sourceQubits) :
    (ControlledCircuitCompilerV2.NormalizedCircuit.mapWires placement
      (phaseShiftRzNormalizedCircuit spec)).circuit =
      (phaseShiftRzNormalizedCircuit (spec.mapWires placement)).circuit := by
  cases spec
  rfl

theorem phaseShiftGlobalPhaseNormalizedCircuit_mapWires_source_order
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : PhaseShiftGlobalPhaseSpec sourceQubits) :
    (ControlledCircuitCompilerV2.NormalizedCircuit.mapWires placement
      (phaseShiftGlobalPhaseNormalizedCircuit spec)).circuit =
      (phaseShiftGlobalPhaseNormalizedCircuit (spec.mapWires placement)).circuit := by
  cases spec
  rfl

theorem controlledRyMacroNormalizedCircuit_mapWires_source_order
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : ControlledRySpec sourceQubits) :
    (ControlledCircuitCompilerV2.NormalizedCircuit.mapWires placement
      (controlledRyMacroNormalizedCircuit spec)).circuit =
      (controlledRyMacroNormalizedCircuit (spec.mapWires placement)).circuit := by
  cases spec
  rfl

theorem controlledRzMacroNormalizedCircuit_mapWires_source_order
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : ControlledRzSpec sourceQubits) :
    (ControlledCircuitCompilerV2.NormalizedCircuit.mapWires placement
      (controlledRzMacroNormalizedCircuit spec)).circuit =
      (controlledRzMacroNormalizedCircuit (spec.mapWires placement)).circuit := by
  cases spec
  rfl

theorem phaseShiftRzNormalizedCircuit_denote_eq {qubits : Nat}
    (symbolValue : String → ℝ) (spec : PhaseShiftRzSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (phaseShiftRzNormalizedCircuit spec).circuit =
      phaseShiftRzOperator symbolValue spec :=
  phaseShiftRzCircuit_denote_eq symbolValue spec

theorem phaseShiftGlobalPhaseNormalizedCircuit_denote_eq {qubits : Nat}
    (symbolValue : String → ℝ) (spec : PhaseShiftGlobalPhaseSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (phaseShiftGlobalPhaseNormalizedCircuit spec).circuit =
      phaseShiftGlobalPhaseOperator symbolValue spec :=
  phaseShiftGlobalPhaseCircuit_denote_eq symbolValue spec

theorem controlledRyMacroNormalizedCircuit_denote_eq {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRySpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledRyMacroNormalizedCircuit spec).circuit =
      controlledRyMacroOperator symbolValue spec :=
  controlledRyMacroCircuit_denote_eq symbolValue spec

theorem controlledRzMacroNormalizedCircuit_denote_eq {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRzSpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledRzMacroNormalizedCircuit spec).circuit =
      controlledRzMacroOperator symbolValue spec :=
  controlledRzMacroCircuit_denote_eq symbolValue spec

theorem phaseShiftRzNormalizedCircuit_mapWires_denote_eq {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ) (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : PhaseShiftRzSpec sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (ControlledCircuitCompilerV2.NormalizedCircuit.mapWires placement
          (phaseShiftRzNormalizedCircuit spec)).circuit =
      wireLiftOperator placement (phaseShiftRzOperator symbolValue spec) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      ((phaseShiftRzCircuit spec).mapGates (PrimitiveGate.mapWires placement)) =
    wireLiftOperator placement (phaseShiftRzOperator symbolValue spec)
  rw [denote_mapPrimitiveWires_eq_wireLiftOperator]
  exact congrArg (wireLiftOperator placement)
    (phaseShiftRzCircuit_denote_eq symbolValue spec)

theorem phaseShiftGlobalPhaseNormalizedCircuit_mapWires_denote_eq
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ) (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : PhaseShiftGlobalPhaseSpec sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (ControlledCircuitCompilerV2.NormalizedCircuit.mapWires placement
          (phaseShiftGlobalPhaseNormalizedCircuit spec)).circuit =
      wireLiftOperator placement (phaseShiftGlobalPhaseOperator symbolValue spec) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      ((phaseShiftGlobalPhaseCircuit spec).mapGates
        (PrimitiveGate.mapWires placement)) =
    wireLiftOperator placement (phaseShiftGlobalPhaseOperator symbolValue spec)
  rw [denote_mapPrimitiveWires_eq_wireLiftOperator]
  exact congrArg (wireLiftOperator placement)
    (phaseShiftGlobalPhaseCircuit_denote_eq symbolValue spec)

theorem controlledRyMacroNormalizedCircuit_mapWires_denote_eq
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ) (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : ControlledRySpec sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (ControlledCircuitCompilerV2.NormalizedCircuit.mapWires placement
          (controlledRyMacroNormalizedCircuit spec)).circuit =
      wireLiftOperator placement (controlledRyMacroOperator symbolValue spec) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      ((controlledRyMacroCircuit spec).mapGates (PrimitiveGate.mapWires placement)) =
    wireLiftOperator placement (controlledRyMacroOperator symbolValue spec)
  rw [denote_mapPrimitiveWires_eq_wireLiftOperator]
  exact congrArg (wireLiftOperator placement)
    (controlledRyMacroCircuit_denote_eq symbolValue spec)

theorem controlledRzMacroNormalizedCircuit_mapWires_denote_eq
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ) (placement : Fin sourceQubits ↪ Fin targetQubits)
    (spec : ControlledRzSpec sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (ControlledCircuitCompilerV2.NormalizedCircuit.mapWires placement
          (controlledRzMacroNormalizedCircuit spec)).circuit =
      wireLiftOperator placement (controlledRzMacroOperator symbolValue spec) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      ((controlledRzMacroCircuit spec).mapGates (PrimitiveGate.mapWires placement)) =
    wireLiftOperator placement (controlledRzMacroOperator symbolValue spec)
  rw [denote_mapPrimitiveWires_eq_wireLiftOperator]
  exact congrArg (wireLiftOperator placement)
    (controlledRzMacroCircuit_denote_eq symbolValue spec)

end

end VerifiedCircuitCore
