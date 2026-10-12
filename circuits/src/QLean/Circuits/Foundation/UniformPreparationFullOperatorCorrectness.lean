import QLean.Circuits.Foundation.UniformPreparationFullOperatorAnalytic
import QLean.Circuits.Foundation.UniformPreparationCorrectness
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.WireEmbedding

/-!
# 任意サイズ一様準備compilerのfull-space Exact契約

一命令を独立なdirty-work作用素へ結び、公開子componentの`seq`だけで有限計画と
任意`0 < N ≤ 2^w`の正本ASTを合成する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- The implementation and pure-analytic names for the local scratch list
denote the same ordered wires. -/
theorem uniformPreparationScratchWires_eq_analytic (width : Nat) :
    uniformPreparationScratchWires width =
      uniformPreparationAnalyticScratchWires width := by
  simp [uniformPreparationScratchWires,
    uniformPreparationAnalyticScratchWires,
    uniformPreparationScratchWire,
    uniformPreparationAnalyticScratchWire]

/-- 型安全CNOT回路のfull-space作用素は独立作用素に一致する。 -/
theorem uniformSafeCnotCircuit_denote_eq_analyticOperator
    {qubits : Nat} (control target : Fin qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.safeCnot control target) =
      uniformSafeCnotAnalyticOperator control target := by
  by_cases different : control ≠ target
  · simp [Circuit.safeCnot, uniformSafeCnotAnalyticOperator, different,
      Circuit.denote, primitiveGateOperatorWithSymbols]
  · simp [Circuit.safeCnot, uniformSafeCnotAnalyticOperator, different,
      Circuit.denote]

/-- 型安全Toffoli回路のfull-space作用素は独立作用素に一致する。 -/
theorem uniformSafeToffoliCircuit_denote_eq_analyticOperator
    {qubits : Nat} (control₀ control₁ target : Fin qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.safeToffoli control₀ control₁ target) =
      uniformSafeToffoliAnalyticOperator control₀ control₁ target := by
  by_cases controlsDifferent : control₀ ≠ control₁
  · by_cases firstDifferent : control₀ ≠ target
    · by_cases secondDifferent : control₁ ≠ target
      · simp [Circuit.safeToffoli, uniformSafeToffoliAnalyticOperator,
          controlsDifferent, firstDifferent, secondDifferent,
          Circuit.denote, primitiveGateOperatorWithSymbols]
      · simp [Circuit.safeToffoli, uniformSafeToffoliAnalyticOperator,
          controlsDifferent, firstDifferent, secondDifferent, Circuit.denote]
    · simp [Circuit.safeToffoli, uniformSafeToffoliAnalyticOperator,
        controlsDifferent, firstDifferent, Circuit.denote]
  · simp [Circuit.safeToffoli, uniformSafeToffoliAnalyticOperator,
      controlsDifferent, Circuit.denote]

/-- 一制御Ry分解回路は四個の独立局所作用素積に一致する。 -/
theorem uniformControlledRyDecompositionCircuit_denote_eq_analyticOperator
    {qubits : Nat} (control target : Fin qubits)
    (different : control ≠ target) (angle : AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.controlledRyMacroExpansion control target different angle) =
      uniformControlledRyDecompositionAnalyticOperator
        control target different angle := by
  rw [Circuit.controlledRyMacroExpansion,
    Circuit.denote_fromList_eq_operatorSequence]
  simp [uniformControlledRyDecompositionAnalyticOperator,
    uniformHalfAngle, Circuit.halfAngle, primitiveGateOperatorWithSymbols]

/-- The existing uniform-preparation one-control rotation is exposed in
parallel as a normalized v2 macro input.  The scientific source order remains
the established four-leaf decomposition, while the type certificate makes the
result directly admissible for a second v2 control lowering. -/
def uniformControlledRyMacroSpec {qubits : Nat} (control target : Fin qubits)
    (different : control ≠ target) (angle : AngleExpr) : ControlledRySpec qubits :=
  { angle := angle, control := control, target := target, different := different }

theorem uniformControlledRyMacroNormalizedCircuit_source_order {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target) (angle : AngleExpr) :
    (controlledRyMacroNormalizedCircuit
      (uniformControlledRyMacroSpec control target different angle)).circuit =
      Circuit.controlledRyMacroExpansion control target different angle := rfl

/-- The normalized macro keeps the pre-existing independent uniform analytic
target under strict operator equality. -/
theorem uniformControlledRyMacroNormalizedCircuit_denote_eq_analyticOperator
    {qubits : Nat} (control target : Fin qubits)
    (different : control ≠ target) (angle : AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (controlledRyMacroNormalizedCircuit
          (uniformControlledRyMacroSpec control target different angle)).circuit =
      uniformControlledRyDecompositionAnalyticOperator
        control target different angle := by
  change Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (Circuit.controlledRyMacroExpansion control target different angle) =
    uniformControlledRyDecompositionAnalyticOperator
      control target different angle
  exact uniformControlledRyDecompositionCircuit_denote_eq_analyticOperator
    control target different angle

def uniformControlledRyMacroNormalizedExactComponent {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target) (angle : AngleExpr) :
    ExactOperatorComponent (primitiveGateOperatorWithSymbols (qubits := qubits) (fun _ => 0)) where
  circuit := (controlledRyMacroNormalizedCircuit
    (uniformControlledRyMacroSpec control target different angle)).circuit
  target := uniformControlledRyDecompositionAnalyticOperator
    control target different angle
  correct := uniformControlledRyMacroNormalizedCircuit_denote_eq_analyticOperator
    control target different angle

/-- 0-control反転列は独立X作用素積に一致する。 -/
theorem uniformInvertZeroControlsCircuit_denote_eq_analyticOperator
    {qubits : Nat} (controls : List (Fin qubits × Bool)) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.invertZeroControls controls) =
      uniformInvertZeroControlsAnalyticOperator controls := by
  rw [Circuit.invertZeroControls, uniformInvertZeroControlsAnalyticOperator,
    Circuit.denote_fromList_eq_operatorSequence]
  congr 1
  induction controls with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨wire, value⟩
      cases value <;> simp [primitiveGateOperatorWithSymbols, inductionHypothesis]

/-- AND鎖compilerは再帰的独立作用素積に一致する。 -/
theorem uniformAndChainControlledRyCircuit_denote_eq_analyticOperator
    {qubits : Nat} (previous : Fin qubits) :
    ∀ (controls scratches : List (Fin qubits))
      (target : Fin qubits) (angle : AngleExpr),
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.andChainControlledRy previous controls scratches target angle) =
        uniformAndChainControlledRyAnalyticOperator
          previous controls scratches target angle
  | [], scratches, target, angle => by
      by_cases different : previous ≠ target
      · simp [Circuit.andChainControlledRy,
          uniformAndChainControlledRyAnalyticOperator, different,
          uniformControlledRyDecompositionCircuit_denote_eq_analyticOperator]
      · simp [Circuit.andChainControlledRy,
          uniformAndChainControlledRyAnalyticOperator, different, Circuit.denote]
  | _ :: _, [], _, _ => rfl
  | control :: controls, scratch :: scratches, target, angle => by
      simp [Circuit.andChainControlledRy,
        uniformAndChainControlledRyAnalyticOperator,
        uniformSafeToffoliCircuit_denote_eq_analyticOperator,
        uniformAndChainControlledRyCircuit_denote_eq_analyticOperator
          scratch controls scratches target angle,
        Circuit.denote, mul_assoc]

/-- 正制御AND compilerは再帰的独立作用素積に一致する。 -/
theorem uniformPositiveMultiControlledRyCircuit_denote_eq_analyticOperator
    {qubits : Nat} :
    ∀ (controls scratches : List (Fin qubits))
      (target : Fin qubits) (angle : AngleExpr),
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.positiveMultiControlledRy controls scratches target angle) =
        uniformPositiveMultiControlledRyAnalyticOperator
          controls scratches target angle
  | [], scratches, target, angle => by
      simp [Circuit.positiveMultiControlledRy,
        uniformPositiveMultiControlledRyAnalyticOperator,
        Circuit.denote, primitiveGateOperatorWithSymbols]
  | [control], scratches, target, angle => by
      by_cases different : control ≠ target
      · simp [Circuit.positiveMultiControlledRy,
          uniformPositiveMultiControlledRyAnalyticOperator, different,
          uniformControlledRyDecompositionCircuit_denote_eq_analyticOperator]
      · simp [Circuit.positiveMultiControlledRy,
          uniformPositiveMultiControlledRyAnalyticOperator, different,
          Circuit.denote]
  | _ :: _ :: _, [], _, _ => rfl
  | control₀ :: control₁ :: controls, scratch :: scratches, target, angle => by
      cases controls with
      | nil =>
          by_cases different : scratch ≠ target
          · simp [Circuit.positiveMultiControlledRy,
              uniformPositiveMultiControlledRyAnalyticOperator, different,
              uniformSafeToffoliCircuit_denote_eq_analyticOperator,
              uniformControlledRyDecompositionCircuit_denote_eq_analyticOperator,
              Circuit.denote]
          · simp [Circuit.positiveMultiControlledRy,
              uniformPositiveMultiControlledRyAnalyticOperator, different,
              uniformSafeToffoliCircuit_denote_eq_analyticOperator,
              Circuit.denote]
      | cons control controls =>
          simp [Circuit.positiveMultiControlledRy,
            uniformPositiveMultiControlledRyAnalyticOperator,
            uniformSafeToffoliCircuit_denote_eq_analyticOperator,
            uniformAndChainControlledRyCircuit_denote_eq_analyticOperator,
            Circuit.denote, mul_assoc]

/-- Bool制御compilerはdirty-work対応独立作用素に一致する。 -/
theorem uniformBoolMultiControlledRyCircuit_denote_eq_analyticOperator
    {qubits : Nat} (controls : List (Fin qubits × Bool))
    (scratch : List (Fin qubits)) (target : Fin qubits) (angle : AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.boolMultiControlledRy controls scratch target angle) =
      uniformBoolMultiControlledRyAnalyticOperator
        controls scratch target angle := by
  simp [Circuit.boolMultiControlledRy,
    uniformBoolMultiControlledRyAnalyticOperator,
    uniformInvertZeroControlsCircuit_denote_eq_analyticOperator,
    uniformPositiveMultiControlledRyCircuit_denote_eq_analyticOperator,
    Circuit.denote, mul_assoc]

/-- 一命令compilerを独立なfull-space作用素へ結ぶ末端component。 -/
def uniformRotationInstructionFullExactOperatorComponent
    (width : Nat)
    (instruction : {instruction : UniformRotationInstruction //
      instruction.WellFormed width}) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := 2 * width) (fun _ => 0)) where
  circuit := compileUniformRotationInstruction width instruction.1 instruction.2
  target := uniformBoolMultiControlledRyAnalyticOperator
    (instruction.1.controls.attach.map fun control =>
      (uniformPreparationAnalyticSelectorWire width
        ⟨control.1.1, instruction.2.2.1 control.1 control.2⟩,
        control.1.2))
    (uniformPreparationAnalyticScratchWires width)
    (uniformPreparationAnalyticSelectorWire width
      ⟨instruction.1.target, instruction.2.1⟩)
    instruction.1.angle
  correct := by
    have scratchEq : uniformPreparationScratchWires width =
        uniformPreparationAnalyticScratchWires width := by
      unfold uniformPreparationScratchWires
        uniformPreparationAnalyticScratchWires
      apply List.map_congr_left
      intro wire _
      apply Fin.ext
      rfl
    change Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.boolMultiControlledRy
          (uniformRotationInstructionControls width instruction.1 instruction.2)
          (uniformPreparationScratchWires width)
          (uniformRotationInstructionTarget width instruction.1 instruction.2)
          instruction.1.angle) = _
    rw [← scratchEq]
    simpa [uniformRotationInstructionControls,
      uniformRotationInstructionTarget, uniformPreparationSelectorWire,
      uniformPreparationAnalyticSelectorWire,
      uniformPreparationScratchWires, uniformPreparationScratchWire,
      uniformPreparationAnalyticScratchWires] using
      uniformBoolMultiControlledRyCircuit_denote_eq_analyticOperator
        (uniformRotationInstructionControls width instruction.1 instruction.2)
        (uniformPreparationScratchWires width)
        (uniformRotationInstructionTarget width instruction.1 instruction.2)
        instruction.1.angle

/-- 命令列を子componentの二項`seq`だけで合成するfull-space component。 -/
def uniformPreparationPlanFullExactOperatorComponent (width : Nat) :
    List {instruction : UniformRotationInstruction //
      instruction.WellFormed width} →
      ExactOperatorComponent
        (primitiveGateOperatorWithSymbols (qubits := 2 * width) (fun _ => 0))
  | [] => ExactOperatorComponent.identity _
  | instruction :: rest => ExactOperatorComponent.seq
      (uniformRotationInstructionFullExactOperatorComponent width instruction)
      (uniformPreparationPlanFullExactOperatorComponent width rest)

/-- 計画componentの回路fieldは命令compiler列の正本ASTに一致する。 -/
theorem uniformPreparationPlanFullExactOperatorComponent_circuit
    (width : Nat) :
    ∀ plan : List {instruction : UniformRotationInstruction //
        instruction.WellFormed width},
      (uniformPreparationPlanFullExactOperatorComponent width plan).circuit =
        Circuit.sequence (plan.map fun instruction =>
          compileUniformRotationInstruction width instruction.1 instruction.2)
  | [] => rfl
  | instruction :: rest => by
      change Circuit.seq
          (compileUniformRotationInstruction width instruction.1 instruction.2)
          (uniformPreparationPlanFullExactOperatorComponent width rest).circuit =
        Circuit.seq
          (compileUniformRotationInstruction width instruction.1 instruction.2)
          (Circuit.sequence (rest.map fun next =>
            compileUniformRotationInstruction width next.1 next.2))
      congr 1
      exact uniformPreparationPlanFullExactOperatorComponent_circuit width rest

/-- 計画componentのtargetは公開子targetの独立作用素積に一致する。 -/
theorem uniformPreparationPlanFullExactOperatorComponent_target
    (width : Nat) :
    ∀ plan : List {instruction : UniformRotationInstruction //
        instruction.WellFormed width},
      (uniformPreparationPlanFullExactOperatorComponent width plan).target =
        uniformPreparationPlanFullAnalyticOperator width plan
  | [] => rfl
  | instruction :: rest => by
      change (uniformPreparationPlanFullExactOperatorComponent width rest).target *
          (uniformRotationInstructionFullExactOperatorComponent
            width instruction).target = _
      rw [uniformPreparationPlanFullExactOperatorComponent_target width rest]
      rfl

/-- 任意`0 < N ≤ 2^w`の正本ASTを独立full-space作用素へ結ぶExact component。 -/
def uniformPreparationFullExactOperatorComponent
    (parameters : UniformPreparationParameters) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := 2 * parameters.width) (fun _ => 0)) where
  circuit := uniformPreparationCircuit parameters
  target := uniformPreparationFullAnalyticOperator parameters
  correct := by
    let child := uniformPreparationPlanFullExactOperatorComponent parameters.width
      (attachedUniformRotationPlan parameters.width parameters.validCount
        parameters.validCountLeCapacity)
    have circuitEq : child.circuit = uniformPreparationCircuit parameters := by
      rw [uniformPreparationPlanFullExactOperatorComponent_circuit]
      rfl
    have targetEq : child.target =
        uniformPreparationFullAnalyticOperator parameters := by
      rw [uniformPreparationPlanFullExactOperatorComponent_target]
      rfl
    rw [← circuitEq, ← targetEq]
    exact child.correct

/-- 一様準備full-space Exact componentをユニタリ契約へ昇格する。 -/
def uniformPreparationFullUnitaryExactOperatorComponent
    (parameters : UniformPreparationParameters) :
    UnitaryExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := 2 * parameters.width) (fun _ => 0)) :=
  ExactOperatorComponent.toUnitary
    (primitiveGateOperatorWithSymbols_mem_unitaryGroup (qubits := 2 * parameters.width)
      (fun _ => 0))
    (uniformPreparationFullExactOperatorComponent parameters)

/-- 正本一様準備ASTの全作用素は独立full-space targetに厳密一致する。 -/
theorem uniformPreparationCircuit_denote_eq_fullAnalyticOperator
    (parameters : UniformPreparationParameters) :
    (uniformPreparationCircuit parameters).denote
        (primitiveGateOperatorWithSymbols (fun _ => 0)) =
      uniformPreparationFullAnalyticOperator parameters :=
  (uniformPreparationFullExactOperatorComponent parameters).correct

/-- Extensional clean-sector specification of the full-space target: a
scratch-zero basis column has no amplitude on a scratch-dirty basis row.
This exposes the mathematical invariant independently of the compiler AST. -/
theorem uniformPreparationFullAnalyticOperator_scratchZero_transition
    (parameters : UniformPreparationParameters)
    (input output : QubitBasis (2 * parameters.width))
    (inputZero : ∀ wire ∈ uniformPreparationScratchWires parameters.width,
      input wire = false)
    (outputDirty : ∃ wire ∈ uniformPreparationScratchWires parameters.width,
      output wire = true) :
    uniformPreparationFullAnalyticOperator parameters output input = 0 := by
  have inputSupported : SupportedOnUniformScratchZero parameters.width
      (basisKet input) := by
    intro basis dirty
    by_cases equal : basis = input
    · subst basis
      rcases dirty with ⟨wire, member, wireTrue⟩
      rw [inputZero wire member] at wireTrue
      contradiction
    · simp [basisKet, equal]
  have outputZero := uniformPreparationCircuit_preserves_support parameters
    (basisKet input) inputSupported output outputDirty
  rw [uniformPreparationCircuit_denote_eq_fullAnalyticOperator,
    applyOperator_basisKet] at outputZero
  exact outputZero

/-- The independent full-space target is unitary for every valid width/count
parameter record. -/
theorem uniformPreparationFullAnalyticOperator_mem_unitaryGroup
    (parameters : UniformPreparationParameters) :
    uniformPreparationFullAnalyticOperator parameters ∈
      Matrix.unitaryGroup (QubitBasis (2 * parameters.width)) ℂ :=
  (uniformPreparationFullUnitaryExactOperatorComponent parameters).target_unitary

end

end VerifiedCircuitCore
