import QLean.Circuits.Foundation.NormalizedPrimitiveProofBridge
import QLean.Circuits.Foundation.ControlledRotationMacros
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2
import QLean.Circuits.Foundation.ControlledCircuitCompiler
import QLean.Circuits.Foundation.ControlledHadamard
import QLean.Circuits.Foundation.ShuklaVedulaUniformCorrectness
import QLean.Circuits.Foundation.UniformPreparationFullOperatorCorrectness

/-!
# Cycle-free bridge for normalized control proof consumers

The bridge is a top-level leaf.  It joins the existing macro/compiler API to
the existing independent correctness targets without adding an import from a
low-level proof source back into the macro or compiler layers.
-/

namespace VerifiedCircuitCore

noncomputable section

namespace NormalizedControlProofBridge

theorem controlledRyMacro_source_order {qubits : Nat}
    (spec : ControlledRySpec qubits) :
    controlledRyMacroCircuit spec =
      Circuit.controlledRyMacroExpansion spec.control spec.target
        spec.different spec.angle := rfl

theorem controlledRyMacro_strict_target {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRySpec qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledRyMacroCircuit spec) =
      controlledRyMacroOperator symbolValue spec :=
  controlledRyMacroCircuit_denote_eq symbolValue spec

theorem controlledRyMacro_existing_decomposition_target {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.controlledRyMacroExpansion control target different angle) =
      embedControlledSingleQubitOperator control target different
        (localRy angle.uniformValue) :=
  Circuit.controlledRyMacroExpansion_operator control target different angle

theorem controlledRyMacro_zero_strict_target {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (controlledRyMacroCircuit
          { angle := angle, control := control, target := target,
            different := different }) =
      embedControlledSingleQubitOperator control target different
        (localRy angle.uniformValue) := by
  simpa [controlledRyMacroCircuit] using
    (Circuit.controlledRyMacroExpansion_operator control target different angle)

theorem controlledRyMacro_unitary {qubits : Nat}
    (symbolValue : String → ℝ) (spec : ControlledRySpec qubits) :
    controlledRyMacroOperator symbolValue spec ∈
      Matrix.unitaryGroup (QubitBasis qubits) ℂ :=
  controlledRyMacroOperator_mem_unitaryGroup symbolValue spec

theorem controlledRyMacro_v2_normalized {qubits : Nat}
    (spec : ControlledRySpec qubits) :
    ControlledCircuitCompilerV2.IsNormalizedCircuit
      (controlledRyMacroCircuit spec) := by
  intro gate member
  apply (NormalizedPrimitiveProofBridge.root_predicate_iff_v2 gate).mp
  exact controlledRyMacroCircuit_usesOnlyNormalizedPrimitives spec gate member

theorem controlledRzMacro_v2_normalized {qubits : Nat}
    (spec : ControlledRzSpec qubits) :
    ControlledCircuitCompilerV2.IsNormalizedCircuit
      (controlledRzMacroCircuit spec) := by
  intro gate member
  apply (NormalizedPrimitiveProofBridge.root_predicate_iff_v2 gate).mp
  exact controlledRzMacroCircuit_usesOnlyNormalizedPrimitives spec gate member

theorem safeToffoli_v2_normalized {qubits : Nat}
    (control₀ control₁ target : Fin qubits) :
    ControlledCircuitCompilerV2.IsNormalizedCircuit
      (Circuit.safeToffoli control₀ control₁ target) := by
  intro gate member
  unfold Circuit.safeToffoli at member
  split at member <;> try split at member <;> try split at member
  all_goals simp [Circuit.flatten] at member
  all_goals subst gate
  all_goals simp [ControlledCircuitCompilerV2.IsNormalizedPrimitive]

private theorem controlledRyMacroExpansion_v2_normalized
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) :
    ∀ gate ∈
      (Circuit.controlledRyMacroExpansion control target different angle).flatten,
      ControlledCircuitCompilerV2.IsNormalizedPrimitive gate := by
  intro gate member
  simp only [Circuit.controlledRyMacroExpansion, Circuit.flatten_fromList,
    List.mem_cons] at member
  simp at member
  rcases member with member | member | member | member
  all_goals subst gate
  all_goals simp [ControlledCircuitCompilerV2.IsNormalizedPrimitive]

theorem andChainControlledRy_v2_normalized {qubits : Nat}
    (previous : Fin qubits) (controls scratches : List (Fin qubits))
    (target : Fin qubits) (angle : AngleExpr) :
    ControlledCircuitCompilerV2.IsNormalizedCircuit
      (Circuit.andChainControlledRy previous controls scratches target angle) := by
  induction controls generalizing previous scratches with
  | nil =>
      intro gate member
      simp only [Circuit.andChainControlledRy] at member
      split at member
      · exact controlledRyMacroExpansion_v2_normalized previous target _ angle gate member
      · simp [Circuit.flatten] at member
  | cons control controls inductionHypothesis =>
      cases scratches with
      | nil =>
          intro gate member
          simp [Circuit.andChainControlledRy, Circuit.flatten] at member
      | cons scratch scratches =>
          intro gate member
          simp only [Circuit.andChainControlledRy, Circuit.flatten,
            List.mem_append] at member
          rcases member with member | member | member
          · exact safeToffoli_v2_normalized previous control scratch gate member
          · exact inductionHypothesis scratch scratches gate member
          · exact safeToffoli_v2_normalized previous control scratch gate member

theorem positiveMultiControlledRy_v2_normalized {qubits : Nat}
    (controls scratches : List (Fin qubits)) (target : Fin qubits)
    (angle : AngleExpr) :
    ControlledCircuitCompilerV2.IsNormalizedCircuit
      (Circuit.positiveMultiControlledRy controls scratches target angle) := by
  cases controls with
  | nil =>
      intro gate member
      simp [Circuit.positiveMultiControlledRy, Circuit.flatten] at member
      subst gate
      simp [ControlledCircuitCompilerV2.IsNormalizedPrimitive]
  | cons first rest =>
      cases rest with
      | nil =>
          intro gate member
          simp only [Circuit.positiveMultiControlledRy] at member
          split at member
          · exact controlledRyMacroExpansion_v2_normalized first target _ angle gate member
          · simp [Circuit.flatten] at member
      | cons second controls =>
          cases scratches with
          | nil =>
              intro gate member
              simp [Circuit.positiveMultiControlledRy, Circuit.flatten] at member
          | cons scratch scratches =>
              intro gate member
              simp only [Circuit.positiveMultiControlledRy, Circuit.flatten,
                List.mem_append] at member
              rcases member with member | member | member
              · exact safeToffoli_v2_normalized first second scratch gate member
              · cases controls with
                | nil =>
                    simp only at member
                    split at member
                    · exact controlledRyMacroExpansion_v2_normalized
                        scratch target _ angle gate member
                    · simp [Circuit.flatten] at member
                | cons third controls =>
                    exact andChainControlledRy_v2_normalized scratch
                      (third :: controls) scratches target angle gate member
              · exact safeToffoli_v2_normalized first second scratch gate member

theorem shukla_controlledHadamard_source_plan_to_normalized_macro
    {width : Nat} (control target : Fin width) (different : control ≠ target) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledHadamardSourcePlan control target) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (controlledHadamardNormalizedMacroCircuit
          (ControlledHadamardSpecialAngleSpec.toRyZ {
            control := control, target := target, different := different })) := by
  let specialSpec : ControlledHadamardSpecialAngleSpec width := {
    control := control, target := target, different := different }
  calc
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledHadamardSourcePlan control target) =
        embedControlledSingleQubitOperator control target different localH :=
      sourcePlanOperator_controlledHadamardSourcePlan control target different
    _ = controlledHadamardSpecialAngleOperator specialSpec := rfl
    _ = Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (controlledHadamardNormalizedMacroCircuit specialSpec.toRyZ) := by
      change controlledHadamardSpecialAngleOperator specialSpec =
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (controlledHadamardNormalizedMacroCircuit specialSpec.toRyZ)
      symm
      simpa [controlledHadamardSpecialAngleExactOperatorComponent,
        controlledHadamardNormalizedMacroCircuit,
        controlledHadamardSpecialAngleCircuit, controlledRyZSevenGateCircuit] using
        (controlledHadamardSpecialAngleExactOperatorComponent
          (fun _ => 0) specialSpec).correct

theorem controlledHadamardNormalizedMacro_v2_normalized
    {qubits : Nat} (spec : ControlledHadamardSevenGateSpec qubits) :
    ControlledCircuitCompilerV2.IsNormalizedCircuit
      (controlledHadamardNormalizedMacroCircuit spec) := by
  intro gate member
  apply (NormalizedPrimitiveProofBridge.root_predicate_iff_v2 gate).mp
  exact controlledHadamardNormalizedMacroCircuit_usesOnlyNormalizedPrimitives
    spec gate member

theorem controlledRyMacro_apply_sparse {qubits : Nat}
    (spec : ControlledRySpec qubits) (output input : QubitBasis qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (controlledRyMacroCircuit spec) output input =
      if agreesExcept spec.target output input then
        if input spec.control then
          localRy spec.angle.uniformValue (output spec.target) (input spec.target)
        else if output spec.target = input spec.target then 1 else 0
      else 0 := by
  simpa [controlledRyMacroCircuit] using
    (Circuit.controlledRyMacroExpansion_apply_sparse spec.control spec.target
      spec.different spec.angle output input)

theorem positiveMultiControlledRy_sparse_compatibility
    {qubits : Nat}
    (controls scratches : List (Fin qubits))
    (target : Fin qubits)
    (angle : AngleExpr)
    (output input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.positiveMultiControlledRy controls scratches target angle)
        output input =
      positiveControlledRyAmplitude controls target angle.uniformValue output input :=
  positiveMultiControlledRy_apply_sparse controls scratches target angle output input
    enoughScratch layoutNodup scratchZero

theorem andChainControlledRy_sparse_compatibility
    {qubits : Nat}
    (previous : Fin qubits)
    (controls scratches : List (Fin qubits))
    (target : Fin qubits)
    (angle : AngleExpr)
    (output input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length)
    (layoutNodup : (previous :: controls ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.andChainControlledRy previous controls scratches target angle)
        output input =
      positiveControlledRyAmplitude (previous :: controls) target
        angle.uniformValue output input :=
  andChainControlledRy_apply_sparse previous controls scratches target angle
    output input enoughScratch layoutNodup scratchZero

theorem shukla_controlledRy_source_plan_compatibility
    {width : Nat} (control target : Fin width) (different : control ≠ target)
    (angle : AngleExpr) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledRySourcePlan control target angle) =
      embedControlledSingleQubitOperator control target different
        (localRy angle.uniformValue) :=
  sourcePlanOperator_controlledRySourcePlan control target different angle

theorem shukla_controlledRy_source_plan_to_macro {width : Nat}
    (control target : Fin width) (different : control ≠ target)
    (angle : AngleExpr) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledRySourcePlan control target angle) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (controlledRyMacroCircuit
          { angle := angle, control := control, target := target,
            different := different }) := by
  calc
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledRySourcePlan control target angle) =
        embedControlledSingleQubitOperator control target different
          (localRy angle.uniformValue) :=
      sourcePlanOperator_controlledRySourcePlan control target different angle
    _ = Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (controlledRyMacroCircuit
          { angle := angle, control := control, target := target,
            different := different }) := by
      symm
      simpa [controlledRyMacroCircuit] using
        (Circuit.controlledRyMacroExpansion_operator control target different angle)

theorem shukla_controlledHadamard_source_plan_compatibility
    {width : Nat} (control target : Fin width) (different : control ≠ target) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (controlledHadamardSourcePlan control target) =
      embedControlledSingleQubitOperator control target different localH :=
  sourcePlanOperator_controlledHadamardSourcePlan control target different

theorem shukla_source_plan_append_compatibility
    {width : Nat} (symbolValue : String → ℝ)
    (first second : List (ExternallyControlledPrimitivePlan width)) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator symbolValue
        (first ++ second) =
      ExternallyControlledPrimitivePlan.sourcePlanOperator symbolValue second *
        ExternallyControlledPrimitivePlan.sourcePlanOperator symbolValue first :=
  ExternallyControlledPrimitivePlan.sourcePlanOperator_append symbolValue first second

theorem shukla_zeroControlledRy_source_plan_compatibility
    {width : Nat} (control target : Fin width) (different : control ≠ target)
    (angle : AngleExpr) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (zeroControlledRySourcePlan control target angle) =
      embedZeroControlledSingleQubitOperator control target different
        (localRy angle.uniformValue) :=
  sourcePlanOperator_zeroControlledRySourcePlan control target different angle

theorem shukla_zeroControlledHadamard_source_plan_compatibility
    {width : Nat} (control target : Fin width) (different : control ≠ target) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (zeroControlledHadamardSourcePlan control target) =
      embedZeroControlledSingleQubitOperator control target different localH :=
  sourcePlanOperator_zeroControlledHadamardSourcePlan control target different

theorem shukla_width_only_state_target
    (parameters : UniformPreparationParameters) :
    applyOperator
        ((shuklaVedulaWidthOnlyUniformCircuit parameters).denote
          (primitiveGateOperatorWithSymbols (qubits := parameters.width) (fun _ => 0)))
        (basisKet (fun _ => false : QubitBasis parameters.width)) =
      uniformPreparationTargetState parameters :=
  shuklaVedulaWidthOnlyUniformCircuit_correct_state parameters

theorem normalized_uniform_safe_cnot_target
    {qubits : Nat} (control target : Fin qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.safeCnot control target) =
      uniformSafeCnotAnalyticOperator control target :=
  uniformSafeCnotCircuit_denote_eq_analyticOperator control target

theorem normalized_uniform_safe_toffoli_target
    {qubits : Nat} (control₀ control₁ target : Fin qubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.safeToffoli control₀ control₁ target) =
      uniformSafeToffoliAnalyticOperator control₀ control₁ target :=
  uniformSafeToffoliCircuit_denote_eq_analyticOperator control₀ control₁ target

theorem normalized_uniform_macro_source_order {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) :
    (controlledRyMacroNormalizedCircuit
      (uniformControlledRyMacroSpec control target different angle)).circuit =
      Circuit.controlledRyMacroExpansion control target different angle :=
  uniformControlledRyMacroNormalizedCircuit_source_order control target different angle

theorem normalized_uniform_macro_strict_target {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (controlledRyMacroNormalizedCircuit
          (uniformControlledRyMacroSpec control target different angle)).circuit =
      uniformControlledRyDecompositionAnalyticOperator
        control target different angle :=
  uniformControlledRyMacroNormalizedCircuit_denote_eq_analyticOperator
    control target different angle

theorem normalized_uniform_and_chain_target {qubits : Nat}
    (previous : Fin qubits) :
    ∀ (controls scratches : List (Fin qubits))
      (target : Fin qubits) (angle : AngleExpr),
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.andChainControlledRy previous controls scratches target angle) =
        uniformAndChainControlledRyAnalyticOperator
          previous controls scratches target angle :=
  uniformAndChainControlledRyCircuit_denote_eq_analyticOperator previous

theorem normalized_uniform_positive_target {qubits : Nat} :
    ∀ (controls scratches : List (Fin qubits))
      (target : Fin qubits) (angle : AngleExpr),
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (Circuit.positiveMultiControlledRy controls scratches target angle) =
        uniformPositiveMultiControlledRyAnalyticOperator
          controls scratches target angle :=
  uniformPositiveMultiControlledRyCircuit_denote_eq_analyticOperator

theorem normalized_uniform_bool_target {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (scratch : List (Fin qubits)) (target : Fin qubits) (angle : AngleExpr) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (Circuit.boolMultiControlledRy controls scratch target angle) =
      uniformBoolMultiControlledRyAnalyticOperator controls scratch target angle :=
  uniformBoolMultiControlledRyCircuit_denote_eq_analyticOperator
    controls scratch target angle

theorem normalized_uniform_plan_circuit_source_order
    (width : Nat) :
    ∀ plan : List {instruction : UniformRotationInstruction //
        instruction.WellFormed width},
      (uniformPreparationPlanFullExactOperatorComponent width plan).circuit =
        Circuit.sequence (plan.map fun instruction =>
          compileUniformRotationInstruction width instruction.1 instruction.2) :=
  uniformPreparationPlanFullExactOperatorComponent_circuit width

theorem normalized_uniform_plan_target
    (width : Nat) :
    ∀ plan : List {instruction : UniformRotationInstruction //
        instruction.WellFormed width},
      (uniformPreparationPlanFullExactOperatorComponent width plan).target =
        uniformPreparationPlanFullAnalyticOperator width plan :=
  uniformPreparationPlanFullExactOperatorComponent_target width

theorem normalized_uniform_full_strict_target
    (parameters : UniformPreparationParameters) :
    (uniformPreparationCircuit parameters).denote
        (primitiveGateOperatorWithSymbols (fun _ => 0)) =
      uniformPreparationFullAnalyticOperator parameters :=
  uniformPreparationCircuit_denote_eq_fullAnalyticOperator parameters

theorem normalized_uniform_full_target_unitary
    (parameters : UniformPreparationParameters) :
    uniformPreparationFullAnalyticOperator parameters ∈
      Matrix.unitaryGroup (QubitBasis (2 * parameters.width)) ℂ :=
  uniformPreparationFullAnalyticOperator_mem_unitaryGroup parameters

end NormalizedControlProofBridge

end

end VerifiedCircuitCore
