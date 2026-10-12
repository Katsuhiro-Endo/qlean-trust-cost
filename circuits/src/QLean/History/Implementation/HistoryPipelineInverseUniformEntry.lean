import QLean.History.Implementation.HistoryPipelineRepairedH3

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components

noncomputable section

theorem sourceOperator_inverse119
    {qubits : Nat} (symbolValue : String → ℝ)
    (leaf : ExternallyControlledPrimitivePlan qubits) :
    ExternallyControlledPrimitivePlan.sourceOperator symbolValue leaf.inverse =
      star (ExternallyControlledPrimitivePlan.sourceOperator symbolValue leaf) := by
  cases leaf with
  | x target =>
      simp [ExternallyControlledPrimitivePlan.inverse,
        ExternallyControlledPrimitivePlan.sourceOperator,
        star_embedSingleQubitOperator, star_localX]
  | z target =>
      simp [ExternallyControlledPrimitivePlan.inverse,
        ExternallyControlledPrimitivePlan.sourceOperator,
        star_embedSingleQubitOperator, star_localZ]
  | h target =>
      simp [ExternallyControlledPrimitivePlan.inverse,
        ExternallyControlledPrimitivePlan.sourceOperator,
        star_embedSingleQubitOperator, star_localH]
  | ry angle target =>
      simp [ExternallyControlledPrimitivePlan.inverse,
        ExternallyControlledPrimitivePlan.sourceOperator, AngleExpr.eval_neg,
        star_embedSingleQubitOperator, star_localRy]
  | phaseShift angle target =>
      simp [ExternallyControlledPrimitivePlan.inverse,
        ExternallyControlledPrimitivePlan.sourceOperator, AngleExpr.eval_neg,
        star_embedSingleQubitOperator, star_localPhaseShift]
  | rz angle target =>
      simp [ExternallyControlledPrimitivePlan.inverse,
        ExternallyControlledPrimitivePlan.sourceOperator, AngleExpr.eval_neg,
        star_embedSingleQubitOperator, star_localRz]
  | cnot control target different =>
      simp only [ExternallyControlledPrimitivePlan.inverse,
        ExternallyControlledPrimitivePlan.sourceOperator]
      unfold reversibleAnalyticCnotOperator
      exact (star_cnotOperator control target different).symm
  | toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      simp only [ExternallyControlledPrimitivePlan.inverse,
        ExternallyControlledPrimitivePlan.sourceOperator]
      unfold analyticToffoliOperator
      exact (star_toffoliOperator control₀ control₁ target
        firstDifferent secondDifferent).symm

theorem operatorSequence_reverse_map_star119
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operators : List (Operator basis)) :
    operatorSequence (operators.reverse.map star) =
      star (operatorSequence operators) := by
  induction operators with
  | nil => simp [operatorSequence]
  | cons first rest inductionHypothesis =>
      rw [List.reverse_cons, List.map_append, operatorSequence_append]
      simp only [List.map_singleton, operatorSequence, Matrix.one_mul]
      rw [inductionHypothesis]
      simp

theorem sourcePlanOperator_inversePlan119
    {qubits : Nat} (symbolValue : String → ℝ)
    (plan : List (ExternallyControlledPrimitivePlan qubits)) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator symbolValue
        (ExternallyControlledPrimitivePlan.inversePlan plan) =
      star (ExternallyControlledPrimitivePlan.sourcePlanOperator
        symbolValue plan) := by
  unfold ExternallyControlledPrimitivePlan.inversePlan
    ExternallyControlledPrimitivePlan.sourcePlanOperator
  rw [List.map_map]
  have mapped :
      plan.reverse.map
          (ExternallyControlledPrimitivePlan.sourceOperator symbolValue ∘
            ExternallyControlledPrimitivePlan.inverse) =
        (plan.map
          (ExternallyControlledPrimitivePlan.sourceOperator symbolValue)).reverse.map star := by
    simp only [List.map_reverse, List.map_map]
    apply congrArg List.reverse
    apply List.map_congr_left
    intro leaf _member
    exact sourceOperator_inverse119 symbolValue leaf
  rw [mapped]
  exact operatorSequence_reverse_map_star119 _

theorem shuklaUniformInverseSourceOperator119
    (parameters : UniformPreparationParameters) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (shuklaVedulaWidthOnlyUniformInversePlan parameters) =
      star (shuklaVedulaWidthOnlyUniformStrictOperator (fun _ => 0) parameters) := by
  unfold shuklaVedulaWidthOnlyUniformInversePlan
    shuklaVedulaWidthOnlyUniformStrictOperator
  exact sourcePlanOperator_inversePlan119 (fun _ => 0)
    (shuklaVedulaWidthOnlyUniformPlan parameters)

theorem shuklaUniformInverse_zero_entry119
    (parameters : UniformPreparationParameters)
    (input : QubitBasis parameters.width) :
    ExternallyControlledPrimitivePlan.sourcePlanOperator (fun _ => 0)
        (shuklaVedulaWidthOnlyUniformInversePlan parameters)
        (fun _ => false) input =
      if qubitBasisLittleEndianIndex parameters.width input <
          parameters.validCount then
        (1 / Real.sqrt parameters.validCount : ℝ)
      else 0 := by
  rw [shuklaUniformInverseSourceOperator119]
  have forward := congrFun
    (applyOperator_shuklaVedulaWidthOnlyUniformStrictOperator_zeroKet parameters)
    input
  simp only [applyOperator_basisKet] at forward
  rw [Matrix.star_apply, forward]
  by_cases inside : qubitBasisLittleEndianIndex parameters.width input <
      parameters.validCount <;>
    simp [uniformPreparationTargetState, inside]

theorem uniformInverseStrict_clean_entry119
    {targetQubits : Nat}
    (parameters : UniformPreparationParameters)
    (layout : ExternallyControlledCircuitLayout parameters.width targetQubits)
    (valid : layout.CleanWorkValid)
    (output input : QubitBasis targetQubits)
    (clean : externallyControlledCleanWorkPredicate
      valid input) :
    ExternallyControlledPrimitivePlan.strictPlanOperator (fun _ => 0)
        layout (shuklaVedulaWidthOnlyUniformInversePlan parameters) output input =
      externallyControlledWireLiftOperator
        layout (star (shuklaVedulaWidthOnlyUniformStrictOperator (fun _ => 0)
          parameters)) output input := by
  let plan := shuklaVedulaWidthOnlyUniformInversePlan parameters
  have inside : basisKet input ∈ SubspaceMapComponent.basisSpan
      (externallyControlledCleanWorkPredicate valid) := by
    apply SubspaceMapComponent.basisKet_mem_basisSpan
    exact clean
  have cleanAgreement :=
    ExternallyControlledPrimitivePlan.strictPlanOperator_apply_eq_semanticPlanOperator_of_mem
      (fun _ => 0) layout valid plan (basisKet input) inside
  have entryAgreement := congrFun cleanAgreement output
  simp only [applyOperator_basisKet] at entryAgreement
  dsimp [plan] at entryAgreement ⊢
  rw [entryAgreement,
    ExternallyControlledPrimitivePlan.semanticPlanOperator_eq_controlledWireLift,
    shuklaUniformInverseSourceOperator119]

end
end ExecutableHistoryExecutableHistory
