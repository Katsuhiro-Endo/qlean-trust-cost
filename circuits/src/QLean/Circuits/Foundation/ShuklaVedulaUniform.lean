import QLean.Circuits.Foundation.ControlledCircuitCompiler
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.ShuklaVedulaUniformAnalytic

/-!
# Width-only Shukla--Vedula uniform compiler

The source-order primitive implementation and its full-space strict target are
kept separate from the all-zero-input uniform-state semantic theorem.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Total six-constructor re-encoding used by the width-only source plan.
The analytic Z/Rz words are normalized to the PhaseShift vocabulary before they
reach the executable primitive AST. -/
def ExternallyControlledPrimitivePlan.normalizedPrimitive {qubits : Nat} :
    ExternallyControlledPrimitivePlan qubits → PrimitiveGate qubits
  | .x target => .x target
  | .z target => .phaseShift .pi target
  | .h target => .h target
  | .ry angle target => .ry angle target
  | .phaseShift angle target => .phaseShift angle target
  | .rz angle target => .phaseShift angle target
  | .cnot control target different => .cnot control target different
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent
      secondDifferent =>
      .toffoli control₀ control₁ target controlsDifferent firstDifferent
        secondDifferent

/-- The Shukla--Vedula source generators use only the executable six-constructor
core.  Z/Rz remain available in the independent analytic plan for other users. -/
def ExternallyControlledPrimitivePlan.IsNormalizedCorePlan {qubits : Nat} :
    ExternallyControlledPrimitivePlan qubits → Prop
  | .x _ | .h _ | .ry _ _ | .phaseShift _ _ | .cnot _ _ _ |
      .toffoli _ _ _ _ _ _ => True
  | .z _ | .rz _ _ => False

@[simp] theorem ExternallyControlledPrimitivePlan.normalizedPrimitive_supported
    {qubits : Nat} (plan : ExternallyControlledPrimitivePlan qubits) :
    IsExternallyControllablePrimitive plan.normalizedPrimitive := by
  cases plan <;>
    simp [ExternallyControlledPrimitivePlan.normalizedPrimitive,
      IsExternallyControllablePrimitive]

theorem ExternallyControlledPrimitivePlan.sourceNormalizedCircuit_eq_gate_normalizedPrimitive
    {qubits : Nat} (plan : ExternallyControlledPrimitivePlan qubits)
    (core : plan.IsNormalizedCorePlan) :
    plan.sourceNormalizedCircuit = .gate plan.normalizedPrimitive := by
  cases plan <;>
    simp [ExternallyControlledPrimitivePlan.IsNormalizedCorePlan,
      ExternallyControlledPrimitivePlan.sourceNormalizedCircuit,
      ExternallyControlledPrimitivePlan.normalizedPrimitive] at core ⊢

theorem ExternallyControlledPrimitivePlan.ofPrimitive_normalizedPrimitive_of_core
    {qubits : Nat} (plan : ExternallyControlledPrimitivePlan qubits)
    (core : plan.IsNormalizedCorePlan) :
    ExternallyControlledPrimitivePlan.ofPrimitive plan.normalizedPrimitive
        plan.normalizedPrimitive_supported = plan := by
  cases plan <;>
    simp [ExternallyControlledPrimitivePlan.IsNormalizedCorePlan,
      ExternallyControlledPrimitivePlan.normalizedPrimitive,
      ExternallyControlledPrimitivePlan.ofPrimitive] at core ⊢

theorem ExternallyControlledPrimitivePlan.sourceNormalizedCircuit_hasOnlyExternallyControllablePrimitives
    {qubits : Nat} (plan : ExternallyControlledPrimitivePlan qubits) :
    ∀ gate, gate ∈ plan.sourceNormalizedCircuit.flatten →
      IsExternallyControllablePrimitive gate := by
  cases plan <;>
    simp [ExternallyControlledPrimitivePlan.sourceNormalizedCircuit,
      phaseShiftRzCircuit, Circuit.flatten, IsExternallyControllablePrimitive]

theorem controlledRySourcePlan_isNormalizedCore
    {width : Nat} (control target : Fin width) (angle : AngleExpr) :
    ∀ leaf ∈ controlledRySourcePlan control target angle,
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan leaf := by
  classical
  by_cases different : control ≠ target <;>
    simp [controlledRySourcePlan, different,
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan]

theorem controlledHadamardSourcePlan_isNormalizedCore
    {width : Nat} (control target : Fin width) :
    ∀ leaf ∈ controlledHadamardSourcePlan control target,
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan leaf := by
  classical
  by_cases different : control ≠ target <;>
    simp [controlledHadamardSourcePlan, different,
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan]

theorem zeroControlledRySourcePlan_isNormalizedCore
    {width : Nat} (control target : Fin width) (angle : AngleExpr) :
    ∀ leaf ∈ zeroControlledRySourcePlan control target angle,
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan leaf := by
  classical
  by_cases different : control ≠ target <;>
    simp [zeroControlledRySourcePlan, controlledRySourcePlan, different,
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan]

theorem zeroControlledHadamardSourcePlan_isNormalizedCore
    {width : Nat} (control target : Fin width) :
    ∀ leaf ∈ zeroControlledHadamardSourcePlan control target,
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan leaf := by
  classical
  by_cases different : control ≠ target <;>
    simp [zeroControlledHadamardSourcePlan, controlledHadamardSourcePlan,
      different, ExternallyControlledPrimitivePlan.IsNormalizedCorePlan]
theorem shuklaVedulaUniformTailPlan_isNormalizedCore
    {width : Nat} (validCount accumulated : Nat) :
    (locations : List (Fin width)) →
    ∀ leaf ∈ shuklaVedulaUniformTailPlan validCount accumulated locations,
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan leaf
  | [] => by simp [shuklaVedulaUniformTailPlan]
  | [_] => by simp [shuklaVedulaUniformTailPlan]
  | current :: next :: rest => by
      intro leaf member
      simp only [shuklaVedulaUniformTailPlan] at member
      rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact zeroControlledRySourcePlan_isNormalizedCore current next _ leaf member
        · rcases List.mem_flatMap.mp member with ⟨wire, _, member⟩
          exact zeroControlledHadamardSourcePlan_isNormalizedCore next wire leaf
            member
      · exact shuklaVedulaUniformTailPlan_isNormalizedCore validCount
          (accumulated + 2 ^ current.val) (next :: rest) leaf member
termination_by locations => locations.length

theorem shuklaVedulaWidthOnlyUniformPlan_isNormalizedCore
    (parameters : UniformPreparationParameters) :
    ∀ leaf ∈ shuklaVedulaWidthOnlyUniformPlan parameters,
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan leaf := by
  classical
  by_cases full : parameters.validCount = 2 ^ parameters.width
  · simp [shuklaVedulaWidthOnlyUniformPlan, full,
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan]
  · have strictBound : parameters.validCount < 2 ^ parameters.width :=
      lt_of_le_of_ne parameters.validCountLeCapacity full
    unfold shuklaVedulaWidthOnlyUniformPlan
    simp [full]
    generalize widthOnlyUniformOneLocationsOfStrictBound
        parameters.width parameters.validCount strictBound = locations
    cases locations with
    | nil => simp
    | cons only rest =>
        cases rest with
        | nil =>
            simp [ExternallyControlledPrimitivePlan.IsNormalizedCorePlan]
        | cons second rest =>
            intro leaf member
            simp only [List.mem_cons, List.mem_append] at member
            rcases member with member | member
            · subst leaf
              simp [ExternallyControlledPrimitivePlan.IsNormalizedCorePlan]
            · rcases member with member | member
              · rcases List.mem_map.mp member with ⟨wire, _, rfl⟩
                simp [ExternallyControlledPrimitivePlan.IsNormalizedCorePlan]
              · rcases member with member | member
                · rcases List.mem_map.mp member with ⟨wire, _, rfl⟩
                  simp [ExternallyControlledPrimitivePlan.IsNormalizedCorePlan]
                · rcases member with member | member
                  · subst leaf
                    simp [ExternallyControlledPrimitivePlan.IsNormalizedCorePlan]
                  · rcases member with member | member
                    · rcases List.mem_flatMap.mp member with ⟨wire, _, member⟩
                      exact zeroControlledHadamardSourcePlan_isNormalizedCore
                        second wire leaf member
                    · exact shuklaVedulaUniformTailPlan_isNormalizedCore
                        parameters.validCount (2 ^ only.val)
                        (second :: rest) leaf member

/-- One source leaf as a full-space exact primitive component. -/
def ExternallyControlledPrimitivePlan.sourceExactOperatorComponent
    {qubits : Nat} (symbolValue : String → ℝ)
    (plan : ExternallyControlledPrimitivePlan qubits) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) where
  circuit := plan.sourceNormalizedCircuit
  target := plan.sourceOperator symbolValue
  correct := plan.sourceNormalizedCircuit_correct symbolValue

@[simp] theorem ExternallyControlledPrimitivePlan.sourceExactOperatorComponent_circuit
    {qubits : Nat} (symbolValue : String → ℝ)
    (plan : ExternallyControlledPrimitivePlan qubits) :
    (plan.sourceExactOperatorComponent symbolValue).circuit =
      plan.sourceNormalizedCircuit := rfl

/-- Canonical width-only primitive AST in exact source order. -/
def shuklaVedulaWidthOnlyUniformCircuit
    (parameters : UniformPreparationParameters) :
    Circuit (PrimitiveGate parameters.width) :=
  Circuit.sequence
    (((shuklaVedulaWidthOnlyUniformPlan parameters).map
      ExternallyControlledPrimitivePlan.normalizedPrimitive).map Circuit.gate)

/-- Full dirty-input strict target of the width-only source plan. -/
def shuklaVedulaWidthOnlyUniformStrictOperator
    (symbolValue : String → ℝ)
    (parameters : UniformPreparationParameters) :
    Operator (QubitBasis parameters.width) :=
  ExternallyControlledPrimitivePlan.sourcePlanOperator symbolValue
    (shuklaVedulaWidthOnlyUniformPlan parameters)

/-- Full-space Exact contract for the source-faithful width-only variant. -/
def shuklaVedulaWidthOnlyUniformFullExactOperatorComponent
    (symbolValue : String → ℝ)
    (parameters : UniformPreparationParameters) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := parameters.width) symbolValue) :=
  ExactOperatorComponent.sequence <|
    (shuklaVedulaWidthOnlyUniformPlan parameters).map fun leaf =>
      leaf.sourceExactOperatorComponent symbolValue

/-- The public Exact component exposes the canonical source-order AST. -/
theorem shuklaVedulaWidthOnlyUniformFullExactOperatorComponent_circuit
    (symbolValue : String → ℝ)
    (parameters : UniformPreparationParameters) :
    (shuklaVedulaWidthOnlyUniformFullExactOperatorComponent
      symbolValue parameters).circuit =
      shuklaVedulaWidthOnlyUniformCircuit parameters := by
  rw [shuklaVedulaWidthOnlyUniformFullExactOperatorComponent,
    ExactOperatorComponent.sequenceComponents_circuit]
  unfold shuklaVedulaWidthOnlyUniformCircuit
  have mapEq : ∀ (plans : List
      (ExternallyControlledPrimitivePlan parameters.width)),
      (∀ leaf, leaf ∈ plans →
        ExternallyControlledPrimitivePlan.IsNormalizedCorePlan leaf) →
      plans.map (fun leaf =>
        (leaf.sourceExactOperatorComponent symbolValue).circuit) =
      plans.map (fun leaf =>
        Circuit.gate leaf.normalizedPrimitive) := by
    intro plans
    induction plans with
    | nil =>
        intro _
        rfl
    | cons first rest inductionHypothesis =>
        intro core
        have firstCore := core first (by simp)
        have restCore : ∀ leaf, leaf ∈ rest →
            ExternallyControlledPrimitivePlan.IsNormalizedCorePlan leaf := by
          intro leaf member
          exact core leaf (by simp [member])
        simp only [List.map_cons]
        rw [first.sourceExactOperatorComponent_circuit symbolValue,
          first.sourceNormalizedCircuit_eq_gate_normalizedPrimitive firstCore,
          inductionHypothesis restCore]
  apply congrArg Circuit.sequence
  simpa [List.map_map, Function.comp_def] using
    mapEq (shuklaVedulaWidthOnlyUniformPlan parameters)
      (shuklaVedulaWidthOnlyUniformPlan_isNormalizedCore parameters)

/-- The public Exact component target is the independent source-plan
operator product. -/
theorem shuklaVedulaWidthOnlyUniformFullExactOperatorComponent_target
    (symbolValue : String → ℝ)
    (parameters : UniformPreparationParameters) :
    (shuklaVedulaWidthOnlyUniformFullExactOperatorComponent
      symbolValue parameters).target =
      shuklaVedulaWidthOnlyUniformStrictOperator symbolValue parameters := by
  rw [shuklaVedulaWidthOnlyUniformFullExactOperatorComponent,
    ExactOperatorComponent.sequence_target_eq_operatorSequence]
  unfold shuklaVedulaWidthOnlyUniformStrictOperator
    ExternallyControlledPrimitivePlan.sourcePlanOperator
  simp only [List.map_map]
  rfl

/-- The full strict source compiler is unitary on arbitrary dirty input. -/
def shuklaVedulaWidthOnlyUniformFullUnitaryExactOperatorComponent
    (symbolValue : String → ℝ)
    (parameters : UniformPreparationParameters) :
    UnitaryExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := parameters.width) symbolValue) :=
  ExactOperatorComponent.toUnitary
    (primitiveGateOperatorWithSymbols_mem_unitaryGroup symbolValue)
    (shuklaVedulaWidthOnlyUniformFullExactOperatorComponent
      symbolValue parameters)

/-- Every flattened source leaf is admitted by the external-control decoder. -/
theorem shuklaVedulaWidthOnlyUniformCircuit_hasOnlyExternallyControllablePrimitives
    (parameters : UniformPreparationParameters) :
    ∀ gate, gate ∈ (shuklaVedulaWidthOnlyUniformCircuit parameters).flatten →
      IsExternallyControllablePrimitive gate := by
  intro gate member
  unfold shuklaVedulaWidthOnlyUniformCircuit at member
  rw [Circuit.flatten_sequence_map_gate] at member
  rcases List.mem_map.mp member with ⟨leaf, _, rfl⟩
  exact leaf.normalizedPrimitive_supported

/-- The decoder recovers a normalized core plan from its six-constructor
re-encoding. -/
theorem decodeSupportedPrimitiveStream_normalizedPrimitive_of_core
    {qubits : Nat} (plans : List (ExternallyControlledPrimitivePlan qubits)) :
    ∀ (supported : ∀ gate, gate ∈ plans.map
        ExternallyControlledPrimitivePlan.normalizedPrimitive →
      IsExternallyControllablePrimitive gate),
      (∀ plan, plan ∈ plans →
        ExternallyControlledPrimitivePlan.IsNormalizedCorePlan plan) →
      decodeSupportedPrimitiveStream
          (plans.map ExternallyControlledPrimitivePlan.normalizedPrimitive)
          supported = plans := by
  induction plans with
  | nil =>
      intro _ _
      rfl
  | cons first rest inductionHypothesis =>
      intro supported core
      have firstCore := core first (by simp)
      have restSupported : ∀ gate, gate ∈ rest.map
          ExternallyControlledPrimitivePlan.normalizedPrimitive →
        IsExternallyControllablePrimitive gate := by
        intro gate member
        exact supported gate (by simp [member])
      have restCore : ∀ plan, plan ∈ rest →
          ExternallyControlledPrimitivePlan.IsNormalizedCorePlan plan := by
        intro plan member
        exact core plan (by simp [member])
      simp only [List.map_cons, decodeSupportedPrimitiveStream]
      rw [ExternallyControlledPrimitivePlan.ofPrimitive_normalizedPrimitive_of_core
        first firstCore]
      congr 1
      exact inductionHypothesis restSupported restCore

/-- The generic decoder recovers exactly the canonical source plan. -/
theorem decode_shuklaVedulaWidthOnlyUniformCircuit
    (parameters : UniformPreparationParameters) :
    decodeSupportedPrimitiveCircuit
        (shuklaVedulaWidthOnlyUniformCircuit parameters)
        (shuklaVedulaWidthOnlyUniformCircuit_hasOnlyExternallyControllablePrimitives
          parameters) =
      shuklaVedulaWidthOnlyUniformPlan parameters := by
  unfold decodeSupportedPrimitiveCircuit
  unfold shuklaVedulaWidthOnlyUniformCircuit
  simp only [Circuit.flatten_sequence_map_gate]
  apply decodeSupportedPrimitiveStream_normalizedPrimitive_of_core
    (shuklaVedulaWidthOnlyUniformPlan parameters)
  exact shuklaVedulaWidthOnlyUniformPlan_isNormalizedCore parameters

theorem ExternallyControlledPrimitivePlan.inverse_normalizedPrimitive_of_core
    {qubits : Nat} (plan : ExternallyControlledPrimitivePlan qubits)
    (core : plan.IsNormalizedCorePlan) :
    (plan.inverse).normalizedPrimitive =
      PrimitiveGate.inverse plan.normalizedPrimitive := by
  cases plan <;>
    simp [ExternallyControlledPrimitivePlan.IsNormalizedCorePlan,
      ExternallyControlledPrimitivePlan.inverse,
      ExternallyControlledPrimitivePlan.normalizedPrimitive,
      PrimitiveGate.inverse] at core ⊢

theorem ExternallyControlledPrimitivePlan.inversePlan_map_normalizedPrimitive_of_core
    {qubits : Nat} (plans : List (ExternallyControlledPrimitivePlan qubits))
    (core : ∀ plan, plan ∈ plans →
      ExternallyControlledPrimitivePlan.IsNormalizedCorePlan plan) :
    (ExternallyControlledPrimitivePlan.inversePlan plans).map
        ExternallyControlledPrimitivePlan.normalizedPrimitive =
      (plans.map ExternallyControlledPrimitivePlan.normalizedPrimitive).reverse.map
        PrimitiveGate.inverse := by
  induction plans with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      have firstCore := core first (by simp)
      have restCore : ∀ plan, plan ∈ rest →
          ExternallyControlledPrimitivePlan.IsNormalizedCorePlan plan := by
        intro plan member
        exact core plan (by simp [member])
      simp only [ExternallyControlledPrimitivePlan.inversePlan,
        List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      change
        (ExternallyControlledPrimitivePlan.inversePlan rest).map
            ExternallyControlledPrimitivePlan.normalizedPrimitive ++
          [first.inverse.normalizedPrimitive] =
        ((rest.map ExternallyControlledPrimitivePlan.normalizedPrimitive).reverse.map
            PrimitiveGate.inverse) ++
          [PrimitiveGate.inverse first.normalizedPrimitive]
      rw [inductionHypothesis restCore,
        ExternallyControlledPrimitivePlan.inverse_normalizedPrimitive_of_core
          first firstCore]

/-- The canonical inverse plan is source reverse order with every primitive
leaf inverted. -/
theorem shuklaVedulaWidthOnlyUniformInversePlan_sourceOrder
    (parameters : UniformPreparationParameters) :
    (shuklaVedulaWidthOnlyUniformInversePlan parameters).map
        ExternallyControlledPrimitivePlan.normalizedPrimitive =
      ((shuklaVedulaWidthOnlyUniformPlan parameters).map
        ExternallyControlledPrimitivePlan.normalizedPrimitive).reverse.map
          PrimitiveGate.inverse :=
  ExternallyControlledPrimitivePlan.inversePlan_map_normalizedPrimitive_of_core _
    (shuklaVedulaWidthOnlyUniformPlan_isNormalizedCore parameters)

/-- Externally controlled inverse compiler on the coherent clean-work span.
The target remains the independent work-preserving semantic plan product. -/
def shuklaVedulaWidthOnlyUniformInverseExternallyControlledCleanSubspaceMapComponent
    {targetQubits : Nat} (symbolValue : String → ℝ)
    (parameters : UniformPreparationParameters)
    (layout : ExternallyControlledCircuitLayout parameters.width targetQubits)
    (valid : layout.CleanWorkValid) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) :=
  externallyControlledCleanSubspaceMapComponent symbolValue layout valid
    (shuklaVedulaWidthOnlyUniformInversePlan parameters)

end

end VerifiedCircuitCore
