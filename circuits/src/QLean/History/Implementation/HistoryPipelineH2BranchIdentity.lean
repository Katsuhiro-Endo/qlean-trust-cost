import QLean.History.Implementation.HistoryPipelineCorrectedBranchBasis
import QLean.History.Implementation.HistoryPipelineCorrectedP05Circuit

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

def h2AfterSelector119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  historyTaylorSelectorEqualityBasisAction layout input

def h2AfterTime119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  historyTaylorTimeComparisonBasisAction layout (h2AfterSelector119 layout input)

def h2AfterIdleEnd119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  historyTaylorIdleEndComparisonBasisAction layout (h2AfterTime119 layout input)

def h2BeforeQ119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  historyTaylorActiveConjunctionBasisAction layout (h2AfterIdleEnd119 layout input)

theorem h2BeforeOperators_apply_basisKet119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    VerifiedCircuitCore.applyOperator
        (VerifiedCircuitCore.operatorSequence
          [historyTaylorSelectorEqualityOperator layout,
           historyTaylorTimeComparisonOperator layout,
           historyTaylorIdleEndComparisonOperator layout,
           historyTaylorActiveConjunctionOperator layout])
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input) := by
  simp only [VerifiedCircuitCore.operatorSequence,
    VerifiedCircuitCore.applyOperator_mul, Matrix.one_mul]
  simp only [historyTaylorSelectorEqualityOperator,
    historyTaylorTimeComparisonOperator,
    historyTaylorIdleEndComparisonOperator,
    historyTaylorActiveConjunctionOperator,
    applyOperator_deterministicOperator_basisKet]
  rfl

theorem h2BeforeQ119_active_false_of_selector_false
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input)
    (selectorFalse :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 1 input = false) :
    h2BeforeQ119 layout input (historyActiveWire layout) = false := by
  have branchFalse :
      h2AfterIdleEnd119 layout input (historyBranchWire layout) = false := by
    have afterSelector :=
      historyTaylorSelectorEqualityBasisAction_maps_phase layout input auxiliary
    have afterTime := historyTaylorTimeComparisonBasisAction_maps_phase
      layout (h2AfterSelector119 layout input) afterSelector
    have afterIdle := historyTaylorIdleEndComparisonBasisAction_maps_phase
      layout (h2AfterTime119 layout input) afterTime
    unfold h2AfterIdleEnd119
    rw [afterIdle.1]
    unfold historyTaylorIdleEndComparisonBasisAction
    rw [layout.selectorEqualsNat_xorWire_workspace
      (historyLessThanIdleEndWire layout)
      (historyLessThanIdleEndWire_mem_workspace layout)]
    unfold h2AfterTime119 historyTaylorTimeComparisonBasisAction
    rw [layout.selectorEqualsNat_xorWire_workspace
      (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_mem_workspace layout)]
    unfold h2AfterSelector119 historyTaylorSelectorEqualityBasisAction
      ClassicalReversibleStage.equalityToConstantDirectBasisAction
    rw [layout.selectorEqualsNat_xorWire_workspace
      (historyBranchWire layout) (historyBranchWire_mem_workspace layout)]
    exact selectorFalse
  have afterSelector :=
    historyTaylorSelectorEqualityBasisAction_maps_phase layout input auxiliary
  have afterTime := historyTaylorTimeComparisonBasisAction_maps_phase
    layout (h2AfterSelector119 layout input) afterSelector
  have afterIdle := historyTaylorIdleEndComparisonBasisAction_maps_phase
    layout (h2AfterTime119 layout input) afterTime
  have afterActive := historyTaylorActiveConjunctionBasisAction_maps_phase
    layout (h2AfterIdleEnd119 layout input) afterIdle
  unfold h2BeforeQ119
  rw [afterActive.2.2.2.1]
  unfold historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
  rw [xorWire_apply_other _ (historyBranchWire layout)
      (historyBranchWire_ne_activeWire layout),
    xorWire_apply_other _ (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_ne_activeWire layout), branchFalse]
  rfl

theorem executableH2Q10_apply_basisKet_of_active_false119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (activeFalse :
      input (historyActiveWire (ExecutableLayout119 source domain)) = false) :
    VerifiedCircuitCore.applyOperator
        (h2ControlledQ10CleanOperator
          (historyP15ControlledQ10UnderstandingSpecification
            source.qParameters (ExecutableLayout119 source domain)
            (ExecutableAdmissible119 source domain).placementWidths))
        (VerifiedCircuitCore.basisKet input) = VerifiedCircuitCore.basisKet input := by
  unfold h2ControlledQ10CleanOperator r12ControlledSubcircuitCleanOperator
  rw [ExternallyControlledPrimitivePlan.semanticPlanOperator_eq_controlledWireLift]
  funext output
  rw [VerifiedCircuitCore.applyOperator_basisKet,
    externallyControlledWireLiftOperator_apply]
  change (if input (historyActiveWire (ExecutableLayout119 source domain)) = true
      then _ else if output = input then 1 else 0) = _
  simp [activeFalse, VerifiedCircuitCore.basisKet]

theorem historyTaylorSelectorEqualityBasisAction_involutive119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    historyTaylorSelectorEqualityBasisAction layout
        (historyTaylorSelectorEqualityBasisAction layout input) = input := by
  unfold historyTaylorSelectorEqualityBasisAction
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [layout.selectorEqualsNat_xorWire_workspace
    (historyBranchWire layout) (historyBranchWire_mem_workspace layout)]
  funext wire
  by_cases equal : wire = historyBranchWire layout
  · subst wire
    simp [xorWire]
  · simp [xorWire, equal]

theorem historyTaylorTimeComparisonBasisAction_involutive119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    historyTaylorTimeComparisonBasisAction layout
        (historyTaylorTimeComparisonBasisAction layout input) = input := by
  unfold historyTaylorTimeComparisonBasisAction
    historyTaylorClockLessThanTimeValue
  rw [layout.clock_read_xorWire_workspace
    (historyLessThanTimeWire layout)
    (historyLessThanTimeWire_mem_workspace layout)]
  funext wire
  by_cases equal : wire = historyLessThanTimeWire layout
  · subst wire
    simp [xorWire]
  · simp [xorWire, equal]

theorem historyTaylorIdleEndComparisonBasisAction_involutive119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    historyTaylorIdleEndComparisonBasisAction layout
        (historyTaylorIdleEndComparisonBasisAction layout input) = input := by
  unfold historyTaylorIdleEndComparisonBasisAction
    historyTaylorClockLessThanIdleEndValue
  rw [layout.clock_read_xorWire_workspace
    (historyLessThanIdleEndWire layout)
    (historyLessThanIdleEndWire_mem_workspace layout)]
  funext wire
  by_cases equal : wire = historyLessThanIdleEndWire layout
  · subst wire
    simp [xorWire]
  · simp [xorWire, equal]

theorem historyTaylorActiveConjunctionBasisAction_involutive119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    historyTaylorActiveConjunctionBasisAction layout
        (historyTaylorActiveConjunctionBasisAction layout input) = input := by
  unfold historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction
  have branchOther := xorWire_apply_other (historyActiveWire layout)
    (historyBranchWire layout) (historyBranchWire_ne_activeWire layout)
    ([input (historyBranchWire layout),
      input (historyLessThanTimeWire layout)].all id) input
  have timeOther := xorWire_apply_other (historyActiveWire layout)
    (historyLessThanTimeWire layout) (historyLessThanTimeWire_ne_activeWire layout)
    ([input (historyBranchWire layout),
      input (historyLessThanTimeWire layout)].all id) input
  have conditionStable :
      ClassicalReversibleStage.allWiresTrue
          [historyBranchWire layout, historyLessThanTimeWire layout]
          (xorWire (historyActiveWire layout)
            (ClassicalReversibleStage.allWiresTrue
              [historyBranchWire layout, historyLessThanTimeWire layout] input)
            input) =
        ClassicalReversibleStage.allWiresTrue
          [historyBranchWire layout, historyLessThanTimeWire layout] input := by
    simp only [ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires]
    simp only [List.map_cons, List.map_nil]
    rw [branchOther, timeOther]
  rw [conditionStable]
  funext wire
  by_cases equal : wire = historyActiveWire layout
  · subst wire
    simp [xorWire]
  · simp [xorWire, equal]

theorem historyTaylorInvalidClockOperator_apply_basisKet_of_branch_false119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (branchFalse : input (historyBranchWire layout) = false) :
    VerifiedCircuitCore.applyOperator (historyTaylorInvalidClockOperator layout)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  rw [historyTaylorInvalidClockOperator,
    applyOperator_deterministicOperator_basisKet]
  congr 1
  funext wire
  simp [historyTaylorInvalidClockBasisAction,
    historyTaylorInvalidClockCondition, branchFalse, xorWire]

theorem historyTaylorOrderBoundaryOperator_apply_basisKet_of_branch_false119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (branchFalse : input (historyBranchWire layout) = false) :
    VerifiedCircuitCore.applyOperator (historyTaylorOrderBoundaryOperator layout)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  rw [historyTaylorOrderBoundaryOperator,
    applyOperator_deterministicOperator_basisKet]
  congr 1
  funext wire
  simp [historyTaylorOrderBoundaryBasisAction,
    historyTaylorOrderBoundaryCondition, branchFalse, xorWire]

theorem historyTaylorIdleBoundaryOperator_apply_basisKet_of_branch_false119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (branchFalse : input (historyBranchWire layout) = false) :
    VerifiedCircuitCore.applyOperator (historyTaylorIdleBoundaryOperator layout)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  rw [historyTaylorIdleBoundaryOperator,
    applyOperator_deterministicOperator_basisKet]
  congr 1
  funext wire
  simp [historyTaylorIdleBoundaryBasisAction,
    historyTaylorIdleBoundaryCondition, branchFalse, xorWire]

theorem historyTaylorDegreeIncrementOperator_apply_basisKet_of_branch_false119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (branchFalse : input (historyBranchWire layout) = false) :
    VerifiedCircuitCore.applyOperator (historyTaylorDegreeIncrementOperator layout)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  rw [historyTaylorDegreeIncrementOperator,
    predicateControlledAddMod2PowOperator,
    applyOperator_deterministicOperator_basisKet]
  congr 1
  simp [historyTaylorDegreeIncrementCondition, branchFalse,
    predicateControlledAddMod2PowBasisAction]

theorem applyOperator_predicateControlledSingleQubitOperator_basisKet_of_false119
    {qubits : Nat}
    (predicate : QubitBasis qubits → Bool)
    (target : Fin qubits)
    (localOperator : Matrix Bool Bool ℂ)
    (input : QubitBasis qubits)
    (predicateFalse : predicate input = false) :
    VerifiedCircuitCore.applyOperator
        (predicateControlledSingleQubitOperator predicate target localOperator)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  funext output
  rw [VerifiedCircuitCore.applyOperator_basisKet,
    predicateControlledSingleQubitOperator_apply]
  simp only [predicateFalse, Bool.false_eq_true, ↓reduceIte,
    VerifiedCircuitCore.basisKet]
  by_cases agrees : agreesExcept target output input
  · by_cases targetEqual : output target = input target
    · have equal : output = input := by
        funext wire
        by_cases isTarget : wire = target
        · simpa [isTarget] using targetEqual
        · exact agrees wire isTarget
      subst output
      simp [agreesExcept]
    · have different : output ≠ input := by
        intro equal
        exact targetEqual (congrFun equal target)
      simp [agrees, targetEqual, different]
  · have different : output ≠ input := by
      intro equal
      apply agrees
      subst output
      exact fun _ _ => rfl
    simp [agrees, different]

theorem applyOperator_operatorSequence_basisKet_of_each_fixed119
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operators : List (VerifiedCircuitCore.Operator basis)) (input : basis)
    (fixed : ∀ operator, operator ∈ operators →
      VerifiedCircuitCore.applyOperator operator (VerifiedCircuitCore.basisKet input) =
        VerifiedCircuitCore.basisKet input) :
    VerifiedCircuitCore.applyOperator
        (VerifiedCircuitCore.operatorSequence operators)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  induction operators with
  | nil =>
      change Matrix.mulVec 1 (VerifiedCircuitCore.basisKet input) =
        VerifiedCircuitCore.basisKet input
      exact Matrix.one_mulVec _
  | cons first rest inductionHypothesis =>
      simp only [VerifiedCircuitCore.operatorSequence,
        VerifiedCircuitCore.applyOperator_mul]
      rw [fixed first (by simp)]
      apply inductionHypothesis
      intro operator member
      exact fixed operator (by simp [member])

theorem historyTaylorCoefficientLoopOperator_apply_basisKet_of_branch_false119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (input : QubitBasis qubits)
    (branchFalse : input (historyBranchWire layout) = false) :
    VerifiedCircuitCore.applyOperator
      (historyTaylorCoefficientLoopOperator layout angles)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  unfold historyTaylorCoefficientLoopOperator
  apply applyOperator_operatorSequence_basisKet_of_each_fixed119
  intro operator member
  simp only [List.mem_map] at member
  rcases member with ⟨index, _, rfl⟩
  apply applyOperator_predicateControlledSingleQubitOperator_basisKet_of_false119
  simp [branchFalse]

theorem historyTaylorIdleCoefficientOperator_apply_basisKet_of_branch_false119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : VerifiedCircuitCore.AngleExpr)
    (input : QubitBasis qubits)
    (branchFalse : input (historyBranchWire layout) = false) :
    VerifiedCircuitCore.applyOperator
      (historyTaylorIdleCoefficientOperator layout angle)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  unfold historyTaylorIdleCoefficientOperator
  apply applyOperator_predicateControlledSingleQubitOperator_basisKet_of_false119
  simp [branchFalse]

theorem h2RestoreEntryFlags_apply_basisKet119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits) :
    VerifiedCircuitCore.applyOperator
        (VerifiedCircuitCore.operatorSequence
          [historyTaylorIdleEndComparisonOperator layout,
           historyTaylorTimeComparisonOperator layout,
           historyTaylorSelectorEqualityOperator layout])
        (VerifiedCircuitCore.basisKet (h2AfterIdleEnd119 layout input)) =
      VerifiedCircuitCore.basisKet input := by
  simp only [VerifiedCircuitCore.operatorSequence,
    VerifiedCircuitCore.applyOperator_mul, Matrix.one_mul,
    historyTaylorIdleEndComparisonOperator,
    historyTaylorTimeComparisonOperator,
    historyTaylorSelectorEqualityOperator,
    applyOperator_deterministicOperator_basisKet]
  rw [show historyTaylorIdleEndComparisonBasisAction layout
      (h2AfterIdleEnd119 layout input) = h2AfterTime119 layout input by
    exact historyTaylorIdleEndComparisonBasisAction_involutive119
      layout (h2AfterTime119 layout input)]
  rw [show historyTaylorTimeComparisonBasisAction layout
      (h2AfterTime119 layout input) = h2AfterSelector119 layout input by
    exact historyTaylorTimeComparisonBasisAction_involutive119
      layout (h2AfterSelector119 layout input)]
  rw [show historyTaylorSelectorEqualityBasisAction layout
      (h2AfterSelector119 layout input) = input by
    exact historyTaylorSelectorEqualityBasisAction_involutive119 layout input]

theorem h2AfterIdleEnd119_branch_false_of_selector_false119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input)
    (selectorFalse :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 1 input = false) :
    h2AfterIdleEnd119 layout input (historyBranchWire layout) = false := by
  have afterSelector :=
    historyTaylorSelectorEqualityBasisAction_maps_phase layout input auxiliary
  have afterTime := historyTaylorTimeComparisonBasisAction_maps_phase
    layout (h2AfterSelector119 layout input) afterSelector
  have afterIdle := historyTaylorIdleEndComparisonBasisAction_maps_phase
    layout (h2AfterTime119 layout input) afterTime
  unfold h2AfterIdleEnd119
  rw [afterIdle.1]
  unfold historyTaylorIdleEndComparisonBasisAction
  rw [layout.selectorEqualsNat_xorWire_workspace
    (historyLessThanIdleEndWire layout)
    (historyLessThanIdleEndWire_mem_workspace layout)]
  unfold h2AfterTime119 historyTaylorTimeComparisonBasisAction
  rw [layout.selectorEqualsNat_xorWire_workspace
    (historyLessThanTimeWire layout)
    (historyLessThanTimeWire_mem_workspace layout)]
  unfold h2AfterSelector119 historyTaylorSelectorEqualityBasisAction
    ClassicalReversibleStage.equalityToConstantDirectBasisAction
  rw [layout.selectorEqualsNat_xorWire_workspace
    (historyBranchWire layout) (historyBranchWire_mem_workspace layout)]
  exact selectorFalse

theorem h2PostOperators_apply_basisKet_of_selector_false119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr)
    (input : QubitBasis qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout input)
    (selectorFalse :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 1 input = false) :
    VerifiedCircuitCore.applyOperator
        (VerifiedCircuitCore.operatorSequence
          [historyTaylorActiveConjunctionOperator layout,
           historyTaylorInvalidClockOperator layout,
           historyTaylorOrderBoundaryOperator layout,
           historyTaylorIdleBoundaryOperator layout,
           historyTaylorDegreeIncrementOperator layout,
           historyTaylorCoefficientLoopOperator layout angles,
           historyTaylorIdleCoefficientOperator layout idleAngle,
           VerifiedCircuitCore.operatorSequence
             [historyTaylorIdleEndComparisonOperator layout,
              historyTaylorTimeComparisonOperator layout,
              historyTaylorSelectorEqualityOperator layout]])
        (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input)) =
      VerifiedCircuitCore.basisKet input := by
  have branchFalse := h2AfterIdleEnd119_branch_false_of_selector_false119
    layout input auxiliary selectorFalse
  simp only [VerifiedCircuitCore.operatorSequence,
    VerifiedCircuitCore.applyOperator_mul, Matrix.one_mul]
  rw [show VerifiedCircuitCore.applyOperator
      (historyTaylorActiveConjunctionOperator layout)
      (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input)) =
        VerifiedCircuitCore.basisKet (h2AfterIdleEnd119 layout input) by
    rw [historyTaylorActiveConjunctionOperator,
      applyOperator_deterministicOperator_basisKet]
    exact congrArg VerifiedCircuitCore.basisKet
      (historyTaylorActiveConjunctionBasisAction_involutive119
        layout (h2AfterIdleEnd119 layout input))]
  rw [historyTaylorInvalidClockOperator_apply_basisKet_of_branch_false119
    layout _ branchFalse]
  rw [historyTaylorOrderBoundaryOperator_apply_basisKet_of_branch_false119
    layout _ branchFalse]
  rw [historyTaylorIdleBoundaryOperator_apply_basisKet_of_branch_false119
    layout _ branchFalse]
  rw [historyTaylorDegreeIncrementOperator_apply_basisKet_of_branch_false119
    layout _ branchFalse]
  rw [historyTaylorCoefficientLoopOperator_apply_basisKet_of_branch_false119
    layout angles _ branchFalse]
  rw [historyTaylorIdleCoefficientOperator_apply_basisKet_of_branch_false119
    layout idleAngle _ branchFalse]
  simpa only [VerifiedCircuitCore.operatorSequence,
    VerifiedCircuitCore.applyOperator_mul, Matrix.one_mul] using
    h2RestoreEntryFlags_apply_basisKet119 layout input

theorem executableH2Clean_apply_basisKet_of_selector_false119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (angles : Fin source.historyParameters.taylorOrder →
      VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (auxiliary : historyTaylorAuxiliaryBoundaryPredicate
      (ExecutableLayout119 source domain) input)
    (selectorFalse :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires (ExecutableLayout119 source domain).selector) 1
        input = false) :
    VerifiedCircuitCore.applyOperator
        (h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification
            (ExecutableLayout119 source domain)
            (ScientificWidthGenericContract.correctedCleanEvidence259
              (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
            (ExecutableAdmissible119 source domain).placementWidths
            angles idleAngle))
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  let layout := ExecutableLayout119 source domain
  let clean := ScientificWidthGenericContract.correctedCleanEvidence259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  unfold h2TaylorCleanOperator
  rw [h2TaylorCleanSourceOperators_historyP15_eq]
  change VerifiedCircuitCore.applyOperator
    (VerifiedCircuitCore.operatorSequence
      ([historyTaylorSelectorEqualityOperator layout,
        historyTaylorTimeComparisonOperator layout,
        historyTaylorIdleEndComparisonOperator layout,
        historyTaylorActiveConjunctionOperator layout,
        h2ControlledQ10CleanOperator
          (historyP15ControlledQ10UnderstandingSpecification
            source.qParameters layout widths)] ++
       [historyTaylorActiveConjunctionOperator layout,
        historyTaylorInvalidClockOperator layout,
        historyTaylorOrderBoundaryOperator layout,
        historyTaylorIdleBoundaryOperator layout,
        historyTaylorDegreeIncrementOperator layout,
        historyTaylorCoefficientLoopOperator layout angles,
        historyTaylorIdleCoefficientOperator layout idleAngle,
        VerifiedCircuitCore.operatorSequence
          [historyTaylorIdleEndComparisonOperator layout,
           historyTaylorTimeComparisonOperator layout,
           historyTaylorSelectorEqualityOperator layout]]))
      (VerifiedCircuitCore.basisKet input) = VerifiedCircuitCore.basisKet input
  rw [VerifiedCircuitCore.operatorSequence_append,
    VerifiedCircuitCore.applyOperator_mul]
  rw [show VerifiedCircuitCore.applyOperator
      (VerifiedCircuitCore.operatorSequence
        [historyTaylorSelectorEqualityOperator layout,
         historyTaylorTimeComparisonOperator layout,
         historyTaylorIdleEndComparisonOperator layout,
         historyTaylorActiveConjunctionOperator layout,
         h2ControlledQ10CleanOperator
           (historyP15ControlledQ10UnderstandingSpecification
             source.qParameters layout widths)])
      (VerifiedCircuitCore.basisKet input) =
        VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input) by
    rw [show [historyTaylorSelectorEqualityOperator layout,
        historyTaylorTimeComparisonOperator layout,
        historyTaylorIdleEndComparisonOperator layout,
        historyTaylorActiveConjunctionOperator layout,
        h2ControlledQ10CleanOperator
          (historyP15ControlledQ10UnderstandingSpecification
            source.qParameters layout widths)] =
      [historyTaylorSelectorEqualityOperator layout,
       historyTaylorTimeComparisonOperator layout,
       historyTaylorIdleEndComparisonOperator layout,
       historyTaylorActiveConjunctionOperator layout] ++
      [h2ControlledQ10CleanOperator
        (historyP15ControlledQ10UnderstandingSpecification
          source.qParameters layout widths)] by rfl]
    rw [VerifiedCircuitCore.operatorSequence_append]
    rw [show VerifiedCircuitCore.operatorSequence
        [h2ControlledQ10CleanOperator
          (historyP15ControlledQ10UnderstandingSpecification
            source.qParameters layout widths)] =
      h2ControlledQ10CleanOperator
        (historyP15ControlledQ10UnderstandingSpecification
          source.qParameters layout widths) by
      simp [VerifiedCircuitCore.operatorSequence]]
    rw [VerifiedCircuitCore.applyOperator_mul]
    rw [h2BeforeOperators_apply_basisKet119 layout input]
    exact executableH2Q10_apply_basisKet_of_active_false119
      source domain (h2BeforeQ119 layout input)
      (h2BeforeQ119_active_false_of_selector_false
        layout input auxiliary selectorFalse)]
  exact h2PostOperators_apply_basisKet_of_selector_false119
    layout angles idleAngle input auxiliary selectorFalse

theorem correctedBranchH2_identity119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (branch : Fin 4)
    (index : OldHistoryIndex119 source)
    (branchNeOne : branch.val ≠ 1) :
    VerifiedCircuitCore.applyOperator
        (h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification
            (ExecutableLayout119 source domain)
            (ScientificWidthGenericContract.correctedCleanEvidence259
              (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
            (ExecutableAdmissible119 source domain).placementWidths
            (fun degree => correctedTaylorCoefficientAngle119
              source.toCommonSource119 degree.val)
            compiledIdleCoefficientAngle119))
        (VerifiedCircuitCore.basisKet
          (correctedBranchHistoryBasis119 source domain fits branch index)) =
      VerifiedCircuitCore.basisKet
        (correctedBranchHistoryBasis119 source domain fits branch index) := by
  apply executableH2Clean_apply_basisKet_of_selector_false119
  · exact correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits branch index
  · rw [correctedBranchHistoryBasis119_selector_one]
    simp [branchNeOne]

end
end ExecutableHistoryExecutableHistory
