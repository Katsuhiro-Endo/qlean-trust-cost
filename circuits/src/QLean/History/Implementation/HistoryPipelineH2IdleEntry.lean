import QLean.History.Implementation.HistoryPipelineH2ActiveEntry

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

/-- Algebraic evaluation of the post-Q10 word on an idling-clock column.
The Taylor-coefficient loop is inactive and the single idle rotation is
selected.  All assumptions are concrete basis actions of the constituent
stages. -/
theorem applyOperator_h2PostOperator_idle_of_stage_actions119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr)
    (before stable incremented output : QubitBasis qubits)
    (activeStep :
      historyTaylorActiveConjunctionBasisAction layout before = stable)
    (invalidStep : historyTaylorInvalidClockBasisAction layout stable = stable)
    (orderBoundaryStep :
      historyTaylorOrderBoundaryBasisAction layout stable = stable)
    (idleBoundaryStep :
      historyTaylorIdleBoundaryBasisAction layout stable = stable)
    (degreeStep :
      historyTaylorDegreeIncrementBasisAction layout stable = incremented)
    (coefficientLoopFixes :
      VerifiedCircuitCore.applyOperator
        (historyTaylorCoefficientLoopOperator layout angles)
        (VerifiedCircuitCore.basisKet incremented) =
      VerifiedCircuitCore.basisKet incremented)
    (idlePredicateTrue :
      (incremented (historyBranchWire layout) &&
        historyTaylorIdleIntervalCondition layout incremented) = true)
    (idleSignalFalse : incremented layout.coefficientSignal = false)
    (restoreClean :
      VerifiedCircuitCore.applyOperator
          (operatorSequence
            [historyTaylorIdleEndComparisonOperator layout,
             historyTaylorTimeComparisonOperator layout,
             historyTaylorSelectorEqualityOperator layout])
          (VerifiedCircuitCore.basisKet incremented) =
        VerifiedCircuitCore.basisKet output)
    (restoreDirty :
      VerifiedCircuitCore.applyOperator
          (operatorSequence
            [historyTaylorIdleEndComparisonOperator layout,
             historyTaylorTimeComparisonOperator layout,
             historyTaylorSelectorEqualityOperator layout])
          (VerifiedCircuitCore.basisKet
            (replaceQubitWire incremented layout.coefficientSignal true)) =
        VerifiedCircuitCore.basisKet
          (replaceQubitWire output layout.coefficientSignal true)) :
    VerifiedCircuitCore.applyOperator
        (h2PostOperator119 layout angles idleAngle)
        (VerifiedCircuitCore.basisKet before) =
      ((Real.cos (idleAngle.uniformValue / 2) : Real) : Complex) •
          VerifiedCircuitCore.basisKet output +
        ((Real.sin (idleAngle.uniformValue / 2) : Real) : Complex) •
          VerifiedCircuitCore.basisKet
            (replaceQubitWire output layout.coefficientSignal true) := by
  unfold h2PostOperator119
  simp only [operatorSequence, applyOperator_mul, Matrix.one_mul]
  rw [historyTaylorActiveConjunctionOperator,
    applyOperator_deterministicOperator_basisKet, activeStep]
  rw [historyTaylorInvalidClockOperator,
    applyOperator_deterministicOperator_basisKet, invalidStep]
  rw [historyTaylorOrderBoundaryOperator,
    applyOperator_deterministicOperator_basisKet, orderBoundaryStep]
  rw [historyTaylorIdleBoundaryOperator,
    applyOperator_deterministicOperator_basisKet, idleBoundaryStep]
  have degreeStep' :
      predicateControlledAddMod2PowBasisAction
          (historyTaylorDegreeIncrementCondition layout) layout.order 1 stable =
        incremented := by
    simpa [historyTaylorDegreeIncrementBasisAction] using degreeStep
  rw [historyTaylorDegreeIncrementOperator,
    predicateControlledAddMod2PowOperator,
    applyOperator_deterministicOperator_basisKet, degreeStep']
  rw [coefficientLoopFixes]
  unfold historyTaylorIdleCoefficientOperator
  rw [applyOperator_predicateControlledRy_basisKet_of_true_false119
    (fun basis => basis (historyBranchWire layout) &&
      historyTaylorIdleIntervalCondition layout basis)
    layout.coefficientSignal idleAngle.uniformValue incremented
    idlePredicateTrue idleSignalFalse]
  have restoreClean' :
      VerifiedCircuitCore.applyOperator
          (historyTaylorSelectorEqualityOperator layout)
          (VerifiedCircuitCore.applyOperator
            (historyTaylorTimeComparisonOperator layout)
            (VerifiedCircuitCore.applyOperator
              (historyTaylorIdleEndComparisonOperator layout)
              (VerifiedCircuitCore.basisKet incremented))) =
        VerifiedCircuitCore.basisKet output := by
    simpa [operatorSequence, applyOperator_mul, Matrix.one_mul] using restoreClean
  have restoreDirty' :
      VerifiedCircuitCore.applyOperator
          (historyTaylorSelectorEqualityOperator layout)
          (VerifiedCircuitCore.applyOperator
            (historyTaylorTimeComparisonOperator layout)
            (VerifiedCircuitCore.applyOperator
              (historyTaylorIdleEndComparisonOperator layout)
              (VerifiedCircuitCore.basisKet
                (replaceQubitWire incremented layout.coefficientSignal true)))) =
        VerifiedCircuitCore.basisKet
          (replaceQubitWire output layout.coefficientSignal true) := by
    simpa [operatorSequence, applyOperator_mul, Matrix.one_mul] using restoreDirty
  simp_rw [applyOperator_add, applyOperator_smul]
  rw [restoreClean', restoreDirty']

theorem historyTaylorCoefficientLoopOperator_apply_basisKet_of_clock_false119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (input : QubitBasis qubits)
    (clockFalse : historyTaylorClockLessThanTimeValue layout input = false) :
    VerifiedCircuitCore.applyOperator
        (historyTaylorCoefficientLoopOperator layout angles)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  unfold historyTaylorCoefficientLoopOperator
  apply applyOperator_operatorSequence_of_each_fixes119
  intro operator member
  rcases List.mem_map.mp member with ⟨index, indexMember, rfl⟩
  unfold historyTaylorCoefficientIterationOperator
  apply applyOperator_predicateControlledSingleQubitOperator_basisKet_column_false119
  simp [clockFalse]

theorem h2AfterIdleEnd119_time_flag_idle119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks) :
    h2AfterIdleEnd119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h2SelectedBranch119 index)
        (historyLessThanTimeWire (ExecutableLayout119 source domain)) = false := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 index
  have value := h2BeforeQ119_time_flag_value
    source domain fits h2SelectedBranch119 index
  change h2BeforeQ119 layout input (historyLessThanTimeWire layout) = _ at value
  unfold h2BeforeQ119 historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction at value
  rw [xorWire_apply_other (historyActiveWire layout)
    (historyLessThanTimeWire layout)
    (historyLessThanTimeWire_ne_activeWire layout)] at value
  simpa [clockIdle] using value

theorem h2AfterIdleEnd119_idle_flag_logical119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    h2AfterIdleEnd119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h2SelectedBranch119 index)
        (historyLessThanIdleEndWire (ExecutableLayout119 source domain)) = true := by
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 index
  have value := h2BeforeQ119_idle_flag_value_numeric
    source domain fits h2SelectedBranch119 index
  change h2BeforeQ119 layout input (historyLessThanIdleEndWire layout) = _ at value
  unfold h2BeforeQ119 historyTaylorActiveConjunctionBasisAction
    ClassicalReversibleStage.conjunctionDirectBasisAction at value
  rw [xorWire_apply_other (historyActiveWire layout)
    (historyLessThanIdleEndWire layout)
    (historyLessThanIdleEndWire_ne_activeWire layout)] at value
  simpa using value

theorem h2BeforeQ119_active_false_of_idle_clock119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks) :
    h2BeforeQ119 (ExecutableLayout119 source domain)
        (correctedBranchHistoryBasis119 source domain fits
          h2SelectedBranch119 index)
        (historyActiveWire (ExecutableLayout119 source domain)) = false := by
  rw [h2BeforeQ119_active_selected_value]
  simp [h2SelectedBranch119, clockIdle]

end
end ExecutableHistoryExecutableHistory
