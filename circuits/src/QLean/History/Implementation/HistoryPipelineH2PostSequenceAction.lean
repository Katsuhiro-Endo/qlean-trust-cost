import QLean.History.Implementation.HistoryPipelineH2CoefficientLoopAction

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

/-- Algebraic evaluation of the H2 post-Q10 source word once its deterministic
boundary actions and the selected Taylor index have been identified.  Every
hypothesis below is a concrete stage fact; no target-operator equality is
assumed. -/
theorem applyOperator_h2PostOperator_of_stage_actions119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr)
    (idleAngle : AngleExpr)
    (selected : Fin parameters.taylorOrder)
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
    (loopBranchTrue : incremented (historyBranchWire layout) = true)
    (loopClockTrue :
      historyTaylorClockLessThanTimeValue layout incremented = true)
    (loopOrderSelected :
      ClassicalReversibleStage.littleEndianRegisterEqualsNat
        (historyRegisterWires layout.order) (selected.val + 1) incremented = true)
    (loopSignalFalse : incremented layout.coefficientSignal = false)
    (idleCoefficientFalse :
      (incremented (historyBranchWire layout) &&
        historyTaylorIdleIntervalCondition layout incremented) = false)
    (idleCoefficientDirtyFalse :
      ((replaceQubitWire incremented layout.coefficientSignal true)
          (historyBranchWire layout) &&
        historyTaylorIdleIntervalCondition layout
          (replaceQubitWire incremented layout.coefficientSignal true)) = false)
    (restoreClean :
      applyOperator
          (operatorSequence
            [historyTaylorIdleEndComparisonOperator layout,
             historyTaylorTimeComparisonOperator layout,
             historyTaylorSelectorEqualityOperator layout])
          (basisKet incremented) = basisKet output)
    (restoreDirty :
      applyOperator
          (operatorSequence
            [historyTaylorIdleEndComparisonOperator layout,
             historyTaylorTimeComparisonOperator layout,
             historyTaylorSelectorEqualityOperator layout])
          (basisKet
            (replaceQubitWire incremented layout.coefficientSignal true)) =
        basisKet (replaceQubitWire output layout.coefficientSignal true)) :
    applyOperator (h2PostOperator119 layout angles idleAngle) (basisKet before) =
      ((Real.cos ((angles selected).uniformValue / 2) : Real) : Complex) •
          basisKet output +
        ((Real.sin ((angles selected).uniformValue / 2) : Real) : Complex) •
          basisKet (replaceQubitWire output layout.coefficientSignal true) := by
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
  rw [applyOperator_historyTaylorCoefficientLoopOperator_selected119
    layout angles selected incremented loopBranchTrue loopClockTrue
    loopOrderSelected loopSignalFalse]
  rw [applyOperator_add, applyOperator_smul, applyOperator_smul]
  unfold historyTaylorIdleCoefficientOperator
  rw [applyOperator_predicateControlledSingleQubitOperator_basisKet_column_false119
    _ layout.coefficientSignal (localRy idleAngle.uniformValue) incremented
    idleCoefficientFalse]
  rw [applyOperator_predicateControlledSingleQubitOperator_basisKet_column_false119
    _ layout.coefficientSignal (localRy idleAngle.uniformValue)
    (replaceQubitWire incremented layout.coefficientSignal true)
    idleCoefficientDirtyFalse]
  have restoreClean' :
      applyOperator (historyTaylorSelectorEqualityOperator layout)
          (applyOperator (historyTaylorTimeComparisonOperator layout)
            (applyOperator (historyTaylorIdleEndComparisonOperator layout)
              (basisKet incremented))) = basisKet output := by
    simpa [operatorSequence, applyOperator_mul, Matrix.one_mul] using restoreClean
  have restoreDirty' :
      applyOperator (historyTaylorSelectorEqualityOperator layout)
          (applyOperator (historyTaylorTimeComparisonOperator layout)
            (applyOperator (historyTaylorIdleEndComparisonOperator layout)
              (basisKet
                (replaceQubitWire incremented layout.coefficientSignal true)))) =
        basisKet (replaceQubitWire output layout.coefficientSignal true) := by
    simpa [operatorSequence, applyOperator_mul, Matrix.one_mul] using restoreDirty
  simp_rw [applyOperator_add, applyOperator_smul]
  rw [restoreClean', restoreDirty']

end
end ExecutableHistoryExecutableHistory
