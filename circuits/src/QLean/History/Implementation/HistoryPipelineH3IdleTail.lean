import QLean.History.Implementation.HistoryPipelineH3IdleLogical
import QLean.History.Implementation.HistoryPipelineH3ActiveInvocation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
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

/-- The suffix of the repaired H3 circuit following the idle transform. -/
noncomputable def h3IdlePostTransformOperator119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    VerifiedCircuitCore.Operator
      (QubitBasis (ExecutableRaw119 source).history.qubits) :=
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  operatorSequence [
    (repairedH3ActiveConjunction119 source domain).target,
    (repairedH3CoefficientRotation119 source domain).target,
    (repairedH3ActiveConjunction119 source domain).target,
    (repairedH3IdleEndComparison119 source domain).target,
    (repairedH3TimeComparison119 source domain).target,
    (historyProjectorControlExactComponent internalZeroSymbolEnvironment
      layout clock.projectorControl).target,
    (historyControlledClockIncrementExactComponent internalZeroSymbolEnvironment
      layout clock.controlledIncrement).target,
    (repairedH3SelectorEquality119 source domain).target]

/-- An inactive H3 suffix has no phase and has the same classical basis
action as the already verified active tail. -/
theorem h3IdlePostTransformOperator119_apply_basisKet
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (branchTrue : input (historyBranchWire
      (ExecutableLayout119 source domain)) = true)
    (timeFalse : input (historyLessThanTimeWire
      (ExecutableLayout119 source domain)) = false)
    (activeFalse : input (historyActiveWire
      (ExecutableLayout119 source domain)) = false)
    (idleComparisonClean :
      (forall index,
        (historyTaylorActiveConjunctionBasisAction
          (ExecutableLayout119 source domain) input)
          ((historyBorrowRegister (ExecutableLayout119 source domain)).wire index) =
            false) ∧
      forall index,
        (historyTaylorActiveConjunctionBasisAction
          (ExecutableLayout119 source domain) input)
          ((historyBoundRegister (ExecutableLayout119 source domain)).wire index) =
            false)
    (timeComparisonClean :
      let afterActive := historyTaylorActiveConjunctionBasisAction
        (ExecutableLayout119 source domain) input
      let afterIdle := historyTaylorIdleEndComparisonBasisAction
        (ExecutableLayout119 source domain) afterActive
      (forall index, afterIdle
          ((historyBorrowRegister (ExecutableLayout119 source domain)).wire index) =
            false) ∧
        forall index, afterIdle
          ((historyBoundRegister (ExecutableLayout119 source domain)).wire index) =
            false)
    (projectorWorkClean :
      let afterActive := historyTaylorActiveConjunctionBasisAction
        (ExecutableLayout119 source domain) input
      let afterIdle := historyTaylorIdleEndComparisonBasisAction
        (ExecutableLayout119 source domain) afterActive
      let afterTime := historyTaylorTimeComparisonBasisAction
        (ExecutableLayout119 source domain) afterIdle
      ClassicalReversibleStage.minimumWorkCleanPredicate
          (historyRegisterWires
            (historyEqualityWork (ExecutableLayout119 source domain))) afterTime ∧
        h3I06CleanInputPredicate (ExecutableLayout119 source domain) afterTime)
    (clockWorkClean :
      let layout := ExecutableLayout119 source domain
      let clock := ExecutableClockEvidence119 source domain
      let afterActive := historyTaylorActiveConjunctionBasisAction layout input
      let afterIdle := historyTaylorIdleEndComparisonBasisAction layout afterActive
      let afterTime := historyTaylorTimeComparisonBasisAction layout afterIdle
      let afterProjector := h3I06BasisAction layout afterTime
      controlledAddConstantMod2PowCleanPredicate
        (historyControlledClockIncrementSpec layout clock.controlledIncrement)
        afterProjector) :
    VerifiedCircuitCore.applyOperator
        (h3IdlePostTransformOperator119 source domain)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet
        (h3ActiveTailBasisAction119 source domain input) := by
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  let afterActive := historyTaylorActiveConjunctionBasisAction layout input
  let afterIdle := historyTaylorIdleEndComparisonBasisAction layout afterActive
  let afterTime := historyTaylorTimeComparisonBasisAction layout afterIdle
  let afterProjector := h3I06BasisAction layout afterTime
  let afterClock := controlledAddConstantMod2PowBasisAction
    (historyControlledClockIncrementSpec layout clock.controlledIncrement)
    afterProjector
  change input (historyBranchWire layout) = true at branchTrue
  change input (historyLessThanTimeWire layout) = false at timeFalse
  change input (historyActiveWire layout) = false at activeFalse
  have activeFixed : afterActive = input := by
    funext wire
    by_cases isActive : wire = historyActiveWire layout
    · subst wire
      unfold afterActive historyTaylorActiveConjunctionBasisAction
        ClassicalReversibleStage.conjunctionDirectBasisAction
        ClassicalReversibleStage.allWiresTrue
        ClassicalReversibleStage.readWires
      simp only [List.map, List.all, id_eq, Bool.and_true, xorWire,
        Function.update_self]
      rw [branchTrue, timeFalse, activeFalse]
      rfl
    · unfold afterActive historyTaylorActiveConjunctionBasisAction
        ClassicalReversibleStage.conjunctionDirectBasisAction
      apply xorWire_apply_other
      exact isActive
  have firstActive : VerifiedCircuitCore.applyOperator
      (repairedH3ActiveConjunction119 source domain).target
      (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
    rw [repairedH3ActiveConjunction119_apply_basisKet]
    change VerifiedCircuitCore.basisKet afterActive =
      VerifiedCircuitCore.basisKet input
    rw [activeFixed]
  have rotation : VerifiedCircuitCore.applyOperator
      (repairedH3CoefficientRotation119 source domain).target
      (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
    rw [repairedH3CoefficientRotation119_target]
    exact h3semanticVerification_controlled_single_apply_basisKet_of_control_false
      (historyActiveWire layout) layout.coefficientSignal
      clock.coefficientControl_ne_signal _ input activeFalse
  have idleRestoreStep : VerifiedCircuitCore.applyOperator
      (repairedH3IdleEndComparison119 source domain).target
      (VerifiedCircuitCore.basisKet afterActive) =
      VerifiedCircuitCore.basisKet afterIdle := by
    unfold repairedH3IdleEndComparison119
    rw [historyLessThanConstantExactComponent_target]
    rw [historyLessThanConstantOperator_apply_basisKet_of_clean119]
    · rfl
    · exact idleComparisonClean
  have timeRestoreStep : VerifiedCircuitCore.applyOperator
      (repairedH3TimeComparison119 source domain).target
      (VerifiedCircuitCore.basisKet afterIdle) =
      VerifiedCircuitCore.basisKet afterTime := by
    unfold repairedH3TimeComparison119
    rw [historyLessThanConstantExactComponent_target]
    rw [historyLessThanConstantOperator_apply_basisKet_of_clean119]
    · rfl
    · exact timeComparisonClean
  have idleRestoreInput : VerifiedCircuitCore.applyOperator
      (repairedH3IdleEndComparison119 source domain).target
      (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet afterIdle := by
    rw [← activeFixed]
    exact idleRestoreStep
  have projectorStep : VerifiedCircuitCore.applyOperator
      (historyProjectorControlExactComponent internalZeroSymbolEnvironment
        layout clock.projectorControl).target
      (VerifiedCircuitCore.basisKet afterTime) =
      VerifiedCircuitCore.basisKet afterProjector := by
    rw [historyProjectorControlExactComponent_target]
    exact h3I06_projectorControlOperator_apply_basisKet_of_cleanEntry
      layout afterTime projectorWorkClean.1 projectorWorkClean.2
  have clockStep : VerifiedCircuitCore.applyOperator
      (historyControlledClockIncrementExactComponent internalZeroSymbolEnvironment
        layout clock.controlledIncrement).target
      (VerifiedCircuitCore.basisKet afterProjector) =
      VerifiedCircuitCore.basisKet afterClock := by
    rw [historyControlledClockIncrementExactComponent_target]
    unfold controlledAddConstantMod2PowDirtyOperator
    rw [ClassicalReversibleStage.analyticOperator_eq_deterministicReference,
      applyOperator_deterministicOperator_basisKet,
      controlledAddConstantMod2PowStage_reference_apply_of_clean]
    exact clockWorkClean
  have selectorStep : VerifiedCircuitCore.applyOperator
      (repairedH3SelectorEquality119 source domain).target
      (VerifiedCircuitCore.basisKet afterClock) =
      VerifiedCircuitCore.basisKet (h3AfterSelector119 layout afterClock) :=
    repairedH3SelectorEquality119_apply_basisKet source domain afterClock
  unfold h3IdlePostTransformOperator119
  simp only [operatorSequence, VerifiedCircuitCore.applyOperator_mul,
    Matrix.one_mul]
  rw [firstActive, rotation, firstActive]
  rw [idleRestoreInput, timeRestoreStep, projectorStep, clockStep, selectorStep]
  unfold h3ActiveTailBasisAction119
  rfl

end
end ExecutableHistoryExecutableHistory
