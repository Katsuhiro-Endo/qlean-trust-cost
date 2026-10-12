import QLean.History.Implementation.HistoryPipelineH3UniformEntry
import QLean.History.Implementation.HistoryPipelineControlledRotationAction

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
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

theorem embedControlledSingleQubitOperator_eq_predicate119
    {qubits : Nat} (control target : Fin qubits) (different : control ≠ target)
    (localOperator : Matrix Bool Bool ℂ) :
    embedControlledSingleQubitOperator control target different localOperator =
      predicateControlledSingleQubitOperator
        (fun basis : QubitBasis qubits => basis control) target localOperator := by
  ext output input
  rw [embedControlledSingleQubitOperator_apply_sparse,
    predicateControlledSingleQubitOperator_apply]
  by_cases agrees : agreesExcept target output input
  · rw [if_pos agrees, if_pos agrees]
  · rw [if_neg agrees, if_neg agrees]

/-- The repaired active coefficient rotation is exactly a minus sign on a
clean signal basis ket. -/
theorem repairedH3CoefficientRotation119_apply_basisKet_active_clean
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (activeTrue : input (historyActiveWire
      (ExecutableLayout119 source domain)) = true)
    (coefficientZero : input
      (ExecutableLayout119 source domain).coefficientSignal = false) :
    VerifiedCircuitCore.applyOperator
        (repairedH3CoefficientRotation119 source domain).target
        (VerifiedCircuitCore.basisKet input) =
      (-1 : Complex) • VerifiedCircuitCore.basisKet input := by
  let layout := ExecutableLayout119 source domain
  let evidence := ExecutableClockEvidence119 source domain
  rw [repairedH3CoefficientRotation119_target]
  rw [embedControlledSingleQubitOperator_eq_predicate119]
  rw [applyOperator_predicateControlledRy_basisKet_of_true_false119
    (fun basis : QubitBasis (ExecutableRaw119 source).history.qubits =>
      basis (historyActiveWire layout)) layout.coefficientSignal
    compiledIdleCoefficientAngle119.uniformValue input activeTrue coefficientZero]
  have sinZero : Real.sin
      (compiledIdleCoefficientAngle119.uniformValue / 2) = 0 := by
    rw [compiledIdleCoefficientAngle119_value]
    simp
  have cosMinus : Real.cos
      (compiledIdleCoefficientAngle119.uniformValue / 2) = -1 := by
    exact idleCoefficient_clean_amplitude119
  rw [sinZero, cosMinus]
  simp

/-- In the active-clock sector, the first active uncompute, the repaired idle
word, and the second active recompute cancel exactly on basis kets. -/
theorem repairedH3ActiveIdleSandwich119_apply_basisKet
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (branchTrue : input (historyBranchWire
      (ExecutableLayout119 source domain)) = true)
    (timeTrue : input (historyLessThanTimeWire
      (ExecutableLayout119 source domain)) = true)
    (idleEndTrue : input (historyLessThanIdleEndWire
      (ExecutableLayout119 source domain)) = true)
    (idleZero : input (historyIdleFlag
      (ExecutableLayout119 source domain)) = false)
    (activeTrue : input (historyActiveWire
      (ExecutableLayout119 source domain)) = true) :
    VerifiedCircuitCore.applyOperator
        (operatorSequence [
          (repairedH3ActiveConjunction119 source domain).target,
          (repairedH3IdleTransform119 source domain).target,
          (repairedH3ActiveConjunction119 source domain).target])
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.basisKet input := by
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  let parameters := HistoryRawSchema.parameters203
    (ExecutableRaw119 source).history
    (ExecutableAdmissible119 source domain).analytic
  let after := historyTaylorActiveConjunctionBasisAction layout input
  have afterBranch : after (historyBranchWire layout) = true := by
    unfold after historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _ (historyBranchWire_ne_activeWire layout)]
    exact branchTrue
  have afterTime : after (historyLessThanTimeWire layout) = true := by
    unfold after historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _
      (historyLessThanTimeWire_ne_activeWire layout)]
    exact timeTrue
  have afterIdleEnd : after (historyLessThanIdleEndWire layout) = true := by
    unfold after historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other _ _
      (historyLessThanIdleEndWire_ne_activeWire layout)]
    exact idleEndTrue
  have afterIdleZero : after (historyIdleFlag layout) = false := by
    have idleNeActive : historyIdleFlag layout ≠ historyActiveWire layout := by
      intro equal
      change layout.workspace.wire _ = layout.workspace.wire _ at equal
      have indexEqual := layout.workspace.injective equal
      have valuesEqual := congrArg Fin.val indexEqual
      dsimp at valuesEqual
      have sharedAtLeast :
          5 ≤ historySharedPoolWidth parameters
            (ExecutableRaw119 source).history.generatorWorkWidth := by
        calc
          5 ≤ historyStructuralPoolWidth parameters := by
            unfold historyStructuralPoolWidth
            omega
          _ ≤ historySharedPoolWidth parameters
              (ExecutableRaw119 source).history.generatorWorkWidth :=
            Nat.le_max_right _ _
      omega
    unfold after historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [xorWire_apply_other]
    · exact idleZero
    · exact idleNeActive
  have afterActiveZero : after (historyActiveWire layout) = false := by
    unfold after historyTaylorActiveConjunctionBasisAction
      ClassicalReversibleStage.conjunctionDirectBasisAction
      ClassicalReversibleStage.allWiresTrue
      ClassicalReversibleStage.readWires
    simp only [xorWire, Function.update_self, List.map, List.all, id_eq,
      Bool.and_true]
    rw [activeTrue, branchTrue, timeTrue]
    rfl
  simp only [operatorSequence, VerifiedCircuitCore.applyOperator_mul,
    Matrix.one_mul]
  rw [repairedH3ActiveConjunction119_apply_basisKet]
  rw [repairedH3IdleTransform119_target]
  rw [repairedH3IdleTransformOperator119_apply_basisKet_of_active_clock
    layout clock.idleTransform source.historyParameters.binaryLabels
    (repairedH3IdleAngle119 source).uniformValue after afterIdleEnd afterTime
    afterIdleZero afterActiveZero]
  rw [repairedH3ActiveConjunction119_apply_basisKet]
  have involutive := historyTaylorActiveConjunctionBasisAction_involutive119
    layout input
  change VerifiedCircuitCore.basisKet
      (historyTaylorActiveConjunctionBasisAction layout after) =
        VerifiedCircuitCore.basisKet input
  rw [involutive]

end
end ExecutableHistoryExecutableHistory
