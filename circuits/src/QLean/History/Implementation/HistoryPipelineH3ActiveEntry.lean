import QLean.History.Implementation.HistoryPipelineH3ActiveInvocation
import QLean.History.Implementation.HistoryPipelineH2LogicalSupport

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
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

noncomputable def h3ActivePrefixTargets119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) : List
      (VerifiedCircuitCore.Operator
        (QubitBasis (ExecutableRaw119 source).history.qubits)) := [
    (repairedH3SelectorEquality119 source domain).target,
    (repairedH3TimeComparison119 source domain).target,
    (repairedH3IdleEndComparison119 source domain).target,
    (repairedH3ActiveConjunction119 source domain).target]

noncomputable def h3ActiveTailTargets119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) : List
      (VerifiedCircuitCore.Operator
        (QubitBasis (ExecutableRaw119 source).history.qubits)) :=
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  [(repairedH3ActiveConjunction119 source domain).target,
   (repairedH3IdleTransform119 source domain).target,
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

noncomputable def h3ActivePrefixOperator119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    VerifiedCircuitCore.Operator
      (QubitBasis (ExecutableRaw119 source).history.qubits) :=
  operatorSequence (h3ActivePrefixTargets119 source domain)

theorem h3ActivePrefixOperator119_apply_basisKet
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    VerifiedCircuitCore.applyOperator (h3ActivePrefixOperator119 source domain)
        (VerifiedCircuitCore.basisKet logical) =
      VerifiedCircuitCore.basisKet (h3BeforeUniform119 layout logical) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  have auxiliary : historyTaylorAuxiliaryBoundaryPredicate layout logical :=
    correctedBranchHistoryBasis119_p15_auxiliary
      source domain fits h3SelectedBranch119 index
  unfold h3ActivePrefixOperator119 h3ActivePrefixTargets119
  simp only [operatorSequence, VerifiedCircuitCore.applyOperator_mul,
    Matrix.one_mul]
  rw [repairedH3SelectorEquality119_apply_basisKet source domain logical]
  rw [repairedH3TimeComparison119_apply_basisKet
    source domain logical auxiliary]
  rw [repairedH3IdleEndComparison119_apply_basisKet
    source domain logical auxiliary]
  rw [repairedH3ActiveConjunction119_apply_basisKet source domain]
  rfl

theorem repairedH3RecordedTarget119_decompose_active
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    repairedH3RecordedTarget119 source domain =
      h3ActiveTailOperator119 source domain *
        (historyOrderUniformPreparationInverseExactComponent
          (ExecutableLayout119 source domain)
          (ExecutableClockEvidence119 source domain).uniformExternalControl
        ).target *
        h3ActivePrefixOperator119 source domain := by
  have split :
      (repairedH3Components119 source domain).map
          VerifiedCircuitCore.ExactOperatorComponent.target =
        (h3ActivePrefixTargets119 source domain ++
          [(historyOrderUniformPreparationInverseExactComponent
            (ExecutableLayout119 source domain)
            (ExecutableClockEvidence119 source domain).uniformExternalControl
          ).target]) ++ h3ActiveTailTargets119 source domain := by
    rfl
  have tail : h3ActiveTailOperator119 source domain =
      operatorSequence (h3ActiveTailTargets119 source domain) := by
    rfl
  unfold repairedH3RecordedTarget119
  rw [split, operatorSequence_append, operatorSequence_append]
  simp only [operatorSequence, Matrix.one_mul]
  rw [← tail]
  unfold h3ActivePrefixOperator119
  rw [mul_assoc]

def h3ActiveOutputIndex119
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    OldHistoryIndex119 source where
  clock := ⟨index.clock.val + 1, clockNext⟩
  state := {
    label := ⟨0, source.historyWellFormed.binaryLabels_pos⟩
    configuration := index.state.configuration }

@[simp] theorem h3ActiveOutputIndex119_clock
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    (h3ActiveOutputIndex119 source index clockNext).clock.val =
      index.clock.val + 1 := rfl

@[simp] theorem h3ActiveOutputIndex119_label
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    (h3ActiveOutputIndex119 source index clockNext).state.label.val = 0 := rfl

@[simp] theorem h3ActiveOutputIndex119_configuration
    (source : AlignedCommonSource119)
    (index : OldHistoryIndex119 source)
    (clockNext : index.clock.val + 1 < source.historyParameters.clockEnd) :
    (h3ActiveOutputIndex119 source index clockNext).state.configuration =
      index.state.configuration := rfl

end
end ExecutableHistoryExecutableHistory
