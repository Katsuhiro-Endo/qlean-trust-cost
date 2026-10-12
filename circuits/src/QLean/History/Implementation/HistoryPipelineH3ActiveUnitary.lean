import QLean.History.Implementation.HistoryPipelineH3ActiveEntry

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

noncomputable def h3ActiveTailComponents119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    List (VerifiedCircuitCore.ExactOperatorComponent
      (primitiveGateOperatorWithSymbols
        (qubits := (ExecutableRaw119 source).history.qubits)
        internalZeroSymbolEnvironment)) :=
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  [repairedH3ActiveConjunction119 source domain,
   repairedH3IdleTransform119 source domain,
   repairedH3ActiveConjunction119 source domain,
   repairedH3CoefficientRotation119 source domain,
   repairedH3ActiveConjunction119 source domain,
   repairedH3IdleEndComparison119 source domain,
   repairedH3TimeComparison119 source domain,
   historyProjectorControlExactComponent internalZeroSymbolEnvironment
      layout clock.projectorControl,
   historyControlledClockIncrementExactComponent internalZeroSymbolEnvironment
      layout clock.controlledIncrement,
   repairedH3SelectorEquality119 source domain]

noncomputable def h3ActiveTailComponent119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    VerifiedCircuitCore.ExactOperatorComponent
      (primitiveGateOperatorWithSymbols
        (qubits := (ExecutableRaw119 source).history.qubits)
        internalZeroSymbolEnvironment) :=
  VerifiedCircuitCore.ExactOperatorComponent.sequence
    (h3ActiveTailComponents119 source domain)

theorem h3ActiveTailComponent119_target
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (h3ActiveTailComponent119 source domain).target =
      h3ActiveTailOperator119 source domain := by
  unfold h3ActiveTailComponent119 h3ActiveTailComponents119
    h3ActiveTailOperator119
  exact VerifiedCircuitCore.ExactOperatorComponent.sequence_target_eq_operatorSequence _

theorem h3ActiveTailOperator119_mem_unitaryGroup
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    h3ActiveTailOperator119 source domain ∈
      Matrix.unitaryGroup
        (QubitBasis (ExecutableRaw119 source).history.qubits) ℂ := by
  have hmem := VerifiedCircuitCore.primitiveCircuit_denote_mem_unitaryGroup
    internalZeroSymbolEnvironment (h3ActiveTailComponent119 source domain).circuit
  rw [(h3ActiveTailComponent119 source domain).correct,
    h3ActiveTailComponent119_target] at hmem
  exact hmem

theorem h3ActiveTailOperator119_apply_injective
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    Function.Injective
      (VerifiedCircuitCore.applyOperator (h3ActiveTailOperator119 source domain)) := by
  intro left right equal
  let tail := h3ActiveTailOperator119 source domain
  have hmem : tail ∈ Matrix.unitaryGroup
      (QubitBasis (ExecutableRaw119 source).history.qubits) ℂ :=
    h3ActiveTailOperator119_mem_unitaryGroup source domain
  have hleft : star tail * tail = 1 :=
    (Matrix.mem_unitaryGroup_iff').1 hmem
  calc
    left = VerifiedCircuitCore.applyOperator (1 :
        VerifiedCircuitCore.Operator
          (QubitBasis (ExecutableRaw119 source).history.qubits)) left := by
            change left = Matrix.mulVec 1 left
            rw [Matrix.one_mulVec]
    _ = VerifiedCircuitCore.applyOperator (star tail * tail) left := by rw [hleft]
    _ = VerifiedCircuitCore.applyOperator (star tail)
        (VerifiedCircuitCore.applyOperator tail left) := by
          rw [VerifiedCircuitCore.applyOperator_mul]
    _ = VerifiedCircuitCore.applyOperator (star tail)
        (VerifiedCircuitCore.applyOperator tail right) := by rw [equal]
    _ = VerifiedCircuitCore.applyOperator (star tail * tail) right := by
          rw [VerifiedCircuitCore.applyOperator_mul]
    _ = VerifiedCircuitCore.applyOperator (1 :
        VerifiedCircuitCore.Operator
          (QubitBasis (ExecutableRaw119 source).history.qubits)) right := by rw [hleft]
    _ = right := by
      change Matrix.mulVec 1 right = right
      rw [Matrix.one_mulVec]

end
end ExecutableHistoryExecutableHistory
