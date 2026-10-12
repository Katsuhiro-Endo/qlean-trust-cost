import QLean.Proofs.CheckpointCorrespondenceTargetCP01
import QLean.Proofs.FiniteKernelPublicCorrespondence
import QLean.Circuits.CheckpointCircuitSymbolFreedom

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option warningAsError true

namespace QLean.Proofs.GeneralScientificPublicCheckpoints

open Matrix VerifiedCircuitCore ProbabilityGeneratorQProof
open QLean.MathematicalSpecifications
open QLean.MathematicalSpecifications.CoalescingWalkModel
open QLean.MathematicalSpecifications.PublicCheckpoints
open QLean.MathematicalSpecifications.Targets
open QLean.Circuits.CheckpointCircuits
open QLean.Circuits.CheckpointCircuitSymbolFreedom
open QLean.Correspondence.CheckpointReadout
open QLean.Correspondence.GeneralCheckpointData
open QLean.Proofs.GeneralCheckpointCorrespondence

noncomputable section

theorem generatorCircuit_correct {parameters : Parameters}
    (_input : Input parameters) (_valid : Valid _input) :
    VerifiedMath.BlockReadout.squareBlock (generatorBinding parameters)
        (Circuit.denote VerifiedCircuitCore.primitiveGateOperator
          (generatorCircuit
            (QLean.Proofs.CheckpointCorrespondence.General.parametersToCircuit parameters))) =
      (((((3 : ℝ) * (parameters.K : ℝ)) : ℝ) : ℂ))⁻¹ •
        generatorMatrix parameters := by
  change generatorBlock (generatorBinding parameters)
      (Circuit.denote VerifiedCircuitCore.primitiveGateOperator
        (generatorCircuit
          (QLean.Proofs.CheckpointCorrespondence.General.parametersToCircuit parameters))) = _
  have old := QLean.Proofs.CheckpointCorrespondence.generatorCircuit_correct parameters
  rw [generatorCircuit_denote_eq_internal]
  rw [show (fun _ : String => (0 : ℝ)) =
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment by rfl]
  rw [ProbabilityGeneratorQProof.compileCircuitToCanonicalCore_denote]
  rw [generatorBlock_reindexJointOperator]
  exact old

theorem historyCircuit_correct (input : ExecutableInput) :
    VerifiedMath.BlockReadout.squareBlock (historyBinding input)
      (Circuit.denote VerifiedCircuitCore.primitiveGateOperator (historyCircuit input)) =
    ((ExecutableHistoryExecutableP18.executableAlpha119 input.source : ℂ)⁻¹) •
      historyMatrix (historyMatrixParameters input.source)
        (historyMatrixConditions input.source) := by
  change historyBlock (historyBinding input)
      (Circuit.denote VerifiedCircuitCore.primitiveGateOperator (historyCircuit input)) = _
  rw [Circuit.denote_primitiveGateOperator_eq_withSymbols _
    (historyCircuit_isSymbolFree input)
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment]
  exact QLean.Proofs.GeneralCheckpointCorrespondence.historyCircuit_correct input

theorem kernelReflectionCircuit_correct
    (input : QLean.Circuits.FiniteKernelCircuit.Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    let executable := input.executableInput nonzero
    let physical := QLean.Circuits.CommonKernelReflection.canonicalCircuitInput executable
    VerifiedMath.OperatorRelations.RealLogicalActionApprox VerifiedMath.Complexification.euclideanVector
      (VerifiedMath.BlockReadout.squareBlock (qsvtBinding physical)
        (Circuit.denote VerifiedCircuitCore.primitiveGateOperator
          (kernelReflectionCircuit input VerifiedMath.Quantum.QSP.defaultPhaseProvider)))
      (fun state => WithLp.toLp 2
        ((kernelReflectionMatrix
          (kernelReflectionParameters executable.source executable.assumptions)
          (kernelReflectionConditions executable.source executable.assumptions)).mulVec state.ofLp))
      (input.epsilon : ℝ) := by
  exact FiniteKernelPublicCorrespondence.kernelReflectionCircuit_correct input nonzero

theorem successfulHistoryCircuit_correct
    (input : QLean.Circuits.FiniteKernelCircuit.Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    let executable := input.executableInput nonzero
    let physical := QLean.Circuits.CommonKernelReflection.canonicalCircuitInput executable
    VerifiedMath.OperatorRelations.StateApprox
      ((kernelHistoryProjector
          (kernelReflectionParameters executable.source executable.assumptions)).mulVec
        ((VerifiedMath.BlockReadout.squareBlock (qsvtBinding physical)
          (Circuit.denote VerifiedCircuitCore.primitiveGateOperator
            (successfulHistoryCircuit input VerifiedMath.Quantum.QSP.defaultPhaseProvider))).mulVec
          (kernelExtensionState
            (kernelReflectionParameters executable.source executable.assumptions))))
      (successfulHistoryState
        (kernelReflectionParameters executable.source executable.assumptions)
        (kernelReflectionConditions executable.source executable.assumptions))
      (input.epsilon : ℝ) := by
  exact FiniteKernelPublicCorrespondence.successfulHistoryCircuit_correct input nonzero

end
end QLean.Proofs.GeneralScientificPublicCheckpoints
