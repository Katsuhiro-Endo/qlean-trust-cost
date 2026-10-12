import QLean.Circuits.FiniteKernelCorrectness
import QLean.Proofs.GeneralCheckpointCorrespondence

/-! Independent CP03/CP04 targets for the provider-parametric finite
constructor. Real scientific-input compilation belongs outside this entry;
no theorem here asserts accuracy for an external numerical provider. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000

namespace QLean.Proofs.FiniteKernelPublicCorrespondence

open VerifiedCircuitCore
open QLean.Circuits.FiniteKernelCircuit
open QLean.Circuits.CommonKernelReflection
open QLean.Correspondence.CheckpointReadout QLean.Correspondence.GeneralCheckpointData
open QLean.MathematicalSpecifications
open QLean.MathematicalSpecifications.PublicCheckpoints QLean.MathematicalSpecifications.Targets
open QLean.Proofs.GeneralCheckpointCorrespondence
open QLean.Proofs.CheckpointCorrespondence.Internal
open NativeSignalQSVTFunctionalBridge NativeConcreteP18QSPWitness
open ExecutableHistoryExecutableP18

noncomputable section

/-- Fix the finite physical carrier before the legacy logical binding is
elaborated. This is the shared circuit semantics, not a different operator. -/
def finiteDenotation (input : Input)
    (circuit : Circuit (PrimitiveGate (kernelQubits input))) :
    Operator (QubitBasis (kernelQubits input)) :=
  Circuit.denote primitiveGateOperator circuit

/-- The actual finite constructor is related directly to the independent
kernel-reflection matrix, not to the denotation of another circuit. -/
theorem kernelReflectionCircuit_correct (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    let executable := input.executableInput nonzero
    VerifiedMath.OperatorRelations.RealLogicalActionApprox QLean.MathematicalSpecifications.PublicCheckpoints.complexifyVector
      (qsvtBlock (qsvtBinding (canonicalCircuitInput executable))
        (finiteDenotation input
          (kernelReflectionCircuit input VerifiedMath.Quantum.QSP.defaultPhaseProvider)))
      (fun state => WithLp.toLp 2
        ((kernelReflectionMatrix
          (kernelReflectionParameters executable.source executable.assumptions)
          (kernelReflectionConditions executable.source executable.assumptions)).mulVec state.ofLp))
      (input.epsilon : ℝ) := by
  let executable := input.executableInput nonzero
  dsimp only
  rw [qsvtBlock_eq_reindex]
  apply realLogicalApprox_of_reindex_native
    (extendedIndexEquiv executable.source executable.assumptions)
    (NativeSingularPairTwoFrame.cleanBlock
      (Circuit.denote primitiveGateOperator
        (kernelReflectionCircuit input VerifiedMath.Quantum.QSP.defaultPhaseProvider))
      (input.logicalEmbedding nonzero))
    (kernelReflectionMatrix
      (kernelReflectionParameters executable.source executable.assumptions)
      (kernelReflectionConditions executable.source executable.assumptions)) (input.epsilon : ℝ)
  have contract := QLean.Circuits.FiniteKernelCircuit.kernelReflectionCircuit_correct input nonzero
  dsimp only at contract
  rw [certifiedIdealReflection_eq_independent_reindex executable] at contract
  exact contract

theorem successfulHistoryCircuit_native_error (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    let executable := input.executableInput nonzero
    stateL2Norm
      (M13cSpecification.complexHistoryProjector119
        ((NativeSingularPairTwoFrame.cleanBlock
          (finiteDenotation input
            (successfulHistoryCircuit input VerifiedMath.Quantum.QSP.defaultPhaseProvider))
          (input.logicalEmbedding nonzero)).mulVec
            (NativeSignalQSVTFunctionalBridge.complexifyVector (TypedNegativeCases.actualBasis
              (d := ExecutableD119 executable.source)
              (c := ExecutableC119 executable.source)
              (R := ExecutableLabels119 executable.source)))) -
        M13cSpecification.idealHistoryTarget119 executable) ≤ (input.epsilon : ℝ) := by
  let executable := input.executableInput nonzero
  let basis := TypedNegativeCases.actualBasis
    (d := ExecutableD119 executable.source) (c := ExecutableC119 executable.source)
    (R := ExecutableLabels119 executable.source)
  have approx := QLean.Circuits.FiniteKernelCircuit.kernelReflectionCircuit_correct input nonzero basis
  dsimp only
  rw [← executableIdealHistoryProjection_eq_target executable,
    ← M13cSpecification.complexHistoryProjector119_sub]
  exact (M13cSpecification.complexHistoryProjector119_contract _).trans
    (approx.trans (mul_le_of_le_one_right
      (by exact_mod_cast le_of_lt input.epsilon_pos)
      (ConcreteHistoryInput.m13ExtensionBasisE_norm
        (d := ExecutableD119 executable.source) (c := ExecutableC119 executable.source)
        (R := ExecutableLabels119 executable.source))))

/-- The very same CP03 preparation, with the history readout, has the
independently defined successful-history state as its approximate target. -/
theorem successfulHistoryCircuit_correct (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    let executable := input.executableInput nonzero
    stateNorm (fun index =>
      successfulHistoryReadout (canonicalCircuitInput executable)
        (finiteDenotation input
          (successfulHistoryCircuit input VerifiedMath.Quantum.QSP.defaultPhaseProvider)) index -
      successfulHistoryState
        (kernelReflectionParameters executable.source executable.assumptions)
        (kernelReflectionConditions executable.source executable.assumptions) index) ≤
      (input.epsilon : ℝ) := by
  let executable := input.executableInput nonzero
  dsimp only
  rw [successfulHistoryReadout_reindex, independentSuccessfulHistory_eq_reindex executable]
  change stateNorm
    ((M13cSpecification.complexHistoryProjector119
        ((NativeSingularPairTwoFrame.cleanBlock
          (finiteDenotation input (successfulHistoryCircuit input VerifiedMath.Quantum.QSP.defaultPhaseProvider))
          (input.logicalEmbedding nonzero)).mulVec
            (NativeSignalQSVTFunctionalBridge.complexifyVector
              (TypedNegativeCases.actualBasis
                (d := ExecutableD119 executable.source) (c := ExecutableC119 executable.source)
                (R := ExecutableLabels119 executable.source)))) -
        M13cSpecification.idealHistoryTarget119 executable) ∘
      extendedIndexEquiv executable.source executable.assumptions) ≤ (input.epsilon : ℝ)
  rw [stateNorm_comp_equiv]
  exact successfulHistoryCircuit_native_error input nonzero

end
end QLean.Proofs.FiniteKernelPublicCorrespondence
