import QLean.Circuits.FiniteKernelDefaultProvider
import QLean.Circuits.FiniteScientificSparsePreparationBridge
import QLean.SignalProcessing.M13bFiniteCommonFunctional

/-! Default-provider correctness of the same finite-input constructor used
for numerical generation. The numerical provider has no accuracy theorem.
The signal evidence is constructed from the sparse preparation proof here,
never requested as an additional public correctness assumption. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace QLean.Circuits.FiniteKernelCircuit

open VerifiedCircuitCore M13bSpecification
open ExecutableHistoryExecutableHistory ExecutableHistoryExecutableP18
open QLean.Circuits.FiniteScientificCircuitSource
open QLean.Circuits.FiniteScientificPreparationBridge
open QLean.Circuits.FiniteScientificSparsePreparationBridge
open M13bQSVTLogicalEmbedding NativeSignalQSVTActual NativeSingularPairTwoFrame
open M13bFiniteCommonCompression M13bFiniteCommonFunctional
open NativeConcreteP18QSPWitness NativeSignalQSVTFunctionalBridge
open M13bGramBasisStrictPair M13bGramFullCompressedAction

noncomputable section

def Input.logicalEmbedding (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    Matrix (QubitBasis (kernelQubits input))
      (executableSignalCleanIndex119 input.source.layoutSource) ℂ :=
  let executable := input.executableInput nonzero
  qsvtLogicalEmbedding119 executable.domain executable.fits
    (theoreticalCanonicalP18CircuitSource executable.source executable.domain
      executable.fits executable.assumptions)

theorem Input.sparseOuterPlan_eq (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    let executable := input.executableInput nonzero
    @theoreticalCommonOuterPlan input.source.layoutSource executable.domain input.fits
      executable.assumptions
      (sparseCommonP18Implementation input.source executable.domain
        input.fits executable.assumptions) = input.source.outerPlan input.fits := by
  let executable := input.executableInput nonzero
  exact sparseCommonOuterPlan_nu_one input.source executable.domain
    executable.fits executable.assumptions rfl

/-- One finite public constructor, with the existence-based provider fixed
only in the theorem. The goal is the independent ideal kernel reflection on
every real logical vector, with the requested error and no chosen phase
witness, assumed block equality, or numerical-accuracy premise. -/
theorem kernelReflectionCircuit_correct (input : Input)
    (nonzero : input.source.layoutSource.initial ≠ 0) :
    let executable := input.executableInput nonzero
    RealLogicalL2OperatorApprox119
      (fun v => (cleanBlock
        (Circuit.denote primitiveGateOperator
          (kernelReflectionCircuit input VerifiedMath.Quantum.QSP.defaultPhaseProvider))
        (input.logicalEmbedding nonzero)).mulVec (complexifyVector v))
      (fun v => complexifyVector (WithLp.toLp 2
        ((GramOperator.idealKernelReflection
          (M13bPrimitiveCandidate.certifiedInput119 executable).base.system
          (M13bPrimitiveCandidate.certifiedInput119 executable).base.alpha
          (M13bPrimitiveCandidate.certifiedInput119 executable).base.nu
          (M13bPrimitiveCandidate.certifiedInput119 executable).base.hdet).mulVec v.ofLp)))
      (input.epsilon : ℝ) := by
  let executable := input.executableInput nonzero
  let implementation := sparseCommonP18Implementation input.source executable.domain
    executable.fits executable.assumptions
  have correct := @commonProgram_real_logical_operator_approx
    (input.synthesisRequest nonzero) implementation
    (QLean.Circuits.CheckpointCircuits.cp03ProgramWord
      (VerifiedMath.Quantum.QSP.defaultPhaseProvider input.polynomialRequest))
    (defaultPhaseProvider_meets input nonzero)
  unfold commonLogicalBlock at correct
  erw [input.sparseOuterPlan_eq nonzero] at correct
  simp only [kernelReflectionCircuit_denote]
  exact correct

end
end QLean.Circuits.FiniteKernelCircuit
