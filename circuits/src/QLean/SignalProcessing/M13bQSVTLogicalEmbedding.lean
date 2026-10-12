import QLean.SignalProcessing.M13bHermitianOuterScalar
import QLean.SignalProcessing.M13bConjugateControlledCompute
import QLean.SignalProcessing.M13bControlXStateSemantics
import QLean.SignalProcessing.M13bHadamardTrueStateSemantics
import QLean.SignalProcessing.M13bTwoFrameHermitianDilation
import QLean.SignalProcessing.M13bHermitianSuccessReflection

/-!
# M13b: pair-independent logical QSVT embedding

The logical source register is embedded once into the concrete signal-zero
image, then through the standard image-phase ancillas, and finally into the
control-false clean branch of the external compiler layout.  This definition
does not depend on a strict singular pair.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace M13bQSVTLogicalEmbedding

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness
open NativeQSPWitnessTransferModel
open SpectralSamplingProof.Analytic
open NativeSingularPairTwoFrame
open NativeSignalQSVTActual
open VerifiedCircuitCore.NativeEmbeddingImagePhase

noncomputable section

private theorem basisKetEmbeddingMatrix_trans
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (first : α ↪ β) (second : β ↪ γ) :
    basisKetEmbeddingMatrix (first.trans second) =
      basisKetEmbeddingMatrix second * basisKetEmbeddingMatrix first := by
  classical
  ext output input
  simp [basisKetEmbeddingMatrix, Matrix.mul_apply,
    Function.Embedding.trans]

private theorem basisKetEmbeddingMatrix_mulVec_basisKet
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (embedding : α ↪ β) (input : α) :
    (basisKetEmbeddingMatrix embedding).mulVec (basisKet input) =
      basisKet (embedding input) := by
  classical
  ext output
  simp only [basisKetEmbeddingMatrix, Matrix.mulVec, dotProduct, basisKet]
  rw [Finset.sum_eq_single input]
  · simp
  · intro other _ different
    simp [different]
  · simp

theorem fixedOutside_basisKetEmbeddingMatrix_mulVec
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (state : State (QubitBasis sourceQubits)) :
    (basisKetEmbeddingMatrix (fixedOutsideBasisEmbedding placement outside)).mulVec state =
      fixedOutsideStateEmbedding placement outside state := by
  classical
  rw [state_eq_sum_smul_basisKet119 state]
  rw [Matrix.mulVec_sum]
  rw [fixedOutsideStateEmbedding_finset_sum119]
  simp_rw [Matrix.mulVec_smul, fixedOutsideStateEmbedding_smul119,
    fixedOutsideStateEmbedding_basisKet,
    basisKetEmbeddingMatrix_mulVec_basisKet]

/-- The concrete three-stage basis embedding for the logical QSVT source
register.  It is deliberately independent of the strict singular pair. -/
def qsvtLogicalBasisEmbedding119
    {source : ExecutableHistoryExecutableHistory.AlignedCommonSource119}
    {assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source}
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) :
    executableSignalCleanIndex119 source ↪
      QubitBasis (widenedP18Qubits119 source domain fits assumptions circuitSource + 3) :=
  (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource).trans
    ((fixedOutsideBasisEmbedding
      (standardImagePhasePlacement
        (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (fun _ => false)).trans
      (fixedOutsideBasisEmbedding
        (M13bExternallyControlledCompute.m13bExternalControlLayout
          (widenedP18Qubits119 source domain fits assumptions circuitSource)).placement
        (M13bExternallyControlledCompute.m13bControlOutside
          (widenedP18Qubits119 source domain fits assumptions circuitSource) false)))

/-- The pair-independent physical logical embedding used by QSVT. -/
def qsvtLogicalEmbedding119
    {source : ExecutableHistoryExecutableHistory.AlignedCommonSource119}
    {assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source}
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) :
    Matrix
      (QubitBasis (widenedP18Qubits119 source domain fits assumptions circuitSource + 3))
      (executableSignalCleanIndex119 source) ℂ :=
  VerifiedMath.Basis.embeddingMatrix
    (qsvtLogicalBasisEmbedding119 domain fits circuitSource)

theorem qsvtLogicalEmbedding119_factor
    {source : ExecutableHistoryExecutableHistory.AlignedCommonSource119}
    {assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source}
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) :
    qsvtLogicalEmbedding119 domain fits circuitSource =
      basisKetEmbeddingMatrix
        (fixedOutsideBasisEmbedding
          (M13bExternallyControlledCompute.m13bExternalControlLayout
            (widenedP18Qubits119 source domain fits assumptions circuitSource)).placement
          (M13bExternallyControlledCompute.m13bControlOutside
            (widenedP18Qubits119 source domain fits assumptions circuitSource) false)) *
      basisKetEmbeddingMatrix
        (fixedOutsideBasisEmbedding
          (standardImagePhasePlacement
            (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
          (fun _ => false)) *
      executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource := by
  change basisKetEmbeddingMatrix (qsvtLogicalBasisEmbedding119 domain fits circuitSource) = _
  unfold qsvtLogicalBasisEmbedding119
  rw [basisKetEmbeddingMatrix_trans, basisKetEmbeddingMatrix_trans]
  rfl

end

end M13bQSVTLogicalEmbedding
