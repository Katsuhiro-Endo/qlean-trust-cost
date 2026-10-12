import QLean.SignalProcessing.M13bBoundaryNoLeak
import QLean.SignalProcessing.NativeQSPWitnessTwoFrameModel

set_option autoImplicit false

namespace M13bGramBoundaryWitness

open VerifiedCircuitCore
open NativeConcreteP18QSPWitness
open NativeSingularPairTwoFrame
open NativeQSPWitnessTransferModel
open NativeQSPWitnessTwoFrameModel
open M13bGramBasisStrictPair
open M13bBoundaryNoLeak
open SpectralSamplingProof.Analytic

noncomputable def boundaryGramVector119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source) :
    Column (executableSignalCleanIndex119 source) :=
  realColumn119
    ((DalzellDilation.gramBasis130 (executableGramOperator119 source assumptions) j).ofLp)

noncomputable def boundaryGramImage119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source) :
    Column (executableSignalCleanIndex119 source) :=
  realColumn119
    ((executableGramOperator119 source assumptions).mulVec
      ((DalzellDilation.gramBasis130 (executableGramOperator119 source assumptions) j).ofLp))

theorem boundaryGramVector_inner_one119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source) :
    inner ℂ (euclideanColumn (boundaryGramVector119 source assumptions j))
      (euclideanColumn (boundaryGramVector119 source assumptions j)) = 1 := by
  rw [inner_pi_complex]
  have h := DalzellDilation.gram_basis_dot_self130
    (executableGramOperator119 source assumptions) j
  simpa [boundaryGramVector119, realColumn119, dotProduct] using congrArg (fun x : ℝ => (x : ℂ)) h

theorem boundaryGramImage_inner_one119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source)
    (hj : DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 1) :
    inner ℂ (euclideanColumn (boundaryGramImage119 source assumptions j))
      (euclideanColumn (boundaryGramImage119 source assumptions j)) = 1 := by
  rw [inner_pi_complex]
  have h := DalzellDilation.gram_eigenvalue_eq_unitNormSquared130
    (executableGramOperator119 source assumptions) j
  rw [hj] at h
  simpa [boundaryGramImage119, realColumn119, JenningsHistory.unitNormSquared,
    dotProduct] using congrArg (fun x : ℝ => (x : ℂ)) h.symm

noncomputable def boundarySourceFrame119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions)
    (j : executableSignalCleanIndex119 source) :=
  twoColumnFrame
    ((executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource).mulVec
      (boundaryGramVector119 source assumptions j)) 0

noncomputable def boundaryTargetFrame119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions)
    (j : executableSignalCleanIndex119 source) :=
  twoColumnFrame 0
    ((executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource).mulVec
      (boundaryGramImage119 source assumptions j))

theorem boundary_clean_projector119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions)
    (x : Column (executableSignalCleanIndex119 source)) :
    (cleanProjector
      (executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource)).mulVec
      ((executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource).mulVec x) =
      (executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource).mulVec x := by
  unfold cleanProjector
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_assoc,
    executableSignalSourceKetEmbedding119_isometry source domain fits assumptions circuitSource,
    Matrix.mul_one]

theorem boundaryFrame_source_phase119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions)
    (j : executableSignalCleanIndex119 source) (angle : ℝ) :
    VerifiedCircuitCore.NativeEmbeddingImagePhase.sourceImagePhaseOperator
      (NativeSignalQSVTActual.executableSignalSourceEmbedding119 source domain fits assumptions circuitSource) angle *
      boundarySourceFrame119 source domain fits assumptions circuitSource j =
      boundarySourceFrame119 source domain fits assumptions circuitSource j *
        fixedPointProjectorTransferMatrix .source angle := by
  have hphase :
      VerifiedCircuitCore.NativeEmbeddingImagePhase.sourceImagePhaseOperator
          (NativeSignalQSVTActual.executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
          angle =
        imagePhaseOperator
          (executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource) angle := by
    simpa [executableSignalSourceKetEmbedding119] using
      (sourceImagePhaseOperator_eq_imagePhaseOperator_basisKetEmbedding119
        (NativeSignalQSVTActual.executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
        angle)
  rw [hphase]
  unfold boundarySourceFrame119
  rw [operator_mul_twoColumnFrame,
    imagePhase_apply_of_projector_one _ angle _
      (boundary_clean_projector119 source domain fits assumptions circuitSource _),
    imagePhase_apply_of_projector_zero _ angle 0 (by simp)]
  ext output column
  fin_cases column <;>
    simp [twoColumnFrame, fixedPointProjectorTransferMatrix,
      Matrix.mul_apply, fixedPointSourceIndex, mul_comm]

set_option maxHeartbeats 800000 in
theorem boundaryFrame_target_phase119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions)
    (j : executableSignalCleanIndex119 source) (angle : ℝ) :
    VerifiedCircuitCore.NativeEmbeddingImagePhase.sourceImagePhaseOperator
      (NativeSignalQSVTActual.executableSignalSourceEmbedding119 source domain fits assumptions circuitSource) angle *
      boundaryTargetFrame119 source domain fits assumptions circuitSource j =
      boundaryTargetFrame119 source domain fits assumptions circuitSource j *
        fixedPointProjectorTransferMatrix .target angle := by
  have hphase :
      VerifiedCircuitCore.NativeEmbeddingImagePhase.sourceImagePhaseOperator
          (NativeSignalQSVTActual.executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
          angle =
        imagePhaseOperator
          (executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource) angle := by
    simpa [executableSignalSourceKetEmbedding119] using
      (sourceImagePhaseOperator_eq_imagePhaseOperator_basisKetEmbedding119
        (NativeSignalQSVTActual.executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
        angle)
  rw [hphase]
  unfold boundaryTargetFrame119
  rw [operator_mul_twoColumnFrame,
    imagePhase_apply_of_projector_zero _ angle 0 (by simp),
    imagePhase_apply_of_projector_one _ angle _
      (boundary_clean_projector119 source domain fits assumptions circuitSource _)]
  ext output column
  fin_cases column <;>
    simp [twoColumnFrame, fixedPointProjectorTransferMatrix,
      Matrix.mul_apply, fixedPointTargetIndex, mul_comm]

noncomputable def widenedBoundarySourceFrame119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119 source domain fits assumptions)
    (j : executableSignalCleanIndex119 source) :=
  widenedFrameLift119 source domain fits assumptions circuitSource
    (boundarySourceFrame119 source domain fits assumptions circuitSource j)

noncomputable def widenedBoundaryTargetFrame119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119 source domain fits assumptions)
    (j : executableSignalCleanIndex119 source) :=
  widenedFrameLift119 source domain fits assumptions circuitSource
    (boundaryTargetFrame119 source domain fits assumptions circuitSource j)

end M13bGramBoundaryWitness
