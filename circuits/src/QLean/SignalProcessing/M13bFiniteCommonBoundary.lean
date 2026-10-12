import QLean.SignalProcessing.M13bFiniteCommonOuter
import QLean.SignalProcessing.M13bGramBoundaryWitness
import QLean.SignalProcessing.M13bGramBoundaryTransferUnitary

/-! The unit-singular-value endpoint for the new common P18 signal.  Its
clean compression saturates a unitary norm, so there is no discarded leakage.
The endpoint frame has a zero column and is deliberately handled separately
from the strict-pair formulas that divide by the complementary amplitude. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace M13bFiniteCommonBoundary

open VerifiedCircuitCore NativeEmbeddingImagePhase
open ExecutableHistoryExecutableHistory ExecutableHistoryExecutableP18
open ExecutableHistoryHistoryEmbedding NativeConcreteP18QSPWitness NativeSignalQSVTActual
open QLean.Circuits.FiniteScientificPreparationBridge
open M13bFiniteOuterTwoFrame M13bFiniteOuterIntertwining
open M13bFiniteCommonTwoFrame M13bFiniteCommonOuter
open NativeQSPWitnessTwoFrameModel NativeQSPWitnessTransferModel NativeSingularPairTwoFrame
open SpectralSamplingProof.Analytic M13bGramBasisStrictPair M13bGramBoundaryWitness

noncomputable section

def commonSignalOperator
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions] :
    Operator (QubitBasis (ExecutableSignalP18Qubits119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions))) :=
  circuitDenotation (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit

theorem commonSignal_cleanBlock
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions] :
    cleanBlock (commonSignalOperator source domain fits assumptions)
      (executableSignalSourceKetEmbedding119 source domain fits assumptions
        (theoreticalCanonicalP18CircuitSource source domain fits assumptions)) =
      executableGNuOperator119 source assumptions := by
  change cleanBlock (commonSignalOperator source domain fits assumptions)
    (basisKetEmbeddingMatrix (executableSignalSourceEmbedding119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions))) = _
  rw [theoreticalCommonSourceEmbedding_eq_aligned]
  exact theoreticalCommonP18Signal_cleanBlock source domain fits assumptions

theorem commonSignal_star_left
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions] :
    Matrix.conjTranspose (commonSignalOperator source domain fits assumptions) *
      commonSignalOperator source domain fits assumptions = 1 :=
  (Matrix.mem_unitaryGroup_iff').mp
    (primitiveCircuit_denote_mem_unitaryGroup (fun _ : String => 0) _)

theorem commonBoundary_compression
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (j : executableSignalCleanIndex119 source) :
    let E := executableSignalSourceKetEmbedding119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    (Matrix.conjTranspose E).mulVec
      ((commonSignalOperator source domain fits assumptions).mulVec
        (E.mulVec (boundaryGramVector119 source assumptions j))) =
      boundaryGramImage119 source assumptions j := by
  dsimp only
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  change (cleanBlock (commonSignalOperator source domain fits assumptions)
    (executableSignalSourceKetEmbedding119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions))).mulVec
        (boundaryGramVector119 source assumptions j) = _
  rw [commonSignal_cleanBlock]
  exact executableGNu_mulVec_realColumn119 source assumptions _

theorem commonBoundary_no_leakage_forward
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (j : executableSignalCleanIndex119 source)
    (endpoint : DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 1) :
    let E := executableSignalSourceKetEmbedding119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    (commonSignalOperator source domain fits assumptions).mulVec
      (E.mulVec (boundaryGramVector119 source assumptions j)) =
      E.mulVec (boundaryGramImage119 source assumptions j) := by
  apply M13bBoundaryNoLeak.no_leakage_of_unit_saturation
  · exact commonSignal_star_left source domain fits assumptions
  · exact executableSignalSourceKetEmbedding119_isometry source domain fits assumptions _
  · exact commonBoundary_compression source domain fits assumptions j
  · exact boundaryGramVector_inner_one119 source assumptions j
  · exact boundaryGramImage_inner_one119 source assumptions j endpoint

theorem commonBoundary_no_leakage_adjoint
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (j : executableSignalCleanIndex119 source)
    (endpoint : DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 1) :
    let E := executableSignalSourceKetEmbedding119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    (Matrix.conjTranspose (commonSignalOperator source domain fits assumptions)).mulVec
      (E.mulVec (boundaryGramImage119 source assumptions j)) =
      E.mulVec (boundaryGramVector119 source assumptions j) := by
  dsimp only
  rw [← commonBoundary_no_leakage_forward source domain fits assumptions j endpoint,
    Matrix.mulVec_mulVec, commonSignal_star_left, Matrix.one_mulVec]

theorem commonBoundary_inner_forward
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (j : executableSignalCleanIndex119 source)
    (endpoint : DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 1) :
    let circuitSource := theoreticalCanonicalP18CircuitSource source domain fits assumptions
    frameLeftProduct (commonSignalOperator source domain fits assumptions)
      (boundarySourceFrame119 source domain fits assumptions circuitSource j) =
    frameRightProduct (boundaryTargetFrame119 source domain fits assumptions circuitSource j)
      (fixedPointSignalTransferMatrix 1 .forward) := by
  dsimp only
  have forward := commonBoundary_no_leakage_forward source domain fits assumptions j endpoint
  ext output column
  fin_cases column
  · simpa [frameLeftProduct, frameRightProduct, boundarySourceFrame119, boundaryTargetFrame119,
      twoColumnFrame, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      fixedPointSignalTransferMatrix, fixedPointSourceAmplitude, fixedPointTargetAmplitude] using
        congrFun forward output
  · simp [frameLeftProduct, frameRightProduct, boundarySourceFrame119, boundaryTargetFrame119,
      twoColumnFrame, Matrix.mul_apply, fixedPointSignalTransferMatrix,
      fixedPointSourceAmplitude, fixedPointTargetAmplitude]

theorem commonBoundary_inner_adjoint
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (j : executableSignalCleanIndex119 source)
    (endpoint : DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 1) :
    let circuitSource := theoreticalCanonicalP18CircuitSource source domain fits assumptions
    frameLeftProduct (Matrix.conjTranspose (commonSignalOperator source domain fits assumptions))
      (boundaryTargetFrame119 source domain fits assumptions circuitSource j) =
    frameRightProduct (boundarySourceFrame119 source domain fits assumptions circuitSource j)
      (fixedPointSignalTransferMatrix 1 .adjoint) := by
  dsimp only
  have adjoint := commonBoundary_no_leakage_adjoint source domain fits assumptions j endpoint
  ext output column
  fin_cases column
  · simp [frameLeftProduct, frameRightProduct, boundarySourceFrame119, boundaryTargetFrame119,
      twoColumnFrame, Matrix.mul_apply, fixedPointSignalTransferMatrix,
      fixedPointSourceAmplitude, fixedPointTargetAmplitude]
  · simpa [frameLeftProduct, frameRightProduct, boundarySourceFrame119, boundaryTargetFrame119,
      twoColumnFrame, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      fixedPointSignalTransferMatrix, fixedPointSourceAmplitude, fixedPointTargetAmplitude,
      Matrix.conjTranspose_apply] using congrFun adjoint output

def commonBoundarySourceFrame
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source) :=
  widenedBoundarySourceFrame119 source domain fits assumptions
    (theoreticalCanonicalP18CircuitSource source domain fits assumptions) j

def commonBoundaryTargetFrame
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source) :=
  widenedBoundaryTargetFrame119 source domain fits assumptions
    (theoreticalCanonicalP18CircuitSource source domain fits assumptions) j

/-- Keep the phase transport abstract in the signal width.  Instantiating
the full two-frame record before wrapping its products expands the concrete
scientific layout during definitional equality checking. -/
theorem boundarySource_phase_wrapped
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (j : executableSignalCleanIndex119 source) (angle : ℝ) :
    frameLeftProduct (widenedStepOperator119 (fun _ : String => 0)
      source domain fits assumptions circuitSource (.projectorPhase .source angle))
      (widenedBoundarySourceFrame119 source domain fits assumptions circuitSource j) =
    frameRightProduct
      (widenedBoundarySourceFrame119 source domain fits assumptions circuitSource j)
      (fixedPointProjectorTransferMatrix .source angle) := by
  change frameLeftProduct _ (widenedFrameLift119 source domain fits assumptions circuitSource
    (boundarySourceFrame119 source domain fits assumptions circuitSource j)) = _
  rw [sourcePhase_mul_widenedFrameLift_wrapped]
  have action := boundaryFrame_source_phase119 source domain fits assumptions circuitSource j angle
  change frameLeftProduct _ _ = frameRightProduct _ _ at action
  rw [action, widenedFrameLift_frameRight]
  rfl

theorem boundaryTarget_phase_wrapped
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (j : executableSignalCleanIndex119 source) (angle : ℝ) :
    frameLeftProduct (widenedStepOperator119 (fun _ : String => 0)
      source domain fits assumptions circuitSource (.projectorPhase .target angle))
      (widenedBoundaryTargetFrame119 source domain fits assumptions circuitSource j) =
    frameRightProduct
      (widenedBoundaryTargetFrame119 source domain fits assumptions circuitSource j)
      (fixedPointProjectorTransferMatrix .target angle) := by
  change frameLeftProduct _ (widenedFrameLift119 source domain fits assumptions circuitSource
    (boundaryTargetFrame119 source domain fits assumptions circuitSource j)) = _
  rw [targetPhase_mul_widenedFrameLift_wrapped]
  have action := boundaryFrame_target_phase119 source domain fits assumptions circuitSource j angle
  change frameLeftProduct _ _ = frameRightProduct _ _ at action
  rw [action, widenedFrameLift_frameRight]
  rfl

theorem commonBoundary_twoFrameWitness
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (j : executableSignalCleanIndex119 source)
    (endpoint : DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 1) :
    PlanTwoFrameWitness (theoreticalCommonOuterPlan source domain fits assumptions) 1
      (commonBoundarySourceFrame source domain fits assumptions j)
      (commonBoundaryTargetFrame source domain fits assumptions j) := by
  let circuitSource := theoreticalCanonicalP18CircuitSource source domain fits assumptions
  apply PlanTwoFrameWitness.ofWrapped
  · rw [commonStep_forward_operator]
    change frameLeftProduct
      (wireLiftOperator (standardImagePhasePlacement
        (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
        (commonSignalOperator source domain fits assumptions))
      (widenedFrameLift119 source domain fits assumptions circuitSource
        (boundarySourceFrame119 source domain fits assumptions circuitSource j)) =
      frameRightProduct (widenedFrameLift119 source domain fits assumptions circuitSource
        (boundaryTargetFrame119 source domain fits assumptions circuitSource j)) _
    rw [arbitraryOperator_mul_widenedFrameLift,
      commonBoundary_inner_forward source domain fits assumptions j endpoint,
      widenedFrameLift_frameRight]
  · rw [commonStep_adjoint_operator]
    change frameLeftProduct
      (star (wireLiftOperator (standardImagePhasePlacement
        (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
        (commonSignalOperator source domain fits assumptions)))
      (widenedFrameLift119 source domain fits assumptions circuitSource
        (boundaryTargetFrame119 source domain fits assumptions circuitSource j)) =
      frameRightProduct (widenedFrameLift119 source domain fits assumptions circuitSource
        (boundarySourceFrame119 source domain fits assumptions circuitSource j)) _
    rw [arbitraryAdjoint_mul_widenedFrameLift,
      commonBoundary_inner_adjoint source domain fits assumptions j endpoint,
      widenedFrameLift_frameRight]
  · intro angle
    rw [(commonStep_phase_operators source domain fits assumptions angle).1]
    exact (commonFinitePhase_frame_eq_legacy source domain fits assumptions angle
      (boundarySourceFrame119 source domain fits assumptions circuitSource j)).trans
      (boundarySource_phase_wrapped source domain fits assumptions circuitSource j angle)
  · intro angle
    rw [(commonStep_phase_operators source domain fits assumptions angle).2]
    exact (commonFinitePhase_frame_eq_legacy source domain fits assumptions angle
      (boundaryTargetFrame119 source domain fits assumptions circuitSource j)).trans
      (boundaryTarget_phase_wrapped source domain fits assumptions circuitSource j angle)

theorem commonBoundary_outer_intertwines
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (j : executableSignalCleanIndex119 source)
    (endpoint : DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 1)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (wellFormed : FrameWord .source
      (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))) .target) :
    controlLeftProduct
      (circuitDenotation ((theoreticalCommonOuterPlan source domain fits assumptions).compile
        program .pi)) (commonBoundarySourceFrame source domain fits assumptions j) =
    controlRightProduct (commonBoundarySourceFrame source domain fits assumptions j)
      (outerTransfer (abstractTransferWord 1
        (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))))) := by
  exact compile_intertwines_of_twoFrame
    (theoreticalCommonOuterPlan source domain fits assumptions)
    (commonPlan_layout source domain fits assumptions)
    (commonPlan_phaseEvaluation source domain fits assumptions)
    1 (commonBoundarySourceFrame source domain fits assumptions j)
    (commonBoundaryTargetFrame source domain fits assumptions j)
    (commonBoundary_twoFrameWitness source domain fits assumptions j endpoint)
    program wellFormed
    (M13bGramBoundaryTransferUnitary.boundary_transfer_word_unitary _)

/-- Every logical Gram-basis vector is covered.  The first branch includes
the zero eigenvalue through `executableGramZeroStrictPair119`; no nonzero
spectral assumption is introduced. -/
theorem commonGram_strict_or_endpoint
    (source : AlignedCommonSource119) (assumptions : ExecutableM13Assumptions119 source)
    (j : executableSignalCleanIndex119 source) :
    Real.sqrt (DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j) < 1 ∨
      DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 1 := by
  have upper := executable_gram_basis_sqrt_le_one119 source assumptions j
  by_cases strict : Real.sqrt
      (DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j) < 1
  · exact Or.inl strict
  · right
    have atOne : Real.sqrt
        (DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j) = 1 :=
      le_antisymm upper (le_of_not_gt strict)
    have square := Real.sq_sqrt (DalzellDilation.gram_eigenvalue_nonneg130
      (executableGramOperator119 source assumptions) j)
    rw [atOne] at square
    simpa using square.symm

end
end M13bFiniteCommonBoundary
