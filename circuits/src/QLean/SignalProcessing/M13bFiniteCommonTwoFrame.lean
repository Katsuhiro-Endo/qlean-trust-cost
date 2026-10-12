import QLean.Circuits.FiniteScientificPreparationBridge
import QLean.SignalProcessing.M13bFiniteOuterTwoFrame

/-! Connect the new finite P18 signal to the generic source-order QSP
two-frame theorem.  The ideal Gram operator is inherited from the proved
clean block, while the finite phase word remains an executable input. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace M13bFiniteCommonTwoFrame

open VerifiedCircuitCore
open QLean.Circuits.FiniteScientificPreparationBridge
open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open ExecutableHistoryHistoryEmbedding
open NativeConcreteP18QSPWitness
open NativeSingularPairTwoFrame
open NativeSignalQSVTActual
open NativeEmbeddingImagePhase
open NativeQSPWitnessTransferModel
open NativeQSPWitnessTwoFrameModel
open SpectralSamplingProof.Analytic

noncomputable section

set_option maxHeartbeats 1000000

/-- The forward query emitted by the new outer plan is the wire lift of the
new P18 signal.  Its expensive finite-basis denotation is kept behind the
abstract-width operator helper; only the plan-field identity is specialized. -/
theorem commonStep_forward_operator
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    :
    let circuitSource := theoreticalCanonicalP18CircuitSource
      source domain fits assumptions
    M13bFiniteOuterTwoFrame.realStepOperator
        (theoreticalCommonOuterPlan source domain fits assumptions)
        (.signal .forward) =
      M13bFiniteOuterTwoFrame.wireLiftDenotation
        (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit
        (NativeEmbeddingImagePhase.standardImagePhasePlacement
          (NativeSignalQSVTActual.ExecutableSignalP18Qubits119
            source domain fits assumptions circuitSource)) := by
  intro circuitSource
  apply M13bFiniteOuterTwoFrame.realStepOperator_signal_forward_wireLift
  exact theoreticalCommonOuterPlan_signalCircuit source domain fits assumptions

/-- The inverse step is the adjoint of the very same new finite signal. -/
theorem commonStep_adjoint_operator
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    :
    let circuitSource := theoreticalCanonicalP18CircuitSource
      source domain fits assumptions
    M13bFiniteOuterTwoFrame.realStepOperator
        (theoreticalCommonOuterPlan source domain fits assumptions)
        (.signal .adjoint) =
      star (M13bFiniteOuterTwoFrame.wireLiftDenotation
        (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit
        (NativeEmbeddingImagePhase.standardImagePhasePlacement
          (NativeSignalQSVTActual.ExecutableSignalP18Qubits119
            source domain fits assumptions circuitSource))) := by
  intro circuitSource
  apply M13bFiniteOuterTwoFrame.realStepOperator_signal_adjoint_wireLift
  exact theoreticalCommonOuterPlan_signalCircuit source domain fits assumptions

/-- The source and target phase steps keep the existing certified physical
image circuits.  Only the signal query changes its preparation subcircuit. -/
theorem commonStep_phase_operators
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (angle : ℝ) :
    M13bFiniteOuterTwoFrame.realStepOperator
        (theoreticalCommonOuterPlan source domain fits assumptions)
        (.projectorPhase .source angle) =
      M13bFiniteOuterTwoFrame.circuitDenotation
        (theoreticalFinitePhaseCircuit source fits (.const angle)) ∧
    M13bFiniteOuterTwoFrame.realStepOperator
        (theoreticalCommonOuterPlan source domain fits assumptions)
        (.projectorPhase .target angle) =
      M13bFiniteOuterTwoFrame.circuitDenotation
        (theoreticalFinitePhaseCircuit source fits (.const angle)) := by
  have phaseFields := theoreticalCommonOuterPlan_phaseCircuits
    source domain fits assumptions (.const angle)
  constructor
  · apply M13bFiniteOuterTwoFrame.realStepOperator_source_phase_of_circuit
    exact phaseFields.1
  · apply M13bFiniteOuterTwoFrame.realStepOperator_target_phase_of_circuit
    exact phaseFields.2

/-- The strict source frame of the new P18 signal, lifted with zeroed
external wires into the finite outer QSVT register. -/
noncomputable def commonStrictSourceFrame
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    Matrix (QubitBasis (widenedP18Qubits119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)))
      (Fin 2) ℂ :=
  let circuitSource := theoreticalCanonicalP18CircuitSource
    source domain fits assumptions
  widenedFrameLift119 source domain fits assumptions circuitSource
    (sourceFrame (theoreticalCommonP18StrictPairData
      source domain fits assumptions pair))

noncomputable def commonStrictTargetFrame
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    Matrix (QubitBasis (widenedP18Qubits119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)))
      (Fin 2) ℂ :=
  let circuitSource := theoreticalCanonicalP18CircuitSource
    source domain fits assumptions
  widenedFrameLift119 source domain fits assumptions circuitSource
    (targetFrame (theoreticalCommonP18StrictPairData
      source domain fits assumptions pair))

/-- Wire lifting intertwines any inner operator with the fixed-zero outside
frame lift.  The statement is polymorphic in the P18 circuit source, so no
large scientific width is unfolded while establishing linearity. -/
theorem arbitraryOperator_mul_widenedFrameLift
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119
      source domain fits assumptions)
    (U : Operator (QubitBasis
      (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource)))
    (frame : Matrix
      (QubitBasis
        (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (Fin 2) ℂ) :
    M13bFiniteOuterTwoFrame.frameLeftProduct (wireLiftOperator
        (standardImagePhasePlacement
          (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource)) U)
      (widenedFrameLift119 source domain fits assumptions circuitSource frame) =
    widenedFrameLift119 source domain fits assumptions circuitSource
      (M13bFiniteOuterTwoFrame.frameLeftProduct U frame) := by
  classical
  unfold M13bFiniteOuterTwoFrame.frameLeftProduct
  ext output column
  change applyOperator
      (wireLiftOperator
        (standardImagePhasePlacement
          (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource)) U)
      (fixedOutsideStateEmbedding
        (standardImagePhasePlacement
          (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
        (fun _ => false) (fun input => frame input column)) output = _
  rw [applyOperator_wireLift_fixedOutsideState119]
  rfl

theorem arbitraryAdjoint_mul_widenedFrameLift
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119
      source domain fits assumptions)
    (U : Operator (QubitBasis
      (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource)))
    (frame : Matrix
      (QubitBasis
        (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (Fin 2) ℂ) :
    M13bFiniteOuterTwoFrame.frameLeftProduct (star (wireLiftOperator
        (standardImagePhasePlacement
          (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource)) U))
      (widenedFrameLift119 source domain fits assumptions circuitSource frame) =
    widenedFrameLift119 source domain fits assumptions circuitSource
      (M13bFiniteOuterTwoFrame.frameLeftProduct (Matrix.conjTranspose U) frame) := by
  rw [star_wireLiftOperator119]
  simpa only [Matrix.star_eq_conjTranspose] using
    arbitraryOperator_mul_widenedFrameLift
      source domain fits assumptions circuitSource (star U) frame

theorem widenedFrameLift_frameRight
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119
      source domain fits assumptions)
    (frame : Matrix
      (QubitBasis
        (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (Fin 2) ℂ)
    (transfer : Matrix (Fin 2) (Fin 2) ℂ) :
    widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameRightProduct frame transfer) =
      M13bFiniteOuterTwoFrame.frameRightProduct
        (widenedFrameLift119 source domain fits assumptions circuitSource frame)
        transfer := by
  unfold M13bFiniteOuterTwoFrame.frameRightProduct
  exact widenedFrameLift119_mul source domain fits assumptions circuitSource
    frame transfer

theorem sourcePhase_mul_widenedFrameLift_wrapped
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119
      source domain fits assumptions)
    (angle : ℝ)
    (frame : Matrix
      (QubitBasis
        (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (Fin 2) ℂ) :
    M13bFiniteOuterTwoFrame.frameLeftProduct
        (widenedStepOperator119 (fun _ : String => 0)
          source domain fits assumptions circuitSource
          (.projectorPhase .source angle))
        (widenedFrameLift119 source domain fits assumptions circuitSource frame) =
      widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameLeftProduct
          (sourceImagePhaseOperator
            (executableSignalSourceEmbedding119
              source domain fits assumptions circuitSource) angle) frame) := by
  unfold M13bFiniteOuterTwoFrame.frameLeftProduct
  exact widenedSourcePhase_mul_widenedFrameLift119
    source domain fits assumptions circuitSource angle frame

theorem targetPhase_mul_widenedFrameLift_wrapped
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119
      source domain fits assumptions)
    (angle : ℝ)
    (frame : Matrix
      (QubitBasis
        (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (Fin 2) ℂ) :
    M13bFiniteOuterTwoFrame.frameLeftProduct
        (widenedStepOperator119 (fun _ : String => 0)
          source domain fits assumptions circuitSource
          (.projectorPhase .target angle))
        (widenedFrameLift119 source domain fits assumptions circuitSource frame) =
      widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameLeftProduct
          (sourceImagePhaseOperator
            (executableSignalSourceEmbedding119
              source domain fits assumptions circuitSource) angle) frame) := by
  unfold M13bFiniteOuterTwoFrame.frameLeftProduct
  exact widenedTargetPhase_mul_widenedFrameLift119
    source domain fits assumptions circuitSource angle frame

/-- The finite common signal rotates each strict physical singular pair by
the independently specified singular-value transfer matrix. -/
theorem commonFinitePhase_frame_eq_legacy
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (angle : ℝ)
    (frame : Matrix (QubitBasis (ExecutableSignalP18Qubits119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions))) (Fin 2) ℂ) :
    let circuitSource := theoreticalCanonicalP18CircuitSource source domain fits assumptions
    M13bFiniteOuterTwoFrame.frameLeftProduct
      (M13bFiniteOuterTwoFrame.circuitDenotation
        (theoreticalFinitePhaseCircuit source fits (.const angle)))
      (widenedFrameLift119 source domain fits assumptions circuitSource frame) =
    M13bFiniteOuterTwoFrame.frameLeftProduct
      (widenedStepOperator119 (fun _ : String => 0) source domain fits assumptions
        circuitSource (.projectorPhase .source angle))
      (widenedFrameLift119 source domain fits assumptions circuitSource frame) := by
  dsimp only
  rw [sourcePhase_mul_widenedFrameLift_wrapped]
  ext output column
  exact congrFun (theoreticalFinitePhase_apply_clean_state source domain fits assumptions
    (.const angle) (fun index => frame index column)) output

theorem commonStrict_forward
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    M13bFiniteOuterTwoFrame.frameLeftProduct
      (M13bFiniteOuterTwoFrame.realStepOperator
        (theoreticalCommonOuterPlan source domain fits assumptions)
        (.signal .forward))
      (commonStrictSourceFrame source domain fits assumptions pair) =
    M13bFiniteOuterTwoFrame.frameRightProduct
      (commonStrictTargetFrame source domain fits assumptions pair)
      (fixedPointSignalTransferMatrix (pair.sigma ^ 2) .forward) := by
  classical
  let circuitSource := theoreticalCanonicalP18CircuitSource
    source domain fits assumptions
  let data := theoreticalCommonP18StrictPairData
    source domain fits assumptions pair
  rw [commonStep_forward_operator]
  change M13bFiniteOuterTwoFrame.frameLeftProduct
      (M13bFiniteOuterTwoFrame.wireLiftDenotation
        (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit
        (standardImagePhasePlacement
          (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource)))
      (widenedFrameLift119 source domain fits assumptions circuitSource (sourceFrame data)) =
    M13bFiniteOuterTwoFrame.frameRightProduct
      (widenedFrameLift119 source domain fits assumptions circuitSource (targetFrame data))
      (fixedPointSignalTransferMatrix (pair.sigma ^ 2) .forward)
  calc
    _ = M13bFiniteOuterTwoFrame.frameLeftProduct
        (wireLiftOperator
          (standardImagePhasePlacement
            (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource)) data.U)
        (widenedFrameLift119 source domain fits assumptions circuitSource
          (sourceFrame data)) := by rfl
    _ = widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameLeftProduct data.U (sourceFrame data)) :=
      arbitraryOperator_mul_widenedFrameLift
        source domain fits assumptions circuitSource data.U (sourceFrame data)
    _ = widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameRightProduct
          (targetFrame data) (singularTransferMatrix data.sigma data.g)) := by
      have h := theoreticalCommonP18_twoFrame_forward
        source domain fits assumptions pair
      simpa only [M13bFiniteOuterTwoFrame.frameLeftProduct,
        M13bFiniteOuterTwoFrame.frameRightProduct] using
        congrArg (widenedFrameLift119 source domain fits assumptions circuitSource) h
    _ = M13bFiniteOuterTwoFrame.frameRightProduct
          (widenedFrameLift119 source domain fits assumptions circuitSource
            (targetFrame data))
          (singularTransferMatrix data.sigma data.g) :=
      widenedFrameLift_frameRight source domain fits assumptions circuitSource _ _
    _ = _ := by
      have sigmaEq : data.sigma = pair.sigma := rfl
      have gEq : data.g = pair.g := rfl
      rw [sigmaEq, gEq, strictPair_forward_transfer119 pair]

/-- The inverse query acts on the target frame by the adjoint of the same
independent singular-value transfer matrix. -/
theorem commonStrict_adjoint
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    M13bFiniteOuterTwoFrame.frameLeftProduct
      (M13bFiniteOuterTwoFrame.realStepOperator
        (theoreticalCommonOuterPlan source domain fits assumptions)
        (.signal .adjoint))
      (commonStrictTargetFrame source domain fits assumptions pair) =
    M13bFiniteOuterTwoFrame.frameRightProduct
      (commonStrictSourceFrame source domain fits assumptions pair)
      (fixedPointSignalTransferMatrix (pair.sigma ^ 2) .adjoint) := by
  classical
  let circuitSource := theoreticalCanonicalP18CircuitSource
    source domain fits assumptions
  let data := theoreticalCommonP18StrictPairData
    source domain fits assumptions pair
  rw [commonStep_adjoint_operator]
  change M13bFiniteOuterTwoFrame.frameLeftProduct
      (star (M13bFiniteOuterTwoFrame.wireLiftDenotation
        (theoreticalCommonP18SignalProgram source domain fits assumptions).signalCircuit
        (standardImagePhasePlacement
          (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))))
      (widenedFrameLift119 source domain fits assumptions circuitSource (targetFrame data)) =
    M13bFiniteOuterTwoFrame.frameRightProduct
      (widenedFrameLift119 source domain fits assumptions circuitSource (sourceFrame data))
      (fixedPointSignalTransferMatrix (pair.sigma ^ 2) .adjoint)
  calc
    _ = M13bFiniteOuterTwoFrame.frameLeftProduct
        (star (wireLiftOperator
          (standardImagePhasePlacement
            (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource)) data.U))
        (widenedFrameLift119 source domain fits assumptions circuitSource
          (targetFrame data)) := by rfl
    _ = widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameLeftProduct
          (Matrix.conjTranspose data.U) (targetFrame data)) :=
      arbitraryAdjoint_mul_widenedFrameLift
        source domain fits assumptions circuitSource data.U (targetFrame data)
    _ = widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameRightProduct
          (sourceFrame data)
          (Matrix.conjTranspose (singularTransferMatrix data.sigma data.g))) := by
      have h := theoreticalCommonP18_twoFrame_adjoint
        source domain fits assumptions pair
      simpa only [M13bFiniteOuterTwoFrame.frameLeftProduct,
        M13bFiniteOuterTwoFrame.frameRightProduct] using
        congrArg (widenedFrameLift119 source domain fits assumptions circuitSource) h
    _ = M13bFiniteOuterTwoFrame.frameRightProduct
          (widenedFrameLift119 source domain fits assumptions circuitSource
            (sourceFrame data))
          (Matrix.conjTranspose (singularTransferMatrix data.sigma data.g)) :=
      widenedFrameLift_frameRight source domain fits assumptions circuitSource _ _
    _ = _ := by
      have sigmaEq : data.sigma = pair.sigma := rfl
      have gEq : data.g = pair.g := rfl
      rw [sigmaEq, gEq, strictPair_adjoint_transfer119 pair]

/-- The source-role image phase acts on the new signal's strict source
frame by the canonical two-dimensional projector phase. -/
theorem commonStrict_source_phase
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (pair : ExecutableP18StrictSingularPair119 source assumptions)
    (angle : ℝ) :
    M13bFiniteOuterTwoFrame.frameLeftProduct
      (M13bFiniteOuterTwoFrame.realStepOperator
        (theoreticalCommonOuterPlan source domain fits assumptions)
        (.projectorPhase .source angle))
      (commonStrictSourceFrame source domain fits assumptions pair) =
    M13bFiniteOuterTwoFrame.frameRightProduct
      (commonStrictSourceFrame source domain fits assumptions pair)
      (fixedPointProjectorTransferMatrix .source angle) := by
  classical
  let circuitSource := theoreticalCanonicalP18CircuitSource
    source domain fits assumptions
  let data := theoreticalCommonP18StrictPairData
    source domain fits assumptions pair
  have phaseEq : sourceImagePhaseOperator
      (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
      angle = imagePhaseOperator data.E angle := by
    rw [theoreticalCommonSourceEmbedding_eq_aligned]
    exact sourceImagePhaseOperator_eq_imagePhaseOperator_basisKetEmbedding119 _ angle
  have phaseCircuit :=
    (commonStep_phase_operators source domain fits assumptions angle).1
  change M13bFiniteOuterTwoFrame.frameLeftProduct
      (M13bFiniteOuterTwoFrame.realStepOperator
        (theoreticalCommonOuterPlan source domain fits assumptions)
        (.projectorPhase .source angle))
      (widenedFrameLift119 source domain fits assumptions circuitSource (sourceFrame data)) =
    M13bFiniteOuterTwoFrame.frameRightProduct
      (widenedFrameLift119 source domain fits assumptions circuitSource (sourceFrame data))
      (fixedPointProjectorTransferMatrix .source angle)
  calc
    _ = M13bFiniteOuterTwoFrame.frameLeftProduct
        (widenedStepOperator119 (fun _ : String => 0)
          source domain fits assumptions circuitSource
          (.projectorPhase .source angle))
        (widenedFrameLift119 source domain fits assumptions circuitSource
          (sourceFrame data)) := by
      rw [phaseCircuit]
      exact commonFinitePhase_frame_eq_legacy source domain fits assumptions angle (sourceFrame data)
    _ = widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameLeftProduct
          (sourceImagePhaseOperator
            (executableSignalSourceEmbedding119
              source domain fits assumptions circuitSource) angle)
          (sourceFrame data)) :=
      sourcePhase_mul_widenedFrameLift_wrapped
        source domain fits assumptions circuitSource angle (sourceFrame data)
    _ = widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameLeftProduct
          (imagePhaseOperator data.E angle) (sourceFrame data)) := by
      rw [phaseEq]
    _ = widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameRightProduct
          (sourceFrame data) (fixedPointProjectorTransferMatrix .source angle)) := by
      simpa only [M13bFiniteOuterTwoFrame.frameLeftProduct,
        M13bFiniteOuterTwoFrame.frameRightProduct] using
        congrArg (widenedFrameLift119 source domain fits assumptions circuitSource)
          (strictFrame_source_phase119 data angle)
    _ = _ := widenedFrameLift_frameRight
      source domain fits assumptions circuitSource _ _

/-- The target-role phase uses the same physical clean image, with the
opposite ordering of strict-frame columns. -/
theorem commonStrict_target_phase
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (pair : ExecutableP18StrictSingularPair119 source assumptions)
    (angle : ℝ) :
    M13bFiniteOuterTwoFrame.frameLeftProduct
      (M13bFiniteOuterTwoFrame.realStepOperator
        (theoreticalCommonOuterPlan source domain fits assumptions)
        (.projectorPhase .target angle))
      (commonStrictTargetFrame source domain fits assumptions pair) =
    M13bFiniteOuterTwoFrame.frameRightProduct
      (commonStrictTargetFrame source domain fits assumptions pair)
      (fixedPointProjectorTransferMatrix .target angle) := by
  classical
  let circuitSource := theoreticalCanonicalP18CircuitSource
    source domain fits assumptions
  let data := theoreticalCommonP18StrictPairData
    source domain fits assumptions pair
  have phaseEq : sourceImagePhaseOperator
      (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
      angle = imagePhaseOperator data.E angle := by
    rw [theoreticalCommonSourceEmbedding_eq_aligned]
    exact sourceImagePhaseOperator_eq_imagePhaseOperator_basisKetEmbedding119 _ angle
  have phaseCircuit :=
    (commonStep_phase_operators source domain fits assumptions angle).2
  change M13bFiniteOuterTwoFrame.frameLeftProduct
      (M13bFiniteOuterTwoFrame.realStepOperator
        (theoreticalCommonOuterPlan source domain fits assumptions)
        (.projectorPhase .target angle))
      (widenedFrameLift119 source domain fits assumptions circuitSource (targetFrame data)) =
    M13bFiniteOuterTwoFrame.frameRightProduct
      (widenedFrameLift119 source domain fits assumptions circuitSource (targetFrame data))
      (fixedPointProjectorTransferMatrix .target angle)
  calc
    _ = M13bFiniteOuterTwoFrame.frameLeftProduct
        (widenedStepOperator119 (fun _ : String => 0)
          source domain fits assumptions circuitSource
          (.projectorPhase .target angle))
        (widenedFrameLift119 source domain fits assumptions circuitSource
          (targetFrame data)) := by
      rw [phaseCircuit]
      exact commonFinitePhase_frame_eq_legacy source domain fits assumptions angle (targetFrame data)
    _ = widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameLeftProduct
          (sourceImagePhaseOperator
            (executableSignalSourceEmbedding119
              source domain fits assumptions circuitSource) angle)
          (targetFrame data)) :=
      targetPhase_mul_widenedFrameLift_wrapped
        source domain fits assumptions circuitSource angle (targetFrame data)
    _ = widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameLeftProduct
          (imagePhaseOperator data.E angle) (targetFrame data)) := by
      rw [phaseEq]
    _ = widenedFrameLift119 source domain fits assumptions circuitSource
        (M13bFiniteOuterTwoFrame.frameRightProduct
          (targetFrame data) (fixedPointProjectorTransferMatrix .target angle)) := by
      simpa only [M13bFiniteOuterTwoFrame.frameLeftProduct,
        M13bFiniteOuterTwoFrame.frameRightProduct] using
        congrArg (widenedFrameLift119 source domain fits assumptions circuitSource)
          (strictFrame_target_phase119 data angle)
    _ = _ := widenedFrameLift_frameRight
      source domain fits assumptions circuitSource _ _

/-- All four circuit equations for the new finite P18 query, packaged for
the source-order QSP word theorem.  No property of an unrelated preparation
unitary or user-supplied phase accuracy is assumed. -/
theorem commonStrict_twoFrameWitness
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    M13bFiniteOuterTwoFrame.PlanTwoFrameWitness
      (theoreticalCommonOuterPlan source domain fits assumptions)
      (pair.sigma ^ 2)
      (commonStrictSourceFrame source domain fits assumptions pair)
      (commonStrictTargetFrame source domain fits assumptions pair) := by
  apply M13bFiniteOuterTwoFrame.PlanTwoFrameWitness.ofWrapped
  · exact commonStrict_forward source domain fits assumptions pair
  · exact commonStrict_adjoint source domain fits assumptions pair
  · intro angle
    exact commonStrict_source_phase source domain fits assumptions pair angle
  · intro angle
    exact commonStrict_target_phase source domain fits assumptions pair angle

end
end M13bFiniteCommonTwoFrame
