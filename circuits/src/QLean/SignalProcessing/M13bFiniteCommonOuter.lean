import QLean.SignalProcessing.M13bFiniteCommonTwoFrame
import QLean.SignalProcessing.M13bFiniteOuterIntertwining
import QLean.SignalProcessing.M13bUnitaritySemanticVerification

/-! The common finite outer compiler instantiated with the new preparation
and its proved P18 signal.  No legacy circuit-syntax equality is used. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace M13bFiniteCommonOuter

open VerifiedCircuitCore VerifiedCircuitCore.NativeEmbeddingImagePhase
open ExecutableHistoryExecutableHistory ExecutableHistoryExecutableP18
open ExecutableHistoryHistoryEmbedding NativeConcreteP18QSPWitness
open QLean.Circuits.FiniteScientificPreparationBridge
open M13bFiniteOuterTwoFrame M13bFiniteOuterIntertwining M13bFiniteCommonTwoFrame
open NativeQSPWitnessTwoFrameModel NativeQSPWitnessTransferModel
open SpectralSamplingProof.Analytic

noncomputable section

theorem commonPlan_layout
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions] :
    (theoreticalCommonOuterPlan source domain fits assumptions).layout =
      M13bExternallyControlledCompute.m13bExternalControlLayout
        (widenedP18Qubits119 source domain fits assumptions
          (theoreticalCanonicalP18CircuitSource source domain fits assumptions)) := by
  unfold theoreticalCommonOuterPlan
  rfl

theorem commonPlan_phaseEvaluation
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions] :
    PlanPhaseEvaluation (theoreticalCommonOuterPlan source domain fits assumptions) := by
  constructor
  · intro angle
    rw [(theoreticalCommonOuterPlan_phaseCircuits source domain fits assumptions angle).1,
      (theoreticalCommonOuterPlan_phaseCircuits source domain fits assumptions
        (.const (angle.eval (fun _ : String => 0)))).1]
    exact theoreticalFinitePhase_denote_eval source fits angle
  · intro angle
    rw [(theoreticalCommonOuterPlan_phaseCircuits source domain fits assumptions angle).2,
      (theoreticalCommonOuterPlan_phaseCircuits source domain fits assumptions
        (.const (angle.eval (fun _ : String => 0)))).2]
    exact theoreticalFinitePhase_denote_eval source fits angle

/-- The entire common outer circuit, not only its word, acts by the
independent Hermitianized transfer on every strict singular-pair frame.
Strict here includes singular value zero; value one has its own frame. -/
theorem commonStrict_outer_intertwines
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (pair : ExecutableP18StrictSingularPair119 source assumptions)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (wellFormed : FrameWord .source
      (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))) .target) :
    controlLeftProduct
      (circuitDenotation ((theoreticalCommonOuterPlan source domain fits assumptions).compile
        program .pi)) (commonStrictSourceFrame source domain fits assumptions pair) =
    controlRightProduct (commonStrictSourceFrame source domain fits assumptions pair)
      (outerTransfer (abstractTransferWord (pair.sigma ^ 2)
        (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))))) := by
  exact compile_intertwines_of_twoFrame
    (theoreticalCommonOuterPlan source domain fits assumptions)
    (commonPlan_layout source domain fits assumptions)
    (commonPlan_phaseEvaluation source domain fits assumptions)
    (pair.sigma ^ 2)
    (commonStrictSourceFrame source domain fits assumptions pair)
    (commonStrictTargetFrame source domain fits assumptions pair)
    (commonStrict_twoFrameWitness source domain fits assumptions pair)
    program wellFormed
    (M13bUnitaritySemanticVerification.strict_transfer_word_unitary pair _)

end
end M13bFiniteCommonOuter
