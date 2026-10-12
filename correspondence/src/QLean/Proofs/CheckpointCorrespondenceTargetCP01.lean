import VerifiedMath.Basis
import VerifiedMath.FiniteComplex
import VerifiedMath.FiniteDistribution
import QLean.MathematicalSpecifications.PublicCheckpointData
import VerifiedMath.OperatorRelations
import QLean.Circuits.CheckpointCircuits
import QLean.Correspondence.BenchmarkHistoryCorrespondence
import QLean.Correspondence.KernelReflectionTransport
import QLean.SignalProcessing.M13bSpecification
import QLean.Correspondence.RepresentationTransport
import QLean.MathematicalSpecifications.CoalescingWalkModel
import Mathlib.Tactic
import QLean.Generator.Analysis.QGenerator
import QLean.SignalProcessing.M13bPrimitiveCandidate
import QLean.SignalProcessing.JenningsM13AnalyticBounds
import QLean.History.JenningsExecutableHistoryDomain
import QLean.SignalProcessing.M13cSpecification
import QLean.SignalProcessing.M13bQSVTLogicalEmbedding
import QLean.Circuits.Foundation.ClassicalArithmeticCorrectnessAnalytic
import Mathlib
import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.History.Jennings.PureSpec
import QLean.SignalProcessing.PhaseScheduleProofsPhaseWordContract
import QLean.SignalProcessing.PhaseScheduleProofsChebyshevContract
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.PhaseShiftMacros
import QLean.History.HistoryEmbeddingNorm
import QLean.History.Jennings.ProofEstablishedBridge
import QLean.Circuits.Foundation.FinitePhaseTransformAnalytic
import QLean.Circuits.Foundation.CircuitListLemmas
import QLean.Circuits.Foundation.Foundations
import QLean.Circuits.Foundation.QubitBasisEncoding
import QLean.Circuits.Foundation.QuantumFourierAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic
import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.WireEmbeddingAnalytic
import QLean.Circuits.Foundation.ReversibleLogicCleanAnalytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkMultiControlledXCorrectnessAnalytic
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2
import QLean.Circuits.Foundation.QuantumFourier
import QLean.Circuits.Foundation.OperatorL2Error
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import QLean.Circuits.Foundation.Metrics
import QLean.Circuits.Foundation.ReversibleLogic
import QLean.Circuits.Foundation.WireEmbedding
import QLean.Circuits.Foundation.WireEmbeddingL2Analytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkClean
import QLean.Circuits.Foundation.ControlledConstantAdderAnalytic
import QLean.Analysis.StateNormBounds
import QLean.SignalProcessing.NativeSingularPairTwoFrame
import QLean.Generator.Implementation.QDecoderCorrectness
import QLean.Proofs.CheckpointCorrespondenceCore
import QLean.MathematicalSpecifications.DelimiterEncodingProofs
import QLean.MathematicalSpecifications.Targets
import QLean.Correspondence.GeneralRepresentationTransport

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Proofs.CheckpointCorrespondence

noncomputable section

open scoped Matrix.Norms.L2Operator

open QLean.MathematicalSpecifications
open QLean.MathematicalSpecifications.PublicCheckpoints
open QLean.MathematicalSpecifications.Targets
open QLean.Correspondence.RepresentationTransport

open QLean.Proofs.CheckpointCorrespondence.Internal
open QLean.Circuits.CheckpointCircuits
open ProbabilityGeneratorQProof
open HistoryBlockEncoding.M09Bridge

namespace General

abbrev parametersToCircuit :=
  QLean.Correspondence.GeneralRepresentationTransport.parametersToCircuit

abbrev configurationEquiv :=
  QLean.Correspondence.GeneralRepresentationTransport.configurationEquiv

abbrev SpecificationConfiguration
    (parameters : CoalescingWalkModel.Parameters) :=
  CoalescingWalkModel.Configuration parameters

theorem width_eq_general (parameters : CoalescingWalkModel.Parameters) :
    delimiterWidth parameters =
      (parametersToCircuit parameters).systemWidth := by
  exact QLean.Correspondence.GeneralRepresentationTransport.delimiterWidth_eq_systemWidth
    parameters

/-- The complete mathematical delimiter-word space and the complete physical
system register have the same width for every admissible `q,K`. -/
abbrev delimiterWordEquiv :=
  QLean.Correspondence.GeneralRepresentationTransport.delimiterWordEquiv

theorem configurationEncoding_transport_general
    (parameters : CoalescingWalkModel.Parameters)
    (configuration : SpecificationConfiguration parameters) :
    delimiterWordEquiv parameters
        (configurationEncoding parameters configuration) =
      delimiterEncoding (configurationEquiv parameters configuration) := by
  funext physicalBit
  have wordWidth_eq : siteWordWidth parameters =
      (parametersToCircuit parameters).wordWidth := by rfl
  have cardEq :
      (configurationEquiv parameters configuration).1.card =
        configuration.1.card := by
    simp [configurationEquiv]
  change configurationEncoding parameters configuration
      (Fin.cast (width_eq_general parameters).symm physicalBit) = _
  by_cases before : physicalBit.val <
      siteWordWidth parameters * configuration.1.card
  · have beforeCircuit : physicalBit.val <
        (parametersToCircuit parameters).wordWidth *
          (configurationEquiv parameters configuration).1.card := by
      rw [cardEq, ← wordWidth_eq]
      exact before
    have beforeMath :
        (Fin.cast (width_eq_general parameters).symm physicalBit).val <
          siteWordWidth parameters * configuration.1.card := by
      change physicalBit.val < _
      exact before
    rw [configurationEncoding, delimiterEncoding,
      dif_pos beforeMath, dif_pos beforeCircuit]
    let mathSlot : Fin configuration.1.card :=
      ⟨physicalBit.val / siteWordWidth parameters,
        (Nat.div_lt_iff_lt_mul (by
          simp [siteWordWidth, parameters.q_pos])).2
          (by simpa [Nat.mul_comm] using before)⟩
    let mathWordBit : Fin (siteWordWidth parameters) :=
      ⟨physicalBit.val % siteWordWidth parameters,
        Nat.mod_lt _ (by simp [siteWordWidth, parameters.q_pos])⟩
    change QLean.MathematicalSpecifications.Targets.siteBit parameters
        (CoalescingWalkModel.siteAt configuration mathSlot) mathWordBit =
      ProbabilityGeneratorQProof.siteBit (parametersToCircuit parameters)
        (ProbabilityGeneratorQProof.QConfiguration.siteAt
          (configurationEquiv parameters configuration)
          (Fin.cast (by simp [configurationEquiv]) mathSlot))
        (Fin.cast (by rfl) mathWordBit)
    rw [QLean.Correspondence.GeneralRepresentationTransport.siteAt_transport
      parameters configuration mathSlot]
    simp [QLean.MathematicalSpecifications.Targets.siteBit,
      QLean.MathematicalSpecifications.Targets.siteBitVector,
      ProbabilityGeneratorQProof.siteBit,
      ProbabilityGeneratorQProof.siteBitVector,
      ProbabilityGeneratorQProof.siteCodeEquiv,
      QLean.Correspondence.GeneralRepresentationTransport.siteEquiv]
    congr 1
  · have beforeCircuit : ¬ physicalBit.val <
        (parametersToCircuit parameters).wordWidth *
          (configurationEquiv parameters configuration).1.card := by
      rw [cardEq, ← wordWidth_eq]
      exact before
    have beforeMath :
        ¬ (Fin.cast (width_eq_general parameters).symm physicalBit).val <
          siteWordWidth parameters * configuration.1.card := by
      change ¬ physicalBit.val < _
      exact before
    rw [configurationEncoding, delimiterEncoding,
      dif_neg beforeMath, dif_neg beforeCircuit]
    change decide (physicalBit.val =
        siteWordWidth parameters * configuration.1.card) =
      decide (physicalBit.val =
        (parametersToCircuit parameters).wordWidth *
          (configurationEquiv parameters configuration).1.card)
    rw [wordWidth_eq, cardEq]

theorem legalDelimiter_transport_general
    (parameters : CoalescingWalkModel.Parameters)
    (bits : DelimiterWord parameters) :
    QLean.MathematicalSpecifications.Targets.IsLegalDelimiter parameters bits ↔
      ProbabilityGeneratorQProof.IsLegalDelimiter
        (delimiterWordEquiv parameters bits) := by
  constructor
  · rintro ⟨configuration, encoded⟩
    refine ⟨configurationEquiv parameters configuration, ?_⟩
    rw [← configurationEncoding_transport_general]
    exact congrArg (delimiterWordEquiv parameters) encoded
  · rintro ⟨configuration, encoded⟩
    refine ⟨(configurationEquiv parameters).symm configuration, ?_⟩
    apply (delimiterWordEquiv parameters).injective
    rw [configurationEncoding_transport_general]
    simpa using encoded

theorem decodeConfiguration_transport_general
    (parameters : CoalescingWalkModel.Parameters)
    (bits : DelimiterWord parameters) :
    decodeDelimiter (delimiterWordEquiv parameters bits) =
      Option.map (configurationEquiv parameters)
        (decodeConfiguration parameters bits) := by
  cases decoded : decodeConfiguration parameters bits with
  | none =>
      simp only [Option.map_none]
      apply decodeDelimiter_eq_none_iff.mpr
      exact fun circuitLegal =>
        (decodeConfiguration_eq_none_iff parameters).mp decoded
          ((legalDelimiter_transport_general parameters bits).mpr circuitLegal)
  | some configuration =>
      simp only [Option.map_some]
      apply decodeDelimiter_eq_some_iff.mpr
      rw [← configurationEncoding_transport_general]
      exact congrArg (delimiterWordEquiv parameters)
        ((decodeConfiguration_eq_some_iff parameters).mp decoded)

theorem embeddedGenerator_transport_general
    (parameters : CoalescingWalkModel.Parameters) :
    (fun output input =>
      embeddedProbabilityGenerator (parametersToCircuit parameters)
        (delimiterWordEquiv parameters output)
        (delimiterWordEquiv parameters input)) =
      generatorMatrix parameters := by
  funext output input
  simp only [embeddedProbabilityGenerator, generatorMatrix, Matrix.of_apply]
  rw [decodeConfiguration_transport_general,
    decodeConfiguration_transport_general]
  cases outputDecoded : decodeConfiguration parameters output with
  | none => simp
  | some outputConfiguration =>
      cases inputDecoded : decodeConfiguration parameters input with
      | none => simp
      | some inputConfiguration =>
          simp only [Option.map_some]
          exact_mod_cast
            QLean.Correspondence.GeneralRepresentationTransport.generator_transport
              parameters
            outputConfiguration inputConfiguration

end General

private theorem successBlock_eq_inv_smul_of_zero_error
    {ancillaQubits systemQubits : Nat}
    (success : RegisterBasis ancillaQubits)
    (operator : Matrix (JointBasis ancillaQubits systemQubits)
      (JointBasis ancillaQubits systemQubits) ℂ)
    (target : Matrix (RegisterBasis systemQubits)
      (RegisterBasis systemQubits) ℂ)
    (alpha : ℝ)
    (certified : IsApproxQubitBlockEncoding success operator target alpha 0) :
    qubitSuccessBlock success operator = ((alpha : ℂ))⁻¹ • target := by
  have alphaNonzero : (alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt certified.2.1)
  have differenceNormZero :
      ‖target - (alpha : ℂ) • qubitSuccessBlock success operator‖ = 0 :=
    le_antisymm certified.2.2.2 (norm_nonneg _)
  have targetEq : target =
      (alpha : ℂ) • qubitSuccessBlock success operator :=
    sub_eq_zero.mp (norm_eq_zero.mp differenceNormZero)
  rw [targetEq, smul_smul, inv_mul_cancel₀ alphaNonzero, one_smul]

/-- CP01, parameter-general: the actual primitive generator circuit implements
the independently defined matrix on the entire delimiter-word space.  Thus
rows and columns containing invalid delimiter words are included, not omitted
by restricting the theorem to legal configurations. -/
theorem generatorCircuit_correct
    (parameters : CoalescingWalkModel.Parameters) :
    (fun output input =>
      qubitSuccessBlock
        (allZeroAncilla
          (General.parametersToCircuit parameters).ancillaWidth)
        ((cp01GeneratorCircuit (General.parametersToCircuit parameters)).toIdealOperator
          primitiveGateOperator)
        (General.delimiterWordEquiv parameters output)
        (General.delimiterWordEquiv parameters input)) =
      (((((3 : ℝ) * (parameters.K : ℝ)) : ℝ) : ℂ))⁻¹ •
        generatorMatrix parameters := by
  let circuitParameters := General.parametersToCircuit parameters
  have certified :=
    probabilityGeneratorScale3KErrorZeroBlockEncoding_correct circuitParameters
  unfold EmbeddedProbabilityGeneratorScale3KErrorZeroSpec at certified
  have exactBlock := successBlock_eq_inv_smul_of_zero_error
    (allZeroAncilla circuitParameters.ancillaWidth)
    ((uqCircuit circuitParameters).toIdealOperator primitiveGateOperator)
    (embeddedProbabilityGenerator circuitParameters)
    (3 * circuitParameters.K) certified
  funext output input
  have entry := congrFun
    (congrFun exactBlock (General.delimiterWordEquiv parameters output))
    (General.delimiterWordEquiv parameters input)
  have targetEntry := congrFun
    (congrFun (General.embeddedGenerator_transport_general parameters) output)
    input
  change _ =
    (((((3 : ℝ) * (circuitParameters.K : ℝ)) : ℝ) : ℂ))⁻¹ *
      embeddedProbabilityGenerator circuitParameters
        (General.delimiterWordEquiv parameters output)
        (General.delimiterWordEquiv parameters input) at entry
  change _ =
    (((((3 : ℝ) * (parameters.K : ℝ)) : ℝ) : ℂ))⁻¹ *
      generatorMatrix parameters output input
  rw [targetEntry] at entry
  simpa [cp01GeneratorCircuit, circuitParameters,
    General.parametersToCircuit] using entry

end

end QLean.Proofs.CheckpointCorrespondence
