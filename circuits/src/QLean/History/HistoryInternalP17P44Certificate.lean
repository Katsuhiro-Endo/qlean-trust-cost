import QLean.Spectral.Analysis.R12OperatorDag
import QLean.Circuits.Foundation.Foundations
import QLean.Spectral.Circuits.HistoryBlock
import QLean.Spectral.Circuits.HistoryTaylorBlock
import QLean.Spectral.Circuits.HistoryTaylorQ10CleanLink
import QLean.Spectral.Analysis.HistoryClockCheckpointSpecifications
import QLean.Spectral.Circuits.HistoryClockClean
import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.Gates
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.QuantumFourier
import QLean.Circuits.Foundation.QuantumFourierAnalytic
import QLean.Circuits.Foundation.QubitBasisEncoding
import QLean.Circuits.Foundation.OperatorL2Error
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import QLean.Circuits.Foundation.ReversibleLogic
import QLean.Circuits.Foundation.ReversibleLogicCleanAnalytic
import QLean.Circuits.Foundation.UniformPreparationCorrectness
import QLean.Circuits.Foundation.ShuklaVedulaUniformCorrectness
import QLean.Circuits.Foundation.WireEmbedding
import QLean.Circuits.Foundation.BitonicNetworkAnalytic
import QLean.Circuits.Foundation.EqualityBranchLessThanAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.Circuits.Foundation.ControlledConstantAdder
import QLean.Circuits.Foundation.PrimitiveOperatorSemantics
import QLean.Circuits.Foundation.FinitePhaseTransformAnalytic
import QLean.Generator.Implementation.ProbabilityGeneratorCoreExactAdapter
import Mathlib
import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2
import QLean.Circuits.Foundation.PhaseShiftMacros
import QLean.Circuits.Foundation.ControlledHadamard
import QLean.Circuits.Foundation.Metrics
import QLean.Circuits.Foundation.WireEmbeddingAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkMultiControlledXCorrectnessAnalytic
import QLean.Spectral.Circuits.ControlledSubcircuit
import QLean.Generator.Implementation.OracleCanonicalFullStageCompiler
import QLean.Generator.Implementation.QVerifiedTopComponents
import QLean.Generator.Implementation.QVerifiedArithmeticComponents
import QLean.Circuits.Foundation.ControlledRotationMacros
import QLean.History.Integration.GeneratorActual.P17Actual
import QLean.History.Integration.IndexedHistoryProvider.HistoryProviderIndexedChildEstablishedBridge
import QLean.History.Integration.CanonicalHistoryAdapter.HistoryProofFreeCanonicalAdapter

set_option autoImplicit false

namespace GeneratorRawSchema

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ProbabilityGeneratorQProof

structure RawP17P44Data206 where
  q : Nat
  K : Nat
  targetQubits : Nat
  control : Nat
  placement : List Nat
  controlWork : List Nat
  selectorAngles : List ScientificAngleExpr
  coefficientAngles : List ScientificAngleExpr
  idleCoefficientAngle : ScientificAngleExpr

def canonicalLayout206 {sourceQubits : Nat} :
    ExternallyControlledCircuitLayout sourceQubits (sourceQubits + 1) :=
  { placement :=
      { toFun := fun index => Fin.castLE (Nat.le_succ sourceQubits) index
        inj' := by
          intro left right equality
          apply Fin.ext
          simpa using congrArg
            (fun x : Fin (sourceQubits + 1) => x.val) equality }
    control := ⟨sourceQubits, Nat.lt_succ_self sourceQubits⟩
    control_ne_placed := by
      intro source equality
      have values := congrArg Fin.val equality
      simp at values
      omega
    controlWork := [] }

def p17Circuit206 (parameters : QParameters) :
    VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate
        (parameters.ancillaWidth + parameters.systemWidth)) :=
  (ProbabilityGeneratorQProof.uqCircuit parameters).mapGates
    ProbabilityGeneratorQProof.PrimitiveGate.toCanonicalCore

theorem p17Circuit206_eq_accepted183 (parameters : QParameters) :
    p17Circuit206 parameters = (GeneratorActual.p17Actual parameters).circuit := by
  exact (GeneratorActual.p17Actual_source_order parameters).symm

theorem p17Circuit206_supported (parameters : QParameters) :
    ∀ gate, gate ∈ (p17Circuit206 parameters).flatten →
      IsExternallyControllablePrimitive gate := by
  intro gate member
  rw [p17Circuit206, Circuit.flatten_mapGates] at member
  rcases List.mem_map.mp member with ⟨raw, _, rfl⟩
  cases raw <;>
    simp [ProbabilityGeneratorQProof.PrimitiveGate.toCanonicalCore,
      IsExternallyControllablePrimitive]

structure HistoryP17P44Admissible206 (data : RawP17P44Data206) : Prop where
  q_positive : 0 < data.q
  K_positive : 0 < data.K
  target_layout : data.targetQubits =
    (QParameters.mk data.q data.K q_positive K_positive).ancillaWidth +
      (QParameters.mk data.q data.K q_positive K_positive).systemWidth + 1
  control_layout : data.control =
    (QParameters.mk data.q data.K q_positive K_positive).ancillaWidth +
      (QParameters.mk data.q data.K q_positive K_positive).systemWidth
  placement_layout : data.placement = List.range
    ((QParameters.mk data.q data.K q_positive K_positive).ancillaWidth +
      (QParameters.mk data.q data.K q_positive K_positive).systemWidth)
  control_work_empty : data.controlWork = []
  selector_length : data.selectorAngles.length = 3
  selector_core : ∀ angle, angle ∈ data.selectorAngles → CanonicalHistoryAdapter.ScientificAngleCore angle
  coefficient_core : ∀ angle, angle ∈ data.coefficientAngles → CanonicalHistoryAdapter.ScientificAngleCore angle
  idle_core : CanonicalHistoryAdapter.ScientificAngleCore data.idleCoefficientAngle

structure GeneratedP17P44Binding206 (data : RawP17P44Data206) where
  parameters : QParameters
  input : IndexedHistoryProvider.P17P44InputBinding188 parameters
    (canonicalLayout206 : ExternallyControlledCircuitLayout
      (parameters.ancillaWidth + parameters.systemWidth)
      (parameters.ancillaWidth + parameters.systemWidth + 1))

def generatedP17P44Binding206 (data : RawP17P44Data206)
    (admissible : HistoryP17P44Admissible206 data) :
    GeneratedP17P44Binding206 data := by
  let parameters : QParameters :=
    { q := data.q
      K := data.K
      q_pos := admissible.q_positive
      K_pos := admissible.K_positive }
  let certificate :
      ExternallyControlledPrimitiveCircuitCertificate
        (GeneratorActual.p17Actual parameters).circuit := by
    refine { leavesSupported := ?_ }
    intro gate member
    rw [← p17Circuit206_eq_accepted183 parameters] at member
    exact p17Circuit206_supported parameters gate member
  exact { parameters := parameters, input := ⟨certificate⟩ }

end GeneratorRawSchema
