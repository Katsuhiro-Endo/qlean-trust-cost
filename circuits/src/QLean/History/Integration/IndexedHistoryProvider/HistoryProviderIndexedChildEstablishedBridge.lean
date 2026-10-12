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
import QLean.Spectral.Analysis.ControlledSubcircuit

set_option autoImplicit false

namespace IndexedHistoryProvider

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ProbabilityGeneratorQProof

noncomputable section

/-! The P17 provider is fixed at the accepted public exact component.  There is
    no ID argument and no generic transport wrapper: the identity is the
    constructor result itself. -/

/-! The P17 input to P44 is a dependent binding.  Its certificate is indexed
    by the accepted P17 circuit; the P44 parent occurrence is deliberately a
    separate record below. -/
structure P17P44InputBinding188 {targetQubits : Nat}
    (p : QParameters)
    (layout : ExternallyControlledCircuitLayout
      (p.ancillaWidth + p.systemWidth) targetQubits) where
  certificate : ExternallyControlledPrimitiveCircuitCertificate
    (GeneratorActual.p17Actual p).circuit

/-! Parent occurrences are not inferred from the input edge.  They are two
    independent, witness-bearing occurrence records. -/

/-! P44 decoding: direct lowering is a leaf with no PComponentId.  Provider
    roles use the fixed P43/P50 constructors and are kept in a dependent
    sigma, so no ID-list is the identity source. -/

/-! A structural list-occurrence lemma used by both history parents. -/

/-! P15 uses the fixed auxiliary provider family and one central P44
    generator.  The central card and its source occurrence share one witness. -/

/-! P16 fixed source-order providers and cards.  The identifier list below is
    computed from these provider constructors; it is not an ID injection or a
    primary hand-written registry. -/

end
end IndexedHistoryProvider
