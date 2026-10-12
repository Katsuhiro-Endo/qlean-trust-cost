import QLean.History.Integration.HistoryAssemblyExistenceAdapter
import QLean.History.Integration.IndexedHistoryProvider.HistoryProviderIndexedChildEstablishedBridge
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
import QLean.History.Integration.HistoryIndexCast.HistoryP15P16FinCastSemanticBridgeEstablishedBridge
import QLean.Generator.Implementation.UQCircuit
import QLean.Generator.Implementation.CoreCircuitEmbedding
import QLean.Generator.Implementation.PrimitiveCoreSemanticsAdapter
import QLean.Generator.Implementation.UniformPreparationFullOperatorCorrectness

set_option linter.defProp false

set_option warningAsError true
set_option autoImplicit false

namespace HistoryAssemblyComponentIntegration

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ProbabilityGeneratorQProof

noncomputable section

abbrev RawInput145 := HistoryAssemblyExistenceAdapter.RawInput145

/-! Public component bindings are built from accepted actual constructors.
    The result type carries the independent target and the exact source order;
    callers cannot inject a parent, target, operator, circuit, or certificate. -/

abbrev CorrectedAdmissible145 (input : RawInput145) :=
  HistoryAssemblyExistenceAdapter.CorrectedAdmissible145 input

noncomputable def p16ConcreteEvidence145
    (input : RawInput145)
    (admissible : CorrectedAdmissible145 input) :
    HistoryClockConcreteSourceOrderEvidence
      (ScientificWidthGenericContract.correctedLayout259 input admissible) :=
  HistoryIndexCast.history_clock_concrete_source_order_evidence207
    input.history admissible.analytic

end

end HistoryAssemblyComponentIntegration
