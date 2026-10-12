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

set_option autoImplicit false

namespace GeneratorActual

open VerifiedCircuitCore
open ProbabilityGeneratorQProof

noncomputable section

/- The actual P17 provider is the public Q-core exact component.  This
   module deliberately does not import the historical HistorySourceOrder umbrella or the
   broad P17 stage wrapper. -/
def p17Actual (p : QParameters) :
    VerifiedCircuitCore.ExactOperatorComponent
      (primitiveGateOperatorWithSymbols
        (qubits := p.ancillaWidth + p.systemWidth) internalZeroSymbolEnvironment) :=
  probabilityGeneratorCanonicalCoreExactOperatorComponent p

theorem p17Actual_source_order (p : QParameters) :
    (p17Actual p).circuit =
      (uqCircuit p).mapGates PrimitiveGate.toCanonicalCore := by
  rfl

end
end GeneratorActual
