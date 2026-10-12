import QLean.Circuits.PublicInterface
import QLean.SignalProcessing.M13bFiniteOuterCompiler
import QLean.SignalProcessing.M13bConjugateControlledCompute
import QLean.SignalProcessing.M13bControlXStateSemantics
import QLean.SignalProcessing.M13bHadamardTrueStateSemantics
import QLean.SignalProcessing.M13bHermitianSuccessReflection
import QLean.Circuits.Foundation.Foundations
import Mathlib
import QLean.Circuits.Foundation.QubitBasisEncoding
import QLean.Circuits.Foundation.QuantumFourierAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic
import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.WireEmbeddingAnalytic
import QLean.Circuits.Foundation.ReversibleLogicCleanAnalytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkMultiControlledXCorrectnessAnalytic
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2
import QLean.Circuits.Foundation.PhaseShiftMacros
import QLean.Circuits.Foundation.QuantumFourier
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.OperatorL2Error
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import QLean.Circuits.Foundation.Metrics
import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.Circuits.Foundation.ReversibleLogic
import QLean.Circuits.Foundation.WireEmbedding
import QLean.Circuits.Foundation.FiniteGateExport
import QLean.SignalProcessing.M13cSpecification
import QLean.SignalProcessing.M13bQSVTLogicalEmbedding
import QLean.Circuits.Foundation.ClassicalArithmeticCorrectnessAnalytic
import QLean.History.Jennings.PureSpec
import QLean.SignalProcessing.PhaseScheduleProofsPhaseWordContract
import QLean.SignalProcessing.PhaseScheduleProofsChebyshevContract
import QLean.Circuits.Foundation.Combinators
import QLean.History.HistoryEmbeddingNorm
import QLean.History.Jennings.ProofEstablishedBridge
import QLean.Circuits.Foundation.FinitePhaseTransformAnalytic
import QLean.Circuits.Foundation.CircuitListLemmas
import QLean.Circuits.Foundation.WireEmbeddingL2Analytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkClean
import QLean.Circuits.Foundation.ControlledConstantAdderAnalytic
import QLean.History.ExtendedHistoryEnumeration
import QLean.Generator.Analysis.QConfigurationEnumeration
import QLean.SignalProcessing.NativeFiniteSignalEmbedding

/-!
# Internal implementations for the eight public circuit values

This module retains historical implementation names for compatibility.  The
human-facing eight definitions live in `CheckpointCircuits.lean` and reach
this module through one layer of meaningfully named builders.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
set_option warningAsError true

namespace QLean.Circuits.CheckpointCircuits

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof.Analytic
open M13bPrimitiveCandidate
open NativeConcreteP18QSPWitness
open ScientificExtractionPhysicalSpecification

noncomputable section

/-- CP01 implementation: the emitted probability-generator circuit. -/
def cp01GeneratorCircuit (parameters : QParameters) :=
  uqCircuit parameters

/-- CP02 implementation: the emitted corrected history block circuit. -/
def cp02HistoryCircuit (input : ExecutableInput119) :=
  (ExecutableHistoryExecutableHistory.correctedP05Component119
    input.source input.domain).circuit

/-! ## Single public-to-internal mapping boundary -/

/-- Internal builder for the public history circuit. -/
def buildHistoryCircuit (input : ExecutableInput) :
    VerifiedCircuitCore.Circuit
      (VerifiedCircuitCore.PrimitiveGate (historyQubits input)) :=
  cp02HistoryCircuit input

end

end QLean.Circuits.CheckpointCircuits
