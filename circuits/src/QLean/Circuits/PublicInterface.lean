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
import QLean.History.Implementation.HistoryPipelineP05Final
import QLean.SignalProcessing.M13bApprovedOddQSPBridge

/-!
# Public circuit input and register types

This module is the single naming boundary between the eight reviewed public
circuits and the historical implementation modules.  It contains circuit-side
data only and imports neither the independent mathematical specifications nor
the correspondence project.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.CheckpointCircuits

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof.Analytic
open M13bPrimitiveCandidate
open NativeConcreteP18QSPWitness
open ExecutableHistoryExecutableP18

noncomputable section

/-- Parameters consumed by the public probability-generator circuit. -/
abbrev GeneratorParameters := ProbabilityGeneratorQProof.QParameters

/-- Fully generated executable input shared by the history and spectral stages. -/
abbrev ExecutableInput := M13bPrimitiveCandidate.ExecutableInput119

/-- Number of qubits in the canonical shared-core generator circuit. -/
abbrev generatorQubits (parameters : GeneratorParameters) : Nat :=
  parameters.ancillaWidth + parameters.systemWidth

/-- Number of qubits in the public history block circuit. -/
abbrev historyQubits (input : ExecutableInput) : Nat :=
  (ExecutableHistoryExecutableHistory.ExecutableRaw119 input.source).history.qubits

/-- Number of qubits in the QSVT kernel-reflection and successful-history circuit. -/
abbrev kernelReflectionQubits (input : ExecutableInput) : Nat :=
  widenedP18Qubits119 input.source input.domain input.fits input.assumptions
      input.circuitSource + 3

end

end QLean.Circuits.CheckpointCircuits
