import QLean.History.Implementation.HistoryPipelineFiniteScientificWidth
import QLean.History.ExtendedHistoryEnumeration
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
import QLean.Circuits.Foundation.FiniteGateExport
import QLean.Generator.Analysis.QConfigurationEnumeration

/-! Finite history-basis layout plan. -/

set_option autoImplicit false
set_option warningAsError true

namespace ScientificExtractionPhysicalSpecification

open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryImplementationRole
open ProbabilityGeneratorQProof
open VerifiedCircuitCore
open VerifiedCircuitCore.ControlledCircuitCompilerV2

open SpectralSamplingProof.Analytic

def finiteScientificHistorySourcePlan119
    (source : AlignedCommonSource119)
    (fits : HistoryIndexFitsLayout119 source)
    {targetQubits : Nat}
    (layout : ControlLayout (finiteScientificHistoryQubits119 source)
      targetQubits) :
    FiniteHistoryBasisPlan119
      (Fintype.card (QConfiguration source.qParameters))
      source.historyParameters.clockEnd
      source.historyParameters.binaryLabels
      (finiteScientificHistoryQubits119 source) targetQubits where
  layout := layout
  historyBasis := finiteScientificCanonicalHistoryBasis119 source fits
  inrBasis := fun _ => false

end ScientificExtractionPhysicalSpecification
