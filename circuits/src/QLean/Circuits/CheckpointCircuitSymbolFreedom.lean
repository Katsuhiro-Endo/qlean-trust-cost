import QLean.Circuits.CP03ProgramConversion
import Mathlib
import QLean.Circuits.Foundation.QubitBasisEncoding
import QLean.Circuits.Foundation.QuantumFourierAnalytic
import QLean.SignalProcessing.M13cSpecification
import QLean.SignalProcessing.M13bQSVTLogicalEmbedding
import QLean.Circuits.Foundation.ClassicalArithmeticCorrectnessAnalytic
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
import QLean.Circuits.CommonKernelReflectionCircuit
import QLean.Circuits.CheckpointCircuits
import QLean.Circuits.FiniteScientificCircuitSource
import QLean.Circuits.FiniteKernelCircuit
import QLean.Circuits.Foundation.FiniteGateExport
import QLean.Circuits.Foundation.Gates
import VerifiedMath.FiniteComplex
import QLean.History.Implementation.HistoryPipelineFiniteCorrectedP05Plan
import QLean.History.Implementation.HistoryPipelineFiniteCorrectedP05
import QLean.History.Implementation.HistoryPipelineSumComposition
import QLean.SignalProcessing.M13bFiniteOuterCompiler
import QLean.Circuits.QSPProgramSyntax
import QLean.Generator.Analysis.QGenerator
import QLean.History.FiniteScientificHistoryPlan
import QLean.Circuits.FiniteKernelResources

/-!
# Public-circuit symbol-freedom certificates

CP01 is symbol-free directly from its finite angle grammar.  The remaining
public circuits currently use a closure pass.  The two paths must not be
confused: closure proves environment independence of the result, but does
not by itself prove that an underlying builder had no unresolved symbols.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.CheckpointCircuitSymbolFreedom

open VerifiedCircuitCore
open QLean.Circuits.CheckpointCircuits

noncomputable section

theorem historyCircuit_isSymbolFree (input : ExecutableInput) :
    Circuit.IsSymbolFree (historyCircuit input) :=
  Circuit.specializeSymbols_isSymbolFree _ _

/-! Exact bridges from the public closed circuits to the legacy internal
builders.  These are semantic equalities, not aliases: correspondence proofs
can retain their established internal denotations while the public API has no
environment argument. -/

theorem generatorCircuit_denote_eq_internal (parameters : GeneratorParameters) :
    Circuit.denote primitiveGateOperator (generatorCircuit parameters) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        ((ProbabilityGeneratorQProof.uqCircuit parameters).mapGates
          ProbabilityGeneratorQProof.PrimitiveGate.toCanonicalCore) := by
  rfl

end

end QLean.Circuits.CheckpointCircuitSymbolFreedom
