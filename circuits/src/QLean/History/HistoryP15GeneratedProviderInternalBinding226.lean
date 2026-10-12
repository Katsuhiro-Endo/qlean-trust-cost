import QLean.History.Integration.HistoryRawSchema.HistoryP15P16EvidenceDerivation
import QLean.History.HistoryInternalP17P44Certificate
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

set_option autoImplicit false

namespace ExecutableHistoryData

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ProbabilityGeneratorQProof

local notation "Circuit" => VerifiedCircuitCore.Circuit
local notation "PrimitiveGate" => VerifiedCircuitCore.PrimitiveGate
local notation "AngleExpr" => VerifiedCircuitCore.AngleExpr

/-!
  The executable boundary is intentionally independent of the accepted
  propositions.  The only input to the decoder is the raw P15 packet and a
  raw P17/P44 packet.  The finite predicate below contains only data which
  Lean can decide over Nat, Fin, List, Bool, and the finite angle syntax.
  No real inequality, circuit, target, correctness, or occurrence field is
  present in this predicate.
-/

structure RawP15ExecutableData225 where
  history : HistoryRawSchema.HistoryP15P16Raw203
  generator : GeneratorRawSchema.RawP17P44Data206
  sharedQ : Nat
  sharedK : Nat

def actualIncrement225 {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    Circuit (PrimitiveGate qubits) :=
  (controlledAddConstantMod2PowStage spec).compile

def actualRotation225 {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) : Circuit (PrimitiveGate qubits) :=
  Circuit.controlledRyMacroExpansion control target different angle

def actualX225 {qubits : Nat} (target : Fin qubits) :
    Circuit (PrimitiveGate qubits) := .gate (.x target)

def actualCnot225 {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target) :
    Circuit (PrimitiveGate qubits) := .gate (.cnot control target different)

def actualToffoli225 {qubits : Nat}
    (control₀ control₁ target : Fin qubits)
    (controlsDifferent : control₀ ≠ control₁)
    (firstDifferent : control₀ ≠ target)
    (secondDifferent : control₁ ≠ target) :
    Circuit (PrimitiveGate qubits) :=
  .gate (.toffoli control₀ control₁ target controlsDifferent
    firstDifferent secondDifferent)

/-! The proof layer is deliberately separate.  It is the only layer allowed
    to mention accepted admissibility, equality, correctness, or occurrence
    cards.  The executable above has no argument of any of these types. -/

theorem actualIncrement225_eq_history226
    {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    actualIncrement225 spec =
      (controlledAddConstantMod2PowExactOperatorComponent
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment spec).circuit := by
  exact (controlledAddConstantMod2PowExactOperatorComponent_circuit _ _).symm

end ExecutableHistoryData
