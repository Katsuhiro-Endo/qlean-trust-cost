import QLean.History.Foundation.M09Bridge
import QLean.History.Foundation.HistorySpec
import QLean.History.Foundation.QModel
import QLean.Spectral.Analysis.HistoryBlock
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
import QLean.Generator.Analysis.LinearAlgebra
import QLean.History.Foundation.HistoryLCU
import Mathlib

open Matrix

namespace HistoryBlockEncoding
namespace Checkpoint2

noncomputable section

namespace RealHistory

def castMatrix
    {α β : Type*}
    (matrix : Matrix α β ℚ) : Matrix α β ℝ :=
  fun row column => matrix row column

end RealHistory

namespace M09

open ProbabilityGeneratorQProof
open ProbabilityGeneratorQProof.QParameters
open HistoryBlockEncoding.QModel
open VerifiedCircuitCore

end M09

namespace M10

end M10

end
end Checkpoint2
end HistoryBlockEncoding
