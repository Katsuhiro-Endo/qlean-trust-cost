import QLean.Circuits.Foundation.ControlledCircuitCompilerAnalytic
import QLean.Circuits.Foundation.ControlledHadamard
import QLean.Circuits.Foundation.ControlledRotationMacros

/-!
# Source-faithful P44 controlled-subcircuit semantics

The frozen `emit_controlled_subcircuit` boundary is not one controlled-Rz
leaf.  It lowers a supported primitive source stream in source order.  Direct
X/Z/CNOT lowering is internal to P44, while the source inventory attributes
the multi-control and controlled-rotation lowering families to P43 and P50.
-/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

/-- Independent coherent clean-work P44 target in source execution order. -/
noncomputable def r12ControlledSubcircuitCleanOperator
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    Operator (QubitBasis targetQubits) :=
  ExternallyControlledPrimitivePlan.semanticPlanOperator
    symbolValue layout plan

/-- The unplaced source operator retained by the P44 child contract. -/
noncomputable def r12ControlledSubcircuitSourceOperator {sourceQubits : Nat}
    (symbolValue : String → ℝ)
    (plan : List (ExternallyControlledPrimitivePlan sourceQubits)) :
    Operator (QubitBasis sourceQubits) :=
  ExternallyControlledPrimitivePlan.sourcePlanOperator symbolValue plan

end SpectralSamplingProof.Analytic

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

section NormalizedMacro


end NormalizedMacro

end SpectralSamplingProof.Analytic

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

section NormalizedMacroEstablishedBridge

end NormalizedMacroEstablishedBridge

end SpectralSamplingProof.Analytic
