import QLean.Spectral.Analysis.ControlledSubcircuit
import QLean.Circuits.Foundation.ControlledCircuitCompiler

/-!
# Proof-bearing P44 controlled-subcircuit adapters

These adapters retain the actual source Exact child and its supported-leaf
certificate while exposing the source-faithful strict and clean P44 layers.
The strict composition theorem below reconstructs the parent equality from
the three lowering-family contracts instead of reading the assembled
parent's stored proof field.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

/-- Full-dirty P44 Exact component for any certified source Exact child. -/
noncomputable def r12ControlledSubcircuitStrictExactComponent
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (child : ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := sourceQubits) symbolValue))
    (certificate : ExternallyControlledPrimitiveCircuitCertificate
      child.circuit) :
    ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := targetQubits) symbolValue) :=
  externallyControlledStrictExactOperatorComponentOfExact
    symbolValue layout child certificate

end SpectralSamplingProof.Components
