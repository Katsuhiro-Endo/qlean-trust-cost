import QLean.Circuits.Foundation.Gates
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.WireEmbedding
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2

/-!
# Cycle-free bridge for normalized primitive proof consumers

This module is intentionally a top-level leaf: it depends on the existing
primitive proof layer and the normalized V2 layer, while neither layer imports
this bridge.  It exposes only aliases and strict wrappers over existing
independent operator targets.
-/

namespace VerifiedCircuitCore

noncomputable section

namespace NormalizedPrimitiveProofBridge

theorem root_predicate_iff_v2 {qubits : Nat} (gate : PrimitiveGate qubits) :
    IsNormalizedPrimitive gate ↔
      ControlledCircuitCompilerV2.IsNormalizedPrimitive gate :=
  isNormalizedPrimitive_iff_controlledCircuitCompilerV2 gate

end NormalizedPrimitiveProofBridge

end

end VerifiedCircuitCore
