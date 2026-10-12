import QLean.Circuits.Foundation.PrimitiveOperatorSemantics

/-!
# Pure finite-phase signal-transform semantics

This module specifies finite QSVT/Yoder--Low--Chuang/fixed-point amplitude
amplification sequences as explicit operator products.  It deliberately does
not claim a closed-form polynomial, an optimal phase schedule, or a standard
QFT-style kernel theorem.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Which public signal child is executed at a finite-phase signal step. -/
inductive SignalDirection where
  | forward
  | adjoint
deriving DecidableEq, Repr

end

end VerifiedCircuitCore
