import QLean.Spectral.Analysis.HistoryUnderstandingSpecifications

/-!
# Corrected clean H3/H4 specifications

This leaf records the corrected seven-stage H3 word independently of the
historical H3 source record.  In particular, the projector-control stage is
one I06 occurrence and the selector-equality stage occurs again only as the
final branch uncompute.
-/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-- Pure corrected-H3 data.  The source word is fixed below as
`I01; I02; I03; I04; I06; I07; I01`; the final I01 is deliberately the same
selector-equality operator as the first one. -/
structure H3CorrectedCleanSpecification (qubits : Nat) where
  i01SelectorEquality : Operator (QubitBasis qubits)
  i02OrderUniformPreparationInverse : Operator (QubitBasis qubits)
  i03IdleTransform : Operator (QubitBasis qubits)
  i04CoefficientRotation : Operator (QubitBasis qubits)
  i06ProjectorControl : Operator (QubitBasis qubits)
  i07ControlledClockIncrement : Operator (QubitBasis qubits)
  cleanPredicate : QubitBasis qubits -> Prop

/-- The corrected H4 clean specification keeps the established human-facing
H1 and H2 definitions, but replaces the historical H3 child by the literal
corrected seven-stage H3 specification above. -/
structure H4CorrectedCleanSpecification (qubits : Nat) where
  selector : H1SelectorUnderstandingSpecification qubits
  taylor : H2TaylorUnderstandingSpecification qubits
  correctedClock : H3CorrectedCleanSpecification qubits

/-- The strengthened H4 input boundary adds H2's Q10 block-encoding input
condition but leaves the corrected H3 condition unchanged. -/
def h4CorrectedIdealInputPredicate {qubits : Nat}
    (spec : H4CorrectedCleanSpecification qubits)
    (basis : QubitBasis qubits) : Prop :=
  h2TaylorIdealInputPredicate spec.taylor basis /\
    spec.correctedClock.cleanPredicate basis

end

end SpectralSamplingProof.Analytic
