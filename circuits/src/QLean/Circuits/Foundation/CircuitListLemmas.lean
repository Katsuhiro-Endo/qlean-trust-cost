import QLean.Circuits.Foundation.Gates

/-! List identities for circuit reversal, repetition, and gate counting. -/

set_option autoImplicit false
set_option warningAsError true

namespace VerifiedCircuitCore

private theorem listReplicateFlattenReverse {Gate : Type*}
    (items : List Gate) :
    ∀ count, (List.replicate count items.reverse).flatten =
      (List.replicate count items).flatten.reverse := by
  intro count
  simpa [List.reverse_replicate] using
    (List.flatten_reverse (L := List.replicate count items.reverse))

theorem Circuit.flatten_reverse {Gate : Type*}
    (inverseGate : Gate → Gate) :
    ∀ circuit : Circuit Gate,
      (circuit.reverse inverseGate).flatten =
        circuit.flatten.reverse.map inverseGate
  | .identity => by simp [Circuit.reverse, Circuit.flatten]
  | .gate value => by simp [Circuit.reverse, Circuit.flatten]
  | .seq first second => by
      simp [Circuit.reverse, Circuit.flatten,
        Circuit.flatten_reverse inverseGate first,
        Circuit.flatten_reverse inverseGate second,
        List.reverse_append, List.map_append]
  | .repeat count body => by
      simp only [Circuit.reverse, Circuit.flatten,
        Circuit.flatten_reverse inverseGate body]
      simpa [List.map_reverse, List.map_flatten] using
        (listReplicateFlattenReverse
          (body.flatten.map inverseGate) count)

@[simp] theorem Circuit.gateCount_reverse {Gate : Type*}
    (inverseGate : Gate → Gate) (circuit : Circuit Gate) :
    (circuit.reverse inverseGate).gateCount = circuit.gateCount := by
  simp [Circuit.gateCount, Circuit.flatten_reverse]

@[simp] theorem Circuit.gateCount_sequence {Gate : Type*}
    (circuits : List (Circuit Gate)) :
    (Circuit.sequence circuits).gateCount =
      (circuits.map Circuit.gateCount).sum := by
  induction circuits with
  | nil => simp [Circuit.gateCount, Circuit.sequence, Circuit.flatten]
  | cons first rest inductionHypothesis =>
      have restLength :
          (Circuit.sequence rest).flatten.length =
            (rest.map Circuit.gateCount).sum := by
        simpa [Circuit.gateCount] using inductionHypothesis
      simp [Circuit.gateCount, Circuit.sequence, Circuit.flatten,
        restLength]

end VerifiedCircuitCore
