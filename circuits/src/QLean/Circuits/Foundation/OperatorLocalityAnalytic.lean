import QLean.Circuits.Foundation.PrimitiveOperatorSemantics

/-!
# Basis-support locality for independent operators

This module records locality only through basis action and matrix support.  It
does not depend on a gate language, compiler, or execution semantics.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- An operator can change basis values only on a declared finite wire set. -/
def OperatorPreservesOutside {qubits : Nat}
    (support : Finset (Fin qubits))
    (operator : Operator (QubitBasis qubits)) : Prop :=
  ∀ output input, operator output input ≠ 0 →
    ∀ wire, wire ∉ support → output wire = input wire

namespace OperatorPreservesOutside

/-- A locality proof remains valid after enlarging its declared support. -/
theorem mono {qubits : Nat}
    {support larger : Finset (Fin qubits)}
    {operator : Operator (QubitBasis qubits)}
    (locality : OperatorPreservesOutside support operator)
    (subset : support ⊆ larger) :
    OperatorPreservesOutside larger operator := by
  intro output input nonzero wire outside
  apply locality output input nonzero wire
  intro member
  exact outside (subset member)

/-- The identity operator is local on every declared support. -/
theorem one {qubits : Nat} (support : Finset (Fin qubits)) :
    OperatorPreservesOutside support
      (1 : Operator (QubitBasis qubits)) := by
  intro output input nonzero wire _
  by_cases equal : output = input
  · exact congrFun equal wire
  · simp [equal] at nonzero

/-- A deterministic action local on a support has a local deterministic
operator. -/
theorem deterministicOperator {qubits : Nat}
    (support : Finset (Fin qubits))
    (action : QubitBasis qubits → QubitBasis qubits)
    (actionOutside : ∀ input wire, wire ∉ support →
      action input wire = input wire) :
    OperatorPreservesOutside support (deterministicOperator action) := by
  intro output input nonzero wire outside
  by_cases equal : output = action input
  · subst output
    exact actionOutside input wire outside
  · simp [VerifiedCircuitCore.deterministicOperator, equal] at nonzero

/-- A deterministic XOR update changes only its target wire, regardless of
how the Boolean update value is computed from the input basis. -/
theorem deterministicXorWire {qubits : Nat}
    (target : Fin qubits) (value : QubitBasis qubits → Bool) :
    OperatorPreservesOutside {target}
      (VerifiedCircuitCore.deterministicOperator fun input =>
        xorWire target (value input) input) := by
  apply deterministicOperator
  intro input wire outside
  apply xorWire_apply_other
  simpa using outside

/-- A predicate-controlled one-qubit specification has matrix support only on
its target wire.  Predicate independence is needed for unitarity, but not for
this support-locality statement: every nonzero matrix entry already satisfies
`agreesExcept target` by definition. -/
theorem predicateControlledSingleQubitOperator {qubits : Nat}
    (predicate : QubitBasis qubits → Bool) (target : Fin qubits)
    (localOperator : Matrix Bool Bool ℂ) :
    OperatorPreservesOutside {target}
      (VerifiedCircuitCore.predicateControlledSingleQubitOperator
        predicate target localOperator) := by
  intro output input nonzero wire outside
  rw [VerifiedCircuitCore.predicateControlledSingleQubitOperator_apply] at nonzero
  by_cases agrees : agreesExcept target output input
  · exact agrees wire (by simpa using outside)
  · simp [agrees] at nonzero

/-- Sequential operator multiplication is local on the union of the two
supports.  The proof ranges over an arbitrary intermediate finite basis. -/
theorem mul {qubits : Nat}
    {firstSupport secondSupport : Finset (Fin qubits)}
    {first second : Operator (QubitBasis qubits)}
    (firstLocal : OperatorPreservesOutside firstSupport first)
    (secondLocal : OperatorPreservesOutside secondSupport second) :
    OperatorPreservesOutside (firstSupport ∪ secondSupport) (second * first) := by
  intro output input productNonzero wire outside
  have outsideFirst : wire ∉ firstSupport := by
    intro member
    exact outside (Finset.mem_union_left _ member)
  have outsideSecond : wire ∉ secondSupport := by
    intro member
    exact outside (Finset.mem_union_right _ member)
  by_contra changed
  have everyTermZero : ∀ intermediate : QubitBasis qubits,
      second output intermediate * first intermediate input = 0 := by
    intro intermediate
    by_cases firstZero : first intermediate input = 0
    · simp [firstZero]
    by_cases secondZero : second output intermediate = 0
    · simp [secondZero]
    have intermediateInput :=
      firstLocal intermediate input firstZero wire outsideFirst
    have outputIntermediate :=
      secondLocal output intermediate secondZero wire outsideSecond
    exact False.elim (changed (outputIntermediate.trans intermediateInput))
  apply productNonzero
  change (∑ intermediate : QubitBasis qubits,
    second output intermediate * first intermediate input) = 0
  simp [everyTermZero]

/-- Taking the adjoint does not change the set of basis wires on which an
operator may change values. -/
theorem conjTranspose {qubits : Nat}
    {support : Finset (Fin qubits)}
    {operator : Operator (QubitBasis qubits)}
    (locality : OperatorPreservesOutside support operator) :
    OperatorPreservesOutside support (Matrix.conjTranspose operator) := by
  intro output input nonzero wire outside
  have reversedNonzero : operator input output ≠ 0 := by
    intro zero
    apply nonzero
    simp [Matrix.conjTranspose_apply, zero]
  exact (locality input output reversedNonzero wire outside).symm

/-- An execution-order operator sequence is local on a common support when
every member is local on that support. -/
theorem operatorSequence_of_forall {qubits : Nat}
    (support : Finset (Fin qubits))
    (operators : List (Operator (QubitBasis qubits)))
    (locality : ∀ operator, operator ∈ operators →
      OperatorPreservesOutside support operator) :
    OperatorPreservesOutside support (operatorSequence operators) := by
  induction operators with
  | nil => simpa [operatorSequence] using one support
  | cons first rest inductionHypothesis =>
      have firstLocal := locality first (by simp)
      have restLocal : OperatorPreservesOutside support
          (operatorSequence rest) := by
        apply inductionHypothesis
        intro operator member
        exact locality operator (by simp [member])
      simpa [operatorSequence] using firstLocal.mul restLocal

end OperatorPreservesOutside

/-- A basis assignment is zero on every wire in a protected set. -/
def QubitBasisZeroOn {qubits : Nat}
    (protectedWires : Finset (Fin qubits))
    (input : QubitBasis qubits) : Prop :=
  ∀ wire, wire ∈ protectedWires → input wire = false

end

end VerifiedCircuitCore
