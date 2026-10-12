import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.Circuits.Foundation.ClassicalArithmeticCorrectnessAnalytic

/-!
# Coherent clean boundaries for minimum-work Boolean controls

These components expose the mathematical basis action implemented by the
source-faithful minimum-work compiler.  The dirty circuit remains an ordinary
primitive-gate Exact component; only its clean-work basis span is refined to
the direct Boolean XOR action.
-/

namespace VerifiedCircuitCore

noncomputable section

namespace ClassicalReversibleStage

/-- Clean-work predicate shared by the equality and conjunction compilers. -/
def minimumWorkCleanPredicate {qubits : Nat}
    (scratches : List (Fin qubits)) (input : QubitBasis qubits) : Prop :=
  ∀ wire, wire ∈ scratches → input wire = false

/-- Direct mathematical action of equality with a fixed little-endian
constant.  No compiler scratch appears in this definition. -/
def equalityToConstantDirectBasisAction {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat) (target : Fin qubits)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire target (littleEndianRegisterEqualsNat register constant input) input

@[simp] theorem equalityToConstantDirectBasisAction_apply_target
    {qubits : Nat} (register : List (Fin qubits)) (constant : Nat)
    (target : Fin qubits) (input : QubitBasis qubits) :
    equalityToConstantDirectBasisAction register constant target input target =
      (input target != littleEndianRegisterEqualsNat register constant input) :=
  xorWire_apply_same target _ input

theorem equalityToConstantDirectBasisAction_apply_other
    {qubits : Nat} (register : List (Fin qubits)) (constant : Nat)
    (target wire : Fin qubits) (different : wire ≠ target)
    (input : QubitBasis qubits) :
    equalityToConstantDirectBasisAction register constant target input wire =
      input wire :=
  xorWire_apply_other target wire different _ input

/-- Linear extension of `equalityToConstantDirectBasisAction`. -/
def equalityToConstantDirectOperator {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat) (target : Fin qubits) :
    Operator (QubitBasis qubits) :=
  deterministicOperator
    (equalityToConstantDirectBasisAction register constant target)

/-- Direct mathematical conjunction action.  The compiler AND chain is not
part of this specification. -/
def conjunctionDirectBasisAction {qubits : Nat}
    (controls : List (Fin qubits)) (target : Fin qubits)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire target (allWiresTrue controls input) input

@[simp] theorem conjunctionDirectBasisAction_apply_target
    {qubits : Nat} (controls : List (Fin qubits)) (target : Fin qubits)
    (input : QubitBasis qubits) :
    conjunctionDirectBasisAction controls target input target =
      (input target != allWiresTrue controls input) :=
  xorWire_apply_same target _ input

theorem conjunctionDirectBasisAction_apply_other
    {qubits : Nat} (controls : List (Fin qubits))
    (target wire : Fin qubits) (different : wire ≠ target)
    (input : QubitBasis qubits) :
    conjunctionDirectBasisAction controls target input wire = input wire :=
  xorWire_apply_other target wire different _ input

/-- Linear extension of `conjunctionDirectBasisAction`. -/
def conjunctionDirectOperator {qubits : Nat}
    (controls : List (Fin qubits)) (target : Fin qubits) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (conjunctionDirectBasisAction controls target)

/-- The direct equality action preserves every clean scratch wire. -/
theorem equalityToConstantDirectBasisAction_clean
    {qubits : Nat} (register scratches : List (Fin qubits))
    (constant : Nat) (target : Fin qubits) (input : QubitBasis qubits)
    (layoutNodup : (register ++ scratches ++ [target]).Nodup)
    (clean : minimumWorkCleanPredicate scratches input) :
    minimumWorkCleanPredicate scratches
      (equalityToConstantDirectBasisAction register constant target input) := by
  intro wire member
  unfold equalityToConstantDirectBasisAction
  have targetDifferent : target ≠ wire := by
    have split := List.nodup_append.mp layoutNodup
    exact (split.2.2 wire (by simp [member]) target (by simp)).symm
  rw [xorWire_apply_other target wire targetDifferent.symm]
  exact clean wire member

/-- Coherent B1 component: the compiled minimum-work equality stage has the
direct equality action on clean scratch and restores that scratch. -/
def xorEqualityToConstantMinimumWorkCleanSubspaceMapComponent
    {qubits : Nat} (symbolValue : String → ℝ)
    (register scratches : List (Fin qubits)) (constant : Nat)
    (target : Fin qubits)
    (enoughScratch : register.length ≤ scratches.length + 2)
    (layoutNodup : (register ++ scratches ++ [target]).Nodup) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  let exact :=
    primitiveExactOperatorComponent symbolValue
      (xorEqualityToConstantIntoTargetMinimumWork
        register scratches constant target)
  SubspaceMapComponent.ofBasisSpan
    (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) exact.circuit
    (equalityToConstantDirectOperator register constant target)
    (minimumWorkCleanPredicate scratches) (minimumWorkCleanPredicate scratches)
    (by
      intro input clean
      calc
        applyOperator
            (exact.circuit.denote
              (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue))
            (basisKet input) =
            applyOperator exact.target (basisKet input) :=
          congrArg (fun operator => applyOperator operator (basisKet input))
            exact.correct
        _ = applyOperator
            (equalityToConstantDirectOperator register constant target)
            (basisKet input) := by
          rw [primitiveExactOperatorComponent_target,
            analyticOperator_eq_deterministicReference,
            equalityToConstantDirectOperator,
            applyOperator_deterministicOperator_basisKet,
            applyOperator_deterministicOperator_basisKet]
          apply congrArg basisKet
          exact xorEqualityToConstantIntoTargetMinimumWork_reference_apply_of_cleanWork
            register scratches constant target input enoughScratch layoutNodup clean)
    (by
      intro input clean
      rw [equalityToConstantDirectOperator,
        applyOperator_deterministicOperator_basisKet]
      exact SubspaceMapComponent.basisKet_mem_basisSpan
        (equalityToConstantDirectBasisAction_clean register scratches constant
          target input layoutNodup clean))

/-- Asymmetric coherent form of the B1 clean boundary.  Applications may
name human-readable phase predicates while reusing the same direct action. -/
def xorEqualityToConstantMinimumWorkCleanSubspaceMapComponentBetween
    {qubits : Nat} (symbolValue : String → ℝ)
    (register scratches : List (Fin qubits)) (constant : Nat)
    (target : Fin qubits)
    (enoughScratch : register.length ≤ scratches.length + 2)
    (layoutNodup : (register ++ scratches ++ [target]).Nodup)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (inputClean : ∀ input, inputPredicate input →
      minimumWorkCleanPredicate scratches input)
    (directMaps : ∀ input, inputPredicate input →
      outputPredicate
        (equalityToConstantDirectBasisAction register constant target input)) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  let exact :=
    primitiveExactOperatorComponent symbolValue
      (xorEqualityToConstantIntoTargetMinimumWork
        register scratches constant target)
  SubspaceMapComponent.ofBasisSpan
    (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) exact.circuit
    (equalityToConstantDirectOperator register constant target)
    inputPredicate outputPredicate
    (by
      intro input inside
      calc
        applyOperator
            (exact.circuit.denote
              (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue))
            (basisKet input) =
            applyOperator exact.target (basisKet input) :=
          congrArg (fun operator => applyOperator operator (basisKet input))
            exact.correct
        _ = applyOperator
            (equalityToConstantDirectOperator register constant target)
            (basisKet input) := by
          rw [primitiveExactOperatorComponent_target,
            analyticOperator_eq_deterministicReference,
            equalityToConstantDirectOperator,
            applyOperator_deterministicOperator_basisKet,
            applyOperator_deterministicOperator_basisKet]
          apply congrArg basisKet
          exact xorEqualityToConstantIntoTargetMinimumWork_reference_apply_of_cleanWork
            register scratches constant target input enoughScratch layoutNodup
            (inputClean input inside))
    (by
      intro input inside
      rw [equalityToConstantDirectOperator,
        applyOperator_deterministicOperator_basisKet]
      exact SubspaceMapComponent.basisKet_mem_basisSpan
        (directMaps input inside))

/-- The direct conjunction action preserves every clean scratch wire. -/
theorem conjunctionDirectBasisAction_clean
    {qubits : Nat} (controls scratches : List (Fin qubits))
    (target : Fin qubits) (input : QubitBasis qubits)
    (layoutNodup : (controls ++ scratches ++ [target]).Nodup)
    (clean : minimumWorkCleanPredicate scratches input) :
    minimumWorkCleanPredicate scratches
      (conjunctionDirectBasisAction controls target input) := by
  intro wire member
  unfold conjunctionDirectBasisAction
  have targetDifferent : target ≠ wire := by
    have split := List.nodup_append.mp layoutNodup
    exact (split.2.2 wire (by simp [member]) target (by simp)).symm
  rw [xorWire_apply_other target wire targetDifferent.symm]
  exact clean wire member

/-- Coherent B4 component: the compiled minimum-work conjunction stage has
the direct conjunction action on clean scratch and restores that scratch. -/
def xorConjunctionMinimumWorkCleanSubspaceMapComponent
    {qubits : Nat} (symbolValue : String → ℝ)
    (controls scratches : List (Fin qubits)) (target : Fin qubits)
    (enoughScratch : controls.length ≤ scratches.length + 2)
    (layoutNodup : (controls ++ scratches ++ [target]).Nodup) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  let exact :=
    primitiveExactOperatorComponent symbolValue
      (xorConjunctionIntoTargetMinimumWork controls scratches target)
  SubspaceMapComponent.ofBasisSpan
    (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) exact.circuit
    (conjunctionDirectOperator controls target)
    (minimumWorkCleanPredicate scratches) (minimumWorkCleanPredicate scratches)
    (by
      intro input clean
      calc
        applyOperator
            (exact.circuit.denote
              (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue))
            (basisKet input) =
            applyOperator exact.target (basisKet input) :=
          congrArg (fun operator => applyOperator operator (basisKet input))
            exact.correct
        _ = applyOperator (conjunctionDirectOperator controls target)
            (basisKet input) := by
          rw [primitiveExactOperatorComponent_target,
            analyticOperator_eq_deterministicReference,
            conjunctionDirectOperator,
            applyOperator_deterministicOperator_basisKet,
            applyOperator_deterministicOperator_basisKet]
          apply congrArg basisKet
          simpa [xorConjunctionIntoTargetMinimumWork,
            conjunctionDirectBasisAction] using
            (minimumWorkPositiveMultiControlledX_reference_apply_of_cleanWork
              controls scratches target input enoughScratch layoutNodup clean))
    (by
      intro input clean
      rw [conjunctionDirectOperator,
        applyOperator_deterministicOperator_basisKet]
      exact SubspaceMapComponent.basisKet_mem_basisSpan
        (conjunctionDirectBasisAction_clean controls scratches target input
          layoutNodup clean))

/-- Asymmetric coherent form of the B4 clean boundary. -/
def xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    {qubits : Nat} (symbolValue : String → ℝ)
    (controls scratches : List (Fin qubits)) (target : Fin qubits)
    (enoughScratch : controls.length ≤ scratches.length + 2)
    (layoutNodup : (controls ++ scratches ++ [target]).Nodup)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (inputClean : ∀ input, inputPredicate input →
      minimumWorkCleanPredicate scratches input)
    (directMaps : ∀ input, inputPredicate input →
      outputPredicate (conjunctionDirectBasisAction controls target input)) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) :=
  let exact :=
    primitiveExactOperatorComponent symbolValue
      (xorConjunctionIntoTargetMinimumWork controls scratches target)
  SubspaceMapComponent.ofBasisSpan
    (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue) exact.circuit
    (conjunctionDirectOperator controls target)
    inputPredicate outputPredicate
    (by
      intro input inside
      calc
        applyOperator
            (exact.circuit.denote
              (primitiveGateOperatorWithSymbols (qubits := qubits) symbolValue))
            (basisKet input) =
            applyOperator exact.target (basisKet input) :=
          congrArg (fun operator => applyOperator operator (basisKet input))
            exact.correct
        _ = applyOperator (conjunctionDirectOperator controls target)
            (basisKet input) := by
          rw [primitiveExactOperatorComponent_target,
            analyticOperator_eq_deterministicReference,
            conjunctionDirectOperator,
            applyOperator_deterministicOperator_basisKet,
            applyOperator_deterministicOperator_basisKet]
          apply congrArg basisKet
          simpa [xorConjunctionIntoTargetMinimumWork,
            conjunctionDirectBasisAction] using
            (minimumWorkPositiveMultiControlledX_reference_apply_of_cleanWork
              controls scratches target input enoughScratch layoutNodup
              (inputClean input inside)))
    (by
      intro input inside
      rw [conjunctionDirectOperator,
        applyOperator_deterministicOperator_basisKet]
      exact SubspaceMapComponent.basisKet_mem_basisSpan
        (directMaps input inside))

end ClassicalReversibleStage

end

end VerifiedCircuitCore
