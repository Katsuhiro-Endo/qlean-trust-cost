import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic
import QLean.Circuits.Foundation.QubitBasisEncoding

/-!
# Source-order controlled constant addition: analytic specification

This module defines a layout-independent masked-constant Cuccaro family.  Its
full-dirty target is the exact reversible basis action of the recorded gate
plan.  A separate direct action records the clean-register modular-addition
meaning.
-/

namespace VerifiedCircuitCore

noncomputable section

/-- Write a complete bit vector into a register while leaving all outside
wires unchanged. -/
def writeRegisterBits {qubits width : Nat}
    (register : Register qubits width) (bits : QubitBasis width)
    (input : QubitBasis qubits) : QubitBasis qubits := fun wire =>
  if found : ∃ index, register.wire index = wire then
    bits (Classical.choose found)
  else input wire

/-- Write the low `width` bits of a natural number into a register while
leaving all outside wires unchanged. -/
def writeRegisterValue {qubits width : Nat}
    (register : Register qubits width) (value : Nat)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  writeRegisterBits register (fun index => value.testBit index.val) input

/-- Reading a wire written by `writeRegisterBits` returns its selected bit. -/
@[simp] theorem writeRegisterBits_apply_wire {qubits width : Nat}
    (register : Register qubits width) (bits : QubitBasis width)
    (input : QubitBasis qubits) (index : Fin width) :
    writeRegisterBits register bits input (register.wire index) = bits index := by
  rw [writeRegisterBits, dif_pos ⟨index, rfl⟩]
  have chosen := Classical.choose_spec
    (show ∃ candidate, register.wire candidate = register.wire index from
      ⟨index, rfl⟩)
  have equal : Classical.choose
      (show ∃ candidate, register.wire candidate = register.wire index from
        ⟨index, rfl⟩) = index := register.injective chosen
  rw [equal]

/-- A bit-vector register write preserves every outside wire. -/
theorem writeRegisterBits_apply_outside {qubits width : Nat}
    (register : Register qubits width) (bits : QubitBasis width)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : ∀ index, register.wire index ≠ wire) :
    writeRegisterBits register bits input wire = input wire := by
  rw [writeRegisterBits, dif_neg]
  intro found
  rcases found with ⟨index, equal⟩
  exact outside index equal

/-- Writing a one-bit register is one functional update. -/
theorem writeRegisterBits_widthOne {qubits : Nat}
    (register : Register qubits 1) (bits : QubitBasis 1)
    (input : QubitBasis qubits) :
    writeRegisterBits register bits input =
      Function.update input (register.wire 0) (bits 0) := by
  funext wire
  by_cases selected : wire = register.wire 0
  · subst wire
    simp
  · rw [writeRegisterBits_apply_outside]
    · simp [Function.update, selected]
    · intro index equal
      have indexZero : index = 0 := Fin.eq_zero index
      subst index
      exact selected equal.symm

/-- Reading a wire written by `writeRegisterValue` returns the corresponding
little-endian value bit. -/
@[simp] theorem writeRegisterValue_apply_wire {qubits width : Nat}
    (register : Register qubits width) (value : Nat)
    (input : QubitBasis qubits) (index : Fin width) :
    writeRegisterValue register value input (register.wire index) =
      value.testBit index.val := by
  exact writeRegisterBits_apply_wire register _ input index

/-- A register write preserves every wire outside that register. -/
theorem writeRegisterValue_apply_outside {qubits width : Nat}
    (register : Register qubits width) (value : Nat)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : ∀ index, register.wire index ≠ wire) :
    writeRegisterValue register value input wire = input wire := by
  exact writeRegisterBits_apply_outside register _ input wire outside

/-- Read a register as an unsigned little-endian natural number. -/
def registerValue {qubits width : Nat}
    (register : Register qubits width) (input : QubitBasis qubits) : Nat :=
  qubitBasisLittleEndianIndex width (register.read input)

/-- Writing back the value read from a register is the identity basis action. -/
theorem writeRegisterValue_registerValue {qubits width : Nat}
    (register : Register qubits width) (input : QubitBasis qubits) :
    writeRegisterValue register (registerValue register input) input = input := by
  funext wire
  by_cases inside : ∃ index, register.wire index = wire
  · rcases inside with ⟨index, rfl⟩
    rw [writeRegisterValue_apply_wire]
    have recovered := congrFun
      (qubitBasisOfLittleEndianIndex_index (register.read input)) index
    exact recovered
  · rw [writeRegisterValue_apply_outside]
    intro index equal
    exact inside ⟨index, equal⟩

/-- Sum bit of a classical full adder. -/
def fullAdderSum (left right carry : Bool) : Bool :=
  Bool.xor (Bool.xor left right) carry

/-- Carry-out bit of a classical full adder. -/
def fullAdderCarry (left right carry : Bool) : Bool :=
  (left && right) || (left && carry) || (right && carry)

/-- Little-endian ripple sum bits, including one input carry and discarding the
final carry modulo the chosen width. -/
def rippleSumBits : (width : Nat) → Bool → QubitBasis width →
    QubitBasis width → QubitBasis width
  | 0, _, _, _ => fun index => Fin.elim0 index
  | width + 1, carry, addend, accumulator => fun index =>
      Fin.cases
        (fullAdderSum (addend 0) (accumulator 0) carry)
        (rippleSumBits width
          (fullAdderCarry (addend 0) (accumulator 0) carry)
          (fun higher => addend higher.succ)
          (fun higher => accumulator higher.succ))
        index

/-- Pulling a factor of two through a binary-width remainder, while retaining
one explicit low bit. -/
theorem lowBit_add_two_mul_mod (low value modulus : Nat)
    (low_lt_two : low < 2) (modulus_positive : 0 < modulus) :
    low + 2 * (value % modulus) =
      (low + 2 * value) % (2 * modulus) := by
  rw [Nat.add_mod, Nat.mul_mod_mul_left]
  have low_lt_product : low < 2 * modulus := by omega
  rw [Nat.mod_eq_of_lt low_lt_product]
  have remainder_lt := Nat.mod_lt value modulus_positive
  have sum_lt : low + 2 * (value % modulus) < 2 * modulus := by omega
  exact (Nat.mod_eq_of_lt sum_lt).symm

/-- A Boolean bit constructor is its explicit low bit plus twice its tail. -/
theorem natBit_eq_lowBit_add_two_mul (value : Bool) (tail : Nat) :
    Nat.bit value tail = Nat.bit value 0 + 2 * tail := by
  cases value
  · simp [Nat.bit]
  · simp [Nat.bit]
    omega

/-- The sum bit and carry-out of a full adder encode the sum of its three input
bits. -/
theorem fullAdder_bit_decomposition (left right carry : Bool) :
    Nat.bit (fullAdderSum left right carry) 0 +
        2 * Nat.bit (fullAdderCarry left right carry) 0 =
      Nat.bit left 0 + Nat.bit right 0 + Nat.bit carry 0 := by
  cases left <;> cases right <;> cases carry <;>
    norm_num [fullAdderSum, fullAdderCarry, Nat.bit]

/-- The full-adder sum is symmetric in its outer inputs. -/
theorem fullAdderSum_outer_comm (left middle right : Bool) :
    fullAdderSum left middle right = fullAdderSum right middle left := by
  cases left <;> cases middle <;> cases right <;> rfl

/-- The full-adder carry is symmetric in its outer inputs. -/
theorem fullAdderCarry_outer_comm (left middle right : Bool) :
    fullAdderCarry left middle right = fullAdderCarry right middle left := by
  cases left <;> cases middle <;> cases right <;> rfl

/-- One full-adder bit and its carry are the low-bit decomposition of natural
addition modulo twice the tail modulus. -/
theorem fullAdder_mod (left right carry : Bool) (leftTail rightTail modulus : Nat)
    (modulus_positive : 0 < modulus) :
    Nat.bit (fullAdderSum left right carry) 0 +
        2 * ((leftTail + rightTail +
          Nat.bit (fullAdderCarry left right carry) 0) % modulus) =
      (Nat.bit left leftTail + Nat.bit right rightTail + Nat.bit carry 0) %
        (2 * modulus) := by
  have lowBound : Nat.bit (fullAdderSum left right carry) 0 < 2 := by
    cases fullAdderSum left right carry <;> simp [Nat.bit]
  calc
    Nat.bit (fullAdderSum left right carry) 0 +
          2 * ((leftTail + rightTail +
            Nat.bit (fullAdderCarry left right carry) 0) % modulus) =
        (Nat.bit (fullAdderSum left right carry) 0 +
          2 * (leftTail + rightTail +
            Nat.bit (fullAdderCarry left right carry) 0)) %
          (2 * modulus) :=
      lowBit_add_two_mul_mod _ _ _ lowBound modulus_positive
    _ = (Nat.bit left leftTail + Nat.bit right rightTail + Nat.bit carry 0) %
          (2 * modulus) := by
      congr 1
      rw [natBit_eq_lowBit_add_two_mul left,
        natBit_eq_lowBit_add_two_mul right]
      have bits := fullAdder_bit_decomposition left right carry
      omega

/-- Ripple bits encode addition modulo `2^width`. -/
theorem qubitBasisLittleEndianIndex_rippleSumBits :
    ∀ (width : Nat) (carry : Bool)
      (addend accumulator : QubitBasis width),
      qubitBasisLittleEndianIndex width
          (rippleSumBits width carry addend accumulator) =
        (qubitBasisLittleEndianIndex width addend +
          qubitBasisLittleEndianIndex width accumulator +
          Nat.bit carry 0) % (2 ^ width)
  | 0, carry, addend, accumulator => by
      simp only [qubitBasisLittleEndianIndex]
      norm_num [pow_zero, Nat.mod_one]
  | width + 1, carry, addend, accumulator => by
      let addendTail : QubitBasis width := fun index => addend index.succ
      let accumulatorTail : QubitBasis width :=
        fun index => accumulator index.succ
      have inductionHypothesis :=
        qubitBasisLittleEndianIndex_rippleSumBits width
          (fullAdderCarry (addend 0) (accumulator 0) carry)
          addendTail accumulatorTail
      change Nat.bit (fullAdderSum (addend 0) (accumulator 0) carry)
          (qubitBasisLittleEndianIndex width
            (rippleSumBits width
              (fullAdderCarry (addend 0) (accumulator 0) carry)
              addendTail accumulatorTail)) =
        (Nat.bit (addend 0)
            (qubitBasisLittleEndianIndex width addendTail) +
          Nat.bit (accumulator 0)
            (qubitBasisLittleEndianIndex width accumulatorTail) +
          Nat.bit carry 0) % (2 ^ (width + 1))
      rw [inductionHypothesis]
      rw [show Nat.bit (fullAdderSum (addend 0) (accumulator 0) carry)
          ((qubitBasisLittleEndianIndex width addendTail +
              qubitBasisLittleEndianIndex width accumulatorTail +
              Nat.bit (fullAdderCarry (addend 0) (accumulator 0) carry) 0) %
            2 ^ width) =
          Nat.bit (fullAdderSum (addend 0) (accumulator 0) carry) 0 +
            2 * ((qubitBasisLittleEndianIndex width addendTail +
                qubitBasisLittleEndianIndex width accumulatorTail +
                Nat.bit (fullAdderCarry (addend 0) (accumulator 0) carry) 0) %
              2 ^ width) by
        cases fullAdderSum (addend 0) (accumulator 0) carry
        · simp [Nat.bit]
        · simp [Nat.bit]
          omega]
      simpa [Nat.bit, Nat.pow_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using
        fullAdder_mod (addend 0) (accumulator 0) carry
          (qubitBasisLittleEndianIndex width addendTail)
          (qubitBasisLittleEndianIndex width accumulatorTail)
          (2 ^ width) (by positivity)

/-- Remove the low wire from a positive-width register. -/
def Register.dropLow {qubits width : Nat}
    (register : Register qubits (width + 1)) : Register qubits width where
  wire index := register.wire index.succ
  injective := by
    intro left right equal
    have values := congrArg Fin.val (register.injective equal)
    exact Fin.ext (Nat.succ.inj values)

/-- One source-order Cuccaro majority step. -/
def cuccaroMajorityStage {qubits : Nat}
    (a b carry : Fin qubits) : ClassicalReversibleStage qubits :=
  ClassicalReversibleStage.sequence [
    ClassicalReversibleStage.safeXorControlled carry b,
    ClassicalReversibleStage.safeXorControlled carry a,
    ClassicalReversibleStage.safeXorDoublyControlled a b carry]

/-- One source-order Cuccaro unmajority-and-add step. -/
def cuccaroUnmajorityAddStage {qubits : Nat}
    (a b carry : Fin qubits) : ClassicalReversibleStage qubits :=
  ClassicalReversibleStage.sequence [
    ClassicalReversibleStage.safeXorDoublyControlled a b carry,
    ClassicalReversibleStage.safeXorControlled carry a,
    ClassicalReversibleStage.safeXorControlled a b]

/-- Direct basis action of one source-order majority step. -/
def cuccaroMajorityBasisAction {qubits : Nat}
    (a b carry : Fin qubits) (input : QubitBasis qubits) : QubitBasis qubits :=
  let afterB := xorWire b (input carry) input
  let afterA := xorWire a (afterB carry) afterB
  xorWire carry (afterA a && afterA b) afterA

/-- Direct basis action of one source-order unmajority-and-add step. -/
def cuccaroUnmajorityAddBasisAction {qubits : Nat}
    (a b carry : Fin qubits) (input : QubitBasis qubits) : QubitBasis qubits :=
  let afterCarry := xorWire carry (input a && input b) input
  let afterA := xorWire a (afterCarry carry) afterCarry
  xorWire b (afterA a) afterA

/-- The MAJ stage reference is its direct three-update basis action. -/
theorem cuccaroMajorityStage_reference_apply {qubits : Nat}
    (a b carry : Fin qubits) (a_ne_b : a ≠ b)
    (a_ne_carry : a ≠ carry) (b_ne_carry : b ≠ carry)
    (input : QubitBasis qubits) :
    (cuccaroMajorityStage a b carry).reference input =
      cuccaroMajorityBasisAction a b carry input := by
  simp [cuccaroMajorityStage, ClassicalReversibleStage.sequence,
    ClassicalReversibleStage.safeXorControlled,
    ClassicalReversibleStage.safeXorDoublyControlled,
    ClassicalReversibleStage.reference,
    ClassicalReversibleInstruction.reference,
    ClassicalReversibleInstruction.basisAction,
    cuccaroMajorityBasisAction, a_ne_b, a_ne_carry, b_ne_carry,
    Ne.symm a_ne_carry, Ne.symm b_ne_carry]

/-- A majority step preserves every wire outside its three operands. -/
theorem cuccaroMajorityBasisAction_apply_outside {qubits : Nat}
    (a b carry wire : Fin qubits) (wire_ne_a : wire ≠ a)
    (wire_ne_b : wire ≠ b) (wire_ne_carry : wire ≠ carry)
    (input : QubitBasis qubits) :
    cuccaroMajorityBasisAction a b carry input wire = input wire := by
  simp [cuccaroMajorityBasisAction, xorWire, Function.update,
    wire_ne_a, wire_ne_b, wire_ne_carry]

/-- MAJ stores the full-adder carry-out in its `carry` wire. -/
theorem cuccaroMajorityBasisAction_apply_carry {qubits : Nat}
    (a b carry : Fin qubits) (a_ne_b : a ≠ b)
    (a_ne_carry : a ≠ carry) (b_ne_carry : b ≠ carry)
    (input : QubitBasis qubits) :
    cuccaroMajorityBasisAction a b carry input carry =
      fullAdderCarry (input a) (input b) (input carry) := by
  cases valueA : input a <;> cases valueB : input b <;>
    cases valueCarry : input carry <;>
    simp [cuccaroMajorityBasisAction, xorWire, Function.update,
      a_ne_b, Ne.symm a_ne_b,
      Ne.symm a_ne_carry, Ne.symm b_ne_carry,
      fullAdderCarry, valueA, valueB, valueCarry]

/-- The UMA stage reference is its direct three-update basis action. -/
theorem cuccaroUnmajorityAddStage_reference_apply {qubits : Nat}
    (a b carry : Fin qubits) (a_ne_b : a ≠ b)
    (a_ne_carry : a ≠ carry) (b_ne_carry : b ≠ carry)
    (input : QubitBasis qubits) :
    (cuccaroUnmajorityAddStage a b carry).reference input =
      cuccaroUnmajorityAddBasisAction a b carry input := by
  simp [cuccaroUnmajorityAddStage, ClassicalReversibleStage.sequence,
    ClassicalReversibleStage.safeXorControlled,
    ClassicalReversibleStage.safeXorDoublyControlled,
    ClassicalReversibleStage.reference,
    ClassicalReversibleInstruction.reference,
    ClassicalReversibleInstruction.basisAction,
    cuccaroUnmajorityAddBasisAction, a_ne_b, a_ne_carry, b_ne_carry,
    Ne.symm a_ne_carry]

/-- With no intervening higher-bit work, MAJ followed by UMA restores both
temporary wires and writes the full-adder sum into `b`. -/
theorem cuccaroMajority_then_unmajorityAdd_reference_apply {qubits : Nat}
    (a b carry : Fin qubits) (a_ne_b : a ≠ b)
    (a_ne_carry : a ≠ carry) (b_ne_carry : b ≠ carry)
    (input : QubitBasis qubits) :
    (cuccaroUnmajorityAddStage a b carry).reference
        ((cuccaroMajorityStage a b carry).reference input) =
      Function.update input b
        (fullAdderSum (input a) (input b) (input carry)) := by
  rw [cuccaroMajorityStage_reference_apply a b carry a_ne_b a_ne_carry
      b_ne_carry,
    cuccaroUnmajorityAddStage_reference_apply a b carry a_ne_b a_ne_carry
      b_ne_carry]
  funext wire
  by_cases wire_a : wire = a
  · subst wire
    cases valueA : input a <;> cases valueB : input b <;>
      cases valueCarry : input carry
    all_goals
      simp [cuccaroMajorityBasisAction, cuccaroUnmajorityAddBasisAction,
        xorWire, Function.update, a_ne_b, a_ne_carry, b_ne_carry,
        Ne.symm a_ne_b, Ne.symm a_ne_carry, Ne.symm b_ne_carry,
        valueA, valueB, valueCarry]
  · by_cases wire_b : wire = b
    · subst wire
      cases valueA : input a <;> cases valueB : input b <;>
        cases valueCarry : input carry
      all_goals
        simp [cuccaroMajorityBasisAction, cuccaroUnmajorityAddBasisAction,
          xorWire, Function.update, a_ne_b, a_ne_carry, b_ne_carry,
          Ne.symm a_ne_b, Ne.symm a_ne_carry, Ne.symm b_ne_carry,
          fullAdderSum, valueA, valueB, valueCarry]
    · by_cases wire_carry : wire = carry
      · subst wire
        cases valueA : input a <;> cases valueB : input b <;>
          cases valueCarry : input carry
        all_goals
          simp [cuccaroMajorityBasisAction, cuccaroUnmajorityAddBasisAction,
            xorWire, Function.update, a_ne_b, a_ne_carry, b_ne_carry,
            Ne.symm a_ne_b, Ne.symm a_ne_carry, Ne.symm b_ne_carry,
            valueA, valueB, valueCarry]
      · simp [cuccaroMajorityBasisAction, cuccaroUnmajorityAddBasisAction,
          xorWire, Function.update, wire_a, wire_b, wire_carry]

/-- Replacing an intervening higher-bit computation by any action that
preserves the three local MAJ wires yields the same restored low-wire result;
all other wires retain the intervening action's value. -/
theorem cuccaroUnmajorityAddBasisAction_of_preservedMajorityWires
    {qubits : Nat} (a b carry : Fin qubits)
    (a_ne_b : a ≠ b) (a_ne_carry : a ≠ carry)
    (b_ne_carry : b ≠ carry) (input middleState : QubitBasis qubits)
    (preservesA : middleState a = cuccaroMajorityBasisAction a b carry input a)
    (preservesB : middleState b = cuccaroMajorityBasisAction a b carry input b)
    (preservesCarry : middleState carry =
      cuccaroMajorityBasisAction a b carry input carry) :
    cuccaroUnmajorityAddBasisAction a b carry middleState = fun wire =>
      if wire = a then input a
      else if wire = b then fullAdderSum (input a) (input b) (input carry)
      else if wire = carry then input carry
      else middleState wire := by
  funext wire
  by_cases wire_a : wire = a
  · subst wire
    cases valueA : input a <;> cases valueB : input b <;>
      cases valueCarry : input carry
    all_goals
      simp_all [cuccaroMajorityBasisAction, cuccaroUnmajorityAddBasisAction,
        xorWire, Function.update,
        Ne.symm a_ne_b, Ne.symm a_ne_carry, Ne.symm b_ne_carry]
  · by_cases wire_b : wire = b
    · subst wire
      cases valueA : input a <;> cases valueB : input b <;>
        cases valueCarry : input carry
      all_goals
        simp_all [cuccaroMajorityBasisAction, cuccaroUnmajorityAddBasisAction,
          xorWire, Function.update,
          Ne.symm a_ne_b, Ne.symm a_ne_carry, Ne.symm b_ne_carry,
          fullAdderSum]
    · by_cases wire_carry : wire = carry
      · subst wire
        cases valueA : input a <;> cases valueB : input b <;>
          cases valueCarry : input carry
        all_goals
          simp_all [cuccaroMajorityBasisAction, cuccaroUnmajorityAddBasisAction,
            xorWire, Function.update,
            Ne.symm a_ne_b, Ne.symm a_ne_carry, Ne.symm b_ne_carry]
      · simp [cuccaroUnmajorityAddBasisAction, xorWire, Function.update,
          wire_a, wire_b, wire_carry]

/-- Layout for two positive-width equal-length registers and one carry wire.
The actual register width is `tailWidth + 1`. -/
structure CuccaroAddModSpec (qubits tailWidth : Nat) where
  addend : Register qubits (tailWidth + 1)
  accumulator : Register qubits (tailWidth + 1)
  carry : Fin qubits
  addend_accumulator_disjoint : ∀ left right,
    addend.wire left ≠ accumulator.wire right
  carry_ne_addend : ∀ index, carry ≠ addend.wire index
  carry_ne_accumulator : ∀ index, carry ≠ accumulator.wire index

/-- Low-index wire of a positive-width register. -/
def CuccaroAddModSpec.lowIndex {qubits tailWidth : Nat}
    (_spec : CuccaroAddModSpec qubits tailWidth) : Fin (tailWidth + 1) :=
  ⟨0, Nat.zero_lt_succ tailWidth⟩

/-- Higher-bit Cuccaro layout, using the previous low addend bit as carry. -/
def CuccaroAddModSpec.dropLow {qubits tailWidth : Nat}
    (spec : CuccaroAddModSpec qubits (tailWidth + 1)) :
    CuccaroAddModSpec qubits tailWidth where
  addend := spec.addend.dropLow
  accumulator := spec.accumulator.dropLow
  carry := spec.addend.wire spec.lowIndex
  addend_accumulator_disjoint := fun left right =>
    spec.addend_accumulator_disjoint left.succ right.succ
  carry_ne_addend := by
    intro index equal
    have values := congrArg Fin.val (spec.addend.injective equal)
    simp [CuccaroAddModSpec.lowIndex] at values
  carry_ne_accumulator := fun index =>
    spec.addend_accumulator_disjoint spec.lowIndex index.succ

/-- Source-order MAJ chain after the initial carry-to-low-bit step. -/
def CuccaroAddModSpec.forwardMiddleStages {qubits tailWidth : Nat}
    (spec : CuccaroAddModSpec qubits tailWidth) :
    List (ClassicalReversibleStage qubits) :=
  (List.finRange tailWidth).map fun index =>
    cuccaroMajorityStage
      (spec.addend.wire index.castSucc)
      (spec.accumulator.wire index.succ)
      (spec.addend.wire index.succ)

/-- Source-order reversed UMA chain. -/
def CuccaroAddModSpec.reverseMiddleStages {qubits tailWidth : Nat}
    (spec : CuccaroAddModSpec qubits tailWidth) :
    List (ClassicalReversibleStage qubits) :=
  spec.forwardMiddleStages.reverse.map fun stage => stage.reverse

/-- Recursive MAJ/higher-ripple/UMA form of the positive-width Cuccaro chain.
Its flattened order is the ascending MAJ chain followed by the descending UMA
chain. -/
def cuccaroRippleStage {qubits : Nat} :
    (tailWidth : Nat) → CuccaroAddModSpec qubits tailWidth →
      ClassicalReversibleStage qubits
  | 0, spec =>
      .seq
        (cuccaroMajorityStage spec.carry
          (spec.accumulator.wire spec.lowIndex)
          (spec.addend.wire spec.lowIndex))
        (cuccaroUnmajorityAddStage spec.carry
          (spec.accumulator.wire spec.lowIndex)
          (spec.addend.wire spec.lowIndex))
  | tailWidth + 1, spec =>
      .seq
        (cuccaroMajorityStage spec.carry
          (spec.accumulator.wire spec.lowIndex)
          (spec.addend.wire spec.lowIndex))
        (.seq (cuccaroRippleStage tailWidth spec.dropLow)
          (cuccaroUnmajorityAddStage spec.carry
            (spec.accumulator.wire spec.lowIndex)
            (spec.addend.wire spec.lowIndex)))

/-- Direct ripple meaning: write the modular full-adder sum into the
accumulator and preserve the addend, carry, and all outside wires. -/
def cuccaroRippleBasisAction {qubits tailWidth : Nat}
    (spec : CuccaroAddModSpec qubits tailWidth)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  writeRegisterBits spec.accumulator
    (rippleSumBits (tailWidth + 1) (input spec.carry)
      (spec.addend.read input) (spec.accumulator.read input)) input

/-- The one-bit recursive MAJ/UMA chain has the direct ripple meaning. -/
theorem cuccaroRippleStage_reference_apply_zero {qubits : Nat}
    (spec : CuccaroAddModSpec qubits 0) (input : QubitBasis qubits) :
    (cuccaroRippleStage 0 spec).reference input =
      cuccaroRippleBasisAction spec input := by
  have carry_ne_accumulator := spec.carry_ne_accumulator spec.lowIndex
  have carry_ne_addend := spec.carry_ne_addend spec.lowIndex
  have accumulator_ne_addend :=
    (spec.addend_accumulator_disjoint spec.lowIndex spec.lowIndex).symm
  have sumOrder :
      fullAdderSum (input spec.carry)
          (input (spec.accumulator.wire spec.lowIndex))
          (input (spec.addend.wire spec.lowIndex)) =
        fullAdderSum (input (spec.addend.wire spec.lowIndex))
          (input (spec.accumulator.wire spec.lowIndex))
          (input spec.carry) := by
    cases carryValue : input spec.carry <;>
      cases accumulatorValue : input (spec.accumulator.wire spec.lowIndex) <;>
      cases addendValue : input (spec.addend.wire spec.lowIndex) <;>
      simp [fullAdderSum]
  have sumOrderZero :
      fullAdderSum (input spec.carry)
          (input (spec.accumulator.wire 0))
          (input (spec.addend.wire 0)) =
        fullAdderSum (input (spec.addend.wire 0))
          (input (spec.accumulator.wire 0))
          (input spec.carry) := by
    simpa [CuccaroAddModSpec.lowIndex] using sumOrder
  rw [show cuccaroRippleStage 0 spec =
      .seq
        (cuccaroMajorityStage spec.carry
          (spec.accumulator.wire spec.lowIndex)
          (spec.addend.wire spec.lowIndex))
        (cuccaroUnmajorityAddStage spec.carry
          (spec.accumulator.wire spec.lowIndex)
          (spec.addend.wire spec.lowIndex)) by rfl]
  rw [show (ClassicalReversibleStage.seq _ _).reference input =
      (cuccaroUnmajorityAddStage spec.carry
        (spec.accumulator.wire spec.lowIndex)
        (spec.addend.wire spec.lowIndex)).reference
        ((cuccaroMajorityStage spec.carry
          (spec.accumulator.wire spec.lowIndex)
          (spec.addend.wire spec.lowIndex)).reference input) by rfl]
  rw [cuccaroMajority_then_unmajorityAdd_reference_apply
    spec.carry (spec.accumulator.wire spec.lowIndex)
      (spec.addend.wire spec.lowIndex) carry_ne_accumulator
      carry_ne_addend accumulator_ne_addend]
  rw [show Function.update input (spec.accumulator.wire spec.lowIndex)
      (fullAdderSum (input spec.carry)
        (input (spec.accumulator.wire spec.lowIndex))
        (input (spec.addend.wire spec.lowIndex))) =
      cuccaroRippleBasisAction spec input by
    rw [cuccaroRippleBasisAction, writeRegisterBits_widthOne]
    simpa [CuccaroAddModSpec.lowIndex, rippleSumBits, Register.read] using
      congrArg
        (fun value => Function.update input (spec.accumulator.wire 0) value)
        sumOrderZero]

/-- The recursive Cuccaro chain implements the direct ripple action at every
positive register width. -/
theorem cuccaroRippleStage_reference_apply :
    ∀ {qubits : Nat} (tailWidth : Nat)
      (spec : CuccaroAddModSpec qubits tailWidth)
      (input : QubitBasis qubits),
      (cuccaroRippleStage tailWidth spec).reference input =
        cuccaroRippleBasisAction spec input
  | _, 0, spec, input => cuccaroRippleStage_reference_apply_zero spec input
  | qubits, tailWidth + 1, spec, input => by
      let low := spec.lowIndex
      let a := spec.carry
      let b := spec.accumulator.wire low
      let carry := spec.addend.wire low
      let afterMajority := cuccaroMajorityBasisAction a b carry input
      let middleState := cuccaroRippleBasisAction spec.dropLow afterMajority
      have a_ne_b : a ≠ b := spec.carry_ne_accumulator low
      have a_ne_carry : a ≠ carry := spec.carry_ne_addend low
      have b_ne_carry : b ≠ carry :=
        (spec.addend_accumulator_disjoint low low).symm
      have majorityReference :
          (cuccaroMajorityStage a b carry).reference input = afterMajority :=
        cuccaroMajorityStage_reference_apply a b carry a_ne_b a_ne_carry
          b_ne_carry input
      have recursiveReference :
          (cuccaroRippleStage tailWidth spec.dropLow).reference afterMajority =
            middleState :=
        cuccaroRippleStage_reference_apply tailWidth spec.dropLow afterMajority
      have middlePreservesA : middleState a = afterMajority a := by
        apply writeRegisterBits_apply_outside
        intro index equal
        exact (spec.carry_ne_accumulator index.succ) equal.symm
      have middlePreservesB : middleState b = afterMajority b := by
        apply writeRegisterBits_apply_outside
        intro index equal
        have values := congrArg Fin.val (spec.accumulator.injective equal)
        simp [low, CuccaroAddModSpec.lowIndex] at values
      have middlePreservesCarry : middleState carry = afterMajority carry := by
        apply writeRegisterBits_apply_outside
        intro index equal
        exact (spec.addend_accumulator_disjoint low index.succ) equal.symm
      change (cuccaroUnmajorityAddStage a b carry).reference
          ((cuccaroRippleStage tailWidth spec.dropLow).reference
            ((cuccaroMajorityStage a b carry).reference input)) = _
      rw [majorityReference, recursiveReference,
        cuccaroUnmajorityAddStage_reference_apply a b carry a_ne_b
          a_ne_carry b_ne_carry]
      rw [cuccaroUnmajorityAddBasisAction_of_preservedMajorityWires
        a b carry a_ne_b a_ne_carry b_ne_carry input middleState
        middlePreservesA middlePreservesB middlePreservesCarry]
      change (fun wire =>
          if wire = a then input a
          else if wire = b then
            fullAdderSum (input a) (input b) (input carry)
          else if wire = carry then input carry
          else middleState wire) =
        writeRegisterBits spec.accumulator
          (rippleSumBits (tailWidth + 2) (input spec.carry)
            (spec.addend.read input) (spec.accumulator.read input)) input
      funext wire
      by_cases wire_a : wire = a
      · subst wire
        rw [if_pos rfl]
        exact (writeRegisterBits_apply_outside spec.accumulator
          (rippleSumBits (tailWidth + 2) (input spec.carry)
            (spec.addend.read input) (spec.accumulator.read input)) input a
          (fun index equal => (spec.carry_ne_accumulator index) equal.symm)).symm
      · rw [if_neg wire_a]
        by_cases wire_b : wire = b
        · subst wire
          rw [if_pos rfl, writeRegisterBits_apply_wire]
          change fullAdderSum (input a) (input b) (input carry) =
            rippleSumBits (tailWidth + 2) (input a)
              (spec.addend.read input) (spec.accumulator.read input) low
          simpa [rippleSumBits, Register.read, a, b, carry, low,
            CuccaroAddModSpec.lowIndex] using
            fullAdderSum_outer_comm (input a) (input b) (input carry)
        · rw [if_neg wire_b]
          by_cases wire_carry : wire = carry
          · subst wire
            rw [if_pos rfl]
            exact (writeRegisterBits_apply_outside spec.accumulator
              (rippleSumBits (tailWidth + 2) (input spec.carry)
                (spec.addend.read input) (spec.accumulator.read input)) input carry
              (fun index equal =>
                (spec.addend_accumulator_disjoint low index) equal.symm)).symm
          · rw [if_neg wire_carry]
            by_cases inAccumulator : ∃ index, spec.accumulator.wire index = wire
            · rcases inAccumulator with ⟨index, rfl⟩
              revert wire_a wire_b wire_carry
              refine Fin.cases ?_ (fun higher => ?_) index
              · intro wire_a wire_b wire_carry
                exact (wire_b (by simp [b, low,
                    CuccaroAddModSpec.lowIndex])).elim
              · intro wire_a wire_b wire_carry
                have tailWriter :
                    writeRegisterBits spec.dropLow.accumulator
                      (rippleSumBits (tailWidth + 1) (afterMajority carry)
                        (spec.dropLow.addend.read afterMajority)
                        (spec.dropLow.accumulator.read afterMajority))
                      afterMajority (spec.accumulator.wire higher.succ) =
                    rippleSumBits (tailWidth + 1) (afterMajority carry)
                      (spec.dropLow.addend.read afterMajority)
                      (spec.dropLow.accumulator.read afterMajority) higher := by
                  change writeRegisterBits spec.dropLow.accumulator _ _
                    (spec.dropLow.accumulator.wire higher) = _
                  exact writeRegisterBits_apply_wire _ _ _ _
                have fullWriter :
                    writeRegisterBits spec.accumulator
                      (rippleSumBits (tailWidth + 2) (input spec.carry)
                        (spec.addend.read input) (spec.accumulator.read input))
                      input (spec.accumulator.wire higher.succ) =
                    rippleSumBits (tailWidth + 2) (input spec.carry)
                      (spec.addend.read input) (spec.accumulator.read input)
                      higher.succ := writeRegisterBits_apply_wire _ _ _ _
                change
                  writeRegisterBits spec.dropLow.accumulator
                      (rippleSumBits (tailWidth + 1) (afterMajority carry)
                        (spec.dropLow.addend.read afterMajority)
                        (spec.dropLow.accumulator.read afterMajority))
                      afterMajority (spec.accumulator.wire higher.succ) = _
                rw [tailWriter, fullWriter]
                change rippleSumBits (tailWidth + 1)
                    (afterMajority carry)
                    (spec.dropLow.addend.read afterMajority)
                    (spec.dropLow.accumulator.read afterMajority) higher =
                  rippleSumBits (tailWidth + 1)
                    (fullAdderCarry (input carry) (input b) (input a))
                    (fun inner => spec.addend.read input inner.succ)
                    (fun inner => spec.accumulator.read input inner.succ) higher
                have afterCarry : afterMajority carry =
                    fullAdderCarry (input carry) (input b) (input a) := by
                  change cuccaroMajorityBasisAction a b carry input carry = _
                  rw [cuccaroMajorityBasisAction_apply_carry a b carry
                    a_ne_b a_ne_carry b_ne_carry]
                  exact fullAdderCarry_outer_comm (input a) (input b)
                    (input carry)
                have addendTail : spec.dropLow.addend.read afterMajority =
                    fun inner => spec.addend.read input inner.succ := by
                  funext inner
                  apply cuccaroMajorityBasisAction_apply_outside
                  · exact (spec.carry_ne_addend inner.succ).symm
                  · exact spec.addend_accumulator_disjoint inner.succ low
                  · intro equal
                    have values := congrArg Fin.val (spec.addend.injective equal)
                    simp [low, CuccaroAddModSpec.lowIndex] at values
                have accumulatorTail : spec.dropLow.accumulator.read afterMajority =
                    fun inner => spec.accumulator.read input inner.succ := by
                  funext inner
                  apply cuccaroMajorityBasisAction_apply_outside
                  · exact (spec.carry_ne_accumulator inner.succ).symm
                  · intro equal
                    have values := congrArg Fin.val
                      (spec.accumulator.injective equal)
                    simp [low, CuccaroAddModSpec.lowIndex] at values
                  · exact (spec.addend_accumulator_disjoint low inner.succ).symm
                rw [afterCarry, addendTail, accumulatorTail]
            · rw [writeRegisterBits_apply_outside]
              · change
                  writeRegisterBits spec.dropLow.accumulator
                    (rippleSumBits (tailWidth + 1) (afterMajority carry)
                      (spec.dropLow.addend.read afterMajority)
                      (spec.dropLow.accumulator.read afterMajority))
                    afterMajority wire = input wire
                rw [writeRegisterBits_apply_outside]
                · exact cuccaroMajorityBasisAction_apply_outside a b carry wire
                    wire_a wire_b wire_carry input
                · intro index equal
                  exact inAccumulator ⟨index.succ, equal⟩
              · intro index equal
                exact inAccumulator ⟨index, equal⟩

/-- Source-faithful Cuccaro addition plan.

At width one the source emits exactly one CNOT.  At larger width it emits the
initial MAJ, ascending MAJ chain, descending UMA chain, and final UMA.
-/
def cuccaroAddModStage {qubits tailWidth : Nat}
    (spec : CuccaroAddModSpec qubits tailWidth) :
    ClassicalReversibleStage qubits :=
  if tailWidth = 0 then
    ClassicalReversibleStage.safeXorControlled
      (spec.addend.wire spec.lowIndex)
      (spec.accumulator.wire spec.lowIndex)
  else
    cuccaroRippleStage tailWidth spec

private theorem safeXorControlled_reference_apply_direct
    {qubits : Nat} (control target : Fin qubits)
    (different : control ≠ target) (input : QubitBasis qubits) :
    (ClassicalReversibleStage.safeXorControlled control target).reference input =
      xorWire target (input control) input := by
  simp [ClassicalReversibleStage.safeXorControlled,
    ClassicalReversibleStage.reference,
    ClassicalReversibleInstruction.reference,
    ClassicalReversibleInstruction.basisAction, different]

/-- With a clean carry input, the source-order Cuccaro plan has the direct
ripple action at every positive register width. -/
theorem cuccaroAddModStage_reference_apply_of_carry_false
    {qubits tailWidth : Nat} (spec : CuccaroAddModSpec qubits tailWidth)
    (input : QubitBasis qubits) (carryFalse : input spec.carry = false) :
    (cuccaroAddModStage spec).reference input =
      cuccaroRippleBasisAction spec input := by
  cases tailWidth with
  | zero =>
      have different := spec.addend_accumulator_disjoint 0 0
      have lowZero : spec.lowIndex = 0 := Fin.eq_zero spec.lowIndex
      funext wire
      by_cases isAccumulator : wire = spec.accumulator.wire 0
      · subst wire
        rw [cuccaroAddModStage, if_pos rfl, lowZero,
          safeXorControlled_reference_apply_direct
            (spec.addend.wire 0) (spec.accumulator.wire 0) different]
        rw [cuccaroRippleBasisAction, writeRegisterBits_apply_wire]
        simp [rippleSumBits, Register.read, carryFalse, fullAdderSum, xorWire]
        cases input (spec.accumulator.wire 0) <;>
          cases input (spec.addend.wire 0) <;> rfl
      · rw [cuccaroAddModStage, if_pos rfl, lowZero,
          safeXorControlled_reference_apply_direct
            (spec.addend.wire 0) (spec.accumulator.wire 0) different]
        rw [cuccaroRippleBasisAction,
          writeRegisterBits_apply_outside]
        · simp [xorWire, isAccumulator]
        · intro index equal
          have indexZero : index = 0 := Fin.eq_zero index
          subst index
          exact isAccumulator equal.symm
  | succ tailWidth =>
      rw [cuccaroAddModStage, if_neg (Nat.succ_ne_zero tailWidth)]
      exact cuccaroRippleStage_reference_apply (tailWidth + 1) spec input

/-- Full-dirty independent Cuccaro target. -/
def cuccaroAddModDirtyOperator {qubits tailWidth : Nat}
    (spec : CuccaroAddModSpec qubits tailWidth) :
    Operator (QubitBasis qubits) :=
  (cuccaroAddModStage spec).analyticOperator

/-- Layout for a controlled constant addition through a masked addend
register. -/
structure ControlledAddConstantMod2PowSpec (qubits tailWidth : Nat) extends
    CuccaroAddModSpec qubits tailWidth where
  control : Fin qubits
  constant : Nat
  control_ne_addend : ∀ index, control ≠ addend.wire index
  control_ne_accumulator : ∀ index, control ≠ accumulator.wire index
  control_ne_carry : control ≠ carry

/-- Register indices selected by the recorded constant. -/
def controlledConstantMaskIndices {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    List (Fin (tailWidth + 1)) :=
  (List.finRange (tailWidth + 1)).filter fun index =>
    spec.constant.testBit index.val

/-- Physical mask targets in ascending source order. -/
def controlledConstantMaskTargets {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    List (Fin qubits) :=
  (controlledConstantMaskIndices spec).map spec.addend.wire

/-- Compute the selected constant into the masked addend register. -/
def controlledConstantMaskStage {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    ClassicalReversibleStage qubits :=
  ClassicalReversibleStage.sequence <|
    (controlledConstantMaskTargets spec).map
      (ClassicalReversibleStage.safeXorControlled spec.control)

/-- A safe controlled XOR with distinct wires has the direct XOR action. -/
theorem ClassicalReversibleStage.safeXorControlled_reference_apply
    {qubits : Nat} (control target : Fin qubits)
    (different : control ≠ target) (input : QubitBasis qubits) :
    (ClassicalReversibleStage.safeXorControlled control target).reference input =
      xorWire target (input control) input := by
  simp [ClassicalReversibleStage.safeXorControlled,
    ClassicalReversibleStage.reference,
    ClassicalReversibleInstruction.reference,
    ClassicalReversibleInstruction.basisAction, different]

/-- A duplicate-free list of controlled-X targets toggles exactly its members. -/
theorem ClassicalReversibleStage.sequenceSafeXorControlled_reference_apply
    {qubits : Nat} (control : Fin qubits) (targets : List (Fin qubits))
    (targetsNodup : targets.Nodup) (controlOutside : control ∉ targets)
    (input : QubitBasis qubits) :
    (ClassicalReversibleStage.sequence
        (targets.map (ClassicalReversibleStage.safeXorControlled control))).reference
        input = fun wire =>
      if wire ∈ targets then input wire != input control else input wire := by
  induction targets generalizing input with
  | nil => rfl
  | cons target rest inductionHypothesis =>
      have targetOutside : target ∉ rest := (List.nodup_cons.mp targetsNodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp targetsNodup).2
      have control_ne_target : control ≠ target := by
        intro equal
        exact controlOutside (by simp [equal])
      have controlOutsideRest : control ∉ rest := by
        intro member
        exact controlOutside (by simp [member])
      change (ClassicalReversibleStage.sequence
          (rest.map (ClassicalReversibleStage.safeXorControlled control))).reference
          ((ClassicalReversibleStage.safeXorControlled control target).reference
            input) = _
      rw [inductionHypothesis restNodup controlOutsideRest,
        ClassicalReversibleStage.safeXorControlled_reference_apply
          control target control_ne_target]
      funext wire
      by_cases wire_target : wire = target
      · subst wire
        simp [targetOutside, xorWire]
      · by_cases wire_rest : wire ∈ rest
        · simp [wire_target, wire_rest, xorWire, control_ne_target]
        · simp [wire_target, wire_rest, xorWire]

/-- The source-order mask target list contains no duplicate wire. -/
theorem controlledConstantMaskTargets_nodup {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    (controlledConstantMaskTargets spec).Nodup := by
  apply List.Nodup.map spec.addend.injective
  exact (List.nodup_finRange (tailWidth + 1)).filter _

/-- Membership in the mask target list is exactly the selected constant bit. -/
theorem controlledConstantMaskTargets_mem_iff {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth)
    (index : Fin (tailWidth + 1)) :
    spec.addend.wire index ∈ controlledConstantMaskTargets spec ↔
      spec.constant.testBit index.val := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨candidate, candidateMember, equal⟩
    have indicesEqual : candidate = index := spec.addend.injective equal
    subst candidate
    exact (List.mem_filter.mp candidateMember).2
  · intro selected
    apply List.mem_map.mpr
    exact ⟨index, List.mem_filter.mpr ⟨List.mem_finRange index, selected⟩, rfl⟩

/-- The external control is outside every mask target. -/
theorem controlledConstantMaskTargets_control_outside {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    spec.control ∉ controlledConstantMaskTargets spec := by
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  exact spec.control_ne_addend index equal.symm

/-- The mask pass toggles precisely the selected addend bit. -/
theorem controlledConstantMaskStage_reference_apply_addend
    {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth)
    (input : QubitBasis qubits) (index : Fin (tailWidth + 1)) :
    (controlledConstantMaskStage spec).reference input
        (spec.addend.wire index) =
      (input (spec.addend.wire index) !=
        (input spec.control && spec.constant.testBit index.val)) := by
  rw [controlledConstantMaskStage,
    ClassicalReversibleStage.sequenceSafeXorControlled_reference_apply
      spec.control (controlledConstantMaskTargets spec)
      (controlledConstantMaskTargets_nodup spec)
      (controlledConstantMaskTargets_control_outside spec)]
  change (if spec.addend.wire index ∈ controlledConstantMaskTargets spec then
      input (spec.addend.wire index) != input spec.control
    else input (spec.addend.wire index)) = _
  by_cases selected : spec.constant.testBit index.val
  · rw [if_pos ((controlledConstantMaskTargets_mem_iff spec index).2 selected)]
    simp [selected]
  · rw [if_neg (fun member => selected
      ((controlledConstantMaskTargets_mem_iff spec index).1 member))]
    simp [selected]

/-- The mask pass preserves every wire outside the addend register. -/
theorem controlledConstantMaskStage_reference_apply_outside
    {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : ∀ index, spec.addend.wire index ≠ wire) :
    (controlledConstantMaskStage spec).reference input wire = input wire := by
  rw [controlledConstantMaskStage,
    ClassicalReversibleStage.sequenceSafeXorControlled_reference_apply
      spec.control (controlledConstantMaskTargets spec)
      (controlledConstantMaskTargets_nodup spec)
      (controlledConstantMaskTargets_control_outside spec)]
  change (if wire ∈ controlledConstantMaskTargets spec then
      input wire != input spec.control else input wire) = input wire
  rw [if_neg]
  intro member
  rcases List.mem_map.mp member with ⟨index, _, equal⟩
  exact outside index equal

/-- On an all-zero addend, the mask pass encodes the selected constant modulo
the register width. -/
theorem controlledConstantMaskStage_reference_registerValue_of_clean
    {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth)
    (input : QubitBasis qubits)
    (addendClean : ∀ index, input (spec.addend.wire index) = false) :
    registerValue spec.addend
        ((controlledConstantMaskStage spec).reference input) =
      (if input spec.control then spec.constant else 0) %
        2 ^ (tailWidth + 1) := by
  let selectedValue := if input spec.control then spec.constant else 0
  let encoded : Fin (2 ^ (tailWidth + 1)) :=
    ⟨selectedValue % 2 ^ (tailWidth + 1),
      Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  have readEqual : spec.addend.read
        ((controlledConstantMaskStage spec).reference input) =
      qubitBasisOfLittleEndianIndex encoded := by
    funext index
    rw [Register.read,
      controlledConstantMaskStage_reference_apply_addend spec input index,
      addendClean index]
    change (false !=
        (input spec.control && spec.constant.testBit index.val)) =
      (selectedValue % 2 ^ (tailWidth + 1)).testBit index.val
    rw [Nat.testBit_mod_two_pow]
    cases controlValue : input spec.control <;>
      simp [index.isLt, selectedValue, controlValue]
  change qubitBasisLittleEndianIndex (tailWidth + 1)
      (spec.addend.read
        ((controlledConstantMaskStage spec).reference input)) = _
  rw [readEqual, qubitBasisLittleEndianIndex_basis]

/-- Ripple bits after a clean mask compute are the direct conditional modular
sum encoded in little-endian order. -/
theorem rippleSumBits_after_controlledConstantMask_of_clean
    {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth)
    (input : QubitBasis qubits)
    (clean : (∀ index, input (spec.addend.wire index) = false) ∧
      input spec.carry = false) :
    let first := (controlledConstantMaskStage spec).reference input
    let desiredValue :=
      (registerValue spec.accumulator input +
        if input spec.control then spec.constant else 0) %
          2 ^ (tailWidth + 1)
    rippleSumBits (tailWidth + 1) (first spec.carry)
        (spec.addend.read first) (spec.accumulator.read first) =
      qubitBasisOfLittleEndianIndex
        ⟨desiredValue, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
  dsimp only
  let first := (controlledConstantMaskStage spec).reference input
  have firstCarry : first spec.carry = false := by
    change (controlledConstantMaskStage spec).reference input spec.carry = false
    rw [controlledConstantMaskStage_reference_apply_outside]
    · exact clean.2
    · intro index equal
      exact (spec.carry_ne_addend index) equal.symm
  have firstAccumulator : spec.accumulator.read first =
      spec.accumulator.read input := by
    funext index
    apply controlledConstantMaskStage_reference_apply_outside
    intro addendIndex equal
    exact spec.addend_accumulator_disjoint addendIndex index equal
  have firstAddendValue : registerValue spec.addend first =
      (if input spec.control then spec.constant else 0) %
        2 ^ (tailWidth + 1) :=
    controlledConstantMaskStage_reference_registerValue_of_clean
      spec input clean.1
  apply (qubitBasisLittleEndianEquiv (tailWidth + 1)).injective
  apply Fin.ext
  change qubitBasisLittleEndianIndex (tailWidth + 1)
      (rippleSumBits (tailWidth + 1) (first spec.carry)
        (spec.addend.read first) (spec.accumulator.read first)) =
    qubitBasisLittleEndianIndex (tailWidth + 1)
      (qubitBasisOfLittleEndianIndex _)
  rw [qubitBasisLittleEndianIndex_basis,
    qubitBasisLittleEndianIndex_rippleSumBits, firstCarry]
  change (registerValue spec.addend first +
      registerValue spec.accumulator first + 0) %
        2 ^ (tailWidth + 1) = _
  rw [firstAddendValue]
  rw [show registerValue spec.accumulator first =
      registerValue spec.accumulator input by
    exact congrArg (qubitBasisLittleEndianIndex (tailWidth + 1))
      firstAccumulator]
  have accumulatorBound : registerValue spec.accumulator input <
      2 ^ (tailWidth + 1) :=
    qubitBasisLittleEndianIndex_lt (spec.accumulator.read input)
  cases controlValue : input spec.control
  · simp [Nat.mod_eq_of_lt accumulatorBound]
  · simp only [if_true, Nat.add_zero]
    calc
      (spec.constant % 2 ^ (tailWidth + 1) +
          registerValue spec.accumulator input) % 2 ^ (tailWidth + 1) =
          (spec.constant + registerValue spec.accumulator input) %
            2 ^ (tailWidth + 1) := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt accumulatorBound]
      _ = (registerValue spec.accumulator input + spec.constant) %
            2 ^ (tailWidth + 1) := by rw [Nat.add_comm]

/-- Source-order mask-compute, Cuccaro-add, mask-uncompute plan.

The second mask pass intentionally uses the same ascending source order as the
first pass, matching the recorded emitter rather than a syntactic reversal.
-/
def controlledAddConstantMod2PowStage {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    ClassicalReversibleStage qubits :=
  .seq (controlledConstantMaskStage spec)
    (.seq (cuccaroAddModStage spec.toCuccaroAddModSpec)
      (controlledConstantMaskStage spec))

/-- Full-dirty independent target of the complete recorded plan. -/
def controlledAddConstantMod2PowDirtyOperator {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    Operator (QubitBasis qubits) :=
  (controlledAddConstantMod2PowStage spec).analyticOperator

/-- The addend/carry clean predicate used by the direct modular-add meaning. -/
def controlledAddConstantMod2PowCleanPredicate {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth)
    (input : QubitBasis qubits) : Prop :=
  (∀ index, input (spec.addend.wire index) = false) ∧
    input spec.carry = false

/-- Direct clean-register meaning: conditionally add the recorded constant
modulo the accumulator width, preserving all outside wires. -/
def controlledAddConstantMod2PowBasisAction {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  if input spec.control then
    writeRegisterValue spec.accumulator
      ((registerValue spec.accumulator input + spec.constant) %
        2 ^ (tailWidth + 1)) input
  else input

/-- Direct modular addition controlled by an independently stated predicate.
No predicate-computation work register is part of this mathematical action. -/
def predicateControlledAddMod2PowBasisAction {qubits width : Nat}
    (predicate : QubitBasis qubits → Bool)
    (accumulator : Register qubits width) (constant : Nat)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  if predicate input then
    writeRegisterValue accumulator
      ((registerValue accumulator input + constant) % 2 ^ width) input
  else input

/-- Linear extension of predicate-controlled modular addition. -/
def predicateControlledAddMod2PowOperator {qubits width : Nat}
    (predicate : QubitBasis qubits → Bool)
    (accumulator : Register qubits width) (constant : Nat) :
    Operator (QubitBasis qubits) :=
  deterministicOperator
    (predicateControlledAddMod2PowBasisAction predicate accumulator constant)

/-- The ordinary one-control semantic action is the predicate specialization
of the independent direct modular-add specification. -/
theorem controlledAddConstantMod2PowBasisAction_eq_predicateControlled
    {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    controlledAddConstantMod2PowBasisAction spec =
      predicateControlledAddMod2PowBasisAction
        (fun input => input spec.control) spec.accumulator spec.constant := by
  funext input
  rfl

/-- Predicate-controlled modular addition preserves every wire outside its
accumulator.  This is the pure locality rule needed when the control predicate
is mathematical rather than stored in one control qubit. -/
theorem predicateControlledAddMod2PowBasisAction_apply_outside
    {qubits width : Nat}
    (predicate : QubitBasis qubits → Bool)
    (accumulator : Register qubits width) (constant : Nat)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outsideAccumulator : ∀ index, wire ≠ accumulator.wire index) :
    predicateControlledAddMod2PowBasisAction predicate accumulator constant
        input wire = input wire := by
  unfold predicateControlledAddMod2PowBasisAction
  split
  · exact writeRegisterValue_apply_outside accumulator _ input wire
      (fun index equal => outsideAccumulator index equal.symm)
  · rfl

/-- Direct independent clean-register target. -/
def controlledAddConstantMod2PowSemanticOperator {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (controlledAddConstantMod2PowBasisAction spec)

/-- Wires that the direct clean controlled-add meaning may change. -/
def controlledAddConstantMod2PowSemanticSupport {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    Finset (Fin qubits) :=
  Finset.univ.image spec.accumulator.wire

/-- The direct clean controlled-add action preserves every wire outside its
accumulator. -/
theorem controlledAddConstantMod2PowBasisAction_apply_outside
    {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outsideAccumulator : ∀ index, wire ≠ spec.accumulator.wire index) :
    controlledAddConstantMod2PowBasisAction spec input wire = input wire := by
  cases controlValue : input spec.control
  · simp [controlledAddConstantMod2PowBasisAction, controlValue]
  · rw [controlledAddConstantMod2PowBasisAction, if_pos]
    · exact writeRegisterValue_apply_outside spec.accumulator _ input wire
        (fun index equal => outsideAccumulator index equal.symm)
    · simpa using controlValue

/-- The semantic controlled-add operator changes only the accumulator,
independently of the compiler's masked-constant and carry work. -/
theorem controlledAddConstantMod2PowSemanticOperator_preservesOutside
    {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth) :
    OperatorPreservesOutside
      (controlledAddConstantMod2PowSemanticSupport spec)
      (controlledAddConstantMod2PowSemanticOperator spec) := by
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  apply controlledAddConstantMod2PowBasisAction_apply_outside spec input wire
  · intro index equal
    subst wire
    exact outside (by
      simp [controlledAddConstantMod2PowSemanticSupport])

/-- On clean masked-addend and carry inputs, the complete source-order plan is
the direct conditional modular-add basis action, and restores the clean work. -/
theorem controlledAddConstantMod2PowStage_reference_apply_of_clean
    {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth)
    (input : QubitBasis qubits)
    (clean : controlledAddConstantMod2PowCleanPredicate spec input) :
    (controlledAddConstantMod2PowStage spec).reference input =
      controlledAddConstantMod2PowBasisAction spec input := by
  let first := (controlledConstantMaskStage spec).reference input
  let middle := (cuccaroAddModStage spec.toCuccaroAddModSpec).reference first
  change (controlledConstantMaskStage spec).reference middle = _
  have firstCarry : first spec.carry = false := by
    change (controlledConstantMaskStage spec).reference input spec.carry = false
    rw [controlledConstantMaskStage_reference_apply_outside]
    · exact clean.2
    · intro index equal
      exact (spec.carry_ne_addend index) equal.symm
  have middleEqual : middle =
      cuccaroRippleBasisAction spec.toCuccaroAddModSpec first := by
    exact cuccaroAddModStage_reference_apply_of_carry_false
      spec.toCuccaroAddModSpec first firstCarry
  have rippleEqual :=
    rippleSumBits_after_controlledConstantMask_of_clean spec input clean
  funext wire
  by_cases inAccumulator : ∃ index, spec.accumulator.wire index = wire
  · rcases inAccumulator with ⟨index, rfl⟩
    rw [controlledConstantMaskStage_reference_apply_outside]
    · rw [middleEqual, cuccaroRippleBasisAction,
        writeRegisterBits_apply_wire, rippleEqual]
      cases controlValue : input spec.control
      · have accumulatorBound : registerValue spec.accumulator input <
            2 ^ (tailWidth + 1) :=
          qubitBasisLittleEndianIndex_lt (spec.accumulator.read input)
        have recovered := congrFun
          (qubitBasisOfLittleEndianIndex_index
            (spec.accumulator.read input)) index
        simp only [controlledAddConstantMod2PowBasisAction, controlValue,
          Bool.false_eq_true, if_false]
        simp only [Nat.add_zero, Nat.mod_eq_of_lt accumulatorBound]
        exact recovered
      · simp [controlledAddConstantMod2PowBasisAction, controlValue,
          qubitBasisOfLittleEndianIndex]
    · intro addendIndex equal
      exact spec.addend_accumulator_disjoint addendIndex index equal
  · by_cases inAddend : ∃ index, spec.addend.wire index = wire
    · rcases inAddend with ⟨index, rfl⟩
      have middleAddend : middle (spec.addend.wire index) =
          first (spec.addend.wire index) := by
        rw [middleEqual, cuccaroRippleBasisAction,
          writeRegisterBits_apply_outside]
        intro accumulatorIndex equal
        exact (spec.addend_accumulator_disjoint index accumulatorIndex)
          equal.symm
      have middleControl : middle spec.control = first spec.control := by
        rw [middleEqual, cuccaroRippleBasisAction,
          writeRegisterBits_apply_outside]
        intro accumulatorIndex equal
        exact (spec.control_ne_accumulator accumulatorIndex) equal.symm
      have firstControl : first spec.control = input spec.control := by
        apply controlledConstantMaskStage_reference_apply_outside
        intro addendIndex equal
        exact (spec.control_ne_addend addendIndex) equal.symm
      have firstAddend : first (spec.addend.wire index) =
          (input (spec.addend.wire index) !=
            (input spec.control && spec.constant.testBit index.val)) := by
        exact controlledConstantMaskStage_reference_apply_addend
          spec input index
      have targetAddend :
          controlledAddConstantMod2PowBasisAction spec input
              (spec.addend.wire index) = input (spec.addend.wire index) := by
        cases controlValue : input spec.control
        · simp [controlledAddConstantMod2PowBasisAction, controlValue]
        · rw [controlledAddConstantMod2PowBasisAction, if_pos]
          · apply writeRegisterValue_apply_outside
            intro accumulatorIndex equal
            exact spec.addend_accumulator_disjoint index accumulatorIndex
              equal.symm
          · simpa using controlValue
      rw [controlledConstantMaskStage_reference_apply_addend,
        middleAddend, middleControl, firstControl,
        firstAddend, targetAddend, clean.1 index]
      cases input spec.control <;> cases spec.constant.testBit index.val <;>
        decide
    · rw [controlledConstantMaskStage_reference_apply_outside]
      · rw [middleEqual, cuccaroRippleBasisAction,
          writeRegisterBits_apply_outside]
        · have firstOutside : first wire = input wire := by
            apply controlledConstantMaskStage_reference_apply_outside
            intro index equal
            exact inAddend ⟨index, equal⟩
          rw [firstOutside]
          cases controlValue : input spec.control
          · simp [controlledAddConstantMod2PowBasisAction, controlValue]
          · rw [controlledAddConstantMod2PowBasisAction, if_pos]
            · rw [writeRegisterValue_apply_outside]
              intro index equal
              exact inAccumulator ⟨index, equal⟩
            · simpa using controlValue
        · intro index equal
          exact inAccumulator ⟨index, equal⟩
      · intro index equal
        exact inAddend ⟨index, equal⟩

/-- The direct conditional modular-add action restores the masked addend and
carry clean predicate. -/
theorem controlledAddConstantMod2PowBasisAction_clean
    {qubits tailWidth : Nat}
    (spec : ControlledAddConstantMod2PowSpec qubits tailWidth)
    (input : QubitBasis qubits)
    (clean : controlledAddConstantMod2PowCleanPredicate spec input) :
    controlledAddConstantMod2PowCleanPredicate spec
      (controlledAddConstantMod2PowBasisAction spec input) := by
  constructor
  · intro index
    cases controlValue : input spec.control
    · simpa [controlledAddConstantMod2PowBasisAction, controlValue] using
        clean.1 index
    · rw [controlledAddConstantMod2PowBasisAction, if_pos]
      · rw [writeRegisterValue_apply_outside]
        · exact clean.1 index
        · intro accumulatorIndex equal
          exact spec.addend_accumulator_disjoint index accumulatorIndex
            equal.symm
      · simpa using controlValue
  · cases controlValue : input spec.control
    · simpa [controlledAddConstantMod2PowBasisAction, controlValue] using
        clean.2
    · rw [controlledAddConstantMod2PowBasisAction, if_pos]
      · rw [writeRegisterValue_apply_outside]
        · exact clean.2
        · intro accumulatorIndex equal
          exact (spec.carry_ne_accumulator accumulatorIndex) equal.symm
      · simpa using controlValue

end

end VerifiedCircuitCore
