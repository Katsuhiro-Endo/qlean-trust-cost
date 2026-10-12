import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic

/-!
# Classical-stage realizations of register copy actions

The stages below use only the typed classical instruction language.  Their
references are identified with the independently defined register basis maps.
-/

namespace VerifiedCircuitCore

namespace ClassicalReversibleStage

/-- Typed classical instruction stage for register XOR copy. -/
def registerXorCopyStage {qubits width : Nat}
    (spec : RegisterXorCopySpec qubits width) :
    ClassicalReversibleStage qubits :=
  sequence <| (List.finRange width).map fun index =>
    .instruction (.xorControlled
      (spec.source.wire index) (spec.target.wire index)
      (spec.disjoint index index))

/-- The typed register-copy stage has the independent pure basis action. -/
theorem registerXorCopyStage_reference_apply {qubits width : Nat}
    (spec : RegisterXorCopySpec qubits width) (input : QubitBasis qubits) :
    (registerXorCopyStage spec).reference input =
      registerXorCopyBasisAction spec input := by
  rw [registerXorCopyStage, sequence_reference_apply]
  unfold registerXorCopyBasisAction
  simp [List.foldl_map, ClassicalReversibleStage.reference,
    ClassicalReversibleInstruction.reference,
    ClassicalReversibleInstruction.basisAction]

/-- Typed classical instruction stage for controlled register XOR copy. -/
def controlledRegisterXorCopyStage {qubits width : Nat}
    (spec : ControlledRegisterXorCopySpec qubits width) :
    ClassicalReversibleStage qubits :=
  sequence <| (List.finRange width).map fun index =>
    .instruction (.xorDoublyControlled spec.control
      (spec.source.wire index) (spec.target.wire index)
      (spec.controlSourceDifferent index)
      (spec.controlTargetDifferent index)
      (spec.sourceTargetDisjoint index index))

/-- The typed controlled-copy stage has the independent pure basis action. -/
theorem controlledRegisterXorCopyStage_reference_apply {qubits width : Nat}
    (spec : ControlledRegisterXorCopySpec qubits width)
    (input : QubitBasis qubits) :
    (controlledRegisterXorCopyStage spec).reference input =
      controlledRegisterXorCopyBasisAction spec input := by
  rw [controlledRegisterXorCopyStage, sequence_reference_apply]
  unfold controlledRegisterXorCopyBasisAction
  simp [List.foldl_map, ClassicalReversibleStage.reference,
    ClassicalReversibleInstruction.reference,
    ClassicalReversibleInstruction.basisAction]

/-- Typed CNOT-Toffoli-CNOT stage for a one-bit controlled swap. -/
def fredkinStage {qubits : Nat} (control left right : Fin qubits)
    (controlLeftDifferent : control ≠ left)
    (controlRightDifferent : control ≠ right)
    (leftRightDifferent : left ≠ right) : ClassicalReversibleStage qubits :=
  .seq
    (.instruction (.xorControlled left right leftRightDifferent))
    (.seq
      (.instruction (.xorDoublyControlled control right left
        controlRightDifferent controlLeftDifferent
        (Ne.symm leftRightDifferent)))
      (.instruction (.xorControlled left right leftRightDifferent)))

/-- The typed Fredkin stage realizes the independent one-bit swap action. -/
theorem fredkinStage_reference_apply {qubits : Nat}
    (control left right : Fin qubits)
    (controlLeftDifferent : control ≠ left)
    (controlRightDifferent : control ≠ right)
    (leftRightDifferent : left ≠ right)
    (input : QubitBasis qubits) :
    (fredkinStage control left right controlLeftDifferent
      controlRightDifferent leftRightDifferent).reference input =
        fredkinBasisAction control left right input := by
  simp [fredkinStage, ClassicalReversibleStage.reference,
    ClassicalReversibleInstruction.reference,
    ClassicalReversibleInstruction.basisAction]
  funext wire
  by_cases controlValue : input control
  · by_cases wireIsLeft : wire = left
    · subst wire
      cases leftValue : input left <;> cases rightValue : input right <;>
        simp [fredkinBasisAction, controlValue, xorWire,
          Function.update_apply, leftValue, rightValue,
          controlRightDifferent, leftRightDifferent]
    · by_cases wireIsRight : wire = right
      · subst wire
        cases leftValue : input left <;> cases rightValue : input right <;>
          simp [fredkinBasisAction, controlValue, xorWire,
            leftValue, rightValue,
            controlRightDifferent, leftRightDifferent,
            Ne.symm leftRightDifferent]
      · simp [fredkinBasisAction, controlValue, xorWire,
          Function.update_apply, wireIsLeft, wireIsRight]
  · have controlFalse : input control = false :=
      Bool.eq_false_of_not_eq_true controlValue
    by_cases wireIsLeft : wire = left
    · subst wire
      cases leftValue : input left <;> cases rightValue : input right <;>
        simp [fredkinBasisAction, controlFalse, xorWire,
          Function.update_apply, leftValue, rightValue,
          controlRightDifferent, leftRightDifferent]
    · by_cases wireIsRight : wire = right
      · subst wire
        cases leftValue : input left <;> cases rightValue : input right <;>
          simp [fredkinBasisAction, controlFalse, xorWire,
            leftValue, rightValue,
            controlRightDifferent, leftRightDifferent,
            Ne.symm leftRightDifferent]
      · simp [fredkinBasisAction, controlFalse, xorWire,
          Function.update_apply, wireIsLeft, wireIsRight]

/-- Typed classical stage for a controlled register swap. -/
def controlledRegisterSwapStage {qubits width : Nat}
    (spec : ControlledRegisterSwapSpec qubits width) :
    ClassicalReversibleStage qubits :=
  sequence <| (List.finRange width).map fun index =>
    fredkinStage spec.control (spec.left.wire index) (spec.right.wire index)
      (spec.controlLeftDifferent index)
      (spec.controlRightDifferent index)
      (spec.leftRightDisjoint index index)

/-- The typed controlled-swap stage has the independent register basis
action on every input basis value. -/
theorem controlledRegisterSwapStage_reference_apply {qubits width : Nat}
    (spec : ControlledRegisterSwapSpec qubits width)
    (input : QubitBasis qubits) :
    (controlledRegisterSwapStage spec).reference input =
      controlledRegisterSwapBasisAction spec input := by
  rw [controlledRegisterSwapStage, sequence_reference_apply]
  unfold controlledRegisterSwapBasisAction
  simp [List.foldl_map, fredkinStage_reference_apply]

end ClassicalReversibleStage

end VerifiedCircuitCore
