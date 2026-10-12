import QLean.Circuits.Foundation.ClassicalConstructionMultiControlledXCorrectnessAnalytic
import QLean.Circuits.Foundation.QubitBasisEncoding

/-!
# Equality-branch unsigned less-than semantics

This module gives basis-action semantics to the equality-flag / Boolean-branch
implementation of unsigned little-endian comparison.  It is intentionally
separate from the ripple-borrow comparator family.
-/

namespace VerifiedCircuitCore

namespace ClassicalReversibleStage

/-- A Boolean control row is enabled exactly when every wire has its expected
value. -/
def boolControlsSatisfied {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (input : QubitBasis qubits) : Bool :=
  controls.all fun control => decide (input control.1 = control.2)

/-- Target-flip parity of a source-ordered Boolean control program. -/
def boolControlProgramParity {qubits : Nat} :
    List (List (Fin qubits × Bool)) -> QubitBasis qubits -> Bool
  | [], _ => false
  | controls :: program, input =>
      if boolControlsSatisfied controls input then
        !(boolControlProgramParity program input)
      else
        boolControlProgramParity program input

/-- Parity of a Boolean list. -/
def boolListParity : List Bool -> Bool
  | [] => false
  | value :: values => if value then !(boolListParity values) else
      boolListParity values

/-- Bitwise equality / strict-less conditions, ordered from low to high
significance. -/
def equalityBranchLessConditions : List Bool -> List Bool -> List Bool ->
    List Bool
  | leftBit :: left, rightBit :: right, equalities =>
      ((!leftBit) && rightBit && (equalities.drop 1).all id) ::
        equalityBranchLessConditions left right (equalities.drop 1)
  | _, _, _ => []

/-- Equality-branch comparison on little-endian Boolean words. -/
def equalityBranchLittleEndianLess (left right : List Bool) : Bool :=
  boolListParity <| equalityBranchLessConditions left right
    (List.zipWith (fun leftBit rightBit => decide (leftBit = rightBit))
      left right)

/-- Natural value represented by a little-endian Boolean list. -/
def littleEndianListNat : List Bool -> Nat
  | [] => 0
  | bit :: bits => 2 * littleEndianListNat bits + bit.toNat

/-- The list decoder agrees with the canonical little-endian basis index. -/
theorem littleEndianListNat_finRange {width : Nat}
    (basis : QubitBasis width) :
    littleEndianListNat ((List.finRange width).map basis) =
      qubitBasisLittleEndianIndex width basis := by
  induction width with
  | zero => rfl
  | succ width inductionHypothesis =>
      rw [List.finRange_succ]
      simp only [List.map_cons, List.map_map, littleEndianListNat,
        qubitBasisLittleEndianIndex]
      change 2 * littleEndianListNat
          (List.map (fun wire => basis wire.succ) (List.finRange width)) +
          (basis 0).toNat = _
      rw [inductionHypothesis (fun wire => basis wire.succ)]
      cases basis 0 <;> rfl

@[simp] theorem invertZeroControls_nil {qubits : Nat} :
    invertZeroControls ([] : List (Fin qubits × Bool)) = .identity := rfl

@[simp] theorem invertZeroControls_cons_true {qubits : Nat}
    (wire : Fin qubits) (controls : List (Fin qubits × Bool)) :
    invertZeroControls ((wire, true) :: controls) =
      invertZeroControls controls := rfl

@[simp] theorem invertZeroControls_cons_false {qubits : Nat}
    (wire : Fin qubits) (controls : List (Fin qubits × Bool)) :
    invertZeroControls ((wire, false) :: controls) =
      .seq (.instruction (.xorOne wire)) (invertZeroControls controls) := rfl

/-- Zero-control preparation leaves every non-control wire unchanged. -/
theorem invertZeroControls_reference_apply_outside {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (wire : Fin qubits)
    (input : QubitBasis qubits) (outside : wire ∉ controls.map Prod.fst) :
    (invertZeroControls controls).reference input wire = input wire := by
  induction controls generalizing input with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨controlWire, expected⟩
      have wireDifferent : wire ≠ controlWire := by
        intro equal
        apply outside
        simp [equal]
      have tailOutside : wire ∉ controls.map Prod.fst := by
        intro member
        apply outside
        simp [member]
      cases expected with
      | false =>
          change (invertZeroControls controls).reference
              (xorWire controlWire true input) wire = input wire
          rw [inductionHypothesis (xorWire controlWire true input) tailOutside]
          exact xorWire_apply_other controlWire wire wireDifferent true input
      | true => exact inductionHypothesis input tailOutside

/-- After zero-control preparation, a control wire records whether its input
matched the expected Boolean. -/
theorem invertZeroControls_reference_apply_member {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (entry : Fin qubits × Bool) (input : QubitBasis qubits)
    (controlNodup : (controls.map Prod.fst).Nodup)
    (member : entry ∈ controls) :
    (invertZeroControls controls).reference input entry.1 =
      decide (input entry.1 = entry.2) := by
  induction controls generalizing entry input with
  | nil => simp at member
  | cons head controls inductionHypothesis =>
      rcases head with ⟨headWire, headExpected⟩
      have headFresh := (List.nodup_cons.mp controlNodup).1
      have tailNodup := (List.nodup_cons.mp controlNodup).2
      by_cases isHead : entry = (headWire, headExpected)
      · subst entry
        have tailOutside : headWire ∉ controls.map Prod.fst := headFresh
        cases headExpected with
        | false =>
            change (invertZeroControls controls).reference
                (xorWire headWire true input) headWire = _
            rw [invertZeroControls_reference_apply_outside controls headWire
              (xorWire headWire true input) tailOutside]
            cases value : input headWire <;> simp [xorWire, value]
        | true =>
            change (invertZeroControls controls).reference input headWire =
              decide (input headWire = true)
            rw [invertZeroControls_reference_apply_outside controls headWire
              input tailOutside]
            cases input headWire <;> rfl
      · have tailMember : entry ∈ controls := by
          simpa [isHead] using member
        have entryDifferent : entry.1 ≠ headWire := by
          intro equal
          apply headFresh
          have mapped : entry.1 ∈ controls.map Prod.fst :=
            List.mem_map.mpr ⟨entry, tailMember, rfl⟩
          simpa [equal] using mapped
        cases headExpected with
        | false =>
            change (invertZeroControls controls).reference
                (xorWire headWire true input) entry.1 = _
            rw [inductionHypothesis entry (xorWire headWire true input)
              tailNodup tailMember]
            rw [xorWire_apply_other headWire entry.1 entryDifferent]
        | true => exact inductionHypothesis entry input tailNodup tailMember

/-- Zero-control preparation commutes with a target XOR outside its controls. -/
theorem invertZeroControls_reference_commutes_xorWire {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (target : Fin qubits)
    (value : Bool) (input : QubitBasis qubits)
    (targetOutside : target ∉ controls.map Prod.fst) :
    (invertZeroControls controls).reference (xorWire target value input) =
      xorWire target value ((invertZeroControls controls).reference input) := by
  induction controls generalizing input with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨controlWire, expected⟩
      have different : controlWire ≠ target := by
        intro equal
        apply targetOutside
        simp [equal]
      have tailOutside : target ∉ controls.map Prod.fst := by
        intro member
        apply targetOutside
        simp [member]
      cases expected with
      | false =>
          change (invertZeroControls controls).reference
              (xorWire controlWire true (xorWire target value input)) = _
          rw [xorWire_commute controlWire target different]
          exact inductionHypothesis (xorWire controlWire true input) tailOutside
      | true => exact inductionHypothesis input tailOutside

/-- Repeating zero-control preparation restores the input when control wires
are distinct. -/
theorem invertZeroControls_reference_involutive {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (input : QubitBasis qubits)
    (controlNodup : (controls.map Prod.fst).Nodup) :
    (invertZeroControls controls).reference
        ((invertZeroControls controls).reference input) = input := by
  induction controls generalizing input with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨controlWire, expected⟩
      have headFresh := (List.nodup_cons.mp controlNodup).1
      have tailNodup := (List.nodup_cons.mp controlNodup).2
      cases expected with
      | true => exact inductionHypothesis input tailNodup
      | false =>
          change (invertZeroControls controls).reference
              (xorWire controlWire true
                ((invertZeroControls controls).reference
                  (xorWire controlWire true input))) = input
          rw [← invertZeroControls_reference_commutes_xorWire controls
            controlWire true (xorWire controlWire true input) headFresh]
          rw [inductionHypothesis
            (xorWire controlWire true (xorWire controlWire true input))
            tailNodup]
          exact xorWire_involutive controlWire true input

/-- Positive-control conjunction after zero-control preparation equals the
original Boolean control condition. -/
theorem allWiresTrue_invertZeroControls_reference {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (input : QubitBasis qubits)
    (controlNodup : (controls.map Prod.fst).Nodup) :
    allWiresTrue (controls.map Prod.fst)
        ((invertZeroControls controls).reference input) =
      boolControlsSatisfied controls input := by
  unfold allWiresTrue readWires
  have values :
      (controls.map Prod.fst).map
          ((invertZeroControls controls).reference input) =
        controls.map (fun entry => decide (input entry.1 = entry.2)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro entry member
    exact invertZeroControls_reference_apply_member controls entry input
      controlNodup member
  rw [values]
  simp [boolControlsSatisfied]

/-- A Boolean multi-controlled stage has its direct clean-work action. -/
theorem boolMultiControlledX_reference_apply_of_cleanWork {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (input : QubitBasis qubits)
    (enoughScratch : controls.length ≤ scratches.length + 1)
    (layoutNodup : (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (boolMultiControlledX controls scratches target).reference input =
      xorWire target (boolControlsSatisfied controls input) input := by
  let controlWires := controls.map Prod.fst
  let invert := invertZeroControls controls
  let prepared := invert.reference input
  have combinedNodup : (controlWires ++ scratches).Nodup :=
    (List.nodup_append.mp layoutNodup).1
  have controlNodup : controlWires.Nodup :=
    (List.nodup_append.mp combinedNodup).1
  have targetOutside : target ∉ controlWires := by
    intro member
    have separated := (List.nodup_append.mp layoutNodup).2.2
    exact separated target (List.mem_append_left scratches member)
      target (by simp) rfl
  have scratchesOutside : ∀ wire ∈ scratches, wire ∉ controlWires := by
    have separated := (List.nodup_append.mp combinedNodup).2.2
    intro wire scratchMember controlMember
    exact separated wire controlMember wire scratchMember rfl
  have preparedScratchZero : ∀ wire ∈ scratches, prepared wire = false := by
    intro wire member
    change (invertZeroControls controls).reference input wire = false
    rw [invertZeroControls_reference_apply_outside controls wire input
      (scratchesOutside wire member)]
    exact scratchZero wire member
  have preparedCondition :
      allWiresTrue controlWires prepared = boolControlsSatisfied controls input :=
    allWiresTrue_invertZeroControls_reference controls input controlNodup
  change invert.reference
      ((positiveMultiControlledX controlWires scratches target).reference
        prepared) = _
  rw [positiveMultiControlledX_reference_apply_of_cleanWork controlWires
    scratches target prepared (by simpa [controlWires] using enoughScratch)
    (by simpa [controlWires] using layoutNodup) preparedScratchZero]
  rw [preparedCondition]
  rw [invertZeroControls_reference_commutes_xorWire controls target
    (boolControlsSatisfied controls input) prepared targetOutside]
  rw [invertZeroControls_reference_involutive controls input controlNodup]

/-- One equality-flag stage writes bit equality into a clean flag. -/
theorem computeBitEqual_reference_apply_flag {qubits : Nat}
    (left right flag : Fin qubits)
    (leftDifferent : left ≠ flag) (rightDifferent : right ≠ flag)
    (input : QubitBasis qubits) (flagZero : input flag = false) :
    (computeBitEqual left right flag).reference input flag =
      decide (input left = input right) := by
  simp [computeBitEqual, safeXorControlled, leftDifferent, rightDifferent,
    ClassicalReversibleStage.reference,
    ClassicalReversibleInstruction.reference,
    ClassicalReversibleInstruction.basisAction, xorWire, flagZero]
  cases input left <;> cases input right <;> rfl

/-- One equality-flag stage changes no wire other than its flag. -/
theorem computeBitEqual_reference_apply_other {qubits : Nat}
    (left right flag wire : Fin qubits)
    (leftDifferent : left ≠ flag) (rightDifferent : right ≠ flag)
    (wireDifferent : wire ≠ flag) (input : QubitBasis qubits) :
    (computeBitEqual left right flag).reference input wire = input wire := by
  simp [computeBitEqual, safeXorControlled, leftDifferent, rightDifferent,
    ClassicalReversibleStage.reference,
    ClassicalReversibleInstruction.reference,
    ClassicalReversibleInstruction.basisAction, xorWire, wireDifferent]

/-- Equality-flag computation leaves every non-flag wire unchanged. -/
theorem computeEqualityFlags_reference_apply_outside {qubits : Nat}
    (left right flags : List (Fin qubits)) (wire : Fin qubits)
    (input : QubitBasis qubits)
    (leftDisjoint : left.Disjoint flags)
    (rightDisjoint : right.Disjoint flags)
    (outside : wire ∉ flags) :
    (computeEqualityFlags left right flags).reference input wire = input wire := by
  induction left generalizing right flags input with
  | nil => simp [computeEqualityFlags, sequence, reference]
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp [computeEqualityFlags, sequence, reference]
      | cons rightHead rightTail =>
          cases flags with
          | nil => simp [computeEqualityFlags, sequence, reference]
          | cons flagHead flagTail =>
              rcases List.disjoint_cons_right.mp leftDisjoint with
                ⟨flagHeadAbsentLeft, leftDisjointTailFlags⟩
              rcases List.disjoint_cons_right.mp rightDisjoint with
                ⟨flagHeadAbsentRight, rightDisjointTailFlags⟩
              have leftTailDisjoint : leftTail.Disjoint flagTail :=
                (List.disjoint_cons_left.mp leftDisjointTailFlags).2
              have rightTailDisjoint : rightTail.Disjoint flagTail :=
                (List.disjoint_cons_left.mp rightDisjointTailFlags).2
              have leftDifferent : leftHead ≠ flagHead := by
                intro equal
                subst leftHead
                exact flagHeadAbsentLeft (by simp)
              have rightDifferent : rightHead ≠ flagHead := by
                intro equal
                subst rightHead
                exact flagHeadAbsentRight (by simp)
              have outsideParts : wire ≠ flagHead ∧ wire ∉ flagTail := by
                simpa only [List.mem_cons, not_or] using outside
              change (computeEqualityFlags leftTail rightTail flagTail).reference
                  ((computeBitEqual leftHead rightHead flagHead).reference input)
                  wire = input wire
              rw [inductionHypothesis rightTail flagTail _ leftTailDisjoint
                rightTailDisjoint outsideParts.2]
              exact computeBitEqual_reference_apply_other leftHead rightHead
                flagHead wire leftDifferent rightDifferent outsideParts.1 input

/-- On clean, pairwise-disjoint flags, equality computation writes the
bitwise equality vector in source order. -/
theorem computeEqualityFlags_readWires {qubits : Nat}
    (left right flags : List (Fin qubits)) (input : QubitBasis qubits)
    (leftLength : left.length = flags.length)
    (rightLength : right.length = flags.length)
    (leftDisjoint : left.Disjoint flags)
    (rightDisjoint : right.Disjoint flags)
    (flagsNodup : flags.Nodup)
    (flagsZero : readWires flags input =
      List.replicate flags.length false) :
    readWires flags ((computeEqualityFlags left right flags).reference input) =
      List.zipWith (fun leftBit rightBit => decide (leftBit = rightBit))
        (readWires left input) (readWires right input) := by
  induction left generalizing right flags input with
  | nil =>
      have flagsEmpty : flags = [] := by
        cases flags with
        | nil => rfl
        | cons flagHead flagTail => simp at leftLength
      subst flags
      have rightEmpty : right = [] := by
        cases right with
        | nil => rfl
        | cons rightHead rightTail => simp at rightLength
      subst right
      rfl
  | cons leftHead leftTail inductionHypothesis =>
      cases flags with
      | nil => simp at leftLength
      | cons flagHead flagTail =>
          cases right with
          | nil => simp at rightLength
          | cons rightHead rightTail =>
              have leftTailLength : leftTail.length = flagTail.length := by
                simpa using Nat.succ.inj leftLength
              have rightTailLength : rightTail.length = flagTail.length := by
                simpa using Nat.succ.inj rightLength
              rcases List.disjoint_cons_right.mp leftDisjoint with
                ⟨flagHeadAbsentLeft, leftDisjointTailFlags⟩
              rcases List.disjoint_cons_left.mp leftDisjointTailFlags with
                ⟨leftHeadAbsentFlagTail, leftTailDisjoint⟩
              rcases List.disjoint_cons_right.mp rightDisjoint with
                ⟨flagHeadAbsentRight, rightDisjointTailFlags⟩
              rcases List.disjoint_cons_left.mp rightDisjointTailFlags with
                ⟨rightHeadAbsentFlagTail, rightTailDisjoint⟩
              have leftDifferent : leftHead ≠ flagHead := by
                intro equal
                subst leftHead
                exact flagHeadAbsentLeft (by simp)
              have rightDifferent : rightHead ≠ flagHead := by
                intro equal
                subst rightHead
                exact flagHeadAbsentRight (by simp)
              have flagHeadAbsentTail : flagHead ∉ flagTail :=
                (List.nodup_cons.mp flagsNodup).1
              have flagTailNodup : flagTail.Nodup :=
                (List.nodup_cons.mp flagsNodup).2
              have flagHeadZero : input flagHead = false := by
                have headEquality := congrArg List.head? flagsZero
                simpa [readWires, List.replicate_succ, ← Nat.succ_eq_add_one]
                  using headEquality
              have flagTailZero :
                  readWires flagTail input =
                    List.replicate flagTail.length false := by
                have tailEquality := congrArg List.tail flagsZero
                simpa [readWires] using tailEquality
              let firstState :=
                (computeBitEqual leftHead rightHead flagHead).reference input
              have leftTailUnchanged :
                  readWires leftTail firstState = readWires leftTail input := by
                apply List.map_congr_left
                intro wire member
                exact computeBitEqual_reference_apply_other leftHead rightHead
                  flagHead wire leftDifferent rightDifferent (by
                    intro equal
                    apply flagHeadAbsentLeft
                    rw [← equal]
                    exact List.mem_cons_of_mem leftHead member) input
              have rightTailUnchanged :
                  readWires rightTail firstState = readWires rightTail input := by
                apply List.map_congr_left
                intro wire member
                exact computeBitEqual_reference_apply_other leftHead rightHead
                  flagHead wire leftDifferent rightDifferent (by
                    intro equal
                    apply flagHeadAbsentRight
                    rw [← equal]
                    exact List.mem_cons_of_mem rightHead member) input
              have flagTailStillZero :
                  readWires flagTail firstState =
                    List.replicate flagTail.length false := by
                rw [show readWires flagTail firstState = readWires flagTail input by
                  apply List.map_congr_left
                  intro wire member
                  exact computeBitEqual_reference_apply_other leftHead rightHead
                    flagHead wire leftDifferent rightDifferent (by
                      intro equal
                      apply flagHeadAbsentTail
                      rw [← equal]
                      exact member) input]
                exact flagTailZero
              have tailResult := inductionHypothesis rightTail flagTail firstState
                leftTailLength rightTailLength leftTailDisjoint rightTailDisjoint
                flagTailNodup flagTailStillZero
              change readWires (flagHead :: flagTail)
                  ((computeEqualityFlags leftTail rightTail flagTail).reference
                    firstState) = _
              simp only [readWires, List.map_cons, List.zipWith_cons_cons]
              congr 1
              · rw [computeEqualityFlags_reference_apply_outside leftTail
                  rightTail flagTail flagHead firstState leftTailDisjoint
                  rightTailDisjoint flagHeadAbsentTail]
                exact computeBitEqual_reference_apply_flag leftHead rightHead
                  flagHead leftDifferent rightDifferent input flagHeadZero
              · change readWires flagTail
                    ((computeEqualityFlags leftTail rightTail flagTail).reference
                      firstState) = _
                rw [tailResult, leftTailUnchanged, rightTailUnchanged]
                rfl

/-- Equality of all zipped bit-equality tests is list equality. -/
theorem all_zipWith_decide_eq (left right : List Bool)
    (sameLength : left.length = right.length) :
    (List.zipWith (fun leftBit rightBit => decide (leftBit = rightBit))
      left right).all id = decide (left = right) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail => simp at sameLength
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp at sameLength
      | cons rightHead rightTail =>
          have tailLength : leftTail.length = rightTail.length := by
            simpa using Nat.succ.inj sameLength
          by_cases headEqual : leftHead = rightHead
          · subst rightHead
            simp [inductionHypothesis rightTail tailLength]
          · simp [headEqual]

/-- Equal-length little-endian Boolean words are determined by their natural
values. -/
theorem littleEndianListNat_injective_of_length_eq
    (left right : List Bool) (sameLength : left.length = right.length)
    (sameValue : littleEndianListNat left = littleEndianListNat right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail => simp at sameLength
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp at sameLength
      | cons rightHead rightTail =>
          have tailLength : leftTail.length = rightTail.length := by
            simpa using Nat.succ.inj sameLength
          cases leftHead <;> cases rightHead
          · congr
            apply inductionHypothesis rightTail tailLength
            simp [littleEndianListNat] at sameValue
            omega
          · simp [littleEndianListNat] at sameValue
            omega
          · simp [littleEndianListNat] at sameValue
            omega
          · congr
            apply inductionHypothesis rightTail tailLength
            simp [littleEndianListNat] at sameValue
            omega

/-- Head/tail recurrence of equality-branch comparison. -/
theorem equalityBranchLittleEndianLess_cons
    (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (sameLength : leftTail.length = rightTail.length) :
    equalityBranchLittleEndianLess (leftHead :: leftTail)
        (rightHead :: rightTail) =
      if (!leftHead) && rightHead && decide (leftTail = rightTail) then
        !(equalityBranchLittleEndianLess leftTail rightTail)
      else
        equalityBranchLittleEndianLess leftTail rightTail := by
  unfold equalityBranchLittleEndianLess
  simp only [List.zipWith_cons_cons, equalityBranchLessConditions, List.drop,
    boolListParity]
  rw [all_zipWith_decide_eq leftTail rightTail sameLength]

/-- The equality-branch Boolean comparison is ordinary unsigned `<`. -/
theorem equalityBranchLittleEndianLess_eq_decide_lt
    (left right : List Bool) (sameLength : left.length = right.length) :
    equalityBranchLittleEndianLess left right =
      decide (littleEndianListNat left < littleEndianListNat right) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail => simp at sameLength
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp at sameLength
      | cons rightHead rightTail =>
          have tailLength : leftTail.length = rightTail.length := by
            simpa using Nat.succ.inj sameLength
          have tailComparison := inductionHypothesis rightTail tailLength
          have tailValueNe_of_listNe (different : leftTail ≠ rightTail) :
              littleEndianListNat leftTail ≠ littleEndianListNat rightTail := by
            intro equal
            exact different <|
              littleEndianListNat_injective_of_length_eq leftTail rightTail
                tailLength equal
          by_cases tailsEqual : leftTail = rightTail
          · subst rightTail
            cases leftHead <;> cases rightHead <;>
              simp [equalityBranchLittleEndianLess_cons, tailComparison,
                littleEndianListNat]
          · have valuesDifferent := tailValueNe_of_listNe tailsEqual
            by_cases tailLess :
                littleEndianListNat leftTail < littleEndianListNat rightTail
            · have fullLess (leftBit rightBit : Bool) :
                  littleEndianListNat (leftBit :: leftTail) <
                    littleEndianListNat (rightBit :: rightTail) := by
                cases leftBit <;> cases rightBit <;>
                  simp [littleEndianListNat] <;> omega
              cases leftHead <;> cases rightHead <;>
                rw [equalityBranchLittleEndianLess_cons _ _ _ _ tailLength,
                  tailComparison] <;>
                simp [tailsEqual, tailLess, fullLess]
            · have tailGreater :
                  littleEndianListNat rightTail <
                    littleEndianListNat leftTail := by
                omega
              have fullNotLess (leftBit rightBit : Bool) :
                  ¬ littleEndianListNat (leftBit :: leftTail) <
                    littleEndianListNat (rightBit :: rightTail) := by
                cases leftBit <;> cases rightBit <;>
                  simp [littleEndianListNat] <;> omega
              cases leftHead <;> cases rightHead <;>
                rw [equalityBranchLittleEndianLess_cons _ _ _ _ tailLength,
                  tailComparison] <;>
                simp [tailsEqual, tailLess, fullNotLess]

/-- XOR outside a Boolean control row preserves its truth value. -/
theorem boolControlsSatisfied_xorWire_outside {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (target : Fin qubits)
    (value : Bool) (input : QubitBasis qubits)
    (targetOutside : target ∉ controls.map Prod.fst) :
    boolControlsSatisfied controls (xorWire target value input) =
      boolControlsSatisfied controls input := by
  induction controls with
  | nil => rfl
  | cons control controls inductionHypothesis =>
      rcases control with ⟨controlWire, expected⟩
      have different : controlWire ≠ target := by
        intro equal
        apply targetOutside
        simp [equal]
      have tailOutside : target ∉ controls.map Prod.fst := by
        intro member
        apply targetOutside
        simp [member]
      simp only [boolControlsSatisfied, List.all_cons]
      rw [xorWire_apply_other target controlWire different]
      congr 1
      exact inductionHypothesis tailOutside

/-- Program parity is the parity of its row truth values. -/
theorem boolControlProgramParity_eq_boolListParity {qubits : Nat}
    (program : List (List (Fin qubits × Bool)))
    (input : QubitBasis qubits) :
    boolControlProgramParity program input =
      boolListParity
        (program.map fun controls => boolControlsSatisfied controls input) := by
  induction program with
  | nil => rfl
  | cons controls program inductionHypothesis =>
      simp only [boolControlProgramParity, List.map_cons, boolListParity]
      rw [inductionHypothesis]

/-- XOR outside every row preserves the parity of a Boolean control program. -/
theorem boolControlProgramParity_xorWire_outside {qubits : Nat}
    (program : List (List (Fin qubits × Bool))) (target : Fin qubits)
    (value : Bool) (input : QubitBasis qubits)
    (targetOutside : ∀ controls ∈ program,
      target ∉ controls.map Prod.fst) :
    boolControlProgramParity program (xorWire target value input) =
      boolControlProgramParity program input := by
  induction program with
  | nil => rfl
  | cons controls program inductionHypothesis =>
      have headOutside := targetOutside controls (by simp)
      have tailOutside : ∀ tailControls ∈ program,
          target ∉ tailControls.map Prod.fst := by
        intro tailControls member
        exact targetOutside tailControls (by simp [member])
      simp only [boolControlProgramParity]
      rw [boolControlsSatisfied_xorWire_outside controls target value input
        headOutside]
      rw [inductionHypothesis tailOutside]

/-- A source-ordered Boolean branch program flips only its common target by
the parity of enabled rows and restores clean scratch after every row. -/
theorem boolControlledXProgram_reference_apply_of_cleanWork {qubits : Nat}
    (program : List (List (Fin qubits × Bool)))
    (scratches : List (Fin qubits)) (target : Fin qubits)
    (input : QubitBasis qubits)
    (enoughScratch : ∀ controls ∈ program,
      controls.length ≤ scratches.length + 1)
    (layoutNodup : ∀ controls ∈ program,
      (controls.map Prod.fst ++ scratches ++ [target]).Nodup)
    (scratchZero : ∀ wire ∈ scratches, input wire = false) :
    (boolControlledXProgram program scratches target).reference input =
      xorWire target (boolControlProgramParity program input) input := by
  induction program generalizing input with
  | nil =>
      simp [boolControlledXProgram, sequence, reference,
        boolControlProgramParity, xorWire]
  | cons controls program inductionHypothesis =>
      have headEnough := enoughScratch controls (by simp)
      have headLayout := layoutNodup controls (by simp)
      have tailEnough : ∀ tailControls ∈ program,
          tailControls.length ≤ scratches.length + 1 := by
        intro tailControls member
        exact enoughScratch tailControls (by simp [member])
      have tailLayout : ∀ tailControls ∈ program,
          (tailControls.map Prod.fst ++ scratches ++ [target]).Nodup := by
        intro tailControls member
        exact layoutNodup tailControls (by simp [member])
      have targetOutsideScratch : target ∉ scratches := by
        intro member
        have separated := (List.nodup_append.mp headLayout).2.2
        exact separated target (List.mem_append_right _ member)
          target (by simp) rfl
      have targetOutsideTailControls : ∀ tailControls ∈ program,
          target ∉ tailControls.map Prod.fst := by
        intro tailControls member targetMember
        have currentLayout := tailLayout tailControls member
        have separated := (List.nodup_append.mp currentLayout).2.2
        exact separated target (List.mem_append_left _ targetMember)
          target (by simp) rfl
      change (boolControlledXProgram program scratches target).reference
          ((boolMultiControlledX controls scratches target).reference input) = _
      rw [boolMultiControlledX_reference_apply_of_cleanWork controls scratches
        target input headEnough headLayout scratchZero]
      have scratchZeroAfter : ∀ wire ∈ scratches,
          xorWire target (boolControlsSatisfied controls input) input wire =
            false := by
        intro wire member
        rw [xorWire_apply_other target wire (by
          intro equal
          apply targetOutsideScratch
          simpa [equal] using member)]
        exact scratchZero wire member
      rw [inductionHypothesis
        (xorWire target (boolControlsSatisfied controls input) input)
        tailEnough tailLayout scratchZeroAfter]
      rw [boolControlProgramParity_xorWire_outside program target
        (boolControlsSatisfied controls input) input targetOutsideTailControls]
      cases firstEnabled : boolControlsSatisfied controls input <;>
        cases tailParity : boolControlProgramParity program input <;>
        simp [boolControlProgramParity, firstEnabled, tailParity, xorWire]

/-- Boolean program parity for the comparison rows equals the corresponding
list of bit conditions. -/
theorem boolControlProgramParity_equalityBranchLessThanControlProgram
    {qubits : Nat} (left right equalFlags : List (Fin qubits))
    (input : QubitBasis qubits) :
    boolControlProgramParity
        (equalityBranchLessThanControlProgram left right equalFlags) input =
      boolListParity (equalityBranchLessConditions
        (readWires left input) (readWires right input)
        (readWires equalFlags input)) := by
  rw [boolControlProgramParity_eq_boolListParity]
  congr 1
  induction left generalizing right equalFlags with
  | nil =>
      simp [equalityBranchLessThanControlProgram,
        equalityBranchLessConditions, readWires]
  | cons leftBit left inductionHypothesis =>
      cases right with
      | nil =>
          simp [equalityBranchLessThanControlProgram,
            equalityBranchLessConditions, readWires]
      | cons rightBit right =>
          have higherValues :
              ((equalFlags.drop 1).map fun wire => (wire, true)).all
                  (fun control => decide (input control.1 = control.2)) =
                ((equalFlags.drop 1).map input).all id := by
            rw [List.all_map, List.all_map]
            apply List.all_congr rfl
            intro wire
            change decide (input wire = true) = input wire
            cases input wire <;> rfl
          simp only [equalityBranchLessThanControlProgram, List.map_cons,
            equalityBranchLessConditions, readWires]
          congr 1
          · simp only [boolControlsSatisfied, List.all_cons]
            rw [higherValues]
            cases input leftBit <;> cases input rightBit <;> simp
          · simpa [readWires, List.map_drop] using
              inductionHypothesis right (equalFlags.drop 1)

/-- Every comparison row needs at most one more control than the equality
flag count. -/
theorem equalityBranchLessThanControlProgram_controls_length_le
    {qubits : Nat} :
    ∀ (left right equalFlags : List (Fin qubits))
      (controls : List (Fin qubits × Bool)),
      left.length = equalFlags.length ->
      controls ∈ equalityBranchLessThanControlProgram left right equalFlags ->
      controls.length ≤ equalFlags.length + 1
  | [], _, _, _, _, member => by
      simp [equalityBranchLessThanControlProgram] at member
  | _ :: _, [], _, _, _, member => by
      simp [equalityBranchLessThanControlProgram] at member
  | leftBit :: left, rightBit :: right, equalFlags, controls,
      lengthEqual, member => by
      simp only [equalityBranchLessThanControlProgram, List.mem_cons] at member
      rcases member with rfl | tailMember
      · cases equalFlags with
        | nil => simp at lengthEqual
        | cons _ equalFlags => simp
      · have tailLength : left.length = (equalFlags.drop 1).length := by
          simp only [List.length_cons, List.length_drop] at lengthEqual ⊢
          omega
        have bound := equalityBranchLessThanControlProgram_controls_length_le
          left right (equalFlags.drop 1) controls tailLength tailMember
        simp only [List.length_drop] at bound
        omega

/-- Every row control wire belongs to one of the two words or the equality
flag register. -/
theorem equalityBranchLessThanControlProgram_source_mem {qubits : Nat} :
    ∀ (left right equalFlags : List (Fin qubits))
      (controls : List (Fin qubits × Bool)),
      controls ∈ equalityBranchLessThanControlProgram left right equalFlags ->
      ∀ control ∈ controls, control.1 ∈ left ++ right ++ equalFlags
  | [], _, _, _, member => by
      simp [equalityBranchLessThanControlProgram] at member
  | _ :: _, [], _, _, member => by
      simp [equalityBranchLessThanControlProgram] at member
  | leftBit :: left, rightBit :: right, equalFlags, controls, member => by
      simp only [equalityBranchLessThanControlProgram, List.mem_cons] at member
      rcases member with rfl | tailMember
      · intro control controlMember
        simp only [List.mem_cons] at controlMember
        rcases controlMember with rfl | controlMember
        · simp
        · rcases controlMember with rfl | higherMember
          · simp
          · rcases List.mem_map.mp higherMember with ⟨wire, wireMember, rfl⟩
            have originalMember : wire ∈ equalFlags :=
              List.mem_of_mem_drop wireMember
            simp [originalMember]
      · intro control controlMember
        have tailResult := equalityBranchLessThanControlProgram_source_mem
          left right (equalFlags.drop 1) controls tailMember control controlMember
        rcases List.mem_append.mp tailResult with leftRightMember | flagMember
        · rcases List.mem_append.mp leftRightMember with leftMember | rightMember
          · simp [leftMember]
          · simp [rightMember]
        · have originalMember : control.1 ∈ equalFlags :=
            List.mem_of_mem_drop flagMember
          simp [originalMember]

/-- A comparison row has no repeated wire whenever its complete source
registers have no repeated wire. -/
theorem equalityBranchLessThanControlProgram_controls_nodup {qubits : Nat} :
    ∀ (left right equalFlags : List (Fin qubits))
      (controls : List (Fin qubits × Bool)),
      (left ++ right ++ equalFlags).Nodup ->
      controls ∈ equalityBranchLessThanControlProgram left right equalFlags ->
      (controls.map Prod.fst).Nodup
  | [], _, _, _, _, member => by
      simp [equalityBranchLessThanControlProgram] at member
  | _ :: _, [], _, _, _, member => by
      simp [equalityBranchLessThanControlProgram] at member
  | leftBit :: left, rightBit :: right, equalFlags, controls,
      sourceNodup, member => by
      simp only [equalityBranchLessThanControlProgram, List.mem_cons] at member
      have leftSplit :
          (leftBit :: left).Nodup ∧
          ((rightBit :: right) ++ equalFlags).Nodup ∧
          ∀ a ∈ leftBit :: left,
            ∀ b ∈ (rightBit :: right) ++ equalFlags, a ≠ b := by
        rw [← List.nodup_append]
        simpa [List.append_assoc] using sourceNodup
      have rightSplit := List.nodup_append.mp leftSplit.2.1
      rcases member with rfl | tailMember
      · simp only [List.map_cons, List.map_map]
        have mapIdentity :
            List.map
                (Prod.fst ∘ fun wire : Fin qubits => (wire, true))
                (equalFlags.drop 1) = equalFlags.drop 1 := by
          induction equalFlags.drop 1 with
          | nil => rfl
          | cons wire wires inductionHypothesis =>
              simp only [List.map_cons, Function.comp_apply,
                inductionHypothesis]
        rw [mapIdentity]
        change (leftBit :: rightBit :: equalFlags.drop 1).Nodup
        rw [List.nodup_cons, List.nodup_cons]
        refine ⟨?_, ?_, rightSplit.2.1.sublist
          (List.drop_sublist 1 equalFlags)⟩
        · intro member
          rcases List.mem_cons.mp member with equal | flagMember
          · exact leftSplit.2.2 leftBit (by simp) rightBit (by simp) equal
          · exact leftSplit.2.2 leftBit (by simp) _
              (List.mem_append_right _ (List.mem_of_mem_drop flagMember)) rfl
        · intro flagMember
          exact rightSplit.2.2 rightBit (by simp) _
            (List.mem_of_mem_drop flagMember) rfl
      · have tailLeftNodup : left.Nodup := leftSplit.1.tail
        have tailRightNodup : right.Nodup := rightSplit.1.tail
        have tailFlagsNodup : (equalFlags.drop 1).Nodup :=
          rightSplit.2.1.sublist (List.drop_sublist 1 equalFlags)
        have tailLeftRightDisjoint :
            ∀ a ∈ left, ∀ b ∈ right, a ≠ b := by
          intro a aMember b bMember
          exact leftSplit.2.2 a (by simp [aMember]) b
            (List.mem_append_left _ (by simp [bMember]))
        have tailLeftFlagsDisjoint :
            ∀ a ∈ left, ∀ b ∈ equalFlags.drop 1, a ≠ b := by
          intro a aMember b bMember
          exact leftSplit.2.2 a (by simp [aMember]) b
            (List.mem_append_right _ (List.mem_of_mem_drop bMember))
        have tailRightFlagsDisjoint :
            ∀ a ∈ right, ∀ b ∈ equalFlags.drop 1, a ≠ b := by
          intro a aMember b bMember
          exact rightSplit.2.2 a (by simp [aMember]) b
            (List.mem_of_mem_drop bMember)
        have tailSourceNodup :
            (left ++ right ++ equalFlags.drop 1).Nodup := by
          rw [List.nodup_append]
          refine ⟨?_, tailFlagsNodup, ?_⟩
          · rw [List.nodup_append]
            exact ⟨tailLeftNodup, tailRightNodup,
              tailLeftRightDisjoint⟩
          · intro a aMember b bMember
            rcases List.mem_append.mp aMember with aLeft | aRight
            · exact tailLeftFlagsDisjoint a aLeft b bMember
            · exact tailRightFlagsDisjoint a aRight b bMember
        exact equalityBranchLessThanControlProgram_controls_nodup left right
          (equalFlags.drop 1) controls tailSourceNodup tailMember

/-- A full source/work/target layout validates every Boolean comparison row. -/
theorem equalityBranchLessThanControlProgram_layout {qubits : Nat}
    (left right equalFlags scratches : List (Fin qubits))
    (target : Fin qubits)
    (fullLayout :
      (left ++ right ++ equalFlags ++ scratches ++ [target]).Nodup) :
    ∀ controls ∈ equalityBranchLessThanControlProgram left right equalFlags,
      (controls.map Prod.fst ++ scratches ++ [target]).Nodup := by
  intro controls controlsMember
  let sources := left ++ right ++ equalFlags
  let rest := scratches ++ [target]
  have split : sources.Nodup ∧ rest.Nodup ∧
      ∀ a ∈ sources, ∀ b ∈ rest, a ≠ b := by
    rw [← List.nodup_append]
    simpa [sources, rest, List.append_assoc] using fullLayout
  have combined : (controls.map Prod.fst ++ rest).Nodup := by
    rw [List.nodup_append]
    refine ⟨equalityBranchLessThanControlProgram_controls_nodup left right
      equalFlags controls split.1 controlsMember, split.2.1, ?_⟩
    intro wire wireMember other otherMember
    have sourceMember : wire ∈ sources := by
      rcases List.mem_map.mp wireMember with ⟨control, controlMember, rfl⟩
      exact equalityBranchLessThanControlProgram_source_mem left right
        equalFlags controls controlsMember control controlMember
    exact split.2.2 wire sourceMember other otherMember
  simpa [rest, List.append_assoc] using combined

/-- Comparison condition evaluated after equality-flag computation. -/
def equalityBranchLessThanCondition {qubits : Nat}
    (left right equalFlags : List (Fin qubits))
    (input : QubitBasis qubits) : Bool :=
  let computed := (computeEqualityFlags left right equalFlags).reference input
  boolControlProgramParity
    (equalityBranchLessThanControlProgram left right equalFlags) computed

/-- On clean equality flags, the computed branch condition equals the direct
little-endian comparison. -/
theorem equalityBranchLessThanCondition_eq_littleEndianLess {qubits : Nat}
    (left right equalFlags : List (Fin qubits))
    (input : QubitBasis qubits)
    (leftLength : left.length = equalFlags.length)
    (rightLength : right.length = equalFlags.length)
    (leftDisjointFlags : left.Disjoint equalFlags)
    (rightDisjointFlags : right.Disjoint equalFlags)
    (flagsNodup : equalFlags.Nodup)
    (flagsZero : readWires equalFlags input =
      List.replicate equalFlags.length false) :
    equalityBranchLessThanCondition left right equalFlags input =
      equalityBranchLittleEndianLess (readWires left input)
        (readWires right input) := by
  let computed := (computeEqualityFlags left right equalFlags).reference input
  have leftUnchanged : readWires left computed = readWires left input := by
    apply List.map_congr_left
    intro wire member
    exact computeEqualityFlags_reference_apply_outside left right equalFlags
      wire input leftDisjointFlags rightDisjointFlags
      ((List.disjoint_left.mp leftDisjointFlags) member)
  have rightUnchanged : readWires right computed = readWires right input := by
    apply List.map_congr_left
    intro wire member
    exact computeEqualityFlags_reference_apply_outside left right equalFlags
      wire input leftDisjointFlags rightDisjointFlags
      ((List.disjoint_left.mp rightDisjointFlags) member)
  have flagValues :
      readWires equalFlags computed =
        List.zipWith (fun leftBit rightBit => decide (leftBit = rightBit))
          (readWires left input) (readWires right input) :=
    computeEqualityFlags_readWires left right equalFlags input leftLength
      rightLength leftDisjointFlags rightDisjointFlags flagsNodup flagsZero
  unfold equalityBranchLessThanCondition
  rw [boolControlProgramParity_equalityBranchLessThanControlProgram]
  rw [leftUnchanged, rightUnchanged, flagValues]
  rfl

/-- Equality-flag computation commutes with XOR on a wire outside both words
and the flag register. -/
theorem computeEqualityFlags_reference_commutes_xorWire {qubits : Nat}
    (left right flags : List (Fin qubits)) (target : Fin qubits)
    (value : Bool) (input : QubitBasis qubits)
    (leftDisjoint : left.Disjoint flags)
    (rightDisjoint : right.Disjoint flags)
    (targetAbsentLeft : target ∉ left)
    (targetAbsentRight : target ∉ right)
    (targetAbsentFlags : target ∉ flags) :
    (computeEqualityFlags left right flags).reference
        (xorWire target value input) =
      xorWire target value
        ((computeEqualityFlags left right flags).reference input) := by
  induction left generalizing right flags input with
  | nil => simp [computeEqualityFlags, sequence, reference]
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp [computeEqualityFlags, sequence, reference]
      | cons rightHead rightTail =>
          cases flags with
          | nil => simp [computeEqualityFlags, sequence, reference]
          | cons flagHead flagTail =>
              rcases List.disjoint_cons_right.mp leftDisjoint with
                ⟨flagHeadAbsentLeft, leftDisjointTailFlags⟩
              rcases List.disjoint_cons_left.mp leftDisjointTailFlags with
                ⟨leftHeadAbsentFlagTail, leftTailDisjoint⟩
              rcases List.disjoint_cons_right.mp rightDisjoint with
                ⟨flagHeadAbsentRight, rightDisjointTailFlags⟩
              rcases List.disjoint_cons_left.mp rightDisjointTailFlags with
                ⟨rightHeadAbsentFlagTail, rightTailDisjoint⟩
              have leftDifferentFlag : leftHead ≠ flagHead := by
                intro equal
                subst leftHead
                exact flagHeadAbsentLeft (by simp)
              have rightDifferentFlag : rightHead ≠ flagHead := by
                intro equal
                subst rightHead
                exact flagHeadAbsentRight (by simp)
              have targetPartsLeft : target ≠ leftHead ∧ target ∉ leftTail := by
                simpa only [List.mem_cons, not_or] using targetAbsentLeft
              have targetPartsRight : target ≠ rightHead ∧ target ∉ rightTail := by
                simpa only [List.mem_cons, not_or] using targetAbsentRight
              have targetPartsFlags : target ≠ flagHead ∧ target ∉ flagTail := by
                simpa only [List.mem_cons, not_or] using targetAbsentFlags
              have outsideHead :
                  target ∉ (computeBitEqual leftHead rightHead flagHead).supportWires := by
                simp [computeBitEqual, safeXorControlled, supportWires,
                  ClassicalReversibleInstruction.supportWires,
                  leftDifferentFlag, rightDifferentFlag,
                  targetPartsLeft.1, targetPartsRight.1, targetPartsFlags.1]
              change (computeEqualityFlags leftTail rightTail flagTail).reference
                  ((computeBitEqual leftHead rightHead flagHead).reference
                    (xorWire target value input)) = _
              rw [reference_commutes_xorWire_of_not_mem_support
                (computeBitEqual leftHead rightHead flagHead) target value input
                outsideHead]
              rw [inductionHypothesis rightTail flagTail _ leftTailDisjoint
                rightTailDisjoint targetPartsLeft.2 targetPartsRight.2
                targetPartsFlags.2]
              rfl

/-- Layout evidence for the equality-branch comparator.  These fields match
the exact requirements of each clean Boolean branch and make the plan usable
with collision-safe, zip-truncating source lists. -/
structure EqualityBranchUnsignedLessThanSpec (qubits : Nat) where
  left : List (Fin qubits)
  right : List (Fin qubits)
  equalFlags : List (Fin qubits)
  scratch : List (Fin qubits)
  target : Fin qubits
  leftLength : left.length = equalFlags.length
  rightLength : right.length = equalFlags.length
  leftDisjointFlags : left.Disjoint equalFlags
  rightDisjointFlags : right.Disjoint equalFlags
  flagsDisjointScratch : equalFlags.Disjoint scratch
  flagsNodup : equalFlags.Nodup
  targetAbsentLeft : target ∉ left
  targetAbsentRight : target ∉ right
  targetAbsentFlags : target ∉ equalFlags
  targetAbsentScratch : target ∉ scratch
  programEnough : ∀ controls ∈
      equalityBranchLessThanControlProgram left right equalFlags,
    controls.length ≤ scratch.length + 1
  programLayout : ∀ controls ∈
      equalityBranchLessThanControlProgram left right equalFlags,
    (controls.map Prod.fst ++ scratch ++ [target]).Nodup

namespace EqualityBranchUnsignedLessThanSpec

/-- Construct a validated equality-branch plan from one full disjoint layout
and the equality-flag scratch capacity. -/
def ofFullLayout {qubits : Nat}
    (left right equalFlags scratch : List (Fin qubits))
    (target : Fin qubits)
    (leftLength : left.length = equalFlags.length)
    (rightLength : right.length = equalFlags.length)
    (fullLayout :
      (left ++ right ++ equalFlags ++ scratch ++ [target]).Nodup)
    (scratchEnough : equalFlags.length ≤ scratch.length) :
    EqualityBranchUnsignedLessThanSpec qubits := by
  have leftSplit : left.Nodup ∧
      (right ++ equalFlags ++ scratch ++ [target]).Nodup ∧
      ∀ a ∈ left, ∀ b ∈ right ++ equalFlags ++ scratch ++ [target], a ≠ b := by
    rw [← List.nodup_append]
    simpa [List.append_assoc] using fullLayout
  have rightSplit : right.Nodup ∧
      (equalFlags ++ scratch ++ [target]).Nodup ∧
      ∀ a ∈ right, ∀ b ∈ equalFlags ++ scratch ++ [target], a ≠ b := by
    rw [← List.nodup_append]
    simpa [List.append_assoc] using leftSplit.2.1
  have flagSplit : equalFlags.Nodup ∧
      (scratch ++ [target]).Nodup ∧
      ∀ a ∈ equalFlags, ∀ b ∈ scratch ++ [target], a ≠ b := by
    rw [← List.nodup_append]
    simpa [List.append_assoc] using rightSplit.2.1
  have scratchSplit := List.nodup_append.mp flagSplit.2.1
  have leftDisjointFlags : left.Disjoint equalFlags := by
    rw [List.disjoint_left]
    intro a aMember aFlagMember
    exact leftSplit.2.2 a aMember a (by
      simpa [List.append_assoc] using
        (List.mem_append_right right
          (List.mem_append_left (scratch ++ [target]) aFlagMember))) rfl
  have rightDisjointFlags : right.Disjoint equalFlags := by
    rw [List.disjoint_left]
    intro a aMember aFlagMember
    exact rightSplit.2.2 a aMember a (by
      simpa [List.append_assoc] using
        (List.mem_append_left (scratch ++ [target]) aFlagMember)) rfl
  have flagsDisjointScratch : equalFlags.Disjoint scratch := by
    rw [List.disjoint_left]
    intro a aMember aScratchMember
    exact flagSplit.2.2 a aMember a
      (List.mem_append_left [target] aScratchMember) rfl
  have targetAbsentLeft : target ∉ left := by
    intro member
    exact leftSplit.2.2 target member target (by simp) rfl
  have targetAbsentRight : target ∉ right := by
    intro member
    exact rightSplit.2.2 target member target (by simp) rfl
  have targetAbsentFlags : target ∉ equalFlags := by
    intro member
    exact flagSplit.2.2 target member target
      (List.mem_append_right scratch (List.mem_singleton_self target)) rfl
  have targetAbsentScratch : target ∉ scratch := by
    intro member
    exact scratchSplit.2.2 target member target (by simp) rfl
  exact
    { left := left
      right := right
      equalFlags := equalFlags
      scratch := scratch
      target := target
      leftLength := leftLength
      rightLength := rightLength
      leftDisjointFlags := leftDisjointFlags
      rightDisjointFlags := rightDisjointFlags
      flagsDisjointScratch := flagsDisjointScratch
      flagsNodup := flagSplit.1
      targetAbsentLeft := targetAbsentLeft
      targetAbsentRight := targetAbsentRight
      targetAbsentFlags := targetAbsentFlags
      targetAbsentScratch := targetAbsentScratch
      programEnough := by
        intro controls controlsMember
        have bound := equalityBranchLessThanControlProgram_controls_length_le
          left right equalFlags controls leftLength controlsMember
        omega
      programLayout :=
        equalityBranchLessThanControlProgram_layout left right equalFlags
          scratch target fullLayout }

/-- The source-faithful classical stage of a validated equality-branch plan. -/
def stage {qubits : Nat} (spec : EqualityBranchUnsignedLessThanSpec qubits) :
    ClassicalReversibleStage qubits :=
  equalityBranchUnsignedLessThanStage spec.left spec.right spec.equalFlags
    spec.scratch spec.target

/-- Clean comparison work predicate. -/
def cleanInput {qubits : Nat} (spec : EqualityBranchUnsignedLessThanSpec qubits)
    (input : QubitBasis qubits) : Prop :=
  (∀ wire ∈ spec.equalFlags, input wire = false) ∧
    ∀ wire ∈ spec.scratch, input wire = false

/-- Direct clean semantic action. -/
def basisAction {qubits : Nat} (spec : EqualityBranchUnsignedLessThanSpec qubits)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire spec.target
    (decide (littleEndianListNat (readWires spec.left input) <
      littleEndianListNat (readWires spec.right input))) input

/-- The direct semantic action preserves clean comparison work. -/
theorem basisAction_cleanInput {qubits : Nat}
    (spec : EqualityBranchUnsignedLessThanSpec qubits)
    (input : QubitBasis qubits) (clean : spec.cleanInput input) :
    spec.cleanInput (spec.basisAction input) := by
  unfold basisAction
  constructor
  · intro wire member
    rw [xorWire_apply_other spec.target wire (by
      intro equal
      apply spec.targetAbsentFlags
      simpa [equal] using member)]
    exact clean.1 wire member
  · intro wire member
    rw [xorWire_apply_other spec.target wire (by
      intro equal
      apply spec.targetAbsentScratch
      simpa [equal] using member)]
    exact clean.2 wire member

/-- The direct semantic action preserves every wire except the target. -/
theorem basisAction_apply_other {qubits : Nat}
    (spec : EqualityBranchUnsignedLessThanSpec qubits)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (different : wire ≠ spec.target) :
    spec.basisAction input wire = input wire := by
  exact xorWire_apply_other spec.target wire different _ input

/-- The equality-branch stage has the direct unsigned less-than action on
clean comparison work, restoring all flag and scratch wires. -/
theorem stage_reference_apply_of_cleanWork {qubits : Nat}
    (spec : EqualityBranchUnsignedLessThanSpec qubits)
    (input : QubitBasis qubits) (clean : spec.cleanInput input) :
    spec.stage.reference input = spec.basisAction input := by
  let compute := computeEqualityFlags spec.left spec.right spec.equalFlags
  let program := equalityBranchLessThanControlProgram
    spec.left spec.right spec.equalFlags
  let use := boolControlledXProgram program spec.scratch spec.target
  let computed := compute.reference input
  have flagsZero : readWires spec.equalFlags input =
      List.replicate spec.equalFlags.length false := by
    have allFalse : ∀ wires : List (Fin qubits),
        (∀ wire ∈ wires, input wire = false) ->
        readWires wires input = List.replicate wires.length false := by
      intro wires zero
      induction wires with
      | nil => rfl
      | cons wire wires inductionHypothesis =>
          simp only [readWires, List.map_cons, List.length_cons,
            List.replicate_succ]
          rw [zero wire (by simp)]
          have tail := inductionHypothesis (by
            intro tailWire member
            exact zero tailWire (by simp [member]))
          simpa [readWires] using congrArg (List.cons false) tail
    exact allFalse spec.equalFlags clean.1
  have computedScratchZero : ∀ wire ∈ spec.scratch,
      computed wire = false := by
    intro wire member
    change (computeEqualityFlags spec.left spec.right spec.equalFlags).reference
      input wire = false
    rw [computeEqualityFlags_reference_apply_outside spec.left spec.right
      spec.equalFlags wire input spec.leftDisjointFlags
      spec.rightDisjointFlags (by
        intro wireInFlags
        exact (List.disjoint_left.mp spec.flagsDisjointScratch)
          wireInFlags member)]
    exact clean.2 wire member
  have useResult :
      use.reference computed =
        xorWire spec.target
          (equalityBranchLessThanCondition spec.left spec.right
            spec.equalFlags input) computed := by
    exact boolControlledXProgram_reference_apply_of_cleanWork program
      spec.scratch spec.target computed spec.programEnough spec.programLayout
      computedScratchZero
  change compute.reverse.reference (use.reference (compute.reference input)) = _
  rw [useResult]
  rw [← computeEqualityFlags_reference_commutes_xorWire spec.left spec.right
    spec.equalFlags spec.target
    (equalityBranchLessThanCondition spec.left spec.right spec.equalFlags input)
    input spec.leftDisjointFlags spec.rightDisjointFlags spec.targetAbsentLeft
    spec.targetAbsentRight spec.targetAbsentFlags]
  rw [reverse_reference]
  rw [equalityBranchLessThanCondition_eq_littleEndianLess spec.left spec.right
    spec.equalFlags input spec.leftLength spec.rightLength
    spec.leftDisjointFlags spec.rightDisjointFlags spec.flagsNodup flagsZero]
  rw [equalityBranchLittleEndianLess_eq_decide_lt]
  · change compute.reference.symm
        (compute.reference (spec.basisAction input)) = spec.basisAction input
    exact compute.reference.symm_apply_apply _
  · simpa [readWires] using spec.leftLength.trans spec.rightLength.symm

end EqualityBranchUnsignedLessThanSpec

end ClassicalReversibleStage

end VerifiedCircuitCore
