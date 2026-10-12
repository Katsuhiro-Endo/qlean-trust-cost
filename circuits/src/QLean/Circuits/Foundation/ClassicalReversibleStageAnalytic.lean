import QLean.Circuits.Foundation.OperatorLocalityAnalytic

/-!
# Fin-wire古典可逆stageの回路非依存解析仕様

X・CNOT・Toffoli相当の型安全な命令と、その実行順合成を定義する。
衝突するwire指定を受けたsafe constructorは恒等stageへ退避する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 全dirty計算基底上で意味を持つ古典可逆命令。 -/
inductive ClassicalReversibleInstruction (qubits : Nat) where
  /-- 一bitを反転する。 -/
  | xorOne (target : Fin qubits)
  /-- control bitをtargetへXORする。 -/
  | xorControlled (control target : Fin qubits) (different : control ≠ target)
  /-- 二controlのANDをtargetへXORする。 -/
  | xorDoublyControlled
      (control₁ control₂ target : Fin qubits)
      (controlsDifferent : control₁ ≠ control₂)
      (firstDifferent : control₁ ≠ target)
      (secondDifferent : control₂ ≠ target)

namespace ClassicalReversibleInstruction

/-- 一命令の直接的な計算基底作用。 -/
def basisAction {qubits : Nat} :
    ClassicalReversibleInstruction qubits → QubitBasis qubits → QubitBasis qubits
  | .xorOne target => xorWire target true
  | .xorControlled control target _ =>
      fun input => xorWire target (input control) input
  | .xorDoublyControlled control₁ control₂ target _ _ _ =>
      fun input => xorWire target (input control₁ && input control₂) input

/-- 各古典可逆命令の基底作用は自己逆である。 -/
theorem basisAction_involutive {qubits : Nat}
    (instruction : ClassicalReversibleInstruction qubits) :
    Function.Involutive instruction.basisAction := by
  intro input
  cases instruction with
  | xorOne target =>
      funext wire
      by_cases isTarget : wire = target
      · subst wire
        simp [basisAction, xorWire]
      · simp [basisAction, xorWire, isTarget]
  | xorControlled control target different =>
      funext wire
      by_cases isTarget : wire = target
      · subst wire
        simp [basisAction, xorWire, different]
      · simp [basisAction, xorWire, isTarget, different]
  | xorDoublyControlled control₁ control₂ target _ firstDifferent
      secondDifferent =>
      funext wire
      by_cases isTarget : wire = target
      · subst wire
        simp [basisAction, xorWire, firstDifferent, secondDifferent]
      · simp [basisAction, xorWire, isTarget, firstDifferent, secondDifferent]

/-- 一命令の基底作用を自己逆な解析置換として束ねる。 -/
def reference {qubits : Nat}
    (instruction : ClassicalReversibleInstruction qubits) :
    Equiv.Perm (QubitBasis qubits) where
  toFun := instruction.basisAction
  invFun := instruction.basisAction
  left_inv := instruction.basisAction_involutive
  right_inv := instruction.basisAction_involutive

/-- Wires read or written by one classical reversible instruction. -/
def supportWires {qubits : Nat}
    (instruction : ClassicalReversibleInstruction qubits) : Finset (Fin qubits) :=
  match instruction with
  | .xorOne target => {target}
  | .xorControlled control target _ => {control, target}
  | .xorDoublyControlled control₁ control₂ target _ _ _ =>
      {control₁, control₂, target}

/-- XOR on a wire outside an instruction's support commutes with its action. -/
theorem basisAction_commutes_xorWire_of_not_mem_support {qubits : Nat}
    (instruction : ClassicalReversibleInstruction qubits)
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (outside : wire ∉ instruction.supportWires) :
    instruction.basisAction (xorWire wire value input) =
      xorWire wire value (instruction.basisAction input) := by
  cases instruction with
  | xorOne target =>
      have wire_ne_target : wire ≠ target := by
        intro equal
        subst wire
        exact outside (by simp [supportWires])
      funext output
      by_cases output_target : output = target
      · subst output
        simp [basisAction, xorWire, wire_ne_target,
          Ne.symm wire_ne_target]
      · by_cases output_wire : output = wire
        · subst output
          simp [basisAction, xorWire, wire_ne_target,
            Ne.symm wire_ne_target]
        · simp [basisAction, xorWire, wire_ne_target,
            Ne.symm wire_ne_target, output_target, output_wire]
  | xorControlled control target different =>
      have wire_ne_control : wire ≠ control := by
        intro equal
        subst wire
        exact outside (by simp [supportWires])
      have wire_ne_target : wire ≠ target := by
        intro equal
        subst wire
        exact outside (by simp [supportWires])
      funext output
      by_cases output_target : output = target
      · subst output
        simp [basisAction, xorWire, wire_ne_target,
          Ne.symm wire_ne_control, Ne.symm wire_ne_target]
      · by_cases output_wire : output = wire
        · subst output
          simp [basisAction, xorWire, wire_ne_target,
            Ne.symm wire_ne_control, Ne.symm wire_ne_target]
        · simp [basisAction, xorWire, wire_ne_target,
            Ne.symm wire_ne_control, Ne.symm wire_ne_target, output_target,
            output_wire]
  | xorDoublyControlled control₁ control₂ target controlsDifferent
      firstDifferent secondDifferent =>
      have wire_ne_control₁ : wire ≠ control₁ := by
        intro equal
        subst wire
        exact outside (by simp [supportWires])
      have wire_ne_control₂ : wire ≠ control₂ := by
        intro equal
        subst wire
        exact outside (by simp [supportWires])
      have wire_ne_target : wire ≠ target := by
        intro equal
        subst wire
        exact outside (by simp [supportWires])
      funext output
      by_cases output_target : output = target
      · subst output
        simp [basisAction, xorWire,
          wire_ne_target, Ne.symm wire_ne_control₁,
          Ne.symm wire_ne_control₂, Ne.symm wire_ne_target]
      · by_cases output_wire : output = wire
        · subst output
          simp [basisAction, xorWire,
            wire_ne_target, Ne.symm wire_ne_control₁,
            Ne.symm wire_ne_control₂, Ne.symm wire_ne_target]
        · simp [basisAction, xorWire,
            wire_ne_target, Ne.symm wire_ne_control₁,
            Ne.symm wire_ne_control₂, Ne.symm wire_ne_target, output_target,
            output_wire]

/-- 一命令の解析置換は自己逆である。 -/
theorem reference_selfInverse {qubits : Nat}
    (instruction : ClassicalReversibleInstruction qubits) :
    instruction.reference = instruction.reference⁻¹ := by
  apply Equiv.ext
  intro input
  rfl

end ClassicalReversibleInstruction

/-- 古典可逆命令を実行順に階層合成する解析stage。 -/
inductive ClassicalReversibleStage (qubits : Nat) where
  /-- 何もしないstage。 -/
  | identity
  /-- 一命令だけのstage。 -/
  | instruction (value : ClassicalReversibleInstruction qubits)
  /-- firstの後にsecondを実行する二項合成。 -/
  | seq (first second : ClassicalReversibleStage qubits)
  /-- 同じstageを指定回数だけ実行する。 -/
  | repeat (count : Nat) (body : ClassicalReversibleStage qubits)

namespace ClassicalReversibleStage

/-- stage全体の回路非依存な解析置換。 -/
def reference {qubits : Nat} :
    ClassicalReversibleStage qubits → Equiv.Perm (QubitBasis qubits)
  | .identity => 1
  | .instruction value => value.reference
  | .seq first second => second.reference * first.reference
  | .repeat count body => body.reference ^ count

/-- stageを実行順に逆転する。全命令は自己逆である。 -/
def reverse {qubits : Nat} :
    ClassicalReversibleStage qubits → ClassicalReversibleStage qubits
  | .identity => .identity
  | .instruction value => .instruction value
  | .seq first second => .seq second.reverse first.reverse
  | .repeat count body => .repeat count body.reverse

/-- Reversing the syntax realizes the inverse of the independent reference
permutation. -/
@[simp] theorem reverse_reference {qubits : Nat}
    (stage : ClassicalReversibleStage qubits) :
    stage.reverse.reference = stage.reference.symm := by
  induction stage with
  | identity => rfl
  | instruction value => exact value.reference_selfInverse
  | seq first second firstHypothesis secondHypothesis =>
      rw [reverse, reference, reference, firstHypothesis, secondHypothesis]
      change first.reference⁻¹ * second.reference⁻¹ =
        (second.reference * first.reference)⁻¹
      rw [mul_inv_rev]
  | «repeat» count body inductionHypothesis =>
      rw [reverse, reference, reference, inductionHypothesis]
      change body.reference⁻¹ ^ count = (body.reference ^ count)⁻¹
      rw [inv_pow]

/-- All wires read or written by a classical reversible stage. -/
def supportWires {qubits : Nat} :
    ClassicalReversibleStage qubits → Finset (Fin qubits)
  | .identity => ∅
  | .instruction value => value.supportWires
  | .seq first second => first.supportWires ∪ second.supportWires
  | .repeat _ body => body.supportWires

/-- Reversing a stage does not change its wire support. -/
@[simp] theorem supportWires_reverse {qubits : Nat}
    (stage : ClassicalReversibleStage qubits) :
    stage.reverse.supportWires = stage.supportWires := by
  induction stage with
  | identity => rfl
  | instruction value => rfl
  | seq first second firstHypothesis secondHypothesis =>
      simp [reverse, supportWires, firstHypothesis, secondHypothesis,
        Finset.union_comm]
  | «repeat» count body inductionHypothesis =>
      simp [reverse, supportWires, inductionHypothesis]

/-- XOR on a wire outside a stage's support commutes with its reference
permutation. -/
theorem reference_commutes_xorWire_of_not_mem_support {qubits : Nat}
    (stage : ClassicalReversibleStage qubits)
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (outside : wire ∉ stage.supportWires) :
    stage.reference (xorWire wire value input) =
      xorWire wire value (stage.reference input) := by
  induction stage generalizing input with
  | identity => rfl
  | instruction instruction =>
      exact instruction.basisAction_commutes_xorWire_of_not_mem_support
        wire value input outside
  | seq first second firstHypothesis secondHypothesis =>
      have outsideFirst : wire ∉ first.supportWires := by
        intro member
        exact outside (Finset.mem_union_left _ member)
      have outsideSecond : wire ∉ second.supportWires := by
        intro member
        exact outside (Finset.mem_union_right _ member)
      change second.reference (first.reference (xorWire wire value input)) = _
      rw [firstHypothesis input outsideFirst,
        secondHypothesis (first.reference input) outsideSecond]
      rfl
  | «repeat» count body bodyHypothesis =>
      change (body.reference ^ count) (xorWire wire value input) = _
      induction count generalizing input with
      | zero => rfl
      | succ count countHypothesis =>
          rw [pow_succ]
          change (body.reference ^ count)
              (body.reference (xorWire wire value input)) =
            xorWire wire value
              ((body.reference ^ count) (body.reference input))
          have outsideBody : wire ∉ body.supportWires := by
            simpa [supportWires] using outside
          rw [bodyHypothesis input outsideBody]
          have recurse := countHypothesis (body.reference input) (by
            simpa [supportWires] using outside)
          simpa [reference] using recurse

/-- The same support-locality rule is directly available for reverse stages. -/
theorem reverse_reference_commutes_xorWire_of_not_mem_support {qubits : Nat}
    (stage : ClassicalReversibleStage qubits)
    (wire : Fin qubits) (value : Bool) (input : QubitBasis qubits)
    (outside : wire ∉ stage.supportWires) :
    stage.reverse.reference (xorWire wire value input) =
      xorWire wire value (stage.reverse.reference input) := by
  apply reference_commutes_xorWire_of_not_mem_support
  simpa using outside

/-- A stage leaves every wire outside its support unchanged. -/
theorem reference_apply_of_not_mem_support {qubits : Nat}
    (stage : ClassicalReversibleStage qubits)
    (input : QubitBasis qubits) (wire : Fin qubits)
    (outside : wire ∉ stage.supportWires) :
    stage.reference input wire = input wire := by
  induction stage generalizing input with
  | identity => rfl
  | instruction instruction =>
      cases instruction with
      | xorOne target =>
          have different : wire ≠ target := by
            intro equal
            subst wire
            exact outside (by simp [supportWires,
              ClassicalReversibleInstruction.supportWires])
          simp [reference, ClassicalReversibleInstruction.reference,
            ClassicalReversibleInstruction.basisAction, xorWire, different]
      | xorControlled control target different =>
          have wire_ne_target : wire ≠ target := by
            intro equal
            subst wire
            exact outside (by simp [supportWires,
              ClassicalReversibleInstruction.supportWires])
          simp [reference, ClassicalReversibleInstruction.reference,
            ClassicalReversibleInstruction.basisAction, xorWire,
            wire_ne_target]
      | xorDoublyControlled control₁ control₂ target controlsDifferent
          firstDifferent secondDifferent =>
          have wire_ne_target : wire ≠ target := by
            intro equal
            subst wire
            exact outside (by simp [supportWires,
              ClassicalReversibleInstruction.supportWires])
          simp [reference, ClassicalReversibleInstruction.reference,
            ClassicalReversibleInstruction.basisAction, xorWire,
            wire_ne_target]
  | seq first second firstHypothesis secondHypothesis =>
      have outsideFirst : wire ∉ first.supportWires := by
        intro member
        exact outside (Finset.mem_union_left _ member)
      have outsideSecond : wire ∉ second.supportWires := by
        intro member
        exact outside (Finset.mem_union_right _ member)
      change second.reference (first.reference input) wire = input wire
      rw [secondHypothesis (first.reference input) outsideSecond,
        firstHypothesis input outsideFirst]
  | «repeat» count body bodyHypothesis =>
      have outsideBody : wire ∉ body.supportWires := by
        simpa [supportWires] using outside
      change (body.reference ^ count) input wire = input wire
      have powerOutside : ∀ repetitions (state : QubitBasis qubits),
          (body.reference ^ repetitions) state wire = state wire := by
        intro repetitions
        induction repetitions with
        | zero => intro state; rfl
        | succ repetitions inductionHypothesis =>
            intro state
            rw [pow_succ]
            change (body.reference ^ repetitions)
                (body.reference state) wire = state wire
            rw [inductionHypothesis (body.reference state),
              bodyHypothesis state outsideBody]
      exact powerOutside count input

/-- On its support, a stage reference depends only on the input values on
that support. -/
theorem reference_apply_congr_of_eq_on_support_of_mem {qubits : Nat}
    (stage : ClassicalReversibleStage qubits)
    (left right : QubitBasis qubits)
    (agree : ∀ wire, wire ∈ stage.supportWires →
      left wire = right wire)
    (wire : Fin qubits) (supported : wire ∈ stage.supportWires) :
    stage.reference left wire = stage.reference right wire := by
  induction stage generalizing left right wire with
  | identity => simp [supportWires] at supported
  | instruction instruction =>
      cases instruction with
      | xorOne target =>
          have wire_eq_target : wire = target := by
            simpa [supportWires,
              ClassicalReversibleInstruction.supportWires] using supported
          subst wire
          simp only [reference, ClassicalReversibleInstruction.reference,
            ClassicalReversibleInstruction.basisAction]
          simp [xorWire, agree target (by
            simp [supportWires,
              ClassicalReversibleInstruction.supportWires])]
      | xorControlled control target different =>
          simp only [reference, ClassicalReversibleInstruction.reference,
            ClassicalReversibleInstruction.basisAction]
          by_cases isTarget : wire = target
          · subst wire
            simp [xorWire,
              agree control (by simp [supportWires,
                ClassicalReversibleInstruction.supportWires]),
              agree target (by simp [supportWires,
                ClassicalReversibleInstruction.supportWires])]
          · simp [xorWire, isTarget, agree wire supported]
      | xorDoublyControlled control₁ control₂ target controlsDifferent
          firstDifferent secondDifferent =>
          simp only [reference, ClassicalReversibleInstruction.reference,
            ClassicalReversibleInstruction.basisAction]
          by_cases isTarget : wire = target
          · subst wire
            simp [xorWire,
              agree control₁ (by simp [supportWires,
                ClassicalReversibleInstruction.supportWires]),
              agree control₂ (by simp [supportWires,
                ClassicalReversibleInstruction.supportWires]),
              agree target (by simp [supportWires,
                ClassicalReversibleInstruction.supportWires])]
          · simp [xorWire, isTarget, agree wire supported]
  | seq first second firstHypothesis secondHypothesis =>
      have intermediateAgree : ∀ candidate,
          candidate ∈ second.supportWires →
          first.reference left candidate = first.reference right candidate := by
        intro candidate candidateSecond
        by_cases candidateFirst : candidate ∈ first.supportWires
        · exact firstHypothesis left right
            (fun supportWire supportMember =>
              agree supportWire (Finset.mem_union_left _ supportMember))
            candidate candidateFirst
        · rw [reference_apply_of_not_mem_support first left candidate
              candidateFirst,
            reference_apply_of_not_mem_support first right candidate
              candidateFirst]
          exact agree candidate (Finset.mem_union_right _ candidateSecond)
      change second.reference (first.reference left) wire =
        second.reference (first.reference right) wire
      by_cases wireSecond : wire ∈ second.supportWires
      · exact secondHypothesis _ _ intermediateAgree wire wireSecond
      · rw [reference_apply_of_not_mem_support second
            (first.reference left) wire wireSecond,
          reference_apply_of_not_mem_support second
            (first.reference right) wire wireSecond]
        have wireFirst : wire ∈ first.supportWires := by
          rcases Finset.mem_union.mp supported with wireFirst | contradiction
          · exact wireFirst
          · exact False.elim (wireSecond contradiction)
        exact firstHypothesis left right
          (fun supportWire supportMember =>
            agree supportWire (Finset.mem_union_left _ supportMember))
          wire wireFirst
  | «repeat» count body bodyHypothesis =>
      have bodySupported : wire ∈ body.supportWires := by
        simpa [supportWires] using supported
      have bodyAgree : ∀ candidate, candidate ∈ body.supportWires →
          left candidate = right candidate := by
        intro candidate member
        exact agree candidate (by simpa [supportWires] using member)
      change (body.reference ^ count) left wire =
        (body.reference ^ count) right wire
      have powerCongruent : ∀ repetitions
          (firstInput secondInput : QubitBasis qubits),
          (∀ candidate, candidate ∈ body.supportWires →
            firstInput candidate = secondInput candidate) →
          ∀ output, output ∈ body.supportWires →
            (body.reference ^ repetitions) firstInput output =
              (body.reference ^ repetitions) secondInput output := by
        intro repetitions
        induction repetitions with
        | zero =>
            intro firstInput secondInput inputsAgree output outputSupported
            exact inputsAgree output outputSupported
        | succ repetitions inductionHypothesis =>
            intro firstInput secondInput inputsAgree output outputSupported
            rw [pow_succ]
            change (body.reference ^ repetitions)
                (body.reference firstInput) output =
              (body.reference ^ repetitions)
                (body.reference secondInput) output
            apply inductionHypothesis
            · intro candidate candidateSupported
              exact bodyHypothesis firstInput secondInput inputsAgree candidate
                candidateSupported
            · exact outputSupported
      exact powerCongruent count left right bodyAgree wire bodySupported

/-- If two inputs agree on a stage's support and at the observed wire, then
the stage produces the same value at that wire. -/
theorem reference_apply_congr_of_eq_on_support {qubits : Nat}
    (stage : ClassicalReversibleStage qubits)
    (left right : QubitBasis qubits)
    (agreeSupport : ∀ supportWire, supportWire ∈ stage.supportWires →
      left supportWire = right supportWire)
    (wire : Fin qubits) (agreeWire : left wire = right wire) :
    stage.reference left wire = stage.reference right wire := by
  by_cases supported : wire ∈ stage.supportWires
  · exact reference_apply_congr_of_eq_on_support_of_mem stage left right
      agreeSupport wire supported
  · rw [reference_apply_of_not_mem_support stage left wire supported,
      reference_apply_of_not_mem_support stage right wire supported,
      agreeWire]

/-- stage列を左から右へ実行する二項木へまとめる。 -/
def sequence {qubits : Nat} :
    List (ClassicalReversibleStage qubits) → ClassicalReversibleStage qubits
  | [] => .identity
  | first :: rest => .seq first (sequence rest)

/-- A classical stage list acts by left-to-right folding of its independent
references. -/
theorem sequence_reference_apply {qubits : Nat}
    (stages : List (ClassicalReversibleStage qubits))
    (input : QubitBasis qubits) :
    (sequence stages).reference input =
      stages.foldl (fun state stage => stage.reference state) input := by
  induction stages generalizing input with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      change (sequence rest).reference (first.reference input) = _
      exact inductionHypothesis (first.reference input)

/-- compute--use--reverse-computeを一つのstageへまとめる。 -/
def computeUseUncompute {qubits : Nat}
    (compute use : ClassicalReversibleStage qubits) :
    ClassicalReversibleStage qubits :=
  .seq compute (.seq use compute.reverse)

/-- stage全体の独立な置換行列作用素。 -/
def analyticOperator {qubits : Nat}
    (stage : ClassicalReversibleStage qubits) : Operator (QubitBasis qubits) :=
  stage.reference⁻¹.permMatrix ℂ

/--
The stage operator is the deterministic operator of its forward basis action.

The inverse on `permMatrix` is essential: `p.permMatrix` acts on a basis ket by
`p⁻¹`, so `(stage.reference⁻¹).permMatrix` acts by `stage.reference`.
-/
theorem analyticOperator_eq_deterministicReference {qubits : Nat}
    (stage : ClassicalReversibleStage qubits) :
    stage.analyticOperator = deterministicOperator stage.reference := by
  ext output input
  have equivalence : stage.reference.symm output = input ↔
      output = stage.reference input := by
    constructor
    · intro equal
      have mapped := congrArg stage.reference equal
      simpa using mapped
    · intro equal
      have mapped := congrArg stage.reference.symm equal
      simpa using mapped
  simp [analyticOperator, deterministicOperator, equivalence]

/-- The independent stage operator changes only wires in the syntactic stage
support. -/
theorem analyticOperator_preservesOutside {qubits : Nat}
    (stage : ClassicalReversibleStage qubits) :
    OperatorPreservesOutside stage.supportWires stage.analyticOperator := by
  rw [analyticOperator_eq_deterministicReference]
  apply OperatorPreservesOutside.deterministicOperator
  intro input wire outside
  exact reference_apply_of_not_mem_support stage input wire outside

/-- Sequential classical stages compose their independent analytic operators
in execution order. -/
theorem analyticOperator_seq {qubits : Nat}
    (first second : ClassicalReversibleStage qubits) :
    (ClassicalReversibleStage.seq first second).analyticOperator =
      second.analyticOperator * first.analyticOperator := by
  simp only [analyticOperator, reference, mul_inv_rev]
  rw [Matrix.permMatrix_mul]

/-- A source-order list of classical stages has the corresponding
`operatorSequence` analytic target. -/
theorem analyticOperator_sequence {qubits : Nat}
    (stages : List (ClassicalReversibleStage qubits)) :
    (ClassicalReversibleStage.sequence stages).analyticOperator =
      operatorSequence (stages.map analyticOperator) := by
  induction stages with
  | nil => simp [sequence, analyticOperator, reference, operatorSequence]
  | cons first rest inductionHypothesis =>
      simp [sequence, analyticOperator_seq, operatorSequence,
        inductionHypothesis]

/-- wireが異なるときだけcontrolled XOR命令を追加する。 -/
def safeXorControlled {qubits : Nat} (control target : Fin qubits) :
    ClassicalReversibleStage qubits :=
  if different : control ≠ target then
    .instruction (.xorControlled control target different)
  else .identity

/-- Collision-safe raw register XOR copy.  Source and target lists are paired
from left to right and execution stops when either list ends.  A pair whose
source and target wires coincide contributes the identity stage. -/
def rawXorCopy {qubits : Nat} :
    List (Fin qubits) → List (Fin qubits) → ClassicalReversibleStage qubits
  | source :: sources, target :: targets =>
      .seq (safeXorControlled source target) (rawXorCopy sources targets)
  | _, _ => .identity

/-- A raw collision-safe XOR copy preserves every wire outside its (possibly
truncated) target list.  No disjointness, distinctness, or equal-length
assumption is required. -/
theorem rawXorCopy_reference_apply_outside_target {qubits : Nat}
    (sources targets : List (Fin qubits)) (input : QubitBasis qubits)
    (wire : Fin qubits) (outside : wire ∉ targets) :
    (rawXorCopy sources targets).reference input wire = input wire := by
  induction sources generalizing targets input with
  | nil => rfl
  | cons source sources inductionHypothesis =>
      cases targets with
      | nil => rfl
      | cons target targets =>
          have wire_ne_target : wire ≠ target := by
            intro equal
            subst wire
            exact outside (by simp)
          have outsideTargets : wire ∉ targets := by
            intro member
            exact outside (by simp [member])
          change (rawXorCopy sources targets).reference
              ((safeXorControlled source target).reference input) wire =
            input wire
          rw [inductionHypothesis targets
            ((safeXorControlled source target).reference input) outsideTargets]
          by_cases different : source ≠ target
          · simp [safeXorControlled, reference,
              ClassicalReversibleInstruction.reference,
              ClassicalReversibleInstruction.basisAction, xorWire,
              different, wire_ne_target]
          · simp [safeXorControlled, reference, different]

/-- 三wireが相異なるときだけdoubly-controlled XOR命令を追加する。 -/
def safeXorDoublyControlled {qubits : Nat}
    (control₁ control₂ target : Fin qubits) : ClassicalReversibleStage qubits :=
  if controlsDifferent : control₁ ≠ control₂ then
    if firstDifferent : control₁ ≠ target then
      if secondDifferent : control₂ ≠ target then
        .instruction (.xorDoublyControlled control₁ control₂ target
          controlsDifferent firstDifferent secondDifferent)
      else .identity
    else .identity
  else .identity

/-- Bool値0のcontrolから反転対象wireだけを取り出す。 -/
def zeroControlWires {qubits : Nat}
    (controls : List (Fin qubits × Bool)) : List (Fin qubits) :=
  controls.filterMap fun control => if control.2 then none else some control.1

/-- Bool値0のcontrolだけを前処理・後処理するX stage列。 -/
def invertZeroControls {qubits : Nat}
    (controls : List (Fin qubits × Bool)) : ClassicalReversibleStage qubits :=
  sequence <| (zeroControlWires controls).map fun wire =>
    .instruction (.xorOne wire)

/-- 途中まで計算したANDを延長し、使用後に逆計算する。 -/
def andChainUse {qubits : Nat} (previous : Fin qubits) :
    List (Fin qubits) → List (Fin qubits) → Fin qubits →
      ClassicalReversibleStage qubits
  | [], _, target => safeXorControlled previous target
  | control :: controls, scratch :: scratches, target =>
      let step := safeXorDoublyControlled previous control scratch
      .seq step (.seq (andChainUse scratch controls scratches target) step)
  | _ :: _, [], _ => .identity

/-- 全controlが1のときだけtargetを反転し、AND scratchを逆計算する。 -/
def positiveMultiControlledX {qubits : Nat} :
    List (Fin qubits) → List (Fin qubits) → Fin qubits →
      ClassicalReversibleStage qubits
  | [], _, target => .instruction (.xorOne target)
  | [control], _, target => safeXorControlled control target
  | control₁ :: control₂ :: controls, scratch :: scratches, target =>
      let first := safeXorDoublyControlled control₁ control₂ scratch
      .seq first (.seq (andChainUse scratch controls scratches target) first)
  | _ :: _ :: _, [], _ => .identity

/-- Minimum-work tail of a positive multi-controlled XOR.  The last
remaining control is reserved for the final Toffoli into the target, so a
tail of `n` controls uses only `n - 1` scratch wires. -/
def minimumWorkAndChainUse {qubits : Nat} (previous : Fin qubits) :
    List (Fin qubits) → List (Fin qubits) → Fin qubits →
      ClassicalReversibleStage qubits
  | [], _, target => safeXorControlled previous target
  | [last], _, target => safeXorDoublyControlled previous last target
  | control :: controls, scratch :: scratches, target =>
      let step := safeXorDoublyControlled previous control scratch
      .seq step
        (.seq (minimumWorkAndChainUse scratch controls scratches target) step)
  | _ :: _ :: _, [], _ => .identity

/-- Source-faithful minimum-work positive multi-controlled XOR.  For `n ≥ 2`
controls it uses `n - 2` clean scratch wires: all but the last control are
folded into the scratch chain, the last control participates directly in the
target Toffoli, and the chain is uncomputed. -/
def minimumWorkPositiveMultiControlledX {qubits : Nat} :
    List (Fin qubits) → List (Fin qubits) → Fin qubits →
      ClassicalReversibleStage qubits
  | [], _, target => .instruction (.xorOne target)
  | [control], _, target => safeXorControlled control target
  | [first, second], _, target =>
      safeXorDoublyControlled first second target
  | first :: second :: controls, scratch :: scratches, target =>
      let step := safeXorDoublyControlled first second scratch
      .seq step
        (.seq (minimumWorkAndChainUse scratch controls scratches target) step)
  | _ :: _ :: _ :: _, [], _ => .identity

/-- 0-control前後反転を含むBool値付き多重制御X。 -/
def boolMultiControlledX {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (scratch : List (Fin qubits))
    (target : Fin qubits) : ClassicalReversibleStage qubits :=
  let invert := invertZeroControls controls
  .seq invert (.seq
    (positiveMultiControlledX (controls.map Prod.fst) scratch target) invert)

/-- Minimum-work Boolean multi-controlled XOR.  Zero-controls are prepared
and restored exactly as in `boolMultiControlledX`, while the positive-control
body reserves the last control for the target Toffoli.  In particular, two
Boolean controls require no scratch wire. -/
def boolMultiControlledXMinimumWork {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (scratch : List (Fin qubits))
    (target : Fin qubits) : ClassicalReversibleStage qubits :=
  let invert := invertZeroControls controls
  .seq invert (.seq
    (minimumWorkPositiveMultiControlledX (controls.map Prod.fst) scratch target)
      invert)

/-- Source-order wire list selected by the one-bits of a fixed-width natural
constant.  Exposing this list keeps the mathematical mask independent of the
stage AST and makes truncation at `register.length` explicit. -/
def constantXorWires {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat) : List (Fin qubits) :=
  register.zipIdx.filterMap fun indexed =>
    if constant.testBit indexed.2 then some indexed.1 else none

/-- Every selected constant-mask wire comes from the declared register. -/
theorem constantXorWires_mem_register {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat) (wire : Fin qubits)
    (member : wire ∈ constantXorWires register constant) :
    wire ∈ register := by
  unfold constantXorWires at member
  rcases List.mem_filterMap.mp member with
    ⟨indexed, indexedMember, selected⟩
  split at selected
  · simp only [Option.some.injEq] at selected
    rw [← selected]
    exact List.fst_mem_of_mem_zipIdx indexedMember
  · contradiction

/-- Selecting positions from a duplicate-free register cannot introduce a
duplicate. -/
theorem constantXorWires_nodup {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat)
    (nodup : register.Nodup) :
    (constantXorWires register constant).Nodup := by
  unfold constantXorWires
  apply List.Pairwise.filterMap
    (R := fun left right : Fin qubits × Nat => left.1 ≠ right.1)
    (S := (· ≠ ·))
  · intro left right different leftWire leftSelected rightWire rightSelected equal
    apply different
    have leftEqual : left.1 = leftWire := by
      split at leftSelected <;> simp_all
    have rightEqual : right.1 = rightWire := by
      split at rightSelected <;> simp_all
    exact leftEqual.trans (equal.trans rightEqual.symm)
  · have mapped : (register.zipIdx.map Prod.fst).Nodup := by
      simpa using nodup
    exact List.pairwise_map.mp mapped

/-- Nat定数の1-bit位置だけを反転する。 -/
def xorConstant {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat) :
    ClassicalReversibleStage qubits :=
  sequence <| (constantXorWires register constant).map fun wire =>
    .instruction (.xorOne wire)

/-- The support of a source-ordered stage list is contained in any set that
contains every child support. -/
private theorem supportWires_sequence_subset_of_forall {qubits : Nat}
    (stages : List (ClassicalReversibleStage qubits))
    (support : Finset (Fin qubits))
    (inside : ∀ stage, stage ∈ stages → stage.supportWires ⊆ support) :
    (sequence stages).supportWires ⊆ support := by
  induction stages with
  | nil => simp [sequence, supportWires]
  | cons first rest inductionHypothesis =>
      intro wire member
      simp only [sequence, supportWires, Finset.mem_union] at member
      rcases member with firstMember | restMember
      · exact inside first (by simp) firstMember
      · exact inductionHypothesis (fun stage stageMember =>
          inside stage (by simp [stageMember])) restMember

/-- Every wire read or written by a constant-XOR stage belongs to the declared
register list.  Consumers can therefore establish disjointness without
unfolding `zipIdx`, filtering, or the recursive stage tree. -/
theorem xorConstant_supportWires_subset {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat) :
    (xorConstant register constant).supportWires ⊆ register.toFinset := by
  unfold xorConstant
  apply supportWires_sequence_subset_of_forall
  intro stage stageMember
  rcases List.mem_map.mp stageMember with ⟨selected, selectedMember, equal⟩
  subst stage
  intro wire member
  have wireEq : wire = selected := by
    simpa [supportWires, ClassicalReversibleInstruction.supportWires] using member
  subst wire
  exact List.mem_toFinset.mpr
    (constantXorWires_mem_register register constant selected selectedMember)

/-- 二bitの一致値を一つのflagへXORする三段stage。 -/
def computeBitEqual {qubits : Nat}
    (left right flag : Fin qubits) : ClassicalReversibleStage qubits :=
  .seq (safeXorControlled left flag)
    (.seq (safeXorControlled right flag) (.instruction (.xorOne flag)))

/-- 各bitの一致flagを順に計算する。 -/
def computeEqualityFlags {qubits : Nat}
    (left right flags : List (Fin qubits)) : ClassicalReversibleStage qubits :=
  sequence <| (left.zip (right.zip flags)).map fun entry =>
    computeBitEqual entry.1 entry.2.1 entry.2.2

/-- Boolean control rows for the equality-branch implementation of unsigned
little-endian comparison.  Row `i` checks `left[i] = 0`, `right[i] = 1`, and
that every more-significant equality flag is true.  This is deliberately a
separate implementation family from the ripple-borrow comparator. -/
def equalityBranchLessThanControlProgram {qubits : Nat} :
    List (Fin qubits) -> List (Fin qubits) -> List (Fin qubits) ->
      List (List (Fin qubits × Bool))
  | leftBit :: left, rightBit :: right, equalFlags =>
      let higherEqual := (equalFlags.drop 1).map fun wire => (wire, true)
      ((leftBit, false) :: (rightBit, true) :: higherEqual) ::
        equalityBranchLessThanControlProgram left right (equalFlags.drop 1)
  | _, _, _ => []

/-- Apply a source-ordered list of Boolean multi-controlled target XORs. -/
def boolControlledXProgram {qubits : Nat}
    (program : List (List (Fin qubits × Bool)))
    (scratch : List (Fin qubits)) (target : Fin qubits) :
    ClassicalReversibleStage qubits :=
  sequence <| program.map fun controls =>
    boolMultiControlledX controls scratch target

/-- Equality-branch implementation of `target ^= (left < right)` for
little-endian unsigned words.  Equality flags are computed, the mutually
exclusive comparison branches are applied in source order, and the flags are
uncomputed.  The family name distinguishes this AST from ripple-borrow
unsigned comparison. -/
def equalityBranchUnsignedLessThanStage {qubits : Nat}
    (left right equalFlags scratch : List (Fin qubits))
    (target : Fin qubits) : ClassicalReversibleStage qubits :=
  let compute := computeEqualityFlags left right equalFlags
  let use := boolControlledXProgram
    (equalityBranchLessThanControlProgram left right equalFlags)
    scratch target
  computeUseUncompute compute use

/-- 二wordが等しいときだけtargetをXORし、一致flagを逆計算する。 -/
def xorEqualityIntoTarget {qubits : Nat}
    (left right flags scratch : List (Fin qubits)) (target : Fin qubits) :
    ClassicalReversibleStage qubits :=
  let compute := computeEqualityFlags left right flags
  computeUseUncompute compute (positiveMultiControlledX flags scratch target)

/-- Register bits paired with the corresponding bits of a natural-number
constant, in little-endian order. -/
def equalityToConstantControls {qubits : Nat}
    (register : List (Fin qubits)) (constant : Nat) :
    List (Fin qubits × Bool) :=
  register.zipIdx.map fun indexed =>
    (indexed.1, constant.testBit indexed.2)

/-- XOR the target exactly when the little-endian register equals a constant.
The multi-control scratch is computed and uncomputed by the underlying stage. -/
def xorEqualityToConstantIntoTarget {qubits : Nat}
    (register scratch : List (Fin qubits)) (constant : Nat)
    (target : Fin qubits) : ClassicalReversibleStage qubits :=
  boolMultiControlledX (equalityToConstantControls register constant)
    scratch target

/-- Source-faithful minimum-work equality-to-constant XOR.  A width-`n`
register uses at most `n - 2` clean scratch wires; width two is compiled to
zero-control preparation, one Toffoli, and zero-control restoration. -/
def xorEqualityToConstantIntoTargetMinimumWork {qubits : Nat}
    (register scratch : List (Fin qubits)) (constant : Nat)
    (target : Fin qubits) : ClassicalReversibleStage qubits :=
  boolMultiControlledXMinimumWork
    (equalityToConstantControls register constant) scratch target

/-- XOR the conjunction of all positive controls into the target while
preserving the controls and uncomputing the AND-chain scratch. -/
def xorConjunctionIntoTarget {qubits : Nat}
    (controls scratch : List (Fin qubits)) (target : Fin qubits) :
    ClassicalReversibleStage qubits :=
  positiveMultiControlledX controls scratch target

/-- Source-faithful minimum-work conjunction XOR.  For two controls this is
the direct Toffoli and therefore requires no scratch wire; in general it uses
only `controls.length - 2` clean scratch wires. -/
def xorConjunctionIntoTargetMinimumWork {qubits : Nat}
    (controls scratch : List (Fin qubits)) (target : Fin qubits) :
    ClassicalReversibleStage qubits :=
  minimumWorkPositiveMultiControlledX controls scratch target

/-- 上位側からcarry条件を順に作用させるincrement stage。 -/
def incrementCarrySequence {qubits : Nat} :
    List (Fin qubits) → List (Fin qubits) → List (Fin qubits) →
      ClassicalReversibleStage qubits
  | _, [], _ => .identity
  | lower, target :: higher, scratch =>
      .seq (incrementCarrySequence (lower ++ [target]) higher scratch)
        (positiveMultiControlledX lower scratch target)

/-- little-endian wordの全dirty周期increment stage。 -/
def incrementWordMod2PowInPlace {qubits : Nat}
    (word scratch : List (Fin qubits)) : ClassicalReversibleStage qubits :=
  incrementCarrySequence [] word scratch

/-- Controlled carry sequence: each target bit is toggled exactly when the
external control and all lower word bits are true. -/
def controlledIncrementCarrySequence {qubits : Nat}
    (control : Fin qubits) :
    List (Fin qubits) → List (Fin qubits) → List (Fin qubits) →
      ClassicalReversibleStage qubits
  | _, [], _ => .identity
  | lower, target :: higher, scratch =>
      .seq (controlledIncrementCarrySequence control
        (lower ++ [target]) higher scratch)
        (positiveMultiControlledX (control :: lower) scratch target)

/-- Increment a little-endian word modulo `2^width` iff `control` is true,
with every multi-control scratch chain uncomputed. -/
def controlledIncrementWordMod2PowInPlace {qubits : Nat}
    (control : Fin qubits) (word scratch : List (Fin qubits)) :
    ClassicalReversibleStage qubits :=
  controlledIncrementCarrySequence control [] word scratch

/-- 上位側からborrow条件を順に作用させるdecrement stage。 -/
def decrementBorrowSequence {qubits : Nat} :
    List (Fin qubits) → List (Fin qubits) → List (Fin qubits) →
      ClassicalReversibleStage qubits
  | _, [], _ => .identity
  | lower, target :: higher, scratch =>
      .seq (decrementBorrowSequence (lower ++ [target]) higher scratch)
        (boolMultiControlledX (lower.map fun wire => (wire, false)) scratch target)

/-- little-endian wordの全dirty周期decrement stage。 -/
def decrementWordMod2PowInPlace {qubits : Nat}
    (word scratch : List (Fin qubits)) : ClassicalReversibleStage qubits :=
  decrementBorrowSequence [] word scratch

end ClassicalReversibleStage

end

end VerifiedCircuitCore
