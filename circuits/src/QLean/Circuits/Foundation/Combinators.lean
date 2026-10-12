import QLean.Circuits.Foundation.Contracts
import QLean.Circuits.Foundation.Metrics
import QLean.Circuits.Foundation.OperatorLocality

/-!
# componentの一般合成則

二項seq、reverse、repeat、gate/wire写像、control、C-U-U、状態準備後の作用、
および抽象誤差modelによる加法的誤差合成を提供する。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- gate compilerと作用素のモノイド準同型が葉で可換なら、全回路でも可換する。 -/
theorem Circuit.denote_mapGates_monoidHom
    {Gate MappedGate basis mappedBasis : Type*}
    [Fintype basis] [DecidableEq basis]
    [Fintype mappedBasis] [DecidableEq mappedBasis]
    (gateOperator : Gate → Operator basis)
    (mappedOperator : MappedGate → Operator mappedBasis)
    (mapGate : Gate → MappedGate)
    (operatorLift : Operator basis →* Operator mappedBasis)
    (gateCorrect : ∀ gate,
      mappedOperator (mapGate gate) = operatorLift (gateOperator gate)) :
    ∀ circuit : Circuit Gate,
      Circuit.denote mappedOperator (circuit.mapGates mapGate) =
        operatorLift (Circuit.denote gateOperator circuit)
  | .identity => by simp [Circuit.mapGates, Circuit.denote]
  | .gate value => gateCorrect value
  | .seq first second => by
      simp only [Circuit.mapGates, Circuit.denote_seq,
        Circuit.denote_mapGates_monoidHom gateOperator mappedOperator mapGate
          operatorLift gateCorrect first,
        Circuit.denote_mapGates_monoidHom gateOperator mappedOperator mapGate
          operatorLift gateCorrect second, map_mul]
  | .repeat count body => by
      simp only [Circuit.mapGates, Circuit.denote_repeat,
        Circuit.denote_mapGates_monoidHom gateOperator mappedOperator mapGate
          operatorLift gateCorrect body, map_pow]

/--
実際に回路へ現れるsource葉だけでcompiler正しさを要求し、回路compiler全体の
作用素liftを導く。未使用のsource gate constructorに意味保存を要求しない。
-/
theorem Circuit.denote_compileGates_monoidHom_of_mem
    {Gate MappedGate basis mappedBasis : Type*}
    [Fintype basis] [DecidableEq basis]
    [Fintype mappedBasis] [DecidableEq mappedBasis]
    (gateOperator : Gate → Operator basis)
    (mappedOperator : MappedGate → Operator mappedBasis)
    (compileGate : Gate → Circuit MappedGate)
    (operatorLift : Operator basis →* Operator mappedBasis) :
    ∀ circuit : Circuit Gate,
      (∀ gate, gate ∈ circuit.flatten →
        Circuit.denote mappedOperator (compileGate gate) =
          operatorLift (gateOperator gate)) →
      Circuit.denote mappedOperator (circuit.compileGates compileGate) =
        operatorLift (Circuit.denote gateOperator circuit)
  | .identity, _ => by simp [Circuit.compileGates, Circuit.denote]
  | .gate value, correct => correct value (by simp [Circuit.flatten])
  | .seq first second, correct => by
      have firstCorrect := Circuit.denote_compileGates_monoidHom_of_mem
        gateOperator mappedOperator compileGate operatorLift first
        (fun gate member => correct gate (by
          simp [Circuit.flatten, member]))
      have secondCorrect := Circuit.denote_compileGates_monoidHom_of_mem
        gateOperator mappedOperator compileGate operatorLift second
        (fun gate member => correct gate (by
          simp [Circuit.flatten, member]))
      simp [Circuit.compileGates, Circuit.denote, firstCorrect, secondCorrect,
        map_mul]
  | .repeat 0 body, _ => by
      simp [Circuit.compileGates, Circuit.denote]
  | .repeat (count + 1) body, correct => by
      have bodyCorrect := Circuit.denote_compileGates_monoidHom_of_mem
        gateOperator mappedOperator compileGate operatorLift body
        (fun gate member => correct gate (by
          simp [Circuit.flatten, member]))
      simp [Circuit.compileGates, Circuit.denote, bodyCorrect, map_pow]

namespace ExactOperatorComponent

/-- 何もしない回路を恒等作用素へ結ぶ。 -/
def identity
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) : ExactOperatorComponent gateOperator where
  circuit := .identity
  target := 1
  correct := rfl

/-- A single gate as an exact operator component. -/
def ofGate
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) (gate : Gate) :
    ExactOperatorComponent gateOperator where
  circuit := .gate gate
  target := gateOperator gate
  correct := rfl

@[simp] theorem ofGate_circuit
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) (gate : Gate) :
    (ofGate gateOperator gate).circuit = .gate gate := rfl

@[simp] theorem ofGate_target
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) (gate : Gate) :
    (ofGate gateOperator gate).target = gateOperator gate := rfl

/-- Repackage an exact component under a propositionally equal independent
target.  The circuit is retained definitionally, while the target transport is
checked once inside this constructor. -/
def refineTarget
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (child : ExactOperatorComponent gateOperator)
    (target : Operator basis) (targetEq : child.target = target) :
    ExactOperatorComponent gateOperator where
  circuit := child.circuit
  target := target
  correct := child.correct.trans targetEq

/-- The target-refinement constructor preserves the child circuit.  Consumers
can use this opaque projection theorem without unfolding a large child family. -/
@[simp] theorem refineTarget_circuit
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (child : ExactOperatorComponent gateOperator)
    (target : Operator basis) (targetEq : child.target = target) :
    (refineTarget child target targetEq).circuit = child.circuit := rfl

/-- The public target of target refinement is exactly the requested target. -/
@[simp] theorem refineTarget_target
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (child : ExactOperatorComponent gateOperator)
    (target : Operator basis) (targetEq : child.target = target) :
    (refineTarget child target targetEq).target = target := rfl

/-- Correctness of target refinement is available as a named opaque theorem. -/
theorem refineTarget_correct
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (child : ExactOperatorComponent gateOperator)
    (target : Operator basis) (targetEq : child.target = target) :
    (refineTarget child target targetEq).circuit.denote gateOperator = target :=
  (refineTarget child target targetEq).correct

/-- 二つの厳密作用素componentを実行順に逐次合成する。 -/
def seq
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (first second : ExactOperatorComponent gateOperator) :
    ExactOperatorComponent gateOperator where
  circuit := .seq first.circuit second.circuit
  target := second.target * first.target
  correct := by rw [Circuit.denote_seq, first.correct, second.correct]

/-- 厳密作用素componentを指定回数反復する。 -/
def «repeat»
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (count : Nat) (component : ExactOperatorComponent gateOperator) :
    ExactOperatorComponent gateOperator where
  circuit := .repeat count component.circuit
  target := component.target ^ count
  correct := by rw [Circuit.denote_repeat, component.correct]

/-- 厳密作用素componentの有限列を実行順にfold合成する。 -/
def sequence
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (components : List (ExactOperatorComponent gateOperator)) :
    ExactOperatorComponent gateOperator :=
  match components with
  | [] => identity gateOperator
  | first :: rest => seq first (sequence rest)

/-- The target of component-level sequencing is the execution-order operator
product of the public child targets. -/
theorem sequence_target_eq_operatorSequence
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (components : List (ExactOperatorComponent gateOperator)) :
    (sequence components).target =
      operatorSequence (components.map ExactOperatorComponent.target) := by
  induction components with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [sequence, seq, List.map_cons, operatorSequence]
      simpa [ExactOperatorComponent.seq] using
        congrArg (fun operator => operator * first.target) inductionHypothesis

/-- gate意味論を保存する写像で厳密componentを別gate型へ移す。 -/
def mapGates
    {Gate MappedGate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {mappedOperator : MappedGate → Operator basis}
    (mapGate : Gate → MappedGate)
    (mapCorrect : ∀ gate, mappedOperator (mapGate gate) = gateOperator gate)
    (component : ExactOperatorComponent gateOperator) :
    ExactOperatorComponent mappedOperator where
  circuit := component.circuit.mapGates mapGate
  target := component.target
  correct := calc
    Circuit.denote mappedOperator (component.circuit.mapGates mapGate) =
        Circuit.denote (mappedOperator ∘ mapGate) component.circuit :=
      Circuit.denote_mapGates mappedOperator mapGate component.circuit
    _ = Circuit.denote gateOperator component.circuit :=
      Circuit.denote_congr (fun value => mapCorrect value) component.circuit
    _ = component.target := component.correct

/--
gate compilerと作用素のモノイド準同型から、基底型を変える厳密component liftを作る。
-/
def liftByCompiler
    {Gate MappedGate basis mappedBasis : Type*}
    [Fintype basis] [DecidableEq basis]
    [Fintype mappedBasis] [DecidableEq mappedBasis]
    (gateOperator : Gate → Operator basis)
    (mappedOperator : MappedGate → Operator mappedBasis)
    (mapGate : Gate → MappedGate)
    (operatorLift : Operator basis →* Operator mappedBasis)
    (gateCorrect : ∀ gate,
      mappedOperator (mapGate gate) = operatorLift (gateOperator gate))
    (component : ExactOperatorComponent gateOperator) :
    ExactOperatorComponent mappedOperator where
  circuit := component.circuit.mapGates mapGate
  target := operatorLift component.target
  correct := by
    rw [Circuit.denote_mapGates_monoidHom gateOperator mappedOperator mapGate
      operatorLift gateCorrect component.circuit, component.correct]

/--
Expand each source leaf to a target circuit while transporting an Exact
component through an operator monoid homomorphism.  Correctness is required
only for source leaves that actually occur in the component AST.
-/
def liftByCircuitCompiler
    {Gate MappedGate basis mappedBasis : Type*}
    [Fintype basis] [DecidableEq basis]
    [Fintype mappedBasis] [DecidableEq mappedBasis]
    (gateOperator : Gate → Operator basis)
    (mappedOperator : MappedGate → Operator mappedBasis)
    (compileGate : Gate → Circuit MappedGate)
    (operatorLift : Operator basis →* Operator mappedBasis)
    (component : ExactOperatorComponent gateOperator)
    (gateCorrect : ∀ gate, gate ∈ component.circuit.flatten →
      Circuit.denote mappedOperator (compileGate gate) =
        operatorLift (gateOperator gate)) :
    ExactOperatorComponent mappedOperator where
  circuit := component.circuit.compileGates compileGate
  target := operatorLift component.target
  correct := by
    rw [Circuit.denote_compileGates_monoidHom_of_mem gateOperator mappedOperator
      compileGate operatorLift component.circuit gateCorrect]
    rw [component.correct]

/-- `repeat`のconsumer向け明示名。 -/
abbrev repeatComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (count : Nat) (component : ExactOperatorComponent gateOperator) :=
  ExactOperatorComponent.repeat count component

/-- `sequence`のconsumer向け明示名。 -/
abbrev sequenceComponents
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (components : List (ExactOperatorComponent gateOperator)) :=
  ExactOperatorComponent.sequence components

/-- The implementation circuit of an exact component sequence is the
corresponding syntactic circuit sequence. -/
theorem sequenceComponents_circuit
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (components : List (ExactOperatorComponent gateOperator)) :
    (sequenceComponents gateOperator components).circuit =
      Circuit.sequence (components.map fun component => component.circuit) := by
  induction components with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp [sequenceComponents, sequence, seq, Circuit.sequence,
        inductionHypothesis]

/-- Reconstruct the correctness of an Exact component sequence exclusively
from the public correctness contracts of the components occurring in the
sequence.  This is the proof edge used by application catalog certificates;
it does not inspect the proof field stored in the assembled parent. -/
theorem sequence_correctness_of_children
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (components : List (ExactOperatorComponent gateOperator))
    (eachCorrect : ∀ component, component ∈ components →
      Circuit.denote gateOperator component.circuit = component.target) :
    Circuit.denote gateOperator
        (ExactOperatorComponent.sequence components).circuit =
      (ExactOperatorComponent.sequence components).target := by
  induction components with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      have firstCorrect := eachCorrect first (by simp)
      have restCorrect := inductionHypothesis (fun component member =>
        eachCorrect component (by simp [member]))
      change Circuit.denote gateOperator
          (.seq first.circuit
            (ExactOperatorComponent.sequence rest).circuit) =
        (ExactOperatorComponent.sequence rest).target * first.target
      rw [Circuit.denote_seq, firstCorrect, restCorrect]

/-- 各逆gateが共役転置を表すとき、componentを構文的に逆実行する。 -/
def reverse
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (inverseGate : Gate → Gate)
    (inverseCorrect : ∀ gate,
      gateOperator (inverseGate gate) = Matrix.conjTranspose (gateOperator gate))
    (component : ExactOperatorComponent gateOperator) :
    ExactOperatorComponent gateOperator where
  circuit := component.circuit.reverse inverseGate
  target := Matrix.conjTranspose component.target
  correct := by rw [Circuit.denote_reverse inverseGate gateOperator inverseCorrect,
    component.correct]

/-- 制御意味論を満たすgate compilerで厳密componentを制御化する。 -/
def control
    {Gate ControlledGate Control basis : Type*}
    [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {controlledGateOperator : ControlledGate → Operator basis}
    (controlGate : Control → Gate → ControlledGate)
    (controlOperator : Control → Operator basis → Operator basis)
    (laws : Circuit.ControlSemantics gateOperator controlledGateOperator
      controlGate controlOperator)
    (controlValue : Control) (component : ExactOperatorComponent gateOperator) :
    ExactOperatorComponent controlledGateOperator where
  circuit := component.circuit.control controlGate controlValue
  target := controlOperator controlValue component.target
  correct := by
    rw [Circuit.denote_control gateOperator controlledGateOperator controlGate
      controlOperator laws controlValue component.circuit]
    rw [component.correct]

/-- compute、use、compute逆を三つの公開component契約だけから合成する。 -/
def computeUseUncompute
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (inverseGate : Gate → Gate)
    (inverseCorrect : ∀ gate,
      gateOperator (inverseGate gate) = Matrix.conjTranspose (gateOperator gate))
    (compute use : ExactOperatorComponent gateOperator) :
    ExactOperatorComponent gateOperator :=
  seq compute (seq use (reverse inverseGate inverseCorrect compute))

end ExactOperatorComponent

namespace UnitaryExactOperatorComponent

/-- 恒等回路をユニタリ恒等作用素へ結ぶ。 -/
def identity
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) :
    UnitaryExactOperatorComponent gateOperator where
  toExactOperatorComponent := ExactOperatorComponent.identity gateOperator
  target_unitary := Submonoid.one_mem _

/-- 二つのユニタリ厳密componentを実行順に逐次合成する。 -/
def seq
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (first second : UnitaryExactOperatorComponent gateOperator) :
    UnitaryExactOperatorComponent gateOperator where
  toExactOperatorComponent := ExactOperatorComponent.seq first.toExact second.toExact
  target_unitary := Submonoid.mul_mem _ second.target_unitary first.target_unitary

/-- ユニタリ厳密componentを指定回数反復する。 -/
def «repeat»
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (count : Nat) (component : UnitaryExactOperatorComponent gateOperator) :
    UnitaryExactOperatorComponent gateOperator where
  toExactOperatorComponent := ExactOperatorComponent.repeat count component.toExact
  target_unitary := Submonoid.pow_mem _ component.target_unitary count

/-- ユニタリ厳密component列を公開子契約だけからfold合成する。 -/
def sequence
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (components : List (UnitaryExactOperatorComponent gateOperator)) :
    UnitaryExactOperatorComponent gateOperator :=
  match components with
  | [] => identity gateOperator
  | first :: rest => seq first (sequence rest)

/-- sequence targetは公開子targetの実行順積である。 -/
theorem sequence_target_eq_operatorSequence
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (components : List (UnitaryExactOperatorComponent gateOperator)) :
    (sequence components).target =
      operatorSequence (components.map fun component => component.target) := by
  induction components with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [sequence, seq, List.map_cons, operatorSequence]
      change (sequence rest).target * first.target =
        operatorSequence (rest.map fun component => component.target) * first.target
      exact congrArg (fun operator => operator * first.target) inductionHypothesis

/-- gate意味論を保存する写像でユニタリ厳密componentを別gate型へ移す。 -/
def mapGates
    {Gate MappedGate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {mappedOperator : MappedGate → Operator basis}
    (mapGate : Gate → MappedGate)
    (mapCorrect : ∀ gate, mappedOperator (mapGate gate) = gateOperator gate)
    (component : UnitaryExactOperatorComponent gateOperator) :
    UnitaryExactOperatorComponent mappedOperator where
  toExactOperatorComponent :=
    ExactOperatorComponent.mapGates mapGate mapCorrect component.toExact
  target_unitary := component.target_unitary

/--
Circuit-valued leaf compiler variant of `liftByCompiler`.  A separate proof
states that the operator lift preserves unitarity.
-/
def liftByCircuitCompiler
    {Gate MappedGate basis mappedBasis : Type*}
    [Fintype basis] [DecidableEq basis]
    [Fintype mappedBasis] [DecidableEq mappedBasis]
    (gateOperator : Gate → Operator basis)
    (mappedOperator : MappedGate → Operator mappedBasis)
    (compileGate : Gate → Circuit MappedGate)
    (operatorLift : Operator basis →* Operator mappedBasis)
    (unitaryPreserved : ∀ {operator : Operator basis},
      operator ∈ Matrix.unitaryGroup basis ℂ →
        operatorLift operator ∈ Matrix.unitaryGroup mappedBasis ℂ)
    (component : UnitaryExactOperatorComponent gateOperator)
    (gateCorrect : ∀ gate, gate ∈ component.circuit.flatten →
      Circuit.denote mappedOperator (compileGate gate) =
        operatorLift (gateOperator gate)) :
    UnitaryExactOperatorComponent mappedOperator where
  toExactOperatorComponent := ExactOperatorComponent.liftByCircuitCompiler
    gateOperator mappedOperator compileGate operatorLift component.toExact
    gateCorrect
  target_unitary := unitaryPreserved component.target_unitary

/--
作用素liftがユニタリ性を保存するとき、基底型を変えるcompiler liftもユニタリ契約を保つ。
-/
def liftByCompiler
    {Gate MappedGate basis mappedBasis : Type*}
    [Fintype basis] [DecidableEq basis]
    [Fintype mappedBasis] [DecidableEq mappedBasis]
    (gateOperator : Gate → Operator basis)
    (mappedOperator : MappedGate → Operator mappedBasis)
    (mapGate : Gate → MappedGate)
    (operatorLift : Operator basis →* Operator mappedBasis)
    (gateCorrect : ∀ gate,
      mappedOperator (mapGate gate) = operatorLift (gateOperator gate))
    (unitaryPreserved : ∀ {operator : Operator basis},
      operator ∈ Matrix.unitaryGroup basis ℂ →
        operatorLift operator ∈ Matrix.unitaryGroup mappedBasis ℂ)
    (component : UnitaryExactOperatorComponent gateOperator) :
    UnitaryExactOperatorComponent mappedOperator where
  toExactOperatorComponent := ExactOperatorComponent.liftByCompiler
    gateOperator mappedOperator mapGate operatorLift gateCorrect component.toExact
  target_unitary := unitaryPreserved component.target_unitary

/-- 各逆gateが共役転置を表すとき、ユニタリcomponentを逆実行する。 -/
def reverse
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (inverseGate : Gate → Gate)
    (inverseCorrect : ∀ gate,
      gateOperator (inverseGate gate) = Matrix.conjTranspose (gateOperator gate))
    (component : UnitaryExactOperatorComponent gateOperator) :
    UnitaryExactOperatorComponent gateOperator where
  toExactOperatorComponent :=
    ExactOperatorComponent.reverse inverseGate inverseCorrect component.toExact
  target_unitary := by
    change Matrix.conjTranspose component.target ∈ Matrix.unitaryGroup basis ℂ
    rw [Matrix.mem_unitaryGroup_iff]
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff').mp component.target_unitary

/-- 制御作用素constructorがユニタリ性を保存するとき、厳密componentを制御化する。 -/
def control
    {Gate ControlledGate Control basis : Type*}
    [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {controlledGateOperator : ControlledGate → Operator basis}
    (controlGate : Control → Gate → ControlledGate)
    (controlOperator : Control → Operator basis → Operator basis)
    (laws : Circuit.ControlSemantics gateOperator controlledGateOperator
      controlGate controlOperator)
    (controlUnitary : ∀ controlValue {operator : Operator basis},
      operator ∈ Matrix.unitaryGroup basis ℂ →
        controlOperator controlValue operator ∈ Matrix.unitaryGroup basis ℂ)
    (controlValue : Control)
    (component : UnitaryExactOperatorComponent gateOperator) :
    UnitaryExactOperatorComponent controlledGateOperator where
  toExactOperatorComponent := ExactOperatorComponent.control controlGate
    controlOperator laws controlValue component.toExact
  target_unitary := controlUnitary controlValue component.target_unitary

/-- compute、use、compute逆を三つの公開ユニタリ契約だけから合成する。 -/
def computeUseUncompute
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (inverseGate : Gate → Gate)
    (inverseCorrect : ∀ gate,
      gateOperator (inverseGate gate) = Matrix.conjTranspose (gateOperator gate))
    (compute use : UnitaryExactOperatorComponent gateOperator) :
    UnitaryExactOperatorComponent gateOperator :=
  seq compute (seq use (reverse inverseGate inverseCorrect compute))

/-- consumer向けの明示的な反復名。 -/
abbrev repeatComponent := @UnitaryExactOperatorComponent.repeat

/-- consumer向けの明示的な有限列名。 -/
abbrev sequenceComponents := @UnitaryExactOperatorComponent.sequence

end UnitaryExactOperatorComponent

namespace ExactOperatorComponent

/--
全primitive gateのユニタリ性から、厳密componentをユニタリ厳密componentへ昇格する。
targetのユニタリ性は回路全体を再展開せず、既存`correct`でtransportする。
-/
def toUnitary
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (gateUnitary : ∀ gate,
      gateOperator gate ∈ Matrix.unitaryGroup basis ℂ)
    (component : ExactOperatorComponent gateOperator) :
    UnitaryExactOperatorComponent gateOperator where
  toExactOperatorComponent := component
  target_unitary := by
    rw [← component.correct]
    exact Circuit.denote_mem_unitaryGroup gateOperator gateUnitary component.circuit

end ExactOperatorComponent

namespace PermutationComponent

/-- 恒等回路を恒等基底置換へ結ぶ。 -/
def identity
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (gatePermutation : Gate → Equiv.Perm basis) :
    PermutationComponent gateOperator gatePermutation where
  circuit := .identity
  reference := 1
  runBasis_correct := by intro input; rfl
  operator_correct := by simp [Circuit.denote]

/--
各葉の置換が自己逆で、gate作用素がその置換行列なら、基底作用証明から
全作用素契約を構成する。
-/
def ofInvolutiveCircuit
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (gatePermutation : Gate → Equiv.Perm basis)
    (gateInvolutive : ∀ gate,
      gatePermutation gate = (gatePermutation gate)⁻¹)
    (gateOperatorCorrect : ∀ gate,
      gateOperator gate = (gatePermutation gate).permMatrix ℂ)
    (circuit : Circuit Gate)
    (reference : Equiv.Perm basis)
    (runBasisCorrect : ∀ input,
      circuit.runBasis gatePermutation input = reference input) :
    PermutationComponent gateOperator gatePermutation where
  circuit := circuit
  reference := reference
  runBasis_correct := runBasisCorrect
  operator_correct := by
    have leafCorrect : ∀ gate,
        gateOperator gate = Circuit.permutationGateOperator gatePermutation gate := by
      intro gate
      rw [gateOperatorCorrect gate]
      exact congrArg (fun permutation => permutation.permMatrix ℂ)
        (gateInvolutive gate)
    have executionCorrect :
        circuit.toExecutionPermutation gatePermutation = reference := by
      ext input
      exact runBasisCorrect input
    rw [Circuit.denote_congr leafCorrect circuit,
      Circuit.denote_permutationGateOperator, executionCorrect]

/-- 置換componentを実行順に逐次合成する。 -/
def seq
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {gatePermutation : Gate → Equiv.Perm basis}
    (first second : PermutationComponent gateOperator gatePermutation) :
    PermutationComponent gateOperator gatePermutation where
  circuit := .seq first.circuit second.circuit
  reference := second.reference * first.reference
  runBasis_correct := by
    intro input
    change second.circuit.runBasis gatePermutation
      (first.circuit.runBasis gatePermutation input) = _
    rw [first.runBasis_correct, second.runBasis_correct]
    rfl
  operator_correct := by
    rw [Circuit.denote_seq, first.operator_correct, second.operator_correct]
    rw [mul_inv_rev, Matrix.permMatrix_mul]

/-- 逆gateが逆置換と共役転置を表すとき、置換componentを逆実行する。 -/
def reverse
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {gatePermutation : Gate → Equiv.Perm basis}
    (inverseGate : Gate → Gate)
    (inversePermutation : ∀ gate,
      gatePermutation (inverseGate gate) = (gatePermutation gate)⁻¹)
    (inverseOperator : ∀ gate,
      gateOperator (inverseGate gate) = Matrix.conjTranspose (gateOperator gate))
    (component : PermutationComponent gateOperator gatePermutation) :
    PermutationComponent gateOperator gatePermutation where
  circuit := component.circuit.reverse inverseGate
  reference := component.reference⁻¹
  runBasis_correct := by
    intro input
    rw [Circuit.runBasis]
    rw [Circuit.toExecutionPermutation_reverse inverseGate gatePermutation
      inversePermutation]
    rw [show component.circuit.toExecutionPermutation gatePermutation =
      component.reference by
        apply Equiv.ext
        intro value
        exact component.runBasis_correct value]
  operator_correct := by
    rw [Circuit.denote_reverse inverseGate gateOperator inverseOperator,
      component.operator_correct]
    simp

/-- 同一置換componentを指定回数だけ反復する。 -/
def «repeat»
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {gatePermutation : Gate → Equiv.Perm basis}
    (count : Nat) (component : PermutationComponent gateOperator gatePermutation) :
    PermutationComponent gateOperator gatePermutation where
  circuit := .repeat count component.circuit
  reference := component.reference ^ count
  runBasis_correct := by
    intro input
    change (component.circuit.toExecutionPermutation gatePermutation ^ count) input = _
    have equal : component.circuit.toExecutionPermutation gatePermutation =
        component.reference := by
      apply Equiv.ext
      intro value
      exact component.runBasis_correct value
    rw [equal]
  operator_correct := by
    rw [Circuit.denote_repeat, component.operator_correct]
    induction count with
    | zero => simp
    | succ count inductionHypothesis =>
        rw [pow_succ, pow_succ, inductionHypothesis]
        rw [← Matrix.permMatrix_mul]
        simp only [mul_inv_rev]

/-- 置換componentの有限列を実行順にfold合成する。 -/
def sequence
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {gatePermutation : Gate → Equiv.Perm basis}
    (components : List (PermutationComponent gateOperator gatePermutation)) :
    PermutationComponent gateOperator gatePermutation :=
  match components with
  | [] => identity gateOperator gatePermutation
  | first :: rest => seq first (sequence rest)

/-- `repeat`のconsumer向け、componentを先に取る明示名。 -/
abbrev repeatComponent
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {gatePermutation : Gate → Equiv.Perm basis}
    (component : PermutationComponent gateOperator gatePermutation)
    (count : Nat) := PermutationComponent.repeat count component

/-- `sequence`のconsumer向け明示名。 -/
abbrev sequenceComponents
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (gatePermutation : Gate → Equiv.Perm basis)
    (components : List (PermutationComponent gateOperator gatePermutation)) :=
  PermutationComponent.sequence components

end PermutationComponent

namespace CleanComponent

/-- 関数を実行順に指定回数反復した解析参照関数。 -/
def iterateReference {basis : Type*} (reference : basis → basis) : Nat → basis → basis
  | 0 => id
  | count + 1 => iterateReference reference count ∘ reference

/-- 各stepの復元関係を中間状態を介して連鎖した反復復元関係。 -/
def iteratedRestoration {basis : Type*} (restoration : basis → basis → Prop) :
    Nat → basis → basis → Prop
  | 0, input, output => output = input
  | count + 1, input, output =>
      ∃ middle, restoration input middle ∧
        iteratedRestoration restoration count middle output

/-- 恒等回路を、常に適用可能で全情報を保存するclean変換へ結ぶ。 -/
def identity
    {Gate basis : Type*} (gatePermutation : Gate → Equiv.Perm basis) :
    CleanComponent gatePermutation where
  circuit := .identity
  reference := id
  inputCondition := fun _ => True
  outputCondition := fun _ => True
  restoration := fun input output => output = input
  runBasis_correct := by intro input _; rfl
  outputCondition_correct := by simp
  restoration_correct := by simp

/--
中間条件を入力predicateへ明示的に保持する、二つのclean componentの逐次合成。
bridge型の`seq`と異なり、各子の入力条件を親の入力条件として記録する。
-/
def seqWithConditions
    {Gate basis : Type*}
    {gatePermutation : Gate → Equiv.Perm basis}
    (first second : CleanComponent gatePermutation) :
    CleanComponent gatePermutation where
  circuit := .seq first.circuit second.circuit
  reference := second.reference ∘ first.reference
  inputCondition := fun input =>
    first.inputCondition input ∧ second.inputCondition (first.reference input)
  outputCondition := second.outputCondition
  restoration := fun input output =>
    ∃ middle,
      middle = first.reference input ∧ first.restoration input middle ∧
        second.restoration middle output
  runBasis_correct := by
    intro input conditions
    change second.circuit.runBasis gatePermutation
      (first.circuit.runBasis gatePermutation input) = _
    rw [first.runBasis_correct input conditions.1]
    exact second.runBasis_correct _ conditions.2
  outputCondition_correct := by
    intro input conditions
    exact second.outputCondition_correct _ conditions.2
  restoration_correct := by
    intro input conditions
    exact ⟨first.reference input, rfl,
      first.restoration_correct input conditions.1,
      second.restoration_correct _ conditions.2⟩

/-- clean component列を、全中間入力条件を追跡しながら右fold合成する。 -/
def sequenceComponents
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis) :
    List (CleanComponent gatePermutation) → CleanComponent gatePermutation
  | [] => identity gatePermutation
  | first :: rest => seqWithConditions first
      (sequenceComponents gatePermutation rest)

/-- The implementation circuit of a clean component sequence is the
corresponding syntactic circuit sequence. -/
theorem sequenceComponents_circuit
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (components : List (CleanComponent gatePermutation)) :
    (sequenceComponents gatePermutation components).circuit =
      Circuit.sequence (components.map fun component => component.circuit) := by
  induction components with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp [sequenceComponents, seqWithConditions, Circuit.sequence,
        inductionHypothesis]

/-- clean componentを、各中間入力条件を追跡しながら指定回数反復する。 -/
def repeatComponent
    {Gate basis : Type*}
    {gatePermutation : Gate → Equiv.Perm basis}
    (component : CleanComponent gatePermutation) :
    Nat → CleanComponent gatePermutation
  | 0 => identity gatePermutation
  | count + 1 => seqWithConditions component (repeatComponent component count)

/-- 置換componentを、全入力で適用可能なclean componentとして読む。 -/
def ofPermutation
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {gatePermutation : Gate → Equiv.Perm basis}
    (component : PermutationComponent gateOperator gatePermutation) :
    CleanComponent gatePermutation where
  circuit := component.circuit
  reference := component.reference
  inputCondition := fun _ => True
  outputCondition := fun _ => True
  restoration := fun input output => output = component.reference input
  runBasis_correct := fun input _ => component.runBasis_correct input
  outputCondition_correct := by simp
  restoration_correct := by simp

/--
同じ実装回路を持つclean componentの参照関数を、独立な公開解析仕様へ精密化する。
-/
def refineReference
    {Gate basis : Type*} {gatePermutation : Gate → Equiv.Perm basis}
    (implementation : CleanComponent gatePermutation)
    (targetReference : basis → basis)
    (targetInputCondition targetOutputCondition : basis → Prop)
    (targetRestoration : basis → basis → Prop)
    (inputBridge : ∀ input, targetInputCondition input →
      implementation.inputCondition input)
    (referenceEq : ∀ input, targetInputCondition input →
      implementation.reference input = targetReference input)
    (outputCorrect : ∀ input, targetInputCondition input →
      targetOutputCondition (targetReference input))
    (restorationCorrect : ∀ input, targetInputCondition input →
      targetRestoration input (targetReference input)) :
    CleanComponent gatePermutation where
  circuit := implementation.circuit
  reference := targetReference
  inputCondition := targetInputCondition
  outputCondition := targetOutputCondition
  restoration := targetRestoration
  runBasis_correct := by
    intro input clean
    exact (implementation.runBasis_correct input (inputBridge input clean)).trans
      (referenceEq input clean)
  outputCondition_correct := outputCorrect
  restoration_correct := restorationCorrect

/-- 一つ目の出力条件が二つ目の入力条件を導くとき、clean componentを逐次合成する。 -/
def seq
    {Gate basis : Type*}
    {gatePermutation : Gate → Equiv.Perm basis}
    (first second : CleanComponent gatePermutation)
    (bridge : ∀ output, first.outputCondition output →
      second.inputCondition output) : CleanComponent gatePermutation where
  circuit := .seq first.circuit second.circuit
  reference := second.reference ∘ first.reference
  inputCondition := first.inputCondition
  outputCondition := second.outputCondition
  restoration := fun input output =>
    first.restoration input (first.reference input) ∧
      second.restoration (first.reference input) output
  runBasis_correct := by
    intro input clean
    change second.circuit.runBasis gatePermutation
      (first.circuit.runBasis gatePermutation input) = _
    rw [first.runBasis_correct input clean]
    rw [second.runBasis_correct (first.reference input)
      (bridge _ (first.outputCondition_correct input clean))]
    rfl
  outputCondition_correct := by
    intro input clean
    exact second.outputCondition_correct _
      (bridge _ (first.outputCondition_correct input clean))
  restoration_correct := by
    intro input clean
    exact ⟨first.restoration_correct input clean,
      second.restoration_correct _
        (bridge _ (first.outputCondition_correct input clean))⟩

/-- 同一clean変換を、出力から次の入力条件へのbridgeを使って反復する。 -/
def «repeat»
    {Gate basis : Type*}
    {gatePermutation : Gate → Equiv.Perm basis}
    (component : CleanComponent gatePermutation)
    (bridge : ∀ output, component.outputCondition output →
      component.inputCondition output)
    (count : Nat) : CleanComponent gatePermutation where
  circuit := .repeat count component.circuit
  reference := iterateReference component.reference count
  inputCondition := component.inputCondition
  outputCondition := component.inputCondition
  restoration := iteratedRestoration component.restoration count
  runBasis_correct := by
    intro input clean
    change (component.circuit.toExecutionPermutation gatePermutation ^ count) input = _
    induction count generalizing input with
    | zero => rfl
    | succ count inductionHypothesis =>
        rw [pow_succ]
        change (component.circuit.toExecutionPermutation gatePermutation ^ count)
          (component.circuit.toExecutionPermutation gatePermutation input) = _
        have step : component.circuit.toExecutionPermutation gatePermutation input =
            component.reference input := by
          simpa [Circuit.runBasis] using component.runBasis_correct input clean
        rw [step]
        simp only [iterateReference, Function.comp_apply]
        exact inductionHypothesis (component.reference input)
          (bridge _ (component.outputCondition_correct input clean))
  outputCondition_correct := by
    intro input clean
    induction count generalizing input with
    | zero => exact clean
    | succ count inductionHypothesis =>
        exact inductionHypothesis (component.reference input)
          (bridge _ (component.outputCondition_correct input clean))
  restoration_correct := by
    intro input clean
    induction count generalizing input with
    | zero => rfl
    | succ count inductionHypothesis =>
        exact ⟨component.reference input, component.restoration_correct input clean,
          inductionHypothesis (component.reference input)
            (bridge _ (component.outputCondition_correct input clean))⟩

/-- compute・use・uncomputeの三契約を二回のclean逐次合成だけで束ねる。 -/
def computeUseUncompute
    {Gate basis : Type*}
    {gatePermutation : Gate → Equiv.Perm basis}
    (compute use uncompute : CleanComponent gatePermutation)
    (computeToUse : ∀ output, compute.outputCondition output →
      use.inputCondition output)
    (useToUncompute : ∀ output, use.outputCondition output →
      uncompute.inputCondition output) : CleanComponent gatePermutation :=
  seq compute (seq use uncompute useToUncompute) computeToUse

end CleanComponent

namespace SubspaceMapComponent

/-- 条件を満たす計算基底 ket が生成する coherent 部分空間。 -/
def basisSpan {basis : Type*} [DecidableEq basis]
    (predicate : basis → Prop) : Submodule ℂ (State basis) :=
  Submodule.span ℂ
    (Set.range (fun input : { value : basis // predicate value } =>
      basisKet input.1))

/-- 条件を満たす計算基底 ket は対応する `basisSpan` に属する。 -/
theorem basisKet_mem_basisSpan
    {basis : Type*} [DecidableEq basis]
    {predicate : basis → Prop} {input : basis} (inside : predicate input) :
    basisKet input ∈ basisSpan predicate := by
  apply Submodule.subset_span
  exact ⟨⟨input, inside⟩, rfl⟩

/-- Every state in a coherent basis span has zero coordinate on basis values
outside the generating predicate.  This is the converse-facing observation
used to turn a `SubspaceMapComponent.target_maps` proof into an extensional
matrix-entry support theorem. -/
theorem basisSpan_apply_eq_zero
    {basis : Type*} [DecidableEq basis]
    {predicate : basis → Prop} {state : State basis}
    (inside : state ∈ basisSpan predicate)
    (output : basis) (outside : ¬ predicate output) :
    state output = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ inside
  · intro generator member
    rcases member with ⟨input, rfl⟩
    by_cases equal : output = input.1
    · subst output
      exact False.elim (outside input.2)
    · simp [basisKet, equal]
  · rfl
  · intro left right _ _ leftZero rightZero
    simp [leftZero, rightZero]
  · intro scalar value _ valueZero
    simp [valueZero]

/-- It is enough to place every generating basis ket in a subspace in order
to include the entire coherent basis span in that subspace. -/
theorem basisSpan_le_of_basis
    {basis : Type*} [DecidableEq basis]
    {predicate : basis → Prop} {subspace : Submodule ℂ (State basis)}
    (inside : ∀ input, predicate input → basisKet input ∈ subspace) :
    basisSpan predicate ≤ subspace := by
  rw [basisSpan]
  apply Submodule.span_le.mpr
  rintro state ⟨input, rfl⟩
  exact inside input.1 input.2

/-- If an operator column has no amplitude outside a basis predicate, applying
it to that basis ket lies in the coherent span generated by the predicate. -/
theorem applyOperator_basisKet_mem_basisSpan_of_entry_support
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (operator : Operator basis) (input : basis) (predicate : basis → Prop)
    (support : ∀ output, ¬ predicate output → operator output input = 0) :
    applyOperator operator (basisKet input) ∈ basisSpan predicate := by
  have expansion :
      applyOperator operator (basisKet input) =
        ∑ output : basis, operator output input • basisKet output := by
    funext output
    rw [applyOperator_basisKet]
    simp [basisKet, VerifiedMath.Basis.vector]
  rw [expansion]
  apply Submodule.sum_mem
  intro output _
  by_cases inside : predicate output
  · exact (basisSpan predicate).smul_mem _
      (basisKet_mem_basisSpan inside)
  · simp [support output inside]

/-- Operator entry locality turns any outside-stable basis predicate into a
coherent basis-span preservation theorem. -/
theorem applyOperator_basisKet_mem_basisSpan_of_preservesOutside
    {qubits : Nat} (operator : Operator (QubitBasis qubits))
    (support : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support operator)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (predicateStable : ∀ input output,
      inputPredicate input →
      (∀ wire, wire ∉ support → output wire = input wire) →
      outputPredicate output)
    (input : QubitBasis qubits) (inside : inputPredicate input) :
    applyOperator operator (basisKet input) ∈ basisSpan outputPredicate := by
  apply applyOperator_basisKet_mem_basisSpan_of_entry_support
  intro output outsideOutput
  by_contra nonzero
  exact outsideOutput
    (predicateStable input output inside (locality output input nonzero))

/-- A support-local operator preserves zeroes on every disjoint protected wire
as a coherent basis-span statement. -/
theorem applyOperator_basisKet_mem_basisSpan_zeroOn
    {qubits : Nat} (operator : Operator (QubitBasis qubits))
    (support protectedWires : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support operator)
    (disjoint : Disjoint support protectedWires)
    (input : QubitBasis qubits)
    (inside : QubitBasisZeroOn protectedWires input) :
    applyOperator operator (basisKet input) ∈
      basisSpan (QubitBasisZeroOn protectedWires) := by
  apply applyOperator_basisKet_mem_basisSpan_of_preservesOutside
    operator support locality (QubitBasisZeroOn protectedWires)
      (QubitBasisZeroOn protectedWires) _ input inside
  intro original output originalZero sameOutside wire wireProtected
  rw [sameOutside wire]
  · exact originalZero wire wireProtected
  · intro wireSupported
    exact (Finset.disjoint_left.mp disjoint) wireSupported wireProtected

/-- 基底 ket 上の正しさと写像先だけから coherent span 上の契約を作る。 -/
def ofBasisSpan
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (circuit : Circuit Gate) (target : Operator basis)
    (inputPredicate outputPredicate : basis → Prop)
    (basisCorrect : ∀ input, inputPredicate input →
      applyOperator (circuit.denote gateOperator) (basisKet input) =
        applyOperator target (basisKet input))
    (basisMaps : ∀ input, inputPredicate input →
      applyOperator target (basisKet input) ∈ basisSpan outputPredicate) :
    SubspaceMapComponent gateOperator where
  circuit := circuit
  target := target
  inputSubspace := basisSpan inputPredicate
  outputSubspace := basisSpan outputPredicate
  correct := by
    intro state inside
    refine Submodule.span_induction ?_ ?_ ?_ ?_ inside
    · intro generator member
      rcases member with ⟨input, rfl⟩
      exact basisCorrect input.1 input.2
    · simp
    · intro left right _ _ leftCorrect rightCorrect
      rw [applyOperator_add, applyOperator_add, leftCorrect, rightCorrect]
    · intro scalar basisState _ stateCorrect
      rw [applyOperator_smul, applyOperator_smul, stateCorrect]
  target_maps := by
    intro state inside
    refine Submodule.span_induction ?_ ?_ ?_ ?_ inside
    · intro generator member
      rcases member with ⟨input, rfl⟩
      exact basisMaps input.1 input.2
    · simp
    · intro left right _ _ leftInside rightInside
      rw [applyOperator_add]
      exact (basisSpan outputPredicate).add_mem leftInside rightInside
    · intro scalar basisState _ stateInside
      rw [applyOperator_smul]
      exact (basisSpan outputPredicate).smul_mem scalar stateInside

/-- 回路作用も、解析作用と同じく入力部分空間を出力部分空間へ写す。 -/
theorem actual_maps
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : SubspaceMapComponent gateOperator)
    (state : State basis) (inside : state ∈ component.inputSubspace) :
    applyOperator (component.circuit.denote gateOperator) state ∈
      component.outputSubspace := by
  rw [component.correct state inside]
  exact component.target_maps state inside

/-- 出力部分空間と次の入力部分空間が一致する二つの部分空間写像を合成する。 -/
def seq
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (first second : SubspaceMapComponent gateOperator)
    (middle : second.inputSubspace = first.outputSubspace) :
    SubspaceMapComponent gateOperator where
  circuit := .seq first.circuit second.circuit
  target := second.target * first.target
  inputSubspace := first.inputSubspace
  outputSubspace := second.outputSubspace
  correct := by
    intro state inside
    rw [Circuit.denote_seq, applyOperator_mul, first.correct state inside]
    have intermediate : applyOperator first.target state ∈ second.inputSubspace := by
      rw [middle]
      exact first.target_maps state inside
    rw [second.correct _ intermediate, applyOperator_mul]
  target_maps := by
    intro state inside
    rw [applyOperator_mul]
    have intermediate : applyOperator first.target state ∈ second.inputSubspace := by
      rw [middle]
      exact first.target_maps state inside
    exact second.target_maps _ intermediate

/-- Identity map on an explicitly chosen coherent subspace. -/
def identity
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (subspace : Submodule ℂ (State basis)) :
    SubspaceMapComponent gateOperator where
  circuit := .identity
  target := 1
  inputSubspace := subspace
  outputSubspace := subspace
  correct := by intro _ _; rfl
  target_maps := by
    intro state inside
    change Matrix.mulVec (1 : Operator basis) state ∈ subspace
    rw [Matrix.one_mulVec]
    exact inside

/-- Repackage a subspace map whose public input and output spaces are both
propositionally equal to a common coherent space. -/
def withCommonSpace
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : SubspaceMapComponent gateOperator)
    (common : Submodule ℂ (State basis))
    (inputEq : component.inputSubspace = common)
    (outputEq : component.outputSubspace = common) :
    SubspaceMapComponent gateOperator where
  circuit := component.circuit
  target := component.target
  inputSubspace := common
  outputSubspace := common
  correct := by
    intro state inside
    apply component.correct state
    rw [inputEq]
    exact inside
  target_maps := by
    intro state inside
    have mapped := component.target_maps state (by
      rw [inputEq]
      exact inside)
    rw [outputEq] at mapped
    exact mapped

/-- Rename the independent target of a subspace map along a proved operator
equality while preserving its implementation and coherent spaces. -/
def refineTarget
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (child : SubspaceMapComponent gateOperator)
    (target : Operator basis) (targetEq : child.target = target) :
    SubspaceMapComponent gateOperator where
  circuit := child.circuit
  target := target
  inputSubspace := child.inputSubspace
  outputSubspace := child.outputSubspace
  correct := by
    intro state inside
    rw [← targetEq]
    exact child.correct state inside
  target_maps := by
    intro state inside
    rw [← targetEq]
    exact child.target_maps state inside

@[simp] theorem refineTarget_circuit
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (child : SubspaceMapComponent gateOperator)
    (target : Operator basis) (targetEq : child.target = target) :
    (child.refineTarget target targetEq).circuit = child.circuit := rfl

@[simp] theorem refineTarget_target
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (child : SubspaceMapComponent gateOperator)
    (target : Operator basis) (targetEq : child.target = target) :
    (child.refineTarget target targetEq).target = target := rfl

@[simp] theorem refineTarget_inputSubspace
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (child : SubspaceMapComponent gateOperator)
    (target : Operator basis) (targetEq : child.target = target) :
    (child.refineTarget target targetEq).inputSubspace =
      child.inputSubspace := rfl

@[simp] theorem refineTarget_outputSubspace
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (child : SubspaceMapComponent gateOperator)
    (target : Operator basis) (targetEq : child.target = target) :
    (child.refineTarget target targetEq).outputSubspace =
      child.outputSubspace := rfl

theorem refineTarget_correct
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (child : SubspaceMapComponent gateOperator)
    (target : Operator basis) (targetEq : child.target = target)
    (state : State basis) (inside : state ∈ child.inputSubspace) :
    applyOperator ((child.refineTarget target targetEq).circuit.denote gateOperator)
        state =
      applyOperator target state :=
  (child.refineTarget target targetEq).correct state (by simpa using inside)

/-- Compose a source-order list of maps that all preserve one common
subspace.  The empty list is the identity; consequently the circuit and target
are exactly `Circuit.sequence` and `operatorSequence` of the public children. -/
def sequenceOnCommon
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (common : Submodule ℂ (State basis))
    (components : List (SubspaceMapComponent gateOperator))
    (spaces : ∀ component, component ∈ components →
      component.inputSubspace = common ∧
        component.outputSubspace = common) :
    SubspaceMapComponent gateOperator where
  circuit := Circuit.sequence (components.map fun component => component.circuit)
  target := operatorSequence (components.map fun component => component.target)
  inputSubspace := common
  outputSubspace := common
  correct := by
    intro state inside
    induction components generalizing state with
    | nil => rfl
    | cons first rest inductionHypothesis =>
        have firstSpaces := spaces first (by simp)
        have firstInput : state ∈ first.inputSubspace := by
          rw [firstSpaces.1]
          exact inside
        have firstOutput : applyOperator first.target state ∈ common := by
          have mapped := first.target_maps state firstInput
          rw [firstSpaces.2] at mapped
          exact mapped
        simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
          operatorSequence, applyOperator_mul]
        rw [first.correct state firstInput]
        exact inductionHypothesis
          (fun component member => spaces component (by simp [member]))
          (applyOperator first.target state) firstOutput
  target_maps := by
    intro state inside
    induction components generalizing state with
    | nil =>
        change Matrix.mulVec (1 : Operator basis) state ∈ common
        rw [Matrix.one_mulVec]
        exact inside
    | cons first rest inductionHypothesis =>
        have firstSpaces := spaces first (by simp)
        have firstInput : state ∈ first.inputSubspace := by
          rw [firstSpaces.1]
          exact inside
        have firstOutput : applyOperator first.target state ∈ common := by
          have mapped := first.target_maps state firstInput
          rw [firstSpaces.2] at mapped
          exact mapped
        simpa only [List.map_cons, operatorSequence, applyOperator_mul] using
          inductionHypothesis
            (fun component member => spaces component (by simp [member]))
            (applyOperator first.target state) firstOutput

@[simp] theorem sequenceOnCommon_circuit
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (common : Submodule ℂ (State basis))
    (components : List (SubspaceMapComponent gateOperator))
    (spaces : ∀ component, component ∈ components →
      component.inputSubspace = common ∧
        component.outputSubspace = common) :
    (sequenceOnCommon gateOperator common components spaces).circuit =
      Circuit.sequence (components.map fun component => component.circuit) := rfl

@[simp] theorem sequenceOnCommon_target
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis)
    (common : Submodule ℂ (State basis))
    (components : List (SubspaceMapComponent gateOperator))
    (spaces : ∀ component, component ∈ components →
      component.inputSubspace = common ∧
        component.outputSubspace = common) :
    (sequenceOnCommon gateOperator common components spaces).target =
      operatorSequence (components.map fun component => component.target) := rfl

/-- A source-order list of coherent maps with explicit intermediate spaces.
Unlike `sequenceOnCommon`, the first input and final output spaces may differ,
and every intermediate boundary remains visible in the proof object. -/
inductive SpaceChain
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis} :
    List (SubspaceMapComponent gateOperator) →
      Submodule ℂ (State basis) → Submodule ℂ (State basis) → Prop
  | nil (space : Submodule ℂ (State basis)) : SpaceChain [] space space
  | cons (first : SubspaceMapComponent gateOperator)
      (rest : List (SubspaceMapComponent gateOperator))
      (input middle output : Submodule ℂ (State basis))
      (inputEq : first.inputSubspace = input)
      (outputEq : first.outputSubspace = middle)
      (tail : SpaceChain rest middle output) :
      SpaceChain (first :: rest) input output

namespace SpaceChain

/-- A list of components sharing one coherent space forms a visible
`SpaceChain` from that space to itself. -/
theorem ofCommon
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (components : List (SubspaceMapComponent gateOperator))
    (common : Submodule ℂ (State basis))
    (spaces : ∀ component, component ∈ components →
      component.inputSubspace = common ∧
        component.outputSubspace = common) :
    SpaceChain components common common := by
  induction components with
  | nil => exact .nil common
  | cons first rest inductionHypothesis =>
      have firstSpaces := spaces first (by simp)
      refine .cons first rest common common common firstSpaces.1
        firstSpaces.2 ?_
      exact inductionHypothesis (fun component member =>
        spaces component (by simp [member]))

/-- Concatenate two typed coherent chains at an identical middle space. -/
theorem append
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {first second : List (SubspaceMapComponent gateOperator)}
    {input middle output : Submodule ℂ (State basis)}
    (left : SpaceChain first input middle)
    (right : SpaceChain second middle output) :
    SpaceChain (first ++ second) input output := by
  induction left with
  | nil space => simpa using right
  | cons head tail start next finish inputEq outputEq rest inductionHypothesis =>
      exact .cons head (tail ++ second) start next output inputEq outputEq
        (inductionHypothesis right)

/-- A single component exposes its declared input/output spaces as a chain. -/
theorem singleton
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : SubspaceMapComponent gateOperator) :
    SpaceChain [component] component.inputSubspace component.outputSubspace :=
  .cons component [] component.inputSubspace component.outputSubspace
    component.outputSubspace rfl rfl (.nil component.outputSubspace)

end SpaceChain

/-- Compose a typed source-order chain while retaining the public
`Circuit.sequence` and `operatorSequence` normal forms. -/
def sequenceAlong
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {components : List (SubspaceMapComponent gateOperator)}
    {inputSpace outputSpace : Submodule ℂ (State basis)}
    (chain : SpaceChain components inputSpace outputSpace) :
    SubspaceMapComponent gateOperator where
  circuit := Circuit.sequence (components.map fun component => component.circuit)
  target := operatorSequence (components.map fun component => component.target)
  inputSubspace := inputSpace
  outputSubspace := outputSpace
  correct := by
    intro state inside
    induction chain generalizing state with
    | nil space => rfl
    | cons first rest input middle output inputEq outputEq tail inductionHypothesis =>
        have firstInside : state ∈ first.inputSubspace := by
          rw [inputEq]
          exact inside
        have firstOutput : applyOperator first.target state ∈ middle := by
          have mapped := first.target_maps state firstInside
          rw [outputEq] at mapped
          exact mapped
        simp only [List.map_cons, Circuit.sequence, Circuit.denote_seq,
          operatorSequence, applyOperator_mul]
        rw [first.correct state firstInside]
        exact inductionHypothesis (applyOperator first.target state) firstOutput
  target_maps := by
    intro state inside
    induction chain generalizing state with
    | nil space =>
        change Matrix.mulVec (1 : Operator basis) state ∈ space
        rw [Matrix.one_mulVec]
        exact inside
    | cons first rest input middle output inputEq outputEq tail inductionHypothesis =>
        have firstInside : state ∈ first.inputSubspace := by
          rw [inputEq]
          exact inside
        have firstOutput : applyOperator first.target state ∈ middle := by
          have mapped := first.target_maps state firstInside
          rw [outputEq] at mapped
          exact mapped
        simpa only [List.map_cons, operatorSequence, applyOperator_mul] using
          inductionHypothesis (applyOperator first.target state) firstOutput

@[simp] theorem sequenceAlong_circuit
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {components : List (SubspaceMapComponent gateOperator)}
    {inputSpace outputSpace : Submodule ℂ (State basis)}
    (chain : SpaceChain components inputSpace outputSpace) :
    (sequenceAlong chain).circuit =
      Circuit.sequence (components.map fun component => component.circuit) := rfl

@[simp] theorem sequenceAlong_target
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {components : List (SubspaceMapComponent gateOperator)}
    {inputSpace outputSpace : Submodule ℂ (State basis)}
    (chain : SpaceChain components inputSpace outputSpace) :
    (sequenceAlong chain).target =
      operatorSequence (components.map fun component => component.target) := rfl

@[simp] theorem sequenceAlong_inputSubspace
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {components : List (SubspaceMapComponent gateOperator)}
    {inputSpace outputSpace : Submodule ℂ (State basis)}
    (chain : SpaceChain components inputSpace outputSpace) :
    (sequenceAlong chain).inputSubspace = inputSpace := rfl

@[simp] theorem sequenceAlong_outputSubspace
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {components : List (SubspaceMapComponent gateOperator)}
    {inputSpace outputSpace : Submodule ℂ (State basis)}
    (chain : SpaceChain components inputSpace outputSpace) :
    (sequenceAlong chain).outputSubspace = outputSpace := rfl

/-- 部分空間写像の後ろへ、その出力部分空間を保存する厳密作用素を接続する。 -/
def thenExact
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (first : SubspaceMapComponent gateOperator)
    (second : ExactOperatorComponent gateOperator)
    (secondMaps : ∀ state, state ∈ first.outputSubspace →
      applyOperator second.target state ∈ first.outputSubspace) :
    SubspaceMapComponent gateOperator where
  circuit := .seq first.circuit second.circuit
  target := second.target * first.target
  inputSubspace := first.inputSubspace
  outputSubspace := first.outputSubspace
  correct := by
    intro state inside
    rw [Circuit.denote_seq, applyOperator_mul, first.correct state inside,
      second.correct, applyOperator_mul]
  target_maps := by
    intro state inside
    rw [applyOperator_mul]
    exact secondMaps _ (first.target_maps state inside)

/-- 厳密作用素の後ろへ部分空間写像を接続する。 -/
def prependExact
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (first : ExactOperatorComponent gateOperator)
    (second : SubspaceMapComponent gateOperator)
    (inputSubspace : Submodule ℂ (State basis))
    (firstMaps : ∀ state, state ∈ inputSubspace →
      applyOperator first.target state ∈ second.inputSubspace) :
    SubspaceMapComponent gateOperator where
  circuit := .seq first.circuit second.circuit
  target := second.target * first.target
  inputSubspace := inputSubspace
  outputSubspace := second.outputSubspace
  correct := by
    intro state inside
    rw [Circuit.denote_seq, applyOperator_mul, first.correct]
    rw [second.correct _ (firstMaps state inside), applyOperator_mul]
  target_maps := by
    intro state inside
    rw [applyOperator_mul]
    exact second.target_maps _ (firstMaps state inside)

/-- Restrict an existing subspace map to a coherent basis span when its target
maps every generating basis ket back into that span. -/
def restrictBasisSpan
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : SubspaceMapComponent gateOperator)
    (predicate : basis → Prop)
    (predicateInside : ∀ input, predicate input →
      basisKet input ∈ component.inputSubspace)
    (predicateMaps : ∀ input, predicate input →
      applyOperator component.target (basisKet input) ∈ basisSpan predicate) :
    SubspaceMapComponent gateOperator :=
  ofBasisSpan gateOperator component.circuit component.target predicate predicate
    (by
      intro input inside
      exact component.correct (basisKet input) (predicateInside input inside))
    predicateMaps

/-- Refine an existing possibly-asymmetric coherent map by a read-only basis
invariant.  The original input/output predicates remain owned by the child;
the new invariant is transported solely from the target's write-locality.
This is useful when a controlled child reads a live flag but cannot modify it. -/
def restrictBasisSpanWithInvariant
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : SubspaceMapComponent gateOperator)
    (support : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (inputPredicate outputPredicate invariant : QubitBasis qubits → Prop)
    (inputInside : ∀ input, inputPredicate input →
      basisKet input ∈ component.inputSubspace)
    (outputSpace : component.outputSubspace = basisSpan outputPredicate)
    (invariantStable : ∀ input output,
      invariant input →
      (∀ wire, wire ∉ support → output wire = input wire) →
      invariant output) :
    SubspaceMapComponent gateOperator :=
  ofBasisSpan gateOperator component.circuit component.target
    (fun input => inputPredicate input ∧ invariant input)
    (fun output => outputPredicate output ∧ invariant output)
    (by
      intro input inside
      exact component.correct _ (inputInside input inside.1))
    (by
      intro input inside
      apply applyOperator_basisKet_mem_basisSpan_of_entry_support
      intro output outside
      have mapped := component.target_maps (basisKet input)
        (inputInside input inside.1)
      rw [outputSpace] at mapped
      by_cases originalOutput : outputPredicate output
      · have invariantOutside : ¬ invariant output := by
          intro outputInvariant
          exact outside ⟨originalOutput, outputInvariant⟩
        by_contra nonzero
        exact invariantOutside
          (invariantStable input output inside.2
            (locality output input nonzero))
      · simpa only [applyOperator_basisKet] using
          basisSpan_apply_eq_zero mapped output originalOutput)

@[simp] theorem restrictBasisSpanWithInvariant_circuit
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : SubspaceMapComponent gateOperator)
    (support : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (inputPredicate outputPredicate invariant : QubitBasis qubits → Prop)
    (inputInside : ∀ input, inputPredicate input →
      basisKet input ∈ component.inputSubspace)
    (outputSpace : component.outputSubspace = basisSpan outputPredicate)
    (invariantStable : ∀ input output,
      invariant input →
      (∀ wire, wire ∉ support → output wire = input wire) →
      invariant output) :
    (component.restrictBasisSpanWithInvariant support locality
      inputPredicate outputPredicate invariant inputInside outputSpace
      invariantStable).circuit = component.circuit := rfl

@[simp] theorem restrictBasisSpanWithInvariant_target
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : SubspaceMapComponent gateOperator)
    (support : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (inputPredicate outputPredicate invariant : QubitBasis qubits → Prop)
    (inputInside : ∀ input, inputPredicate input →
      basisKet input ∈ component.inputSubspace)
    (outputSpace : component.outputSubspace = basisSpan outputPredicate)
    (invariantStable : ∀ input output,
      invariant input →
      (∀ wire, wire ∉ support → output wire = input wire) →
      invariant output) :
    (component.restrictBasisSpanWithInvariant support locality
      inputPredicate outputPredicate invariant inputInside outputSpace
      invariantStable).target = component.target := rfl

theorem restrictBasisSpanWithInvariant_spaces
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : SubspaceMapComponent gateOperator)
    (support : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (inputPredicate outputPredicate invariant : QubitBasis qubits → Prop)
    (inputInside : ∀ input, inputPredicate input →
      basisKet input ∈ component.inputSubspace)
    (outputSpace : component.outputSubspace = basisSpan outputPredicate)
    (invariantStable : ∀ input output,
      invariant input →
      (∀ wire, wire ∉ support → output wire = input wire) →
      invariant output) :
    (component.restrictBasisSpanWithInvariant support locality
        inputPredicate outputPredicate invariant inputInside outputSpace
        invariantStable).inputSubspace =
          basisSpan (fun input => inputPredicate input ∧ invariant input) ∧
      (component.restrictBasisSpanWithInvariant support locality
        inputPredicate outputPredicate invariant inputInside outputSpace
        invariantStable).outputSubspace =
          basisSpan (fun output => outputPredicate output ∧ invariant output) := by
  constructor <;> rfl

/-- Restrict an existing support-local subspace map to zeroes on a protected
set disjoint from the support. -/
def restrictBasisSpanOutsideZero
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : SubspaceMapComponent gateOperator)
    (support protectedWires : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (disjoint : Disjoint support protectedWires)
    (protectedInside : ∀ input, QubitBasisZeroOn protectedWires input →
      basisKet input ∈ component.inputSubspace) :
    SubspaceMapComponent gateOperator :=
  component.restrictBasisSpan (QubitBasisZeroOn protectedWires) protectedInside
    (applyOperator_basisKet_mem_basisSpan_zeroOn component.target support
      protectedWires locality disjoint)

@[simp] theorem restrictBasisSpanOutsideZero_circuit
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : SubspaceMapComponent gateOperator)
    (support protectedWires : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (disjoint : Disjoint support protectedWires)
    (protectedInside : ∀ input, QubitBasisZeroOn protectedWires input →
      basisKet input ∈ component.inputSubspace) :
    (component.restrictBasisSpanOutsideZero support protectedWires locality disjoint
      protectedInside).circuit = component.circuit := rfl

@[simp] theorem restrictBasisSpanOutsideZero_target
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : SubspaceMapComponent gateOperator)
    (support protectedWires : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (disjoint : Disjoint support protectedWires)
    (protectedInside : ∀ input, QubitBasisZeroOn protectedWires input →
      basisKet input ∈ component.inputSubspace) :
    (component.restrictBasisSpanOutsideZero support protectedWires locality disjoint
      protectedInside).target = component.target := rfl

end SubspaceMapComponent

namespace ExactOperatorComponent

/-- 基底 predicate の保存証拠から、厳密作用素を coherent 部分空間写像へ持ち上げる。 -/
def toSubspaceMapOfBasisPreservation
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ExactOperatorComponent gateOperator)
    (inputPredicate outputPredicate : basis → Prop)
    (basisMaps : ∀ input, inputPredicate input →
      applyOperator component.target (basisKet input) ∈
        SubspaceMapComponent.basisSpan outputPredicate) :
    SubspaceMapComponent gateOperator :=
  SubspaceMapComponent.ofBasisSpan gateOperator component.circuit
    component.target inputPredicate outputPredicate
    (by
      intro input _
      rw [component.correct])
    basisMaps

/-- Refine a full-space exact component to an independently specified clean
operator on a coherent computational-basis span.  Unlike
`toSubspaceMapOfBasisPreservation`, the clean target need not equal the dirty
full-space target; the caller must provide their extensional agreement on each
clean basis ket. -/
def toSubspaceMapOfBasisAgreement
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ExactOperatorComponent gateOperator)
    (cleanTarget : Operator basis) (predicate : basis → Prop)
    (agreement : ∀ input, predicate input →
      applyOperator component.target (basisKet input) =
        applyOperator cleanTarget (basisKet input))
    (cleanMaps : ∀ input, predicate input →
      applyOperator cleanTarget (basisKet input) ∈
        SubspaceMapComponent.basisSpan predicate) :
    SubspaceMapComponent gateOperator :=
  SubspaceMapComponent.ofBasisSpan gateOperator component.circuit cleanTarget
    predicate predicate
    (by
      intro input inside
      calc
        applyOperator (component.circuit.denote gateOperator) (basisKet input) =
            applyOperator component.target (basisKet input) :=
          congrArg (fun operator => applyOperator operator (basisKet input))
            component.correct
        _ = applyOperator cleanTarget (basisKet input) :=
          agreement input inside)
    cleanMaps

/-- Refine an exact component to an independently specified clean operator
between two possibly different coherent basis spans.  This is the typed form
needed when a signal register is initialized at the input but intentionally
contains output data afterwards. -/
def toSubspaceMapOfBasisAgreementBetween
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ExactOperatorComponent gateOperator)
    (cleanTarget : Operator basis)
    (inputPredicate outputPredicate : basis → Prop)
    (agreement : ∀ input, inputPredicate input →
      applyOperator component.target (basisKet input) =
        applyOperator cleanTarget (basisKet input))
    (cleanMaps : ∀ input, inputPredicate input →
      applyOperator cleanTarget (basisKet input) ∈
        SubspaceMapComponent.basisSpan outputPredicate) :
    SubspaceMapComponent gateOperator :=
  SubspaceMapComponent.ofBasisSpan gateOperator component.circuit cleanTarget
    inputPredicate outputPredicate
    (by
      intro input inside
      calc
        applyOperator (component.circuit.denote gateOperator) (basisKet input) =
            applyOperator component.target (basisKet input) :=
          congrArg (fun operator => applyOperator operator (basisKet input))
            component.correct
        _ = applyOperator cleanTarget (basisKet input) :=
          agreement input inside)
    cleanMaps

@[simp] theorem toSubspaceMapOfBasisAgreementBetween_circuit
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ExactOperatorComponent gateOperator)
    (cleanTarget : Operator basis)
    (inputPredicate outputPredicate : basis → Prop)
    (agreement : ∀ input, inputPredicate input →
      applyOperator component.target (basisKet input) =
        applyOperator cleanTarget (basisKet input))
    (cleanMaps : ∀ input, inputPredicate input →
      applyOperator cleanTarget (basisKet input) ∈
        SubspaceMapComponent.basisSpan outputPredicate) :
    (component.toSubspaceMapOfBasisAgreementBetween cleanTarget
      inputPredicate outputPredicate agreement cleanMaps).circuit =
        component.circuit := rfl

@[simp] theorem toSubspaceMapOfBasisAgreementBetween_target
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ExactOperatorComponent gateOperator)
    (cleanTarget : Operator basis)
    (inputPredicate outputPredicate : basis → Prop)
    (agreement : ∀ input, inputPredicate input →
      applyOperator component.target (basisKet input) =
        applyOperator cleanTarget (basisKet input))
    (cleanMaps : ∀ input, inputPredicate input →
      applyOperator cleanTarget (basisKet input) ∈
        SubspaceMapComponent.basisSpan outputPredicate) :
    (component.toSubspaceMapOfBasisAgreementBetween cleanTarget
      inputPredicate outputPredicate agreement cleanMaps).target =
        cleanTarget := rfl

theorem toSubspaceMapOfBasisAgreementBetween_spaces
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ExactOperatorComponent gateOperator)
    (cleanTarget : Operator basis)
    (inputPredicate outputPredicate : basis → Prop)
    (agreement : ∀ input, inputPredicate input →
      applyOperator component.target (basisKet input) =
        applyOperator cleanTarget (basisKet input))
    (cleanMaps : ∀ input, inputPredicate input →
      applyOperator cleanTarget (basisKet input) ∈
        SubspaceMapComponent.basisSpan outputPredicate) :
    (component.toSubspaceMapOfBasisAgreementBetween cleanTarget
        inputPredicate outputPredicate agreement cleanMaps).inputSubspace =
        SubspaceMapComponent.basisSpan inputPredicate ∧
      (component.toSubspaceMapOfBasisAgreementBetween cleanTarget
        inputPredicate outputPredicate agreement cleanMaps).outputSubspace =
        SubspaceMapComponent.basisSpan outputPredicate :=
  ⟨rfl, rfl⟩

@[simp] theorem toSubspaceMapOfBasisAgreement_circuit
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ExactOperatorComponent gateOperator)
    (cleanTarget : Operator basis) (predicate : basis → Prop)
    (agreement : ∀ input, predicate input →
      applyOperator component.target (basisKet input) =
        applyOperator cleanTarget (basisKet input))
    (cleanMaps : ∀ input, predicate input →
      applyOperator cleanTarget (basisKet input) ∈
        SubspaceMapComponent.basisSpan predicate) :
    (component.toSubspaceMapOfBasisAgreement cleanTarget predicate agreement
      cleanMaps).circuit = component.circuit := rfl

@[simp] theorem toSubspaceMapOfBasisAgreement_target
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ExactOperatorComponent gateOperator)
    (cleanTarget : Operator basis) (predicate : basis → Prop)
    (agreement : ∀ input, predicate input →
      applyOperator component.target (basisKet input) =
        applyOperator cleanTarget (basisKet input))
    (cleanMaps : ∀ input, predicate input →
      applyOperator cleanTarget (basisKet input) ∈
        SubspaceMapComponent.basisSpan predicate) :
    (component.toSubspaceMapOfBasisAgreement cleanTarget predicate agreement
      cleanMaps).target = cleanTarget := rfl

theorem toSubspaceMapOfBasisAgreement_spaces
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : ExactOperatorComponent gateOperator)
    (cleanTarget : Operator basis) (predicate : basis → Prop)
    (agreement : ∀ input, predicate input →
      applyOperator component.target (basisKet input) =
        applyOperator cleanTarget (basisKet input))
    (cleanMaps : ∀ input, predicate input →
      applyOperator cleanTarget (basisKet input) ∈
        SubspaceMapComponent.basisSpan predicate) :
    (component.toSubspaceMapOfBasisAgreement cleanTarget predicate agreement
        cleanMaps).inputSubspace = SubspaceMapComponent.basisSpan predicate ∧
      (component.toSubspaceMapOfBasisAgreement cleanTarget predicate agreement
        cleanMaps).outputSubspace = SubspaceMapComponent.basisSpan predicate :=
  ⟨rfl, rfl⟩

/-- Lift an exact basis action to a coherent basis-span map when its action is
local to a declared wire support.  The predicate may inspect arbitrarily many
outside wires; it need only be stable under pointwise preservation outside the
support. -/
def toSubspaceMapOfBasisSpanOutsideSupport
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : ExactOperatorComponent gateOperator)
    (support : Finset (Fin qubits))
    (basisAction : QubitBasis qubits → QubitBasis qubits)
    (targetOnBasis : ∀ input,
      applyOperator component.target (basisKet input) =
        basisKet (basisAction input))
    (actionOutside : ∀ input wire, wire ∉ support →
      basisAction input wire = input wire)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (predicateStable : ∀ input output,
      inputPredicate input →
      (∀ wire, wire ∉ support → output wire = input wire) →
      outputPredicate output) :
    SubspaceMapComponent gateOperator :=
  component.toSubspaceMapOfBasisPreservation
    inputPredicate outputPredicate (by
      intro input inside
      rw [targetOnBasis]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      exact predicateStable input (basisAction input) inside
        (actionOutside input))

/-- Lift an exact support-local operator to any pair of outside-stable coherent
basis predicates. -/
def toSubspaceMapOfOutsideSupport
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : ExactOperatorComponent gateOperator)
    (support : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (predicateStable : ∀ input output,
      inputPredicate input →
      (∀ wire, wire ∉ support → output wire = input wire) →
      outputPredicate output) :
    SubspaceMapComponent gateOperator :=
  component.toSubspaceMapOfBasisPreservation inputPredicate outputPredicate
    (SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_of_preservesOutside
      component.target support locality inputPredicate outputPredicate
      predicateStable)

/-- Lift an exact support-local operator to the coherent sector where every
wire of a disjoint protected set is zero. -/
def toSubspaceMapOfOutsideZero
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : ExactOperatorComponent gateOperator)
    (support protectedWires : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (disjoint : Disjoint support protectedWires) :
    SubspaceMapComponent gateOperator :=
  component.toSubspaceMapOfBasisPreservation
    (QubitBasisZeroOn protectedWires) (QubitBasisZeroOn protectedWires)
    (SubspaceMapComponent.applyOperator_basisKet_mem_basisSpan_zeroOn
      component.target support protectedWires locality disjoint)

@[simp] theorem toSubspaceMapOfOutsideZero_circuit
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : ExactOperatorComponent gateOperator)
    (support protectedWires : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (disjoint : Disjoint support protectedWires) :
    (component.toSubspaceMapOfOutsideZero support protectedWires locality disjoint).circuit =
      component.circuit := rfl

@[simp] theorem toSubspaceMapOfOutsideZero_target
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : ExactOperatorComponent gateOperator)
    (support protectedWires : Finset (Fin qubits))
    (locality : OperatorPreservesOutside support component.target)
    (disjoint : Disjoint support protectedWires) :
    (component.toSubspaceMapOfOutsideZero support protectedWires locality disjoint).target =
      component.target := rfl

/-- The outside-support lift retains the exact child circuit. -/
@[simp] theorem toSubspaceMapOfBasisSpanOutsideSupport_circuit
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : ExactOperatorComponent gateOperator)
    (support : Finset (Fin qubits))
    (basisAction : QubitBasis qubits → QubitBasis qubits)
    (targetOnBasis : ∀ input,
      applyOperator component.target (basisKet input) =
        basisKet (basisAction input))
    (actionOutside : ∀ input wire, wire ∉ support →
      basisAction input wire = input wire)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (predicateStable : ∀ input output,
      inputPredicate input →
      (∀ wire, wire ∉ support → output wire = input wire) →
      outputPredicate output) :
    (component.toSubspaceMapOfBasisSpanOutsideSupport support basisAction
      targetOnBasis actionOutside inputPredicate outputPredicate
      predicateStable).circuit = component.circuit := rfl

/-- The outside-support lift retains the exact child target. -/
@[simp] theorem toSubspaceMapOfBasisSpanOutsideSupport_target
    {Gate : Type*} {qubits : Nat}
    {gateOperator : Gate → Operator (QubitBasis qubits)}
    (component : ExactOperatorComponent gateOperator)
    (support : Finset (Fin qubits))
    (basisAction : QubitBasis qubits → QubitBasis qubits)
    (targetOnBasis : ∀ input,
      applyOperator component.target (basisKet input) =
        basisKet (basisAction input))
    (actionOutside : ∀ input wire, wire ∉ support →
      basisAction input wire = input wire)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (predicateStable : ∀ input output,
      inputPredicate input →
      (∀ wire, wire ∉ support → output wire = input wire) →
      outputPredicate output) :
    (component.toSubspaceMapOfBasisSpanOutsideSupport support basisAction
      targetOnBasis actionOutside inputPredicate outputPredicate
      predicateStable).target = component.target := rfl

/-- 厳密作用素の後ろへ部分空間写像を接続する公開向きの合成則。 -/
def thenSubspace
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (first : ExactOperatorComponent gateOperator)
    (second : SubspaceMapComponent gateOperator)
    (inputSubspace : Submodule ℂ (State basis))
    (firstMaps : ∀ state, state ∈ inputSubspace →
      applyOperator first.target state ∈ second.inputSubspace) :
    SubspaceMapComponent gateOperator :=
  SubspaceMapComponent.prependExact first second inputSubspace firstMaps

end ExactOperatorComponent

namespace SubspaceOperatorComponent

/-- 同一部分空間を保存する契約を一般の部分空間写像契約として読む。 -/
def toSubspaceMap
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : SubspaceOperatorComponent gateOperator) :
    SubspaceMapComponent gateOperator where
  circuit := component.circuit
  target := component.target
  inputSubspace := component.subspace
  outputSubspace := component.subspace
  correct := component.correct
  target_maps := component.target_preserves

/-- 正しさとtarget保存から、実回路作用素も指定部分空間を保存する。 -/
theorem actual_preserves
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (component : SubspaceOperatorComponent gateOperator)
    (state : State basis) (inside : state ∈ component.subspace) :
    applyOperator (component.circuit.denote gateOperator) state ∈ component.subspace := by
  rw [component.correct state inside]
  exact component.target_preserves state inside

/-- 同じ部分空間を保存する二componentを実行順に逐次合成する。 -/
def seq
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (first second : SubspaceOperatorComponent gateOperator)
    (sameSubspace : second.subspace = first.subspace) :
    SubspaceOperatorComponent gateOperator where
  circuit := .seq first.circuit second.circuit
  target := second.target * first.target
  subspace := first.subspace
  correct := by
    intro state inside
    rw [Circuit.denote_seq, applyOperator_mul, first.correct state inside]
    have intermediate : applyOperator first.target state ∈ second.subspace := by
      rw [sameSubspace]
      exact first.target_preserves state inside
    rw [second.correct _ intermediate, applyOperator_mul]
  target_preserves := by
    intro state inside
    rw [applyOperator_mul]
    have firstInside := first.target_preserves state inside
    have secondInside : applyOperator first.target state ∈ second.subspace := by
      simpa [sameSubspace] using firstInside
    have result := second.target_preserves _ secondInside
    simpa [sameSubspace] using result

/-- 部分空間componentの後へ厳密全作用素componentを接続する。 -/
def thenExact
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (first : SubspaceOperatorComponent gateOperator)
    (second : ExactOperatorComponent gateOperator)
    (secondPreserves : ∀ state, state ∈ first.subspace →
      applyOperator second.target state ∈ first.subspace) :
    SubspaceOperatorComponent gateOperator where
  circuit := .seq first.circuit second.circuit
  target := second.target * first.target
  subspace := first.subspace
  correct := by
    intro state inside
    rw [Circuit.denote_seq, applyOperator_mul, first.correct state inside,
      second.correct, applyOperator_mul]
  target_preserves := by
    intro state inside
    rw [applyOperator_mul]
    exact secondPreserves _ (first.target_preserves state inside)

end SubspaceOperatorComponent

namespace StatePreparationComponent

/--
gate compiler、作用素lift、状態liftのintertwiningから状態準備componentを別基底へ移す。
-/
def liftByCompiler
    {Gate MappedGate basis mappedBasis : Type*}
    [Fintype basis] [DecidableEq basis]
    [Fintype mappedBasis] [DecidableEq mappedBasis]
    (gateOperator : Gate → Operator basis)
    (mappedOperator : MappedGate → Operator mappedBasis)
    (mapGate : Gate → MappedGate)
    (operatorLift : Operator basis →* Operator mappedBasis)
    (stateLift : State basis → State mappedBasis)
    (gateCorrect : ∀ gate,
      mappedOperator (mapGate gate) = operatorLift (gateOperator gate))
    (apply_intertwines : ∀ operator state,
      applyOperator (operatorLift operator) (stateLift state) =
        stateLift (applyOperator operator state))
    (component : StatePreparationComponent gateOperator) :
    StatePreparationComponent mappedOperator where
  circuit := component.circuit.mapGates mapGate
  initialState := stateLift component.initialState
  targetState := stateLift component.targetState
  correct := by
    rw [Circuit.denote_mapGates_monoidHom gateOperator mappedOperator mapGate
      operatorLift gateCorrect component.circuit]
    rw [apply_intertwines, component.correct]

/--
source葉をtarget回路へ展開するcompilerで状態準備componentを別基底へ移す。
正しさは実際にsource回路へ現れる葉だけに要求する。
-/
def liftByCircuitCompiler
    {Gate MappedGate basis mappedBasis : Type*}
    [Fintype basis] [DecidableEq basis]
    [Fintype mappedBasis] [DecidableEq mappedBasis]
    (gateOperator : Gate → Operator basis)
    (mappedOperator : MappedGate → Operator mappedBasis)
    (compileGate : Gate → Circuit MappedGate)
    (operatorLift : Operator basis →* Operator mappedBasis)
    (stateLift : State basis → State mappedBasis)
    (apply_intertwines : ∀ operator state,
      applyOperator (operatorLift operator) (stateLift state) =
        stateLift (applyOperator operator state))
    (component : StatePreparationComponent gateOperator)
    (gateCorrect : ∀ gate, gate ∈ component.circuit.flatten →
      Circuit.denote mappedOperator (compileGate gate) =
        operatorLift (gateOperator gate)) :
    StatePreparationComponent mappedOperator where
  circuit := component.circuit.compileGates compileGate
  initialState := stateLift component.initialState
  targetState := stateLift component.targetState
  correct := by
    rw [Circuit.denote_compileGates_monoidHom_of_mem gateOperator mappedOperator
      compileGate operatorLift component.circuit gateCorrect]
    rw [apply_intertwines, component.correct]

/-- 厳密状態準備の後に厳密作用素componentを適用する。 -/
def thenExact
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (preparation : StatePreparationComponent gateOperator)
    (operator : ExactOperatorComponent gateOperator) :
    StatePreparationComponent gateOperator where
  circuit := .seq preparation.circuit operator.circuit
  initialState := preparation.initialState
  targetState := applyOperator operator.target preparation.targetState
  correct := by
    rw [Circuit.denote_seq, applyOperator_mul, preparation.correct,
      operator.correct]

/--
計算基底ketから準備した回路を逆実行して指定基底で読む振幅は、
解析目標状態との有限内積に等しい。
-/
theorem reverse_applyOperator_at_basis
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    (gateOperator : Gate → Operator basis) (inverseGate : Gate → Gate)
    (inverseCorrect : ∀ gate,
      gateOperator (inverseGate gate) = Matrix.conjTranspose (gateOperator gate))
    (preparation : StatePreparationComponent gateOperator)
    (input : basis) (initial_eq : preparation.initialState = basisKet input)
    (state : State basis) :
    applyOperator
        ((preparation.circuit.reverse inverseGate).denote gateOperator)
        state input =
      ∑ value, star (preparation.targetState value) * state value := by
  rw [Circuit.denote_reverse inverseGate gateOperator inverseCorrect]
  unfold applyOperator Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro value _
  change star (preparation.circuit.denote gateOperator value input) * state value =
    star (preparation.targetState value) * state value
  have prepared := congrFun preparation.correct value
  rw [initial_eq, applyOperator_basisKet] at prepared
  rw [prepared]

/-- unitary状態準備回路を逆実行し、目標状態から初期状態を厳密に復元する。 -/
def reverse
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (inverseGate : Gate → Gate)
    (inverseCorrect : ∀ gate,
      gateOperator (inverseGate gate) = Matrix.conjTranspose (gateOperator gate))
    (preparation : StatePreparationComponent gateOperator)
    (unitary : preparation.circuit.denote gateOperator ∈
      Matrix.unitaryGroup basis ℂ) : StatePreparationComponent gateOperator where
  circuit := preparation.circuit.reverse inverseGate
  initialState := preparation.targetState
  targetState := preparation.initialState
  correct := by
    rw [Circuit.denote_reverse inverseGate gateOperator inverseCorrect,
      ← preparation.correct, ← applyOperator_mul]
    have inverseProduct :
        Matrix.conjTranspose (preparation.circuit.denote gateOperator) *
          preparation.circuit.denote gateOperator = 1 := by
      exact (Matrix.mem_unitaryGroup_iff').mp unitary
    rw [inverseProduct]
    simp [applyOperator]

/-- 厳密状態準備を誤差0の抽象近似状態準備として読む。 -/
def toApprox
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    (errorModel : StateErrorModel basis)
    (preparation : StatePreparationComponent gateOperator) :
    ApproxStatePreparationComponent gateOperator errorModel where
  circuit := preparation.circuit
  initialState := preparation.initialState
  targetState := preparation.targetState
  error := 0
  error_nonnegative := le_rfl
  correct := by rw [preparation.correct]; exact errorModel.refl _

end StatePreparationComponent

namespace ApproxOperatorComponent

/-- 近似作用素componentを加法的誤差modelで逐次合成する。 -/
def seq
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {errorModel : OperatorErrorModel basis}
    (first second : ApproxOperatorComponent gateOperator errorModel) :
    ApproxOperatorComponent gateOperator errorModel where
  circuit := .seq first.circuit second.circuit
  target := second.target * first.target
  error := first.error + second.error
  error_nonnegative := add_nonneg first.error_nonnegative second.error_nonnegative
  actual_contraction := errorModel.multiplication_contraction
    second.actual_contraction first.actual_contraction
  target_contraction := errorModel.multiplication_contraction
    second.target_contraction first.target_contraction
  correct := by
    rw [Circuit.denote_seq]
    exact errorModel.multiplication first.correct second.correct
      first.error_nonnegative second.error_nonnegative
      first.actual_contraction second.target_contraction

/-- 近似作用素componentの構文的逆は同じ誤差で共役転置targetを近似する。 -/
def reverse
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {errorModel : OperatorErrorModel basis}
    (inverseGate : Gate → Gate)
    (inverseCorrect : ∀ gate,
      gateOperator (inverseGate gate) = Matrix.conjTranspose (gateOperator gate))
    (adjointContraction : ∀ {operator}, errorModel.isContraction operator →
      errorModel.isContraction (Matrix.conjTranspose operator))
    (adjointApprox : ∀ {actual target error},
      errorModel.approx actual target error →
        errorModel.approx (Matrix.conjTranspose actual)
          (Matrix.conjTranspose target) error)
    (component : ApproxOperatorComponent gateOperator errorModel) :
    ApproxOperatorComponent gateOperator errorModel where
  circuit := component.circuit.reverse inverseGate
  target := Matrix.conjTranspose component.target
  error := component.error
  error_nonnegative := component.error_nonnegative
  actual_contraction := by
    rw [Circuit.denote_reverse inverseGate gateOperator inverseCorrect]
    exact adjointContraction component.actual_contraction
  target_contraction := adjointContraction component.target_contraction
  correct := by
    rw [Circuit.denote_reverse inverseGate gateOperator inverseCorrect]
    exact adjointApprox component.correct

/-- contraction作用素の自然数冪もcontractionである。 -/
theorem contraction_pow
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (errorModel : OperatorErrorModel basis) {operator : Operator basis}
    (contraction : errorModel.isContraction operator) :
    ∀ count : Nat, errorModel.isContraction (operator ^ count)
  | 0 => by simpa using errorModel.identity_contraction
  | count + 1 => by
      rw [pow_succ]
      exact errorModel.multiplication_contraction
        (contraction_pow errorModel contraction count) contraction

/-- 同一近似componentの反復では誤差上限が回数に比例する。 -/
def «repeat»
    {Gate basis : Type*} [Fintype basis] [DecidableEq basis]
    {gateOperator : Gate → Operator basis}
    {errorModel : OperatorErrorModel basis}
    (count : Nat) (component : ApproxOperatorComponent gateOperator errorModel) :
    ApproxOperatorComponent gateOperator errorModel where
  circuit := .repeat count component.circuit
  target := component.target ^ count
  error := (count : ℝ) * component.error
  error_nonnegative := mul_nonneg (Nat.cast_nonneg _) component.error_nonnegative
  actual_contraction := by
    rw [Circuit.denote_repeat]
    exact contraction_pow errorModel component.actual_contraction count
  target_contraction := contraction_pow errorModel component.target_contraction count
  correct := by
    rw [Circuit.denote_repeat]
    induction count with
    | zero => simpa using errorModel.refl 1
    | succ count inductionHypothesis =>
        have step := errorModel.multiplication component.correct inductionHypothesis
          component.error_nonnegative (mul_nonneg (Nat.cast_nonneg _) component.error_nonnegative)
          component.actual_contraction
          (contraction_pow errorModel component.target_contraction count)
        simpa [pow_succ, Nat.cast_add, add_mul, add_comm] using step

end ApproxOperatorComponent

end

end VerifiedCircuitCore
