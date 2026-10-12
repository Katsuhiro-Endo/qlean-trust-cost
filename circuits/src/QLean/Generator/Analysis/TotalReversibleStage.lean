import QLean.Generator.Analysis.PrimitiveBasisReferences
import QLean.Circuits.Foundation.Foundations
import QLean.Circuits.Foundation.PrimitiveOperatorSemantics

/-!
# 全dirty基底で意味を持つ可逆stage

回路実装とは独立に、X・CNOT・Toffoliの基底置換と、その実行順合成だけを記録する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 全基底上で意味を持つ一つの可逆命令。 -/
inductive TotalReversibleInstruction (ancillaQubits systemQubits : Nat) where
  /-- 一つのbitを反転する。 -/
  | xorOne (target : Wire ancillaQubits systemQubits)
  /-- 一つのcontrol bitをtargetへXORする。 -/
  | xorControlled
      (control target : Wire ancillaQubits systemQubits)
      (different : control ≠ target)
  /-- 二つのcontrolのANDをtargetへXORする。 -/
  | xorDoublyControlled
      (control₁ control₂ target : Wire ancillaQubits systemQubits)
      (controlsDifferent : control₁ ≠ control₂)
      (firstDifferent : control₁ ≠ target)
      (secondDifferent : control₂ ≠ target)

namespace TotalReversibleInstruction

/-- 一命令の回路非依存な計算基底置換。 -/
def reference {ancillaQubits systemQubits : Nat} :
    TotalReversibleInstruction ancillaQubits systemQubits →
      Equiv.Perm (JointBasis ancillaQubits systemQubits)
  | .xorOne target => xBasisEquiv target
  | .xorControlled control target different =>
      cnotBasisEquiv control target different
  | .xorDoublyControlled control₁ control₂ target controlsDifferent
      firstDifferent secondDifferent =>
      toffoliBasisEquiv control₁ control₂ target controlsDifferent
        firstDifferent secondDifferent

/-- 三種類の命令はいずれも自分自身が逆命令である。 -/
def reverse {ancillaQubits systemQubits : Nat} :
    TotalReversibleInstruction ancillaQubits systemQubits →
      TotalReversibleInstruction ancillaQubits systemQubits := id

/-- 一命令の解析置換は自己逆である。 -/
theorem reference_reverse {ancillaQubits systemQubits : Nat}
    (instruction : TotalReversibleInstruction ancillaQubits systemQubits) :
    reference instruction.reverse = (reference instruction)⁻¹ := by
  apply Equiv.ext
  intro input
  cases instruction <;> rfl

end TotalReversibleInstruction

/-- 可逆命令を実行順に階層合成する回路非依存stage。 -/
inductive TotalReversibleStage (ancillaQubits systemQubits : Nat) where
  /-- 何もしないstage。 -/
  | identity
  /-- 一命令だけのstage。 -/
  | instruction (value : TotalReversibleInstruction ancillaQubits systemQubits)
  /-- firstの後にsecondを実行する二項合成。 -/
  | seq (first second : TotalReversibleStage ancillaQubits systemQubits)
  /-- 同じstageを指定回数だけ実行する。 -/
  | repeat (count : Nat) (body : TotalReversibleStage ancillaQubits systemQubits)

namespace TotalReversibleStage

/-- stageが全基底上で与える解析置換。 -/
def reference {ancillaQubits systemQubits : Nat} :
    TotalReversibleStage ancillaQubits systemQubits →
      Equiv.Perm (JointBasis ancillaQubits systemQubits)
  | .identity => 1
  | .instruction value => value.reference
  | .seq first second => second.reference * first.reference
  | .repeat count body => body.reference ^ count

/-- stageを実行順に逆転する。 -/
def reverse {ancillaQubits systemQubits : Nat} :
    TotalReversibleStage ancillaQubits systemQubits →
      TotalReversibleStage ancillaQubits systemQubits
  | .identity => .identity
  | .instruction value => .instruction value.reverse
  | .seq first second => .seq second.reverse first.reverse
  | .repeat count body => .repeat count body.reverse

/-- stage列を左から右へ実行する二項木へまとめる。 -/
def sequence {ancillaQubits systemQubits : Nat} :
    List (TotalReversibleStage ancillaQubits systemQubits) →
      TotalReversibleStage ancillaQubits systemQubits
  | [] => .identity
  | first :: rest => .seq first (sequence rest)

/-- compute--use--reverse-computeを一つのstageへまとめる。 -/
def computeUseUncompute {ancillaQubits systemQubits : Nat}
    (compute use : TotalReversibleStage ancillaQubits systemQubits) :
    TotalReversibleStage ancillaQubits systemQubits :=
  .seq compute (.seq use compute.reverse)

/-- stage全体の回路非依存な置換行列作用素。 -/
def analyticOperator {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    Operator (JointBasis ancillaQubits systemQubits) :=
  stage.reference⁻¹.permMatrix ℂ

/-- The independent stage operator is the deterministic operator of its
forward pure reference action. -/
theorem analyticOperator_eq_deterministicReference
    {ancillaQubits systemQubits : Nat}
    (stage : TotalReversibleStage ancillaQubits systemQubits) :
    stage.analyticOperator = VerifiedCircuitCore.deterministicOperator stage.reference := by
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
  simp [analyticOperator, VerifiedCircuitCore.deterministicOperator, equivalence]

/-- Sequential pure stages compose their independent operators in execution order. -/
theorem analyticOperator_seq {ancillaQubits systemQubits : Nat}
    (first second : TotalReversibleStage ancillaQubits systemQubits) :
    (TotalReversibleStage.seq first second).analyticOperator =
      second.analyticOperator * first.analyticOperator := by
  change ((second.reference * first.reference)⁻¹).permMatrix ℂ =
    second.reference⁻¹.permMatrix ℂ * first.reference⁻¹.permMatrix ℂ
  rw [mul_inv_rev]
  rw [Matrix.permMatrix_mul]

/-- A pure stage sequence is the execution-order product of its child operators. -/
theorem analyticOperator_sequence {ancillaQubits systemQubits : Nat}
    (stages : List (TotalReversibleStage ancillaQubits systemQubits)) :
    (sequence stages).analyticOperator =
      VerifiedCircuitCore.operatorSequence (stages.map analyticOperator) := by
  induction stages with
  | nil => simp [sequence, analyticOperator, reference,
      VerifiedCircuitCore.operatorSequence]
  | cons first rest inductionHypothesis =>
      rw [sequence, analyticOperator_seq, inductionHypothesis]
      rfl

end TotalReversibleStage

end

end ProbabilityGeneratorQProof
