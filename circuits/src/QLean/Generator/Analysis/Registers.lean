import QLean.Generator.Analysis.LinearAlgebra

/-!
# Q回路の型安全なアンシラ・system register

アンシラ量子ビット数とsystem量子ビット数を型添字に保持し、各wireの所属まで型で表す。
このlayoutはQ固有なので共有coreへ押し上げない。
-/

namespace ProbabilityGeneratorQProof

/-- `n`量子ビットregisterの計算基底。 -/
abbrev RegisterBasis (n : Nat) := Fin n → Bool

/-- アンシラとsystemを区別した型安全なwire番号。 -/
inductive Wire (ancillaQubits systemQubits : Nat) where
  | ancilla (index : Fin ancillaQubits)
  | system (index : Fin systemQubits)
deriving DecidableEq, Repr

/-- Q固有wireと二つのregister添字の直和との同値。 -/
def wireEquivSum (ancillaQubits systemQubits : Nat) :
    Wire ancillaQubits systemQubits ≃ Fin ancillaQubits ⊕ Fin systemQubits where
  toFun
    | .ancilla index => Sum.inl index
    | .system index => Sum.inr index
  invFun
    | Sum.inl index => .ancilla index
    | Sum.inr index => .system index
  left_inv wire := by cases wire <;> rfl
  right_inv index := by cases index <;> rfl

/-- 有限な二registerからなるQ wire型の有限型instance。 -/
instance wireFintype (ancillaQubits systemQubits : Nat) :
    Fintype (Wire ancillaQubits systemQubits) :=
  Fintype.ofEquiv (Fin ancillaQubits ⊕ Fin systemQubits)
    (wireEquivSum ancillaQubits systemQubits).symm

/-- 全Q wireの計算基底。 -/
abbrev JointBasis (ancillaQubits systemQubits : Nat) :=
  Wire ancillaQubits systemQubits → Bool

/-- アンシラ基底とsystem基底を結合基底へまとめる。 -/
def combineBasis {ancillaQubits systemQubits : Nat}
    (ancilla : RegisterBasis ancillaQubits)
    (system : RegisterBasis systemQubits) :
    JointBasis ancillaQubits systemQubits
  | .ancilla index => ancilla index
  | .system index => system index

/-- 結合基底からアンシラ部分を読む。 -/
def ancillaPart {ancillaQubits systemQubits : Nat}
    (basis : JointBasis ancillaQubits systemQubits) :
    RegisterBasis ancillaQubits :=
  fun index => basis (.ancilla index)

/-- 結合基底からsystem部分を読む。 -/
def systemPart {ancillaQubits systemQubits : Nat}
    (basis : JointBasis ancillaQubits systemQubits) :
    RegisterBasis systemQubits :=
  fun index => basis (.system index)

/-- 結合基底を部分へ分解して再結合すると元へ戻る。 -/
@[simp] theorem combine_parts {ancillaQubits systemQubits : Nat}
    (basis : JointBasis ancillaQubits systemQubits) :
    combineBasis (ancillaPart basis) (systemPart basis) = basis := by
  funext wire
  cases wire <;> rfl

/-- 結合した基底からアンシラ部分を読むと元の値になる。 -/
@[simp] theorem ancillaPart_combine {ancillaQubits systemQubits : Nat}
    (ancilla : RegisterBasis ancillaQubits)
    (system : RegisterBasis systemQubits) :
    ancillaPart (combineBasis ancilla system) = ancilla := by
  rfl

/-- 結合した基底からsystem部分を読むと元の値になる。 -/
@[simp] theorem systemPart_combine {ancillaQubits systemQubits : Nat}
    (ancilla : RegisterBasis ancillaQubits)
    (system : RegisterBasis systemQubits) :
    systemPart (combineBasis ancilla system) = system := by
  rfl

/-- 二registerの直積基底とQ結合基底との同値。 -/
def productBasisEquiv (ancillaQubits systemQubits : Nat) :
    (RegisterBasis ancillaQubits × RegisterBasis systemQubits) ≃
      JointBasis ancillaQubits systemQubits where
  toFun pair := combineBasis pair.1 pair.2
  invFun basis := (ancillaPart basis, systemPart basis)
  left_inv pair := by rcases pair with ⟨ancilla, system⟩; rfl
  right_inv basis := combine_parts basis

/-- 指定wireのbitを読む。 -/
def readWire {ancillaQubits systemQubits : Nat}
    (wire : Wire ancillaQubits systemQubits)
    (basis : JointBasis ancillaQubits systemQubits) : Bool :=
  basis wire

/-- 指定wireだけを新しいbit値へ更新する。 -/
def writeWire {ancillaQubits systemQubits : Nat}
    (wire : Wire ancillaQubits systemQubits)
    (value : Bool)
    (basis : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  Function.update basis wire value

/-- 更新したwireを読むと書き込んだ値になる。 -/
@[simp] theorem readWire_write_same {ancillaQubits systemQubits : Nat}
    (wire : Wire ancillaQubits systemQubits)
    (value : Bool)
    (basis : JointBasis ancillaQubits systemQubits) :
    readWire wire (writeWire wire value basis) = value := by
  simp [readWire, writeWire]

/-- 更新対象でないwireは保存される。 -/
@[simp] theorem readWire_write_other {ancillaQubits systemQubits : Nat}
    (wire other : Wire ancillaQubits systemQubits)
    (value : Bool)
    (basis : JointBasis ancillaQubits systemQubits)
    (different : other ≠ wire) :
    readWire other (writeWire wire value basis) = readWire other basis := by
  simp [readWire, writeWire, different]

/-- 任意幅アンシラを全て`|0⟩`とする成功基底。 -/
def allZeroAncilla (ancillaQubits : Nat) : RegisterBasis ancillaQubits :=
  fun _ => false

end ProbabilityGeneratorQProof
