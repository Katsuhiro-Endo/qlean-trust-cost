import QLean.Generator.Implementation.CoreCircuitEmbedding

/-!
# Q wire埋込みの基底・作用素意味論

Q固有 `JointBasis` と共有coreの標準 `QubitBasis` を同一視し、基本gateおよび回路の
denotation保存を証明する。任意の大registerへ持ち上げる場合は、外部wireを固定した
部分空間としてこの標準幅定理を再利用する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 標準数値wireをancilla/system所属付きwireへ戻す。 -/
def canonicalFinToWire {ancillaQubits systemQubits : Nat}
    (index : Fin (ancillaQubits + systemQubits)) :
    Wire ancillaQubits systemQubits :=
  if ancilla : index.val < ancillaQubits then
    .ancilla ⟨index.val, ancilla⟩
  else
    .system ⟨index.val - ancillaQubits, by omega⟩

/-- Q wireを標準数値化して戻すと元のwireになる。 -/
@[simp] theorem canonicalFinToWire_wireToCanonicalFin
    {ancillaQubits systemQubits : Nat}
    (wire : Wire ancillaQubits systemQubits) :
    canonicalFinToWire (wireToCanonicalFin wire) = wire := by
  cases wire with
  | ancilla index =>
      simp [canonicalFinToWire, wireToCanonicalFin, index.isLt]
  | system index =>
      simp [canonicalFinToWire, wireToCanonicalFin]

/-- 標準数値wireを所属付きwireへ戻して再数値化すると元へ戻る。 -/
@[simp] theorem wireToCanonicalFin_canonicalFinToWire
    {ancillaQubits systemQubits : Nat}
    (index : Fin (ancillaQubits + systemQubits)) :
    wireToCanonicalFin (canonicalFinToWire index) = index := by
  by_cases ancilla : index.val < ancillaQubits
  · simp [canonicalFinToWire, ancilla, wireToCanonicalFin]
  · simp [canonicalFinToWire, ancilla, wireToCanonicalFin, Fin.ext_iff]
    omega

/-- Q結合基底を、同じbit配置を持つ共有core標準基底へ移す。 -/
def jointBasisToCore {ancillaQubits systemQubits : Nat}
    (basis : JointBasis ancillaQubits systemQubits) :
    VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits) :=
  fun index => basis (canonicalFinToWire index)

/-- 共有core標準基底をQ結合基底へ戻す。 -/
def coreBasisToJoint {ancillaQubits systemQubits : Nat}
    (basis : VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits)) :
    JointBasis ancillaQubits systemQubits :=
  fun wire => basis (wireToCanonicalFin wire)

/-- Q結合基底と共有core標準基底の同値。 -/
def jointBasisCoreEquiv (ancillaQubits systemQubits : Nat) :
    JointBasis ancillaQubits systemQubits ≃
      VerifiedCircuitCore.QubitBasis (ancillaQubits + systemQubits) where
  toFun := jointBasisToCore
  invFun := coreBasisToJoint
  left_inv basis := by
    funext wire
    simp [jointBasisToCore, coreBasisToJoint]
  right_inv basis := by
    funext index
    simp [jointBasisToCore, coreBasisToJoint]

/-- 基底移行後、元のQ wire位置のbitは保存される。 -/
@[simp] theorem jointBasisToCore_wireToCanonicalFin
    {ancillaQubits systemQubits : Nat}
    (basis : JointBasis ancillaQubits systemQubits)
    (wire : Wire ancillaQubits systemQubits) :
    jointBasisToCore basis (wireToCanonicalFin wire) = basis wire := by
  simp [jointBasisToCore]

/-- 一量子bit埋込みの「target以外一致」条件は標準基底移行で保存される。 -/
theorem agreesExcept_jointBasisToCore_iff
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (output input : JointBasis ancillaQubits systemQubits) :
    VerifiedCircuitCore.agreesExcept (wireToCanonicalFin target)
        (jointBasisToCore output) (jointBasisToCore input) ↔
      SameOutside target output input := by
  constructor
  · intro agree wire different
    have mappedDifferent : wireToCanonicalFin wire ≠ wireToCanonicalFin target :=
      fun equal => different (wireToCanonicalFin_injective equal)
    simpa using agree (wireToCanonicalFin wire) mappedDifferent
  · intro agree index different
    have sourceDifferent : canonicalFinToWire index ≠ target := by
      intro equal
      apply different
      calc
        index = wireToCanonicalFin (canonicalFinToWire index) :=
          (wireToCanonicalFin_canonicalFinToWire index).symm
        _ = wireToCanonicalFin target := congrArg wireToCanonicalFin equal
    exact agree (canonicalFinToWire index) sourceDifferent

end

end ProbabilityGeneratorQProof
