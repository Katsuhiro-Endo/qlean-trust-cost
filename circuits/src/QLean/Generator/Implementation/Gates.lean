import QLean.Generator.Implementation.QubitBlockEncoding
import QLean.Generator.Analysis.PrimitiveBasisReferences
import QLean.Generator.Analysis.PrimitiveOperators
import QLean.Circuits.Foundation.PrimitiveGateProofs
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic

/-!
# 型安全な基本量子ゲート

任意個数のアンシラ・システム量子ビットに対し、対象ワイヤを`Wire`で指定する。
一量子ビットゲートは指定ワイヤと残りのワイヤへ基底を分解し、クロネッカー積で
全ヒルベルト空間へ埋め込む。CNOTは計算基底の置換行列として定義する。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

/-- パウリX行列がユニタリであることを示す。 -/
theorem xMatrix_mem_unitaryGroup :
    xMatrix ∈ Matrix.unitaryGroup Bool ℂ := by
  change VerifiedCircuitCore.localX ∈ Matrix.unitaryGroup Bool ℂ
  exact VerifiedCircuitCore.localX_mem_unitaryGroup

/-- 任意の実角度に対する`Ry`行列がユニタリであることを示す。 -/
theorem ryMatrix_mem_unitaryGroup (angle : ℝ) :
    ryMatrix angle ∈ Matrix.unitaryGroup Bool ℂ := by
  change VerifiedCircuitCore.localRy angle ∈ Matrix.unitaryGroup Bool ℂ
  exact VerifiedCircuitCore.localRy_mem_unitaryGroup angle

/-- 行列の添字を同値で付け替えてもユニタリ性が保存される。 -/
theorem reindex_mem_unitaryGroup
    {oldBasis newBasis : Type*}
    [Fintype oldBasis] [DecidableEq oldBasis]
    [Fintype newBasis] [DecidableEq newBasis]
    (equiv : oldBasis ≃ newBasis)
    {U : Operator oldBasis}
    (unitary : U ∈ Matrix.unitaryGroup oldBasis ℂ) :
    Matrix.reindex equiv equiv U ∈ Matrix.unitaryGroup newBasis ℂ :=
  VerifiedCircuitCore.reindex_mem_unitaryGroup equiv unitary

-- 定義本体は回路非依存な`Analytic.PrimitiveOperators`に置く。

-- 定義本体は回路非依存な`Analytic.PrimitiveOperators`に置く。

/-- 二つの計算基底が、指定ワイヤ以外のすべてのワイヤで一致するという条件。 -/
def SameOutside {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (output input : JointBasis ancillaQubits systemQubits) : Prop :=
  ∀ wire, wire ≠ target → output wire = input wire

/-- 有限個のワイヤ上の`SameOutside`条件は決定可能である。 -/
instance sameOutsideDecidable
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (output input : JointBasis ancillaQubits systemQubits) :
    Decidable (SameOutside target output input) := by
  unfold SameOutside
  infer_instance

/-- 指定ワイヤ以外への制限関数の等式は、`SameOutside`と同値である。 -/
theorem restrictedBasis_eq_iff_sameOutside
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (output input : JointBasis ancillaQubits systemQubits) :
    (fun wire : {wire : Wire ancillaQubits systemQubits // wire ≠ target} =>
        output wire.1) =
      (fun wire : {wire : Wire ancillaQubits systemQubits // wire ≠ target} =>
        input wire.1) ↔
      SameOutside target output input := by
  constructor
  · intro equal wire different
    exact congrFun equal ⟨wire, different⟩
  · intro equal
    funext wire
    exact equal wire.1 wire.2

/-- 任意ワイヤへ埋め込んだ一量子ビット作用素の行列要素を局所的に評価する。 -/
theorem onWire_apply
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (A : Operator Bool)
    (output input : JointBasis ancillaQubits systemQubits) :
    onWire target A output input =
      if SameOutside target output input then
        A (output target) (input target)
      else 0 := by
  change
    A (output target) (input target) *
        (if
          (fun wire : {wire : Wire ancillaQubits systemQubits // wire ≠ target} =>
              output wire.1) =
            (fun wire : {wire : Wire ancillaQubits systemQubits // wire ≠ target} =>
              input wire.1)
          then 1 else 0) =
      if SameOutside target output input then
        A (output target) (input target)
      else 0
  by_cases equal : SameOutside target output input
  · have restricted :
        (fun wire : {wire : Wire ancillaQubits systemQubits // wire ≠ target} =>
            output wire.1) =
          (fun wire : {wire : Wire ancillaQubits systemQubits // wire ≠ target} =>
            input wire.1) :=
      (restrictedBasis_eq_iff_sameOutside target output input).2 equal
    simp [equal, restricted]
  · have restricted :
        (fun wire : {wire : Wire ancillaQubits systemQubits // wire ≠ target} =>
            output wire.1) ≠
          (fun wire : {wire : Wire ancillaQubits systemQubits // wire ≠ target} =>
            input wire.1) := by
      intro restrictedEqual
      exact equal
        ((restrictedBasis_eq_iff_sameOutside target output input).1 restrictedEqual)
    simp [equal, restricted]

/-- ユニタリな一量子ビット作用素を任意ワイヤへ埋め込んでもユニタリである。 -/
theorem onWire_mem_unitaryGroup
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (A : Operator Bool)
    (unitary : A ∈ Matrix.unitaryGroup Bool ℂ) :
    onWire target A ∈
      Matrix.unitaryGroup (JointBasis ancillaQubits systemQubits) ℂ := by
  apply reindex_mem_unitaryGroup (splitWireEquiv target).symm
  exact Matrix.kronecker_mem_unitary unitary (Submonoid.one_mem _)

-- 定義本体は回路非依存な`Analytic.PrimitiveOperators`に置く。

/-- 任意の有限基底上の置換行列がユニタリであることを示す。 -/
theorem permMatrix_mem_unitaryGroup
    {basis : Type*} [Fintype basis] [DecidableEq basis]
    (permutation : Equiv.Perm basis) :
    permutation.permMatrix ℂ ∈ Matrix.unitaryGroup basis ℂ :=
  VerifiedCircuitCore.permMatrix_mem_unitaryGroup permutation

/-- 型安全なCNOT行列がユニタリであることを示す。 -/
theorem cnotMatrix_mem_unitaryGroup
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target) :
    cnotMatrix control target different ∈
      Matrix.unitaryGroup (JointBasis ancillaQubits systemQubits) ℂ :=
  permMatrix_mem_unitaryGroup (cnotBasisEquiv control target different)

end
end ProbabilityGeneratorQProof
