import QLean.Generator.Analysis.PrimitiveBasisReferences
import QLean.Generator.Analysis.AngleExpr
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Q基本ゲートの回路非依存な解析作用素

局所X・Ryとwire埋込み、CNOT・Toffoliの置換行列を回路ASTから独立に定義する。
-/

open Matrix

namespace ProbabilityGeneratorQProof

noncomputable section

/-- パウリXゲートの複素行列表現。 -/
def xMatrix : Operator Bool :=
  Matrix.of fun output input => if output = !input then 1 else 0

/-- 実角度を持つ量子ビット回転`Ry(angle)`の複素行列表現。 -/
def ryMatrix (angle : ℝ) : Operator Bool :=
  Matrix.of fun output input =>
    match output, input with
    | false, false => (Real.cos (angle / 2) : ℂ)
    | false, true  => -(Real.sin (angle / 2) : ℂ)
    | true, false  => (Real.sin (angle / 2) : ℂ)
    | true, true   => (Real.cos (angle / 2) : ℂ)

/-- 指定ワイヤと、それ以外の全ワイヤへ計算基底を分解する同値。 -/
def splitWireEquiv {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits ≃
      Bool × ({wire : Wire ancillaQubits systemQubits // wire ≠ target} → Bool) where
  toFun basis := (basis target, fun wire => basis wire.1)
  invFun pair := fun wire =>
    if equal : wire = target then pair.1 else pair.2 ⟨wire, equal⟩
  left_inv basis := by
    funext wire
    by_cases equal : wire = target
    · subst wire
      simp
    · simp [equal]
  right_inv pair := by
    apply Prod.ext
    · simp
    · funext wire
      simp [wire.2]

/-- 一量子ビット作用素を、指定ワイヤへ作用する全体作用素として埋め込む。 -/
def onWire {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (A : Operator Bool) :
    Operator (JointBasis ancillaQubits systemQubits) :=
  Matrix.reindex (splitWireEquiv target).symm (splitWireEquiv target).symm
    (Matrix.kronecker A
      (1 : Operator ({wire : Wire ancillaQubits systemQubits // wire ≠ target} → Bool)))

/-- 型安全に指定された制御・標的ワイヤ上のCNOT行列。 -/
def cnotMatrix {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target) :
    Operator (JointBasis ancillaQubits systemQubits) :=
  (cnotBasisEquiv control target different).permMatrix ℂ

/-- 型安全に指定された三ワイヤ上のToffoli置換行列。 -/
def toffoliMatrix {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (controlsDifferent : control₁ ≠ control₂)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target) :
    Operator (JointBasis ancillaQubits systemQubits) :=
  (toffoliBasisEquiv control₁ control₂ target controlsDifferent
    firstDifferent secondDifferent).permMatrix ℂ

end

end ProbabilityGeneratorQProof
