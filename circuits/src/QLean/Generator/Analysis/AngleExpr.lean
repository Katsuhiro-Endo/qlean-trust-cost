import QLean.Generator.Analysis.LinearAlgebra

/-!
# 回路非依存な記号角度

理想回転の解析仕様とexportの双方で使う、実行可能な実数式構文木を定義する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 厳密な意味論と外部出力の両方に使える、実行可能な回転角の構文木。 -/
inductive AngleExpr where
  | rational (value : ℚ)
  | pi
  | sqrt (value : AngleExpr)
  | acos (value : AngleExpr)
  | add (left right : AngleExpr)
  | mul (left right : AngleExpr)
  | neg (value : AngleExpr)
deriving DecidableEq, Repr

namespace AngleExpr

/-- 記号角度を厳密な実数として解釈する。 -/
def toReal : AngleExpr → ℝ
  | .rational value => value
  | .pi => Real.pi
  | .sqrt value => Real.sqrt value.toReal
  | .acos value => Real.arccos value.toReal
  | .add left right => left.toReal + right.toReal
  | .mul left right => left.toReal * right.toReal
  | .neg value => -value.toReal

/-- 記号角度の否定を実数化すると、実数化した角度の否定になる。 -/
@[simp] theorem toReal_neg (angle : AngleExpr) :
    (AngleExpr.neg angle).toReal = -angle.toReal := by
  rfl

/-- 記号角度を2で割る実行可能な構文木。 -/
def half (angle : AngleExpr) : AngleExpr :=
  .mul (.rational (1 / 2)) angle

/-- 記号角度を2倍する実行可能な構文木。 -/
def twice (angle : AngleExpr) : AngleExpr :=
  .mul (.rational 2) angle

/-- `half`の厳密実数意味は元の角度の半分である。 -/
@[simp] theorem toReal_half (angle : AngleExpr) :
    angle.half.toReal = angle.toReal / 2 := by
  simp [half, AngleExpr.toReal]
  ring

/-- `twice`の厳密実数意味は元の角度の2倍である。 -/
@[simp] theorem toReal_twice (angle : AngleExpr) :
    angle.twice.toReal = 2 * angle.toReal := by
  simp [twice, AngleExpr.toReal]

end AngleExpr

end

end ProbabilityGeneratorQProof
