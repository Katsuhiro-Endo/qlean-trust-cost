import QLean.Generator.Analysis.Registers
import Mathlib.Tactic

/-!
# 古典基本ゲートの回路非依存な基底参照作用

X・CNOT・Toffoliを計算基底上の純粋関数と置換として定義する。
-/

namespace ProbabilityGeneratorQProof

/-- Xが計算基底に作用した結果を、指定ワイヤだけの反転として定義する。 -/
def xBasisAction {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (basis : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  fun wire => if wire = target then !(basis wire) else basis wire

/-- Xの基底作用を二回行うと元に戻る。 -/
theorem xBasisAction_involutive
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (basis : JointBasis ancillaQubits systemQubits) :
    xBasisAction target (xBasisAction target basis) = basis := by
  funext wire
  by_cases isTarget : wire = target
  · subst wire
    simp [xBasisAction]
  · simp [xBasisAction, isTarget]

/-- X作用を左辺へ移すことと右辺へ移すことは同値である。 -/
theorem xBasisAction_eq_iff
    {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits)
    (left right : JointBasis ancillaQubits systemQubits) :
    xBasisAction target left = right ↔ left = xBasisAction target right := by
  constructor
  · intro equal
    have mapped := congrArg (xBasisAction target) equal
    simpa [xBasisAction_involutive] using mapped
  · intro equal
    rw [equal]
    exact xBasisAction_involutive target right

/-- Xの計算基底作用を自己逆な基底置換として束ねる。 -/
def xBasisEquiv {ancillaQubits systemQubits : Nat}
    (target : Wire ancillaQubits systemQubits) :
    Equiv.Perm (JointBasis ancillaQubits systemQubits) where
  toFun := xBasisAction target
  invFun := xBasisAction target
  left_inv := xBasisAction_involutive target
  right_inv := xBasisAction_involutive target

/-- CNOTが計算基底に作用した結果を、制御ビットに応じた標的ビット反転として定義する。 -/
def cnotBasisAction {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (basis : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  fun wire =>
    if basis control then
      if wire = target then !(basis wire) else basis wire
    else basis wire

/-- 制御ワイヤと標的ワイヤが異なるとき、CNOTの基底作用を2回行うと元に戻る。 -/
theorem cnotBasisAction_involutive
    {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target)
    (basis : JointBasis ancillaQubits systemQubits) :
    cnotBasisAction control target (cnotBasisAction control target basis) = basis := by
  funext wire
  by_cases enabled : basis control
  · by_cases isTarget : wire = target
    · subst wire
      simp [cnotBasisAction, enabled, different]
    · simp [cnotBasisAction, enabled, isTarget, different]
  · simp [cnotBasisAction, enabled]

/-- CNOTの計算基底作用を自己逆な基底置換として束ねる。 -/
def cnotBasisEquiv {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits)
    (different : control ≠ target) :
    Equiv.Perm (JointBasis ancillaQubits systemQubits) where
  toFun := cnotBasisAction control target
  invFun := cnotBasisAction control target
  left_inv := cnotBasisAction_involutive control target different
  right_inv := cnotBasisAction_involutive control target different

/-- Toffoliが計算基底に作用した結果を、二制御ANDによる標的反転として定義する。 -/
def toffoliBasisAction {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (basis : JointBasis ancillaQubits systemQubits) :
    JointBasis ancillaQubits systemQubits :=
  fun wire =>
    if basis control₁ && basis control₂ then
      if wire = target then !(basis wire) else basis wire
    else
      basis wire

/-- 三ワイヤが相異なるとき、Toffoliの基底作用を二回行うと元に戻る。 -/
theorem toffoliBasisAction_involutive
    {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (_controlsDifferent : control₁ ≠ control₂)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target)
    (basis : JointBasis ancillaQubits systemQubits) :
    toffoliBasisAction control₁ control₂ target
        (toffoliBasisAction control₁ control₂ target basis) = basis := by
  funext wire
  by_cases firstEnabled : basis control₁
  · by_cases secondEnabled : basis control₂
    · by_cases isTarget : wire = target
      · subst wire
        simp [toffoliBasisAction, firstEnabled, secondEnabled,
          firstDifferent, secondDifferent]
      · simp [toffoliBasisAction, firstEnabled, secondEnabled, isTarget,
          firstDifferent, secondDifferent]
    · simp [toffoliBasisAction, firstEnabled, secondEnabled]
  · simp [toffoliBasisAction, firstEnabled]

/-- Toffoliの計算基底作用を自己逆な基底置換として束ねる。 -/
def toffoliBasisEquiv {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits)
    (controlsDifferent : control₁ ≠ control₂)
    (firstDifferent : control₁ ≠ target)
    (secondDifferent : control₂ ≠ target) :
    Equiv.Perm (JointBasis ancillaQubits systemQubits) where
  toFun := toffoliBasisAction control₁ control₂ target
  invFun := toffoliBasisAction control₁ control₂ target
  left_inv := toffoliBasisAction_involutive control₁ control₂ target
    controlsDifferent firstDifferent secondDifferent
  right_inv := toffoliBasisAction_involutive control₁ control₂ target
    controlsDifferent firstDifferent secondDifferent

end ProbabilityGeneratorQProof
