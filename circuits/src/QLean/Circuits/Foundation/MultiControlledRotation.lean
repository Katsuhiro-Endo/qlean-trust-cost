import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.UniformPreparationAnalytic

/-!
# 多重Bool制御回転の基本ゲートcompiler

任意本数のBool制御を、X/CNOT/Toffoliと一量子bit RyだけからなるcleanなAND鎖へ
分解する。不正なwire配置では型安全な全域constructorが恒等回路を返す。
-/

namespace VerifiedCircuitCore

namespace Circuit

/-- 二wireが異なる場合だけCNOTを生成する型安全な全域constructor。 -/
def safeCnot {qubits : Nat} (control target : Fin qubits) :
    Circuit (PrimitiveGate qubits) :=
  if different : control ≠ target then .gate (.cnot control target different)
  else .identity

/-- 三wireが相異なる場合だけToffoliを生成する型安全な全域constructor。 -/
def safeToffoli {qubits : Nat} (control₀ control₁ target : Fin qubits) :
    Circuit (PrimitiveGate qubits) :=
  if controlsDifferent : control₀ ≠ control₁ then
    if firstDifferent : control₀ ≠ target then
      if secondDifferent : control₁ ≠ target then
        .gate (.toffoli control₀ control₁ target controlsDifferent
          firstDifferent secondDifferent)
      else .identity
    else .identity
  else .identity

/-- 記号角度を厳密に二分する。 -/
def halfAngle (angle : AngleExpr) : AngleExpr :=
  .div angle (.rational 2 1 (by decide))

/-- 一制御Ryを二つの半角Ryと二つのCNOTへ分解した基本ゲート回路。 -/
def controlledRyMacroExpansion {qubits : Nat}
    (control target : Fin qubits) (different : control ≠ target)
    (angle : AngleExpr) : Circuit (PrimitiveGate qubits) :=
  Circuit.fromList [
    .ry (halfAngle angle) target,
    .cnot control target different,
    .ry (.neg (halfAngle angle)) target,
    .cnot control target different]

/-- Bool制御値が零のwireだけを前後で反転するX列。 -/
def invertZeroControls {qubits : Nat}
    (controls : List (Fin qubits × Bool)) : Circuit (PrimitiveGate qubits) :=
  Circuit.fromList <| controls.filterMap fun control =>
    if control.2 then none else some (.x control.1)

/-- 既計算ANDを延長し、最後にRyを適用して同じToffoli列を逆計算する。 -/
def andChainControlledRy {qubits : Nat} (previous : Fin qubits) :
    List (Fin qubits) → List (Fin qubits) → Fin qubits → AngleExpr →
      Circuit (PrimitiveGate qubits)
  | [], _, target, angle =>
      if different : previous ≠ target then
        controlledRyMacroExpansion previous target different angle
      else .identity
  | control :: controls, scratch :: scratches, target, angle =>
      let step := safeToffoli previous control scratch
      .seq step <| .seq
        (andChainControlledRy scratch controls scratches target angle) step
  | _ :: _, [], _, _ => .identity

/-- 正制御ANDをscratchへ計算し、最終AND bitでRyを制御して逆計算する。 -/
def positiveMultiControlledRy {qubits : Nat} :
    List (Fin qubits) → List (Fin qubits) → Fin qubits → AngleExpr →
      Circuit (PrimitiveGate qubits)
  | [], _, target, angle => .gate (.ry angle target)
  | [control], _, target, angle =>
      if different : control ≠ target then
        controlledRyMacroExpansion control target different angle
      else .identity
  | control₀ :: control₁ :: controls, scratch :: scratches, target, angle =>
      let first := safeToffoli control₀ control₁ scratch
      let use : Circuit (PrimitiveGate qubits) :=
        match controls, scratches with
        | [], _ =>
            if different : scratch ≠ target then
              controlledRyMacroExpansion scratch target different angle
            else .identity
        | _, _ => andChainControlledRy scratch controls scratches target angle
      .seq first <| .seq use first
  | _ :: _ :: _, [], _, _ => .identity

/-- Bool値付き制御を零制御Xと正制御AND鎖へ分解した多重制御Ry。 -/
def boolMultiControlledRy {qubits : Nat}
    (controls : List (Fin qubits × Bool)) (scratch : List (Fin qubits))
    (target : Fin qubits) (angle : AngleExpr) : Circuit (PrimitiveGate qubits) :=
  let invert := invertZeroControls controls
  let controlled :=
    positiveMultiControlledRy (controls.map Prod.fst) scratch target angle
  .seq invert <| .seq controlled invert

end Circuit

end VerifiedCircuitCore
