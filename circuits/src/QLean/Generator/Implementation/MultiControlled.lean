import QLean.Generator.Implementation.QuantumCombinators
import QLean.Generator.Analysis.UniformPreparationPlan

/-!
# 多重制御ゲートの基本ゲート分解

任意本数のBool制御を、`X`、`CNOT`、`Toffoli`だけからなるcleanなAND鎖へ分解する。
ANDの一時bitは使用後に逆計算される。ワイヤ相異性を実行時分岐で検査する全域な
constructorを使うため、不正な基本ゲートは構文上生成されない。
-/

namespace ProbabilityGeneratorQProof

namespace Circuit

/-- 二本のワイヤが異なる場合だけCNOTを生成する型安全な全域constructor。 -/
def safeCnot {ancillaQubits systemQubits : Nat}
    (control target : Wire ancillaQubits systemQubits) :
    Circuit (PrimitiveGate ancillaQubits systemQubits) :=
  if different : control ≠ target then
    .gate (.cnot control target different)
  else
    .identity

/-- 三本のワイヤが相異なる場合だけToffoliを生成する型安全な全域constructor。 -/
def safeToffoli {ancillaQubits systemQubits : Nat}
    (control₁ control₂ target : Wire ancillaQubits systemQubits) :
    Circuit (PrimitiveGate ancillaQubits systemQubits) :=
  if controlsDifferent : control₁ ≠ control₂ then
    if firstDifferent : control₁ ≠ target then
      if secondDifferent : control₂ ≠ target then
        .gate (.toffoli control₁ control₂ target controlsDifferent
          firstDifferent secondDifferent)
      else
        .identity
    else
      .identity
  else
    .identity

/-- Bool制御値が0のwireだけを前後で反転するX列。 -/
def invertZeroControls {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool)) :
    Circuit (PrimitiveGate ancillaQubits systemQubits) :=
  Circuit.fromList <| controls.filterMap fun control =>
    if control.2 then none else some (.x control.1)

/--
既に`previous`へ保持したANDへ残りの制御を順に掛け、最後にtargetを反転してから
同じToffoli列を逆順に実行するcleanな再帰鎖。
-/
def andChainUse {ancillaQubits systemQubits : Nat}
    (previous : Wire ancillaQubits systemQubits) :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Wire ancillaQubits systemQubits →
    Circuit (PrimitiveGate ancillaQubits systemQubits)
  | [], _, target => safeCnot previous target
  | control :: controls, scratch :: scratches, target =>
      let step := safeToffoli previous control scratch
      .seq step <| .seq (andChainUse scratch controls scratches target) step
  | _ :: _, [], _ => .identity

/--
全制御が1のときだけtargetを反転する多重制御X。制御0本はX、1本はCNOT、2本以上は
ToffoliのAND鎖を使い、必要なscratchが不足する場合は安全に恒等回路を返す。
-/
def positiveMultiControlledX {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Wire ancillaQubits systemQubits →
    Circuit (PrimitiveGate ancillaQubits systemQubits)
  | [], _, target => .gate (.x target)
  | [control], _, target => safeCnot control target
  | control₁ :: control₂ :: controls, scratch :: scratches, target =>
      let first := safeToffoli control₁ control₂ scratch
      .seq first <| .seq (andChainUse scratch controls scratches target) first
  | _ :: _ :: _, [], _ => .identity

/-- Bool値付き制御を0-control用Xと正制御AND鎖へ分解した多重制御X。 -/
def boolMultiControlledX {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    Circuit (PrimitiveGate ancillaQubits systemQubits) :=
  let invert := invertZeroControls controls
  let controlled := positiveMultiControlledX (controls.map Prod.fst) scratch target
  .seq invert <| .seq controlled invert

/-- AND鎖を延長して制御`Ry`を適用し、使用したscratchを再帰的に消去する。 -/
def andChainControlledRy {ancillaQubits systemQubits : Nat}
    (previous : Wire ancillaQubits systemQubits) :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Wire ancillaQubits systemQubits → AngleExpr →
    Circuit (PrimitiveGate ancillaQubits systemQubits)
  | [], _, target, angle =>
      if different : previous ≠ target then
        controlledRyCircuit previous target different angle
      else
        .identity
  | control :: controls, scratch :: scratches, target, angle =>
      let step := safeToffoli previous control scratch
      .seq step <| .seq
        (andChainControlledRy scratch controls scratches target angle) step
  | _ :: _, [], _, _ => .identity

/--
正制御ANDをscratchへ計算し、その最終bitで`Ry`を制御してからANDを逆計算する。
制御0本では通常の`Ry`、制御1本では二CNOT分解を直接使う。
-/
def positiveMultiControlledRy {ancillaQubits systemQubits : Nat} :
    List (Wire ancillaQubits systemQubits) →
    List (Wire ancillaQubits systemQubits) →
    Wire ancillaQubits systemQubits → AngleExpr →
    Circuit (PrimitiveGate ancillaQubits systemQubits)
  | [], _, target, angle => .gate (.ry target angle)
  | [control], _, target, angle =>
      if different : control ≠ target then
        controlledRyCircuit control target different angle
      else
        .identity
  | control₁ :: control₂ :: controls, scratch :: scratches, target, angle =>
      let first := safeToffoli control₁ control₂ scratch
      let use : Circuit (PrimitiveGate ancillaQubits systemQubits) :=
        match controls, scratches with
        | [], _ =>
            if different : scratch ≠ target then
              controlledRyCircuit scratch target different angle
            else
              .identity
        | _, _ => andChainControlledRy scratch controls scratches target angle
      .seq first <| .seq use first
  | _ :: _ :: _, [], _, _ => .identity

/-- Bool値付き制御を0-control用Xと正制御AND鎖へ分解した多重制御`Ry`。 -/
def boolMultiControlledRy {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) (angle : AngleExpr) :
    Circuit (PrimitiveGate ancillaQubits systemQubits) :=
  let invert := invertZeroControls controls
  let controlled := positiveMultiControlledRy (controls.map Prod.fst) scratch target angle
  .seq invert <| .seq controlled invert

/-- 多重制御Xの全葉は許可した五種類の基本ゲートだけである。 -/
theorem boolMultiControlledX_leaves
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) :
    ∀ gate ∈ (boolMultiControlledX controls scratch target).flatten,
      IsAllowedPrimitiveGate gate :=
  primitiveCircuit_allLeavesAllowed _

/-- 多重制御`Ry`の全葉は許可した五種類の基本ゲートだけである。 -/
theorem boolMultiControlledRy_leaves
    {ancillaQubits systemQubits : Nat}
    (controls : List (Wire ancillaQubits systemQubits × Bool))
    (scratch : List (Wire ancillaQubits systemQubits))
    (target : Wire ancillaQubits systemQubits) (angle : AngleExpr) :
    ∀ gate ∈ (boolMultiControlledRy controls scratch target angle).flatten,
      IsAllowedPrimitiveGate gate :=
  primitiveCircuit_allLeavesAllowed _

end Circuit

end ProbabilityGeneratorQProof
