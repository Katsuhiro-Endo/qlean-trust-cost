import QLean.Circuits.Foundation.UniformPreparationAttachedPlan
import QLean.Circuits.Foundation.PrimitiveOperatorSemantics

/-!
# 任意サイズ一様準備compilerの回路非依存full-space作用素

dirty scratchを含む全計算基底上の作用を、局所行列、基底置換、および実行順作用素積
だけで定義する。実装ASTやその意味論は参照しない。
-/

namespace VerifiedCircuitCore

noncomputable section

/-- 一制御Ry compilerで使う厳密な半角式。 -/
def uniformHalfAngle (angle : AngleExpr) : AngleExpr :=
  .div angle (.rational 2 1 (by decide))

/-- 型安全性検査を含むCNOT compilerの独立作用素。 -/
def uniformSafeCnotAnalyticOperator {qubits : Nat}
    (control target : Fin qubits) : Operator (QubitBasis qubits) :=
  if _different : control ≠ target then
    deterministicOperator fun input => xorWire target (input control) input
  else 1

/-- 型安全性検査を含むToffoli compilerの独立作用素。 -/
def uniformSafeToffoliAnalyticOperator {qubits : Nat}
    (control₀ control₁ target : Fin qubits) : Operator (QubitBasis qubits) :=
  if _controlsDifferent : control₀ ≠ control₁ then
    if _firstDifferent : control₀ ≠ target then
      if _secondDifferent : control₁ ≠ target then
        deterministicOperator fun input =>
          xorWire target (input control₀ && input control₁) input
      else 1
    else 1
  else 1

/-- 0-control前後反転列の独立作用素積。 -/
def uniformInvertZeroControlsAnalyticOperator {qubits : Nat}
    (controls : List (Fin qubits × Bool)) : Operator (QubitBasis qubits) :=
  operatorSequence <| controls.filterMap fun control =>
    if control.2 then none
    else some (embedSingleQubitOperator control.1 localX)

/-- 二つのCNOTと二つの半角Ryによる一制御Ry compilerの独立作用素積。 -/
def uniformControlledRyDecompositionAnalyticOperator {qubits : Nat}
    (control target : Fin qubits) (_different : control ≠ target)
    (angle : AngleExpr) : Operator (QubitBasis qubits) :=
  operatorSequence
    [embedSingleQubitOperator target
        (localRy ((uniformHalfAngle angle).eval fun _ => 0)),
      deterministicOperator fun input => xorWire target (input control) input,
      embedSingleQubitOperator target
        (localRy ((AngleExpr.neg (uniformHalfAngle angle)).eval fun _ => 0)),
      deterministicOperator fun input => xorWire target (input control) input]

/-- AND鎖を延長し、dirty scratchを復元する独立作用素積。 -/
def uniformAndChainControlledRyAnalyticOperator {qubits : Nat}
    (previous : Fin qubits) :
    List (Fin qubits) → List (Fin qubits) → Fin qubits → AngleExpr →
      Operator (QubitBasis qubits)
  | [], _, target, angle =>
      if different : previous ≠ target then
        uniformControlledRyDecompositionAnalyticOperator
          previous target different angle
      else 1
  | control :: controls, scratch :: scratches, target, angle =>
      let step := uniformSafeToffoliAnalyticOperator previous control scratch
      (step * uniformAndChainControlledRyAnalyticOperator
        scratch controls scratches target angle) * step
  | _ :: _, [], _, _ => 1

/-- 正制御AND鎖のdirty-work対応独立作用素積。 -/
def uniformPositiveMultiControlledRyAnalyticOperator {qubits : Nat} :
    List (Fin qubits) → List (Fin qubits) → Fin qubits → AngleExpr →
      Operator (QubitBasis qubits)
  | [], _, target, angle =>
      embedSingleQubitOperator target (localRy (angle.eval fun _ => 0))
  | [control], _, target, angle =>
      if different : control ≠ target then
        uniformControlledRyDecompositionAnalyticOperator
          control target different angle
      else 1
  | control₀ :: control₁ :: controls, scratch :: scratches, target, angle =>
      let first := uniformSafeToffoliAnalyticOperator control₀ control₁ scratch
      let use :=
        match controls, scratches with
        | [], _ =>
            if different : scratch ≠ target then
              uniformControlledRyDecompositionAnalyticOperator
                scratch target different angle
            else 1
        | _, _ => uniformAndChainControlledRyAnalyticOperator
            scratch controls scratches target angle
      (first * use) * first
  | _ :: _ :: _, [], _, _ => 1

/-- Bool制御反転と正制御AND鎖を含むdirty-work対応独立作用素。 -/
def uniformBoolMultiControlledRyAnalyticOperator {qubits : Nat}
    (controls : List (Fin qubits × Bool))
    (scratch : List (Fin qubits)) (target : Fin qubits)
    (angle : AngleExpr) : Operator (QubitBasis qubits) :=
  let invert := uniformInvertZeroControlsAnalyticOperator controls
  let controlled := uniformPositiveMultiControlledRyAnalyticOperator
    (controls.map Prod.fst) scratch target angle
  (invert * controlled) * invert

/-- local compiler全幅の前半にあるselector wireのpure割当て。 -/
def uniformPreparationAnalyticSelectorWire (width : Nat) (wire : Fin width) :
    Fin (2 * width) :=
  ⟨wire.val, by omega⟩

/-- local compiler全幅の後半にある1本のscratch wireのpure割当て。 -/
def uniformPreparationAnalyticScratchWire (width : Nat) (wire : Fin width) :
    Fin (2 * width) :=
  ⟨width + wire.val, by omega⟩

/-- local compiler全幅の後半にあるscratch wireのpure割当て。 -/
def uniformPreparationAnalyticScratchWires (width : Nat) :
    List (Fin (2 * width)) :=
  (List.finRange width).map (uniformPreparationAnalyticScratchWire width)

/-- 証明付き一様準備命令列のdirty-work対応独立作用素積。 -/
def uniformPreparationPlanFullAnalyticOperator
    (width : Nat)
    (plan : List {instruction : UniformRotationInstruction //
      instruction.WellFormed width}) :
    Operator (QubitBasis (2 * width)) :=
  operatorSequence <| plan.map fun instruction =>
    uniformBoolMultiControlledRyAnalyticOperator
      (instruction.1.controls.attach.map fun control =>
        (uniformPreparationAnalyticSelectorWire width
          ⟨control.1.1, instruction.2.2.1 control.1 control.2⟩,
          control.1.2))
      (uniformPreparationAnalyticScratchWires width)
      (uniformPreparationAnalyticSelectorWire width
        ⟨instruction.1.target, instruction.2.1⟩)
      instruction.1.angle

/-- 任意`0 < N ≤ 2^w`の一様準備compilerが全物理基底上で表す独立作用素。 -/
def uniformPreparationFullAnalyticOperator
    (parameters : UniformPreparationParameters) :
    Operator (QubitBasis (2 * parameters.width)) :=
  uniformPreparationPlanFullAnalyticOperator parameters.width
    (attachedUniformRotationPlan parameters.width parameters.validCount
      parameters.validCountLeCapacity)

end

end VerifiedCircuitCore
