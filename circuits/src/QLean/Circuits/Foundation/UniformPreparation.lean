import QLean.Circuits.Foundation.MultiControlledRotation
import QLean.Circuits.Foundation.UniformPreparationAttachedPlan

/-!
# 任意サイズ一様状態準備の基本ゲートAST

local全幅`2w`の前半をselector、後半をAND scratchとして固定し、回路非依存な
二分木回転計画をX/Ry/CNOT/Toffoli列へコンパイルする。
-/

namespace VerifiedCircuitCore

/-- local全幅`2w`の前半にselector wireを型安全に埋め込む。 -/
def uniformPreparationSelectorWire (width : Nat) (wire : Fin width) :
    Fin (2 * width) :=
  ⟨wire.val, by omega⟩

/-- local全幅`2w`の後半にscratch wireを型安全に埋め込む。 -/
def uniformPreparationScratchWire (width : Nat) (wire : Fin width) :
    Fin (2 * width) :=
  ⟨width + wire.val, by omega⟩

/-- 一様準備compilerへ渡す全scratch wire列。 -/
def uniformPreparationScratchWires (width : Nat) : List (Fin (2 * width)) :=
  (List.finRange width).map (uniformPreparationScratchWire width)

/-- well-formed命令のtarget番号をlocal selector wireへ割り当てる。 -/
def uniformRotationInstructionTarget (width : Nat)
    (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) : Fin (2 * width) :=
  uniformPreparationSelectorWire width ⟨instruction.target, wellFormed.1⟩

/-- well-formed命令のBool制御をlocal selector wireへ割り当てる。 -/
def uniformRotationInstructionControls (width : Nat)
    (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    List (Fin (2 * width) × Bool) :=
  instruction.controls.attach.map fun control =>
    (uniformPreparationSelectorWire width
      ⟨control.1.1, wellFormed.2.1 control.1 control.2⟩,
      control.1.2)

/-- 一個のwell-formed回転命令を基本ゲートAND鎖へコンパイルする。 -/
def compileUniformRotationInstruction (width : Nat)
    (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed width) :
    Circuit (PrimitiveGate (2 * width)) :=
  Circuit.boolMultiControlledRy
    (uniformRotationInstructionControls width instruction wellFormed)
    (uniformPreparationScratchWires width)
    (uniformRotationInstructionTarget width instruction wellFormed)
    instruction.angle

/-- 任意`0<N≤2^w`の一様準備を実装するLean正本の基本ゲートAST。 -/
def uniformPreparationCircuit (parameters : UniformPreparationParameters) :
    Circuit (PrimitiveGate (2 * parameters.width)) :=
  Circuit.sequence <|
    (attachedUniformRotationPlan parameters.width parameters.validCount
      parameters.validCountLeCapacity).map fun instruction =>
      compileUniformRotationInstruction parameters.width instruction.1
        instruction.2

/-- 一様準備ASTの全葉はX/Ry/CNOT/Toffoliのいずれかである。 -/
def IsUniformPreparationPrimitive {qubits : Nat}
    (gate : PrimitiveGate qubits) : Prop :=
  match gate with
  | .x _ | .cnot _ _ _ | .toffoli _ _ _ _ _ _ => True
  | .ry angle _ => angle.IsSymbolFree
  | _ => False

end VerifiedCircuitCore
