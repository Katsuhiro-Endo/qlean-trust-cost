import QLean.Generator.Implementation.MultiControlled
import QLean.Generator.Implementation.QTopLevel
import QLean.Generator.Analysis.UniformPreparationAttachedPlan

/-!
# 非2冪一様準備計画の基本ゲート回路化

証明済みの回転計画をcolumn selectorの実wireへ割り当てる。各命令のBool制御はcleanな
Toffoli AND鎖へコンパイルされ、角度は`AngleExpr`のまま保持される。
-/

namespace ProbabilityGeneratorQProof

/-- 一様準備用AND work sliceをQ回路全体の型安全なwire列へ変換する。 -/
def uniformScratchWires (p : QParameters) :
    List (Wire p.ancillaWidth p.systemWidth) :=
  (List.finRange p.andWorkWidth).map fun index =>
    (QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork).ancillaWire index

/-- well-formed命令のtarget番号をcolumn selectorの型安全なwireへ変換する。 -/
def uniformInstructionTarget (p : QParameters)
    (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed p.selectorWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  columnSelectorWire p ⟨instruction.target, wellFormed.1⟩

/-- well-formed命令のBool制御列をcolumn selectorの型安全なwire列へ変換する。 -/
def uniformInstructionControls (p : QParameters)
    (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed p.selectorWidth) :
    List (Wire p.ancillaWidth p.systemWidth × Bool) :=
  instruction.controls.attach.map fun control =>
    (columnSelectorWire p
      ⟨control.1.1, wellFormed.2.1 control.1 control.2⟩,
      control.1.2)

/-- 任意のselector wire割当て上でwell-formed命令のtarget wireを得る。 -/
def uniformInstructionTargetOn (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed p.selectorWidth) :
    Wire p.ancillaWidth p.systemWidth :=
  selectorWire ⟨instruction.target, wellFormed.1⟩

/-- 任意のselector wire割当て上でwell-formed命令のBool制御列を得る。 -/
def uniformInstructionControlsOn (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed p.selectorWidth) :
    List (Wire p.ancillaWidth p.systemWidth × Bool) :=
  instruction.controls.attach.map fun control =>
    (selectorWire ⟨control.1.1, wellFormed.2.1 control.1 control.2⟩,
      control.1.2)

/-- 任意selector slice上で一個の記号回転命令を基本ゲートへコンパイルする。 -/
def compileUniformRotationInstructionOn (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth)
    (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed p.selectorWidth) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  Circuit.boolMultiControlledRy
    (uniformInstructionControlsOn p selectorWire instruction wellFormed)
    (uniformScratchWires p)
    (uniformInstructionTargetOn p selectorWire instruction wellFormed)
    instruction.angle

/-- 一個の記号回転命令を許可基本ゲートだけの多重制御`Ry`へコンパイルする。 -/
def compileUniformRotationInstruction (p : QParameters)
    (instruction : UniformRotationInstruction)
    (wellFormed : instruction.WellFormed p.selectorWidth) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  Circuit.boolMultiControlledRy
    (uniformInstructionControls p instruction wellFormed)
    (uniformScratchWires p)
    (uniformInstructionTarget p instruction wellFormed)
    instruction.angle

/-- `N=6K`の非2冪一様準備を実装する、Lean正本の基本ゲート回路。 -/
def prepareUniformColumnSelectorCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  Circuit.sequence <|
    (attachedUniformRotationPlan p.selectorWidth p.selectorCount
      p.selectorCount_le_capacity).map fun instruction =>
        compileUniformRotationInstruction p instruction.1 instruction.2

/-- 任意selector wire割当て上の`N=6K`非2冪一様準備回路。 -/
def prepareUniformSelectorOnWiresCircuit (p : QParameters)
    (selectorWire : Fin p.selectorWidth → Wire p.ancillaWidth p.systemWidth) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  Circuit.sequence <|
    (attachedUniformRotationPlan p.selectorWidth p.selectorCount
      p.selectorCount_le_capacity).map fun instruction =>
        compileUniformRotationInstructionOn p selectorWire
          instruction.1 instruction.2

/-- row selector上で`N=6K`状態を一様準備する基本ゲート回路。 -/
def prepareUniformRowSelectorCircuit (p : QParameters) :
    Circuit (PrimitiveGate p.ancillaWidth p.systemWidth) :=
  prepareUniformSelectorOnWiresCircuit p (rowSelectorWire p)

/-- Q用一様準備回路の全葉は許可した五種類の基本ゲートだけである。 -/
theorem prepareUniformColumnSelectorCircuit_leaves (p : QParameters) :
    ∀ gate ∈ (prepareUniformColumnSelectorCircuit p).flatten,
      IsAllowedPrimitiveGate gate :=
  primitiveCircuit_allLeavesAllowed _

/-- Q用一様準備回路は理想意味論でユニタリである。 -/
theorem prepareUniformColumnSelectorCircuit_unitary (p : QParameters) :
    (prepareUniformColumnSelectorCircuit p).toIdealOperator primitiveGateOperator ∈
      Matrix.unitaryGroup (JointBasis p.ancillaWidth p.systemWidth) ℂ :=
  primitiveCircuit_mem_unitaryGroup _

end ProbabilityGeneratorQProof
