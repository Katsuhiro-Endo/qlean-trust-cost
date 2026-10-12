import QLean.Generator.Analysis.OracleDiagonalTotalStage
import QLean.Generator.Implementation.OraclePersistentTotalStageCompiler
import QLean.Generator.Implementation.OracleTotalProgramsCompiler

/-!
# diagonal branch の全 dirty 状態上の段階と compiler の一致
-/

namespace ProbabilityGeneratorQProof

namespace OracleDiagonalTotalProgram

/-- pure な column selector 配置は既存 oracle 配置と一致する。 -/
theorem columnSelectorWires_eq (p : QParameters) :
    columnSelectorWires p = ProbabilityGeneratorQProof.columnSelectorWires p := rfl

/-- pure な row selector 配置は既存 oracle 配置と一致する。 -/
theorem rowSelectorWires_eq (p : QParameters) :
    rowSelectorWires p = ProbabilityGeneratorQProof.rowSelectorWires p := rfl

/-- pure な row output 配置は既存 oracle 配置と一致する。 -/
theorem rowOutputWires_eq (p : QParameters) :
    rowOutputWires p = ProbabilityGeneratorQProof.rowOutputWires p := rfl

/-- pure な selector output 配置は既存 oracle 配置と一致する。 -/
theorem selectorOutputWires_eq (p : QParameters) :
    selectorOutputWires p = ProbabilityGeneratorQProof.selectorOutputWires p := rfl

/-- pure な selected wire は既存 oracle 配置と一致する。 -/
theorem selectedWire_eq (p : QParameters) :
    selectedWire p = ProbabilityGeneratorQProof.oracleSelectedWire p := rfl

/-- pure な branch wire は既存 oracle 配置と一致する。 -/
theorem branchWire_eq (p : QParameters) :
    branchWire p = ProbabilityGeneratorQProof.oracleBranchWire p := rfl

/-- pure な present wire は既存 oracle 配置と一致する。 -/
theorem presentWireAt_eq (p : QParameters) (slot : Fin p.K) :
    presentWireAt p slot = ProbabilityGeneratorQProof.oraclePresentWireAt p slot := rfl

/-- pure な AND scratch 配置は既存 oracle 配置と一致する。 -/
theorem andScratchWires_eq (p : QParameters) :
    andScratchWires p = ProbabilityGeneratorQProof.decoderAndScratchWires p := rfl

/-- pure な key signal wire は既存 oracle 配置と一致する。 -/
theorem keySignalWire_eq (p : QParameters) :
    keySignalWire p = ProbabilityGeneratorQProof.keySignalWire p := rfl

/-- pure な negative wire は既存 oracle 配置と一致する。 -/
theorem negativeWire_eq (p : QParameters) :
    negativeWire p = ProbabilityGeneratorQProof.negativeWire p := rfl

/-- pure な active wire は既存 oracle 配置と一致する。 -/
theorem activeWire_eq (p : QParameters) :
    activeWire p = ProbabilityGeneratorQProof.activeWire p := rfl

/-- column diagonal stage の compiler は既存正本 branch と一致する。 -/
theorem compile_columnDiagonal (p : QParameters) (slot : Fin p.K) (copy : Fin 2) :
    (columnDiagonal p slot copy).compile =
      ProbabilityGeneratorQProof.columnDiagonalResultComputeUseUncomputeCircuit
        p slot copy := by
  simp [columnDiagonal,
    ProbabilityGeneratorQProof.columnDiagonalResultComputeUseUncomputeCircuit,
    columnSelectorWires_eq, rowOutputWires_eq, selectorOutputWires_eq,
    selectedWire_eq, branchWire_eq, presentWireAt_eq, andScratchWires_eq,
    negativeWire_eq, activeWire_eq,
    OraclePersistentTotalProgram.columnKeyWires_eq,
    TotalReversibleStage.compile_computeUseUncompute,
    TotalReversibleStage.compile,
    OracleTotalProgram.compile_xorSelectorEqualsConstant,
    TotalReversibleStage.compile_positiveMultiControlledX,
    OracleTotalProgram.compile_controlledXorCopy,
    OracleTotalProgram.compile_controlledXorConstant,
    TotalReversibleStage.compile_safeXorControlled]
  rfl

/-- row diagonal stage の compiler は既存正本 branch と一致する。 -/
theorem compile_rowDiagonal (p : QParameters) (slot : Fin p.K) (copy : Fin 2) :
    (rowDiagonal p slot copy).compile =
      ProbabilityGeneratorQProof.rowDiagonalResultComputeUseUncomputeCircuit
        p slot copy := by
  simp [rowDiagonal,
    ProbabilityGeneratorQProof.rowDiagonalResultComputeUseUncomputeCircuit,
    rowSelectorWires_eq, columnSelectorWires_eq,
    selectedWire_eq, branchWire_eq, presentWireAt_eq, andScratchWires_eq,
    keySignalWire_eq,
    OraclePersistentTotalProgram.systemWires_eq,
    OraclePersistentTotalProgram.columnKeyWires_eq,
    TotalReversibleStage.compile_computeUseUncompute,
    TotalReversibleStage.compile,
    OracleTotalProgram.compile_xorSelectorEqualsConstant,
    TotalReversibleStage.compile_positiveMultiControlledX,
    OracleTotalProgram.compile_controlledXorCopy,
    OracleTotalProgram.compile_controlledXorConstant,
    TotalReversibleStage.compile_safeXorControlled]
  rfl

/-- column diagonal を全入力の基底置換へ結ぶ component。 -/
def columnDiagonalPermutationComponent (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :=
  (columnDiagonal p slot copy).permutationComponent

/-- row diagonal を全入力の基底置換へ結ぶ component。 -/
def rowDiagonalPermutationComponent (p : QParameters)
    (slot : Fin p.K) (copy : Fin 2) :=
  (rowDiagonal p slot copy).permutationComponent

end OracleDiagonalTotalProgram

end ProbabilityGeneratorQProof
