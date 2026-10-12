import QLean.Generator.Analysis.OracleCanonicalFullStage
import QLean.Generator.Implementation.OracleEventLocalTotalStageCompiler
import QLean.Generator.Implementation.OracleFullStageCorrectness
import QLean.Generator.Implementation.QOracleSequenceSkeleton

/-!
# canonical column/row oracle の全 dirty Exact contract
-/

namespace ProbabilityGeneratorQProof

noncomputable section

namespace OracleCanonicalTotalProgram

/-- 一つの slot の column 六 branch は既存正本と同じ回路列へ compile される。 -/
theorem compile_columnBranchesAt (p : QParameters) (slot : Fin p.K) :
    (columnBranchesAt p slot).map TotalReversibleStage.compile =
      [columnDiagonalResultComputeUseUncomputeCircuit p slot 0,
       columnDiagonalResultComputeUseUncomputeCircuit p slot 1,
       applyColumnEventReferenceAndRestoreWorkCircuit p slot 2,
       applyColumnEventReferenceAndRestoreWorkCircuit p slot 3,
       applyColumnEventReferenceAndRestoreWorkCircuit p slot 4,
       applyColumnEventReferenceAndRestoreWorkCircuit p slot 5] := by
  simp [columnBranchesAt, OracleDiagonalTotalProgram.compile_columnDiagonal,
    OracleEventTotalProgram.compile_columnEvent]

/-- 一つの slot の row 六 branch は既存正本と同じ回路列へ compile される。 -/
theorem compile_rowBranchesAt (p : QParameters) (slot : Fin p.K) :
    (rowBranchesAt p slot).map TotalReversibleStage.compile =
      [rowDiagonalResultComputeUseUncomputeCircuit p slot 0,
       rowDiagonalResultComputeUseUncomputeCircuit p slot 1,
       applyRowEventReferenceAndRestoreWorkCircuit p slot 2,
       applyRowEventReferenceAndRestoreWorkCircuit p slot 3,
       applyRowEventReferenceAndRestoreWorkCircuit p slot 4,
       applyRowEventReferenceAndRestoreWorkCircuit p slot 5] := by
  simp [rowBranchesAt, OracleDiagonalTotalProgram.compile_rowDiagonal,
    OracleEventTotalProgram.compile_rowEvent]

/-- 全 column branch stage の compiler 列は既存 branch list と一致する。 -/
theorem compile_columnBranches (p : QParameters) :
    (columnBranches p).map TotalReversibleStage.compile =
      columnOracleBranchList p := by
  unfold columnBranches columnOracleBranchList
  induction List.finRange p.K with
  | nil => rfl
  | cons slot slots inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, inductionHypothesis]
      rw [compile_columnBranchesAt]

/-- 全 row branch stage の compiler 列は既存 branch list と一致する。 -/
theorem compile_rowBranches (p : QParameters) :
    (rowBranches p).map TotalReversibleStage.compile = rowOracleBranchList p := by
  unfold rowBranches rowOracleBranchList
  induction List.finRange p.K with
  | nil => rfl
  | cons slot slots inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, inductionHypothesis]
      rw [compile_rowBranchesAt]

/-- column branch fold は既存有限 sequence と一致する。 -/
theorem compile_columnBranchFold (p : QParameters) :
    ((columnChildren p).branchFold p).compile =
      Circuit.sequence (columnOracleBranchList p) := by
  rw [TotalOracleStageChildren.branchFold,
    TotalReversibleStage.compile_sequence]
  change Circuit.sequence ((columnBranches p).map TotalReversibleStage.compile) = _
  rw [compile_columnBranches]

/-- row branch fold は既存有限 sequence と一致する。 -/
theorem compile_rowBranchFold (p : QParameters) :
    ((rowChildren p).branchFold p).compile =
      Circuit.sequence (rowOracleBranchList p) := by
  rw [TotalOracleStageChildren.branchFold,
    TotalReversibleStage.compile_sequence]
  change Circuit.sequence ((rowBranches p).map TotalReversibleStage.compile) = _
  rw [compile_rowBranches]

/-- column の canonical 全 dirty stage は既存正本 oracle と同じASTへ compile される。 -/
theorem compile_columnFullStage (p : QParameters) :
    ((columnChildren p).fullStage p).compile =
      applyColumnOracleReferenceAndRestoreWorkCircuit p := by
  rw [TotalOracleStageChildren.fullStage,
    TotalReversibleStage.compile_computeUseUncompute]
  change Circuit.computeUseUncompute id
      (OraclePersistentTotalProgram.columnPersistent p).compile
      ((columnChildren p).branchFold p).compile = _
  rw [OraclePersistentTotalProgram.compile_columnPersistent,
    compile_columnBranchFold,
    applyColumnOracleReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]

/-- row の canonical 全 dirty stage は既存正本 oracle と同じASTへ compile される。 -/
theorem compile_rowFullStage (p : QParameters) :
    ((rowChildren p).fullStage p).compile =
      applyRowOracleReferenceAndRestoreWorkCircuit p := by
  rw [TotalOracleStageChildren.fullStage,
    TotalReversibleStage.compile_computeUseUncompute]
  change Circuit.computeUseUncompute id
      (OraclePersistentTotalProgram.rowPersistent p).compile
      ((rowChildren p).branchFold p).compile = _
  rw [OraclePersistentTotalProgram.compile_rowPersistent,
    compile_rowBranchFold,
    applyRowOracleReferenceAndRestoreWorkCircuit_eq_computeUseUncompute]

/-- column oracle を許可 PrimitiveGate AST と独立な全空間作用素へ結ぶ component。 -/
def columnExactOperatorComponent (p : QParameters) :=
  (columnChildren p).fullExactOperatorComponent p

/-- row oracle を許可 PrimitiveGate AST と独立な全空間作用素へ結ぶ component。 -/
def rowExactOperatorComponent (p : QParameters) :=
  (rowChildren p).fullExactOperatorComponent p

/-- column Exact component の回路は既存正本 PrimitiveGate AST と一致する。 -/
theorem columnExactOperatorComponent_circuit (p : QParameters) :
    (columnExactOperatorComponent p).circuit =
      applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p := by
  change VerifiedCircuitCore.Circuit.mapGates ReversibleGate.toPrimitive
      ((columnChildren p).fullPermutationComponent p).circuit = _
  rw [TotalOracleStageChildren.fullPermutationComponent,
    TotalReversibleStage.permutationComponent_circuit,
    compile_columnFullStage]
  rfl

/-- row Exact component の回路は既存正本 PrimitiveGate AST と一致する。 -/
theorem rowExactOperatorComponent_circuit (p : QParameters) :
    (rowExactOperatorComponent p).circuit =
      applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit p := by
  change VerifiedCircuitCore.Circuit.mapGates ReversibleGate.toPrimitive
      ((rowChildren p).fullPermutationComponent p).circuit = _
  rw [TotalOracleStageChildren.fullPermutationComponent,
    TotalReversibleStage.permutationComponent_circuit,
    compile_rowFullStage]
  rfl

/-- column oracle 正本の全空間作用素は回路非依存 target と等しい。 -/
theorem columnCircuit_denote_eq_analyticOperator (p : QParameters) :
    (applyColumnOracleReferenceAndRestoreWorkPrimitiveCircuit p).denote
        primitiveGateOperator = columnAnalyticOperator p := by
  rw [← columnExactOperatorComponent_circuit]
  exact (columnChildren p).fullCircuit_denote_eq_fullAnalyticOperator p

/-- row oracle 正本の全空間作用素は回路非依存 target と等しい。 -/
theorem rowCircuit_denote_eq_analyticOperator (p : QParameters) :
    (applyRowOracleReferenceAndRestoreWorkPrimitiveCircuit p).denote
        primitiveGateOperator = rowAnalyticOperator p := by
  rw [← rowExactOperatorComponent_circuit]
  exact (rowChildren p).fullCircuit_denote_eq_fullAnalyticOperator p

end OracleCanonicalTotalProgram

end

end ProbabilityGeneratorQProof
