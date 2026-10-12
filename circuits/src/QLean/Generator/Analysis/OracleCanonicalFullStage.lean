import QLean.Generator.Analysis.BitonicTotalStage
import QLean.Generator.Analysis.OracleDiagonalTotalStage
import QLean.Generator.Analysis.OracleEventLocalTotalStage
import QLean.Generator.Analysis.OracleFullStage

/-!
# column/row oracle の canonical な全 dirty stage

二つの diagonal branch と四つの event branch を各 slot ごとに並べ、
persistent compute の compute--use--uncompute として全空間作用を定義する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

namespace OracleCanonicalTotalProgram

/-- 一つの slot に対応する column 側の六 branch。 -/
def columnBranchesAt (p : QParameters) (slot : Fin p.K) :
    List (TotalReversibleStage p.ancillaWidth p.systemWidth) :=
  [OracleDiagonalTotalProgram.columnDiagonal p slot ⟨0, by decide⟩,
   OracleDiagonalTotalProgram.columnDiagonal p slot ⟨1, by decide⟩,
   OracleEventTotalProgram.columnEventWithSort p slot ⟨2, by decide⟩
     (BitonicTotalProgram.sort p),
   OracleEventTotalProgram.columnEventWithSort p slot ⟨3, by decide⟩
     (BitonicTotalProgram.sort p),
   OracleEventTotalProgram.columnEventWithSort p slot ⟨4, by decide⟩
     (BitonicTotalProgram.sort p),
   OracleEventTotalProgram.columnEventWithSort p slot ⟨5, by decide⟩
     (BitonicTotalProgram.sort p)]

/-- 一つの slot に対応する row 側の六 branch。 -/
def rowBranchesAt (p : QParameters) (slot : Fin p.K) :
    List (TotalReversibleStage p.ancillaWidth p.systemWidth) :=
  [OracleDiagonalTotalProgram.rowDiagonal p slot ⟨0, by decide⟩,
   OracleDiagonalTotalProgram.rowDiagonal p slot ⟨1, by decide⟩,
   OracleEventTotalProgram.rowEventWithSort p slot ⟨2, by decide⟩
     (BitonicTotalProgram.sort p),
   OracleEventTotalProgram.rowEventWithSort p slot ⟨3, by decide⟩
     (BitonicTotalProgram.sort p),
   OracleEventTotalProgram.rowEventWithSort p slot ⟨4, by decide⟩
     (BitonicTotalProgram.sort p),
   OracleEventTotalProgram.rowEventWithSort p slot ⟨5, by decide⟩
     (BitonicTotalProgram.sort p)]

/-- selector 順の全 column branch stage 列。 -/
def columnBranches (p : QParameters) :
    List (TotalReversibleStage p.ancillaWidth p.systemWidth) :=
  (List.finRange p.K).flatMap (columnBranchesAt p)

/-- selector 順の全 row branch stage 列。 -/
def rowBranches (p : QParameters) :
    List (TotalReversibleStage p.ancillaWidth p.systemWidth) :=
  (List.finRange p.K).flatMap (rowBranchesAt p)

/-- column oracle の直接子。 -/
def columnChildren (p : QParameters) : TotalOracleStageChildren p :=
  { persistent := OraclePersistentTotalProgram.columnPersistent p
    branches := columnBranches p }

/-- row oracle の直接子。 -/
def rowChildren (p : QParameters) : TotalOracleStageChildren p :=
  { persistent := OraclePersistentTotalProgram.rowPersistent p
    branches := rowBranches p }

/-- column oracle の回路非依存な全入力基底置換。 -/
def columnReference (p : QParameters) :
    Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth) :=
  (columnChildren p).fullReference p

/-- row oracle の回路非依存な全入力基底置換。 -/
def rowReference (p : QParameters) :
    Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth) :=
  (rowChildren p).fullReference p

/-- column oracle の回路非依存な全空間解析作用素。 -/
def columnAnalyticOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  (columnChildren p).fullAnalyticOperator p

/-- row oracle の回路非依存な全空間解析作用素。 -/
def rowAnalyticOperator (p : QParameters) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  (rowChildren p).fullAnalyticOperator p

end OracleCanonicalTotalProgram

end

end ProbabilityGeneratorQProof
