import QLean.Generator.Analysis.TotalReversibleStage
import QLean.Generator.Analysis.QParameters

/-!
# oracle全dirty作用の純粋な親stage

persistent計算と各branchを、実行順の有限合成と
compute--use--uncomputeだけで束ねる。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- oracle親へ渡す、回路非依存なpersistent stageとbranch stage列。 -/
structure TotalOracleStageChildren (p : QParameters) where
  /-- 全branchに共通する情報を計算するstage。 -/
  persistent : TotalReversibleStage p.ancillaWidth p.systemWidth
  /-- selector順に実行するbranch stage列。 -/
  branches : List (TotalReversibleStage p.ancillaWidth p.systemWidth)

namespace TotalOracleStageChildren

/-- branch stage列を実行順に有限合成する。 -/
def branchFold (p : QParameters) (children : TotalOracleStageChildren p) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  TotalReversibleStage.sequence children.branches

/-- persistent--branch fold--persistent逆実行というoracle全体の純粋stage。 -/
def fullStage (p : QParameters) (children : TotalOracleStageChildren p) :
    TotalReversibleStage p.ancillaWidth p.systemWidth :=
  TotalReversibleStage.computeUseUncompute children.persistent
    (children.branchFold p)

/-- oracle全体が全dirty基底へ及ぼす独立な解析置換。 -/
def fullReference (p : QParameters) (children : TotalOracleStageChildren p) :
    Equiv.Perm (JointBasis p.ancillaWidth p.systemWidth) :=
  (children.fullStage p).reference

/-- oracle全体の独立な全空間解析作用素。 -/
def fullAnalyticOperator (p : QParameters)
    (children : TotalOracleStageChildren p) :
    Operator (JointBasis p.ancillaWidth p.systemWidth) :=
  (children.fullStage p).analyticOperator

end TotalOracleStageChildren

end

end ProbabilityGeneratorQProof
