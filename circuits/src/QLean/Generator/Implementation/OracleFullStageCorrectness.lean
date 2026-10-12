import QLean.Generator.Analysis.OracleFullStage
import QLean.Generator.Implementation.TotalReversibleStageCompiler

/-!
# oracle全dirty親stageの一般正しさ

直接の子stageを有限合成し、同じcompiler contractだけで全空間作用素へ持ち上げる。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

namespace TotalOracleStageChildren

/-- branch foldを全入力置換へ結ぶcomponent。 -/
def branchFoldPermutationComponent (p : QParameters)
    (children : TotalOracleStageChildren p) :
    PermutationComponent
      (TotalReversibleStage.reversibleBasisOperator
        (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth))
      (reversibleGatePermutation
        (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  (children.branchFold p).permutationComponent

/-- persistent計算・branch fold・逆計算を全入力置換へ結ぶcomponent。 -/
def fullPermutationComponent (p : QParameters)
    (children : TotalOracleStageChildren p) :
    PermutationComponent
      (TotalReversibleStage.reversibleBasisOperator
        (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth))
      (reversibleGatePermutation
        (ancillaQubits := p.ancillaWidth) (systemQubits := p.systemWidth)) :=
  (children.fullStage p).permutationComponent

/-- oracle親stageを許可PrimitiveGate列と独立な全空間解析作用素へ結ぶExact component。 -/
def fullExactOperatorComponent (p : QParameters)
    (children : TotalOracleStageChildren p) :
    ExactOperatorComponent
      (primitiveGateOperator : PrimitiveGate p.ancillaWidth p.systemWidth →
        Operator (JointBasis p.ancillaWidth p.systemWidth)) :=
  (children.fullStage p).primitiveExactOperatorComponent

/-- oracle親Exact componentのtargetは純粋層の全空間作用素である。 -/
theorem fullExactOperatorComponent_target (p : QParameters)
    (children : TotalOracleStageChildren p) :
    (children.fullExactOperatorComponent p).target =
      children.fullAnalyticOperator p :=
  (children.fullStage p).primitiveExactOperatorComponent_target

/-- oracle親Exact componentの正しさは子stage compiler contractから無条件で得られる。 -/
theorem fullCircuit_denote_eq_fullAnalyticOperator (p : QParameters)
    (children : TotalOracleStageChildren p) :
    (children.fullExactOperatorComponent p).circuit.denote primitiveGateOperator =
      children.fullAnalyticOperator p := by
  rw [(children.fullExactOperatorComponent p).correct]
  exact children.fullExactOperatorComponent_target p

end TotalOracleStageChildren

end

end ProbabilityGeneratorQProof
