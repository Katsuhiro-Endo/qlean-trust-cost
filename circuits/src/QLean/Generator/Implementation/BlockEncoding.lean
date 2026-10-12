import QLean.Generator.Implementation.CoreAdapter
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Q側で用いるL2作用素ノルムblock encoding規約

共有coreの抽象`BlockEncodingComponent`へ接続する前の、凍結定理と同一な解析命題。
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace ProbabilityGeneratorQProof

/-- 指定アンシラ基底で切り出すsystem作用素block。 -/
def successBlock {ancilla system : Type*} (success : ancilla)
    (operator : Operator (ancilla × system)) : Operator system :=
  Matrix.of fun output input => operator (success, output) (success, input)

end ProbabilityGeneratorQProof

