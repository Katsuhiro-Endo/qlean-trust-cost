import QLean.Generator.Implementation.CompositionalSemantics

/-!
# 回路リスト・葉走査・ゲート数の一般補助

実行順の基本ゲート列と圧縮`Circuit`構文木を相互運用するための補助定義を置く。
exporterと各一般サブ回路生成器は同じ`flatten`を使う。
-/

namespace ProbabilityGeneratorQProof

namespace Circuit

/-- 実行順に並んだゲートリストを左から順に実行する回路へ変換する。 -/
abbrev fromList {Gate : Type*} : List Gate → Circuit Gate :=
  VerifiedCircuitCore.Circuit.fromList

/-- 回路のリストを左から右の実行順で一つの構文木へ連結する。 -/
abbrev sequence {Gate : Type*} : List (Circuit Gate) → Circuit Gate :=
  VerifiedCircuitCore.Circuit.sequence

/-- 空の回路列は恒等回路になる。 -/
@[simp] theorem sequence_nil {Gate : Type*} :
    sequence ([] : List (Circuit Gate)) = .identity := by
  rfl

/-- 非空回路列は先頭回路と残りの列の二項逐次合成になる。 -/
@[simp] theorem sequence_cons {Gate : Type*}
    (head : Circuit Gate) (tail : List (Circuit Gate)) :
    sequence (head :: tail) = .seq head (sequence tail) := by
  rfl

/-- 圧縮回路構文木を実行順のゲートリストへ展開する。 -/
abbrev flatten {Gate : Type*} : Circuit Gate → List Gate :=
  VerifiedCircuitCore.Circuit.flatten

/-- ゲートリストを回路化して再び平坦化すると元のリストへ戻る。 -/
@[simp] theorem flatten_fromList {Gate : Type*} (gates : List Gate) :
    flatten (fromList gates) = gates := by
  exact VerifiedCircuitCore.Circuit.flatten_fromList gates

/-- 回路リストの連結をflattenすると各回路のflattenの連結になる。 -/
theorem flatten_sequence {Gate : Type*} (circuits : List (Circuit Gate)) :
    (sequence circuits).flatten = circuits.flatMap flatten := by
  exact VerifiedCircuitCore.Circuit.flatten_sequence circuits

/-- 回路構文木を完全展開した基本ゲート数。 -/
abbrev gateCount {Gate : Type*} (circuit : Circuit Gate) : Nat :=
  VerifiedCircuitCore.Circuit.gateCount circuit

/-- ゲートリストから作った回路のゲート数はリスト長に等しい。 -/
@[simp] theorem gateCount_fromList {Gate : Type*} (gates : List Gate) :
    gateCount (fromList gates) = gates.length := by
  exact VerifiedCircuitCore.Circuit.gateCount_fromList gates

/-- ゲートリスト回路の基底作用は、リストを左からfoldした作用に等しい。 -/
theorem runBasis_fromList
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (gates : List Gate) (input : basis) :
    (fromList gates).runBasis gatePermutation input =
      gates.foldl (fun state gate => gatePermutation gate state) input := by
  exact VerifiedCircuitCore.Circuit.runBasis_fromList
    gatePermutation gates input

/-- 回路リストの逐次合成は、各回路の基底作用を左からfoldした作用に等しい。 -/
theorem runBasis_sequence
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (circuits : List (Circuit Gate)) (input : basis) :
    (sequence circuits).runBasis gatePermutation input =
      circuits.foldl
        (fun state circuit => circuit.runBasis gatePermutation state) input := by
  exact VerifiedCircuitCore.Circuit.runBasis_sequence
    gatePermutation circuits input

/-- 回路の葉写像は、基本ゲート列から作った回路ではリスト写像と可換である。 -/
theorem map_fromList
    {Gate₁ Gate₂ : Type*} (translate : Gate₁ → Gate₂) :
    ∀ gates : List Gate₁,
      (fromList gates).map translate = fromList (gates.map translate)
  | gates => VerifiedCircuitCore.Circuit.mapGates_fromList translate gates

end Circuit

/-- Q回路正本の葉が許可された5種類の基本ゲートであることを表す述語。 -/
def IsAllowedPrimitiveGate
    {ancillaQubits systemQubits : Nat}
    : PrimitiveGate ancillaQubits systemQubits → Prop
  | .x _ => True
  | .h _ => True
  | .ry _ _ => True
  | .cnot _ _ _ => True
  | .toffoli _ _ _ _ _ _ => True

/-- `PrimitiveGate`型の回路では、全葉が構成上許可された5種類のいずれかである。 -/
theorem primitiveCircuit_allLeavesAllowed
    {ancillaQubits systemQubits : Nat}
    (circuit : Circuit (PrimitiveGate ancillaQubits systemQubits)) :
    ∀ leaf ∈ circuit.flatten, IsAllowedPrimitiveGate leaf := by
  intro leaf _
  cases leaf <;> trivial

end ProbabilityGeneratorQProof
