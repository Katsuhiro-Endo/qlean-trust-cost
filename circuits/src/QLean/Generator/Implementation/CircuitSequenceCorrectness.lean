import QLean.Generator.Implementation.CircuitUtilities

/-!
# 回路列の基底作用を合成する一般補題

多数の相互排他的な分岐を `Circuit.sequence` で並べた回路について、全分岐が恒等な場合と、
一つの分岐だけが作用する場合を一般の基底型・ゲート型で扱う。
-/

namespace ProbabilityGeneratorQProof

namespace Circuit

/-- 二つの回路リストを連結した逐次回路の作用は、前半の後に後半を作用させた値である。 -/
theorem runBasis_sequence_append
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (before after : List (Circuit Gate)) (input : basis) :
    (sequence (before ++ after)).runBasis gatePermutation input =
      (sequence after).runBasis gatePermutation
        ((sequence before).runBasis gatePermutation input) := by
  simp only [runBasis_sequence, List.foldl_append]

/-- リスト中の各回路が同じ入力を固定するなら、その逐次回路全体も入力を固定する。 -/
theorem runBasis_sequence_eq_input_of_each
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (circuits : List (Circuit Gate)) (input : basis)
    (eachIdentity : ∀ circuit ∈ circuits,
      circuit.runBasis gatePermutation input = input) :
    (sequence circuits).runBasis gatePermutation input = input := by
  induction circuits with
  | nil => rfl
  | cons circuit rest inductionHypothesis =>
      change (sequence rest).runBasis gatePermutation
          (circuit.runBasis gatePermutation input) = input
      rw [eachIdentity circuit (by simp)]
      apply inductionHypothesis
      intro next member
      exact eachIdentity next (by simp [member])

/--
前半が入力を固定し、一つの active 回路が出力を作り、後半がその出力を固定するなら、
全回路列の作用は active 回路の作用だけに一致する。
-/
theorem runBasis_sequence_eq_of_single_active
    {Gate basis : Type*}
    (gatePermutation : Gate → Equiv.Perm basis)
    (before after : List (Circuit Gate)) (active : Circuit Gate)
    (input output : basis)
    (beforeIdentity : ∀ circuit ∈ before,
      circuit.runBasis gatePermutation input = input)
    (activeResult : active.runBasis gatePermutation input = output)
    (afterIdentity : ∀ circuit ∈ after,
      circuit.runBasis gatePermutation output = output) :
    (sequence (before ++ active :: after)).runBasis gatePermutation input = output := by
  rw [runBasis_sequence_append]
  rw [runBasis_sequence_eq_input_of_each gatePermutation before input beforeIdentity]
  change (sequence after).runBasis gatePermutation
      (active.runBasis gatePermutation input) = output
  rw [activeResult]
  exact runBasis_sequence_eq_input_of_each gatePermutation after output afterIdentity

end Circuit

end ProbabilityGeneratorQProof
