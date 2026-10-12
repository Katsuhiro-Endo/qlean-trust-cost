import QLean.Generator.Implementation.BitonicSortCorrectness
import QLean.Generator.Implementation.QBitonicNetworkCorrectness

/-!
# Q用bitonic基本ゲート回路の整列定理

純粋networkの一般整列定理を、compare・controlled swapから成る正本可逆回路の
`runBasis`結果へ接続する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- cleanな比較work・scratch・historyから実行したQ sort回路はcandidateを昇順化する。 -/
theorem reversiblySortCandidateWordsAndRestoreHistoryCircuit_sorts_candidates
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (flagsZero : readWires (sortCompareWorkWires p) input =
      List.replicate (sortCompareWorkWires p).length false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p, input wire = false)
    (historiesZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      input ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) = false) :
    IsSortedFin
      (qCandidateValue p
        ((reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
          reversibleGatePermutation input)) := by
  rw [qCandidateValue_runBasis_reversiblySortCandidateWordsAndRestoreHistoryCircuit p input
    flagsZero scratchZero historiesZero]
  rw [qBitonicValuesReference_eq_typed]
  exact qTypedBitonicSchedule_sorts_nat p (qCandidateValue p input)

/-- cleanな入力からのQ sort回路はcandidate値の出現個数を保存する。 -/
theorem reversiblySortCandidateWordsAndRestoreHistoryCircuit_preserves_candidate_valueCount
    (p : QParameters)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (flagsZero : readWires (sortCompareWorkWires p) input =
      List.replicate (sortCompareWorkWires p).length false)
    (scratchZero : ∀ wire ∈ sortAndScratchWires p, input wire = false)
    (historiesZero : ∀ instruction ∈ qTypedBitonicSchedule p,
      input ((QLayout.oracleSlice
        (OracleWorkLayout.canonical p).sortFlags).ancillaWire
          instruction.history) = false)
    (target : Nat) :
    finiteValueCount target
        (qCandidateValue p
          ((reversiblySortCandidateWordsAndRestoreHistoryCircuit p).runBasis
            reversibleGatePermutation input)) =
      finiteValueCount target (qCandidateValue p input) := by
  rw [qCandidateValue_runBasis_reversiblySortCandidateWordsAndRestoreHistoryCircuit p input
    flagsZero scratchZero historiesZero]
  rw [qBitonicValuesReference_eq_typed]
  exact qTypedBitonicSchedule_preserves_valueCount p target
    (qCandidateValue p input)

end ReversibleCircuit

end ProbabilityGeneratorQProof
