import QLean.Generator.Implementation.QOracleEventComputedClean

/-!
# Compact decoder の work 復元

任意の型安全な入力 register 配置について、compact decoder と persistent compute が
比較・AND work を元の値へ戻すことを証明する。合法 delimiter の存在は仮定しない。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/--
適正配置の compact decoder は比較・AND work を入力時の値へ厳密に戻す。
-/
theorem xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_preserves_compareOrAnd_of_layout
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ oracleCompareWorkWires p ∨
      wire ∈ oracleAndWorkWires p) :
    (xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input wire = input wire := by
  let decoded := (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires
    (decoderSuffixWires p) (oracleDegreeWires p)).runBasis
      reversibleGatePermutation input
  have restored : BasisAgreeOn
      (decoderLegalitySupportFor p inputWires)
      ((xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit p inputWires).runBasis
        reversibleGatePermutation input) decoded := by
    simpa [decoded] using
      xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_support_restored_of_input p inputWires
        layout input
  rw [restored wire (by
    rcases member with compareMember | andMember
    · simp [decoderLegalitySupportFor, compareMember]
    · simp [decoderLegalitySupportFor, andMember])]
  change (xorDelimiterDegreeOneHotIntoTargetsCircuit p.wordWidth inputWires (decoderSuffixWires p)
    (oracleDegreeWires p)).runBasis reversibleGatePermutation input wire =
      input wire
  rw [runBasis_xorDelimiterDegreeOneHotIntoTargetsCircuit_outside p.wordWidth inputWires
    (decoderSuffixWires p) (oracleDegreeWires p) wire input
    (by simp [layout.length_eq]) layout.disjoint_suffix layout.disjoint_degree
    (oracleDegreeWires_disjoint_decoderSuffixWires p).symm
    (decoderSuffixWires_nodup p)]
  · rcases member with compareMember | andMember
    · exact (List.disjoint_left.mp layout.disjoint_compare.symm
        compareMember)
    · exact (List.disjoint_left.mp layout.disjoint_and.symm andMember)
  · rcases member with compareMember | andMember
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_compareWork p).symm compareMember)
    · exact (List.disjoint_left.mp
        (decoderSuffixWires_disjoint_andWork p).symm andMember)
  · rcases member with compareMember | andMember
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_compareWork p).symm compareMember)
    · exact (List.disjoint_left.mp
        (oracleDegreeWires_disjoint_andWork p).symm andMember)

/--
Persistent compute も比較・AND work を入力時の値へ厳密に戻す。
-/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_compareOrAnd_of_layout
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (rowMode : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (wire : Wire p.ancillaWidth p.systemWidth)
    (member : wire ∈ oracleCompareWorkWires p ∨
      wire ∈ oracleAndWorkWires p) :
    (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input wire = input wire := by
  rw [computeSharedDecoderPresenceParityAndOneFlagsCircuit_work_eq_compactDecoder p inputWires rowMode
    input wire member]
  exact xorDelimiterLegalityAndDegreeOneHotIntoTargetsCircuit_preserves_compareOrAnd_of_layout p
    inputWires layout input wire member

/--
比較・AND work が 0 の event-clean 入力は、合法性に関係なく persistent compute 後も
event-clean である。
-/
theorem computeSharedDecoderPresenceParityAndOneFlagsCircuit_output_eventSortClean_of_workZero
    (p : QParameters)
    (inputWires : List (Wire p.ancillaWidth p.systemWidth))
    (layout : CompactDecoderInputLayout p inputWires)
    (inputDisjointWork : inputWires.Disjoint (diagonalOracleWorkWires p))
    (rowMode : Bool)
    (input : JointBasis p.ancillaWidth p.systemWidth)
    (eventClean : EventSortCleanInput p input)
    (compareZero : readWires (oracleCompareWorkWires p) input =
      List.replicate (oracleCompareWorkWires p).length false)
    (andZero : ∀ wire ∈ oracleAndWorkWires p, input wire = false) :
    EventSortCleanInput p
      ((computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
        reversibleGatePermutation input) := by
  let output := (computeSharedDecoderPresenceParityAndOneFlagsCircuit p inputWires rowMode).runBasis
    reversibleGatePermutation input
  have preserveWork (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈ oracleCompareWorkWires p ∨
        wire ∈ oracleAndWorkWires p) : output wire = input wire := by
    simpa [output] using
      computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_compareOrAnd_of_layout p inputWires
        layout rowMode input wire member
  have outputCompareZero : readWires (oracleCompareWorkWires p) output =
      List.replicate (oracleCompareWorkWires p).length false := by
    apply readWires_eq_replicate_false_of_forall
    intro wire member
    rw [preserveWork wire (Or.inl member)]
    exact pointwise_false_of_readWires_eq_replicate
      (oracleCompareWorkWires p) input compareZero wire member
  have outputAndZero : ∀ wire ∈ oracleAndWorkWires p,
      output wire = false := by
    intro wire member
    rw [preserveWork wire (Or.inr member)]
    exact andZero wire member
  have preserveMiddle {width : Nat}
      (middle : RegisterSlice p.oracleWorkWidth width)
      (candidateBefore :
        (OracleWorkLayout.canonical p).candidate.start + p.candidateWidth ≤
          middle.start)
      (beforeCompare : middle.start + width ≤
        (OracleWorkLayout.canonical p).compareWork.start)
      (wire : Wire p.ancillaWidth p.systemWidth)
      (member : wire ∈
        ((QLayout.oracleSlice middle).wireList :
          List (Wire p.ancillaWidth p.systemWidth))) :
      output wire = input wire := by
    simpa [output] using computeSharedDecoderPresenceParityAndOneFlagsCircuit_preserves_middleOracleSlice p
      inputWires inputDisjointWork rowMode input middle candidateBefore
      beforeCompare wire member
  refine {
    moved_selector := {
      compare_zero := outputCompareZero
      scratch_zero := ?_
      position_zero := ?_
      pair_zero := ?_ }
    sort_compare_zero := ?_
    sort_scratch_zero := ?_
    sort_history_zero := ?_ }
  · intro wire member
    exact outputAndZero wire (List.mem_of_mem_drop member)
  · change output (oraclePositionWire p) = false
    have positionMember : oraclePositionWire p ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).positionMatch).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr
        ⟨⟨0, by simpa [QParameters.positionMatchWidth] using p.K_pos⟩,
          List.mem_finRange _, rfl⟩
    rw [preserveMiddle (OracleWorkLayout.canonical p).positionMatch (by
      simp [OracleWorkLayout.canonical]
      omega) (by simp [OracleWorkLayout.canonical])
      (oraclePositionWire p) positionMember]
    exact eventClean.moved_selector.position_zero
  · change output (oraclePairWire p) = false
    have pairMember : oraclePairWire p ∈
        ((QLayout.oracleSlice
          (OracleWorkLayout.canonical p).pair).wireList :
            List (Wire p.ancillaWidth p.systemWidth)) := by
      rw [RegisterSlice.wireList]
      exact List.mem_map.mpr
        ⟨⟨0, by simp [QParameters.pairWidth, p.K_pos]⟩,
          List.mem_finRange _, rfl⟩
    rw [preserveMiddle (OracleWorkLayout.canonical p).pair (by
      simp [OracleWorkLayout.canonical]
      omega) (by simp [OracleWorkLayout.canonical])
      (oraclePairWire p) pairMember]
    exact eventClean.moved_selector.pair_zero
  · apply readWires_eq_replicate_false_of_forall
    intro wire member
    rcases List.mem_append.mp member with compareMember | extraMember
    · exact pointwise_false_of_readWires_eq_replicate
        (oracleCompareWorkWires p) output outputCompareZero wire compareMember
    · simp only [List.mem_singleton] at extraMember
      subst wire
      exact outputAndZero _ (by simp [oracleAndWorkWires])
  · intro wire member
    have fullMember := sortAndScratchWires_mem_andSlice p member
    apply outputAndZero wire
    simpa [oracleAndWorkWires, RegisterSlice.wireList] using fullMember
  · intro instruction instructionMember
    change output ((QLayout.oracleSlice
      (OracleWorkLayout.canonical p).sortFlags).ancillaWire
        instruction.history) = false
    rw [preserveMiddle (OracleWorkLayout.canonical p).sortFlags (by
      simp [OracleWorkLayout.canonical]) (by
        simp [OracleWorkLayout.canonical]
        omega) _ (by
          rw [RegisterSlice.wireList]
          exact List.mem_map.mpr
            ⟨instruction.history, List.mem_finRange _, rfl⟩)]
    exact eventClean.sort_history_zero instruction instructionMember

end ReversibleCircuit

end ProbabilityGeneratorQProof
