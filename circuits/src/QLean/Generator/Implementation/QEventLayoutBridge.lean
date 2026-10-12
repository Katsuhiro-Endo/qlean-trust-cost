import QLean.Generator.Implementation.QEventMembershipBridge

/-!
# event 分岐の canonical oracle layout 共通補題

row/column event の多重制御配置に共通する、oracle work 内部 slice の物理 wire 非同一性と
AND scratch からの分離を証明する。
-/

namespace ProbabilityGeneratorQProof

namespace ReversibleCircuit

/-- oracle work 内部の異なる局所 index は異なる物理 ancilla wire を与える。 -/
theorem oracleSlice_ancillaWire_ne_of_localIndex_ne
    (p : QParameters) {leftWidth rightWidth : Nat}
    (left : RegisterSlice p.oracleWorkWidth leftWidth)
    (right : RegisterSlice p.oracleWorkWidth rightWidth)
    (leftIndex : Fin leftWidth) (rightIndex : Fin rightWidth)
    (different : left.start + leftIndex.val ≠
      right.start + rightIndex.val) :
    ((QLayout.oracleSlice left).ancillaWire leftIndex :
      Wire p.ancillaWidth p.systemWidth) ≠
      ((QLayout.oracleSlice right).ancillaWire rightIndex :
        Wire p.ancillaWidth p.systemWidth) := by
  intro equal
  apply different
  have numbers := congrArg wireNumber equal
  simp [QLayout.oracleSlice, RegisterSlice.compose,
    RegisterSlice.ancillaWire, RegisterSlice.index, wireNumber] at numbers
  omega

/-- andWork より前の oracle 局所 slice は decoder AND scratch と交わらない。 -/
theorem oracleSlice_disjoint_decoderAndScratch
    (p : QParameters) {width : Nat}
    (slice : RegisterSlice p.oracleWorkWidth width)
    (before : slice.start + width ≤
      (OracleWorkLayout.canonical p).andWork.start) :
    ((QLayout.oracleSlice slice).wireList :
      List (Wire p.ancillaWidth p.systemWidth)).Disjoint
        (decoderAndScratchWires p) := by
  let andSlice := QLayout.oracleSlice (OracleWorkLayout.canonical p).andWork
  have full :
      ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth)).Disjoint
          (andSlice.wireList : List (Wire p.ancillaWidth p.systemWidth)) := by
    apply RegisterSlice.wireList_disjoint_of_end_le_start
    simp [andSlice, QLayout.oracleSlice, RegisterSlice.compose]
    omega
  rw [List.disjoint_left]
  intro wire sliceMember scratchMember
  apply (List.disjoint_left.mp full) sliceMember
  have andMember : wire ∈ oracleAndWorkWires p :=
    List.mem_of_mem_drop scratchMember
  simpa [oracleAndWorkWires, andSlice, RegisterSlice.wireList] using andMember

/--
`andWork` より前にある幅 1 の oracle work slice の唯一の wire は、
decoder AND scratch に含まれない。
-/
theorem oracleSingletonWire_not_mem_decoderAndScratch
    (p : QParameters) (slice : RegisterSlice p.oracleWorkWidth 1)
    (before : slice.start + 1 ≤
      (OracleWorkLayout.canonical p).andWork.start) :
    oracleSingletonWire p slice ∉ decoderAndScratchWires p := by
  intro scratchMember
  have disjoint := oracleSlice_disjoint_decoderAndScratch p slice before
  have sliceMember : oracleSingletonWire p slice ∈
      ((QLayout.oracleSlice slice).wireList :
        List (Wire p.ancillaWidth p.systemWidth)) := by
    change (QLayout.oracleSlice slice).ancillaWire 0 ∈ _
    rw [RegisterSlice.wireList]
    exact List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩
  exact (List.disjoint_left.mp disjoint) sliceMember scratchMember

/--
`base ++ scratch ++ [target]` が非重複で、新しい condition が三領域の外なら、
condition を controls 末尾へ追加しても全配置は非重複である。
-/
theorem eventControls_nodup_insert_before_scratch
    {α : Type*} [DecidableEq α]
    (base scratch : List α) (target condition : α)
    (baseLayout : (base ++ scratch ++ [target]).Nodup)
    (conditionNotBase : condition ∉ base)
    (conditionNotScratch : condition ∉ scratch)
    (conditionNeTarget : condition ≠ target) :
    (base ++ [condition] ++ scratch ++ [target]).Nodup := by
  have baseScratchNodup : (base ++ scratch).Nodup :=
    (List.nodup_append.mp baseLayout).1
  have baseNodup : base.Nodup :=
    (List.nodup_append.mp baseScratchNodup).1
  have scratchNodup : scratch.Nodup :=
    (List.nodup_append.mp baseScratchNodup).2.1
  have baseScratchSeparated :
      ∀ left ∈ base, ∀ right ∈ scratch, left ≠ right :=
    (List.nodup_append.mp baseScratchNodup).2.2
  have prefixTargetSeparated :
      ∀ left ∈ base ++ scratch, ∀ right ∈ [target], left ≠ right :=
    (List.nodup_append.mp baseLayout).2.2
  have controlsNodup : (base ++ [condition]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨baseNodup, by simp, ?_⟩
    intro left leftMember right rightMember
    have rightEq : right = condition := by simpa using rightMember
    subst right
    exact fun equal => conditionNotBase (equal ▸ leftMember)
  have controlsScratchNodup : (base ++ [condition] ++ scratch).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨controlsNodup, scratchNodup, ?_⟩
    intro left leftMember right rightMember
    rcases List.mem_append.mp leftMember with baseMember | conditionMember
    · exact baseScratchSeparated left baseMember right rightMember
    · have leftEq : left = condition := by simpa using conditionMember
      subst left
      exact fun equal => conditionNotScratch (equal ▸ rightMember)
  apply List.nodup_append.mpr
  refine ⟨controlsScratchNodup, by simp, ?_⟩
  intro left leftMember right rightMember
  have rightEq : right = target := by simpa using rightMember
  subst right
  rcases List.mem_append.mp leftMember with controlsMember | scratchMember
  · rcases List.mem_append.mp controlsMember with baseMember | conditionMember
    · exact prefixTargetSeparated left
        (List.mem_append_left scratch baseMember) target (by simp)
    · have leftEq : left = condition := by simpa using conditionMember
      subst left
      exact conditionNeTarget
  · exact prefixTargetSeparated left
      (List.mem_append_right base scratchMember) target (by simp)

end ReversibleCircuit

end ProbabilityGeneratorQProof
