import QLean.Generator.Implementation.QSortedCandidateBridge
import Mathlib.Tactic

/-!
# canonical candidate値の完全な出現個数

合法配置を「昇順site値＋末尾marker」へ写す`configurationCandidateValue`について、任意値の
出現個数を一般`q,K`で特徴付ける。さらに物理event更新をsource削除・moved挿入として表し、
candidate変更回路の個数保存証明から直接使える補題を与える。
-/

namespace ProbabilityGeneratorQProof

open ReversibleCircuit

/-- canonical candidate値がmarkerであることと、そのwordがpaddingであることは同値である。 -/
theorem configurationCandidateValue_eq_marker_iff
    (p : QParameters) (configuration : QConfiguration p)
    (word : Fin p.sortWordCount) :
    configurationCandidateValue p configuration word = 2 ^ p.wordWidth ↔
      configuration.1.card ≤ word.val := by
  by_cases active : word.val < configuration.1.card
  · rw [configurationCandidateValue_active p configuration word active]
    have siteLt := qSite_val_lt_marker p
      (configuration.siteAt ⟨word.val, active⟩)
    constructor
    · intro equal
      omega
    · intro padding
      omega
  · rw [configurationCandidateValue_padding p configuration word
      (Nat.le_of_not_gt active)]
    simp [Nat.le_of_not_gt active]

/-- canonical candidate値は常にmarker以下である。 -/
theorem configurationCandidateValue_le_marker
    (p : QParameters) (configuration : QConfiguration p)
    (word : Fin p.sortWordCount) :
    configurationCandidateValue p configuration word ≤ 2 ^ p.wordWidth := by
  by_cases active : word.val < configuration.1.card
  · rw [configurationCandidateValue_active p configuration word active]
    exact Nat.le_of_lt
      (qSite_val_lt_marker p (configuration.siteAt ⟨word.val, active⟩))
  · rw [configurationCandidateValue_padding p configuration word
      (Nat.le_of_not_gt active)]

/-- marker値の出現個数は、全sort word数から配置site数を引いたpadding数である。 -/
theorem finiteValueCount_configurationCandidateValue_marker
    (p : QParameters) (configuration : QConfiguration p) :
    finiteValueCount (2 ^ p.wordWidth)
        (configurationCandidateValue p configuration) =
      p.sortWordCount - configuration.1.card := by
  unfold finiteValueCount
  simp_rw [configurationCandidateValue_eq_marker_iff]
  rw [Finset.sum_boole]
  have cardLe : configuration.1.card ≤ p.sortWordCount :=
    le_trans configuration.2.2 p.K_le_sortWordCount
  apply Finset.card_eq_of_bijective
    (fun index indexLt => by
      have sumLt : configuration.1.card + index < p.sortWordCount := by
        simpa [Nat.add_comm] using Nat.add_lt_of_lt_sub indexLt
      exact (⟨configuration.1.card + index, sumLt⟩ : Fin p.sortWordCount))
  · intro word wordMember
    have padding : configuration.1.card ≤ word.val := by
      simpa using wordMember
    let index := word.val - configuration.1.card
    have indexLt : index < p.sortWordCount - configuration.1.card :=
      Nat.sub_lt_sub_right padding word.isLt
    refine ⟨index, indexLt, ?_⟩
    apply Fin.ext
    simp [index]
    omega
  · intro index indexLt
    simp
  · intro left right leftLt rightLt equal
    have valuesEqual := congrArg Fin.val equal
    simp at valuesEqual
    omega

/-- markerより大きい値はcanonical candidateに一度も出現しない。 -/
theorem finiteValueCount_configurationCandidateValue_gt_marker
    (p : QParameters) (configuration : QConfiguration p)
    (target : Nat) (markerLt : 2 ^ p.wordWidth < target) :
    finiteValueCount target (configurationCandidateValue p configuration) = 0 := by
  apply finiteValueCount_eq_zero_of_forall_ne
  intro word equal
  have bound := configurationCandidateValue_le_marker p configuration word
  omega

/-- 任意targetのcanonical candidate出現個数をmarkerとの三分岐で完全特徴付けする。 -/
theorem finiteValueCount_configurationCandidateValue
    (p : QParameters) (configuration : QConfiguration p) (target : Nat) :
    finiteValueCount target (configurationCandidateValue p configuration) =
      if target < 2 ^ p.wordWidth then
        if ∃ site : QSite p, site ∈ configuration.1 ∧ site.val = target then 1 else 0
      else if target = 2 ^ p.wordWidth then
        p.sortWordCount - configuration.1.card
      else 0 := by
  by_cases below : target < 2 ^ p.wordWidth
  · simp [below, finiteValueCount_configurationCandidateValue_lt_marker]
  · by_cases marker : target = 2 ^ p.wordWidth
    · subst target
      simp [finiteValueCount_configurationCandidateValue_marker]
    · have above : 2 ^ p.wordWidth < target := by omega
      simp [below, marker,
        finiteValueCount_configurationCandidateValue_gt_marker p configuration target above]

/-- site型targetのcanonical出現個数は、配置site集合へのmembershipの指示関数である。 -/
theorem finiteValueCount_configurationCandidateValue_site
    (p : QParameters) (configuration : QConfiguration p) (target : QSite p) :
    finiteValueCount target.val (configurationCandidateValue p configuration) =
      if target ∈ configuration.1 then 1 else 0 := by
  rw [finiteValueCount_configurationCandidateValue_lt_marker p configuration target.val
    (qSite_val_lt_marker p target)]
  by_cases member : target ∈ configuration.1
  · rw [if_pos member]
    exact if_pos ⟨target, member, rfl⟩
  · rw [if_neg member, if_neg]
    intro witness
    rcases witness with ⟨site, siteMember, valueEqual⟩
    apply member
    have siteEqual : site = target := Fin.ext valueEqual
    simpa [siteEqual] using siteMember

/-- active更新後のsite型target出現個数は`insert moved (erase source)`へのmembershipである。 -/
theorem finiteValueCount_configurationCandidateValue_update_active
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) (target : QSite p) :
    finiteValueCount target.val
        (configurationCandidateValue p (updateConfiguration input event)) =
      if target ∈ insert (moveSite event.1 event.2) (input.1.erase event.1) then 1 else 0 := by
  rw [finiteValueCount_configurationCandidateValue_site]
  rw [updateConfiguration_sites_active input event active]

/-- active更新後のsite出現個数をmoved一致またはsource以外の既存membershipで展開する。 -/
theorem finiteValueCount_configurationCandidateValue_update_active_iff
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) (target : QSite p) :
    finiteValueCount target.val
        (configurationCandidateValue p (updateConfiguration input event)) =
      if target = moveSite event.1 event.2 ∨
          (target ≠ event.1 ∧ target ∈ input.1) then 1 else 0 := by
  rw [finiteValueCount_configurationCandidateValue_update_active input event active]
  simp

/-- active更新後はsourceのcanonical candidate出現個数が0になる。 -/
theorem finiteValueCount_configurationCandidateValue_update_source
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) :
    finiteValueCount event.1.val
        (configurationCandidateValue p (updateConfiguration input event)) = 0 := by
  rw [finiteValueCount_configurationCandidateValue_update_active_iff input event active]
  have sourceNotMoved : event.1 ≠ moveSite event.1 event.2 :=
    Ne.symm (moveSite_ne_self event.1 event.2)
  simp [sourceNotMoved]

/-- active更新後はmoved siteのcanonical candidate出現個数が1になる。 -/
theorem finiteValueCount_configurationCandidateValue_update_moved
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) :
    finiteValueCount (moveSite event.1 event.2).val
        (configurationCandidateValue p (updateConfiguration input event)) = 1 := by
  rw [finiteValueCount_configurationCandidateValue_update_active_iff input event active]
  simp

/-- sourceでもmovedでもないsiteのcanonical candidate出現個数はactive更新で保存される。 -/
theorem finiteValueCount_configurationCandidateValue_update_other
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) (target : QSite p)
    (notSource : target ≠ event.1)
    (notMoved : target ≠ moveSite event.1 event.2) :
    finiteValueCount target.val
        (configurationCandidateValue p (updateConfiguration input event)) =
      finiteValueCount target.val (configurationCandidateValue p input) := by
  rw [finiteValueCount_configurationCandidateValue_update_active_iff input event active]
  rw [finiteValueCount_configurationCandidateValue_site]
  simp [notSource, notMoved]

/-- active更新のsite型target countをmoved・source・その他の三分岐で表す。 -/
theorem finiteValueCount_configurationCandidateValue_update_piecewise
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) (target : QSite p) :
    finiteValueCount target.val
        (configurationCandidateValue p (updateConfiguration input event)) =
      if target = moveSite event.1 event.2 then 1
      else if target = event.1 then 0
      else finiteValueCount target.val (configurationCandidateValue p input) := by
  by_cases moved : target = moveSite event.1 event.2
  · subst target
    simp [finiteValueCount_configurationCandidateValue_update_moved input event active]
  · by_cases source : target = event.1
    · subst target
      simp [moved, finiteValueCount_configurationCandidateValue_update_source input event active]
    · simp [moved, source,
        finiteValueCount_configurationCandidateValue_update_other input event active target
          source moved]

/-- active sourceは更新前canonical candidateにちょうど一度存在する。 -/
theorem finiteValueCount_configurationCandidateValue_active_source_before
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) :
    finiteValueCount event.1.val (configurationCandidateValue p input) = 1 := by
  rw [finiteValueCount_configurationCandidateValue_site]
  simp [active]

/-- 非衝突replacementでは、moved siteは更新前candidateに存在しない。 -/
theorem finiteValueCount_configurationCandidateValue_noCollision_moved_before
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (noCollision : moveSite event.1 event.2 ∉ input.1.erase event.1) :
    finiteValueCount (moveSite event.1 event.2).val
        (configurationCandidateValue p input) = 0 := by
  rw [finiteValueCount_configurationCandidateValue_site]
  rw [if_neg]
  intro movedMember
  apply noCollision
  exact Finset.mem_erase.mpr ⟨moveSite_ne_self event.1 event.2, movedMember⟩

/-- 衝突branchでは、moved siteは更新前candidateにちょうど一度存在する。 -/
theorem finiteValueCount_configurationCandidateValue_collision_moved_before
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (collision : moveSite event.1 event.2 ∈ input.1.erase event.1) :
    finiteValueCount (moveSite event.1 event.2).val
        (configurationCandidateValue p input) = 1 := by
  rw [finiteValueCount_configurationCandidateValue_site]
  rw [if_pos]
  exact Finset.mem_of_mem_erase collision

/--
非衝突replacementでは、任意site targetについて「更新後＋source指示値」と
「更新前＋moved指示値」が等しい。
-/
theorem finiteValueCount_configurationCandidateValue_noCollision_balance
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1)
    (noCollision : moveSite event.1 event.2 ∉ input.1.erase event.1)
    (target : QSite p) :
    finiteValueCount target.val
        (configurationCandidateValue p (updateConfiguration input event)) +
        (if target = event.1 then 1 else 0) =
      finiteValueCount target.val (configurationCandidateValue p input) +
        (if target = moveSite event.1 event.2 then 1 else 0) := by
  have movedNotSource : moveSite event.1 event.2 ≠ event.1 :=
    moveSite_ne_self event.1 event.2
  by_cases moved : target = moveSite event.1 event.2
  · subst target
    rw [finiteValueCount_configurationCandidateValue_update_moved input event active]
    rw [finiteValueCount_configurationCandidateValue_noCollision_moved_before input event
      noCollision]
    simp [movedNotSource]
  · by_cases source : target = event.1
    · subst target
      rw [finiteValueCount_configurationCandidateValue_update_source input event active]
      rw [finiteValueCount_configurationCandidateValue_active_source_before input event active]
      simp [moved]
    · rw [finiteValueCount_configurationCandidateValue_update_other input event active target
        source moved]
      simp [source, moved]

/--
衝突branchではmovedは既存なので、任意site targetについて更新後countにsource指示値を
足すと更新前countへ戻る。
-/
theorem finiteValueCount_configurationCandidateValue_collision_balance
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1)
    (collision : moveSite event.1 event.2 ∈ input.1.erase event.1)
    (target : QSite p) :
    finiteValueCount target.val
        (configurationCandidateValue p (updateConfiguration input event)) +
        (if target = event.1 then 1 else 0) =
      finiteValueCount target.val (configurationCandidateValue p input) := by
  have movedNotSource : moveSite event.1 event.2 ≠ event.1 :=
    moveSite_ne_self event.1 event.2
  by_cases moved : target = moveSite event.1 event.2
  · subst target
    rw [finiteValueCount_configurationCandidateValue_update_moved input event active]
    rw [finiteValueCount_configurationCandidateValue_collision_moved_before input event
      collision]
    simp [movedNotSource]
  · by_cases source : target = event.1
    · subst target
      rw [finiteValueCount_configurationCandidateValue_update_source input event active]
      rw [finiteValueCount_configurationCandidateValue_active_source_before input event active]
      simp
    · rw [finiteValueCount_configurationCandidateValue_update_other input event active target
        source moved]
      simp [source]

/-- 非衝突replacementでは更新前後のmarker個数が等しい。 -/
theorem finiteValueCount_configurationCandidateValue_noCollision_marker
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1)
    (noCollision : moveSite event.1 event.2 ∉ input.1.erase event.1) :
    finiteValueCount (2 ^ p.wordWidth)
        (configurationCandidateValue p (updateConfiguration input event)) =
      finiteValueCount (2 ^ p.wordWidth)
        (configurationCandidateValue p input) := by
  rw [finiteValueCount_configurationCandidateValue_marker]
  rw [finiteValueCount_configurationCandidateValue_marker]
  rw [updateConfiguration_card_of_noCollision input event active noCollision]

/-- 衝突branchでは粒子が一個減るため、更新後のmarker個数が一個増える。 -/
theorem finiteValueCount_configurationCandidateValue_collision_marker
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1)
    (collision : moveSite event.1 event.2 ∈ input.1.erase event.1) :
    finiteValueCount (2 ^ p.wordWidth)
        (configurationCandidateValue p (updateConfiguration input event)) =
      finiteValueCount (2 ^ p.wordWidth)
          (configurationCandidateValue p input) + 1 := by
  rw [finiteValueCount_configurationCandidateValue_marker]
  rw [finiteValueCount_configurationCandidateValue_marker]
  have cardDrop :=
    updateConfiguration_card_add_one_of_collision input event active collision
  have inputBound : input.1.card ≤ p.sortWordCount :=
    le_trans input.2.2 p.K_le_sortWordCount
  omega

end ProbabilityGeneratorQProof
