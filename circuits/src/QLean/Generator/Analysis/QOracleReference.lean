import QLean.Generator.Analysis.QSelector
import Mathlib.Tactic

/-!
# column/row oracleの純粋参照関数

まず固定幅selectorと合法配置から、column oracleが返す更新後配置・row selector・符号を
純粋関数として定義する。inactive、padding、存在しないslotは`none`へ統一する。
-/

namespace ProbabilityGeneratorQProof

open QParameters

/-- column oracleのactive branchが返す外部値。 -/
structure ColumnReferenceResult (p : QParameters) where
  /-- 更新後配置。 -/
  output : QConfiguration p
  /-- 更新後配置のarrival slotを指すrow selector。 -/
  rowSelector : QSelector p
  /-- 二つの対角copyだけで真になる負号bit。 -/
  negative : Bool
deriving DecidableEq

/-- 配置の`Fin K` slotが実在すれば昇順siteを返す。 -/
def configurationSlot? {p : QParameters}
    (configuration : QConfiguration p) (slot : Fin p.K) :
    Option {site : QSite p // site ∈ configuration.1} :=
  if present : slot.val < configuration.1.card then
    some ((configuration.1.orderIsoOfFin rfl) ⟨slot.val, present⟩)
  else
    none

/-- 配置に属するsiteの昇順slotを`Fin K`として返す。 -/
def slotOfMember {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) : Fin p.K :=
  let smallSlot := (configuration.1.orderIsoOfFin rfl).symm ⟨site, member⟩
  ⟨smallSlot.val, lt_of_lt_of_le smallSlot.isLt configuration.2.2⟩

/-- 配置のsite集合が等しければ、proof項によらず同じsiteの昇順slot番号も等しい。 -/
theorem slotOfMember_eq_of_sites_eq
    {p : QParameters} (left right : QConfiguration p)
    (sitesEqual : left.1 = right.1) (site : QSite p)
    (leftMember : site ∈ left.1) (rightMember : site ∈ right.1) :
    slotOfMember left site leftMember = slotOfMember right site rightMember := by
  have configurationsEqual : left = right := Subtype.ext sitesEqual
  subst right
  rfl

/-- `slotOfMember`で得たslotは実在し、元のsiteを指す。 -/
@[simp] theorem configurationSlot_slotOfMember
    {p : QParameters} (configuration : QConfiguration p)
    (site : QSite p) (member : site ∈ configuration.1) :
    configurationSlot? configuration (slotOfMember configuration site member) =
      some ⟨site, member⟩ := by
  let smallSlot := (configuration.1.orderIsoOfFin rfl).symm ⟨site, member⟩
  unfold configurationSlot? slotOfMember
  split
  · simp only [Option.some.injEq]
    exact (configuration.1.orderIsoOfFin rfl).apply_symm_apply ⟨site, member⟩
  · rename_i absent
    exact (absent smallSlot.isLt).elim

/-- 方向と実際の衝突有無から、対応するevent offset 2--5を返す。 -/
def eventOffset (direction : QDirection) (collision : Bool) : Fin 6 :=
  match direction, collision with
  | .right, false => 2
  | .right, true => 3
  | .up, false => 4
  | .up, true => 5

/-- event offsetは対角offsetではない。 -/
theorem eventOffset_not_diagonal (direction : QDirection) (collision : Bool) :
    ¬(eventOffset direction collision).val < 2 := by
  cases direction <;> cases collision <;> decide

/-- event offsetから読む方向は元の方向へ戻る。 -/
@[simp] theorem selectorDirection_eventOffset
    {p : QParameters} (slot : Fin p.K)
    (direction : QDirection) (collision : Bool) :
    selectorDirection (selectorOfSlotOffset slot (eventOffset direction collision)) = direction := by
  cases direction <;> cases collision <;>
    simp [selectorDirection, eventOffset]

/-- event offsetから読む衝突要求は元のBoolへ戻る。 -/
@[simp] theorem selectorRequestsCollision_eventOffset
    {p : QParameters} (slot : Fin p.K)
    (direction : QDirection) (collision : Bool) :
    selectorRequestsCollision
      (selectorOfSlotOffset slot (eventOffset direction collision)) = collision := by
  cases direction <;> cases collision <;>
    simp [selectorRequestsCollision, eventOffset]

/--
column oracleの純粋参照関数。diagは同じ配置とselectorを返す。eventはrep/collの
要求が実際のmembershipと一致するときだけactiveになる。
-/
def columnReference {p : QParameters}
    (input : QConfiguration p) (selector : QSelector p) :
    Option (ColumnReferenceResult p) :=
  match _selected : configurationSlot? input (selectorSlot selector) with
  | none => none
  | some source =>
      if _diagonal : (selectorOffset selector).val < 2 then
        some ⟨input, selector, true⟩
      else
        let direction := selectorDirection selector
        let event : QEvent p := (source.1, direction)
        let moved := moveSite source.1 direction
        let collision : Bool := decide (moved ∈ input.1.erase source.1)
        if _branchCorrect : collision = selectorRequestsCollision selector then
          let output := updateConfiguration input event
          have movedMember : moved ∈ output.1 :=
            moveSite_mem_updateConfiguration input event source.2
          let arrivalSlot := slotOfMember output moved movedMember
          some ⟨output,
            selectorOfSlotOffset arrivalSlot (selectorOffset selector), false⟩
        else
          none

/-- 物理eventに対応する唯一のcolumn selector。 -/
def selectorForEvent {p : QParameters}
    (input : QConfiguration p) (source : QSite p) (member : source ∈ input.1)
    (direction : QDirection) : QSelector p :=
  let moved := moveSite source direction
  let collision : Bool := decide (moved ∈ input.1.erase source)
  selectorOfSlotOffset (slotOfMember input source member) (eventOffset direction collision)

/-- 選択siteが実在し、event条件が一致すればcolumn参照関数は更新を返す。 -/
theorem columnReference_event_active
    {p : QParameters} (input : QConfiguration p) (selector : QSelector p)
    (source : QSite p) (member : source ∈ input.1)
    (selected : configurationSlot? input (selectorSlot selector) = some ⟨source, member⟩)
    (notDiagonal : ¬(selectorOffset selector).val < 2)
    (branchCorrect :
      (decide (moveSite source (selectorDirection selector) ∈ input.1.erase source) : Bool) =
        selectorRequestsCollision selector) :
    ∃ rowSelector,
      columnReference input selector =
        some ⟨updateConfiguration input (source, selectorDirection selector),
          rowSelector, false⟩ := by
  unfold columnReference
  rw [selected]
  simp only [notDiagonal, dite_false]
  rw [dif_pos branchCorrect]
  exact ⟨_, rfl⟩

/-- 各active物理eventのselectorはcolumn参照関数で必ず受理される。 -/
theorem columnReference_selectorForEvent_active
    {p : QParameters} (input : QConfiguration p)
    (source : QSite p) (member : source ∈ input.1) (direction : QDirection) :
    ∃ rowSelector,
      columnReference input (selectorForEvent input source member direction) =
        some ⟨updateConfiguration input (source, direction), rowSelector, false⟩ := by
  let selector := selectorForEvent input source member direction
  have selected : configurationSlot? input (selectorSlot selector) =
      some ⟨source, member⟩ := by
    simp [selector, selectorForEvent]
  have notDiagonal : ¬(selectorOffset selector).val < 2 := by
    simpa [selector, selectorForEvent] using
      eventOffset_not_diagonal direction
        (decide (moveSite source direction ∈ input.1.erase source))
  have branchCorrect :
      (decide (moveSite source (selectorDirection selector) ∈ input.1.erase source) : Bool) =
        selectorRequestsCollision selector := by
    simp [selector, selectorForEvent]
  have result := columnReference_event_active input selector source member selected
    notDiagonal branchCorrect
  simpa [selector, selectorForEvent] using result

/-- 各実在slotの二つのdiag selectorは同じ配置を負号付きで返す。 -/
theorem columnReference_diagonal
    {p : QParameters} (input : QConfiguration p)
    (source : QSite p) (member : source ∈ input.1) (copy : Fin 2) :
    columnReference input
        (selectorOfSlotOffset (slotOfMember input source member)
          ⟨copy.val, lt_trans copy.isLt (by decide)⟩) =
      some ⟨input,
        selectorOfSlotOffset (slotOfMember input source member)
          ⟨copy.val, lt_trans copy.isLt (by decide)⟩,
        true⟩ := by
  let selector := selectorOfSlotOffset (slotOfMember input source member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  have selected : configurationSlot? input (selectorSlot selector) =
      some ⟨source, member⟩ := by
    simp [selector]
  have diagonal : (selectorOffset selector).val < 2 := by
    simp [selector]
    omega
  change columnReference input selector = some ⟨input, selector, true⟩
  unfold columnReference
  rw [selected]
  simp [diagonal]

/-- row oracleのactive branchが返すpredecessorとcolumn selector。 -/
structure RowReferenceResult (p : QParameters) where
  /-- 復元した更新前配置。 -/
  input : QConfiguration p
  /-- predecessor内のsource slotを指すcolumn selector。 -/
  columnSelector : QSelector p
deriving DecidableEq

/-- rep predecessor用にarrivalをsourceへ置換したsite集合。 -/
def replacementPredecessorSites {p : QParameters}
    (output : QConfiguration p) (arrival source : QSite p) : Finset (QSite p) :=
  insert source (output.1.erase arrival)

/-- coll predecessor用にsourceを一個追加したsite集合。 -/
def collisionPredecessorSites {p : QParameters}
    (output : QConfiguration p) (source : QSite p) : Finset (QSite p) :=
  insert source output.1

/--
row oracleの純粋参照関数。event branchではarrivalを逆移動してsourceを作り、repは置換、
collは一粒子追加によりpredecessorを構成する。
-/
def rowReference {p : QParameters}
    (output : QConfiguration p) (selector : QSelector p) :
    Option (RowReferenceResult p) :=
  match _selected : configurationSlot? output (selectorSlot selector) with
  | none => none
  | some arrival =>
      if _diagonal : (selectorOffset selector).val < 2 then
        some ⟨output, selector⟩
      else
        let direction := selectorDirection selector
        let source := moveSiteBackward arrival.1 direction
        if _absent : source ∉ output.1 then
          if collisionBranch : selectorRequestsCollision selector = true then
            if degreeRoom : output.1.card < p.K then
              let predecessorSites := collisionPredecessorSites output source
              have nonempty : predecessorSites.Nonempty :=
                ⟨source, Finset.mem_insert_self _ _⟩
              have cardBound : predecessorSites.card ≤ p.K := by
                calc
                  predecessorSites.card ≤ output.1.card + 1 :=
                    Finset.card_insert_le _ _
                  _ ≤ p.K := by omega
              let predecessor : QConfiguration p :=
                ⟨predecessorSites, Finset.one_le_card.mpr nonempty, cardBound⟩
              have sourceMember : source ∈ predecessor.1 := Finset.mem_insert_self _ _
              some ⟨predecessor,
                selectorOfSlotOffset (slotOfMember predecessor source sourceMember)
                  (selectorOffset selector)⟩
            else
              none
          else
            let predecessorSites := replacementPredecessorSites output arrival.1 source
            have nonempty : predecessorSites.Nonempty :=
              ⟨source, Finset.mem_insert_self _ _⟩
            have cardBound : predecessorSites.card ≤ p.K := by
              calc
                predecessorSites.card ≤ (output.1.erase arrival.1).card + 1 :=
                  Finset.card_insert_le _ _
                _ = output.1.card := by
                  rw [Finset.card_erase_of_mem arrival.2]
                  omega
                _ ≤ p.K := output.2.2
            let predecessor : QConfiguration p :=
              ⟨predecessorSites, Finset.one_le_card.mpr nonempty, cardBound⟩
            have sourceMember : source ∈ predecessor.1 := Finset.mem_insert_self _ _
            some ⟨predecessor,
              selectorOfSlotOffset (slotOfMember predecessor source sourceMember)
                (selectorOffset selector)⟩
        else
          none

/-- row側でも各実在slotの二つのdiag selectorは同じ配置を返す。 -/
theorem rowReference_diagonal
    {p : QParameters} (output : QConfiguration p)
    (site : QSite p) (member : site ∈ output.1) (copy : Fin 2) :
    rowReference output
        (selectorOfSlotOffset (slotOfMember output site member)
          ⟨copy.val, lt_trans copy.isLt (by decide)⟩) =
      some ⟨output,
        selectorOfSlotOffset (slotOfMember output site member)
          ⟨copy.val, lt_trans copy.isLt (by decide)⟩⟩ := by
  let selector := selectorOfSlotOffset (slotOfMember output site member)
    ⟨copy.val, lt_trans copy.isLt (by decide)⟩
  have selected : configurationSlot? output (selectorSlot selector) =
      some ⟨site, member⟩ := by
    simp [selector]
  have diagonal : (selectorOffset selector).val < 2 := by
    simp [selector]
    omega
  change rowReference output selector = some ⟨output, selector⟩
  unfold rowReference
  rw [selected]
  simp [diagonal]

/-- 物理eventの実際の衝突有無。 -/
def eventCollision {p : QParameters}
    (input : QConfiguration p) (source : QSite p) (direction : QDirection) : Bool :=
  decide (moveSite source direction ∈ input.1.erase source)

/-- 物理eventの更新後配置。 -/
def eventOutput {p : QParameters}
    (input : QConfiguration p) (source : QSite p) (direction : QDirection) :
    QConfiguration p :=
  updateConfiguration input (source, direction)

/-- column側eventが返すrow selectorを純粋に構成する。 -/
def rowSelectorForEvent {p : QParameters}
    (input : QConfiguration p) (source : QSite p) (member : source ∈ input.1)
    (direction : QDirection) : QSelector p :=
  let output := eventOutput input source direction
  let moved := moveSite source direction
  have movedMember : moved ∈ output.1 :=
    moveSite_mem_updateConfiguration input (source, direction) member
  selectorOfSlotOffset (slotOfMember output moved movedMember)
    (eventOffset direction (eventCollision input source direction))

/-- 非衝突eventをrow側で逆算すると元の配置集合へ戻る。 -/
theorem replacementPredecessor_event_eq
    {p : QParameters} (input : QConfiguration p)
    (source : QSite p) (member : source ∈ input.1) (direction : QDirection)
    (noCollision : moveSite source direction ∉ input.1.erase source) :
    replacementPredecessorSites (eventOutput input source direction)
        (moveSite source direction) source = input.1 := by
  apply Finset.ext
  intro site
  simp [replacementPredecessorSites, eventOutput,
    updateConfiguration_sites_active input (source, direction) member,
    noCollision, member]

/-- 衝突eventをrow側で逆算すると元の配置集合へ戻る。 -/
theorem collisionPredecessor_event_eq
    {p : QParameters} (input : QConfiguration p)
    (source : QSite p) (member : source ∈ input.1) (direction : QDirection)
    (collision : moveSite source direction ∈ input.1.erase source) :
    collisionPredecessorSites (eventOutput input source direction) source = input.1 := by
  rw [collisionPredecessorSites, eventOutput,
    updateConfiguration_sites_active input (source, direction) member]
  rw [Finset.insert_eq_self.mpr collision]
  exact Finset.insert_erase member

/--
activeな物理eventをcolumn側で生成した後、そのrow selectorをrow側で逆算すると、
元の配置と同じcolumn selectorへ厳密に戻る。
-/
theorem rowReference_rowSelectorForEvent
    {p : QParameters} (input : QConfiguration p)
    (source : QSite p) (member : source ∈ input.1) (direction : QDirection) :
    rowReference (eventOutput input source direction)
        (rowSelectorForEvent input source member direction) =
      some ⟨input, selectorForEvent input source member direction⟩ := by
  let output := eventOutput input source direction
  let moved := moveSite source direction
  let collision : Bool := eventCollision input source direction
  let rowSelector := rowSelectorForEvent input source member direction
  let columnSelector := selectorForEvent input source member direction
  have movedMember : moved ∈ output.1 := by
    exact moveSite_mem_updateConfiguration input (source, direction) member
  have selected : configurationSlot? output (selectorSlot rowSelector) =
      some ⟨moved, movedMember⟩ := by
    simp [rowSelector, rowSelectorForEvent, output, moved]
  have notDiagonal : ¬(selectorOffset rowSelector).val < 2 := by
    simpa [rowSelector, rowSelectorForEvent, collision] using
      eventOffset_not_diagonal direction collision
  have sourceRecovered : moveSiteBackward moved direction = source := by
    simp [moved]
  have sourceAbsent : source ∉ output.1 := by
    exact source_not_mem_updateConfiguration input (source, direction) member
  change rowReference output rowSelector = some ⟨input, columnSelector⟩
  unfold rowReference
  rw [selected]
  simp only [notDiagonal, dite_false]
  simp only [rowSelector, rowSelectorForEvent, selectorDirection_eventOffset,
    moved, sourceRecovered]
  split
  · by_cases collisionProperty : moved ∈ input.1.erase source
    · have collisionTrue : collision = true := by
        simp [collision, eventCollision, moved, collisionProperty]
      have eventCollisionValue : eventCollision input source direction = true := by
        simp only [eventCollision, decide_eq_true_eq]
        exact collisionProperty
      split
      · rename_i branchCondition
        have degreeRoom : output.1.card < p.K := by
          have cardDrop := updateConfiguration_card_add_one_of_collision
            input (source, direction) member collisionProperty
          change (updateConfiguration input (source, direction)).1.card < p.K
          omega
        split
        · rename_i actualDegreeRoom
          have sitesEqual : collisionPredecessorSites output source = input.1 := by
            simpa [output, moved] using
              collisionPredecessor_event_eq input source member direction collisionProperty
          let predecessorSites := collisionPredecessorSites output source
          have predecessorNonempty : predecessorSites.Nonempty := by
            exact ⟨source, Finset.mem_insert_self _ _⟩
          have predecessorCardBound : predecessorSites.card ≤ p.K := by
            calc
              predecessorSites.card ≤ output.1.card + 1 :=
                Finset.card_insert_le _ _
              _ ≤ p.K := by omega
          let predecessor : QConfiguration p :=
            ⟨predecessorSites, Finset.one_le_card.mpr predecessorNonempty,
              predecessorCardBound⟩
          have predecessorSourceMember : source ∈ predecessor.1 := by
            exact Finset.mem_insert_self _ _
          have predecessorSitesEqual : predecessor.1 = input.1 := by
            exact sitesEqual
          simp only [columnSelector, selectorForEvent, collision, collisionTrue,
            eventOffset]
          congr 2
          · exact Subtype.ext sitesEqual
          · apply Fin.ext
            simp only [selectorOffset_ofSlotOffset]
            change 6 * (slotOfMember predecessor source predecessorSourceMember).val +
                (eventOffset direction true).val =
              6 * (slotOfMember input source member).val +
                (eventOffset direction
                  (eventCollision input source direction)).val
            simp only [eventCollisionValue]
            congr 1
            exact congrArg (fun value : Nat => 6 * value) <|
              congrArg Fin.val
                (slotOfMember_eq_of_sites_eq predecessor input predecessorSitesEqual
                  source predecessorSourceMember member)
        · rename_i noDegreeRoom
          exact (noDegreeRoom degreeRoom).elim
      · rename_i branchCondition
        exfalso
        apply branchCondition
        simp [eventCollisionValue]
    · have collisionFalse : collision = false := by
        simp [collision, eventCollision, moved, collisionProperty]
      have eventCollisionValue : eventCollision input source direction = false := by
        simp only [eventCollision, decide_eq_false_iff_not]
        exact collisionProperty
      split
      · rename_i branchCondition
        simp [eventCollisionValue] at branchCondition
      · rename_i branchCondition
        have sitesEqual : replacementPredecessorSites output moved source = input.1 := by
          simpa [output, moved] using
            replacementPredecessor_event_eq input source member direction collisionProperty
        let predecessorSites := replacementPredecessorSites output moved source
        have predecessorNonempty : predecessorSites.Nonempty := by
          exact ⟨source, Finset.mem_insert_self _ _⟩
        have predecessorCardBound : predecessorSites.card ≤ p.K := by
          calc
            predecessorSites.card ≤ (output.1.erase moved).card + 1 :=
              Finset.card_insert_le _ _
            _ = output.1.card := by
              rw [Finset.card_erase_of_mem movedMember]
              omega
            _ ≤ p.K := output.2.2
        let predecessor : QConfiguration p :=
          ⟨predecessorSites, Finset.one_le_card.mpr predecessorNonempty,
            predecessorCardBound⟩
        have predecessorSourceMember : source ∈ predecessor.1 := by
          exact Finset.mem_insert_self _ _
        have predecessorSitesEqual : predecessor.1 = input.1 := by
          exact sitesEqual
        simp only [columnSelector, selectorForEvent, collision, collisionFalse,
          eventOffset]
        congr 2
        · exact Subtype.ext sitesEqual
        · apply Fin.ext
          simp only [selectorOffset_ofSlotOffset]
          change 6 * (slotOfMember predecessor source predecessorSourceMember).val +
              (eventOffset direction false).val =
            6 * (slotOfMember input source member).val +
              (eventOffset direction
                (eventCollision input source direction)).val
          simp only [eventCollisionValue]
          congr 1
          exact congrArg (fun value : Nat => 6 * value) <|
            congrArg Fin.val
              (slotOfMember_eq_of_sites_eq predecessor input predecessorSitesEqual
                source predecessorSourceMember member)
  · rename_i sourcePresent
    exact (sourcePresent sourceAbsent).elim

end ProbabilityGeneratorQProof
