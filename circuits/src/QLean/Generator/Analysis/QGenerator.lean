import QLean.Generator.Analysis.QEncoding
import QLean.Generator.Analysis.ProbabilityGenerator
import Mathlib.Tactic

/-!
# 一般周期格子の確率生成子と物理空間への埋込み

`G = 2^q`の二次元周期格子上で右・上移動と合体を定義し、技術レポートの確率生成子
`Q`を全`2qK+1`量子ビットsystem空間へ埋め込む。不合法delimiterを含む行列要素は
定義により0である。
-/

open Matrix

namespace ProbabilityGeneratorQProof

open QParameters

/-- 技術レポートで許す右・上の二方向。 -/
inductive QDirection where
  | right
  | up
deriving DecidableEq, Fintype, Repr

/-- 線形化siteを`(y,x)`座標へ戻す。 -/
def siteCoordinates {p : QParameters} (site : QSite p) : Fin p.G × Fin p.G :=
  finProdFinEquiv.symm site

/-- `(y,x)`座標を線形化siteへ変換する。 -/
def siteOfCoordinates {p : QParameters} (coordinates : Fin p.G × Fin p.G) : QSite p :=
  finProdFinEquiv coordinates

/-- `Fin G`座標を周期境界条件付きで1増やす。 -/
def incrementCoordinate {p : QParameters} (coordinate : Fin p.G) : Fin p.G :=
  ⟨(coordinate.val + 1) % p.G,
    Nat.mod_lt _ (by simp [QParameters.G])⟩

/-- `G = 2^q, q>0`では周期incrementで座標は同じ値に留まらない。 -/
theorem incrementCoordinate_ne_self
    {p : QParameters} (coordinate : Fin p.G) :
    incrementCoordinate coordinate ≠ coordinate := by
  have sideGreaterOne : 1 < p.G := by
    simp [QParameters.G, Nat.ne_of_gt p.q_pos]
  intro equal
  have valueEqual := congrArg Fin.val equal
  change (coordinate.val + 1) % p.G = coordinate.val at valueEqual
  by_cases noWrap : coordinate.val + 1 < p.G
  · rw [Nat.mod_eq_of_lt noWrap] at valueEqual
    omega
  · have wrapsExactly : coordinate.val + 1 = p.G := by omega
    rw [wrapsExactly, Nat.mod_self] at valueEqual
    omega

/-- `Fin G`座標を周期境界条件付きで1減らす。 -/
def decrementCoordinate {p : QParameters} (coordinate : Fin p.G) : Fin p.G := by
  if zero : coordinate.val = 0 then
    exact ⟨p.G - 1, Nat.sub_lt (by simp [QParameters.G]) (by decide)⟩
  else
    exact ⟨coordinate.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) coordinate.isLt⟩

/-- 周期decrementの後にincrementすると元の座標へ戻る。 -/
@[simp] theorem increment_decrement_coordinate
    {p : QParameters} (coordinate : Fin p.G) :
    incrementCoordinate (decrementCoordinate coordinate) = coordinate := by
  apply Fin.ext
  have sidePositive : 0 < p.G := by simp [QParameters.G]
  by_cases zero : coordinate.val = 0
  · have cycle : (p.G - 1 + 1) % p.G = 0 := by
      rw [Nat.sub_add_cancel sidePositive, Nat.mod_self]
    simp [decrementCoordinate, zero, incrementCoordinate, cycle]
  · have predecessorSucc : coordinate.val - 1 + 1 = coordinate.val := by omega
    simp [decrementCoordinate, zero, incrementCoordinate, predecessorSucc,
      Nat.mod_eq_of_lt coordinate.isLt]

/-- 周期incrementの後にdecrementすると元の座標へ戻る。 -/
@[simp] theorem decrement_increment_coordinate
    {p : QParameters} (coordinate : Fin p.G) :
    decrementCoordinate (incrementCoordinate coordinate) = coordinate := by
  apply Fin.ext
  by_cases wrap : coordinate.val + 1 = p.G
  · have coordinateValue : coordinate.val = p.G - 1 := by omega
    have sidePositive : 0 < p.G := by simp [QParameters.G]
    have cycle : (p.G - 1 + 1) % p.G = 0 := by
      rw [Nat.sub_add_cancel sidePositive, Nat.mod_self]
    simp [incrementCoordinate, decrementCoordinate, coordinateValue, cycle]
  · have noWrap : coordinate.val + 1 < p.G := by omega
    simp [incrementCoordinate, Nat.mod_eq_of_lt noWrap, decrementCoordinate]

/-- 指定siteを右または上へ周期境界条件付きで一歩移動する。 -/
def moveSite {p : QParameters} (site : QSite p) (direction : QDirection) : QSite p :=
  let coordinates := siteCoordinates site
  match direction with
  | .right => siteOfCoordinates (coordinates.1, incrementCoordinate coordinates.2)
  | .up => siteOfCoordinates (incrementCoordinate coordinates.1, coordinates.2)

/-- 指定siteを右または上方向の逆へ周期境界条件付きで一歩戻す。 -/
def moveSiteBackward {p : QParameters}
    (site : QSite p) (direction : QDirection) : QSite p :=
  let coordinates := siteCoordinates site
  match direction with
  | .right => siteOfCoordinates (coordinates.1, decrementCoordinate coordinates.2)
  | .up => siteOfCoordinates (decrementCoordinate coordinates.1, coordinates.2)

/-- 一歩戻してから同じ方向へ進むと元のsiteへ戻る。 -/
@[simp] theorem moveSite_moveSiteBackward
    {p : QParameters} (site : QSite p) (direction : QDirection) :
    moveSite (moveSiteBackward site direction) direction = site := by
  apply (Equiv.injective finProdFinEquiv.symm)
  cases direction <;> simp [moveSite, moveSiteBackward, siteCoordinates,
    siteOfCoordinates]

/-- 一歩進んでから同じ方向へ戻すと元のsiteへ戻る。 -/
@[simp] theorem moveSiteBackward_moveSite
    {p : QParameters} (site : QSite p) (direction : QDirection) :
    moveSiteBackward (moveSite site direction) direction = site := by
  apply (Equiv.injective finProdFinEquiv.symm)
  cases direction <;> simp [moveSite, moveSiteBackward, siteCoordinates,
    siteOfCoordinates]

/-- 右・上の一歩移動は元のsiteと異なる。 -/
theorem moveSite_ne_self {p : QParameters} (site : QSite p) (direction : QDirection) :
    moveSite site direction ≠ site := by
  intro equal
  have coordinateEqual := congrArg siteCoordinates equal
  cases direction with
  | right =>
      have xEqual := congrArg Prod.snd coordinateEqual
      simp [moveSite, siteCoordinates, siteOfCoordinates] at xEqual
      exact incrementCoordinate_ne_self _ xEqual
  | up =>
      have yEqual := congrArg Prod.fst coordinateEqual
      simp [moveSite, siteCoordinates, siteOfCoordinates] at yEqual
      exact incrementCoordinate_ne_self _ yEqual

/-- 一つの物理移動eventをsource siteと方向の組として表す。 -/
abbrev QEvent (p : QParameters) := QSite p × QDirection

/-- sourceを消し、移動先を挿入する配置更新。既占有ならFinset挿入により合体する。 -/
def updateSiteSet {p : QParameters} (sites : Finset (QSite p)) (event : QEvent p) :
    Finset (QSite p) :=
  if event.1 ∈ sites then
    insert (moveSite event.1 event.2) (sites.erase event.1)
  else
    sites

/-- active eventによる更新後の粒子数は更新前を超えない。 -/
theorem card_updateSiteSet_le
    {p : QParameters} (sites : Finset (QSite p)) (event : QEvent p)
    (active : event.1 ∈ sites) :
    (updateSiteSet sites event).card ≤ sites.card := by
  have positiveCard : 0 < sites.card := Finset.card_pos.mpr ⟨event.1, active⟩
  rw [updateSiteSet, if_pos active]
  calc
    (insert (moveSite event.1 event.2) (sites.erase event.1)).card ≤
        (sites.erase event.1).card + 1 := Finset.card_insert_le _ _
    _ = sites.card := by
      rw [Finset.card_erase_of_mem active]
      omega

/-- active eventによる更新後配置は空でない。 -/
theorem updateSiteSet_nonempty
    {p : QParameters} (sites : Finset (QSite p)) (event : QEvent p)
    (active : event.1 ∈ sites) :
    (updateSiteSet sites event).Nonempty := by
  rw [updateSiteSet, if_pos active]
  exact ⟨moveSite event.1 event.2, Finset.mem_insert_self _ _⟩

/-- 合法配置上の全域的な更新関数。inactive sourceでは入力配置をそのまま返す。 -/
def updateConfiguration {p : QParameters}
    (input : QConfiguration p) (event : QEvent p) : QConfiguration p := by
  by_cases active : event.1 ∈ input.1
  · exact ⟨updateSiteSet input.1 event,
      ⟨Finset.one_le_card.mpr (updateSiteSet_nonempty input.1 event active),
        le_trans (card_updateSiteSet_le input.1 event active) input.2.2⟩⟩
  · exact input

/-- active eventの移動先siteは更新後配置に必ず含まれる。 -/
theorem moveSite_mem_updateConfiguration
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) :
    moveSite event.1 event.2 ∈ (updateConfiguration input event).1 := by
  simp [updateConfiguration, active, updateSiteSet]

/-- active eventでは更新後site集合が`insert moved (erase source)`に展開できる。 -/
theorem updateConfiguration_sites_active
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) :
    (updateConfiguration input event).1 =
      insert (moveSite event.1 event.2) (input.1.erase event.1) := by
  simp [updateConfiguration, active, updateSiteSet]

/-- active eventのsourceは、自己loopがないため更新後配置から必ず消える。 -/
theorem source_not_mem_updateConfiguration
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1) :
    event.1 ∉ (updateConfiguration input event).1 := by
  rw [updateConfiguration_sites_active input event active]
  simp only [Finset.mem_insert, Finset.mem_erase]
  intro member
  rcases member with equal | ⟨different, _member⟩
  · exact (moveSite_ne_self event.1 event.2).symm equal
  · exact different rfl

/-- 衝突eventでは更新後の粒子数がちょうど一個減る。 -/
theorem updateConfiguration_card_add_one_of_collision
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1)
    (collision : moveSite event.1 event.2 ∈ input.1.erase event.1) :
    (updateConfiguration input event).1.card + 1 = input.1.card := by
  have positiveCard : 0 < input.1.card := Finset.card_pos.mpr ⟨event.1, active⟩
  rw [updateConfiguration_sites_active input event active]
  rw [Finset.insert_eq_self.mpr collision]
  rw [Finset.card_erase_of_mem active]
  omega

/-- 非衝突eventでは更新後の粒子数が更新前と等しい。 -/
theorem updateConfiguration_card_of_noCollision
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (active : event.1 ∈ input.1)
    (noCollision : moveSite event.1 event.2 ∉ input.1.erase event.1) :
    (updateConfiguration input event).1.card = input.1.card := by
  rw [updateConfiguration_sites_active input event active]
  rw [Finset.card_insert_of_notMem noCollision]
  rw [Finset.card_erase_of_mem active]
  omega

/-- 入力配置の各occupied siteに右・上を割り当てたactive event集合。 -/
def configurationEvents {p : QParameters} (input : QConfiguration p) :
    Finset (QEvent p) :=
  input.1.product Finset.univ

/-- 配置に含まれる粒子数。 -/
def configurationParticleCount {p : QParameters} (input : QConfiguration p) : Nat :=
  input.1.card

/-- active event集合には各粒子につき右・上のちょうど2個が含まれる。 -/
theorem configurationEvents_card {p : QParameters} (input : QConfiguration p) :
    (configurationEvents input).card = 2 * configurationParticleCount input := by
  have directionCard : Fintype.card QDirection = 2 := by decide
  simp [configurationEvents, configurationParticleCount, directionCard,
    Finset.card_product, Nat.mul_comm]

/-- 一歩移動するactive eventは自己ループ配置を作らない。 -/
theorem configuration_noSelfLoop
    {p : QParameters} (input : QConfiguration p) (event : QEvent p)
    (eventMember : event ∈ configurationEvents input) :
    updateConfiguration input event ≠ input := by
  have active : event.1 ∈ input.1 := by
    simpa [configurationEvents] using (Finset.mem_product.mp eventMember).1
  intro equal
  have valueEqual : (updateConfiguration input event).1 = input.1 :=
    congrArg Subtype.val equal
  have sourceStillPresent : event.1 ∈ (updateConfiguration input event).1 := by
    rw [valueEqual]
    exact active
  have sourceDiffers : event.1 ≠ moveSite event.1 event.2 :=
    Ne.symm (moveSite_ne_self event.1 event.2)
  simp [updateConfiguration, active, updateSiteSet, sourceDiffers] at sourceStillPresent

/-- 合法配置空間上の技術レポートの確率生成子要素。 -/
def configurationProbabilityGenerator {p : QParameters}
    (output input : QConfiguration p) : ℚ :=
  TechnicalReportQ.probabilityGenerator configurationParticleCount
    configurationEvents updateConfiguration output input

/--
物理system全空間上の確率生成子。両側が合法delimiterならレポートの`Q`、どちらかが
不合法なら0とする。
-/
noncomputable def embeddedProbabilityGenerator (p : QParameters) :
    Operator (RegisterBasis p.systemWidth) :=
  Matrix.of fun output input =>
    match decodeDelimiter output, decodeDelimiter input with
    | some outputConfiguration, some inputConfiguration =>
        (configurationProbabilityGenerator outputConfiguration inputConfiguration : ℂ)
    | _, _ => 0

/-- 合法delimiter間では埋込み生成子が配置空間上の`Q`と一致する。 -/
@[simp] theorem embeddedProbabilityGenerator_encoding
    {p : QParameters} (output input : QConfiguration p) :
    embeddedProbabilityGenerator p (delimiterEncoding output) (delimiterEncoding input) =
      (configurationProbabilityGenerator output input : ℂ) := by
  simp [embeddedProbabilityGenerator]

/-- 不合法な出力bit列を含む埋込み生成子要素は0である。 -/
theorem embeddedProbabilityGenerator_illegal_output
    {p : QParameters} (output input : RegisterBasis p.systemWidth)
    (illegal : ¬IsLegalDelimiter output) :
    embeddedProbabilityGenerator p output input = 0 := by
  have decoded : decodeDelimiter output = none := decodeDelimiter_eq_none_iff.mpr illegal
  simp [embeddedProbabilityGenerator, decoded]

/-- 不合法な入力bit列を含む埋込み生成子要素は0である。 -/
theorem embeddedProbabilityGenerator_illegal_input
    {p : QParameters} (output input : RegisterBasis p.systemWidth)
    (illegal : ¬IsLegalDelimiter input) :
    embeddedProbabilityGenerator p output input = 0 := by
  have decoded : decodeDelimiter input = none := decodeDelimiter_eq_none_iff.mpr illegal
  simp [embeddedProbabilityGenerator, decoded]

end ProbabilityGeneratorQProof
