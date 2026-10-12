import QLean.Generator.Analysis.QGenerator
import Mathlib.Tactic

/-!
# 固定幅selectorと一般Q要素の内積公式

selectorを`ℓ = 6i + o`として型安全に分解・再構成する。また、配置eventの数え上げから
得られる正規化内積を物理delimiter空間へ埋め込み、`Q/(3K)`との一致を一般`q,K`で示す。
-/

open Matrix

namespace ProbabilityGeneratorQProof

open QParameters

/-- `6K`個の有効selector値。 -/
abbrev QSelector (p : QParameters) := Fin p.selectorCount

/-- selector `ℓ`が指すslot `⌊ℓ/6⌋`。 -/
def selectorSlot {p : QParameters} (selector : QSelector p) : Fin p.K := by
  refine ⟨selector.val / 6, ?_⟩
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  simpa [QParameters.selectorCount, Nat.mul_comm] using selector.isLt

/-- selector `ℓ`のoffset `ℓ mod 6`。 -/
def selectorOffset {p : QParameters} (selector : QSelector p) : Fin 6 :=
  ⟨selector.val % 6, Nat.mod_lt _ (by decide)⟩

/-- slotとoffsetからselector `6i+o`を構成する。 -/
def selectorOfSlotOffset {p : QParameters} (slot : Fin p.K) (offset : Fin 6) :
    QSelector p := by
  refine ⟨6 * slot.val + offset.val, ?_⟩
  simp only [QParameters.selectorCount]
  omega

/-- slotとoffsetから作ったselectorのslotを読むと元へ戻る。 -/
@[simp] theorem selectorSlot_ofSlotOffset
    {p : QParameters} (slot : Fin p.K) (offset : Fin 6) :
    selectorSlot (selectorOfSlotOffset slot offset) = slot := by
  apply Fin.ext
  simp [selectorSlot, selectorOfSlotOffset, Nat.mul_add_div,
    Nat.div_eq_of_lt offset.isLt]

/-- slotとoffsetから作ったselectorのoffsetを読むと元へ戻る。 -/
@[simp] theorem selectorOffset_ofSlotOffset
    {p : QParameters} (slot : Fin p.K) (offset : Fin 6) :
    selectorOffset (selectorOfSlotOffset slot offset) = offset := by
  apply Fin.ext
  simp [selectorOffset, selectorOfSlotOffset, Nat.mod_eq_of_lt offset.isLt]

/-- selectorをslotとoffsetへ分解して再構成すると元へ戻る。 -/
@[simp] theorem selectorOfSlotOffset_parts
    {p : QParameters} (selector : QSelector p) :
    selectorOfSlotOffset (selectorSlot selector) (selectorOffset selector) = selector := by
  apply Fin.ext
  simp only [selectorOfSlotOffset, selectorSlot, selectorOffset]
  exact Nat.div_add_mod selector.val 6

/-- offset 0,1が二つの負の対角copyであることを表す。 -/
def selectorIsDiagonal {p : QParameters} (selector : QSelector p) : Bool :=
  decide ((selectorOffset selector).val < 2)

/-- event offset 2,3は右、4,5は上を表す。 -/
def selectorDirection {p : QParameters} (selector : QSelector p) : QDirection :=
  if (selectorOffset selector).val < 4 then .right else .up

/-- event offset 3,5が衝突branch、2,4が非衝突branchであることを表す。 -/
def selectorRequestsCollision {p : QParameters} (selector : QSelector p) : Bool :=
  decide ((selectorOffset selector).val % 2 = 1)

/-- 合法配置上の未正規化column/row selector内積。 -/
def configurationRawSelectorOverlap {p : QParameters}
    (output input : QConfiguration p) : ℚ :=
  TechnicalReportQ.rawSelectorOverlap configurationParticleCount
    configurationEvents updateConfiguration output input

/-- 両側で`6K` selectorを一様準備した後の正規化内積。 -/
def configurationNormalizedSelectorOverlap {p : QParameters}
    (output input : QConfiguration p) : ℚ :=
  TechnicalReportQ.normalizedSelectorOverlap p.K configurationParticleCount
    configurationEvents updateConfiguration output input

/-- 一般周期格子のselector内積は厳密に`Q/(3K)`である。 -/
theorem configurationNormalizedSelectorOverlap_eq_generator_div
    {p : QParameters} (output input : QConfiguration p) :
    configurationNormalizedSelectorOverlap output input =
      configurationProbabilityGenerator output input / (3 * (p.K : ℚ)) := by
  exact TechnicalReportQ.normalizedSelectorOverlap_eq_probabilityGenerator_div
    p.K p.K_pos configurationParticleCount configurationEvents updateConfiguration
      configuration_noSelfLoop output input

/-- 物理delimiter空間上へ埋め込んだ正規化selector内積行列。 -/
noncomputable def RowSelectorPathFiniteSumSuccessBlockSpec (p : QParameters) :
    Operator (RegisterBasis p.systemWidth) :=
  Matrix.of fun output input =>
    match decodeDelimiter output, decodeDelimiter input with
    | some outputConfiguration, some inputConfiguration =>
        (configurationNormalizedSelectorOverlap outputConfiguration inputConfiguration : ℂ)
    | _, _ => 0

/-- 物理全空間上でもselector内積行列は厳密に`Q/(3K)`である。 -/
theorem RowSelectorPathFiniteSumSuccessBlockSpec_eq_scaled_generator (p : QParameters) :
    RowSelectorPathFiniteSumSuccessBlockSpec p =
      ((1 : ℂ) / (3 * (p.K : ℂ))) • embeddedProbabilityGenerator p := by
  have nonzeroK : (p.K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt p.K_pos)
  ext output input
  simp only [RowSelectorPathFiniteSumSuccessBlockSpec, embeddedProbabilityGenerator, Matrix.of_apply]
  cases outputDecoded : decodeDelimiter output with
  | none => simp [outputDecoded]
  | some outputConfiguration =>
      cases inputDecoded : decodeDelimiter input with
      | none => simp [outputDecoded, inputDecoded]
      | some inputConfiguration =>
          simp [outputDecoded, inputDecoded]
          rw [configurationNormalizedSelectorOverlap_eq_generator_div]
          push_cast
          field_simp [nonzeroK]

end ProbabilityGeneratorQProof
