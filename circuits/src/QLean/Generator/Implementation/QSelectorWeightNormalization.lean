import QLean.Generator.Implementation.QReferenceOverlapCorrectness
import QLean.Generator.Implementation.QSelectorBasisFiniteSumBridge
import Mathlib.Tactic

/-!
# Q selector 有限和の正規化

column 側と row 側の一様準備がそれぞれ与える `1 / √(6K)` を合成し、
各 selector の符号付き参照寄与の和が厳密に `1 / (6K)` で正規化されることを示す。
この証明は任意の `q,K` を記号のまま扱い、物理基底や行列要素を列挙しない。
-/

namespace ProbabilityGeneratorQProof

open QParameters

noncomputable section

/--
一つのrow selectorへ着地する全column selector pathの参照寄与。
eventでは移動前後でslot番号が変わり得るため、row側の有限和にはこの向きの重みを使う。
-/
def referenceAcceptedRowSelectorWeight {p : QParameters}
    (output input : QConfiguration p) (rowSelector : QSelector p) : ℚ :=
  ∑ columnSelector : QSelector p,
    match columnReference input columnSelector with
    | none => 0
    | some columnResult =>
        if columnResult.rowSelector = rowSelector then
          referenceAcceptedSelectorWeight output input columnSelector
        else 0

/--
row selectorから逆向きにrow参照を一回、その結果のcolumn selectorでcolumn参照を一回
評価して得る符号付き寄与。実回路の基底逆追跡に直接対応する。
-/
def reverseReferenceAcceptedRowSelectorWeight {p : QParameters}
    (output input : QConfiguration p) (rowSelector : QSelector p) : ℚ :=
  match rowReference output rowSelector with
  | none => 0
  | some rowResult =>
      match columnReference input rowResult.columnSelector with
      | none => 0
      | some columnResult =>
          if columnResult.rowSelector = rowSelector ∧
              columnResult.output = output ∧ rowResult.input = input then
            if columnResult.negative then -1 else 1
          else 0

/-- row selectorへ集約した有限和は、row→columnの一意な逆追跡式へ簡約できる。 -/
theorem referenceAcceptedRowSelectorWeight_eq_reverse
    {p : QParameters} (output input : QConfiguration p)
    (rowSelector : QSelector p) :
    referenceAcceptedRowSelectorWeight output input rowSelector =
      reverseReferenceAcceptedRowSelectorWeight output input rowSelector := by
  unfold referenceAcceptedRowSelectorWeight
  cases rowResultEq : rowReference output rowSelector with
  | none =>
      rw [show reverseReferenceAcceptedRowSelectorWeight output input rowSelector = 0 by
        simp [reverseReferenceAcceptedRowSelectorWeight, rowResultEq]]
      apply Fintype.sum_eq_zero
      intro columnSelector
      cases columnResultEq : columnReference input columnSelector with
      | none =>
          simp_all
      | some columnResult =>
          by_cases lands : columnResult.rowSelector = rowSelector
          · simp_all [referenceAcceptedSelectorWeight]
          · simp_all
  | some rowResult =>
      rw [Fintype.sum_eq_single rowResult.columnSelector]
      · cases columnResultEq : columnReference input rowResult.columnSelector with
        | none =>
            simp_all [reverseReferenceAcceptedRowSelectorWeight]
        | some columnResult =>
            by_cases lands : columnResult.rowSelector = rowSelector
            · simp_all [reverseReferenceAcceptedRowSelectorWeight,
                referenceAcceptedSelectorWeight]
            · simp_all [reverseReferenceAcceptedRowSelectorWeight]
      · intro columnSelector different
        cases columnResultEq : columnReference input columnSelector with
        | none =>
            simp_all
        | some columnResult =>
            by_cases lands : columnResult.rowSelector = rowSelector
            · have selectorDifferent :
                  rowResult.columnSelector ≠ columnSelector := Ne.symm different
              simp_all [referenceAcceptedSelectorWeight]
            · simp_all

/-- row selectorごとに集約した寄与の全和は、元のcolumn selector寄与の全和に等しい。 -/
theorem sum_referenceAcceptedRowSelectorWeight
    {p : QParameters} (output input : QConfiguration p) :
    (∑ rowSelector : QSelector p,
      referenceAcceptedRowSelectorWeight output input rowSelector) =
    ∑ columnSelector : QSelector p,
      referenceAcceptedSelectorWeight output input columnSelector := by
  unfold referenceAcceptedRowSelectorWeight
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro columnSelector
  cases columnResult : columnReference input columnSelector with
  | none =>
      simp [columnResult, referenceAcceptedSelectorWeight]
  | some result =>
      simp

/-- 正の自然数を一様準備した二つの振幅の積は、その自然数の逆数である。 -/
theorem uniformAmplitude_mul_self (count : Nat) (positive : 0 < count) :
    (((1 / Real.sqrt (count : ℝ) : ℝ) : ℂ) *
        ((1 / Real.sqrt (count : ℝ) : ℝ) : ℂ)) =
      1 / (count : ℂ) := by
  have countRealPositive : (0 : ℝ) < count := by exact_mod_cast positive
  have sqrtPositive : 0 < Real.sqrt (count : ℝ) :=
    Real.sqrt_pos.2 countRealPositive
  have sqrtSquare : Real.sqrt (count : ℝ) * Real.sqrt (count : ℝ) =
      (count : ℝ) := Real.mul_self_sqrt (le_of_lt countRealPositive)
  have amplitudeReal :
      (1 / Real.sqrt (count : ℝ)) * (1 / Real.sqrt (count : ℝ)) =
        1 / (count : ℝ) := by
    field_simp [ne_of_gt sqrtPositive, ne_of_gt countRealPositive]
    nlinarith [sqrtSquare]
  calc
    (((1 / Real.sqrt (count : ℝ) : ℝ) : ℂ) *
        ((1 / Real.sqrt (count : ℝ) : ℝ) : ℂ)) =
      (((1 / Real.sqrt (count : ℝ)) *
        (1 / Real.sqrt (count : ℝ)) : ℝ) : ℂ) := by norm_num
    _ = ((1 / (count : ℝ) : ℝ) : ℂ) :=
      congrArg (fun value : ℝ => (value : ℂ)) amplitudeReal
    _ = 1 / (count : ℂ) := by norm_num

/--
各物理 selector 基底上の状態振幅が `1 / √(6K)` 倍の参照寄与なら、
row 一様準備との内積は参照 selector 和を `6K` で割った値に一致する。
-/
theorem qRowUniformOverlap_eq_configurationReferenceNormalizedOverlap_of_selector_values
    (p : QParameters)
    (system : RegisterBasis p.systemWidth)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ)
    (output input : QConfiguration p)
    (selectorValues : ∀ selector : QSelector p,
      state (selectorBasisOver p (rowSelectorWire p)
        (zeroAncillaJointBasis p system)
        (selectorBasisOfNat p.selectorWidth selector.val)) =
        ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
          (referenceAcceptedSelectorWeight output input selector : ℂ)) :
    qRowUniformOverlap p system state =
      (configurationReferenceNormalizedOverlap output input : ℂ) := by
  rw [qRowUniformOverlap_eq_qSelector_sum]
  simp_rw [selectorValues]
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum]
  rw [uniformAmplitude_mul_self p.selectorCount p.selectorCount_pos]
  unfold configurationReferenceNormalizedOverlap
  simp only [QParameters.selectorCount]
  push_cast
  ring

/--
各row selector基底上の状態振幅が、そのselectorへ着地する全column path寄与の
`1 / √(6K)`倍なら、row一様内積は正規化済み参照演算子要素に一致する。
-/
theorem qRowUniformOverlap_eq_configurationReferenceNormalizedOverlap_of_row_selector_values
    (p : QParameters)
    (system : RegisterBasis p.systemWidth)
    (state : JointBasis p.ancillaWidth p.systemWidth → ℂ)
    (output input : QConfiguration p)
    (selectorValues : ∀ rowSelector : QSelector p,
      state (selectorBasisOver p (rowSelectorWire p)
        (zeroAncillaJointBasis p system)
        (selectorBasisOfNat p.selectorWidth rowSelector.val)) =
        ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
          (referenceAcceptedRowSelectorWeight output input rowSelector : ℂ)) :
    qRowUniformOverlap p system state =
      (configurationReferenceNormalizedOverlap output input : ℂ) := by
  rw [qRowUniformOverlap_eq_qSelector_sum]
  simp_rw [selectorValues]
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum]
  rw [uniformAmplitude_mul_self p.selectorCount p.selectorCount_pos]
  have castSum :
      (∑ rowSelector : QSelector p,
        (referenceAcceptedRowSelectorWeight output input rowSelector : ℂ)) =
      ((∑ rowSelector : QSelector p,
        referenceAcceptedRowSelectorWeight output input rowSelector : ℚ) : ℂ) := by
    push_cast
    rfl
  rw [castSum, sum_referenceAcceptedRowSelectorWeight output input]
  unfold configurationReferenceNormalizedOverlap
  simp only [QParameters.selectorCount]
  push_cast
  ring

end

end ProbabilityGeneratorQProof
