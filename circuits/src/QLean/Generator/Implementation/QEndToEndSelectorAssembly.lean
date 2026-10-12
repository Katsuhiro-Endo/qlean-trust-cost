import QLean.Generator.Implementation.QSelectorWeightNormalization
import QLean.Generator.Implementation.UQBlockEncodingAssembly

/-!
# selector ごとの実回路証明から success block への合成

実回路の column/row oracle を通る selector 一本ごとの振幅仕様を、全 selector の有限和、
`6K` 正規化、delimiter の合法・非合法場合分けまで一度に持ち上げる。
この層は行列要素を展開せず、任意の物理 system 基底をそのまま扱う。
-/

namespace ProbabilityGeneratorQProof

open QParameters
open Matrix

noncomputable section

/-- 最後の row 一様準備逆回路直前で評価する、canonical な物理 selector 基底。 -/
def qFinalRowSelectorBasis (p : QParameters)
    (system : RegisterBasis p.systemWidth) (selector : QSelector p) :
    JointBasis p.ancillaWidth p.systemWidth :=
  selectorBasisOver p (rowSelectorWire p)
    (zeroAncillaJointBasis p system)
    (selectorBasisOfNat p.selectorWidth selector.val)

/--
参照関数が予言するrow selector一本の振幅。両system基底が合法delimiterのときだけ、
そのrow selectorへ着地する全column path寄与を返し、それ以外の物理基底では`0`とする。
-/
def expectedQSelectorAmplitude (p : QParameters)
    (output input : RegisterBasis p.systemWidth) (selector : QSelector p) : ℂ :=
  match decodeDelimiter output, decodeDelimiter input with
  | some outputConfiguration, some inputConfiguration =>
      ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
        (referenceAcceptedRowSelectorWeight
          outputConfiguration inputConfiguration selector : ℂ)
  | _, _ => 0

/-- 実回路の逆追跡に直接対応する、row→column参照式で書いた同じ期待振幅。 -/
def PrefixAmplitudeReferenceCaseSpec (p : QParameters)
    (output input : RegisterBasis p.systemWidth) (rowSelector : QSelector p) : ℂ :=
  match decodeDelimiter output, decodeDelimiter input with
  | some outputConfiguration, some inputConfiguration =>
      ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
        (reverseReferenceAcceptedRowSelectorWeight
          outputConfiguration inputConfiguration rowSelector : ℂ)
  | _, _ => 0

/-- 逆追跡式の期待振幅は、row selectorへ集約した期待振幅と点ごとに等しい。 -/
theorem PrefixAmplitudeReferenceCaseSpec_eq
    (p : QParameters) (output input : RegisterBasis p.systemWidth)
    (rowSelector : QSelector p) :
    PrefixAmplitudeReferenceCaseSpec p output input rowSelector =
      expectedQSelectorAmplitude p output input rowSelector := by
  unfold PrefixAmplitudeReferenceCaseSpec expectedQSelectorAmplitude
  cases outputDecoded : decodeDelimiter output with
  | none => rfl
  | some outputConfiguration =>
      cases inputDecoded : decodeDelimiter input with
      | none => rfl
      | some inputConfiguration =>
          simp only
          rw [referenceAcceptedRowSelectorWeight_eq_reverse]

/-- 合法delimiter入出力では、逆追跡期待振幅は参照符号付き寄与の一様振幅倍である。 -/
@[simp] theorem PrefixAmplitudeReferenceCaseSpec_encoding
    {p : QParameters} (output input : QConfiguration p)
    (rowSelector : QSelector p) :
    PrefixAmplitudeReferenceCaseSpec p
        (delimiterEncoding output) (delimiterEncoding input) rowSelector =
      ((1 / Real.sqrt (p.selectorCount : ℝ) : ℝ) : ℂ) *
        (reverseReferenceAcceptedRowSelectorWeight output input rowSelector : ℂ) := by
  simp [PrefixAmplitudeReferenceCaseSpec]

/-- row参照が拒否するselectorの逆追跡期待振幅は0である。 -/
theorem PrefixAmplitudeReferenceCaseSpec_of_row_none
    {p : QParameters} (output input : QConfiguration p)
    (rowSelector : QSelector p)
    (rejected : rowReference output rowSelector = none) :
    PrefixAmplitudeReferenceCaseSpec p
        (delimiterEncoding output) (delimiterEncoding input) rowSelector = 0 := by
  simp [PrefixAmplitudeReferenceCaseSpec, reverseReferenceAcceptedRowSelectorWeight,
    rejected]

/-- row参照後のcolumn参照が拒否するselectorの逆追跡期待振幅も0である。 -/
theorem PrefixAmplitudeReferenceCaseSpec_of_column_none
    {p : QParameters} (output input : QConfiguration p)
    (rowSelector : QSelector p) (rowResult : RowReferenceResult p)
    (rowAccepted : rowReference output rowSelector = some rowResult)
    (columnRejected : columnReference input rowResult.columnSelector = none) :
    PrefixAmplitudeReferenceCaseSpec p
        (delimiterEncoding output) (delimiterEncoding input) rowSelector = 0 := by
  simp [PrefixAmplitudeReferenceCaseSpec, reverseReferenceAcceptedRowSelectorWeight,
    rowAccepted, columnRejected]

/--
任意の物理入出力と selector について実回路振幅が参照仕様に一致すれば、
実 `uqCircuit` の success block は埋込み済み参照演算子そのものになる。
-/
theorem uqCircuit_successBlock_eq_embeddedReference_of_selector_values
    (p : QParameters)
    (selectorValues : ∀ output input selector,
      qBeforeRowUniformInverseState p input
          (qFinalRowSelectorBasis p output selector) =
        expectedQSelectorAmplitude p output input selector) :
    qubitSuccessBlock (allZeroAncilla p.ancillaWidth)
        ((uqCircuit p).toIdealOperator primitiveGateOperator) =
      embeddedReferenceSelectorOverlap p := by
  ext output input
  rw [uqCircuit_successBlock_eq_rowUniformOverlap]
  cases outputDecoded : decodeDelimiter output with
  | none =>
      rw [qRowUniformOverlap_eq_qSelector_sum]
      have values := selectorValues output input
      simp only [qFinalRowSelectorBasis] at values
      simp_rw [values]
      simp [expectedQSelectorAmplitude, outputDecoded,
        embeddedReferenceSelectorOverlap]
  | some outputConfiguration =>
      cases inputDecoded : decodeDelimiter input with
      | none =>
          rw [qRowUniformOverlap_eq_qSelector_sum]
          have values := selectorValues output input
          simp only [qFinalRowSelectorBasis] at values
          simp_rw [values]
          simp [expectedQSelectorAmplitude, outputDecoded, inputDecoded,
            embeddedReferenceSelectorOverlap]
      | some inputConfiguration =>
          rw [qRowUniformOverlap_eq_configurationReferenceNormalizedOverlap_of_row_selector_values
            p output (qBeforeRowUniformInverseState p input)
              outputConfiguration inputConfiguration]
          · simp [embeddedReferenceSelectorOverlap, outputDecoded, inputDecoded]
          · intro selector
            simpa [qFinalRowSelectorBasis, expectedQSelectorAmplitude,
              outputDecoded, inputDecoded] using selectorValues output input selector

/--
selector 一本ごとの実回路振幅仕様から、誤差 `0`・正規化係数 `3K` の最終
ブロックエンコーディング仕様を直接得る内部合成補題。
-/
theorem uqCircuit_correct_of_selector_values
    (p : QParameters)
    (selectorValues : ∀ output input selector,
      qBeforeRowUniformInverseState p input
          (qFinalRowSelectorBasis p output selector) =
        expectedQSelectorAmplitude p output input selector) :
    IsApproxQubitBlockEncoding
      (allZeroAncilla p.ancillaWidth)
      ((uqCircuit p).toIdealOperator primitiveGateOperator)
      (embeddedProbabilityGenerator p)
      (3 * p.K)
      0 := by
  apply uqCircuit_correct_from_successBlock_eq
  rw [uqCircuit_successBlock_eq_embeddedReference_of_selector_values p selectorValues]
  exact embeddedReferenceSelectorOverlap_eq_RowSelectorPathFiniteSumSuccessBlockSpec p

/--
row oracleからcolumn oracleへ一意に逆追跡したselector振幅仕様から、最終定理を得る。
実oracle証明が最終的に適用するための最短の内部合成補題である。
-/
theorem uqCircuit_correct_of_reverse_selector_values
    (p : QParameters)
    (selectorValues : ∀ output input rowSelector,
      qBeforeRowUniformInverseState p input
          (qFinalRowSelectorBasis p output rowSelector) =
        PrefixAmplitudeReferenceCaseSpec p output input rowSelector) :
    IsApproxQubitBlockEncoding
      (allZeroAncilla p.ancillaWidth)
      ((uqCircuit p).toIdealOperator primitiveGateOperator)
      (embeddedProbabilityGenerator p)
      (3 * p.K)
      0 := by
  apply uqCircuit_correct_of_selector_values
  intro output input rowSelector
  rw [selectorValues output input rowSelector]
  exact PrefixAmplitudeReferenceCaseSpec_eq p output input rowSelector

end

end ProbabilityGeneratorQProof
