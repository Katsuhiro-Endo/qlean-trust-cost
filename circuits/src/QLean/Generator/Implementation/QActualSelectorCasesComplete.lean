import QLean.Generator.Implementation.QActualPhysicalEventAcceptedCorrectness
import QLean.Generator.Implementation.QActualDiagonalAcceptedCorrectness
import QLean.Generator.Implementation.QActualRejectedPathCorrectness

/-!
# selector一本ごとのactual振幅と解析期待値の完全一致

illegal input、row reject、column reject、不整合、受理の全場合を統合する。block encodingや
component rootは参照せず、最上位有限和合成から再利用できる下位契約として公開する。
-/

namespace ProbabilityGeneratorQProof

noncomputable section

/-- 非合法な評価入力では、どの合法出力とrow selectorに対してもactual振幅は0である。 -/
theorem qActualSelectorAmplitude_eq_zero_of_illegal_input_final
    (p : QParameters) (output : QConfiguration p)
    (input : RegisterBasis p.systemWidth) (rowSelector : QSelector p)
    (illegal : decodeDelimiter input = none) :
    qActualSelectorAmplitude p (delimiterEncoding output) input rowSelector = 0 := by
  cases rowAccepted : rowReference output rowSelector with
  | none =>
      exact qActualSelectorAmplitude_eq_zero_of_rowReference_none p output input
        rowSelector rowAccepted
  | some rowResult =>
      apply qActualSelectorAmplitude_eq_zero_of_illegal_input_of_canonical_preimage
        p (delimiterEncoding output) input rowSelector rowResult.input
          rowResult.columnSelector
      · exact qActualColumnPreparedPreimage_of_rowReference_some output
          rowSelector rowResult rowAccepted
      · exact illegal

/-- row参照のpredecessorと異なる評価入力では、column拒否経路のactual振幅は0である。 -/
theorem qActualSelectorAmplitude_eq_zero_of_columnReference_none_final
    (p : QParameters) (output input : QConfiguration p)
    (rowSelector : QSelector p) (rowResult : RowReferenceResult p)
    (rowAccepted : rowReference output rowSelector = some rowResult)
    (columnRejected : columnReference input rowResult.columnSelector = none) :
    qActualSelectorAmplitude p (delimiterEncoding output)
        (delimiterEncoding input) rowSelector = 0 := by
  by_cases inputEqual : rowResult.input = input
  · obtain ⟨inverseResult, inverseAccepted, _, _⟩ :=
      rowReference_some_has_inverse output rowSelector rowResult rowAccepted
    rw [inputEqual, columnRejected] at inverseAccepted
    contradiction
  · exact qActualSelectorAmplitude_eq_zero_of_configuration_ne_of_canonical_preimage
      p (delimiterEncoding output) input rowResult.input rowSelector
        rowResult.columnSelector
        (qActualColumnPreparedPreimage_of_rowReference_some output
          rowSelector rowResult rowAccepted) inputEqual

/-- rowとcolumnの参照結果が最終入出力へ着地しない経路では、actual振幅は0である。 -/
theorem qActualSelectorAmplitude_eq_zero_of_inconsistent_final
    (p : QParameters) (output input : QConfiguration p)
    (rowSelector : QSelector p) (rowResult : RowReferenceResult p)
    (columnResult : ColumnReferenceResult p)
    (rowAccepted : rowReference output rowSelector = some rowResult)
    (columnAccepted : columnReference input rowResult.columnSelector =
      some columnResult)
    (inconsistent : ¬(columnResult.rowSelector = rowSelector ∧
      columnResult.output = output ∧ rowResult.input = input)) :
    qActualSelectorAmplitude p (delimiterEncoding output)
        (delimiterEncoding input) rowSelector = 0 := by
  by_cases inputEqual : rowResult.input = input
  · obtain ⟨inverseResult, inverseAccepted, inverseOutput, inverseSelector⟩ :=
      rowReference_some_has_inverse output rowSelector rowResult rowAccepted
    rw [inputEqual] at inverseAccepted
    have resultEqual : columnResult = inverseResult :=
      Option.some.inj (columnAccepted.symm.trans inverseAccepted)
    exfalso
    apply inconsistent
    exact ⟨resultEqual ▸ inverseSelector, resultEqual ▸ inverseOutput, inputEqual⟩
  · exact qActualSelectorAmplitude_eq_zero_of_configuration_ne_of_canonical_preimage
      p (delimiterEncoding output) input rowResult.input rowSelector
        rowResult.columnSelector
        (qActualColumnPreparedPreimage_of_rowReference_some output
          rowSelector rowResult rowAccepted) inputEqual

/-- 任意の物理system入出力とrow selectorで、actual振幅は参照関数の期待振幅に一致する。 -/
theorem qActualSelectorAmplitude_eq_expected (p : QParameters) :
    ∀ output input rowSelector,
      qActualSelectorAmplitude p output input rowSelector =
        PrefixAmplitudeReferenceCaseSpec p output input rowSelector := by
  apply qActualSelectorAmplitude_eq_expected_of_reference_cases p
  · intro output input rowSelector illegal
    exact qActualSelectorAmplitude_eq_zero_of_illegal_output p output input
      rowSelector illegal
  · intro output input rowSelector illegal
    exact qActualSelectorAmplitude_eq_zero_of_illegal_input_final p output input
      rowSelector illegal
  · intro output input rowSelector rowRejected
    exact qActualSelectorAmplitude_eq_zero_of_rowReference_none p output
      (delimiterEncoding input) rowSelector rowRejected
  · intro output input rowSelector rowResult rowAccepted columnRejected
    exact qActualSelectorAmplitude_eq_zero_of_columnReference_none_final p output
      input rowSelector rowResult rowAccepted columnRejected
  · intro output input rowSelector rowResult columnResult rowAccepted
      columnAccepted inconsistent
    exact qActualSelectorAmplitude_eq_zero_of_inconsistent_final p output input
      rowSelector rowResult columnResult rowAccepted columnAccepted inconsistent
  · intro output input rowSelector rowResult columnResult rowAccepted
      columnAccepted rowSelectorEqual outputEqual inputEqual
    subst input
    exact qActualSelectorAmplitude_of_reference_some output rowSelector rowResult
      columnResult rowAccepted columnAccepted

end

end ProbabilityGeneratorQProof
