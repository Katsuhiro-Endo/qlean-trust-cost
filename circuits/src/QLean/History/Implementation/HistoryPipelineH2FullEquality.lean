import QLean.History.Implementation.HistoryPipelineH2TerminalEntry

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

/-- On an active input at or above the Taylor boundary, the composed
`post * Q10` word has zero entry on every clean logical row. -/
theorem h2PostQ10_active_boundary_logical_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (labelBoundary : ¬ inputIndex.state.label.val <
      source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let input := h2BeforeQ119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h2SelectedBranch119 inputIndex)
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    (h2PostOperator119 layout
        (fun coefficientIndex => correctedTaylorCoefficientAngle119
          source.toCommonSource119 coefficientIndex.val)
        compiledIdleCoefficientAngle119 *
      h2ControlledQ10CleanOperator
        (ExecutableH2Q10Specification119 source domain)) row input = 0 := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  let placement := evidence.placement.embedding.placement
  let post := h2PostOperator119 layout
    (fun coefficientIndex => correctedTaylorCoefficientAngle119
      source.toCommonSource119 coefficientIndex.val)
    compiledIdleCoefficientAngle119
  let q10 := h2ControlledQ10CleanOperator
    (ExecutableH2Q10Specification119 source domain)
  let input := h2BeforeQ119 layout
    (correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex)
  let replaced := replaceConfiguration119 source inputIndex
    outputIndex.state.configuration
  let expected := h2BeforeQ119 layout
    (correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 replaced)
  let row := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 outputIndex
  have expectedPlaced : restrictToPlacedWires placement expected =
      restrictToPlacedWires placement row := by
    calc
      restrictToPlacedWires placement expected =
          canonicalCoreSuccessBasis119 (ExecutableQParameters119 source domain)
            (executableQConfiguration119 source domain
              outputIndex.state.configuration) := by
        exact h2BeforeQ119_q10RestrictedBasis_eq_success119 source domain fits
          h2SelectedBranch119 replaced
      _ = restrictToPlacedWires placement
          (h2BeforeQ119 layout row) := by
        symm
        exact h2BeforeQ119_q10RestrictedBasis_eq_success119 source domain fits
          h2SelectedBranch119 outputIndex
      _ = restrictToPlacedWires placement row :=
        h2BeforeQ119_restrict_q10_eq_input119 source domain fits
          h2SelectedBranch119 outputIndex
  have expectedOutside : restrictToOutsideWires placement expected =
      restrictToOutsideWires placement input := by
    exact h2BeforeQ119_replaceConfiguration_outside source domain fits
      h2SelectedBranch119 inputIndex outputIndex.state.configuration
  rw [two_stage_product_entry_eq_canonical_middle119 placement
    (h2PostWriteSupport119 layout) post q10
    (h2PostOperator_local119 layout
      (fun coefficientIndex => correctedTaylorCoefficientAngle119
        source.toCommonSource119 coefficientIndex.val)
      compiledIdleCoefficientAngle119)
    (h2PostWriteSupport119_ne_placement widths)
    (executableH2Q10_operator_local119 source domain)
    row input expected expectedPlaced expectedOutside]
  have replacedActive : replaced.clock.val <
      source.historyParameters.physicalClocks := by
    simpa [replaced] using clockActive
  have replacedBoundary : ¬ replaced.state.label.val <
      source.historyParameters.taylorOrder := by
    simpa [replaced] using labelBoundary
  dsimp only [post, row, expected, replaced, input]
  rw [h2PostOperator_active_boundary_logical_entry119 source domain fits
    (replaceConfiguration119 source inputIndex outputIndex.state.configuration)
    outputIndex replacedActive replacedBoundary]
  simp

/-- Every clean logical entry of the actual H2 target vanishes on an active
input at or above the Taylor boundary. -/
theorem executableH2_active_boundary_logical_clean_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (labelBoundary : ¬ inputIndex.state.label.val <
      source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        row input = 0 := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let clean := ScientificWidthGenericContract.correctedCleanEvidence259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let angles : Fin
      (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic).taylorOrder →
        VerifiedCircuitCore.AngleExpr :=
    fun coefficientIndex => correctedTaylorCoefficientAngle119
      source.toCommonSource119 coefficientIndex.val
  let pre := operatorSequence
    [historyTaylorSelectorEqualityOperator layout,
     historyTaylorTimeComparisonOperator layout,
     historyTaylorIdleEndComparisonOperator layout,
     historyTaylorActiveConjunctionOperator layout]
  let q10 := h2ControlledQ10CleanOperator
    (historyP15ControlledQ10UnderstandingSpecification
      (ExecutableH2Q10Specification119 source domain).p layout widths)
  let post := h2PostOperator119 layout angles compiledIdleCoefficientAngle119
  let input := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 inputIndex
  let row := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 outputIndex
  have operatorEq :
      h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout clean widths
            angles compiledIdleCoefficientAngle119) =
        post * (q10 * pre) :=
    h2TaylorCleanOperator_historyP15_decompose119 layout clean widths
      angles compiledIdleCoefficientAngle119
  calc
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout clean widths angles
          compiledIdleCoefficientAngle119) row input =
      VerifiedCircuitCore.applyOperator
        (h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout clean widths
            angles compiledIdleCoefficientAngle119))
        (VerifiedCircuitCore.basisKet input) row := by
          symm
          exact VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = VerifiedCircuitCore.applyOperator (post * (q10 * pre))
        (VerifiedCircuitCore.basisKet input) row := by rw [operatorEq]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator q10
          (VerifiedCircuitCore.applyOperator pre
            (VerifiedCircuitCore.basisKet input))) row := by
      rw [VerifiedCircuitCore.applyOperator_mul,
        VerifiedCircuitCore.applyOperator_mul]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator q10
          (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input))) row := by
      rw [h2BeforeOperators_apply_basisKet119]
    _ = VerifiedCircuitCore.applyOperator (post * q10)
        (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input)) row := by
      rw [VerifiedCircuitCore.applyOperator_mul]
    _ = (post * q10) row (h2BeforeQ119 layout input) :=
      VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = 0 := h2PostQ10_active_boundary_logical_entry119 source domain fits
      inputIndex outputIndex clockActive labelBoundary

/-- Every clean logical entry of the actual H2 target vanishes on the terminal
idle label. -/
theorem executableH2_idle_terminal_logical_clean_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (terminal : ¬ inputIndex.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        row input = 0 := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let clean := ScientificWidthGenericContract.correctedCleanEvidence259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let angles : Fin
      (HistoryRawSchema.parameters203 (ExecutableRaw119 source).history
        (ExecutableAdmissible119 source domain).analytic).taylorOrder →
        VerifiedCircuitCore.AngleExpr :=
    fun coefficientIndex => correctedTaylorCoefficientAngle119
      source.toCommonSource119 coefficientIndex.val
  let pre := operatorSequence
    [historyTaylorSelectorEqualityOperator layout,
     historyTaylorTimeComparisonOperator layout,
     historyTaylorIdleEndComparisonOperator layout,
     historyTaylorActiveConjunctionOperator layout]
  let q10 := h2ControlledQ10CleanOperator
    (historyP15ControlledQ10UnderstandingSpecification
      (ExecutableH2Q10Specification119 source domain).p layout widths)
  let post := h2PostOperator119 layout angles compiledIdleCoefficientAngle119
  let input := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 inputIndex
  let row := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 outputIndex
  have operatorEq :
      h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout clean widths
            angles compiledIdleCoefficientAngle119) =
        post * (q10 * pre) :=
    h2TaylorCleanOperator_historyP15_decompose119 layout clean widths
      angles compiledIdleCoefficientAngle119
  have activeFalse :
      (h2BeforeQ119 layout input) (historyActiveWire layout) = false :=
    h2BeforeQ119_active_false_of_idle_clock119 source domain fits inputIndex
      clockIdle
  have q10Fixed : VerifiedCircuitCore.applyOperator q10
      (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input)) =
        VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input) := by
    exact executableH2Q10_apply_basisKet_of_active_false119 source domain
      (h2BeforeQ119 layout input) activeFalse
  calc
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout clean widths angles
          compiledIdleCoefficientAngle119) row input =
      VerifiedCircuitCore.applyOperator
        (h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout clean widths
            angles compiledIdleCoefficientAngle119))
        (VerifiedCircuitCore.basisKet input) row := by
          symm
          exact VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = VerifiedCircuitCore.applyOperator (post * (q10 * pre))
        (VerifiedCircuitCore.basisKet input) row := by rw [operatorEq]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator q10
          (VerifiedCircuitCore.applyOperator pre
            (VerifiedCircuitCore.basisKet input))) row := by
      rw [VerifiedCircuitCore.applyOperator_mul,
        VerifiedCircuitCore.applyOperator_mul]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator q10
          (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input))) row := by
      rw [h2BeforeOperators_apply_basisKet119]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input)) row := by
      rw [q10Fixed]
    _ = post row (h2BeforeQ119 layout input) :=
      VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = 0 := h2PostOperator_idle_terminal_logical_entry119 source domain fits
      inputIndex outputIndex clockIdle terminal

/-- The mathematical `L1` target is zero on active columns at or above the
Taylor boundary. -/
theorem h2L1_active_boundary_zero119
    (source : AlignedCommonSource119)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (labelBoundary : ¬ inputIndex.state.label.val <
      source.historyParameters.taylorOrder) :
    HistoryBlockEncoding.HistorySpec.L1 source.historyParameters
        (commonModelQ119 source.toCommonSource119) outputIndex inputIndex = 0 := by
  unfold HistoryBlockEncoding.HistorySpec.L1
  by_cases clockEq : outputIndex.clock = inputIndex.clock
  · rw [if_pos clockEq]
    have outputActive : outputIndex.clock.val <
        source.historyParameters.physicalClocks := by
      simpa [clockEq] using clockActive
    rw [if_pos outputActive]
    unfold HistoryBlockEncoding.HistorySpec.deltaTay
    rw [if_neg (by
      intro transition
      exact labelBoundary transition.2)]
  · rw [if_neg clockEq]

/-- The mathematical `L1` target is zero on the terminal idle label. -/
theorem h2L1_idle_terminal_zero119
    (source : AlignedCommonSource119)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (terminal : ¬ inputIndex.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    HistoryBlockEncoding.HistorySpec.L1 source.historyParameters
        (commonModelQ119 source.toCommonSource119) outputIndex inputIndex = 0 := by
  unfold HistoryBlockEncoding.HistorySpec.L1
  by_cases clockEq : outputIndex.clock = inputIndex.clock
  · rw [if_pos clockEq]
    have outputIdle : ¬ outputIndex.clock.val <
        source.historyParameters.physicalClocks := by
      simpa [clockEq] using clockIdle
    rw [if_neg outputIdle]
    unfold HistoryBlockEncoding.HistorySpec.deltaIdle
    rw [if_neg (by
      intro transition
      have inputNextLe : inputIndex.state.label.val + 1 ≤
          source.historyParameters.binaryLabels := by
        exact Nat.succ_le_of_lt inputIndex.state.label.isLt
      have terminalEq : inputIndex.state.label.val + 1 =
          source.historyParameters.binaryLabels := by
        omega
      have outputLt := outputIndex.state.label.isLt
      omega)]
  · rw [if_neg clockEq]

/-- Equality of the actual H2 clean logical block with `L1` on active boundary
columns. -/
theorem executableH2_active_boundary_entry_eq_L1_119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (labelBoundary : ¬ inputIndex.state.label.val <
      source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        row input =
      (HistoryBlockEncoding.HistorySpec.L1 source.historyParameters
        (commonModelQ119 source.toCommonSource119) outputIndex inputIndex :
          Complex) := by
  dsimp only
  rw [executableH2_active_boundary_logical_clean_entry119 source domain fits
    inputIndex outputIndex clockActive labelBoundary]
  rw [h2L1_active_boundary_zero119 source inputIndex outputIndex clockActive
    labelBoundary]
  norm_num

/-- Equality of the actual H2 clean logical block with `L1` on terminal idle
columns. -/
theorem executableH2_idle_terminal_entry_eq_L1_119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (terminal : ¬ inputIndex.state.label.val + 1 <
      source.historyParameters.binaryLabels) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        row input =
      (HistoryBlockEncoding.HistorySpec.L1 source.historyParameters
        (commonModelQ119 source.toCommonSource119) outputIndex inputIndex :
          Complex) := by
  dsimp only
  rw [executableH2_idle_terminal_logical_clean_entry119 source domain fits
    inputIndex outputIndex clockIdle terminal]
  rw [h2L1_idle_terminal_zero119 source inputIndex outputIndex clockIdle terminal]
  norm_num

/-- Exhaustive H2 result: the actual compiled clean logical block equals the
mathematical history layer `L1` for every logical row and column. -/
theorem executableH2_all_logical_entry_eq_L1_119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 inputIndex
    let row := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        row input =
      (HistoryBlockEncoding.HistorySpec.L1 source.historyParameters
        (commonModelQ119 source.toCommonSource119) outputIndex inputIndex :
          Complex) := by
  by_cases clockActive : inputIndex.clock.val <
      source.historyParameters.physicalClocks
  · by_cases labelTaylor : inputIndex.state.label.val <
        source.historyParameters.taylorOrder
    · exact executableH2_active_logical_entry_eq_L1_119 source domain fits
        inputIndex outputIndex clockActive labelTaylor
    · exact executableH2_active_boundary_entry_eq_L1_119 source domain fits
        inputIndex outputIndex clockActive labelTaylor
  · by_cases nextFits : inputIndex.state.label.val + 1 <
        source.historyParameters.binaryLabels
    · exact executableH2_idle_nonterminal_entry_eq_L1_119 source domain fits
        inputIndex outputIndex clockActive nextFits
    · exact executableH2_idle_terminal_entry_eq_L1_119 source domain fits
        inputIndex outputIndex clockActive nextFits

end
end ExecutableHistoryExecutableHistory
