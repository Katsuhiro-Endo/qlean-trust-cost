import QLean.History.Implementation.HistoryPipelineH2ActivePostAction
import QLean.History.Implementation.HistoryPipelineH2ProductSupport

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

theorem operatorSequence_singleton119
    {M : Type*} [Monoid M] (operator : M) :
    VerifiedCircuitCore.operatorSequence [operator] = operator := by
  simp [VerifiedCircuitCore.operatorSequence]

theorem h2PostOperator_active_taylor_clean_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (configuration : QConfiguration source.qParameters)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (labelTaylor : index.state.label.val < source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let logicalInput := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119
      (replaceConfiguration119 source index configuration)
    let logicalOutput := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119
      (raiseHistoryLabel119 source index configuration labelTaylor)
    h2PostOperator119 layout
        (fun coefficientIndex => correctedTaylorCoefficientAngle119
          source.toCommonSource119 coefficientIndex.val)
        compiledIdleCoefficientAngle119
        logicalOutput (h2BeforeQ119 layout logicalInput) =
      (((-(omegaH119 source.toCommonSource119) /
          ((index.state.label.val + 1 : Nat) : Real)) : Real) : Complex) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let oldIndex := replaceConfiguration119 source index configuration
  let newIndex := raiseHistoryLabel119 source index configuration labelTaylor
  let logicalInput := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 oldIndex
  let logicalOutput := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119 newIndex
  have action := applyOperator_h2PostOperator_active_taylor119 source domain
    fits index configuration clockActive labelTaylor
  have rowSignalFalse : logicalOutput layout.coefficientSignal = false := by
    exact correctedBranchHistoryBasis119_coefficientSignal_false119 source
      domain fits h2SelectedBranch119 newIndex
  have rowNeDirty : logicalOutput ≠
      replaceQubitWire logicalOutput layout.coefficientSignal true := by
    intro equal
    have atSignal := congrFun equal layout.coefficientSignal
    simp [replaceQubitWire, rowSignalFalse] at atSignal
  dsimp only [logicalOutput, newIndex, layout] at rowNeDirty
  calc
    h2PostOperator119 layout
        (fun coefficientIndex => correctedTaylorCoefficientAngle119
          source.toCommonSource119 coefficientIndex.val)
        compiledIdleCoefficientAngle119
        logicalOutput (h2BeforeQ119 layout logicalInput) =
      VerifiedCircuitCore.applyOperator
        (h2PostOperator119 layout
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout logicalInput))
        logicalOutput := by
          symm
          exact VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = ((Real.cos
          ((correctedTaylorCoefficientAngle119 source.toCommonSource119
            index.state.label.val).uniformValue / 2) : Real) : Complex) := by
      rw [action]
      simp [VerifiedCircuitCore.basisKet, logicalOutput, newIndex, rowNeDirty]
    _ = (((-(omegaH119 source.toCommonSource119) /
          ((index.state.label.val + 1 : Nat) : Real)) : Real) : Complex) := by
      congr 1
      simpa [cleanSignalAmplitude119] using
        correctedTaylorCoefficient_clean_amplitude119
          source.toCommonSource119 index.state.label.val

theorem h2PostQ10_active_taylor_clean_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (outputConfiguration : QConfiguration source.qParameters)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (labelTaylor : index.state.label.val < source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let input := h2BeforeQ119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h2SelectedBranch119 index)
    let output := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119
      (raiseHistoryLabel119 source index outputConfiguration labelTaylor)
    (h2PostOperator119 layout
        (fun coefficientIndex => correctedTaylorCoefficientAngle119
          source.toCommonSource119 coefficientIndex.val)
        compiledIdleCoefficientAngle119 *
      h2ControlledQ10CleanOperator
        (ExecutableH2Q10Specification119 source domain)) output input =
      (((-(omegaH119 source.toCommonSource119) /
          ((index.state.label.val + 1 : Nat) : Real)) : Real) : Complex) *
        ((HistoryBlockEncoding.QModel.configurationQMatrix
            (executableQConfiguration119 source domain outputConfiguration)
            (executableQConfiguration119 source domain
              index.state.configuration) : Complex) /
          ((3 * (ExecutableH2Q10Specification119 source domain).p.K : Nat) :
            Complex)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let placement := (historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths).placement.embedding.placement
  let post := h2PostOperator119 layout
    (fun coefficientIndex => correctedTaylorCoefficientAngle119
      source.toCommonSource119 coefficientIndex.val)
    compiledIdleCoefficientAngle119
  let q10 := h2ControlledQ10CleanOperator
    (ExecutableH2Q10Specification119 source domain)
  let input := h2BeforeQ119 layout
    (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119 index)
  let expected := h2BeforeQ119 layout
    (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
      (replaceConfiguration119 source index outputConfiguration))
  let output := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119
    (raiseHistoryLabel119 source index outputConfiguration labelTaylor)
  have postEntry : post output expected =
      (((-(omegaH119 source.toCommonSource119) /
          ((index.state.label.val + 1 : Nat) : Real)) : Real) : Complex) := by
    exact h2PostOperator_active_taylor_clean_entry119 source domain fits index
      outputConfiguration clockActive labelTaylor
  have postExpectedNonzero : post output expected ≠ 0 := by
    rw [postEntry]
    exact_mod_cast div_ne_zero
      (neg_ne_zero.mpr (ne_of_gt
        (omegaH119_positive source.toCommonSource119))) (by positivity)
  have q10Entry : q10 expected input =
      (HistoryBlockEncoding.QModel.configurationQMatrix
          (executableQConfiguration119 source domain outputConfiguration)
          (executableQConfiguration119 source domain
            index.state.configuration) : Complex) /
        ((3 * (ExecutableH2Q10Specification119 source domain).p.K : Nat) :
          Complex) := by
    exact executableH2Q10_selected_logical_entry119 source domain fits index
      clockActive outputConfiguration
  have expectedOutside : restrictToOutsideWires placement expected =
      restrictToOutsideWires placement input := by
    exact h2BeforeQ119_replaceConfiguration_outside source domain fits
      h2SelectedBranch119 index outputConfiguration
  rw [Matrix.mul_apply]
  change (∑ middle, post output middle * q10 middle input) = _
  rw [Fintype.sum_eq_single expected]
  · rw [postEntry, q10Entry]
  · intro middle middleNe
    by_cases postZero : post output middle = 0
    · change post output middle * q10 middle input = 0
      rw [postZero]
      simp
    by_cases q10Zero : q10 middle input = 0
    · change post output middle * q10 middle input = 0
      rw [q10Zero]
      simp
    have middleEq : middle = expected :=
      intermediate_unique_of_two_stage_locality119 placement
        (h2PostWriteSupport119 layout) post q10
        (h2PostOperator_local119 layout
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        (h2PostWriteSupport119_ne_placement widths)
        (executableH2Q10_operator_local119 source domain)
        output input expected middle expectedOutside postExpectedNonzero
        postZero q10Zero
    exact (middleNe middleEq).elim

theorem h2TaylorCleanOperator_historyP15_decompose119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryP15PostQ10Evidence layout)
    (widths : p.ProbabilityGeneratorCanonicalPlacementWidths
      generatorSignalWidth generatorWorkWidth dataWidth)
    (angles : Fin parameters.taylorOrder → VerifiedCircuitCore.AngleExpr)
    (idleAngle : VerifiedCircuitCore.AngleExpr) :
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout evidence widths
          angles idleAngle) =
      h2PostOperator119 layout angles idleAngle *
        (h2ControlledQ10CleanOperator
          (historyP15ControlledQ10UnderstandingSpecification p layout widths) *
        operatorSequence
          [historyTaylorSelectorEqualityOperator layout,
           historyTaylorTimeComparisonOperator layout,
           historyTaylorIdleEndComparisonOperator layout,
           historyTaylorActiveConjunctionOperator layout]) := by
  unfold h2TaylorCleanOperator
  rw [h2TaylorCleanSourceOperators_historyP15_eq]
  change operatorSequence
    (([historyTaylorSelectorEqualityOperator layout,
       historyTaylorTimeComparisonOperator layout,
       historyTaylorIdleEndComparisonOperator layout,
       historyTaylorActiveConjunctionOperator layout] ++
      [h2ControlledQ10CleanOperator
        (historyP15ControlledQ10UnderstandingSpecification p layout widths)]) ++
     [historyTaylorActiveConjunctionOperator layout,
      historyTaylorInvalidClockOperator layout,
      historyTaylorOrderBoundaryOperator layout,
      historyTaylorIdleBoundaryOperator layout,
      historyTaylorDegreeIncrementOperator layout,
      historyTaylorCoefficientLoopOperator layout angles,
      historyTaylorIdleCoefficientOperator layout idleAngle,
      operatorSequence
        [historyTaylorIdleEndComparisonOperator layout,
         historyTaylorTimeComparisonOperator layout,
         historyTaylorSelectorEqualityOperator layout]]) = _
  rw [operatorSequence_append, operatorSequence_append,
    operatorSequence_singleton119]
  rfl

theorem executableH2_active_taylor_clean_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (outputConfiguration : QConfiguration source.qParameters)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (labelTaylor : index.state.label.val < source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 index
    let output := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119
      (raiseHistoryLabel119 source index outputConfiguration labelTaylor)
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        output input =
      (((-(omegaH119 source.toCommonSource119) /
          ((index.state.label.val + 1 : Nat) : Real)) : Real) : Complex) *
        ((HistoryBlockEncoding.QModel.configurationQMatrix
            (executableQConfiguration119 source domain outputConfiguration)
            (executableQConfiguration119 source domain
              index.state.configuration) : Complex) /
          ((3 * (ExecutableH2Q10Specification119 source domain).p.K : Nat) :
            Complex)) := by
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
    h2SelectedBranch119 index
  let output := correctedBranchHistoryBasis119 source domain fits
    h2SelectedBranch119
    (raiseHistoryLabel119 source index outputConfiguration labelTaylor)
  have operatorEq :
      h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout clean widths
            angles compiledIdleCoefficientAngle119) =
        post * (q10 * pre) := by
    exact h2TaylorCleanOperator_historyP15_decompose119 layout clean widths
      angles compiledIdleCoefficientAngle119
  calc
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout clean widths angles
          compiledIdleCoefficientAngle119) output input =
      VerifiedCircuitCore.applyOperator
        (h2TaylorCleanOperator
          (historyP15H2CleanUnderstandingSpecification layout clean widths
            angles compiledIdleCoefficientAngle119))
        (VerifiedCircuitCore.basisKet input) output := by
          symm
          exact VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = VerifiedCircuitCore.applyOperator (post * (q10 * pre))
        (VerifiedCircuitCore.basisKet input) output := by rw [operatorEq]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator (q10 * pre)
          (VerifiedCircuitCore.basisKet input)) output := by
      rw [VerifiedCircuitCore.applyOperator_mul]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator q10
          (VerifiedCircuitCore.applyOperator pre
            (VerifiedCircuitCore.basisKet input))) output := by
      rw [VerifiedCircuitCore.applyOperator_mul]
    _ = VerifiedCircuitCore.applyOperator post
        (VerifiedCircuitCore.applyOperator q10
          (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input))) output := by
      rw [h2BeforeOperators_apply_basisKet119]
    _ = VerifiedCircuitCore.applyOperator (post * q10)
        (VerifiedCircuitCore.basisKet (h2BeforeQ119 layout input)) output := by
      rw [VerifiedCircuitCore.applyOperator_mul]
    _ = (post * q10) output (h2BeforeQ119 layout input) := by
      exact VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = (((-(omegaH119 source.toCommonSource119) /
          ((index.state.label.val + 1 : Nat) : Real)) : Real) : Complex) *
        ((HistoryBlockEncoding.QModel.configurationQMatrix
            (executableQConfiguration119 source domain outputConfiguration)
            (executableQConfiguration119 source domain
              index.state.configuration) : Complex) /
          ((3 * (ExecutableH2Q10Specification119 source domain).p.K : Nat) :
            Complex)) := by
      exact h2PostQ10_active_taylor_clean_entry119 source domain fits index
        outputConfiguration clockActive labelTaylor

theorem executableH2_active_taylor_entry_eq_L1_119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (outputConfiguration : QConfiguration source.qParameters)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (labelTaylor : index.state.label.val < source.historyParameters.taylorOrder) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 index
    let outputIndex :=
      raiseHistoryLabel119 source index outputConfiguration labelTaylor
    let output := correctedBranchHistoryBasis119 source domain fits
      h2SelectedBranch119 outputIndex
    h2TaylorCleanOperator
        (historyP15H2CleanUnderstandingSpecification layout
          (ScientificWidthGenericContract.correctedCleanEvidence259
            (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
          (ExecutableAdmissible119 source domain).placementWidths
          (fun coefficientIndex => correctedTaylorCoefficientAngle119
            source.toCommonSource119 coefficientIndex.val)
          compiledIdleCoefficientAngle119)
        output input =
      (HistoryBlockEncoding.HistorySpec.L1 source.historyParameters
        (commonModelQ119 source.toCommonSource119) outputIndex index : Complex) := by
  dsimp only
  have parameterEq := executableQParameters_eq119 source domain
  have kEq : (ExecutableH2Q10Specification119 source domain).p.K =
      source.qParameters.K := by
    exact congrArg (fun p : QParameters => p.K) parameterEq
  have qEntryEq :
      (HistoryBlockEncoding.QModel.configurationQMatrix
          (executableQConfiguration119 source domain outputConfiguration)
          (executableQConfiguration119 source domain
            index.state.configuration) : Complex) =
        (HistoryBlockEncoding.QModel.configurationQMatrix outputConfiguration
          index.state.configuration : Complex) := by
    cases parameterEq
    rfl
  rw [executableH2_active_taylor_clean_entry119 source domain fits index
    outputConfiguration clockActive labelTaylor]
  rw [kEq, qEntryEq]
  simp [HistoryBlockEncoding.HistorySpec.L1, HistoryBlockEncoding.HistorySpec.deltaTay,
    commonModelQ119, omegaH119, generatorAlpha119, raiseHistoryLabel119,
    clockActive, labelTaylor]
  have kNe : ((source.qParameters.K : Nat) : Complex) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt source.qParameters.K_pos)
  field_simp [kNe]

end
end ExecutableHistoryExecutableHistory
