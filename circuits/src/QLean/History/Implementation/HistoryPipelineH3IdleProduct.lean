import QLean.History.Implementation.HistoryPipelineH3IdleDirty

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 7000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

theorem h3ActiveTailOperator119_decompose_idle
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    h3ActiveTailOperator119 source domain =
      h3IdlePostTransformOperator119 source domain *
        (repairedH3IdleTransform119 source domain).target *
        (repairedH3ActiveConjunction119 source domain).target := by
  unfold h3ActiveTailOperator119 h3IdlePostTransformOperator119
  simp [operatorSequence, mul_assoc]

/-- Exact two-branch action of the complete H3 tail on the final idle label. -/
theorem h3ActiveTailOperator119_apply_basisKet_idle_final
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (finalLabel : index.state.label.val + 1 =
      source.historyParameters.binaryLabels) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    let clean := h3ZeroOrder119 layout before
    let dirty := replaceQubitWire clean layout.coefficientSignal true
    applyOperator (h3ActiveTailOperator119 source domain) (basisKet before) =
      (((Real.cos ((repairedH3IdleAngle119 source).uniformValue / 2) : Real) :
          Complex) •
        basisKet (h3ActiveTailBasisAction119 source domain clean)) +
      (((Real.sin ((repairedH3IdleAngle119 source).uniformValue / 2) : Real) :
          Complex) •
        basisKet (h3ActiveTailBasisAction119 source domain dirty)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  let clean := h3ZeroOrder119 layout before
  let dirty := replaceQubitWire clean layout.coefficientSignal true
  have values := h3BeforeUniform119_idle_clean_values
    source domain fits index clockIdle
  have beforeBranch : before (historyBranchWire layout) = true := by
    simpa [before, logical, layout] using values.1
  have beforeTime : before (historyLessThanTimeWire layout) = false := by
    simpa [before, logical, layout] using values.2.1
  have beforeActive : before (historyActiveWire layout) = false := by
    simpa [before, logical, layout] using values.2.2.2.2.1
  have activeFixed : historyTaylorActiveConjunctionBasisAction layout before =
      before := by
    funext wire
    by_cases isActive : wire = historyActiveWire layout
    · subst wire
      unfold historyTaylorActiveConjunctionBasisAction
        ClassicalReversibleStage.conjunctionDirectBasisAction
        ClassicalReversibleStage.allWiresTrue
        ClassicalReversibleStage.readWires
      simp only [List.map, List.all, id_eq, Bool.and_true, xorWire,
        Function.update_self]
      rw [beforeBranch, beforeTime, beforeActive]
      rfl
    · unfold historyTaylorActiveConjunctionBasisAction
        ClassicalReversibleStage.conjunctionDirectBasisAction
      apply xorWire_apply_other
      exact isActive
  have firstActive : applyOperator
      (repairedH3ActiveConjunction119 source domain).target (basisKet before) =
      basisKet before := by
    rw [repairedH3ActiveConjunction119_apply_basisKet]
    rw [activeFixed]
  have idleAction : applyOperator
      (repairedH3IdleTransform119 source domain).target (basisKet before) =
      (((Real.cos ((repairedH3IdleAngle119 source).uniformValue / 2) : Real) :
          Complex) • basisKet clean) +
        (((Real.sin ((repairedH3IdleAngle119 source).uniformValue / 2) : Real) :
          Complex) • basisKet dirty) := by
    rw [repairedH3IdleTransform119_target]
    rw [repairedH3IdleTransformOperator119_apply_basisKet_idle
      layout (ExecutableClockEvidence119 source domain).idleTransform
      source.historyParameters.binaryLabels
      (repairedH3IdleAngle119 source).uniformValue before
      values.1 values.2.2.1 values.2.1 values.2.2.2.1
      values.2.2.2.2.1 values.2.2.2.2.2]
    have cleanEq : h3IdleTransformCleanAction119 layout
        source.historyParameters.binaryLabels before = clean :=
      h3IdleTransformCleanAction119_eq_zero source domain fits index
        clockIdle finalLabel
    have dirtyEq : h3IdleTransformDirtyAction119 layout
        source.historyParameters.binaryLabels before = dirty := by
      rw [h3IdleTransformDirtyAction119_eq_replace_clean, cleanEq]
    rw [cleanEq, dirtyEq]
  have cleanAction : applyOperator
      (h3IdlePostTransformOperator119 source domain) (basisKet clean) =
      basisKet (h3ActiveTailBasisAction119 source domain clean) :=
    h3IdlePostTransformOperator119_apply_basisKet_logical
      source domain fits index clockIdle
  have dirtyAction : applyOperator
      (h3IdlePostTransformOperator119 source domain) (basisKet dirty) =
      basisKet (h3ActiveTailBasisAction119 source domain dirty) := by
    simpa [dirty, clean, layout] using
      (h3IdlePostTransformOperator119_apply_basisKet_logical_coefficient
        source domain fits index clockIdle true)
  rw [h3ActiveTailOperator119_decompose_idle,
    applyOperator_mul, applyOperator_mul, firstActive, idleAction]
  simp_rw [applyOperator_add, applyOperator_smul]
  rw [cleanAction, dirtyAction]

theorem h3ActiveTailOperator119_idle_final_entry
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (finalLabel : index.state.label.val + 1 =
      source.historyParameters.binaryLabels) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    let clean := h3ZeroOrder119 layout before
    let row := h3ActiveTailBasisAction119 source domain clean
    h3ActiveTailOperator119 source domain row before =
      (((Real.cos ((repairedH3IdleAngle119 source).uniformValue / 2) : Real) :
        Complex)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  let clean := h3ZeroOrder119 layout before
  let dirty := replaceQubitWire clean layout.coefficientSignal true
  let row := h3ActiveTailBasisAction119 source domain clean
  have action := h3ActiveTailOperator119_apply_basisKet_idle_final
    source domain fits index clockIdle finalLabel
  have cleanCoefficient : clean layout.coefficientSignal = false := by
    let zeroIndex := h3OrderZeroIndex119 source index
    have clockIdleZero : ¬ zeroIndex.clock.val <
        source.historyParameters.physicalClocks := by
      simpa [zeroIndex] using clockIdle
    have values := h3BeforeUniform119_idle_clean_values
      source domain fits zeroIndex clockIdleZero
    have cleanEq : clean = h3BeforeUniform119 layout
        (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
          zeroIndex) :=
      h3ZeroOrder119_before_eq_orderZeroIndex source domain fits index
    rw [cleanEq]
    exact values.2.2.2.2.2
  have dirtyCoefficient : dirty layout.coefficientSignal = true := by
    simp [dirty]
  have rowCoefficient : row layout.coefficientSignal = false := by
    unfold row
    rw [h3ActiveTailBasisAction119_coefficientSignal]
    exact cleanCoefficient
  have dirtyRowCoefficient :
      h3ActiveTailBasisAction119 source domain dirty layout.coefficientSignal =
        true := by
    rw [h3ActiveTailBasisAction119_coefficientSignal]
    exact dirtyCoefficient
  have unequal : row ≠ h3ActiveTailBasisAction119 source domain dirty := by
    intro equal
    have atCoefficient := congrFun equal layout.coefficientSignal
    rw [rowCoefficient, dirtyRowCoefficient] at atCoefficient
    contradiction
  have point := congrFun action row
  dsimp only [row, clean, dirty, before, logical, layout] at unequal point ⊢
  simpa only [VerifiedCircuitCore.applyOperator_basisKet,
    Pi.add_apply, Pi.smul_apply, VerifiedCircuitCore.basisKet_apply,
    if_pos rfl, if_neg unequal, ite_true, smul_eq_mul, mul_one, mul_zero,
    add_zero] using point

theorem repairedH3RecordedTarget119_idle_final_physical_entry
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks)
    (finalLabel : index.state.label.val + 1 =
      source.historyParameters.binaryLabels) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    let clean := h3ZeroOrder119 layout before
    let row := h3ActiveTailBasisAction119 source domain clean
    repairedH3RecordedTarget119 source domain row logical =
      -(((1 / Real.sqrt
        (source.historyParameters.taylorOrder + 1) : Real) : Complex)) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  let clean := h3ZeroOrder119 layout before
  let row := h3ActiveTailBasisAction119 source domain clean
  have targetEq := repairedH3RecordedTarget119_decompose_active source domain
  have prefixAction := h3ActivePrefixOperator119_apply_basisKet
    source domain fits index
  have uniformAction := h3UniformInverse119_apply_basisKet_idle
    source domain fits index clockIdle
  have tailEntry := h3ActiveTailOperator119_idle_final_entry
    source domain fits index clockIdle finalLabel
  calc
    repairedH3RecordedTarget119 source domain row logical =
        applyOperator (repairedH3RecordedTarget119 source domain)
          (basisKet logical) row := by
      symm
      exact applyOperator_basisKet _ _ _
    _ = applyOperator
          (h3ActiveTailOperator119 source domain *
            (historyOrderUniformPreparationInverseExactComponent layout
              (ExecutableClockEvidence119 source domain).uniformExternalControl
            ).target * h3ActivePrefixOperator119 source domain)
          (basisKet logical) row := by rw [targetEq]
    _ = applyOperator (h3ActiveTailOperator119 source domain)
          (applyOperator
            (historyOrderUniformPreparationInverseExactComponent layout
              (ExecutableClockEvidence119 source domain).uniformExternalControl
            ).target
            (applyOperator (h3ActivePrefixOperator119 source domain)
              (basisKet logical))) row := by
      rw [applyOperator_mul, applyOperator_mul]
    _ = applyOperator (h3ActiveTailOperator119 source domain)
          (applyOperator
            (historyOrderUniformPreparationInverseExactComponent layout
              (ExecutableClockEvidence119 source domain).uniformExternalControl
            ).target (basisKet before)) row := by rw [prefixAction]
    _ = applyOperator (h3ActiveTailOperator119 source domain)
          (basisKet before) row := by rw [uniformAction]
    _ = h3ActiveTailOperator119 source domain row before := by
      exact applyOperator_basisKet _ _ _
    _ = (((Real.cos ((repairedH3IdleAngle119 source).uniformValue / 2) :
          Real) : Complex)) := tailEntry
    _ = -(((1 / Real.sqrt
          (source.historyParameters.taylorOrder + 1) : Real) : Complex)) := by
      have amplitude : Real.cos
          ((repairedH3IdleAngle119 source).uniformValue / 2) =
          -(Real.sqrt (source.historyParameters.taylorOrder + 1))⁻¹ := by
        simpa [cleanSignalAmplitude119] using
          (repairedH3Idle_clean_amplitude119 source)
      rw [amplitude]
      push_cast
      ring

end
end ExecutableHistoryExecutableHistory
