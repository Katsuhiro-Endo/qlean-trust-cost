import QLean.History.Implementation.HistoryPipelineH3LogicalConstruction

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

/-- The full repaired H3 column on a final idle label contains exactly a
clean logical candidate and a coefficient-signal dirty candidate. -/
theorem repairedH3RecordedTarget119_apply_basisKet_idle_final
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
    applyOperator (repairedH3RecordedTarget119 source domain)
        (basisKet logical) =
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
  have targetEq := repairedH3RecordedTarget119_decompose_active source domain
  have prefixAction := h3ActivePrefixOperator119_apply_basisKet
    source domain fits index
  have uniformAction := h3UniformInverse119_apply_basisKet_idle
    source domain fits index clockIdle
  have tailAction := h3ActiveTailOperator119_apply_basisKet_idle_final
    source domain fits index clockIdle finalLabel
  rw [targetEq, applyOperator_mul, applyOperator_mul, prefixAction, uniformAction]
  exact tailAction

theorem repairedH3RecordedTarget119_idle_final_clean_logical_entry
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks)
    (finalLabel : inputIndex.state.label.val + 1 =
      source.historyParameters.binaryLabels) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 inputIndex
    let row := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 outputIndex
    let before := h3BeforeUniform119 layout input
    let clean := h3ZeroOrder119 layout before
    let cleanOutput := h3ActiveTailBasisAction119 source domain clean
    repairedH3RecordedTarget119 source domain row input =
      if row = cleanOutput then
        (((Real.cos ((repairedH3IdleAngle119 source).uniformValue / 2) : Real) :
          Complex))
      else 0 := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let input := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 inputIndex
  let row := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 outputIndex
  let before := h3BeforeUniform119 layout input
  let clean := h3ZeroOrder119 layout before
  let dirty := replaceQubitWire clean layout.coefficientSignal true
  let cleanOutput := h3ActiveTailBasisAction119 source domain clean
  let dirtyOutput := h3ActiveTailBasisAction119 source domain dirty
  have action := repairedH3RecordedTarget119_apply_basisKet_idle_final
    source domain fits inputIndex clockIdle finalLabel
  have rowCoefficient : row layout.coefficientSignal = false :=
    correctedBranchHistoryBasis119_coefficientSignal_false119
      source domain fits h3SelectedBranch119 outputIndex
  have dirtyCoefficient : dirty layout.coefficientSignal = true := by
    simp [dirty]
  have dirtyOutputCoefficient : dirtyOutput layout.coefficientSignal = true := by
    unfold dirtyOutput
    rw [h3ActiveTailBasisAction119_coefficientSignal]
    exact dirtyCoefficient
  have rowNeDirty : row ≠ dirtyOutput := by
    intro equal
    have atCoefficient := congrFun equal layout.coefficientSignal
    rw [rowCoefficient, dirtyOutputCoefficient] at atCoefficient
    contradiction
  have point := congrFun action row
  have entryPoint : repairedH3RecordedTarget119 source domain row input =
      (((Real.cos ((repairedH3IdleAngle119 source).uniformValue / 2) : Real) :
          Complex) * basisKet cleanOutput row) +
        (((Real.sin ((repairedH3IdleAngle119 source).uniformValue / 2) : Real) :
          Complex) * basisKet dirtyOutput row) := by
    simpa [applyOperator_basisKet, Pi.smul_apply, smul_eq_mul,
      cleanOutput, dirtyOutput, clean, dirty, before, input, layout] using point
  rw [entryPoint]
  by_cases rowEq : row = cleanOutput
  · rw [if_pos rowEq]
    have cleanKet : basisKet cleanOutput row = 1 := by
      simp [basisKet, rowEq]
    have dirtyKet : basisKet dirtyOutput row = 0 := by
      simp [basisKet, rowNeDirty]
    rw [cleanKet, dirtyKet]
    ring
  · rw [if_neg rowEq]
    have cleanKet : basisKet cleanOutput row = 0 := by
      simp [basisKet, rowEq]
    have dirtyKet : basisKet dirtyOutput row = 0 := by
      simp [basisKet, rowNeDirty]
    rw [cleanKet, dirtyKet]
    ring

end
end ExecutableHistoryExecutableHistory
