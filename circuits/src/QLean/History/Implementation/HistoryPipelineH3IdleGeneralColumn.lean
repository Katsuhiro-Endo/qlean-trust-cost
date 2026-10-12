import QLean.History.Implementation.HistoryPipelineH3IdleGeneralSuffix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
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

/-- Exact two-branch action of the complete H3 tail on every idle logical
label.  No final-label assumption is used. -/
theorem h3ActiveTailOperator119_apply_basisKet_idle_general
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    let clean := h3IdleTransformCleanAction119 layout
      source.historyParameters.binaryLabels before
    let dirty := h3IdleTransformDirtyAction119 layout
      source.historyParameters.binaryLabels before
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
  let expected := h3ZeroOrder119 layout before
  let clean := h3IdleTransformCleanAction119 layout
    source.historyParameters.binaryLabels before
  let dirty := h3IdleTransformDirtyAction119 layout
    source.historyParameters.binaryLabels before
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
    exact repairedH3IdleTransformOperator119_apply_basisKet_idle
      layout (ExecutableClockEvidence119 source domain).idleTransform
      source.historyParameters.binaryLabels
      (repairedH3IdleAngle119 source).uniformValue before
      values.1 values.2.2.1 values.2.1 values.2.2.2.1
      values.2.2.2.2.1 values.2.2.2.2.2
  have expectedWorkspace
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace) :
      expected wire = before wire := by
    unfold expected h3ZeroOrder119
    rw [writeRegisterValue_apply_outside]
    intro orderIndex equal
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨workspaceIndex, rfl⟩
    exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex equal
  have cleanWorkspace
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace) :
      clean wire = expected wire := by
    have cleanBefore := h3IdleTransformCleanAction119_workspace
      source domain fits index clockIdle wire member
    change clean wire = before wire at cleanBefore
    exact cleanBefore.trans (expectedWorkspace wire member).symm
  have coefficientOutsideWorkspace
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace) :
      wire ≠ layout.coefficientSignal := by
    have separated := layout.postGeneratorSignal_separated
      layout.coefficientSignal (by simp)
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨workspaceIndex, rfl⟩
    exact separated.2.2 workspaceIndex
  have dirtyWorkspace
      (wire : Fin (ExecutableRaw119 source).history.qubits)
      (member : wire ∈ historyRegisterWires layout.workspace) :
      dirty wire = expected wire := by
    unfold dirty
    rw [h3IdleTransformDirtyAction119_eq_replace_clean]
    rw [replaceQubitWire_outside _ _ _ _
      (coefficientOutsideWorkspace wire member)]
    exact cleanWorkspace wire member
  have cleanAction : applyOperator
      (h3IdlePostTransformOperator119 source domain) (basisKet clean) =
      basisKet (h3ActiveTailBasisAction119 source domain clean) :=
    h3IdlePostTransformOperator119_apply_basisKet_workspace_variant
      source domain fits index clockIdle clean cleanWorkspace
  have dirtyAction : applyOperator
      (h3IdlePostTransformOperator119 source domain) (basisKet dirty) =
      basisKet (h3ActiveTailBasisAction119 source domain dirty) :=
    h3IdlePostTransformOperator119_apply_basisKet_workspace_variant
      source domain fits index clockIdle dirty dirtyWorkspace
  rw [h3ActiveTailOperator119_decompose_idle,
    applyOperator_mul, applyOperator_mul, firstActive, idleAction]
  simp_rw [applyOperator_add, applyOperator_smul]
  rw [cleanAction, dirtyAction]

/-- Exact two-term full repaired H3 column on an arbitrary idle label. -/
theorem repairedH3RecordedTarget119_apply_basisKet_idle_general
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockIdle : ¬ index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    let clean := h3IdleTransformCleanAction119 layout
      source.historyParameters.binaryLabels before
    let dirty := h3IdleTransformDirtyAction119 layout
      source.historyParameters.binaryLabels before
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
  have tailAction := h3ActiveTailOperator119_apply_basisKet_idle_general
    source domain fits index clockIdle
  rw [targetEq, applyOperator_mul, applyOperator_mul, prefixAction, uniformAction]
  exact tailAction

/-- On every idle label, a clean logical row can only see the clean branch
of the exact two-term column. -/
theorem repairedH3RecordedTarget119_idle_general_clean_logical_entry
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (inputIndex outputIndex : OldHistoryIndex119 source)
    (clockIdle : ¬ inputIndex.clock.val <
      source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let input := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 inputIndex
    let row := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 outputIndex
    let before := h3BeforeUniform119 layout input
    let clean := h3IdleTransformCleanAction119 layout
      source.historyParameters.binaryLabels before
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
  let clean := h3IdleTransformCleanAction119 layout
    source.historyParameters.binaryLabels before
  let dirty := h3IdleTransformDirtyAction119 layout
    source.historyParameters.binaryLabels before
  let cleanOutput := h3ActiveTailBasisAction119 source domain clean
  let dirtyOutput := h3ActiveTailBasisAction119 source domain dirty
  have action := repairedH3RecordedTarget119_apply_basisKet_idle_general
    source domain fits inputIndex clockIdle
  have rowCoefficient : row layout.coefficientSignal = false :=
    correctedBranchHistoryBasis119_coefficientSignal_false119
      source domain fits h3SelectedBranch119 outputIndex
  have dirtyCoefficient : dirty layout.coefficientSignal = true := by
    unfold dirty
    rw [h3IdleTransformDirtyAction119_eq_replace_clean]
    simp
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
