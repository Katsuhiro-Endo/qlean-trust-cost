import QLean.History.Implementation.HistoryPipelineH3ActiveUnitary

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
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

theorem h3UniformInverse119_nonzero_outside_eq
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (output : QubitBasis (ExecutableRaw119 source).history.qubits)
    (entryNonzero :
      (historyOrderUniformPreparationInverseExactComponent
        (ExecutableLayout119 source domain)
        (ExecutableClockEvidence119 source domain).uniformExternalControl
      ).target output
        (h3BeforeUniform119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits
            h3SelectedBranch119 index)) ≠ 0) :
    let layout := ExecutableLayout119 source domain
    let before := h3BeforeUniform119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h3SelectedBranch119 index)
    restrictToOutsideWires
        (historyOrderUniformExternalControlLayout layout
          (ExecutableClockEvidence119 source domain).uniformExternalControl
        ).placement output =
      restrictToOutsideWires
        (historyOrderUniformExternalControlLayout layout
          (ExecutableClockEvidence119 source domain).uniformExternalControl
        ).placement before := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).uniformExternalControl
  let blockParameters := HistoryRawSchema.parameters203
    (ExecutableRaw119 source).history
    (ExecutableAdmissible119 source domain).analytic
  let parameters := historyOrderUniformPreparationParameters blockParameters
  let controlled := historyOrderUniformExternalControlLayout layout evidence
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  have clean : externallyControlledCleanWorkPredicate
      (historyOrderUniformExternalControlCleanWorkValid layout evidence) before :=
    h3BeforeUniform119_uniform_work_clean source domain fits index
  have semanticEntry :
      ExternallyControlledPrimitivePlan.strictPlanOperator (fun _ => 0)
          controlled (shuklaVedulaWidthOnlyUniformInversePlan parameters)
          output before =
        externallyControlledWireLiftOperator controlled
          (star (shuklaVedulaWidthOnlyUniformStrictOperator (fun _ => 0)
            parameters)) output before :=
    uniformInverseStrict_clean_entry119 parameters controlled
      (historyOrderUniformExternalControlCleanWorkValid layout evidence)
      output before clean
  have strictNonzero :
      ExternallyControlledPrimitivePlan.strictPlanOperator (fun _ => 0)
          controlled (shuklaVedulaWidthOnlyUniformInversePlan parameters)
          output before ≠ 0 := by
    rw [historyOrderUniformPreparationInverseExactComponent_target] at entryNonzero
    exact entryNonzero
  have wireLiftNonzero : externallyControlledWireLiftOperator controlled
      (star (shuklaVedulaWidthOnlyUniformStrictOperator (fun _ => 0)
        parameters)) output before ≠ 0 := by
    rw [semanticEntry] at strictNonzero
    exact strictNonzero
  funext outside
  exact externallyControlledWireLiftOperator_preservesOutsidePlacement
    controlled _ output before wireLiftNonzero outside.1 (by
      intro member
      rcases Finset.mem_image.mp member with ⟨placed, _, equal⟩
      exact outside.2 placed equal)

theorem h3ZeroOrder119_uniform_outside_eq
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    let layout := ExecutableLayout119 source domain
    let before := h3BeforeUniform119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h3SelectedBranch119 index)
    restrictToOutsideWires
        (historyOrderUniformExternalControlLayout layout
          (ExecutableClockEvidence119 source domain).uniformExternalControl
        ).placement (h3ZeroOrder119 layout before) =
      restrictToOutsideWires
        (historyOrderUniformExternalControlLayout layout
          (ExecutableClockEvidence119 source domain).uniformExternalControl
        ).placement before := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).uniformExternalControl
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  let zero := h3ZeroOrder119 layout before
  funext outside
  change zero outside.val = before outside.val
  apply writeRegisterValue_apply_outside
  intro orderIndex
  exact outside.property orderIndex

theorem h3ActiveTailOperator119_entry_expected
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let before := h3BeforeUniform119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h3SelectedBranch119 index)
    let expected := h3ZeroOrder119 layout before
    let row := h3ActiveTailBasisAction119 source domain expected
    h3ActiveTailOperator119 source domain row expected = (-1 : Complex) := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let before := h3BeforeUniform119 layout
    (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119 index)
  let expected := h3ZeroOrder119 layout before
  let row := h3ActiveTailBasisAction119 source domain expected
  have action := h3ActiveTailOperator119_apply_basisKet_of_uniform_outside
    source domain fits index clockActive expected
      (h3ZeroOrder119_uniform_outside_eq source domain fits index)
  have point := congrFun action row
  simpa [VerifiedCircuitCore.applyOperator_basisKet,
    VerifiedCircuitCore.basisKet_apply, row] using point

theorem h3ActiveTailOperator119_middle_unique
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks)
    (middle : QubitBasis (ExecutableRaw119 source).history.qubits)
    (uniformNonzero :
      (historyOrderUniformPreparationInverseExactComponent
        (ExecutableLayout119 source domain)
        (ExecutableClockEvidence119 source domain).uniformExternalControl
      ).target middle
        (h3BeforeUniform119 (ExecutableLayout119 source domain)
          (correctedBranchHistoryBasis119 source domain fits
            h3SelectedBranch119 index)) ≠ 0)
    (tailNonzero :
      let layout := ExecutableLayout119 source domain
      let before := h3BeforeUniform119 layout
        (correctedBranchHistoryBasis119 source domain fits
          h3SelectedBranch119 index)
      let expected := h3ZeroOrder119 layout before
      let row := h3ActiveTailBasisAction119 source domain expected
      h3ActiveTailOperator119 source domain row middle ≠ 0) :
    let layout := ExecutableLayout119 source domain
    let before := h3BeforeUniform119 layout
      (correctedBranchHistoryBasis119 source domain fits
        h3SelectedBranch119 index)
    middle = h3ZeroOrder119 layout before := by
  dsimp only at tailNonzero ⊢
  let layout := ExecutableLayout119 source domain
  let before := h3BeforeUniform119 layout
    (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119 index)
  let expected := h3ZeroOrder119 layout before
  let row := h3ActiveTailBasisAction119 source domain expected
  have outsideMiddle := h3UniformInverse119_nonzero_outside_eq
    source domain fits index middle uniformNonzero
  have actionMiddle := h3ActiveTailOperator119_apply_basisKet_of_uniform_outside
    source domain fits index clockActive middle outsideMiddle
  have actionExpected := h3ActiveTailOperator119_apply_basisKet_of_uniform_outside
    source domain fits index clockActive expected
      (h3ZeroOrder119_uniform_outside_eq source domain fits index)
  have rowEq : row = h3ActiveTailBasisAction119 source domain middle := by
    by_contra unequal
    have point := congrFun actionMiddle row
    have zero : h3ActiveTailOperator119 source domain row middle = 0 := by
      simpa [VerifiedCircuitCore.applyOperator_basisKet,
        VerifiedCircuitCore.basisKet_apply, unequal] using point
    exact tailNonzero zero
  have outputEq :
      VerifiedCircuitCore.applyOperator (h3ActiveTailOperator119 source domain)
          (VerifiedCircuitCore.basisKet middle) =
        VerifiedCircuitCore.applyOperator (h3ActiveTailOperator119 source domain)
          (VerifiedCircuitCore.basisKet expected) := by
    have actionEq : h3ActiveTailBasisAction119 source domain middle =
        h3ActiveTailBasisAction119 source domain expected := by
      simpa [row] using rowEq.symm
    rw [actionMiddle, actionExpected, actionEq]
  have ketEq : VerifiedCircuitCore.basisKet middle =
      VerifiedCircuitCore.basisKet expected :=
    h3ActiveTailOperator119_apply_injective source domain outputEq
  by_contra unequal
  have point := congrFun ketEq middle
  have middleEq : middle = expected := by
    simpa [VerifiedCircuitCore.basisKet_apply] using point
  exact unequal middleEq

theorem repairedH3RecordedTarget119_active_physical_entry
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (clockActive : index.clock.val < source.historyParameters.physicalClocks) :
    let layout := ExecutableLayout119 source domain
    let logical := correctedBranchHistoryBasis119 source domain fits
      h3SelectedBranch119 index
    let before := h3BeforeUniform119 layout logical
    let expected := h3ZeroOrder119 layout before
    let row := h3ActiveTailBasisAction119 source domain expected
    repairedH3RecordedTarget119 source domain row logical =
      if index.state.label.val ≤ source.historyParameters.taylorOrder then
        -(((1 / Real.sqrt
          (source.historyParameters.taylorOrder + 1) : Real) : Complex))
      else 0 := by
  dsimp only
  let layout := ExecutableLayout119 source domain
  let logical := correctedBranchHistoryBasis119 source domain fits
    h3SelectedBranch119 index
  let before := h3BeforeUniform119 layout logical
  let expected := h3ZeroOrder119 layout before
  let row := h3ActiveTailBasisAction119 source domain expected
  let uniform := (historyOrderUniformPreparationInverseExactComponent layout
    (ExecutableClockEvidence119 source domain).uniformExternalControl).target
  let tail := h3ActiveTailOperator119 source domain
  have targetEq := repairedH3RecordedTarget119_decompose_active source domain
  have prefixAction := h3ActivePrefixOperator119_apply_basisKet
    source domain fits index
  have tailExpected : tail row expected = (-1 : Complex) :=
    h3ActiveTailOperator119_entry_expected source domain fits index clockActive
  have uniformExpected : uniform expected before =
      if index.state.label.val ≤ source.historyParameters.taylorOrder then
        (((1 / Real.sqrt
          (source.historyParameters.taylorOrder + 1) : Real) : Complex))
      else 0 := by
    exact h3UniformInverse_zero_order_entry119
      source domain fits index clockActive
  calc
    repairedH3RecordedTarget119 source domain row logical =
        VerifiedCircuitCore.applyOperator
          (repairedH3RecordedTarget119 source domain)
          (VerifiedCircuitCore.basisKet logical) row := by
      symm
      exact VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = VerifiedCircuitCore.applyOperator (tail * uniform)
          (VerifiedCircuitCore.applyOperator
            (h3ActivePrefixOperator119 source domain)
            (VerifiedCircuitCore.basisKet logical)) row := by
      rw [targetEq, VerifiedCircuitCore.applyOperator_mul]
    _ = VerifiedCircuitCore.applyOperator (tail * uniform)
          (VerifiedCircuitCore.basisKet before) row := by rw [prefixAction]
    _ = (tail * uniform) row before := by
      exact VerifiedCircuitCore.applyOperator_basisKet _ _ _
    _ = ∑ middle, tail row middle * uniform middle before := by
      rw [Matrix.mul_apply]
    _ = tail row expected * uniform expected before := by
      rw [Fintype.sum_eq_single expected]
      intro middle middleNe
      by_cases uniformZero : uniform middle before = 0
      · rw [uniformZero]
        simp
      by_cases tailZero : tail row middle = 0
      · rw [tailZero]
        simp
      have middleEq : middle = expected :=
        h3ActiveTailOperator119_middle_unique source domain fits index
          clockActive middle uniformZero tailZero
      exact (middleNe middleEq).elim
    _ = if index.state.label.val ≤ source.historyParameters.taylorOrder then
          -(((1 / Real.sqrt
            (source.historyParameters.taylorOrder + 1) : Real) : Complex))
        else 0 := by
      rw [tailExpected, uniformExpected]
      split <;> simp

end
end ExecutableHistoryExecutableHistory
