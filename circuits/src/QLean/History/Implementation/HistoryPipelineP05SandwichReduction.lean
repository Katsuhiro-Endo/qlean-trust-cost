import QLean.History.Implementation.HistoryPipelineP05Sandwich

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open HistoryBlockEncoding
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

theorem selectorLocalOperator119_forward_entry
    (taylorOrder : Nat) (branch : Fin 4) :
    selectorLocalOperator119 taylorOrder 1
        (correctedSelectorBranchBasis119 branch)
        (selectorBasis119 false false) =
      (correctedPREPAmplitude119 taylorOrder branch : ℂ) := by
  simpa only [VerifiedCircuitCore.applyOperator_basisKet] using
    selectorLocalOperator_correctedAmplitude119 taylorOrder branch

theorem selectorLocalOperator119_inverse_entry
    (taylorOrder : Nat) (branch : Fin 4) :
    (star (selectorLocalOperator119 taylorOrder 1))
        (selectorBasis119 false false)
        (correctedSelectorBranchBasis119 branch) =
      (correctedPREPAmplitude119 taylorOrder branch : ℂ) := by
  rw [Matrix.star_apply,
    selectorLocalOperator119_forward_entry taylorOrder branch]
  simp [correctedPREPAmplitude119]

theorem repairedP05PhysicalOperator119_entry_branches
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    repairedP05PhysicalOperator119 source domain
        (correctedBranchHistoryBasis119 source domain fits ⟨0, by decide⟩
          outputIndex)
        (correctedBranchHistoryBasis119 source domain fits ⟨0, by decide⟩
          inputIndex) =
      ∑ inputBranch : Fin 4,
        (∑ outputBranch : Fin 4,
          (correctedPREPAmplitude119 source.historyParameters.taylorOrder
              outputBranch : ℂ) *
            repairedSelectMiddle119 source domain
              (correctedBranchHistoryBasis119 source domain fits outputBranch
                outputIndex)
              (correctedBranchHistoryBasis119 source domain fits inputBranch
                inputIndex)) *
          (correctedPREPAmplitude119 source.historyParameters.taylorOrder
            inputBranch : ℂ) := by
  rw [repairedP05PhysicalOperator119_entry_raw]
  rw [← correctedSelectorBranchEquiv119.sum_comp]
  apply Finset.sum_congr rfl
  intro inputBranch _
  rw [← correctedSelectorBranchEquiv119.sum_comp]
  change _ * selectorLocalOperator119 source.historyParameters.taylorOrder 1
      (correctedSelectorBranchBasis119 inputBranch)
      (selectorBasis119 false false) = _
  rw [selectorLocalOperator119_forward_entry]
  apply congrArg (fun value => value *
    (correctedPREPAmplitude119 source.historyParameters.taylorOrder
      inputBranch : ℂ))
  apply Finset.sum_congr rfl
  intro outputBranch _
  change (star (selectorLocalOperator119
        source.historyParameters.taylorOrder 1))
      (selectorBasis119 false false)
      (correctedSelectorBranchBasis119 outputBranch) *
        repairedSelectMiddle119 source domain
          (correctedBranchHistoryBasis119 source domain fits outputBranch
            outputIndex)
          (correctedBranchHistoryBasis119 source domain fits inputBranch
            inputIndex) = _
  rw [selectorLocalOperator119_inverse_entry]

theorem repairedSelectMiddle119_branch_zero_weighted_row
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    (∑ outputBranch : Fin 4,
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
            outputBranch : ℂ) *
          repairedSelectMiddle119 source domain
            (correctedBranchHistoryBasis119 source domain fits outputBranch
              outputIndex)
            (correctedBranchHistoryBasis119 source domain fits ⟨0, by decide⟩
              inputIndex)) =
      (correctedPREPAmplitude119 source.historyParameters.taylorOrder
          ⟨0, by decide⟩ : ℂ) *
        (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) ⟨0, by decide⟩
          outputIndex inputIndex : ℝ) : ℂ)) := by
  simp_rw [repairedSelectMiddle119_branch_zero_entry]
  simp [Fin.sum_univ_succ, correctedBranchOperator119,
    correctedCastMatrix119, HistoryBlockEncoding.HistorySpec.L0]
  by_cases equal : outputIndex = inputIndex <;> simp [equal]

theorem repairedSelectMiddle119_branch_one_weighted_row
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    (∑ outputBranch : Fin 4,
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
            outputBranch : ℂ) *
          repairedSelectMiddle119 source domain
            (correctedBranchHistoryBasis119 source domain fits outputBranch
              outputIndex)
            (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
              inputIndex)) =
      (correctedPREPAmplitude119 source.historyParameters.taylorOrder
          h2SelectedBranch119 : ℂ) *
        (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h2SelectedBranch119
          outputIndex inputIndex : ℝ) : ℂ)) := by
  simp_rw [repairedSelectMiddle119_branch_one_entry]
  simp [h2SelectedBranch119,
    correctedBranchOperator119, correctedCastMatrix119]

theorem repairedSelectMiddle119_branch_two_weighted_row
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    (∑ outputBranch : Fin 4,
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
            outputBranch : ℂ) *
          repairedSelectMiddle119 source domain
            (correctedBranchHistoryBasis119 source domain fits outputBranch
              outputIndex)
            (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
              inputIndex)) =
      (correctedPREPAmplitude119 source.historyParameters.taylorOrder
          h3SelectedBranch119 : ℂ) *
        (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
          outputIndex inputIndex : ℝ) : ℂ)) := by
  simp_rw [repairedSelectMiddle119_branch_two_entry]
  simp [h3SelectedBranch119]

theorem repairedP05PhysicalOperator119_entry_weighted
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    repairedP05PhysicalOperator119 source domain
        (correctedBranchHistoryBasis119 source domain fits ⟨0, by decide⟩
          outputIndex)
        (correctedBranchHistoryBasis119 source domain fits ⟨0, by decide⟩
          inputIndex) =
      ∑ branch : Fin 4,
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
            branch : ℂ) *
          (correctedPREPAmplitude119 source.historyParameters.taylorOrder
            branch : ℂ) *
          (((correctedBranchOperator119 source.historyParameters
            (commonModelQ119 source.toCommonSource119) branch
            outputIndex inputIndex : ℝ) : ℂ)) := by
  rw [repairedP05PhysicalOperator119_entry_branches]
  apply Finset.sum_congr rfl
  intro branch _
  fin_cases branch
  · rw [repairedSelectMiddle119_branch_zero_weighted_row]
    ring
  · change (∑ outputBranch : Fin 4,
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
            outputBranch : ℂ) *
          repairedSelectMiddle119 source domain
            (correctedBranchHistoryBasis119 source domain fits outputBranch
              outputIndex)
            (correctedBranchHistoryBasis119 source domain fits h2SelectedBranch119
              inputIndex)) *
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
          h2SelectedBranch119 : ℂ) =
      (correctedPREPAmplitude119 source.historyParameters.taylorOrder
          h2SelectedBranch119 : ℂ) *
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
          h2SelectedBranch119 : ℂ) *
        (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h2SelectedBranch119
          outputIndex inputIndex : ℝ) : ℂ))
    rw [repairedSelectMiddle119_branch_one_weighted_row]
    ring
  · change (∑ outputBranch : Fin 4,
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
            outputBranch : ℂ) *
          repairedSelectMiddle119 source domain
            (correctedBranchHistoryBasis119 source domain fits outputBranch
              outputIndex)
            (correctedBranchHistoryBasis119 source domain fits h3SelectedBranch119
              inputIndex)) *
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
          h3SelectedBranch119 : ℂ) =
      (correctedPREPAmplitude119 source.historyParameters.taylorOrder
          h3SelectedBranch119 : ℂ) *
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
          h3SelectedBranch119 : ℂ) *
        (((correctedBranchOperator119 source.historyParameters
          (commonModelQ119 source.toCommonSource119) h3SelectedBranch119
          outputIndex inputIndex : ℝ) : ℂ))
    rw [repairedSelectMiddle119_branch_two_weighted_row]
    ring
  · simp [correctedPREPAmplitude119, correctedLambda119]

theorem correctedPREPAmplitude_square_complex119
    (taylorOrder : Nat) (branch : Fin 4) :
    (correctedPREPAmplitude119 taylorOrder branch : ℂ) *
        (correctedPREPAmplitude119 taylorOrder branch : ℂ) =
      ((correctedLambda119 taylorOrder branch /
        correctedAlpha119 taylorOrder : ℝ) : ℂ) := by
  exact_mod_cast correctedPREPAmplitude_square119 taylorOrder branch

theorem correctedWeightedBranchSum119_eq_normalized
    (source : AlignedCommonSource119)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    (∑ branch : Fin 4,
        (correctedPREPAmplitude119 source.historyParameters.taylorOrder
            branch : ℂ) *
          (correctedPREPAmplitude119 source.historyParameters.taylorOrder
            branch : ℂ) *
          (((correctedBranchOperator119 source.historyParameters
            (commonModelQ119 source.toCommonSource119) branch
            outputIndex inputIndex : ℝ) : ℂ))) =
      ((correctedNormalizedHistoryTarget119 source.historyParameters
        (commonModelQ119 source.toCommonSource119)
        outputIndex inputIndex : ℝ) : ℂ) := by
  have weightedEqual := congrFun (congrFun
    (correctedWeightedSuccessBlock_eq_normalizedHistoryTarget119
      source.historyParameters
      (commonModelQ119 source.toCommonSource119)) outputIndex) inputIndex
  rw [← weightedEqual]
  simp_rw [correctedPREPAmplitude_square_complex119]
  simp [Fin.sum_univ_succ, correctedWeightedSuccessBlock119,
    Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    div_eq_mul_inv]
  ring

theorem repairedP05PhysicalOperator119_entry_eq_normalized
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    repairedP05PhysicalOperator119 source domain
        (correctedBranchHistoryBasis119 source domain fits ⟨0, by decide⟩
          outputIndex)
        (correctedBranchHistoryBasis119 source domain fits ⟨0, by decide⟩
          inputIndex) =
      ((correctedNormalizedHistoryTarget119 source.historyParameters
        (commonModelQ119 source.toCommonSource119)
        outputIndex inputIndex : ℝ) : ℂ) := by
  rw [repairedP05PhysicalOperator119_entry_weighted]
  exact correctedWeightedBranchSum119_eq_normalized source outputIndex inputIndex

end

end ExecutableHistoryExecutableHistory
