import QLean.History.Implementation.HistoryPipelineExecutableHistoryRaw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open HistoryBlockEncoding
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof.Analytic
open HistoryPipelineReferenceRawCompiler
open HistoryPipelineReferenceRawValueConstructor
open HistoryPipelineReferenceRawValueConstructorV2
open HistoryPipelineReferenceRawValueConstructorV3
open HistoryPipelineReferenceAdmissibility041

noncomputable section

private theorem highRatio_pos_lt_one119
    (taylorOrder : Nat) {omega : ℝ} (omegaPositive : 0 < omega) :
    0 < (1 + omega) / selectorAlpha119 taylorOrder omega ∧
      (1 + omega) / selectorAlpha119 taylorOrder omega < 1 := by
  have tailPositive : 0 < Real.sqrt ((taylorOrder : ℝ) + 1) := by
    apply Real.sqrt_pos.2
    positivity
  have alphaPositive : 0 < selectorAlpha119 taylorOrder omega := by
    exact selectorAlpha119_positive taylorOrder (le_of_lt omegaPositive)
  constructor
  · exact div_pos (by linarith) alphaPositive
  · apply (div_lt_one alphaPositive).2
    unfold selectorAlpha119 HistoryBlockEncoding.HistoryLCU.alphaH
    linarith

private theorem lowRatio_pos_lt_one119 {omega : ℝ} (omegaPositive : 0 < omega) :
    0 < 1 / (1 + omega) ∧ 1 / (1 + omega) < 1 := by
  constructor
  · positivity
  · exact (div_lt_one (by linarith)).2 (by linarith)

private theorem sqrt_pos_lt_one119 {x : ℝ}
    (positive : 0 < x) (lessOne : x < 1) :
    0 < Real.sqrt x ∧ Real.sqrt x < 1 := by
  have nonnegative : 0 ≤ x := le_of_lt positive
  have sqrtPositive : 0 < Real.sqrt x := Real.sqrt_pos.2 positive
  have sqrtNonnegative : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have square : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt nonnegative
  constructor
  · exact sqrtPositive
  · nlinarith

theorem selectorHighAngle119_pos
    (taylorOrder : Nat) {omega : ℝ} (omegaPositive : 0 < omega) :
    0 < selectorHighAngle119 taylorOrder omega := by
  let ratio := (1 + omega) / selectorAlpha119 taylorOrder omega
  have ratioFacts := highRatio_pos_lt_one119 taylorOrder omegaPositive
  have sqrtFacts := sqrt_pos_lt_one119 ratioFacts.1 ratioFacts.2
  unfold selectorHighAngle119
  have arccosPositive : 0 < Real.arccos (Real.sqrt ratio) :=
    Real.arccos_pos.2 sqrtFacts.2
  positivity

theorem selectorLowAngle119_pos {omega : ℝ} (omegaPositive : 0 < omega) :
    0 < selectorLowAngle119 omega := by
  let ratio := 1 / (1 + omega)
  have ratioFacts := lowRatio_pos_lt_one119 omegaPositive
  have sqrtFacts := sqrt_pos_lt_one119 ratioFacts.1 ratioFacts.2
  unfold selectorLowAngle119
  exact Real.arccos_pos.2 sqrtFacts.2

theorem selectorHighAngle119_le_pi
    (taylorOrder : Nat) {omega : ℝ} :
    selectorHighAngle119 taylorOrder omega ≤ Real.pi := by
  have hsqrt : 0 ≤ Real.sqrt
      ((1 + omega) / selectorAlpha119 taylorOrder omega) :=
    Real.sqrt_nonneg _
  have harccos : Real.arccos
      (Real.sqrt ((1 + omega) / selectorAlpha119 taylorOrder omega)) ≤
      Real.pi / 2 := Real.arccos_le_pi_div_two.2 hsqrt
  unfold selectorHighAngle119
  linarith

theorem selectorLowAngle119_le_pi {omega : ℝ} :
    selectorLowAngle119 omega ≤ Real.pi := by
  have hsqrt : 0 ≤ Real.sqrt (1 / (1 + omega)) := Real.sqrt_nonneg _
  have harccos : Real.arccos (Real.sqrt (1 / (1 + omega))) ≤
      Real.pi / 2 := Real.arccos_le_pi_div_two.2 hsqrt
  unfold selectorLowAngle119
  have piPositive : 0 < Real.pi := Real.pi_pos
  linarith

theorem compiledTaylorCoefficientAngle119_gt_pi (n : Nat) :
    Real.pi < (compiledTaylorCoefficientAngle119 n).uniformValue := by
  let x : ℝ := -(1 : ℝ) / ((n + 1 : Nat) : ℝ)
  have denominatorPositive : (0 : ℝ) < ((n + 1 : Nat) : ℝ) := by positivity
  have denominatorAtLeastOne : (1 : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have xNegative : x < 0 := by
    dsimp [x]
    exact div_neg_of_neg_of_pos (by norm_num) denominatorPositive
  have xLower : (-1 : ℝ) ≤ x := by
    dsimp [x]
    have hdiv : (1 : ℝ) / ((n + 1 : Nat) : ℝ) ≤ 1 :=
      (div_le_one denominatorPositive).2 denominatorAtLeastOne
    calc
      (-1 : ℝ) ≤ -((1 : ℝ) / ((n + 1 : Nat) : ℝ)) := neg_le_neg hdiv
      _ = -(1 : ℝ) / ((n + 1 : Nat) : ℝ) := by ring
  have harccos : Real.arccos 0 < Real.arccos x :=
    Real.arccos_lt_arccos xLower xNegative (by norm_num)
  rw [compiledTaylorCoefficientAngle119_value]
  change Real.pi < 2 * Real.arccos x
  rw [Real.arccos_zero] at harccos
  linarith

theorem executableHistoryDomain119 (source : AlignedCommonSource119) :
    ExecutableHistoryDomain119 source := by
  let blockSize := historyIdleBlockSize source.historyParameters.taylorOrder
  have blockSizePositive : 0 < blockSize := by
    exact historyIdleBlockSize040_pos source.historyParameters.taylorOrder
  have blockSizeAtLeastTwo : 2 ≤ blockSize := by
    exact historyIdleBlockSize040_ge_two source.historyParameters.taylorOrder
  have productAtLeastTwo : 2 ≤ source.historyBlocks * blockSize := by
    have blocksAtLeastOne : 1 ≤ source.historyBlocks := source.historyBlocksPositive
    exact le_trans blockSizeAtLeastTwo
      (by simpa using Nat.mul_le_mul_right blockSize blocksAtLeastOne)
  have addOneEq : rawIdlingSteps041 (referenceData119 source) + 1 =
      source.historyBlocks * blockSize := by
    change (source.historyBlocks * blockSize - 1) + 1 =
      source.historyBlocks * blockSize
    exact Nat.sub_add_cancel (by omega)
  refine { analyticDomain := ?_ }
  refine {
    hqh := ?_
    timeSteps_pos := ?_
    idlingSteps_pos := ?_
    idlingBlockSize_pos := blockSizePositive
    historyBlocks_pos := source.historyBlocksPositive
    selectorCount_pos := by
      change 0 < (3 : Nat)
      norm_num
    duration_step_relation := ?_
    idling_divisibility := ?_
    history_block_relation := ?_
    selector_angles_pos := ?_
    coefficient_angles_pos := ?_
    idle_angle_pos := ?_
    role_separation := ?_ }
  · change |(source.historyParameters.stepSize : ℝ) *
      generatorAlpha119 source.qParameters| ≤ 1
    have hnonnegative : 0 ≤ (source.historyParameters.stepSize : ℝ) *
        generatorAlpha119 source.qParameters := by
      have hstep : 0 < (source.historyParameters.stepSize : ℝ) := by
        exact_mod_cast source.stepPositive
      have hK : 0 < (source.qParameters.K : ℝ) := by
        exact_mod_cast source.qParameters.K_pos
      unfold generatorAlpha119
      positivity
    rw [abs_of_nonneg hnonnegative]
    simpa [generatorAlpha119, mul_comm, mul_left_comm, mul_assoc] using
      source.scaledStepSmall
  · change 0 < source.historyParameters.physicalClocks
    exact source.historyWellFormed.1
  · change 0 < rawIdlingSteps041 (referenceData119 source)
    omega
  · change (source.historyParameters.stepSize : ℝ) *
        (source.historyParameters.physicalClocks : ℝ) =
      (source.historyParameters.stepSize : ℝ) *
        (source.historyParameters.physicalClocks : ℝ)
    rfl
  · change (rawIdlingSteps041 (referenceData119 source) + 1) % blockSize = 0
    rw [addOneEq]
    simp
  · change source.historyBlocks * blockSize =
      rawIdlingSteps041 (referenceData119 source) + 1
    exact addOneEq.symm
  · intro i
    fin_cases i
    · change 0 < (selectorRaw119 source ⟨0, by decide⟩).uniformValue
      rw [selectorRaw119_high_value]
      exact selectorHighAngle119_pos _ (omegaH119_positive source.toCommonSource119)
    · change 0 < (selectorRaw119 source ⟨1, by decide⟩).uniformValue
      rw [selectorRaw119_low_value source _ (by decide)]
      exact selectorLowAngle119_pos (omegaH119_positive source.toCommonSource119)
    · change 0 < (selectorRaw119 source ⟨2, by decide⟩).uniformValue
      rw [selectorRaw119_low_value source _ (by decide)]
      exact selectorLowAngle119_pos (omegaH119_positive source.toCommonSource119)
  · intro n
    change 0 < (compiledTaylorCoefficientAngle119 n).uniformValue
    have h := compiledTaylorCoefficientAngle119_gt_pi n
    have piPositive := Real.pi_pos
    linarith
  · change 0 < compiledIdleCoefficientAngle119.uniformValue
    rw [compiledIdleCoefficientAngle119_value]
    positivity
  · intro i n
    have coefficientLarge := compiledTaylorCoefficientAngle119_gt_pi n
    fin_cases i
    · change (compiledTaylorCoefficientAngle119 n).uniformValue ≠
        (selectorRaw119 source ⟨0, by decide⟩).uniformValue
      rw [selectorRaw119_high_value]
      have selectorSmall := selectorHighAngle119_le_pi
        (omega := omegaH119 source.toCommonSource119)
        source.historyParameters.taylorOrder
      linarith
    · change (compiledTaylorCoefficientAngle119 n).uniformValue ≠
        (selectorRaw119 source ⟨1, by decide⟩).uniformValue
      rw [selectorRaw119_low_value source _ (by decide)]
      have selectorSmall := selectorLowAngle119_le_pi
        (omega := omegaH119 source.toCommonSource119)
      linarith
    · change (compiledTaylorCoefficientAngle119 n).uniformValue ≠
        (selectorRaw119 source ⟨2, by decide⟩).uniformValue
      rw [selectorRaw119_low_value source _ (by decide)]
      have selectorSmall := selectorLowAngle119_le_pi
        (omega := omegaH119 source.toCommonSource119)
      linarith

end
end ExecutableHistoryExecutableHistory
