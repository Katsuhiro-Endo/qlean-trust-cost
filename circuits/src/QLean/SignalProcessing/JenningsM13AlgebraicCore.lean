import QLean.History.Implementation.HistoryPipelineP18Final
import QLean.History.JenningsHistoryWellPosed

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace JenningsM13AlgebraicCore

open Matrix
open JenningsHistory
open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open JenningsHistoryWellPosed
open ProbabilityGeneratorQProof

noncomputable section

theorem unitNormSquared_nonnegative {index : Type*} [Fintype index]
    (vector : index → ℝ) :
    0 ≤ unitNormSquared vector := by
  exact Finset.sum_nonneg fun index _ => mul_self_nonneg (vector index)

theorem unitNormSquared_positive_of_ne_zero
    {index : Type*} [Fintype index]
    (vector : index → ℝ) (nonzero : vector ≠ 0) :
    0 < unitNormSquared vector := by
  have existsNonzero : ∃ index, vector index ≠ 0 := by
    by_contra absent
    apply nonzero
    funext index
    have notNonzero : ¬ vector index ≠ 0 := by
      intro indexNonzero
      exact absent ⟨index, indexNonzero⟩
    exact not_ne_iff.mp notNonzero
  obtain ⟨index, indexNonzero⟩ := existsNonzero
  have termPositive : 0 < vector index * vector index :=
    mul_self_pos.2 indexNonzero
  have termBound : vector index * vector index ≤
      ∑ i, vector i * vector i := by
    exact Finset.single_le_sum
      (fun i _ => mul_self_nonneg (vector i)) (Finset.mem_univ index)
  exact lt_of_lt_of_le termPositive termBound

theorem rhsNorm_ne_zero_of_entry
    {d c r m R : Nat} (system : HistorySpec d c r m R)
    (row : HistoryIndex d c R) (entryNonzero : historyRhs system row ≠ 0) :
    rhsNorm system ≠ 0 := by
  have termPositive : 0 < historyRhs system row * historyRhs system row :=
    mul_self_pos.2 entryNonzero
  have termBound : historyRhs system row * historyRhs system row ≤
      rhsNormSq system := by
    unfold rhsNormSq
    exact Finset.single_le_sum
      (fun i _ => mul_self_nonneg (historyRhs system i))
      (Finset.mem_univ row)
  have normSqPositive : 0 < rhsNormSq system :=
    lt_of_lt_of_le termPositive termBound
  exact ne_of_gt (Real.sqrt_pos.2 normSqPositive)

theorem executableRhsNorm_ne_zero
    (source : AlignedCommonSource119)
    (state : QConfiguration source.qParameters)
    (initialNonzero : source.initial state ≠ 0) :
    rhsNorm (executableSystem119 source) ≠ 0 := by
  have clockPositive : 0 < source.historyParameters.clockEnd := by
    have physicalPositive : 0 < source.historyParameters.physicalClocks :=
      source.historyWellFormed.1
    rw [source.clockEndExact]
    omega
  have orderPositive : 0 < source.historyParameters.binaryLabels := by
    have taylorPositive : 0 < source.historyParameters.taylorOrder :=
      source.historyWellFormed.2.1
    have taylorLess : source.historyParameters.taylorOrder <
        source.historyParameters.binaryLabels :=
      source.historyWellFormed.2.2.2.1
    omega
  let row : HistoryIndex (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) :=
    { clock := ⟨0, clockPositive⟩
      order := ⟨0, orderPositive⟩
      state := ExecutableHistoryReferenceM10Bridge.configurationEquiv
        (QConfiguration source.qParameters) state }
  have castNonzero : (source.initial state : ℝ) ≠ 0 := by
    exact_mod_cast initialNonzero
  apply rhsNorm_ne_zero_of_entry (executableSystem119 source) row
  simpa [row, historyRhs, executableSystem119,
    ExecutableHistoryReferenceM10Bridge.translatedSystem,
    ExecutableHistoryReferenceM10Bridge.configurationEquiv] using castNonzero

theorem normalizedRhs_unitNorm_of_ne_zero
    {d c r m R : Nat} (system : HistorySpec d c r m R)
    (normNonzero : rhsNorm system ≠ 0) :
    unitNorm (normalizedRhs system) := by
  have normSqNonnegative : 0 ≤ rhsNormSq system := by
    unfold rhsNormSq
    exact Finset.sum_nonneg fun index _ =>
      mul_self_nonneg (historyRhs system index)
  have normSquare : rhsNorm system * rhsNorm system = rhsNormSq system := by
    unfold rhsNorm
    nlinarith [Real.sq_sqrt normSqNonnegative]
  unfold unitNorm unitNormSquared normalizedRhs
  calc
    (∑ index, (historyRhs system index / rhsNorm system) *
        (historyRhs system index / rhsNorm system)) =
        ∑ index, (historyRhs system index * historyRhs system index) /
          (rhsNorm system * rhsNorm system) := by
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ = rhsNormSq system / (rhsNorm system * rhsNorm system) := by
      unfold rhsNormSq
      rw [Finset.sum_div]
    _ = 1 := by
      rw [normSquare]
      field_simp [show rhsNormSq system ≠ 0 by
        intro equal
        apply normNonzero
        have : rhsNorm system ^ 2 = 0 := by
          rw [show rhsNorm system ^ 2 = rhsNormSq system by
            nlinarith [normSquare], equal]
        nlinarith]

theorem dalzellBPlus_unitNorm_of_rhsNorm_ne_zero
    {d c r m R : Nat} (system : HistorySpec d c r m R)
    (normNonzero : rhsNorm system ≠ 0) :
    unitNorm (dalzellBPlus system) := by
  have normalized := normalizedRhs_unitNorm_of_ne_zero system normNonzero
  have sqrtTwoPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have sqrtTwoSquare : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold unitNorm unitNormSquared at normalized ⊢
  rw [Fintype.sum_sum_type]
  simp only [dalzellBPlus]
  calc
    (∑ index, (normalizedRhs system index / Real.sqrt 2) *
        (normalizedRhs system index / Real.sqrt 2)) +
        ∑ _unit : Unit, (1 / Real.sqrt 2) * (1 / Real.sqrt 2) =
      (∑ index, normalizedRhs system index * normalizedRhs system index) /
          (Real.sqrt 2 * Real.sqrt 2) +
        1 / (Real.sqrt 2 * Real.sqrt 2) := by
      congr 1
      · calc
          (∑ index, (normalizedRhs system index / Real.sqrt 2) *
              (normalizedRhs system index / Real.sqrt 2)) =
              ∑ index, (normalizedRhs system index * normalizedRhs system index) /
                (Real.sqrt 2 * Real.sqrt 2) := by
            apply Finset.sum_congr rfl
            intro index _
            ring
          _ = (∑ index, normalizedRhs system index * normalizedRhs system index) /
                (Real.sqrt 2 * Real.sqrt 2) := by rw [Finset.sum_div]
      · simp
        field_simp [ne_of_gt sqrtTwoPositive]
        nlinarith [sqrtTwoSquare]
    _ = 1 := by
      rw [normalized, sqrtTwoSquare]
      norm_num

def executableHistorySolution119 (source : AlignedCommonSource119) :
    HistoryVector (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source) :=
  (historyMatrix (executableSystem119 source))⁻¹.mulVec
    (historyRhs (executableSystem119 source))

theorem executableHistorySolution119_spec
    (source : AlignedCommonSource119) :
    linearApply (historyMatrix (executableSystem119 source))
        (executableHistorySolution119 source) =
      historyRhs (executableSystem119 source) := by
  unfold linearApply executableHistorySolution119
  have inverseProduct : historyMatrix (executableSystem119 source) *
      (historyMatrix (executableSystem119 source))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _
      (historyMatrix_det_isUnit (executableSystem119 source))
  have applied := congrArg (fun matrix => matrix.mulVec
      (historyRhs (executableSystem119 source))) inverseProduct
  simpa [Matrix.mulVec_mulVec] using applied

structure ExecutableM13AlgebraicCore119
    (source : AlignedCommonSource119) where
  nu : ℝ
  x : HistoryVector (ExecutableD119 source) (ExecutableC119 source)
    (ExecutableLabels119 source)
  hwell : wellPosed
    (GramOperator.enlargedMatrix (executableSystem119 source)
      (executableAlpha119 source) nu)
  hdet : IsUnit
    (Matrix.det (GramOperator.enlargedMatrix (executableSystem119 source)
      (executableAlpha119 source) nu))
  hraw : linearApply (historyMatrix (executableSystem119 source)) x =
    historyRhs (executableSystem119 source)
  hrhs : rhsNorm (executableSystem119 source) ≠ 0
  hAlpha : executableAlpha119 source ≠ 0
  hNu : nu ≠ 0
  hNuPos : 0 < nu
  hAlphaPos : 0 < executableAlpha119 source
  hb : unitNorm (GramOperator.bPlus (executableSystem119 source))
  hXPos : 0 < unitNormSquared
    (ConcreteHistoryInput.m13XAlpha (executableSystem119 source)
      (executableAlpha119 source) x)

def executableM13AlgebraicCore119
    (source : AlignedCommonSource119)
    (state : QConfiguration source.qParameters)
    (initialNonzero : source.initial state ≠ 0) :
    ExecutableM13AlgebraicCore119 source := by
  let system := executableSystem119 source
  let alpha := executableAlpha119 source
  let x := executableHistorySolution119 source
  have alphaPositive : 0 < alpha := by
    exact ExecutableHistoryExecutableHistory.correctedAlpha119_positive
      source.historyParameters.taylorOrder
  have alphaNonzero : alpha ≠ 0 := ne_of_gt alphaPositive
  have rhsNonzero : rhsNorm system ≠ 0 := by
    exact executableRhsNorm_ne_zero source state initialNonzero
  have xSpec : linearApply (historyMatrix system) x = historyRhs system := by
    exact executableHistorySolution119_spec source
  have xNonzero : x ≠ 0 := by
    intro xZero
    have rhsZero : historyRhs system = 0 := by
      rw [← xSpec, xZero]
      simp [linearApply]
    apply rhsNonzero
    simp [rhsNorm, rhsNormSq, rhsZero]
  have scaledXNonzero : ConcreteHistoryInput.m13XAlpha system alpha x ≠ 0 := by
    unfold ConcreteHistoryInput.m13XAlpha
    exact smul_ne_zero (div_ne_zero alphaNonzero rhsNonzero) xNonzero
  refine {
    nu := 1
    x := x
    hwell := ?_
    hdet := ?_
    hraw := xSpec
    hrhs := rhsNonzero
    hAlpha := alphaNonzero
    hNu := by norm_num
    hNuPos := by norm_num
    hAlphaPos := alphaPositive
    hb := ?_
    hXPos := unitNormSquared_positive_of_ne_zero _ scaledXNonzero }
  · simpa [system, alpha, GramOperator.enlargedMatrix] using
      dalzellExtendedH_wellPosed system alpha 1 alphaNonzero (by norm_num)
  · simpa [system, alpha, GramOperator.enlargedMatrix] using
      dalzellExtendedH_det_isUnit system alpha 1 alphaNonzero (by norm_num)
  · simpa [GramOperator.bPlus] using
      dalzellBPlus_unitNorm_of_rhsNorm_ne_zero system rhsNonzero

end
end JenningsM13AlgebraicCore
