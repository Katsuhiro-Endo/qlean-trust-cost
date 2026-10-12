import QLean.Circuits.FiniteScientificCircuitSource
import QLean.Circuits.FiniteKernelPolynomial
import QLean.History.JenningsHistoryInverseBound
import QLean.SignalProcessing.JenningsM13AnalyticBounds

/-! Proof of the finite inverse-norm planning bound. This is a mathematical
bound on the history operator, not a numerical phase-accuracy certificate. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace QLean.Circuits.FiniteScientificSpectralBound

open Matrix JenningsHistory JenningsM13AnalyticBounds
open ExecutableHistoryExecutableHistory ExecutableHistoryExecutableP18
open QLean.Circuits.FiniteScientificCircuitSource
open scoped Matrix.Norms.L2Operator

theorem normalization_bound (source : AlignedCommonSource119) :
    executableAlpha119 source ≤ (source.historyParameters.taylorOrder + 3 : Nat) := by
  have nonneg : 0 ≤ (source.historyParameters.taylorOrder : ℝ) + 1 := by positivity
  have square := Real.sq_sqrt nonneg
  have root_nonneg := Real.sqrt_nonneg ((source.historyParameters.taylorOrder : ℝ) + 1)
  change 2 + Real.sqrt ((source.historyParameters.taylorOrder : ℝ) + 1) ≤ _
  push_cast
  nlinarith

theorem scaledHistory_norm_le_one (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source) :
    ‖scaledHistory (executableSystem119 source) (executableAlpha119 source)‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro vector
  change ‖(WithLp.toLp 2
    ((scaledHistory (executableSystem119 source) (executableAlpha119 source)).mulVec
      vector.ofLp) : EuclideanSpace ℝ _)‖ ≤ 1 * ‖vector‖
  rw [one_mul]
  have bound := executableScaledHistory_sqrt_contraction source domain fits vector.ofLp
  simpa only [sqrt_unitNormSquared_eq_euclideanNorm, WithLp.toLp_ofLp] using bound

theorem inverse_norm_le_finite (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source) :
    executableHistoryInverseNorm119 source ≤
      (FiniteKernelPolynomial.inverseBound source.historyParameters.taylorOrder
        source.historyParameters.clockEnd source.historyParameters.binaryLabels : ℝ) := by
  letI : Nonempty (ProbabilityGeneratorQProof.QConfiguration source.qParameters) :=
    ⟨canonicalQConfiguration source.qParameters⟩
  letI : Nonempty (HistoryIndex (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) := ⟨
    { clock := ⟨0, source.historyWellFormed.clockEnd_pos⟩
      order := ⟨0, source.historyWellFormed.binaryLabels_pos⟩
      state := ⟨0, Fintype.card_pos⟩ }⟩
  have alpha_pos : 0 < executableAlpha119 source := by
    change 0 < 2 + Real.sqrt _
    positivity
  have raw : historyMatrix (executableSystem119 source) =
      executableAlpha119 source •
        scaledHistory (executableSystem119 source) (executableAlpha119 source) := by
    ext row col
    simp only [Matrix.smul_apply, smul_eq_mul, scaledHistory]
    field_simp [alpha_pos.ne']
  have historyNorm : ‖historyMatrix (executableSystem119 source)‖ ≤
      (source.historyParameters.taylorOrder + 3 : Nat) := by
    rw [raw, norm_smul, Real.norm_of_nonneg alpha_pos.le]
    calc
      _ ≤ executableAlpha119 source * 1 :=
        mul_le_mul_of_nonneg_left (scaledHistory_norm_le_one source domain fits) alpha_pos.le
      _ ≤ _ := by simpa using normalization_bound source
  have bounded := JenningsHistoryInverseBound.scaled_history_inverse_norm_le
    (executableSystem119 source) (executableAlpha119 source)
    (source.historyParameters.taylorOrder + 3 : Nat) alpha_pos
    (normalization_bound source) historyNorm
  simpa only [executableHistoryInverseNorm119, FiniteKernelPolynomial.inverseBound,
    ExecutableC119, ExecutableLabels119, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat,
    add_left_comm, add_comm, add_assoc, show (1 : ℝ) + 3 = 4 by norm_num] using bounded

end QLean.Circuits.FiniteScientificSpectralBound
