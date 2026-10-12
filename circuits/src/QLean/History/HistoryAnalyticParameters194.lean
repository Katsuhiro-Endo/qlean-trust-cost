import Mathlib

set_option autoImplicit false

namespace HistoryAnalyticParameterExistence194

open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

structure HistoryAnalyticParameters194 where
  q : ℝ
  h : ℝ
  duration : ℝ
  stepSize : ℝ
  timeSteps : ℕ
  idlingSteps : ℕ
  idlingBlockSize : ℕ
  historyBlocks : ℕ
  selectorCount : ℕ
  selectorAngles : Fin selectorCount → ℝ
  coefficientAngles : ℕ → ℝ
  idleAngle : ℝ

structure HistoryAnalyticBaseDomain194
    (base : HistoryAnalyticParameters194) : Prop where
  hqh : |base.h * base.q| ≤ 1
  timeSteps_pos : 0 < base.timeSteps
  idlingSteps_pos : 0 < base.idlingSteps
  idlingBlockSize_pos : 0 < base.idlingBlockSize
  historyBlocks_pos : 0 < base.historyBlocks
  selectorCount_pos : 0 < base.selectorCount
  duration_step_relation :
    base.duration = base.stepSize * (base.timeSteps : ℝ)
  idling_divisibility :
    (base.idlingSteps + 1) % base.idlingBlockSize = 0
  history_block_relation :
    base.historyBlocks * base.idlingBlockSize = base.idlingSteps + 1
  selector_angles_pos : ∀ i, 0 < base.selectorAngles i
  coefficient_angles_pos : ∀ n, 0 < base.coefficientAngles n
  idle_angle_pos : 0 < base.idleAngle
  role_separation : ∀ (i : Fin base.selectorCount) (n : ℕ),
    base.coefficientAngles n ≠ base.selectorAngles i

end

end HistoryAnalyticParameterExistence194
