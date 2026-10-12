import Mathlib
import QLean.History.Jennings.PureSpec

noncomputable section

namespace PhaseScheduleProofs

open JenningsHistory

def phaseStepIsSignal125 : PhaseStep → Bool
  | .phase .. => false
  | .signal .. => true

def phaseBlock125 {n : Nat} (schedule : PhaseSchedule n) (k : Nat) : List PhaseStep :=
  let first : List PhaseStep :=
    [.phase (phaseRoleAtNat schedule k) (phaseAtNat schedule k)]
  if k + 1 < n then first ++ [.signal (alternatingDirection k)] else first

theorem phaseWord_source_order125 {n : Nat} (schedule : PhaseSchedule n) :
    phaseWord schedule = (List.range n).flatMap (phaseBlock125 schedule) := by
  rfl

theorem phaseBlock_signal_count125 {n : Nat}
    (schedule : PhaseSchedule n) (k : Nat) :
    ((phaseBlock125 schedule k).filter phaseStepIsSignal125).length =
      if k + 1 < n then 1 else 0 := by
  by_cases h : k + 1 < n <;> simp [phaseBlock125, phaseStepIsSignal125, h]

private theorem sum_const_one125 : ∀ m : Nat,
    (List.map (fun _ : Nat => 1) (List.range m)).sum = m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.sum_range_succ]
    omega

private theorem sum_signal_prefix125 : ∀ m : Nat,
    (List.map (fun k => if k + 1 < m then 1 else 0) (List.range m)).sum = m - 1 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.sum_range_succ]
    have hmap :
        List.map (fun k => if k + 1 < m + 1 then 1 else 0) (List.range m) =
          List.map (fun _ : Nat => 1) (List.range m) := by
      apply List.map_congr_left
      intro k hk
      have hkm : k < m := List.mem_range.mp hk
      simp [show k + 1 < m + 1 by omega]
    rw [hmap]
    have hlast : (if m + 1 < m + 1 then 1 else 0) = 0 := by simp
    rw [hlast, sum_const_one125]
    simp

private theorem filter_flatMap_signal125 {n : Nat}
    (schedule : PhaseSchedule n) (xs : List Nat) :
    ((xs.flatMap (phaseBlock125 schedule)).filter phaseStepIsSignal125) =
      xs.flatMap (fun k => (phaseBlock125 schedule k).filter phaseStepIsSignal125) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem phaseWord_signal_count125 {n : Nat} (schedule : PhaseSchedule n) :
    ((phaseWord schedule).filter phaseStepIsSignal125).length = n - 1 := by
  rw [phaseWord_source_order125, filter_flatMap_signal125, List.length_flatMap]
  simp_rw [phaseBlock_signal_count125]
  exact sum_signal_prefix125 n

end PhaseScheduleProofs
