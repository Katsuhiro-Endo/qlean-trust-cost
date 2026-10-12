import Mathlib

open scoped BigOperators
noncomputable section

namespace JenningsHistory

/-! This file is deliberately problem-mathematics-only.  It imports Mathlib
    and no circuit, compiler, recorded-gate, or canonical declaration. -/

abbrev C2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev V2 := Fin 2 → ℂ

inductive SignalDirection
  | forward
  | adjoint
  deriving DecidableEq, Repr

inductive PhaseRole
  | source
  | target
  deriving DecidableEq, Repr

inductive PhaseStep
  | phase (role : PhaseRole) (angle : ℝ)
  | signal (direction : SignalDirection)

structure PhaseSchedule (n : Nat) where
  phase : Fin n → ℝ
  role : Fin n → PhaseRole
  n_pos : 0 < n
  n_ge_two : 2 ≤ n
  nonzero_phase : ∃ i, phase i ≠ 0

def phaseAtNat {n : Nat} (schedule : PhaseSchedule n) (k : Nat) : ℝ :=
  schedule.phase ⟨k % n, Nat.mod_lt _ schedule.n_pos⟩

def phaseRoleAtNat {n : Nat} (schedule : PhaseSchedule n) (k : Nat) : PhaseRole :=
  schedule.role ⟨k % n, Nat.mod_lt _ schedule.n_pos⟩

def alternatingDirection (k : Nat) : SignalDirection :=
  if k % 2 = 0 then .forward else .adjoint

def sourceBasis : V2 := fun i => if i = 0 then 1 else 0

def phaseMatrix (role : PhaseRole) (angle : ℝ) : C2 := fun row column =>
  if row = column then
    match role with
    | .source => if row = 0 then Complex.exp (Complex.I * (angle : ℂ)) else 1
    | .target => if row = 1 then Complex.exp (Complex.I * (angle : ℂ)) else 1
  else 0

def signalSourceAmplitude (x : ℝ) : ℂ := (x : ℂ)

def signalTargetAmplitude (x : ℝ) : ℂ :=
  (Real.sqrt (max 0 (1 - x ^ 2)) : ℂ)

/-! This is the canonical real two-dimensional signal convention from the
    read-only QSP declaration: [[bad,-good],[good,bad]], with the adjoint
    direction written explicitly. -/
def signalMatrix (x : ℝ) (direction : SignalDirection) : C2 := fun row column =>
  let bad : ℂ := signalSourceAmplitude x
  let good : ℂ := signalTargetAmplitude x
  match direction, row.val, column.val with
  | .forward, 0, 0 => bad
  | .forward, 0, _ => -good
  | .forward, _, 0 => good
  | .forward, _, _ => bad
  | .adjoint, 0, 0 => bad
  | .adjoint, 0, _ => good
  | .adjoint, _, 0 => -good
  | .adjoint, _, _ => bad

def stepMatrix (x : ℝ) : PhaseStep → C2
  | .phase role angle => phaseMatrix role angle
  | .signal direction => signalMatrix x direction

def phaseWord {n : Nat} (schedule : PhaseSchedule n) : List PhaseStep :=
  (List.range n).flatMap fun k =>
    let first : List PhaseStep :=
      [.phase (phaseRoleAtNat schedule k) (phaseAtNat schedule k)]
    if k + 1 < n then first ++ [.signal (alternatingDirection k)] else first

def wordProduct (x : ℝ) (steps : List PhaseStep) : C2 :=
  steps.foldl (fun accumulated step => stepMatrix x step * accumulated) 1

def scheduleResponse {n : Nat} (schedule : PhaseSchedule n) (x : ℝ) : ℂ :=
  (wordProduct x (phaseWord schedule)).mulVec sourceBasis 0

/-! ## The exact Jennings/Dalzell problem system -/

structure HistoryIndex (d c R : Nat) where
  clock : Fin c
  order : Fin R
  state : Fin d
  deriving DecidableEq, Fintype

structure HistorySpec (d c r m R : Nat) where
  step : ℝ
  generator : Matrix (Fin d) (Fin d) ℝ
  initial : Fin d → ℝ
  order_lt : r < R
  physical_pos : 0 < m
  physical_lt : m < c

abbrev HistoryVector (d c R : Nat) := HistoryIndex d c R → ℝ
abbrev HistoryMatrix (d c R : Nat) :=
  Matrix (HistoryIndex d c R) (HistoryIndex d c R) ℝ

def stateIdentityEntry {d : Nat} (i j : Fin d) : ℝ :=
  if i = j then 1 else 0

def taylorDeltaEntry {d c r m R : Nat}
    (spec : HistorySpec d c r m R)
    (j j' : Fin R) (e e' : Fin d) : ℝ :=
  if j.val > 0 ∧ j'.val + 1 = j.val ∧ j.val ≤ r then
    -spec.step * spec.generator e e' / (j.val : ℝ)
  else 0

def idleDeltaEntry {d R : Nat}
    (j j' : Fin R) (e e' : Fin d) : ℝ :=
  if j.val > 0 ∧ j'.val + 1 = j.val then
    -stateIdentityEntry e e'
  else 0

def l0Entry {d c R : Nat}
    (row col : HistoryIndex d c R) : ℝ :=
  if row.clock = col.clock ∧ row.order = col.order ∧ row.state = col.state
  then 1 else 0

def l1Entry {d c r m R : Nat}
    (spec : HistorySpec d c r m R)
    (row col : HistoryIndex d c R) : ℝ :=
  if row.clock = col.clock then
    if row.clock.val < m then
      taylorDeltaEntry spec row.order col.order row.state col.state
    else
      idleDeltaEntry row.order col.order row.state col.state
  else 0

def l2Entry {d c r m R : Nat}
    (_spec : HistorySpec d c r m R)
    (row col : HistoryIndex d c R) : ℝ :=
  if row.clock.val = col.clock.val + 1 then
    if row.clock.val ≤ m then
      if row.order.val = 0 ∧ col.order.val ≤ r ∧ row.state = col.state
      then -1 else 0
    else
      if row.order.val = 0 ∧ col.order.val + 1 = R ∧ row.state = col.state
      then -1 else 0
  else 0

def historyMatrix {d c r m R : Nat}
    (spec : HistorySpec d c r m R) : HistoryMatrix d c R :=
  fun row col =>
    l0Entry row col + l1Entry spec row col + l2Entry spec row col

def historyRhs {d c r m R : Nat}
    (spec : HistorySpec d c r m R) : HistoryVector d c R :=
  fun row =>
    if row.clock.val = 0 ∧ row.order.val = 0 then spec.initial row.state else 0

def rhsNormSq {d c r m R : Nat}
    (spec : HistorySpec d c r m R) : ℝ :=
  ∑ row, historyRhs spec row * historyRhs spec row

def rhsNorm {d c r m R : Nat}
    (spec : HistorySpec d c r m R) : ℝ :=
  Real.sqrt (rhsNormSq spec)

def normalizedRhs {d c r m R : Nat}
    (spec : HistorySpec d c r m R) : HistoryVector d c R :=
  fun row => historyRhs spec row / rhsNorm spec

def scaledHistory {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha : ℝ) : HistoryMatrix d c R :=
  fun row col => historyMatrix system row col / alpha

abbrev ExtendedIndex (d c R : Nat) := Sum (HistoryIndex d c R) Unit
abbrev ExtendedMatrix (d c R : Nat) :=
  Matrix (ExtendedIndex d c R) (ExtendedIndex d c R) ℝ
abbrev ExtendedVector (d c R : Nat) := ExtendedIndex d c R → ℝ

def dalzellExtendedH {d c r m R : Nat}
    (system : HistorySpec d c r m R) (alpha ν : ℝ) : ExtendedMatrix d c R
  | Sum.inl row, Sum.inl col => scaledHistory system alpha row col
  | Sum.inr _, Sum.inr _ => ν⁻¹
  | _, _ => 0

def dalzellBPlus {d c r m R : Nat}
    (system : HistorySpec d c r m R) : ExtendedVector d c R
  | Sum.inl row => normalizedRhs system row / Real.sqrt 2
  | Sum.inr _ => 1 / Real.sqrt 2

def unitNormSquared {ι : Type*} [Fintype ι]
    (v : ι → ℝ) : ℝ := ∑ i, v i * v i

def unitNorm {ι : Type*} [Fintype ι]
    (v : ι → ℝ) : Prop := unitNormSquared v = 1

noncomputable def qBPlusMatrix {ι : Type*}
    (b : ι → ℝ) : Matrix ι ι ℝ := by
  classical
  exact fun i j => (if i = j then 1 else 0) - b i * b j

def linearApply {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℝ) (vector : ι → ℝ) : ι → ℝ :=
  matrix.mulVec vector

def wellPosed {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℝ) : Prop :=
  Function.Bijective (linearApply matrix)

def qBPlusApply {ι : Type*} [Fintype ι]
    (b z : ι → ℝ) : ι → ℝ :=
  (qBPlusMatrix b).mulVec z

lemma qBPlus_apply_formula {ι : Type*} [Fintype ι]
    (b z : ι → ℝ) :
    qBPlusApply b z = z - (∑ j, b j * z j) • b := by
  classical
  funext i
  simp only [qBPlusApply, qBPlusMatrix, Matrix.mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ j, ((if i = j then 1 else 0) - b i * b j) * z j) =
    z i - (∑ j, b j * z j) * b i
  have hdiag : (∑ j, (if i = j then 1 else 0) * z j) = z i := by
    simp
  calc
    (∑ j, ((if i = j then 1 else 0) - b i * b j) * z j) =
        ∑ j, ((if i = j then 1 else 0) * z j - (b i * b j) * z j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j, (if i = j then 1 else 0) * z j) -
        ∑ j, (b i * b j) * z j := by
      rw [Finset.sum_sub_distrib]
    _ = z i - b i * (∑ j, b j * z j) := by
      rw [hdiag]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = z i - (∑ j, b j * z j) * b i := by ring

lemma qBPlus_kernel_iff {ι : Type*} [Fintype ι]
    (b z : ι → ℝ) (hb : unitNorm b) :
    qBPlusApply b z = 0 ↔ ∃ c : ℝ, z = c • b := by
  rw [qBPlus_apply_formula]
  constructor
  · intro hz
    refine ⟨∑ j, b j * z j, ?_⟩
    funext i
    have hi := congrFun hz i
    have hi' : z i - (∑ j, b j * z j) * b i = 0 := by
      simpa [Pi.smul_apply, smul_eq_mul] using hi
    exact sub_eq_zero.mp hi'
  · rintro ⟨c, rfl⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    have hb' : (∑ j, b j * b j) = 1 := by
      simpa [unitNorm, unitNormSquared] using hb
    rw [show (∑ x, b x * (c * b x)) = c * (∑ x, b x * b x) by
      calc
        (∑ x, b x * (c * b x)) = ∑ x, c * (b x * b x) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = c * (∑ x, b x * b x) := by rw [Finset.mul_sum]]
    simp [hb']

noncomputable def uniqueSolution {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℝ) (hwell : wellPosed matrix)
    (rhs : ι → ℝ) : ι → ℝ :=
  Classical.choose (hwell.2 rhs)

lemma uniqueSolution_spec {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℝ) (hwell : wellPosed matrix)
    (rhs : ι → ℝ) :
    linearApply matrix (uniqueSolution matrix hwell rhs) = rhs := by
  exact Classical.choose_spec (hwell.2 rhs)

theorem g_kernel_member_iff {ι : Type*} [Fintype ι]
    (matrix : Matrix ι ι ℝ) (b : ι → ℝ)
    (hwell : wellPosed matrix) (hb : unitNorm b) (y : ι → ℝ) :
    linearApply (qBPlusMatrix b * matrix) y = 0 ↔
      ∃ c : ℝ, y = c • uniqueSolution matrix hwell b := by
  rw [show linearApply (qBPlusMatrix b * matrix) y =
      qBPlusApply b (linearApply matrix y) by
        simp [linearApply, qBPlusApply, Matrix.mulVec_mulVec]]
  constructor
  · intro hy
    rcases (qBPlus_kernel_iff b (linearApply matrix y) hb).mp hy with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply hwell.1
    calc
      linearApply matrix y = c • b := hc
      _ = c • linearApply matrix (uniqueSolution matrix hwell b) := by
        rw [uniqueSolution_spec matrix hwell b]
      _ = linearApply matrix (c • uniqueSolution matrix hwell b) := by
        simp [linearApply, Matrix.mulVec_smul]
  · rintro ⟨c, rfl⟩
    have happly : linearApply matrix (c • uniqueSolution matrix hwell b) =
        c • b := by
      rw [show linearApply matrix (c • uniqueSolution matrix hwell b) =
          c • linearApply matrix (uniqueSolution matrix hwell b) by
            simp [linearApply, Matrix.mulVec_smul]]
      rw [uniqueSolution_spec matrix hwell b]
    rw [happly]
    exact (qBPlus_kernel_iff b (c • b) hb).2 ⟨c, rfl⟩

/-! ## M13: kernel projector/reflection derived from the same Gν system -/

def kernelProjector {ι : Type*} [Fintype ι]
    (kernel : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => kernel i * kernel j / (∑ k, kernel k * kernel k)

def kernelReflection {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (kernel : ι → ℝ) : Matrix ι ι ℝ :=
  2 • kernelProjector kernel - (1 : Matrix ι ι ℝ)

def KernelMember {ι : Type*} (kernel y : ι → ℝ) : Prop :=
  ∃ c : ℝ, y = c • kernel

lemma kernelProjector_apply_formula {ι : Type*} [Fintype ι]
    (kernel y : ι → ℝ) :
    (kernelProjector kernel).mulVec y =
      ((∑ j, kernel j * y j) / (∑ j, kernel j * kernel j)) • kernel := by
  funext i
  simp only [kernelProjector, Matrix.mulVec, Pi.smul_apply, smul_eq_mul]
  let denominator : ℝ := ∑ k, kernel k * kernel k
  change (∑ j, (kernel i * kernel j / denominator) * y j) =
    (∑ j, kernel j * y j) / denominator * kernel i
  calc
    (∑ j, (kernel i * kernel j / denominator) * y j) =
        ∑ j, (kernel i / denominator) * (kernel j * y j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (kernel i / denominator) * (∑ j, kernel j * y j) := by
      rw [Finset.mul_sum]
    _ = (∑ j, kernel j * y j) / denominator * kernel i := by
      simp [div_eq_mul_inv]
      ring

theorem kernelProjector_member_iff {ι : Type*} [Fintype ι]
    (kernel y : ι → ℝ) (hkernel : unitNorm kernel) :
    (kernelProjector kernel).mulVec y = y ↔ KernelMember kernel y := by
  rw [kernelProjector_apply_formula]
  constructor
  · intro hy
    refine ⟨∑ j, kernel j * y j, ?_⟩
    funext i
    have hi := congrFun hy i
    have hn : (∑ k, kernel k * kernel k) = 1 := by
      simpa [unitNorm, unitNormSquared] using hkernel
    simpa [hn, Pi.smul_apply, smul_eq_mul] using hi.symm
  · rintro ⟨c, rfl⟩
    have hn : (∑ k, kernel k * kernel k) = 1 := by
      simpa [unitNorm, unitNormSquared] using hkernel
    have hsum : (∑ x, kernel x * (c * kernel x)) = c := by
      calc
        (∑ x, kernel x * (c * kernel x)) =
            c * (∑ x, kernel x * kernel x) := by
          calc
            (∑ x, kernel x * (c * kernel x)) =
                ∑ x, c * (kernel x * kernel x) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = c * (∑ x, kernel x * kernel x) := by rw [Finset.mul_sum]
        _ = c := by rw [hn]; ring
    funext i
    simp [Pi.smul_apply, smul_eq_mul, hsum, hn]

theorem kernelProjector_zero_iff {ι : Type*} [Fintype ι]
    (kernel y : ι → ℝ) (hkernel : unitNorm kernel) :
    (kernelProjector kernel).mulVec y = 0 ↔
      (∑ j, kernel j * y j) = 0 := by
  rw [kernelProjector_apply_formula]
  have hn : (∑ k, kernel k * kernel k) = 1 := by
    simpa [unitNorm, unitNormSquared] using hkernel
  constructor
  · intro h
    have hdot := congrArg (fun v => ∑ i, kernel i * v i) h
    have hdot' :
        ((∑ j, kernel j * y j) /
          (∑ k, kernel k * kernel k)) *
          (∑ i, kernel i * kernel i) = 0 := by
      calc
        ((∑ j, kernel j * y j) /
            (∑ k, kernel k * kernel k)) *
            (∑ i, kernel i * kernel i) =
            ∑ i, kernel i *
              (((∑ j, kernel j * y j) /
                (∑ k, kernel k * kernel k)) * kernel i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = 0 := by
          simpa [Pi.smul_apply, smul_eq_mul] using hdot
    simpa [hn] using hdot'
  · intro h
    simp [hn, h]

/-! M12 block/layout fixtures and a dimension-three M13 witness. -/

end JenningsHistory
