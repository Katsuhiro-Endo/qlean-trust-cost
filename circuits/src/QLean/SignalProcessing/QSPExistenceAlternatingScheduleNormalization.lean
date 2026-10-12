import QLean.SignalProcessing.QSPExistenceQSPPlanAssembly
import Mathlib
import QLean.History.Jennings.PureSpec
import QLean.SignalProcessing.PhaseScheduleProofsPhaseWordContract
import QLean.SignalProcessing.PhaseScheduleProofsChebyshevContract

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore
open JenningsHistory

noncomputable section

/-! CircuitCore local gauge normalisation.  The raw PhaseScheduleProofs record remains
    proof-free; all evaluator claims are stated separately below. -/

def phaseScheduleProofsRoleToFixed037 : PhaseRole → FixedPointProjectorRole
  | .source => .source
  | .target => .target

def phaseScheduleProofsDirectionToFixed037 : JenningsHistory.SignalDirection →
    VerifiedCircuitCore.SignalDirection
  | .forward => .forward
  | .adjoint => .adjoint

def phaseScheduleProofsStepToFixed037 : PhaseStep → FixedPointRoleAwarePhaseStep
  | .phase role angle =>
      .projectorPhase (phaseScheduleProofsRoleToFixed037 role) angle
  | .signal direction => .signal (phaseScheduleProofsDirectionToFixed037 direction)

def phaseScheduleProofsWordToFixed037 (steps : List PhaseStep) :
    List FixedPointRoleAwarePhaseStep := steps.map phaseScheduleProofsStepToFixed037

def gaugeZ037 : FixedPointTransferMatrix := fun row column =>
  if row ≠ column then 0
  else if row = fixedPointSourceIndex then 1 else -1

def alternatingAnglesWord037Aux : Nat → List ℝ → List PhaseStep
  | _, [] => []
  | index, angle :: rest =>
      [.phase (if index % 2 = 0 then .source else .target) angle] ++
        (if rest.isEmpty then [] else [.signal (alternatingDirection index)]) ++
        alternatingAnglesWord037Aux (index + 1) rest

def alternatingAnglesWord037 (angles : List ℝ) : List PhaseStep :=
  alternatingAnglesWord037Aux 0 angles

end
end SpectralSamplingProof.Analytic

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore
open JenningsHistory

noncomputable section

theorem fixedPointSourceAmplitude_one_sub_sq037
    {x : ℝ} (hx0 : 0 ≤ x) :
    fixedPointSourceAmplitude (1 - x ^ 2) = x := by
  simp only [fixedPointSourceAmplitude]
  rw [show 1 - (1 - x ^ 2) = x ^ 2 by ring]
  rw [max_eq_right (sq_nonneg x), Real.sqrt_sq_eq_abs, abs_of_nonneg hx0]

theorem phaseScheduleProofsSignalMatrix_matches_fixed037
    {x : ℝ} (hx0 : 0 ≤ x) (_hx1 : x ≤ 1)
    (direction : JenningsHistory.SignalDirection) :
    signalMatrix x direction =
      fixedPointSignalTransferMatrix (1 - x ^ 2)
        (phaseScheduleProofsDirectionToFixed037 direction) := by
  have hbad : fixedPointSourceAmplitude (1 - x ^ 2) = x :=
    fixedPointSourceAmplitude_one_sub_sq037 hx0
  ext row column
  fin_cases row <;> fin_cases column <;> cases direction <;>
      simp [JenningsHistory.signalMatrix, fixedPointSignalTransferMatrix,
      signalSourceAmplitude, signalTargetAmplitude,
      fixedPointTargetAmplitude,
      phaseScheduleProofsDirectionToFixed037, hbad]

theorem phaseScheduleProofsPhaseMatrix_matches_fixed037
    (role : PhaseRole) (angle : ℝ) :
    phaseMatrix role angle =
      fixedPointProjectorTransferMatrix (phaseScheduleProofsRoleToFixed037 role) angle := by
  ext row column
  fin_cases row <;> fin_cases column <;> cases role <;>
    simp [JenningsHistory.phaseMatrix, fixedPointProjectorTransferMatrix,
      phaseScheduleProofsRoleToFixed037, fixedPointSourceIndex, fixedPointTargetIndex]

theorem phaseScheduleProofsStepMatrix_matches_fixed037
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (step : PhaseStep) :
    stepMatrix x step =
      fixedPointRoleAwareStepTransferMatrix (1 - x ^ 2)
        (phaseScheduleProofsStepToFixed037 step) := by
  cases step with
  | phase role angle =>
      exact phaseScheduleProofsPhaseMatrix_matches_fixed037 role angle
  | signal direction =>
      exact phaseScheduleProofsSignalMatrix_matches_fixed037 hx0 hx1 direction

theorem phaseScheduleProofsWordProduct_matches_fixed037
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (steps : List PhaseStep) :
    wordProduct x steps =
      fixedPointSourceOrderTransferMatrix (1 - x ^ 2)
        (phaseScheduleProofsWordToFixed037 steps) := by
  have hfold : ∀ (xs : List PhaseStep) (acc : FixedPointTransferMatrix),
      List.foldl (fun accumulated step =>
          stepMatrix x step * accumulated) acc xs =
        List.foldl (fun accumulated step =>
          fixedPointRoleAwareStepTransferMatrix (1 - x ^ 2) step *
            accumulated) acc (phaseScheduleProofsWordToFixed037 xs) := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons first rest ih =>
        intro acc
        simp only [phaseScheduleProofsWordToFixed037, List.map_cons, List.foldl]
        rw [phaseScheduleProofsStepMatrix_matches_fixed037 hx0 hx1 first]
        exact ih _
  exact hfold steps 1

end
end SpectralSamplingProof.Analytic

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore
open JenningsHistory

noncomputable section

def canonicalSourceWord037 : List ℝ → List FixedPointRoleAwarePhaseStep
  | [] => []
  | [angle] => [.projectorPhase .source angle]
  | angle :: rest =>
      [.projectorPhase .source angle, .signal .forward] ++
        canonicalSourceWord037 rest

theorem gaugeZ_mul_self037 : gaugeZ037 * gaugeZ037 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [gaugeZ037, fixedPointSourceIndex,
      Matrix.mul_apply]

theorem gaugeZ_conjugates_forward037 (p : ℝ) :
    gaugeZ037 * fixedPointSignalTransferMatrix p .forward * gaugeZ037 =
      fixedPointSignalTransferMatrix p .adjoint := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [gaugeZ037, fixedPointSignalTransferMatrix,
      fixedPointSourceIndex, Matrix.mul_apply]

theorem gaugeZ_commutes_projector037
    (role : FixedPointProjectorRole) (angle : ℝ) :
    gaugeZ037 * fixedPointProjectorTransferMatrix role angle =
      fixedPointProjectorTransferMatrix role angle * gaugeZ037 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [gaugeZ037, fixedPointProjectorTransferMatrix,
      fixedPointSourceIndex, fixedPointTargetIndex, Matrix.mul_apply]

theorem target_projector_as_source037 (angle : ℝ) :
    fixedPointProjectorTransferMatrix .target angle =
      Complex.exp (Complex.I * (angle : ℂ)) •
        fixedPointProjectorTransferMatrix .source (-angle) := by
  have hcancel' :
      Complex.exp (Complex.I * (angle : ℂ)) *
          Complex.exp (-(Complex.I * (angle : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    rw [show Complex.I * (angle : ℂ) +
        -(Complex.I * (angle : ℂ)) = 0 by ring, Complex.exp_zero]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [fixedPointProjectorTransferMatrix,
      fixedPointSourceIndex, fixedPointTargetIndex, hcancel']

theorem gaugeZ_mul_source_phase037 (angle : ℝ) :
    gaugeZ037 * fixedPointProjectorTransferMatrix .source angle =
      (-1 : ℂ) • fixedPointProjectorTransferMatrix .source
        (angle + Real.pi) := by
  have hshift : Complex.exp (Complex.I *
      ((angle : ℂ) + (Real.pi : ℂ))) =
      -Complex.exp (Complex.I * (angle : ℂ)) := by
    have hdecomp : Complex.I * ((angle : ℂ) + (Real.pi : ℂ)) =
        Complex.I * (angle : ℂ) + (Real.pi : ℂ) * Complex.I := by ring
    rw [hdecomp, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [gaugeZ037, fixedPointProjectorTransferMatrix,
      fixedPointSourceIndex, Matrix.mul_apply,
      hshift]

theorem source_phase_mul_gaugeZ037 (angle : ℝ) :
    fixedPointProjectorTransferMatrix .source angle * gaugeZ037 =
      (-1 : ℂ) • fixedPointProjectorTransferMatrix .source
        (angle + Real.pi) := by
  rw [← gaugeZ_commutes_projector037 .source angle]
  exact gaugeZ_mul_source_phase037 angle

theorem gauge_two_source037
    (a b : ℝ) (left right : FixedPointTransferMatrix) :
    fixedPointProjectorTransferMatrix .source a *
        (gaugeZ037 *
          (left *
            (gaugeZ037 *
              (fixedPointProjectorTransferMatrix .source b * right)))) =
      fixedPointProjectorTransferMatrix .source (a + Real.pi) *
        (left *
          (fixedPointProjectorTransferMatrix .source (b + Real.pi) * right)) := by
  calc
    fixedPointProjectorTransferMatrix .source a *
        (gaugeZ037 *
          (left *
            (gaugeZ037 *
              (fixedPointProjectorTransferMatrix .source b * right)))) =
      (fixedPointProjectorTransferMatrix .source a * gaugeZ037) *
        (left *
          (gaugeZ037 *
            (fixedPointProjectorTransferMatrix .source b * right))) := by
          rw [Matrix.mul_assoc]
    _ = ((-1 : ℂ) •
        fixedPointProjectorTransferMatrix .source (a + Real.pi)) *
        (left *
          (gaugeZ037 *
            (fixedPointProjectorTransferMatrix .source b * right))) := by
          rw [source_phase_mul_gaugeZ037]
    _ = (-1 : ℂ) •
        (fixedPointProjectorTransferMatrix .source (a + Real.pi) *
          (left *
            (gaugeZ037 *
              (fixedPointProjectorTransferMatrix .source b * right)))) := by
          rw [smul_mul_assoc]
    _ = (-1 : ℂ) •
        (fixedPointProjectorTransferMatrix .source (a + Real.pi) *
          (left *
            ((gaugeZ037 *
              fixedPointProjectorTransferMatrix .source b) * right))) := by
          congr 2
          rw [Matrix.mul_assoc]
    _ = (-1 : ℂ) •
        (fixedPointProjectorTransferMatrix .source (a + Real.pi) *
          (left *
            (((-1 : ℂ) •
              fixedPointProjectorTransferMatrix .source (b + Real.pi)) * right))) := by
          rw [gaugeZ_mul_source_phase037]
    _ = fixedPointProjectorTransferMatrix .source (a + Real.pi) *
        (left *
          (fixedPointProjectorTransferMatrix .source (b + Real.pi) * right)) := by
          simp

theorem gauge_two_source_smul037
    (a b : ℝ) (scalar : ℂ) (left right : FixedPointTransferMatrix) :
    fixedPointProjectorTransferMatrix .source a *
        (gaugeZ037 *
          (left *
            (gaugeZ037 *
              ((scalar • fixedPointProjectorTransferMatrix .source b) *
                right)))) =
      scalar •
        (fixedPointProjectorTransferMatrix .source (a + Real.pi) *
          (left *
            (fixedPointProjectorTransferMatrix .source (b + Real.pi) *
              right))) := by
  calc
    fixedPointProjectorTransferMatrix .source a *
        (gaugeZ037 *
          (left *
            (gaugeZ037 *
              ((scalar • fixedPointProjectorTransferMatrix .source b) *
                right)))) =
      fixedPointProjectorTransferMatrix .source a *
        (gaugeZ037 *
          (left *
            (gaugeZ037 *
              (scalar •
                (fixedPointProjectorTransferMatrix .source b * right))))) := by
          rw [smul_mul_assoc]
    _ = scalar •
        (fixedPointProjectorTransferMatrix .source a *
          (gaugeZ037 *
            (left *
              (gaugeZ037 *
                (fixedPointProjectorTransferMatrix .source b * right))))) := by
          simp only [mul_smul_comm]
    _ = scalar •
        (fixedPointProjectorTransferMatrix .source (a + Real.pi) *
          (left *
            (fixedPointProjectorTransferMatrix .source (b + Real.pi) *
              right))) := by
          rw [gauge_two_source037]

theorem gauge_two_source_smul_left037
    (a b : ℝ) (scalar : ℂ) (left right : FixedPointTransferMatrix) :
    fixedPointProjectorTransferMatrix .source a *
        ((gaugeZ037 * left * gaugeZ037) *
          ((scalar • fixedPointProjectorTransferMatrix .source b) * right)) =
      scalar •
        (fixedPointProjectorTransferMatrix .source (a + Real.pi) *
          (left *
            (fixedPointProjectorTransferMatrix .source (b + Real.pi) *
              right))) := by
  simpa only [Matrix.mul_assoc] using
    gauge_two_source_smul037 a b scalar left right

def alternatingFixedWord037 (angles : List ℝ) :
    List FixedPointRoleAwarePhaseStep :=
  phaseScheduleProofsWordToFixed037 (alternatingAnglesWord037 angles)

theorem alternatingFixedWord037_q1 (a0 a1 : ℝ) :
    alternatingFixedWord037 [a0, a1] =
      [.projectorPhase .source a0, .signal .forward,
        .projectorPhase .target a1] := by
  rfl

theorem alternatingFixedWord037_q2 (a0 a1 a2 : ℝ) :
    alternatingFixedWord037 [a0, a1, a2] =
      [.projectorPhase .source a0, .signal .forward,
        .projectorPhase .target a1, .signal .adjoint,
        .projectorPhase .source a2] := by
  rfl

theorem alternating_q1_matrix_gauge037
    (p a0 a1 : ℝ) :
    fixedPointSourceOrderTransferMatrix p
        (alternatingFixedWord037 [a0, a1]) =
      Complex.exp (Complex.I * (a1 : ℂ)) •
        fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037 [a0, -a1]) := by
  rw [alternatingFixedWord037_q1]
  simp [fixedPointSourceOrderTransferMatrix,
    fixedPointRoleAwareStepTransferMatrix, canonicalSourceWord037,
    target_projector_as_source037]

theorem alternating_q2_matrix_gauge037
    (p a0 a1 a2 : ℝ) :
    fixedPointSourceOrderTransferMatrix p
        (alternatingFixedWord037 [a0, a1, a2]) =
      Complex.exp (Complex.I * (a1 : ℂ)) •
        fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037 [a0, -a1 + Real.pi, a2 + Real.pi]) := by
  rw [alternatingFixedWord037_q2]
  simp only [fixedPointSourceOrderTransferMatrix, canonicalSourceWord037,
    fixedPointRoleAwareStepTransferMatrix, List.foldl, List.foldl_append]
  rw [target_projector_as_source037 a1]
  rw [← gaugeZ_conjugates_forward037 p]
  simp only [mul_one]
  simpa only [Matrix.mul_assoc] using gauge_two_source_smul037 a2 (-a1)
    (Complex.exp (Complex.I * (a1 : ℂ)))
    (fixedPointSignalTransferMatrix p .forward)
    (fixedPointSignalTransferMatrix p .forward *
      fixedPointProjectorTransferMatrix .source a0)

end
end SpectralSamplingProof.Analytic

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore
open JenningsHistory

noncomputable section

def phaseLift037 (angle : ℝ) : ℝ :=
  if angle = 0 then 2 * Real.pi else angle

theorem phaseLift037_ne_zero (angle : ℝ) : phaseLift037 angle ≠ 0 := by
  by_cases h : angle = 0
  · simp [phaseLift037, h, Real.pi_ne_zero]
  · simp [phaseLift037, h]

theorem phaseMatrix_phaseLift037 (role : PhaseRole) (angle : ℝ) :
    phaseMatrix role (phaseLift037 angle) = phaseMatrix role angle := by
  by_cases h : angle = 0
  · subst angle
    have h_exp : Complex.exp (Complex.I * (2 * (Real.pi : ℂ))) = 1 := by
      rw [show Complex.I * (2 * (Real.pi : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I by ring,
        Complex.exp_two_pi_mul_I]
    ext row column
    fin_cases row <;> fin_cases column <;> cases role <;>
      simp [phaseMatrix, phaseLift037, h_exp]
  · simp [phaseLift037, h]

def liftFirstAngles037 : List ℝ → List ℝ
  | [] => []
  | angle :: rest => phaseLift037 angle :: rest

theorem liftFirstAngles037_length (angles : List ℝ) :
    (liftFirstAngles037 angles).length = angles.length := by
  cases angles <;> rfl

def phaseScheduleOfAngles037 (angles : List ℝ)
    (h2 : 2 ≤ angles.length) : PhaseSchedule angles.length where
  phase := fun i => (liftFirstAngles037 angles).getD i.val 0
  role := fun i => if i.val % 2 = 0 then .source else .target
  n_pos := by omega
  n_ge_two := h2
  nonzero_phase := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    cases angles with
    | nil => simp at h2
    | cons angle rest =>
        simp [liftFirstAngles037]
        exact phaseLift037_ne_zero angle

def alternatingBlock037 (start n k : Nat) (angleAt : Nat → ℝ) :
    List PhaseStep :=
  [.phase (if (start + k) % 2 = 0 then .source else .target)
      (angleAt k)] ++
    (if k + 1 < n then [.signal (alternatingDirection (start + k))] else [])

def alternatingRangeWord037 (start n : Nat) (angleAt : Nat → ℝ) :
    List PhaseStep :=
  (List.range n).flatMap (fun k => alternatingBlock037 start n k angleAt)

def alternatingRangeRec037 : Nat → Nat → (Nat → ℝ) → List PhaseStep
  | _, 0, _ => []
  | start, n + 1, angleAt =>
      [.phase (if start % 2 = 0 then .source else .target) (angleAt 0)] ++
        (if n = 0 then [] else [.signal (alternatingDirection start)]) ++
        alternatingRangeRec037 (start + 1) n (fun k => angleAt (k + 1))

theorem flatMap_map_succ037 {α : Type} (xs : List Nat) (f : Nat → List α) :
    (xs.map Nat.succ).flatMap f = xs.flatMap (fun k => f (k + 1)) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      simp [List.flatMap, Function.comp_def, Nat.succ_eq_add_one]

theorem alternatingBlock_succ037
    (start n k : Nat) (angleAt : Nat → ℝ) :
    alternatingBlock037 start (n + 1) (k + 1) angleAt =
      alternatingBlock037 (start + 1) n k (fun j => angleAt (j + 1)) := by
  by_cases hkn : k + 1 < n
  · have hindex : start + (k + 1) = start + 1 + k := by omega
    simp only [alternatingBlock037]
    rw [hindex]
    simp [hkn]
  · have hkn' : k + 1 + 1 < n + 1 ↔ k + 1 < n := by omega
    have hindex : start + (k + 1) = start + 1 + k := by omega
    simp only [alternatingBlock037]
    rw [hindex]
    simp [hkn, hkn']

theorem alternatingRangeWord_eq_rec037 :
    ∀ (start n : Nat) (angleAt : Nat → ℝ),
      alternatingRangeWord037 start n angleAt =
        alternatingRangeRec037 start n angleAt := by
  intro start n
  induction n generalizing start with
  | zero => intro angleAt; rfl
  | succ n ih =>
      intro angleAt
      rw [alternatingRangeWord037, List.range_succ_eq_map,
        List.flatMap_cons, flatMap_map_succ037]
      by_cases hn : n = 0
      · subst n
        simp [alternatingBlock037, alternatingRangeRec037]
      · have htail := ih (start + 1) (fun k => angleAt (k + 1))
        have hblocks :
            (List.range n).flatMap
                (fun k => alternatingBlock037 start (n + 1) (k + 1) angleAt) =
              alternatingRangeWord037 (start + 1) n
                (fun k => angleAt (k + 1)) := by
          rw [alternatingRangeWord037]
          apply List.flatMap_congr
          intro k hk
          exact alternatingBlock_succ037 start n k angleAt
        rw [hblocks, htail]
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        simp [alternatingBlock037, alternatingRangeRec037, hn, hnpos]

theorem alternatingAux_eq_rec037 :
    ∀ (start : Nat) (angles : List ℝ),
      alternatingAnglesWord037Aux start angles =
        alternatingRangeRec037 start angles.length
          (fun k => angles.getD k 0) := by
  intro start angles
  induction angles generalizing start with
  | nil => rfl
  | cons angle rest ih =>
      cases rest with
      | nil =>
          simp [alternatingAnglesWord037Aux, alternatingRangeRec037]
      | cons next tail =>
          rw [alternatingAnglesWord037Aux, alternatingRangeRec037.eq_def]
          simp only [List.length_cons]
          have htail := ih (start + 1)
          have hget :
              (fun k => (angle :: next :: tail).getD (k + 1) 0) =
                (fun k => (next :: tail).getD k 0) := by
            funext k
            cases k <;> simp [List.getD]
          rw [hget, htail]
          simp [List.getD]

theorem alternatingAnglesWord037_eq_range037 (angles : List ℝ) :
    alternatingAnglesWord037 angles =
      alternatingRangeWord037 0 angles.length
        (fun k => angles.getD k 0) := by
  rw [alternatingAnglesWord037, alternatingAux_eq_rec037]
  exact (alternatingRangeWord_eq_rec037 0 angles.length
    (fun k => angles.getD k 0)).symm

theorem phaseAtNat_scheduleOfAngles037
    (angles : List ℝ) (h2 : 2 ≤ angles.length) (k : Nat)
    (hk : k < angles.length) :
    phaseAtNat (phaseScheduleOfAngles037 angles h2) k =
      (liftFirstAngles037 angles).getD k 0 := by
  have hmod : k % angles.length = k := Nat.mod_eq_of_lt hk
  simp [phaseAtNat, phaseScheduleOfAngles037, hmod]

theorem phaseRoleAtNat_scheduleOfAngles037
    (angles : List ℝ) (h2 : 2 ≤ angles.length) (k : Nat)
    (hk : k < angles.length) :
    phaseRoleAtNat (phaseScheduleOfAngles037 angles h2) k =
      (if k % 2 = 0 then .source else .target) := by
  have hmod : k % angles.length = k := Nat.mod_eq_of_lt hk
  simp [phaseRoleAtNat, phaseScheduleOfAngles037, hmod]

theorem phaseBlock_scheduleOfAngles037
    (angles : List ℝ) (h2 : 2 ≤ angles.length) (k : Nat)
    (hk : k < angles.length) :
    PhaseScheduleProofs.phaseBlock125 (phaseScheduleOfAngles037 angles h2) k =
      alternatingBlock037 0 angles.length k
        (fun j => (liftFirstAngles037 angles).getD j 0) := by
  have hphase := phaseAtNat_scheduleOfAngles037 angles h2 k hk
  have hrole := phaseRoleAtNat_scheduleOfAngles037 angles h2 k hk
  simp only [PhaseScheduleProofs.phaseBlock125, alternatingBlock037]
  rw [hphase, hrole]
  simp only [Nat.zero_add]
  by_cases hnext : k + 1 < angles.length <;> simp [hnext]

theorem phaseWord_scheduleOfAngles_eq_range037
    (angles : List ℝ) (h2 : 2 ≤ angles.length) :
    phaseWord (phaseScheduleOfAngles037 angles h2) =
      alternatingRangeWord037 0 angles.length
        (fun j => (liftFirstAngles037 angles).getD j 0) := by
  rw [PhaseScheduleProofs.phaseWord_source_order125, alternatingRangeWord037]
  apply List.flatMap_congr
  intro k hk
  exact phaseBlock_scheduleOfAngles037 angles h2 k (by
    exact List.mem_range.mp hk)

theorem phaseWord_scheduleOfAngles_eq_alternating037
    (angles : List ℝ) (h2 : 2 ≤ angles.length) :
    phaseWord (phaseScheduleOfAngles037 angles h2) =
      alternatingAnglesWord037 (liftFirstAngles037 angles) := by
  rw [phaseWord_scheduleOfAngles_eq_range037 angles h2,
    alternatingAnglesWord037_eq_range037,
    liftFirstAngles037_length]

theorem phaseWord_scheduleToFixedSteps_eq037
    (angles : List ℝ) (h2 : 2 ≤ angles.length) :
    phaseScheduleProofsWordToFixed037
        (phaseWord (phaseScheduleOfAngles037 angles h2)) =
      alternatingFixedWord037 (liftFirstAngles037 angles) := by
  rw [phaseWord_scheduleOfAngles_eq_alternating037 angles h2]
  rfl

theorem phaseWord_schedule_matrix_eq_alternating037
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (angles : List ℝ) (h2 : 2 ≤ angles.length) :
    wordProduct x (phaseWord (phaseScheduleOfAngles037 angles h2)) =
      fixedPointSourceOrderTransferMatrix (1 - x ^ 2)
        (alternatingFixedWord037 (liftFirstAngles037 angles)) := by
  rw [phaseScheduleProofsWordProduct_matches_fixed037 hx0 hx1,
    phaseWord_scheduleToFixedSteps_eq037 angles h2]

def gaugeCanonicalAngle037 (n j : Nat) (a : ℝ) : ℝ :=
  if j = 0 then a else
    if j + 1 < n then
      if j % 2 = 0 then a + Real.pi else -a + Real.pi
    else if j % 2 = 0 then a + Real.pi else -a

def gaugeCanonicalAnglesAux037 : Nat → Nat → List ℝ → List ℝ
  | _, _, [] => []
  | n, j, a :: rest =>
      gaugeCanonicalAngle037 n j a ::
        gaugeCanonicalAnglesAux037 n (j + 1) rest

def gaugeCanonicalAngles037 (angles : List ℝ) : List ℝ :=
  gaugeCanonicalAnglesAux037 angles.length 0 angles

def oddAngleSumAux037 : Nat → List ℝ → ℝ
  | _, [] => 0
  | j, a :: rest =>
      (if j % 2 = 1 then a else 0) + oddAngleSumAux037 (j + 1) rest

def oddAngleSum037 (angles : List ℝ) : ℝ := oddAngleSumAux037 0 angles

theorem canonicalSourceWord037_append_single
    (angles : List ℝ) (hangles : angles ≠ []) (angle : ℝ) :
    canonicalSourceWord037 (angles ++ [angle]) =
      canonicalSourceWord037 angles ++
        [.signal .forward, .projectorPhase .source angle] := by
  induction angles with
  | nil => simp_all
  | cons head tail ih =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [canonicalSourceWord037, List.cons_append,
            List.nil_append]
          exact congrArg (fun tail =>
            [FixedPointRoleAwarePhaseStep.projectorPhase
                FixedPointProjectorRole.source head,
              .signal .forward] ++ tail) (ih (by simp))

theorem alternatingAux_append_single037 :
    ∀ (start : Nat) (angles : List ℝ), angles ≠ [] → (angle : ℝ) →
      alternatingAnglesWord037Aux start (angles ++ [angle]) =
        alternatingAnglesWord037Aux start angles ++
          [.signal (alternatingDirection (start + angles.length - 1)),
            .phase
              (if (start + angles.length) % 2 = 0 then .source else .target)
              angle] := by
  intro start angles
  induction angles generalizing start with
  | nil => intro h; simp_all
  | cons head tail ih =>
      intro hangle angle
      cases tail with
      | nil =>
          simp [alternatingAnglesWord037Aux, alternatingDirection]
      | cons next rest =>
          change
            ([PhaseStep.phase
                (if start % 2 = 0 then .source else .target) head] ++
              (if (next :: (rest ++ [angle])).isEmpty = true then []
               else [PhaseStep.signal (alternatingDirection start)]) ++
              alternatingAnglesWord037Aux (start + 1)
                (next :: (rest ++ [angle]))) =
            (([PhaseStep.phase
                (if start % 2 = 0 then .source else .target) head] ++
              (if (next :: rest).isEmpty = true then []
               else [PhaseStep.signal (alternatingDirection start)]) ++
              alternatingAnglesWord037Aux (start + 1) (next :: rest)) ++
              [PhaseStep.signal
                  (alternatingDirection (start + (head :: next :: rest).length - 1)),
                PhaseStep.phase
                  (if (start + (head :: next :: rest).length) % 2 = 0
                   then .source else .target) angle])
          have htail := ih (start + 1) (by simp) angle
          have htail' :
              alternatingAnglesWord037Aux (start + 1)
                  (next :: (rest ++ [angle])) =
                alternatingAnglesWord037Aux (start + 1) (next :: rest) ++
                  [PhaseStep.signal
                      (alternatingDirection
                        (start + (head :: next :: rest).length - 1)),
                    PhaseStep.phase
                      (if (start + (head :: next :: rest).length) % 2 = 0
                       then .source else .target) angle] := by
            have hlen :
                start + (rest.length + 1 + 1) =
                  start + 1 + (rest.length + 1) := by omega
            convert htail using 1 <;>
              simp only [List.cons_append, List.length_cons]
            all_goals simp [hlen]
          rw [htail']
          simp [alternatingDirection]

theorem alternatingAnglesWord037_append_single
    (angles : List ℝ) (hangles : angles ≠ []) (angle : ℝ) :
    alternatingAnglesWord037 (angles ++ [angle]) =
      alternatingAnglesWord037 angles ++
        [.signal (alternatingDirection (angles.length - 1)),
          .phase (if angles.length % 2 = 0 then .source else .target) angle] := by
  change alternatingAnglesWord037Aux 0 (angles ++ [angle]) = _
  rw [alternatingAux_append_single037 0 angles hangles angle]
  simp only [alternatingAnglesWord037, Nat.zero_add]

theorem alternatingFixedWord037_append_single
    (angles : List ℝ) (hangles : angles ≠ []) (angle : ℝ) :
    alternatingFixedWord037 (angles ++ [angle]) =
      alternatingFixedWord037 angles ++
        [.signal (phaseScheduleProofsDirectionToFixed037
            (alternatingDirection (angles.length - 1))),
          .projectorPhase
            (phaseScheduleProofsRoleToFixed037
              (if angles.length % 2 = 0 then .source else .target)) angle] := by
  rw [alternatingFixedWord037, alternatingAnglesWord037_append_single
    angles hangles angle]
  simp only [phaseScheduleProofsWordToFixed037, List.map_append, List.map_cons,
    List.map_nil]
  rfl

theorem gaugeAux_append_single_of_odd037 :
    ∀ (start : Nat) (angles : List ℝ),
      (start + angles.length) % 2 = 1 → (angle : ℝ) →
      gaugeCanonicalAnglesAux037 (start + angles.length + 1) start
          (angles ++ [angle]) =
        gaugeCanonicalAnglesAux037 (start + angles.length) start angles ++
          [gaugeCanonicalAngle037 (start + angles.length + 1)
            (start + angles.length) angle] := by
  intro start angles
  induction angles generalizing start with
  | nil =>
      intro h angle
      simp [gaugeCanonicalAnglesAux037, gaugeCanonicalAngle037]
  | cons head tail ih =>
      intro h angle
      cases tail with
      | nil =>
          simp [gaugeCanonicalAnglesAux037, gaugeCanonicalAngle037] at h ⊢
          have hsmod : start % 2 = 0 := by omega
          simp [hsmod]
      | cons next rest =>
          change
            ([gaugeCanonicalAngle037
                (start + (head :: next :: rest).length + 1) start head] ++
              gaugeCanonicalAnglesAux037
                (start + (head :: next :: rest).length + 1) (start + 1)
                (next :: (rest ++ [angle]))) =
            (([gaugeCanonicalAngle037
                (start + (head :: next :: rest).length) start head] ++
              gaugeCanonicalAnglesAux037
                (start + (head :: next :: rest).length) (start + 1)
                (next :: rest)) ++
              [gaugeCanonicalAngle037
                (start + (head :: next :: rest).length + 1)
                  (start + (head :: next :: rest).length) angle])
          have htail :
              (start + 1 + (next :: rest).length) % 2 = 1 := by
            convert h using 1
            simp only [List.length_cons]
            omega
          have hrec := ih (start + 1) htail angle
          have hrec' :
              gaugeCanonicalAnglesAux037
                  (start + (head :: next :: rest).length + 1) (start + 1)
                  (next :: (rest ++ [angle])) =
                gaugeCanonicalAnglesAux037
                  (start + (head :: next :: rest).length) (start + 1)
                  (next :: rest) ++
                  [gaugeCanonicalAngle037
                    (start + (head :: next :: rest).length + 1)
                      (start + (head :: next :: rest).length) angle] := by
            have htotal1 :
                start + (head :: next :: rest).length + 1 =
                  start + 1 + (next :: rest).length + 1 := by
              simp only [List.length_cons]
              omega
            have htotal0 :
                start + (head :: next :: rest).length =
                  start + 1 + (next :: rest).length := by
              simp only [List.length_cons]
              omega
            rw [htotal1, htotal0]
            simpa only [List.cons_append] using hrec
          rw [hrec']
          have hhead :
              gaugeCanonicalAngle037
                  (start + (head :: next :: rest).length + 1) start head =
                gaugeCanonicalAngle037
                  (start + (head :: next :: rest).length) start head := by
            by_cases hs : start = 0
            · simp [gaugeCanonicalAngle037, hs]
            · by_cases hlen : (next :: rest).length = 0
              · have : False := by
                  simp only [List.length_cons] at hlen
                  omega
                contradiction
              · simp [gaugeCanonicalAngle037, hs]
          rw [hhead]
          simp

theorem gaugeAux_append_two_of_odd037 :
    ∀ (start : Nat) (angles : List ℝ),
      (start + angles.length) % 2 = 1 → (a b : ℝ) →
      gaugeCanonicalAnglesAux037 (start + angles.length + 2) start
          (angles ++ [a, b]) =
        gaugeCanonicalAnglesAux037 (start + angles.length) start angles ++
          [gaugeCanonicalAngle037 (start + angles.length + 2)
              (start + angles.length) a,
            gaugeCanonicalAngle037 (start + angles.length + 2)
              (start + angles.length + 1) b] := by
  intro start angles
  induction angles generalizing start with
  | nil =>
      intro h a b
      simp [gaugeCanonicalAnglesAux037, gaugeCanonicalAngle037]
  | cons head tail ih =>
      intro h a b
      cases tail with
      | nil =>
          have hsmod : start % 2 = 0 := by
            simp at h
            omega
          simp [gaugeCanonicalAnglesAux037, gaugeCanonicalAngle037,
            hsmod]
      | cons next rest =>
          change
            ([gaugeCanonicalAngle037
                (start + (head :: next :: rest).length + 2) start head] ++
              gaugeCanonicalAnglesAux037
                (start + (head :: next :: rest).length + 2) (start + 1)
                (next :: (rest ++ [a, b]))) =
            (([gaugeCanonicalAngle037
                (start + (head :: next :: rest).length) start head] ++
              gaugeCanonicalAnglesAux037
                (start + (head :: next :: rest).length) (start + 1)
                (next :: rest)) ++
              [gaugeCanonicalAngle037
                  (start + (head :: next :: rest).length + 2)
                    (start + (head :: next :: rest).length) a,
                gaugeCanonicalAngle037
                  (start + (head :: next :: rest).length + 2)
                    (start + (head :: next :: rest).length + 1) b])
          have htail :
              (start + 1 + (next :: rest).length) % 2 = 1 := by
            convert h using 1
            simp only [List.length_cons]
            omega
          have hrec := ih (start + 1) htail a b
          have hrec' :
              gaugeCanonicalAnglesAux037
                  (start + (head :: next :: rest).length + 2) (start + 1)
                  (next :: (rest ++ [a, b])) =
                gaugeCanonicalAnglesAux037
                  (start + (head :: next :: rest).length) (start + 1)
                  (next :: rest) ++
                  [gaugeCanonicalAngle037
                      (start + (head :: next :: rest).length + 2)
                        (start + (head :: next :: rest).length) a,
                    gaugeCanonicalAngle037
                      (start + (head :: next :: rest).length + 2)
                        (start + (head :: next :: rest).length + 1) b] := by
            have htotal2 :
                start + (head :: next :: rest).length + 2 =
                  start + 1 + (next :: rest).length + 2 := by
              simp only [List.length_cons]
              omega
            have htotal1 :
                start + (head :: next :: rest).length + 1 =
                  start + 1 + (next :: rest).length + 1 := by
              simp only [List.length_cons]
              omega
            have htotal0 :
                start + (head :: next :: rest).length =
                  start + 1 + (next :: rest).length := by
              simp only [List.length_cons]
              omega
            rw [htotal2, htotal1, htotal0]
            simpa only [List.cons_append] using hrec
          rw [hrec']
          have hhead :
              gaugeCanonicalAngle037
                  (start + (head :: next :: rest).length + 2) start head =
                gaugeCanonicalAngle037
                  (start + (head :: next :: rest).length) start head := by
            by_cases hs : start = 0
            · simp [gaugeCanonicalAngle037, hs]
            · by_cases hlen : (next :: rest).length = 0
              · have : False := by
                  simp only [List.length_cons] at hlen
                  omega
                contradiction
              · simp [gaugeCanonicalAngle037, hs]
          rw [hhead]
          simp

theorem gaugeCanonicalAngles037_append_single_odd
    (angles : List ℝ) (hodd : angles.length % 2 = 1) (a : ℝ) :
    gaugeCanonicalAngles037 (angles ++ [a]) =
      gaugeCanonicalAngles037 angles ++ [-a] := by
  unfold gaugeCanonicalAngles037
  simp only [List.length_append, List.length_cons, List.length_nil,
    Nat.zero_add]
  have haux := gaugeAux_append_single_of_odd037 0 angles
    (by simpa using hodd) a
  have haux' :
      gaugeCanonicalAnglesAux037 (angles.length + 1) 0
          (angles ++ [a]) =
        gaugeCanonicalAnglesAux037 angles.length 0 angles ++
          [gaugeCanonicalAngle037 (angles.length + 1)
            angles.length a] := by
    simpa only [Nat.zero_add] using haux
  rw [haux']
  congr 1
  have hne : angles ≠ [] := by
    intro hnil
    simp [hnil] at hodd
  simp [gaugeCanonicalAngle037, hodd, hne]

theorem gaugeCanonicalAngles037_append_two_odd
    (angles : List ℝ) (hodd : angles.length % 2 = 1)
    (a b : ℝ) :
    gaugeCanonicalAngles037 (angles ++ [a, b]) =
      gaugeCanonicalAngles037 angles ++ [-a + Real.pi, b + Real.pi] := by
  unfold gaugeCanonicalAngles037
  simp only [List.length_append, List.length_cons, List.length_nil,
    Nat.zero_add]
  have haux := gaugeAux_append_two_of_odd037 0 angles
    (by simpa using hodd) a b
  have haux' :
      gaugeCanonicalAnglesAux037 (angles.length + 2) 0
          (angles ++ [a, b]) =
        gaugeCanonicalAnglesAux037 angles.length 0 angles ++
          [gaugeCanonicalAngle037 (angles.length + 2)
              angles.length a,
            gaugeCanonicalAngle037 (angles.length + 2)
              (angles.length + 1) b] := by
    convert haux using 1 <;> norm_num
  rw [haux']
  congr 1
  have hne : angles ≠ [] := by
    intro hnil
    simp [hnil] at hodd
  have hodd1 : (angles.length + 1) % 2 = 0 := by omega
  simp [gaugeCanonicalAngle037, hodd, hodd1, hne]

theorem oddSumAux_append_single_of_odd037 :
    ∀ (start : Nat) (angles : List ℝ),
      (start + angles.length) % 2 = 1 → (angle : ℝ) →
      oddAngleSumAux037 start (angles ++ [angle]) =
        oddAngleSumAux037 start angles + angle := by
  intro start angles
  induction angles generalizing start with
  | nil =>
      intro h angle
      simp only [List.length_nil, Nat.add_zero] at h
      simp [oddAngleSumAux037, h]
  | cons head tail ih =>
      intro h angle
      cases tail with
      | nil =>
          simp at h
          have hsmod : start % 2 = 0 := by omega
          simp [oddAngleSumAux037, hsmod, h]
      | cons next rest =>
          change
            (if start % 2 = 1 then head else 0) +
                oddAngleSumAux037 (start + 1)
                  (next :: (rest ++ [angle])) =
              ((if start % 2 = 1 then head else 0) +
                oddAngleSumAux037 (start + 1) (next :: rest)) + angle
          have htail :
              (start + 1 + (next :: rest).length) % 2 = 1 := by
            convert h using 1
            simp only [List.length_cons]
            omega
          have hrec := ih (start + 1) htail angle
          have hrec' :
              oddAngleSumAux037 (start + 1) (next :: (rest ++ [angle])) =
                oddAngleSumAux037 (start + 1) (next :: rest) + angle := by
            simpa only [List.cons_append] using hrec
          rw [hrec']
          ring

theorem oddAngleSum037_append_single_odd
    (angles : List ℝ) (hodd : angles.length % 2 = 1) (a : ℝ) :
    oddAngleSum037 (angles ++ [a]) = oddAngleSum037 angles + a := by
  unfold oddAngleSum037
  rw [oddSumAux_append_single_of_odd037 0 angles (by simpa using hodd) a]

theorem oddSumAux_append_single_of_even037 :
    ∀ (start : Nat) (angles : List ℝ),
      (start + angles.length) % 2 = 0 → (angle : ℝ) →
      oddAngleSumAux037 start (angles ++ [angle]) =
        oddAngleSumAux037 start angles := by
  intro start angles
  induction angles generalizing start with
  | nil =>
      intro h angle
      simp only [List.length_nil, Nat.add_zero] at h
      simp [oddAngleSumAux037, h]
  | cons head tail ih =>
      intro h angle
      cases tail with
      | nil =>
          simp at h
          have hsmod : start % 2 = 1 := by omega
          simp [oddAngleSumAux037, hsmod, h]
      | cons next rest =>
          change
            (if start % 2 = 1 then head else 0) +
                oddAngleSumAux037 (start + 1)
                  (next :: (rest ++ [angle])) =
              ((if start % 2 = 1 then head else 0) +
                oddAngleSumAux037 (start + 1) (next :: rest))
          have htail :
              (start + 1 + (next :: rest).length) % 2 = 0 := by
            convert h using 1
            simp only [List.length_cons]
            omega
          have hrec := ih (start + 1) htail angle
          have hrec' :
              oddAngleSumAux037 (start + 1) (next :: (rest ++ [angle])) =
                oddAngleSumAux037 (start + 1) (next :: rest) := by
            simpa only [List.cons_append] using hrec
          rw [hrec']

theorem oddAngleSum037_append_single_even
    (angles : List ℝ) (heven : angles.length % 2 = 0) (a : ℝ) :
    oddAngleSum037 (angles ++ [a]) = oddAngleSum037 angles := by
  unfold oddAngleSum037
  rw [oddSumAux_append_single_of_even037 0 angles (by simpa using heven) a]

theorem oddAngleSum037_append_two_odd
    (angles : List ℝ) (hodd : angles.length % 2 = 1)
    (a b : ℝ) :
    oddAngleSum037 (angles ++ [a, b]) = oddAngleSum037 angles + a := by
  have hlen : (angles ++ [a]).length % 2 = 0 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  calc
    oddAngleSum037 (angles ++ [a, b]) =
        oddAngleSum037 ((angles ++ [a]) ++ [b]) := by
          congr 1
          simp [List.append_assoc]
    _ = oddAngleSum037 (angles ++ [a]) :=
      oddAngleSum037_append_single_even (angles ++ [a]) hlen b
    _ = oddAngleSum037 angles + a :=
      oddAngleSum037_append_single_odd angles hodd a

theorem alternatingMatrix_append_single037
    (p : ℝ) (angles : List ℝ) (hangles : angles ≠ []) (a : ℝ) :
    fixedPointSourceOrderTransferMatrix p
        (alternatingFixedWord037 (angles ++ [a])) =
      fixedPointRoleAwareStepTransferMatrix p
          (.projectorPhase
            (phaseScheduleProofsRoleToFixed037
              (if angles.length % 2 = 0 then .source else .target)) a) *
        (fixedPointRoleAwareStepTransferMatrix p
          (.signal (phaseScheduleProofsDirectionToFixed037
            (alternatingDirection (angles.length - 1)))) *
          fixedPointSourceOrderTransferMatrix p
            (alternatingFixedWord037 angles)) := by
  rw [alternatingFixedWord037_append_single angles hangles a]
  rw [fixedPointSourceOrderTransferMatrix_append]
  simp only [List.foldl, fixedPointRoleAwareStepTransferMatrix]

theorem canonicalMatrix_append_single037
    (p : ℝ) (angles : List ℝ) (hangles : angles ≠ []) (a : ℝ) :
    fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037 (angles ++ [a])) =
      fixedPointRoleAwareStepTransferMatrix p
          (.projectorPhase .source a) *
        (fixedPointRoleAwareStepTransferMatrix p (.signal .forward) *
          fixedPointSourceOrderTransferMatrix p
            (canonicalSourceWord037 angles)) := by
  rw [canonicalSourceWord037_append_single angles hangles a]
  rw [fixedPointSourceOrderTransferMatrix_append]
  simp only [List.foldl, fixedPointRoleAwareStepTransferMatrix]

theorem alternatingMatrix_append_two037
    (p : ℝ) (angles : List ℝ) (hangles : angles ≠ [])
    (a b : ℝ) :
    fixedPointSourceOrderTransferMatrix p
        (alternatingFixedWord037 (angles ++ [a, b])) =
      fixedPointRoleAwareStepTransferMatrix p
          (.projectorPhase
            (phaseScheduleProofsRoleToFixed037
              (if (angles.length + 1) % 2 = 0 then .source else .target)) b) *
        (fixedPointRoleAwareStepTransferMatrix p
          (.signal (phaseScheduleProofsDirectionToFixed037
            (alternatingDirection angles.length))) *
          (fixedPointRoleAwareStepTransferMatrix p
            (.projectorPhase
              (phaseScheduleProofsRoleToFixed037
                (if angles.length % 2 = 0 then .source else .target)) a) *
            (fixedPointRoleAwareStepTransferMatrix p
              (.signal (phaseScheduleProofsDirectionToFixed037
                (alternatingDirection (angles.length - 1)))) *
              fixedPointSourceOrderTransferMatrix p
                (alternatingFixedWord037 angles)))) := by
  rw [show angles ++ [a, b] = (angles ++ [a]) ++ [b] by simp]
  have h1 : angles ++ [a] ≠ [] := by simp
  rw [alternatingMatrix_append_single037 p (angles ++ [a]) h1 b]
  rw [alternatingMatrix_append_single037 p angles hangles a]
  simp [List.length_append, List.length_cons, List.length_nil,
    alternatingDirection]

theorem canonicalMatrix_append_two037
    (p : ℝ) (angles : List ℝ) (hangles : angles ≠ [])
    (a b : ℝ) :
    fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037 (angles ++ [a, b])) =
      fixedPointRoleAwareStepTransferMatrix p
          (.projectorPhase .source b) *
        (fixedPointRoleAwareStepTransferMatrix p (.signal .forward) *
          (fixedPointRoleAwareStepTransferMatrix p
            (.projectorPhase .source a) *
            (fixedPointRoleAwareStepTransferMatrix p (.signal .forward) *
              fixedPointSourceOrderTransferMatrix p
                (canonicalSourceWord037 angles)))) := by
  rw [show angles ++ [a, b] = (angles ++ [a]) ++ [b] by simp]
  have h1 : angles ++ [a] ≠ [] := by simp
  rw [canonicalMatrix_append_single037 p (angles ++ [a]) h1 b]
  rw [canonicalMatrix_append_single037 p angles hangles a]

theorem alternatingMatrix_append_single_target_gauge037
    (p : ℝ) (angles : List ℝ) (hangles : angles ≠ [])
    (a : ℝ) (hodd : angles.length % 2 = 1) :
    fixedPointSourceOrderTransferMatrix p
        (alternatingFixedWord037 (angles ++ [a])) =
      Complex.exp (Complex.I * (a : ℂ)) •
        (fixedPointProjectorTransferMatrix .source (-a) *
          (fixedPointSignalTransferMatrix p .forward *
            fixedPointSourceOrderTransferMatrix p
              (alternatingFixedWord037 angles))) := by
  rw [alternatingMatrix_append_single037 p angles hangles a]
  simp only [fixedPointRoleAwareStepTransferMatrix,
    phaseScheduleProofsRoleToFixed037, phaseScheduleProofsDirectionToFixed037]
  have hprev : (angles.length - 1) % 2 = 0 := by omega
  simp [hodd, hprev, alternatingDirection]
  have htarget :
      fixedPointProjectorTransferMatrix .target a =
        Complex.exp (Complex.I * (a : ℂ)) •
          fixedPointProjectorTransferMatrix .source (-a) :=
    target_projector_as_source037 a
  rw [htarget]
  simp only [smul_mul_assoc]

theorem alternatingMatrix_append_two_source_target_gauge037
    (p : ℝ) (angles : List ℝ) (hangles : angles ≠ [])
    (a b : ℝ) (hodd : angles.length % 2 = 1) :
    fixedPointSourceOrderTransferMatrix p
        (alternatingFixedWord037 (angles ++ [a, b])) =
      Complex.exp (Complex.I * (a : ℂ)) •
        (fixedPointProjectorTransferMatrix .source (b + Real.pi) *
          (fixedPointSignalTransferMatrix p .forward *
            (fixedPointProjectorTransferMatrix .source (-a + Real.pi) *
              (fixedPointSignalTransferMatrix p .forward *
                fixedPointSourceOrderTransferMatrix p
                  (alternatingFixedWord037 angles))))) := by
  rw [alternatingMatrix_append_two037 p angles hangles a b]
  simp only [fixedPointRoleAwareStepTransferMatrix,
    phaseScheduleProofsRoleToFixed037, phaseScheduleProofsDirectionToFixed037]
  have hprev : (angles.length - 1) % 2 = 0 := by omega
  have hnext : (angles.length + 1) % 2 = 0 := by omega
  simp [hodd, hprev, hnext, alternatingDirection]
  rw [target_projector_as_source037 a]
  rw [← gaugeZ_conjugates_forward037 p]
  simp only [smul_mul_assoc, mul_smul_comm]
  have hsegment := gauge_two_source_smul_left037 b (-a)
    (Complex.exp (Complex.I * (a : ℂ)))
    (fixedPointSignalTransferMatrix p .forward)
    (fixedPointSignalTransferMatrix p .forward *
      fixedPointSourceOrderTransferMatrix p
        (alternatingFixedWord037 angles))
  simpa only [Matrix.mul_assoc, smul_mul_assoc, mul_smul_comm] using hsegment

theorem exp_smul_exp_add037 (u v : ℝ) (matrix : FixedPointTransferMatrix) :
    Complex.exp (Complex.I * (u : ℂ)) •
        (Complex.exp (Complex.I * (v : ℂ)) • matrix) =
      Complex.exp (Complex.I * ((u + v : ℝ) : ℂ)) • matrix := by
  rw [smul_smul]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem gauge_even_extend037
    (p : ℝ) (angles : List ℝ) (a : ℝ)
    (hangles : angles ≠ []) (hodd : angles.length % 2 = 1)
    (hind :
      fixedPointSourceOrderTransferMatrix p
          (alternatingFixedWord037 angles) =
        Complex.exp (Complex.I * (oddAngleSum037 angles : ℂ)) •
          fixedPointSourceOrderTransferMatrix p
            (canonicalSourceWord037 (gaugeCanonicalAngles037 angles))) :
    fixedPointSourceOrderTransferMatrix p
        (alternatingFixedWord037 (angles ++ [a])) =
      Complex.exp (Complex.I * (oddAngleSum037 (angles ++ [a]) : ℂ)) •
        fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037
            (gaugeCanonicalAngles037 (angles ++ [a]))) := by
  rw [alternatingMatrix_append_single_target_gauge037
    p angles hangles a hodd]
  rw [hind]
  have hcanon :
      fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037
            (gaugeCanonicalAngles037 angles ++ [-a])) =
        fixedPointRoleAwareStepTransferMatrix p
            (.projectorPhase .source (-a)) *
          (fixedPointRoleAwareStepTransferMatrix p (.signal .forward) *
            fixedPointSourceOrderTransferMatrix p
              (canonicalSourceWord037 (gaugeCanonicalAngles037 angles))) := by
    exact canonicalMatrix_append_single037 p
      (gaugeCanonicalAngles037 angles)
      (by
        cases angles with
        | nil => simp at hangles
        | cons head tail =>
            simp [gaugeCanonicalAngles037, gaugeCanonicalAnglesAux037]) (-a)
  rw [gaugeCanonicalAngles037_append_single_odd angles hodd a]
  rw [hcanon]
  simp only [fixedPointRoleAwareStepTransferMatrix]
  simp only [mul_smul_comm]
  have hsum := oddAngleSum037_append_single_odd angles hodd a
  rw [hsum]
  rw [exp_smul_exp_add037 a (oddAngleSum037 angles)]
  congr 1
  ring

theorem gauge_odd_extend037
    (p : ℝ) (angles : List ℝ) (a b : ℝ)
    (hangles : angles ≠ []) (hodd : angles.length % 2 = 1)
    (hind :
      fixedPointSourceOrderTransferMatrix p
          (alternatingFixedWord037 angles) =
        Complex.exp (Complex.I * (oddAngleSum037 angles : ℂ)) •
          fixedPointSourceOrderTransferMatrix p
            (canonicalSourceWord037 (gaugeCanonicalAngles037 angles))) :
    fixedPointSourceOrderTransferMatrix p
        (alternatingFixedWord037 (angles ++ [a, b])) =
      Complex.exp (Complex.I *
          (oddAngleSum037 (angles ++ [a, b]) : ℂ)) •
        fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037
            (gaugeCanonicalAngles037 (angles ++ [a, b]))) := by
  rw [alternatingMatrix_append_two_source_target_gauge037
    p angles hangles a b hodd]
  rw [hind]
  have hcanon :
      fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037
            (gaugeCanonicalAngles037 angles ++
              [-a + Real.pi, b + Real.pi])) =
        fixedPointRoleAwareStepTransferMatrix p
            (.projectorPhase .source (b + Real.pi)) *
          (fixedPointRoleAwareStepTransferMatrix p
              (.signal .forward) *
            (fixedPointRoleAwareStepTransferMatrix p
              (.projectorPhase .source (-a + Real.pi)) *
              (fixedPointRoleAwareStepTransferMatrix p (.signal .forward) *
                fixedPointSourceOrderTransferMatrix p
                  (canonicalSourceWord037
                    (gaugeCanonicalAngles037 angles))))) := by
    exact canonicalMatrix_append_two037 p
      (gaugeCanonicalAngles037 angles)
      (by
        cases angles with
        | nil => simp at hangles
        | cons head tail =>
            simp [gaugeCanonicalAngles037, gaugeCanonicalAnglesAux037])
      (-a + Real.pi) (b + Real.pi)
  rw [gaugeCanonicalAngles037_append_two_odd angles hodd a b]
  rw [hcanon]
  simp only [fixedPointRoleAwareStepTransferMatrix]
  simp only [mul_smul_comm]
  have hsum := oddAngleSum037_append_two_odd angles hodd a b
  rw [hsum]
  rw [exp_smul_exp_add037 a (oddAngleSum037 angles)]
  congr 1
  ring

theorem list_eq_append_singleton_of_two037 (l : List ℝ)
    (hl : 2 ≤ l.length) :
    ∃ pre last, l = pre ++ [last] ∧ 1 ≤ pre.length := by
  revert hl
  induction l using List.reverseRecOn with
  | nil =>
      intro hl
      simp at hl
  | append_singleton pre last ih =>
      intro hl
      have hp : 1 ≤ pre.length := by
        simp only [List.length_append, List.length_cons, List.length_nil,
          Nat.zero_add] at hl
        omega
      exact ⟨pre, last, rfl, hp⟩

theorem arbitrary_length_matrix_gauge037 :
    ∀ (n : Nat) (p : ℝ) (angles : List ℝ),
      angles.length = n → 2 ≤ n →
      fixedPointSourceOrderTransferMatrix p
          (alternatingFixedWord037 angles) =
        Complex.exp (Complex.I * (oddAngleSum037 angles : ℂ)) •
          fixedPointSourceOrderTransferMatrix p
            (canonicalSourceWord037 (gaugeCanonicalAngles037 angles)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro p angles hlen h2
      by_cases hn2 : n = 2
      · obtain ⟨a0, a1, hangles⟩ :=
          List.length_eq_two.mp (by omega : angles.length = 2)
        subst angles
        simpa [gaugeCanonicalAngles037, gaugeCanonicalAnglesAux037,
          gaugeCanonicalAngle037, oddAngleSum037, oddAngleSumAux037] using
          (alternating_q1_matrix_gauge037 p a0 a1)
      · by_cases hn3 : n = 3
        · obtain ⟨a0, a1, a2, hangles⟩ :=
            List.length_eq_three.mp (by omega : angles.length = 3)
          subst angles
          simpa [gaugeCanonicalAngles037, gaugeCanonicalAnglesAux037,
            gaugeCanonicalAngle037, oddAngleSum037, oddAngleSumAux037] using
            (alternating_q2_matrix_gauge037 p a0 a1 a2)
        · induction angles using List.reverseRecOn with
          | nil =>
              simp at hlen
              omega
          | append_singleton init last ihinit =>
              have hinit : init ≠ [] := by
                intro hnil
                subst init
                simp at hlen
                omega
              have hlen_init : init.length + 1 = n := by
                simpa using hlen
              by_cases hneven : n % 2 = 0
              · have hodd : init.length % 2 = 1 := by omega
                have hinit2 : 2 ≤ init.length := by omega
                have hind := ih init.length (by omega) p init (by omega) hinit2
                simpa using
                  (gauge_even_extend037 p init last hinit hodd hind)
              · have hnodd : n % 2 = 1 := by omega
                have hinit2 : 2 ≤ init.length := by omega
                obtain ⟨pre, middle, hdecomp, hprelen⟩ :=
                  list_eq_append_singleton_of_two037 init hinit2
                have hpre : pre ≠ [] := by
                  intro hnil
                  subst pre
                  simp at hprelen
                have hlen_pre : pre.length + 2 = n := by
                  rw [hdecomp] at hlen_init
                  simp only [List.length_append, List.length_cons,
                    List.length_nil, Nat.zero_add] at hlen_init
                  omega
                have hpre2 : 2 ≤ pre.length := by omega
                have hpreodd : pre.length % 2 = 1 := by omega
                have hind := ih pre.length (by omega) p pre
                  (by omega) hpre2
                simpa [hdecomp, List.append_assoc] using
                  (gauge_odd_extend037 p pre middle last
                    hpre hpreodd hind)

theorem alternating_to_canonical_gauge037
    (p : ℝ) (angles : List ℝ) (h2 : 2 ≤ angles.length) :
    fixedPointSourceOrderTransferMatrix p
        (alternatingFixedWord037 angles) =
      Complex.exp (Complex.I * (oddAngleSum037 angles : ℂ)) •
        fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037 (gaugeCanonicalAngles037 angles)) := by
  exact arbitrary_length_matrix_gauge037 angles.length p angles rfl h2

end
end SpectralSamplingProof.Analytic
