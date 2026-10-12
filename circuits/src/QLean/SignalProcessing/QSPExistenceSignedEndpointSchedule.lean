import QLean.SignalProcessing.QSPExistenceChebyshevEndpointExistence
import Mathlib
import QLean.History.Jennings.PureSpec
import QLean.SignalProcessing.PhaseScheduleProofsPhaseWordContract
import QLean.SignalProcessing.PhaseScheduleProofsChebyshevContract

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore
open JenningsHistory

noncomputable section

/-! StateNormalizationContract starts from the signed PhaseScheduleProofs evaluator.  The native
    success-probability evaluator is intentionally not used here. -/

def signedSignalCount042 : List PhaseStep → Nat
  | [] => 0
  | .signal _ :: rest => signedSignalCount042 rest + 1
  | .phase _ _ :: rest => signedSignalCount042 rest

theorem signalMatrix_neg042 (x : ℝ) (direction : JenningsHistory.SignalDirection) :
    signalMatrix (-x) direction =
      (-1 : ℂ) • (gaugeZ037 * signalMatrix x direction * gaugeZ037) := by
  ext row column
  fin_cases row <;> fin_cases column <;> cases direction <;>
    simp [signalMatrix, signalSourceAmplitude, signalTargetAmplitude,
      gaugeZ037, Matrix.mul_apply, fixedPointSourceIndex,
      ]

theorem phaseMatrix_gauge_commute042 (role : PhaseRole) (angle : ℝ) :
    gaugeZ037 * phaseMatrix role angle =
      phaseMatrix role angle * gaugeZ037 := by
  simpa only [phaseScheduleProofsPhaseMatrix_matches_fixed037] using
    (gaugeZ_commutes_projector037 (phaseScheduleProofsRoleToFixed037 role) angle)

theorem gaugeZ_mul_self042 : gaugeZ037 * gaugeZ037 = (1 : C2) := by
  exact gaugeZ_mul_self037

theorem wordProduct_append042 (x : ℝ) (left right : List PhaseStep) :
    wordProduct x (left ++ right) =
      wordProduct x right * wordProduct x left := by
  have hfold : ∀ (xs : List PhaseStep) (acc : C2),
      List.foldl (fun accumulated step =>
          stepMatrix x step * accumulated) acc xs =
        List.foldl (fun accumulated step =>
          stepMatrix x step * accumulated) 1 xs * acc := by
    intro xs
    induction xs with
    | nil => intro acc; simp
    | cons first rest ih =>
        intro acc
        simp only [List.foldl, Matrix.mul_one]
        rw [ih (stepMatrix x first * acc), ih (stepMatrix x first)]
        simp [Matrix.mul_assoc]
  calc
    wordProduct x (left ++ right) =
        List.foldl (fun accumulated step =>
          stepMatrix x step * accumulated) 1 (left ++ right) := rfl
    _ = List.foldl (fun accumulated step =>
          stepMatrix x step * accumulated)
        (List.foldl (fun accumulated step =>
          stepMatrix x step * accumulated) 1 left) right := by
          rw [List.foldl_append]
    _ = List.foldl (fun accumulated step =>
          stepMatrix x step * accumulated) 1 right *
        List.foldl (fun accumulated step =>
          stepMatrix x step * accumulated) 1 left :=
      hfold right _
    _ = wordProduct x right * wordProduct x left := rfl

theorem wordProduct_cons042 (x : ℝ) (step : PhaseStep)
    (rest : List PhaseStep) :
    wordProduct x (step :: rest) =
      wordProduct x rest * stepMatrix x step := by
  rw [show step :: rest = [step] ++ rest by rfl,
    wordProduct_append042]
  simp [wordProduct]

theorem conjugated_mul042 (left right : C2) :
    (gaugeZ037 * left * gaugeZ037) *
        (gaugeZ037 * right * gaugeZ037) =
      gaugeZ037 * (left * right) * gaugeZ037 := by
  calc
    gaugeZ037 * left * gaugeZ037 * (gaugeZ037 * right * gaugeZ037) =
        gaugeZ037 * left *
          (gaugeZ037 * gaugeZ037) * right * gaugeZ037 := by
            noncomm_ring
    _ = gaugeZ037 * (left * right) * gaugeZ037 := by
          rw [gaugeZ_mul_self042]
          simp only [Matrix.mul_one]
          noncomm_ring

theorem conjugated_mul_right_comm042 (left right : C2)
    (hcomm : gaugeZ037 * right = right * gaugeZ037) :
    (gaugeZ037 * left * gaugeZ037) * right =
      gaugeZ037 * (left * right) * gaugeZ037 := by
  calc
    (gaugeZ037 * left * gaugeZ037) * right =
        gaugeZ037 * left * (gaugeZ037 * right) := by
          simp only [Matrix.mul_assoc]
    _ = gaugeZ037 * left * (right * gaugeZ037) := by rw [hcomm]
    _ = gaugeZ037 * (left * (right * gaugeZ037)) := by
          noncomm_ring
    _ = gaugeZ037 * ((left * right) * gaugeZ037) := by
          noncomm_ring
    _ = gaugeZ037 * (left * right) * gaugeZ037 := by
          noncomm_ring

theorem smul_mul_smul042 (a b : ℂ) (left right : C2) :
    (a • left) * (b • right) = (a * b) • (left * right) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  simp [mul_comm]

theorem wordProduct_neg042 (x : ℝ) (steps : List PhaseStep) :
    wordProduct (-x) steps =
      (-1 : ℂ) ^ signedSignalCount042 steps •
        (gaugeZ037 * wordProduct x steps * gaugeZ037) := by
  induction steps with
  | nil =>
      simp [wordProduct, signedSignalCount042, gaugeZ_mul_self042]
  | cons first rest ih =>
      rw [wordProduct_cons042, wordProduct_cons042, ih]
      cases first with
      | phase role angle =>
          rw [show stepMatrix (-x) (.phase role angle) =
              phaseMatrix role angle by rfl]
          rw [show stepMatrix x (.phase role angle) =
              phaseMatrix role angle by rfl]
          have hcomm := phaseMatrix_gauge_commute042 role angle
          have hright := conjugated_mul_right_comm042
            (wordProduct x rest) (phaseMatrix role angle) hcomm
          rw [show signedSignalCount042
              (.phase role angle :: rest) = signedSignalCount042 rest by rfl]
          rw [smul_mul_assoc, hright]
      | signal direction =>
          rw [show stepMatrix (-x) (.signal direction) =
              signalMatrix (-x) direction by rfl]
          rw [show stepMatrix x (.signal direction) =
              signalMatrix x direction by rfl]
          rw [signalMatrix_neg042]
          rw [smul_mul_smul042]
          rw [conjugated_mul042]
          rw [show signedSignalCount042
              (.signal direction :: rest) = signedSignalCount042 rest + 1 by rfl]
          rw [pow_succ]

theorem gauge_source_response042 (x : ℝ) (steps : List PhaseStep) :
    ((gaugeZ037 * wordProduct x steps * gaugeZ037).mulVec sourceBasis) 0 =
      (wordProduct x steps).mulVec sourceBasis 0 := by
  simp [gaugeZ037, sourceBasis, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, fixedPointSourceIndex]

theorem fixedPointSourceOrderTransferMatrix_cons042
    (p : ℝ) (step : FixedPointRoleAwarePhaseStep)
    (rest : List FixedPointRoleAwarePhaseStep) :
    fixedPointSourceOrderTransferMatrix p (step :: rest) =
      fixedPointSourceOrderTransferMatrix p rest *
        fixedPointRoleAwareStepTransferMatrix p step := by
  have hfold : ∀ (xs : List FixedPointRoleAwarePhaseStep) (acc : FixedPointTransferMatrix),
      List.foldl (fun accumulated s =>
          fixedPointRoleAwareStepTransferMatrix p s * accumulated) acc xs =
        List.foldl (fun accumulated s =>
          fixedPointRoleAwareStepTransferMatrix p s * accumulated) 1 xs * acc := by
    intro xs
    induction xs with
    | nil => intro acc; simp
    | cons first tail ih =>
        intro acc
        simp only [List.foldl, Matrix.mul_one]
        rw [ih (fixedPointRoleAwareStepTransferMatrix p first * acc),
          ih (fixedPointRoleAwareStepTransferMatrix p first)]
        simp [Matrix.mul_assoc]
  calc
    fixedPointSourceOrderTransferMatrix p (step :: rest) =
        List.foldl (fun accumulated s =>
          fixedPointRoleAwareStepTransferMatrix p s * accumulated) 1
          (step :: rest) := rfl
    _ = List.foldl (fun accumulated s =>
        fixedPointRoleAwareStepTransferMatrix p s * accumulated)
        (fixedPointRoleAwareStepTransferMatrix p step) rest := by
          simp only [List.foldl, Matrix.mul_one]
    _ = List.foldl (fun accumulated s =>
          fixedPointRoleAwareStepTransferMatrix p s * accumulated) 1 rest *
        fixedPointRoleAwareStepTransferMatrix p step :=
      hfold rest _
    _ = fixedPointSourceOrderTransferMatrix p rest *
        fixedPointRoleAwareStepTransferMatrix p step := rfl

theorem fixedPointSourcePhase_first_shift042
    (p a b : ℝ) (rest : List FixedPointRoleAwarePhaseStep) :
    (fixedPointSourceOrderTransferMatrix p
        (.projectorPhase .source (a + b) :: rest)).mulVec
        fixedPointSourceBasisState fixedPointSourceIndex =
      Complex.exp (Complex.I * (b : ℂ)) *
        (fixedPointSourceOrderTransferMatrix p
          (.projectorPhase .source a :: rest)).mulVec
          fixedPointSourceBasisState fixedPointSourceIndex := by
  rw [fixedPointSourceOrderTransferMatrix_cons042,
    fixedPointSourceOrderTransferMatrix_cons042]
  rw [← Matrix.mulVec_mulVec]
  rw [← Matrix.mulVec_mulVec]
  have hvec :
      (fixedPointRoleAwareStepTransferMatrix p
          (.projectorPhase .source (a + b))).mulVec
          fixedPointSourceBasisState =
        Complex.exp (Complex.I * (b : ℂ)) •
          (fixedPointRoleAwareStepTransferMatrix p
            (.projectorPhase .source a)).mulVec
            fixedPointSourceBasisState := by
    funext index
    fin_cases index
    · simp [fixedPointRoleAwareStepTransferMatrix,
        fixedPointProjectorTransferMatrix, fixedPointSourceBasisState,
        fixedPointSourceIndex]
      rw [← Complex.exp_add]
      congr 1
      ring
    · simp [fixedPointRoleAwareStepTransferMatrix,
        fixedPointProjectorTransferMatrix, fixedPointSourceBasisState,
        fixedPointSourceIndex]
  rw [hvec]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply,
    smul_eq_mul]
  ring

def compensatedFirstAngles042 (angles : List ℝ) (shift : ℝ) : List ℝ :=
  match angles with
  | [] => []
  | head :: tail => (head - shift) :: tail

theorem compensatedFirstAngles042_length
    (angles : List ℝ) (shift : ℝ) :
    (compensatedFirstAngles042 angles shift).length = angles.length := by
  cases angles <;> rfl

theorem compensatedFirstAngles042_odd_sum
    (angles : List ℝ) (shift : ℝ) :
    oddAngleSum037 (compensatedFirstAngles042 angles shift) =
      oddAngleSum037 angles := by
  cases angles <;>
    simp [compensatedFirstAngles042, oddAngleSum037, oddAngleSumAux037]

theorem canonical_matrix_lift_first042
    (p : ℝ) (angles : List ℝ) (h2 : 2 ≤ angles.length) :
    fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037
          (gaugeCanonicalAngles037 (liftFirstAngles037 angles))) =
      fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037 (gaugeCanonicalAngles037 angles)) := by
  cases angles with
  | nil => simp at h2
  | cons head tail =>
      cases tail with
      | nil => simp at h2
      | cons next rest =>
          have hphase := phaseMatrix_phaseLift037 .source head
          have hstep :
              fixedPointRoleAwareStepTransferMatrix p
                  (.projectorPhase .source (phaseLift037 head)) =
                fixedPointRoleAwareStepTransferMatrix p
                  (.projectorPhase .source head) := by
            calc
              fixedPointRoleAwareStepTransferMatrix p
                    (.projectorPhase .source (phaseLift037 head)) =
                  fixedPointProjectorTransferMatrix .source
                    (phaseLift037 head) := by rfl
              _ = phaseMatrix .source (phaseLift037 head) := by
                    symm
                    exact phaseScheduleProofsPhaseMatrix_matches_fixed037 .source
                      (phaseLift037 head)
              _ = phaseMatrix .source head := hphase
              _ = fixedPointProjectorTransferMatrix .source head := by
                    exact phaseScheduleProofsPhaseMatrix_matches_fixed037 .source head
              _ = fixedPointRoleAwareStepTransferMatrix p
                    (.projectorPhase .source head) := by rfl
          simp only [liftFirstAngles037, gaugeCanonicalAngles037,
            gaugeCanonicalAnglesAux037, gaugeCanonicalAngle037,
            List.length_cons, Nat.zero_add, if_true,
            canonicalSourceWord037]
          change fixedPointSourceOrderTransferMatrix p
              (_ :: _ :: _) = fixedPointSourceOrderTransferMatrix p
              (_ :: _ :: _)
          rw [fixedPointSourceOrderTransferMatrix_cons042,
            fixedPointSourceOrderTransferMatrix_cons042]
          rw [hstep]
          conv_rhs =>
            rw [fixedPointSourceOrderTransferMatrix_cons042,
              fixedPointSourceOrderTransferMatrix_cons042]

theorem signedSignalCount042_eq_filter_length
    (steps : List PhaseStep) :
    signedSignalCount042 steps =
      (steps.filter PhaseScheduleProofs.phaseStepIsSignal125).length := by
  induction steps with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | phase role angle =>
          simp [signedSignalCount042, PhaseScheduleProofs.phaseStepIsSignal125, ih]
      | signal direction =>
          simp [signedSignalCount042, PhaseScheduleProofs.phaseStepIsSignal125, ih]

theorem signedSignalCount042_phaseWord
    {n : Nat} (schedule : PhaseSchedule n) :
    signedSignalCount042 (phaseWord schedule) = n - 1 := by
  rw [signedSignalCount042_eq_filter_length]
  exact PhaseScheduleProofs.phaseWord_signal_count125 schedule

theorem fixedPointSourceBasisState_eq_sourceBasis042 :
    fixedPointSourceBasisState = sourceBasis := by
  funext index
  fin_cases index <;>
    simp [fixedPointSourceBasisState, sourceBasis,
      fixedPointSourceIndex]

theorem shapedCanonicalSourceEval042
    (input : GeneralRealQSPPolynomial127)
    (w : ShapedQSPWordSynthesis040 input)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037
          (gaugeCanonicalAngles037 w.angles))).mulVec
        fixedPointSourceBasisState fixedPointSourceIndex =
      Polynomial.eval (fixedPointSourceAmplitude p : ℂ)
        (completionStandardState033 input).sourceFactor := by
  rw [← w.standardWord_shape]
  have h := shapedWord040_source_eval input w.standardWord w.state_match
    p hp0 hp1
  simpa [fixedPointRealizedComplexFailureAmplitude,
    fixedPointEvaluatedState] using h

theorem shapedCanonicalSourceEval042_zero
    (input : GeneralRealQSPPolynomial127)
    (w : ShapedQSPWordSynthesis040 input)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037
          (gaugeCanonicalAngles037 w.angles))).mulVec
        fixedPointSourceBasisState 0 =
      Polynomial.eval (fixedPointSourceAmplitude p : ℂ)
        (completionStandardState033 input).sourceFactor := by
  simpa [fixedPointSourceIndex] using
    (shapedCanonicalSourceEval042 input w p hp0 hp1)

theorem canonicalSource_first_shift042
    (p a b : ℝ) (tailAngles : List ℝ) (htail : tailAngles ≠ []) :
    (fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037 ((a + b) :: tailAngles))).mulVec
        fixedPointSourceBasisState fixedPointSourceIndex =
      Complex.exp (Complex.I * (b : ℂ)) *
        (fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037 (a :: tailAngles))).mulVec
          fixedPointSourceBasisState fixedPointSourceIndex := by
  cases tailAngles with
  | nil => contradiction
  | cons first rest =>
      simp only [canonicalSourceWord037, List.cons_append,
        List.nil_append]
      exact fixedPointSourcePhase_first_shift042 p a b
        (.signal .forward :: canonicalSourceWord037 (first :: rest))

theorem gaugeCanonicalAngles037_cons042
    (head : ℝ) (tail : List ℝ) :
    gaugeCanonicalAngles037 (head :: tail) =
      head :: gaugeCanonicalAnglesAux037 (tail.length + 1) 1 tail := by
  simp [gaugeCanonicalAngles037, gaugeCanonicalAnglesAux037,
    gaugeCanonicalAngle037]

theorem compensatedCanonicalSource042
    (p head shift : ℝ) (tail : List ℝ)
    (h2 : 2 ≤ (head :: tail).length) :
    (fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037
          (gaugeCanonicalAngles037
            (liftFirstAngles037
              (compensatedFirstAngles042 (head :: tail) shift))))).mulVec
        fixedPointSourceBasisState fixedPointSourceIndex =
      Complex.exp (Complex.I * ((-shift : ℝ) : ℂ)) *
        (fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037
            (gaugeCanonicalAngles037 (head :: tail)))).mulVec
          fixedPointSourceBasisState fixedPointSourceIndex := by
  have hcomp2 :
      2 ≤ (compensatedFirstAngles042 (head :: tail) shift).length := by
    simpa [compensatedFirstAngles042] using h2
  calc
    (fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037
          (gaugeCanonicalAngles037
            (liftFirstAngles037
              (compensatedFirstAngles042 (head :: tail) shift))))).mulVec
        fixedPointSourceBasisState fixedPointSourceIndex =
      (fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037
          (gaugeCanonicalAngles037
            (compensatedFirstAngles042 (head :: tail) shift)))).mulVec
        fixedPointSourceBasisState fixedPointSourceIndex := by
          rw [canonical_matrix_lift_first042 p
            (compensatedFirstAngles042 (head :: tail) shift) hcomp2]
    _ = Complex.exp (Complex.I * ((-shift : ℝ) : ℂ)) *
        (fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037
            (gaugeCanonicalAngles037 (head :: tail)))).mulVec
          fixedPointSourceBasisState fixedPointSourceIndex := by
      cases tail with
      | nil => simp at h2
      | cons first rest =>
          let tailAngles : List ℝ :=
            gaugeCanonicalAnglesAux037
              ((first :: rest).length + 1) 1 (first :: rest)
          have htailAngles : tailAngles ≠ [] := by
            simp [tailAngles, gaugeCanonicalAnglesAux037]
          have hcomp :
              gaugeCanonicalAngles037
                  (compensatedFirstAngles042
                    (head :: first :: rest) shift) =
                (head - shift) :: tailAngles := by
            simp [compensatedFirstAngles042,
              gaugeCanonicalAngles037_cons042, tailAngles]
          have horig :
              gaugeCanonicalAngles037 (head :: first :: rest) =
                head :: tailAngles := by
            simp [gaugeCanonicalAngles037_cons042, tailAngles]
          rw [hcomp, horig]
          simpa [sub_eq_add_neg] using
            (canonicalSource_first_shift042 p head (-shift)
              tailAngles htailAngles)

theorem compensatedCanonicalSource042_general
    (p : ℝ) (angles : List ℝ) (shift : ℝ)
    (h2 : 2 ≤ angles.length) :
    (fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037
          (gaugeCanonicalAngles037
            (liftFirstAngles037
              (compensatedFirstAngles042 angles shift))))).mulVec
        fixedPointSourceBasisState fixedPointSourceIndex =
      Complex.exp (Complex.I * ((-shift : ℝ) : ℂ)) *
        (fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037 (gaugeCanonicalAngles037 angles))).mulVec
          fixedPointSourceBasisState fixedPointSourceIndex := by
  cases angles with
  | nil => simp at h2
  | cons head tail =>
      simpa [compensatedFirstAngles042] using
        (compensatedCanonicalSource042 p head shift tail h2)

theorem compensatedCanonicalSource042_general_zero
    (p : ℝ) (angles : List ℝ) (shift : ℝ)
    (h2 : 2 ≤ angles.length) :
    (fixedPointSourceOrderTransferMatrix p
        (canonicalSourceWord037
          (gaugeCanonicalAngles037
            (liftFirstAngles037
              (compensatedFirstAngles042 angles shift))))).mulVec
        fixedPointSourceBasisState 0 =
      Complex.exp (Complex.I * ((-shift : ℝ) : ℂ)) *
        (fixedPointSourceOrderTransferMatrix p
          (canonicalSourceWord037 (gaugeCanonicalAngles037 angles))).mulVec
          fixedPointSourceBasisState 0 := by
  simpa [fixedPointSourceIndex] using
    (compensatedCanonicalSource042_general p angles shift h2)

theorem oddAngleSum037_liftFirst042 (angles : List ℝ) :
    oddAngleSum037 (liftFirstAngles037 angles) =
      oddAngleSum037 angles := by
  cases angles <;>
    simp [liftFirstAngles037, oddAngleSum037, oddAngleSumAux037]

theorem matrix_smul_source042 (c : ℂ) (matrix : C2) :
    ((c • matrix).mulVec fixedPointSourceBasisState)
        0 =
      c * (matrix.mulVec fixedPointSourceBasisState)
        0 := by
  rw [Matrix.smul_mulVec]
  rfl

theorem compensatedScheduleResponse_nonneg042
    (input : GeneralRealQSPPolynomial127)
    (w : ShapedQSPWordSynthesis040 input)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    scheduleResponse
        (phaseScheduleOfAngles037
          (compensatedFirstAngles042 w.angles
            (oddAngleSum037 w.angles))
          (by
            rw [compensatedFirstAngles042_length]
            exact w.angles_ge_two)) x =
      Polynomial.eval (x : ℂ)
        (completionStandardState033 input).sourceFactor := by
  let angles : List ℝ :=
    compensatedFirstAngles042 w.angles (oddAngleSum037 w.angles)
  have h2 : 2 ≤ angles.length := by
    dsimp [angles]
    rw [compensatedFirstAngles042_length]
    exact w.angles_ge_two
  have h2lift : 2 ≤ (liftFirstAngles037 angles).length := by
    rw [liftFirstAngles037_length]
    exact h2
  have hsum : oddAngleSum037 angles = oddAngleSum037 w.angles := by
    dsimp [angles]
    exact compensatedFirstAngles042_odd_sum w.angles
      (oddAngleSum037 w.angles)
  have hlift :
      oddAngleSum037 (liftFirstAngles037 angles) =
        oddAngleSum037 w.angles := by
    rw [oddAngleSum037_liftFirst042, hsum]
  change (wordProduct x
      (phaseWord (phaseScheduleOfAngles037 angles h2))).mulVec sourceBasis 0 =
    Polynomial.eval (x : ℂ)
      (completionStandardState033 input).sourceFactor
  rw [← fixedPointSourceBasisState_eq_sourceBasis042]
  rw [phaseWord_schedule_matrix_eq_alternating037 hx0 hx1 angles h2]
  rw [alternating_to_canonical_gauge037 (1 - x ^ 2)
    (liftFirstAngles037 angles) h2lift]
  rw [matrix_smul_source042]
  dsimp [angles]
  rw [compensatedCanonicalSource042_general_zero (1 - x ^ 2)
    w.angles (oddAngleSum037 w.angles) w.angles_ge_two]
  rw [shapedCanonicalSourceEval042_zero input w (1 - x ^ 2)
    (by nlinarith [sq_nonneg x]) (by nlinarith [sq_nonneg x, hx1])]
  rw [fixedPointSourceAmplitude_one_sub_sq037 hx0]
  rw [hlift]
  rw [← mul_assoc]
  rw [← Complex.exp_add]
  simp

theorem gaugeCanonicalAngles037_length042 (angles : List ℝ) :
    (gaugeCanonicalAngles037 angles).length = angles.length := by
  unfold gaugeCanonicalAngles037
  have haux : ∀ (n j : Nat) (xs : List ℝ),
      (gaugeCanonicalAnglesAux037 n j xs).length = xs.length := by
    intro n j xs
    induction xs generalizing n j with
    | nil => rfl
    | cons head tail ih =>
        simp only [gaugeCanonicalAnglesAux037, List.length_cons]
        rw [ih]
  exact haux angles.length 0 angles

theorem canonicalSourceWord037_signal_count042 (angles : List ℝ) :
    signalCount127 (canonicalSourceWord037 angles) = angles.length - 1 := by
  induction angles with
  | nil => simp [canonicalSourceWord037, signalCount127]
  | cons head tail ih =>
      cases tail with
      | nil => simp [canonicalSourceWord037, signalCount127]
      | cons next rest =>
          simp [canonicalSourceWord037, signalCount127, ih]

theorem shapedAngles_length042
    (input : GeneralRealQSPPolynomial127)
    (w : ShapedQSPWordSynthesis040 input) :
    w.angles.length = input.degree + 1 := by
  have hcount := w.signal_count
  rw [w.standardWord_shape] at hcount
  have hcanonical := canonicalSourceWord037_signal_count042
    (gaugeCanonicalAngles037 w.angles)
  have hanglelen := gaugeCanonicalAngles037_length042 w.angles
  have hcount' :
      (gaugeCanonicalAngles037 w.angles).length - 1 = input.degree :=
    hcanonical.symm.trans hcount
  rw [hanglelen] at hcount'
  have htwo : 2 ≤ w.angles.length := w.angles_ge_two
  omega

theorem compensatedScheduleResponse_neg042
    (input : GeneralRealQSPPolynomial127)
    (w : ShapedQSPWordSynthesis040 input)
    (hodd : input.degree % 2 = 1)
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    scheduleResponse
        (phaseScheduleOfAngles037
          (compensatedFirstAngles042 w.angles
            (oddAngleSum037 w.angles))
          (by
            rw [compensatedFirstAngles042_length]
            exact w.angles_ge_two)) (-y) =
      -Polynomial.eval (y : ℂ)
        (completionStandardState033 input).sourceFactor := by
  let angles : List ℝ :=
    compensatedFirstAngles042 w.angles (oddAngleSum037 w.angles)
  have h2 : 2 ≤ angles.length := by
    dsimp [angles]
    rw [compensatedFirstAngles042_length]
    exact w.angles_ge_two
  have hlen : angles.length = input.degree + 1 := by
    dsimp [angles]
    rw [compensatedFirstAngles042_length]
    exact shapedAngles_length042 input w
  have hcount :
      signedSignalCount042
        (phaseWord (phaseScheduleOfAngles037 angles h2)) =
        input.degree := by
    rw [signedSignalCount042_phaseWord]
    omega
  have hpow : (-1 : ℂ) ^ signedSignalCount042
        (phaseWord (phaseScheduleOfAngles037 angles h2)) = -1 := by
    rw [hcount]
    have hoddZ : Odd input.degree := by
      rcases Nat.even_or_odd input.degree with he | ho
      · rw [Nat.even_iff] at he
        omega
      · exact ho
    exact Odd.neg_one_pow hoddZ
  change (wordProduct (-y)
      (phaseWord (phaseScheduleOfAngles037 angles h2))).mulVec sourceBasis 0 =
    -Polynomial.eval (y : ℂ)
      (completionStandardState033 input).sourceFactor
  rw [wordProduct_neg042 y]
  rw [hpow]
  rw [Matrix.smul_mulVec]
  change (-1 : ℂ) *
      ((gaugeZ037 * wordProduct y
        (phaseWord (phaseScheduleOfAngles037 angles h2)) * gaugeZ037).mulVec
          sourceBasis) 0 = _
  rw [gauge_source_response042]
  have hnonneg := compensatedScheduleResponse_nonneg042 input w y hy0 hy1
  change (wordProduct y
      (phaseWord (phaseScheduleOfAngles037 angles h2))).mulVec sourceBasis 0 =
    Polynomial.eval (y : ℂ)
      (completionStandardState033 input).sourceFactor at hnonneg
  calc
    (-1 : ℂ) *
        (wordProduct y
          (phaseWord (phaseScheduleOfAngles037 angles h2))).mulVec
          sourceBasis 0 =
      -(wordProduct y
          (phaseWord (phaseScheduleOfAngles037 angles h2))).mulVec
          sourceBasis 0 := by ring
    _ = -Polynomial.eval (y : ℂ)
        (completionStandardState033 input).sourceFactor :=
      congrArg Neg.neg hnonneg

theorem compensatedScheduleResponse_real042
    (input : GeneralRealQSPPolynomial127)
    (w : ShapedQSPWordSynthesis040 input)
    (hodd : input.degree % 2 = 1)
    (x : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    (scheduleResponse
        (phaseScheduleOfAngles037
          (compensatedFirstAngles042 w.angles
            (oddAngleSum037 w.angles))
          (by
            rw [compensatedFirstAngles042_length]
            exact w.angles_ge_two)) x).re =
      Polynomial.eval x input.polynomial := by
  by_cases hnonneg : 0 ≤ x
  · have hpos := compensatedScheduleResponse_nonneg042 input w x
      hnonneg hx1
    have hreal := congrArg Complex.re hpos
    have hread := completionStandardState033_real_readout input x
    have hP : (completionPair024 input).P = input.polynomial := rfl
    rw [hread, hP] at hreal
    exact hreal
  · have hxneg : x ≤ 0 := le_of_not_ge hnonneg
    have hy0 : 0 ≤ -x := by linarith
    have hy1 : -x ≤ 1 := by linarith
    have hneg := compensatedScheduleResponse_neg042 input w hodd
      (-x) hy0 hy1
    have hneg' :
        scheduleResponse
            (phaseScheduleOfAngles037
              (compensatedFirstAngles042 w.angles
                (oddAngleSum037 w.angles))
              (by
                rw [compensatedFirstAngles042_length]
                exact w.angles_ge_two)) x =
          -Polynomial.eval (-x : ℂ)
            (completionStandardState033 input).sourceFactor := by
      simpa using hneg
    have hreal := congrArg Complex.re hneg'
    have hread := completionStandardState033_real_readout input (-x)
    have hP : (completionPair024 input).P = input.polynomial := rfl
    have hpar := input.parity_law x
    rw [if_neg (by omega : ¬ input.degree % 2 = 0)] at hpar
    have hcast : (-(x : ℂ)) = ((-x : ℝ) : ℂ) := by norm_num
    rw [hcast] at hreal
    simp only [Complex.neg_re] at hreal
    rw [hread, hP] at hreal
    linarith

end
end SpectralSamplingProof.Analytic
