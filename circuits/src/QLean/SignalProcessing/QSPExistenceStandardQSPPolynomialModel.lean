import QLean.SignalProcessing.QSPExistenceQSPPhaseExtraction

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## Canonical one-query polynomial state

The canonical signal matrix acts on a physical column `(S, g*T)` where the
first coordinate is the source amplitude and `g` is the target amplitude.
The polynomial state therefore stores `S` and `T` separately; it does not
pretend that the square root `g` is itself a polynomial.
-/

structure StandardQSPPolynomialState032 where
  sourceFactor : Polynomial ℂ
  targetFactor : Polynomial ℂ

@[ext] theorem standardPolynomialState_ext032
    {state state' : StandardQSPPolynomialState032}
    (hs : state.sourceFactor = state'.sourceFactor)
    (ht : state.targetFactor = state'.targetFactor) :
    state = state' := by
  cases state
  cases state'
  simp_all

def standardGoodSquare032 : Polynomial ℂ :=
  1 - (Polynomial.X : Polynomial ℂ) ^ 2

def standardPhysicalState032
    (bad good : ℂ) (state : StandardQSPPolynomialState032) :
    FixedPointTransferState :=
  fixedPointPairState
    (Polynomial.eval bad state.sourceFactor)
    (good * Polynomial.eval bad state.targetFactor)

def standardSignalForward032
    (state : StandardQSPPolynomialState032) :
    StandardQSPPolynomialState032 where
  sourceFactor := Polynomial.X * state.sourceFactor -
    standardGoodSquare032 * state.targetFactor
  targetFactor := state.sourceFactor + Polynomial.X * state.targetFactor

def standardSignalAdjoint032
    (state : StandardQSPPolynomialState032) :
    StandardQSPPolynomialState032 where
  sourceFactor := Polynomial.X * state.sourceFactor +
    standardGoodSquare032 * state.targetFactor
  targetFactor := -state.sourceFactor + Polynomial.X * state.targetFactor

theorem fixedPointPairState_congr032
    {source source' target target' : ℂ}
    (hs : source = source') (ht : target = target') :
    fixedPointPairState source target = fixedPointPairState source' target' := by
  funext index
  fin_cases index <;>
    simp [fixedPointPairState, fixedPointSourceIndex, hs, ht]

theorem standardSignalForward032_eval_formula
    (bad good : ℂ)
    (hgood : good ^ 2 = 1 - bad ^ 2)
    (state : StandardQSPPolynomialState032) :
    standardPhysicalState032 bad good (standardSignalForward032 state) =
      fixedPointPairState
        (bad * Polynomial.eval bad state.sourceFactor -
          good * (good * Polynomial.eval bad state.targetFactor))
        (good * Polynomial.eval bad state.sourceFactor +
          bad * (good * Polynomial.eval bad state.targetFactor)) := by
  apply fixedPointPairState_congr032
  · simp [standardSignalForward032, standardGoodSquare032,
      Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow]
    rw [← hgood]
    ring
  · simp [standardSignalForward032, standardGoodSquare032,
      Polynomial.eval_mul]
    ring

theorem standardSignalAdjoint032_eval_formula
    (bad good : ℂ)
    (hgood : good ^ 2 = 1 - bad ^ 2)
    (state : StandardQSPPolynomialState032) :
    standardPhysicalState032 bad good (standardSignalAdjoint032 state) =
      fixedPointPairState
        (bad * Polynomial.eval bad state.sourceFactor +
          good * (good * Polynomial.eval bad state.targetFactor))
        (-good * Polynomial.eval bad state.sourceFactor +
          bad * (good * Polynomial.eval bad state.targetFactor)) := by
  apply fixedPointPairState_congr032
  · simp [standardSignalAdjoint032,
      standardGoodSquare032, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow]
    rw [← hgood]
    ring
  · simp [standardSignalAdjoint032,
      standardGoodSquare032, Polynomial.eval_add, Polynomial.eval_mul]
    ring

theorem standardSignalForward032_adjoint032
    (state : StandardQSPPolynomialState032) :
    standardSignalForward032 (standardSignalAdjoint032 state) = state := by
  cases state with
  | mk sourceFactor targetFactor =>
      simp [standardSignalAdjoint032, standardSignalForward032,
        standardGoodSquare032]
      constructor <;> ring

/-! The canonical real amplitudes satisfy the polynomial normalization on the
scientific domain.  This is the only square-root fact used by the evaluator
bridge; the stored target factor remains polynomial. -/

theorem fixedPointAmplitudes_square_add032
    (successProbability : ℝ)
    (hs0 : 0 ≤ successProbability) (hs1 : successProbability ≤ 1) :
    (fixedPointSourceAmplitude successProbability) ^ 2 +
        (fixedPointTargetAmplitude successProbability) ^ 2 = 1 := by
  have hbad :
      (fixedPointSourceAmplitude successProbability) ^ 2 =
        1 - successProbability := by
    unfold fixedPointSourceAmplitude
    rw [max_eq_right]
    · exact Real.sq_sqrt (by linarith)
    · linarith
  have hgood :
      (fixedPointTargetAmplitude successProbability) ^ 2 =
        successProbability := by
    unfold fixedPointTargetAmplitude
    rw [max_eq_right hs0]
    exact Real.sq_sqrt hs0
  linarith

theorem standardSignalForward032_eval_actual
    (successProbability : ℝ)
    (hs0 : 0 ≤ successProbability) (hs1 : successProbability ≤ 1)
    (state : StandardQSPPolynomialState032) :
    standardPhysicalState032
        (fixedPointSourceAmplitude successProbability)
        (fixedPointTargetAmplitude successProbability)
        (standardSignalForward032 state) =
      (fixedPointSignalTransferMatrix successProbability .forward).mulVec
        (standardPhysicalState032
          (fixedPointSourceAmplitude successProbability)
          (fixedPointTargetAmplitude successProbability) state) := by
  have hsq := fixedPointAmplitudes_square_add032 successProbability hs0 hs1
  have hsq' :
      fixedPointTargetAmplitude successProbability ^ 2 =
        1 - fixedPointSourceAmplitude successProbability ^ 2 := by
    linarith [hsq]
  have hgood :
      (fixedPointTargetAmplitude successProbability : ℂ) ^ 2 =
        1 - (fixedPointSourceAmplitude successProbability : ℂ) ^ 2 := by
    exact_mod_cast hsq'
  simp only [standardPhysicalState032]
  rw [fixedPointSignalTransferMatrix_forward_mulVec_pairState]
  exact standardSignalForward032_eval_formula
    (fixedPointSourceAmplitude successProbability)
    (fixedPointTargetAmplitude successProbability) hgood state

theorem standardSignalAdjoint032_eval_actual
    (successProbability : ℝ)
    (hs0 : 0 ≤ successProbability) (hs1 : successProbability ≤ 1)
    (state : StandardQSPPolynomialState032) :
    standardPhysicalState032
        (fixedPointSourceAmplitude successProbability)
        (fixedPointTargetAmplitude successProbability)
        (standardSignalAdjoint032 state) =
      (fixedPointSignalTransferMatrix successProbability .adjoint).mulVec
        (standardPhysicalState032
          (fixedPointSourceAmplitude successProbability)
          (fixedPointTargetAmplitude successProbability) state) := by
  have hsq := fixedPointAmplitudes_square_add032 successProbability hs0 hs1
  have hsq' :
      fixedPointTargetAmplitude successProbability ^ 2 =
        1 - fixedPointSourceAmplitude successProbability ^ 2 := by
    linarith [hsq]
  have hgood :
      (fixedPointTargetAmplitude successProbability : ℂ) ^ 2 =
        1 - (fixedPointSourceAmplitude successProbability : ℂ) ^ 2 := by
    exact_mod_cast hsq'
  simp only [standardPhysicalState032]
  rw [fixedPointSignalTransferMatrix_adjoint_mulVec_pairState]
  exact standardSignalAdjoint032_eval_formula
    (fixedPointSourceAmplitude successProbability)
    (fixedPointTargetAmplitude successProbability) hgood state

/-! ## Projector phases, exact inverses, and the role-aware source order -/

def standardPhase032 (angle : ℝ) : ℂ :=
  Complex.exp (Complex.I * (angle : ℂ))

def standardSourcePhase032
    (phase : ℂ) (state : StandardQSPPolynomialState032) :
    StandardQSPPolynomialState032 where
  sourceFactor := Polynomial.C phase * state.sourceFactor
  targetFactor := state.targetFactor

def standardTargetPhase032
    (phase : ℂ) (state : StandardQSPPolynomialState032) :
    StandardQSPPolynomialState032 where
  sourceFactor := state.sourceFactor
  targetFactor := Polynomial.C phase * state.targetFactor

def standardSourcePhaseInverse032
    (phase : ℂ) (state : StandardQSPPolynomialState032) :
    StandardQSPPolynomialState032 where
  sourceFactor := Polynomial.C phase⁻¹ * state.sourceFactor
  targetFactor := state.targetFactor

def standardUnitPhase032 (phase : ℂ) : Prop :=
  Complex.normSq phase = 1

theorem standardUnitPhase032_ne_zero
    (phase : ℂ) (hunit : standardUnitPhase032 phase) :
    phase ≠ 0 := by
  intro hzero
  simp [standardUnitPhase032, hzero] at hunit

theorem standardPhase032_unitNormSq (angle : ℝ) :
    standardUnitPhase032 (standardPhase032 angle) := by
  unfold standardUnitPhase032 standardPhase032
  rw [Complex.normSq_eq_norm_sq]
  simp [Complex.norm_exp_I_mul_ofReal]

theorem standardSourcePhaseInverse032_forward032
    (phase : ℂ) (hunit : standardUnitPhase032 phase)
    (state : StandardQSPPolynomialState032) :
    standardSourcePhaseInverse032 phase
        (standardSourcePhase032 phase state) = state := by
  have hne := standardUnitPhase032_ne_zero phase hunit
  cases state with
  | mk sourceFactor targetFactor =>
      simp only [standardSourcePhaseInverse032, standardSourcePhase032]
      apply standardPolynomialState_ext032
      · rw [← mul_assoc, ← Polynomial.C_mul]
        simp [hne]
      · rfl

theorem standardSourcePhase032_eval_actual
    (successProbability : ℝ) (angle : ℝ)
    (state : StandardQSPPolynomialState032) :
    standardPhysicalState032
        (fixedPointSourceAmplitude successProbability)
        (fixedPointTargetAmplitude successProbability)
        (standardSourcePhase032 (standardPhase032 angle) state) =
      (fixedPointProjectorTransferMatrix .source angle).mulVec
        (standardPhysicalState032
          (fixedPointSourceAmplitude successProbability)
          (fixedPointTargetAmplitude successProbability) state) := by
  simp only [standardPhysicalState032]
  rw [fixedPointProjectorTransferMatrix_source_mulVec_pairState]
  apply fixedPointPairState_congr032
  · simp [standardSourcePhase032, standardPhase032, Polynomial.eval_mul]
  · rfl

theorem standardTargetPhase032_eval_actual
    (successProbability : ℝ) (angle : ℝ)
    (state : StandardQSPPolynomialState032) :
    standardPhysicalState032
        (fixedPointSourceAmplitude successProbability)
        (fixedPointTargetAmplitude successProbability)
        (standardTargetPhase032 (standardPhase032 angle) state) =
      (fixedPointProjectorTransferMatrix .target angle).mulVec
        (standardPhysicalState032
          (fixedPointSourceAmplitude successProbability)
          (fixedPointTargetAmplitude successProbability) state) := by
  simp only [standardPhysicalState032]
  rw [fixedPointProjectorTransferMatrix_target_mulVec_pairState]
  apply fixedPointPairState_congr032
  · rfl
  · simp [standardTargetPhase032, standardPhase032, Polynomial.eval_mul]
    ring

def standardPolynomialStep032 :
    FixedPointRoleAwarePhaseStep →
      StandardQSPPolynomialState032 → StandardQSPPolynomialState032
  | .signal .forward => standardSignalForward032
  | .signal .adjoint => standardSignalAdjoint032
  | .projectorPhase .source angle =>
      standardSourcePhase032 (standardPhase032 angle)
  | .projectorPhase .target angle =>
      standardTargetPhase032 (standardPhase032 angle)

theorem standardPolynomialStep032_eval_actual
    (successProbability : ℝ)
    (hs0 : 0 ≤ successProbability) (hs1 : successProbability ≤ 1)
    (step : FixedPointRoleAwarePhaseStep)
    (state : StandardQSPPolynomialState032) :
    standardPhysicalState032
        (fixedPointSourceAmplitude successProbability)
        (fixedPointTargetAmplitude successProbability)
        (standardPolynomialStep032 step state) =
      (fixedPointRoleAwareStepTransferMatrix successProbability step).mulVec
        (standardPhysicalState032
          (fixedPointSourceAmplitude successProbability)
          (fixedPointTargetAmplitude successProbability) state) := by
  cases step with
  | signal direction =>
      cases direction with
      | forward =>
          exact standardSignalForward032_eval_actual
            successProbability hs0 hs1 state
      | adjoint =>
          exact standardSignalAdjoint032_eval_actual
            successProbability hs0 hs1 state
  | projectorPhase role angle =>
      cases role with
      | source =>
          exact standardSourcePhase032_eval_actual
            successProbability angle state
      | target =>
          exact standardTargetPhase032_eval_actual
            successProbability angle state

def standardPolynomialSourceOrder032
    (steps : List FixedPointRoleAwarePhaseStep)
    (initialState : StandardQSPPolynomialState032) :
    StandardQSPPolynomialState032 :=
  steps.foldl
    (fun state step => standardPolynomialStep032 step state) initialState

theorem standardPolynomialSourceOrder032_eval_actual
    (successProbability : ℝ)
    (hs0 : 0 ≤ successProbability) (hs1 : successProbability ≤ 1)
    (steps : List FixedPointRoleAwarePhaseStep)
    (state : StandardQSPPolynomialState032) :
    standardPhysicalState032
        (fixedPointSourceAmplitude successProbability)
        (fixedPointTargetAmplitude successProbability)
        (standardPolynomialSourceOrder032 steps state) =
      fixedPointExecuteSteps successProbability steps
        (standardPhysicalState032
          (fixedPointSourceAmplitude successProbability)
          (fixedPointTargetAmplitude successProbability) state) := by
  induction steps generalizing state with
  | nil => rfl
  | cons first rest ih =>
      change standardPhysicalState032
          (fixedPointSourceAmplitude successProbability)
          (fixedPointTargetAmplitude successProbability)
          (standardPolynomialSourceOrder032 rest
            (standardPolynomialStep032 first state)) =
        fixedPointExecuteSteps successProbability rest
          ((fixedPointRoleAwareStepTransferMatrix successProbability first).mulVec
          (standardPhysicalState032
              (fixedPointSourceAmplitude successProbability)
              (fixedPointTargetAmplitude successProbability) state))
      rw [ih]
      exact congrArg (fixedPointExecuteSteps successProbability rest)
        (standardPolynomialStep032_eval_actual
          successProbability hs0 hs1 first state)

theorem fixedPointSourceOrderTransferMatrix_mulVec_executeSteps032
    (successProbability : ℝ)
    (steps : List FixedPointRoleAwarePhaseStep)
    (state : FixedPointTransferState) :
    (fixedPointSourceOrderTransferMatrix successProbability steps).mulVec state =
      fixedPointExecuteSteps successProbability steps state := by
  unfold fixedPointSourceOrderTransferMatrix fixedPointExecuteSteps
  have foldLaw : ∀ (remaining : List FixedPointRoleAwarePhaseStep)
      (accumulated : FixedPointTransferMatrix)
      (state : FixedPointTransferState),
      (remaining.foldl
          (fun product step =>
            fixedPointRoleAwareStepTransferMatrix successProbability step *
              product)
          accumulated).mulVec state =
        remaining.foldl
          (fun current step =>
            (fixedPointRoleAwareStepTransferMatrix successProbability step).mulVec
              current)
          (accumulated.mulVec state) := by
    intro remaining
    induction remaining with
    | nil => intro accumulated state; rfl
    | cons first rest inductionHypothesis =>
        intro accumulated state
        simp only [List.foldl_cons]
        rw [inductionHypothesis]
        congr 1
        exact (Matrix.mulVec_mulVec state
          (fixedPointRoleAwareStepTransferMatrix successProbability first)
          accumulated).symm
  rw [foldLaw]
  rw [Matrix.one_mulVec]

theorem standardPolynomialSourceOrder032_eval_matrix
    (successProbability : ℝ)
    (hs0 : 0 ≤ successProbability) (hs1 : successProbability ≤ 1)
    (steps : List FixedPointRoleAwarePhaseStep)
    (state : StandardQSPPolynomialState032) :
    standardPhysicalState032
        (fixedPointSourceAmplitude successProbability)
        (fixedPointTargetAmplitude successProbability)
        (standardPolynomialSourceOrder032 steps state) =
      (fixedPointSourceOrderTransferMatrix successProbability steps).mulVec
        (standardPhysicalState032
          (fixedPointSourceAmplitude successProbability)
          (fixedPointTargetAmplitude successProbability) state) := by
  rw [standardPolynomialSourceOrder032_eval_actual
    successProbability hs0 hs1 steps state]
  symm
  exact fixedPointSourceOrderTransferMatrix_mulVec_executeSteps032
    successProbability steps
    (standardPhysicalState032
      (fixedPointSourceAmplitude successProbability)
      (fixedPointTargetAmplitude successProbability) state)

/-! ## Weighted paraunitary invariant -/

def standardWeightedEnergy032
    (x : ℝ) (state : StandardQSPPolynomialState032) : ℝ :=
  Complex.normSq (Polynomial.eval (x : ℂ) state.sourceFactor) +
    (1 - x ^ 2) *
      Complex.normSq (Polynomial.eval (x : ℂ) state.targetFactor)

theorem standardWeightedEnergy032_signalAdjoint
    (x : ℝ) (state : StandardQSPPolynomialState032) :
    standardWeightedEnergy032 x (standardSignalAdjoint032 state) =
      standardWeightedEnergy032 x state := by
  simp [standardWeightedEnergy032, standardSignalAdjoint032,
    standardGoodSquare032, Polynomial.eval_add, Polynomial.eval_mul,
    Complex.normSq_add, Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im]
  have hxr : ((x : ℂ) ^ 2).re = x ^ 2 := by
    norm_num [pow_two, Complex.mul_re]
  have hxi : ((x : ℂ) ^ 2).im = 0 := by
    norm_num [pow_two, Complex.mul_im]
  rw [hxr, hxi]
  ring

theorem standardWeightedEnergy032_sourcePhase
    (x : ℝ) (angle : ℝ) (state : StandardQSPPolynomialState032) :
    standardWeightedEnergy032 x
        (standardSourcePhase032 (standardPhase032 angle) state) =
      standardWeightedEnergy032 x state := by
  simp [standardWeightedEnergy032, standardSourcePhase032,
    standardPhase032, Polynomial.eval_mul,
    Complex.normSq_eq_norm_sq]

/-! ## Symbolic signal-only base rounds and the one-query coefficient law -/

def standardQ0State032 : StandardQSPPolynomialState032 where
  sourceFactor := 1
  targetFactor := 0

theorem standardInverseSourceCoeff_succ032
    (state : StandardQSPPolynomialState032) (degree : ℕ)
    (hpos : 1 ≤ degree)
    (hdegree : state.targetFactor.degree < (degree : WithBot ℕ)) :
    (standardSignalAdjoint032 state).sourceFactor.coeff (degree + 1) =
      state.sourceFactor.coeff degree - state.targetFactor.coeff (degree - 1) := by
  change (Polynomial.X * state.sourceFactor +
      (1 - (Polynomial.X : Polynomial ℂ) ^ 2) * state.targetFactor).coeff
        (degree + 1) = _
  rw [sub_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
    Polynomial.coeff_sub]
  simp only [one_mul]
  have hdegree' : state.targetFactor.degree <
      ((degree + 1 : ℕ) : WithBot ℕ) := by
    exact lt_of_lt_of_le hdegree
      (WithBot.coe_le_coe.mpr (Nat.le_add_right degree 1))
  rw [Polynomial.coeff_eq_zero_of_degree_lt hdegree']
  have hindex : degree - 1 + 2 = degree + 1 := by omega
  rw [← hindex, Polynomial.coeff_X_pow_mul]
  ring

theorem standardInverseSourceCoeff_succ_cancel032
    (state : StandardQSPPolynomialState032) (degree : ℕ)
    (hpos : 1 ≤ degree)
    (hdegree : state.targetFactor.degree < (degree : WithBot ℕ))
    (hcoeff : state.sourceFactor.coeff degree =
      state.targetFactor.coeff (degree - 1)) :
    (standardSignalAdjoint032 state).sourceFactor.coeff (degree + 1) = 0 := by
  rw [standardInverseSourceCoeff_succ032 state degree hpos hdegree, hcoeff]
  ring

end
end SpectralSamplingProof.Analytic
