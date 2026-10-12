import QLean.SignalProcessing.NativeConcreteP18QSPWitness

/-!
# M13b: phase-conjugate two-frame words

Negating only projector angles preserves the alternating source/target frame
discipline.  The resulting word has the entrywise complex-conjugate transfer
matrix, while retaining the same initial and final active frames.
-/

set_option autoImplicit false

namespace M13bConjugatePhaseWord

open SpectralSamplingProof.Analytic
open NativeConcreteP18QSPWitness
open NativeQSPWitnessTransferModel
open NativeQSPWitnessTwoFrameModel

noncomputable section

/-- Phase conjugation keeps signal direction and negates only projector
angles. -/
def conjugateStep119 : FixedPointRoleAwarePhaseStep → FixedPointRoleAwarePhaseStep
  | .signal direction => .signal direction
  | .projectorPhase role angle => .projectorPhase role (-angle)

def conjugateWord119 (steps : List FixedPointRoleAwarePhaseStep) :
    List FixedPointRoleAwarePhaseStep :=
  steps.map conjugateStep119

/-- Conjugate a finite program without evaluating or discarding its angle
syntax.  This is the branch used by the Hermitian selector. -/
def conjugatePhaseProgramStep119 :
    NativeFixedPointPrimitive.PhaseProgramStep →
      NativeFixedPointPrimitive.PhaseProgramStep
  | .signal direction => .signal direction
  | .projectorPhase role angle => .projectorPhase role (.neg angle)

def conjugatePhaseProgram119
    (program : List NativeFixedPointPrimitive.PhaseProgramStep) :
    List NativeFixedPointPrimitive.PhaseProgramStep :=
  program.map conjugatePhaseProgramStep119

theorem conjugatePhaseProgramStep119_eval
    (symbolValue : String → ℝ)
    (step : NativeFixedPointPrimitive.PhaseProgramStep) :
    NativeFixedPointPrimitive.PhaseProgramStep.eval symbolValue
        (conjugatePhaseProgramStep119 step) =
      conjugateStep119
        (NativeFixedPointPrimitive.PhaseProgramStep.eval symbolValue step) := by
  cases step with
  | signal direction => rfl
  | projectorPhase role angle =>
      simp [conjugatePhaseProgramStep119,
        NativeFixedPointPrimitive.PhaseProgramStep.eval,
        conjugateStep119, VerifiedCircuitCore.AngleExpr.eval]

theorem conjugatePhaseProgram119_eval
    (symbolValue : String → ℝ)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep) :
    (conjugatePhaseProgram119 program).map
        (NativeFixedPointPrimitive.PhaseProgramStep.eval symbolValue) =
      conjugateWord119
        (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval symbolValue)) := by
  simp only [conjugatePhaseProgram119, conjugateWord119, List.map_map]
  apply List.map_congr_left
  intro step member
  exact conjugatePhaseProgramStep119_eval symbolValue step

/-- Entrywise, rather than transpose, complex conjugation of a transfer
matrix. -/
def entrywiseConj (transfer : FixedPointTransferMatrix) :
    FixedPointTransferMatrix :=
  fun row column => (starRingEnd ℂ) (transfer row column)

theorem frameAfter_conjugateStep
    (frame : ActiveFrame) (step : FixedPointRoleAwarePhaseStep) :
    frameAfter frame (conjugateStep119 step) = frameAfter frame step := by
  cases frame with
  | source =>
      cases step with
      | signal direction => rfl
      | projectorPhase role angle => cases role <;> rfl
  | target =>
      cases step with
      | signal direction => rfl
      | projectorPhase role angle => cases role <;> rfl

/-- Phase conjugation preserves the role-aware two-frame typing of a word. -/
theorem FrameWord.conjugate
    {initial final : ActiveFrame} {steps : List FixedPointRoleAwarePhaseStep}
    (wellFormed : FrameWord initial steps final) :
    FrameWord initial (conjugateWord119 steps) final := by
  induction wellFormed with
  | nil frame =>
      simpa [conjugateWord119] using (FrameWord.nil frame)
  | @cons current next final step rest transition remaining inductionHypothesis =>
      simp only [conjugateWord119, List.map_cons]
      refine FrameWord.cons ?_ inductionHypothesis
      rw [frameAfter_conjugateStep]
      exact transition

theorem entrywiseConj_one :
    entrywiseConj (1 : FixedPointTransferMatrix) = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [entrywiseConj]

theorem entrywiseConj_mul (left right : FixedPointTransferMatrix) :
    entrywiseConj (left * right) = entrywiseConj left * entrywiseConj right := by
  ext row column
  simp [entrywiseConj, Matrix.mul_apply]

theorem entrywiseConj_signal
    (successProbability : ℝ) (direction : VerifiedCircuitCore.SignalDirection) :
    entrywiseConj (fixedPointSignalTransferMatrix successProbability direction) =
      fixedPointSignalTransferMatrix successProbability direction := by
  ext row column
  cases direction <;> fin_cases row <;> fin_cases column <;>
    simp [entrywiseConj, fixedPointSignalTransferMatrix]

theorem entrywiseConj_projectorPhase
    (role : FixedPointProjectorRole) (angle : ℝ) :
    entrywiseConj (fixedPointProjectorTransferMatrix role angle) =
      fixedPointProjectorTransferMatrix role (-angle) := by
  have hphase :
      (starRingEnd ℂ) (Complex.exp (Complex.I * (angle : ℂ))) =
        Complex.exp (Complex.I * ((-angle : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj]
    have hstar :
        (starRingEnd ℂ) (Complex.I * (angle : ℂ)) =
          -(Complex.I * (angle : ℂ)) := by
      simp
    rw [hstar]
    congr 1
    simp only [Complex.ofReal_neg]
    ring
  ext row column
  cases role <;> fin_cases row <;> fin_cases column <;>
    simp [entrywiseConj, fixedPointProjectorTransferMatrix,
      fixedPointSourceIndex, fixedPointTargetIndex, hphase]

theorem entrywiseConj_step
    (successProbability : ℝ) (step : FixedPointRoleAwarePhaseStep) :
    entrywiseConj (fixedPointRoleAwareStepTransferMatrix successProbability step) =
      fixedPointRoleAwareStepTransferMatrix successProbability (conjugateStep119 step) := by
  cases step with
  | signal direction =>
      exact entrywiseConj_signal successProbability direction
  | projectorPhase role angle =>
      exact entrywiseConj_projectorPhase role angle

/-- The independent two-dimensional evaluator of the conjugate word is the
entrywise complex conjugate of the original evaluator. -/
theorem abstractTransferWord_conjugate
    (successProbability : ℝ) (steps : List FixedPointRoleAwarePhaseStep) :
    abstractTransferWord successProbability (conjugateWord119 steps) =
      entrywiseConj (abstractTransferWord successProbability steps) := by
  induction steps with
  | nil =>
      change (1 : FixedPointTransferMatrix) = entrywiseConj 1
      rw [entrywiseConj_one]
  | cons first rest inductionHypothesis =>
      change abstractTransferWord successProbability (conjugateWord119 rest) *
          fixedPointRoleAwareStepTransferMatrix successProbability
            (conjugateStep119 first) =
        entrywiseConj
          (abstractTransferWord successProbability rest *
            fixedPointRoleAwareStepTransferMatrix successProbability first)
      rw [entrywiseConj_mul, inductionHypothesis, entrywiseConj_step]

end

end M13bConjugatePhaseWord
