import QLean.SignalProcessing.M13bFiniteOuterSemantics
import QLean.SignalProcessing.M13bFiniteOuterTwoFrame
import QLean.SignalProcessing.M13bHermitianOuterScalar
import QLean.SignalProcessing.M13bTwoFrameHermitianDilation

/-! Abstract-width outer reflection transport.  The hypotheses concern only
the actions of the inner program and target phase on explicitly supplied
frames.  They are proved from the actual common signal in its instantiation.
Neither a legacy circuit equality nor an assumed final reflection is used. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace M13bFiniteOuterIntertwining

open VerifiedCircuitCore M13bFiniteOuterCompiler M13bFiniteOuterSemantics
open M13bExternallyControlledCompute M13bControlledStateSemantics
open NativeQSPWitnessTransferModel SpectralSamplingProof.Analytic
open NativeQSPWitnessTwoFrameModel M13bFiniteOuterTwoFrame
open M13bHermitianOuterScalar

noncomputable section

def controlFrame {n : Nat} (frame : Matrix (QubitBasis n) (Fin 2) ℂ) :
    Matrix (QubitBasis (n + 3)) ControlTransferIndex119 ℂ :=
  fun output index =>
    M13bTwoFrameHermitianDilation.controlledFrame119 n index.1 frame output index.2

theorem hermitianCompute_intertwines {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (sourceFrame targetFrame : Matrix (QubitBasis n) (Fin 2) ℂ)
    (transfer : FixedPointTransferMatrix)
    (original : Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.word program) * sourceFrame = targetFrame * transfer)
    (conjugate : Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.word (M13bConjugatePhaseWord.conjugatePhaseProgram119 program)) * sourceFrame =
        targetFrame * M13bConjugatePhaseWord.entrywiseConj transfer) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbols) (plan.hermitianCompute program) *
        controlFrame sourceFrame =
      controlFrame targetFrame * sameDirectionHermitianTransfer119 transfer := by
  classical
  have originalApply (index : Fin 2) :
      circuitAction symbols (plan.word program) (fun input => sourceFrame input index) =
        fun output => (targetFrame * transfer) output index := by
    funext output
    simpa [circuitAction, applyOperator, Matrix.mulVec, dotProduct, Matrix.mul_apply] using
      congrFun (congrFun original output) index
  have conjugateApply (index : Fin 2) :
      circuitAction symbols
          (plan.word (M13bConjugatePhaseWord.conjugatePhaseProgram119 program))
          (fun input => sourceFrame input index) =
        fun output => (targetFrame * M13bConjugatePhaseWord.entrywiseConj transfer) output index := by
    funext output
    simpa [circuitAction, applyOperator, Matrix.mulVec, dotProduct, Matrix.mul_apply] using
      congrFun (congrFun conjugate output) index
  have controlledApply (bit : Bool) (T : FixedPointTransferMatrix) (index : Fin 2) :
      m13bControlledState n bit (fun input => (targetFrame * T) input index) =
        fun output =>
          (M13bTwoFrameHermitianDilation.controlledFrame119 n bit targetFrame * T) output index := by
    funext output
    change M13bTwoFrameHermitianDilation.controlledFrame119 n bit
      (targetFrame * T) output index = _
    rw [M13bTwoFrameHermitianDilation.controlledFrame119_mul]
  ext output column
  rcases column with ⟨bit, index⟩
  change circuitAction symbols (plan.hermitianCompute program)
    (m13bControlledState n bit (fun input => sourceFrame input index)) output = _
  cases bit with
  | false =>
      rw [hermitianCompute_apply_false symbols plan layout]
      unfold hermitianOutput hadamardFalseState hadamardTrueState
      rw [originalApply index, conjugateApply index]
      rw [controlledApply false transfer index, controlledApply true transfer index,
        controlledApply false (M13bConjugatePhaseWord.entrywiseConj transfer) index,
        controlledApply true (M13bConjugatePhaseWord.entrywiseConj transfer) index]
      fin_cases index <;>
        simp [controlFrame, sameDirectionHermitianTransfer119, controlHadamard119,
          phaseConjugateBlock119, Matrix.mul_apply, Fintype.sum_prod_type,
          Fin.sum_univ_two, localH] <;> field_simp <;> ring
  | true =>
      rw [hermitianCompute_apply_true symbols plan layout]
      unfold hadamardFalseState hadamardTrueState
      rw [originalApply index, conjugateApply index]
      rw [controlledApply false transfer index, controlledApply true transfer index,
        controlledApply false (M13bConjugatePhaseWord.entrywiseConj transfer) index,
        controlledApply true (M13bConjugatePhaseWord.entrywiseConj transfer) index]
      fin_cases index <;>
        simp [controlFrame, sameDirectionHermitianTransfer119, controlHadamard119,
          phaseConjugateBlock119, Matrix.mul_apply, Fintype.sum_prod_type,
          Fin.sum_univ_two, localH] <;> field_simp <;> ring

theorem successReflection_intertwines {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (angle : AngleExpr) (angle_value : angle.eval symbols = Real.pi)
    (targetFrame : Matrix (QubitBasis n) (Fin 2) ℂ)
    (phase : Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.word [.projectorPhase .target angle]) * targetFrame =
        targetFrame * fixedPointProjectorTransferMatrix .target Real.pi) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbols)
        (plan.successReflection angle) * controlFrame targetFrame =
      controlFrame targetFrame * hermitianSuccessReflectionTransfer119 := by
  classical
  have phaseApply (index : Fin 2) :
      circuitAction symbols (plan.word [.projectorPhase .target angle])
          (fun input => targetFrame input index) =
        fun output => (targetFrame * fixedPointProjectorTransferMatrix .target Real.pi)
          output index := by
    funext output
    simpa [circuitAction, applyOperator, Matrix.mulVec, dotProduct, Matrix.mul_apply] using
      congrFun (congrFun phase output) index
  have controlledApply (bit : Bool) (T : FixedPointTransferMatrix) (index : Fin 2) :
      m13bControlledState n bit (fun input => (targetFrame * T) input index) =
        fun output =>
          (M13bTwoFrameHermitianDilation.controlledFrame119 n bit targetFrame * T) output index := by
    funext output
    change M13bTwoFrameHermitianDilation.controlledFrame119 n bit
      (targetFrame * T) output index = _
    rw [M13bTwoFrameHermitianDilation.controlledFrame119_mul]
  have hpi : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  ext output column
  rcases column with ⟨bit, index⟩
  change circuitAction symbols (plan.successReflection angle)
    (m13bControlledState n bit (fun input => targetFrame input index)) output = _
  cases bit with
  | false =>
      rw [successReflection_apply_false symbols plan layout angle angle_value, phaseApply index,
        controlledApply false (fixedPointProjectorTransferMatrix .target Real.pi) index]
      fin_cases index <;>
        simp [controlFrame, hermitianSuccessReflectionTransfer119,
          Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
          fixedPointProjectorTransferMatrix, fixedPointSourceIndex,
          fixedPointTargetIndex, M13bTwoFrameHermitianDilation.controlledFrame119, hpi]
  | true =>
      rw [successReflection_apply_true symbols plan layout angle angle_value]
      fin_cases index <;>
        simp [controlFrame, hermitianSuccessReflectionTransfer119,
          Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
          M13bTwoFrameHermitianDilation.controlledFrame119]

/-- Transfer of the complete finite CP03 outer circuit.  Reverse execution
is derived from unitarity, and the target phase is proved separately.  The
frames may be degenerate, so this lemma also serves endpoint constructions. -/
theorem compile_intertwines {n : Nat} (symbols : String → ℝ)
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (angle : AngleExpr) (angle_value : angle.eval symbols = Real.pi)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (sourceFrame targetFrame : Matrix (QubitBasis n) (Fin 2) ℂ)
    (transfer : FixedPointTransferMatrix)
    (original : Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.word program) * sourceFrame = targetFrame * transfer)
    (conjugate : Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.word (M13bConjugatePhaseWord.conjugatePhaseProgram119 program)) * sourceFrame =
        targetFrame * M13bConjugatePhaseWord.entrywiseConj transfer)
    (phase : Circuit.denote (primitiveGateOperatorWithSymbols symbols)
      (plan.word [.projectorPhase .target angle]) * targetFrame =
        targetFrame * fixedPointProjectorTransferMatrix .target Real.pi)
    (unitary : Matrix.conjTranspose transfer * transfer = 1) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbols)
        (plan.compile program angle) * controlFrame sourceFrame =
      controlFrame sourceFrame *
        (Matrix.conjTranspose (sameDirectionHermitianTransfer119 transfer) *
          hermitianSuccessReflectionTransfer119 * sameDirectionHermitianTransfer119 transfer) := by
  let compute := Circuit.denote (primitiveGateOperatorWithSymbols symbols)
    (plan.hermitianCompute program)
  let reflect := Circuit.denote (primitiveGateOperatorWithSymbols symbols)
    (plan.successReflection angle)
  let S := controlFrame sourceFrame
  let T := controlFrame targetFrame
  let H := sameDirectionHermitianTransfer119 transfer
  let R := hermitianSuccessReflectionTransfer119
  have forward : compute * S = T * H :=
    hermitianCompute_intertwines symbols plan layout program
      sourceFrame targetFrame transfer original conjugate
  have reflection : reflect * T = T * R :=
    successReflection_intertwines symbols plan layout angle angle_value targetFrame phase
  have computeUnitary : Matrix.conjTranspose compute * compute = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp (primitiveCircuit_denote_mem_unitaryGroup symbols _)
  have hunitary : Matrix.conjTranspose H * H = 1 :=
    sameDirectionHermitianTransfer119_unitary transfer unitary
  have hright : H * Matrix.conjTranspose H = 1 :=
    (Matrix.mem_unitaryGroup_iff).mp ((Matrix.mem_unitaryGroup_iff').mpr hunitary)
  have backward : Matrix.conjTranspose compute * T = S * Matrix.conjTranspose H := by
    calc
      Matrix.conjTranspose compute * T =
          Matrix.conjTranspose compute * (T * (H * Matrix.conjTranspose H)) := by
            rw [hright]; simp
      _ = Matrix.conjTranspose compute * ((T * H) * Matrix.conjTranspose H) := by
            rw [Matrix.mul_assoc]
      _ = Matrix.conjTranspose compute * ((compute * S) * Matrix.conjTranspose H) := by
            rw [forward]
      _ = (Matrix.conjTranspose compute * compute) * S * Matrix.conjTranspose H := by
            simp only [← Matrix.mul_assoc]
      _ = S * Matrix.conjTranspose H := by rw [computeUnitary]; simp
  rw [compile_denotation]
  simp only [Matrix.star_eq_conjTranspose]
  change (Matrix.conjTranspose compute * reflect * compute) * S =
    S * (Matrix.conjTranspose H * R * H)
  calc
    (Matrix.conjTranspose compute * reflect * compute) * S =
        Matrix.conjTranspose compute * reflect * (compute * S) := Matrix.mul_assoc _ _ _
    _ = Matrix.conjTranspose compute * reflect * (T * H) := by rw [forward]
    _ = Matrix.conjTranspose compute * (reflect * T) * H := by simp only [Matrix.mul_assoc]
    _ = Matrix.conjTranspose compute * (T * R) * H := by rw [reflection]
    _ = (Matrix.conjTranspose compute * T) * R * H := by simp only [Matrix.mul_assoc]
    _ = (S * Matrix.conjTranspose H) * R * H := by rw [backward]
    _ = S * (Matrix.conjTranspose H * R * H) := by simp only [Matrix.mul_assoc]

/-- Small wrappers keep applications at concrete scientific register widths
from unfolding finite-basis arithmetic while the theorem is elaborated. -/
def controlLeftProduct {n : Nat} (operator : Operator (QubitBasis (n + 3)))
    (frame : Matrix (QubitBasis n) (Fin 2) ℂ) :
    Matrix (QubitBasis (n + 3)) ControlTransferIndex119 ℂ :=
  operator * controlFrame frame

def controlRightProduct {n : Nat} (frame : Matrix (QubitBasis n) (Fin 2) ℂ)
    (transfer : Matrix ControlTransferIndex119 ControlTransferIndex119 ℂ) :
    Matrix (QubitBasis (n + 3)) ControlTransferIndex119 ℂ :=
  controlFrame frame * transfer

def outerTransfer (transfer : FixedPointTransferMatrix) :
    Matrix ControlTransferIndex119 ControlTransferIndex119 ℂ :=
  Matrix.conjTranspose (sameDirectionHermitianTransfer119 transfer) *
    hermitianSuccessReflectionTransfer119 * sameDirectionHermitianTransfer119 transfer

def programTransfer (p : ℝ) (program : List NativeFixedPointPrimitive.PhaseProgramStep) :
    FixedPointTransferMatrix :=
  abstractTransferWord p
    (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0)))

/-- Connect the new word theorem to the complete common outer compiler.
The same statement can be instantiated with strict, kernel, or endpoint
frames once their four physical step equations have been established. -/
theorem compile_intertwines_of_twoFrame {n : Nat}
    (plan : Plan n) (layout : plan.layout = m13bExternalControlLayout n)
    (evaluation : PlanPhaseEvaluation plan)
    (p : ℝ) (sourceFrame targetFrame : Matrix (QubitBasis n) (Fin 2) ℂ)
    (physical : PlanTwoFrameWitness plan p sourceFrame targetFrame)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (wellFormed : FrameWord .source
      (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))) .target)
    (unitary : Matrix.conjTranspose (programTransfer p program) * programTransfer p program = 1)
    (angle : AngleExpr := .pi)
    (angle_value : angle.eval (fun _ : String => 0) = Real.pi := by rfl) :
    controlLeftProduct (circuitDenotation (plan.compile program angle)) sourceFrame =
      controlRightProduct sourceFrame (outerTransfer (abstractTransferWord p
        (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))))) := by
  apply compile_intertwines (fun _ : String => 0) plan layout angle angle_value program
    sourceFrame targetFrame _
  · change frameLeftProduct (circuitDenotation (plan.word program)) sourceFrame = _
    rw [word_denotation_eval plan evaluation]
    exact realOperatorWord_intertwines plan p sourceFrame targetFrame physical wellFormed
  · change frameLeftProduct (circuitDenotation (plan.word
        (M13bConjugatePhaseWord.conjugatePhaseProgram119 program))) sourceFrame = _
    rw [word_denotation_eval plan evaluation,
      M13bConjugatePhaseWord.conjugatePhaseProgram119_eval]
    have h := realOperatorWord_intertwines plan p sourceFrame targetFrame physical
      (M13bConjugatePhaseWord.FrameWord.conjugate wellFormed)
    rw [M13bConjugatePhaseWord.abstractTransferWord_conjugate] at h
    exact h
  · change frameLeftProduct (circuitDenotation
      (plan.word [.projectorPhase .target angle])) targetFrame = _
    rw [word_denotation_eval plan evaluation]
    simpa only [List.map_cons, List.map_nil, NativeFixedPointPrimitive.PhaseProgramStep.eval,
      angle_value, realOperatorWord, operatorSequence, one_mul, frameLeftProduct] using
        physical.target_phase Real.pi
  · exact unitary

end
end M13bFiniteOuterIntertwining
