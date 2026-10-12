import QLean.History.Implementation.HistoryPipelineExecutableSelectorAngles

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open HistoryBlockEncoding
open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

def selectorBasis119 (low high : Bool) : QubitBasis 2 :=
  fun wire => if wire = (0 : Fin 2) then low else high

@[simp] theorem selectorBasis119_low (low high : Bool) :
    selectorBasis119 low high (0 : Fin 2) = low := by
  simp [selectorBasis119]

@[simp] theorem selectorBasis119_high (low high : Bool) :
    selectorBasis119 low high (1 : Fin 2) = high := by
  simp [selectorBasis119]

@[simp] theorem selectorBasis119_eq_iff
    (low high low' high' : Bool) :
    selectorBasis119 low high = selectorBasis119 low' high' ↔
      low = low' ∧ high = high' := by
  constructor
  · intro equal
    exact ⟨congrFun equal 0, congrFun equal 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem replaceQubitWire_selectorBasis119_low
    (low high value : Bool) :
    replaceQubitWire (selectorBasis119 low high) (0 : Fin 2) value =
      selectorBasis119 value high := by
  funext wire
  fin_cases wire <;> simp [replaceQubitWire]

@[simp] theorem replaceQubitWire_selectorBasis119_high
    (low high value : Bool) :
    replaceQubitWire (selectorBasis119 low high) (1 : Fin 2) value =
      selectorBasis119 low value := by
  funext wire
  fin_cases wire <;> simp [replaceQubitWire]

@[simp] theorem cnotBasisAction_selectorBasis119 (low high : Bool) :
    cnotBasisAction (1 : Fin 2) (0 : Fin 2) (selectorBasis119 low high) =
      selectorBasis119 (low != high) high := by
  funext wire
  fin_cases wire <;> simp [cnotBasisAction, xorWire]

theorem applyOperator_analyticCnotOperator_state119
    {qubits : Nat} (control target : Fin qubits)
    (different : control ≠ target)
    (state : State (QubitBasis qubits)) :
    applyOperator
        (VerifiedCircuitCore.analyticCnotOperator control target)
        state =
      state ∘ cnotBasisAction control target := by
  change applyOperator
    (deterministicOperator (cnotBasisAction control target)) state = _
  rw [deterministicOperator_eq_permMatrix_of_involutive
    (cnotBasisAction control target)
    (cnotBasisAction_involutive control target different)]
  exact applyOperator_permMatrix
    (involutiveBasisEquiv (cnotBasisAction control target)
      (cnotBasisAction_involutive control target different)) state

def selectorLocalParameters119 (taylorOrder : Nat) (omega : ℝ) :
    HistorySelectorPreparationParameters 2 :=
  selectorPreparationParameters119 (0 : Fin 2) (1 : Fin 2)
    (by decide) taylorOrder omega

def selectorLocalOperator119 (taylorOrder : Nat) (omega : ℝ) :
    Operator (QubitBasis 2) :=
  historySelectorPreparationOperator (fun _ => 0)
    (selectorLocalParameters119 taylorOrder omega)

theorem selectorLocalOperator119_zero_zero
    (taylorOrder : Nat) (omega : ℝ) :
    applyOperator (selectorLocalOperator119 taylorOrder omega)
        (basisKet (selectorBasis119 false false))
        (selectorBasis119 false false) =
      (Real.cos (selectorHighAngle119 taylorOrder omega / 2) *
        Real.cos (selectorLowAngle119 omega) : ℂ) := by
  unfold selectorLocalOperator119 historySelectorPreparationOperator
  simp only [operatorSequence, applyOperator_mul, Matrix.one_mul,
    selectorLocalParameters119, selectorPreparationParameters119,
    AngleExpr.eval]
  rw [applyOperator_analyticCnotOperator_state119 (1 : Fin 2) (0 : Fin 2)
    (by decide)]
  simp only [Function.comp_apply]
  rw [applyOperator_embedSingleQubitOperator_state]
  rw [applyOperator_analyticCnotOperator_state119 (1 : Fin 2) (0 : Fin 2)
    (by decide)]
  simp only [Function.comp_apply]
  simp_rw [applyOperator_embedSingleQubitOperator_state]
  simp [localRy, basisKet]
  rw [show (selectorLowAngle119 omega : ℂ) =
      (selectorLowAngle119 omega : ℂ) / 2 +
        (selectorLowAngle119 omega : ℂ) / 2 by ring]
  rw [Complex.cos_add]
  ring

theorem selectorLocalOperator119_zero_one
    (taylorOrder : Nat) (omega : ℝ) :
    applyOperator (selectorLocalOperator119 taylorOrder omega)
        (basisKet (selectorBasis119 false false))
        (selectorBasis119 true false) =
      (Real.cos (selectorHighAngle119 taylorOrder omega / 2) *
        Real.sin (selectorLowAngle119 omega) : ℂ) := by
  unfold selectorLocalOperator119 historySelectorPreparationOperator
  simp only [operatorSequence, applyOperator_mul, Matrix.one_mul,
    selectorLocalParameters119, selectorPreparationParameters119,
    AngleExpr.eval]
  rw [applyOperator_analyticCnotOperator_state119 (1 : Fin 2) (0 : Fin 2)
    (by decide)]
  simp only [Function.comp_apply]
  rw [applyOperator_embedSingleQubitOperator_state]
  rw [applyOperator_analyticCnotOperator_state119 (1 : Fin 2) (0 : Fin 2)
    (by decide)]
  simp only [Function.comp_apply]
  simp_rw [applyOperator_embedSingleQubitOperator_state]
  simp [localRy, basisKet]
  rw [show (selectorLowAngle119 omega : ℂ) =
      (selectorLowAngle119 omega : ℂ) / 2 +
        (selectorLowAngle119 omega : ℂ) / 2 by ring]
  rw [Complex.sin_add]
  ring

theorem selectorLocalOperator119_one_zero
    (taylorOrder : Nat) (omega : ℝ) :
    applyOperator (selectorLocalOperator119 taylorOrder omega)
        (basisKet (selectorBasis119 false false))
        (selectorBasis119 false true) =
      (Real.sin (selectorHighAngle119 taylorOrder omega / 2) : ℂ) := by
  unfold selectorLocalOperator119 historySelectorPreparationOperator
  simp only [operatorSequence, applyOperator_mul, Matrix.one_mul,
    selectorLocalParameters119, selectorPreparationParameters119,
    AngleExpr.eval]
  rw [applyOperator_analyticCnotOperator_state119 (1 : Fin 2) (0 : Fin 2)
    (by decide)]
  simp only [Function.comp_apply]
  rw [applyOperator_embedSingleQubitOperator_state]
  rw [applyOperator_analyticCnotOperator_state119 (1 : Fin 2) (0 : Fin 2)
    (by decide)]
  simp only [Function.comp_apply]
  simp_rw [applyOperator_embedSingleQubitOperator_state]
  simp [localRy, basisKet]
  have lowIdentity :
      Complex.cos ((selectorLowAngle119 omega : ℂ) / 2) *
          Complex.cos ((selectorLowAngle119 omega : ℂ) / 2) +
        Complex.sin ((selectorLowAngle119 omega : ℂ) / 2) *
          Complex.sin ((selectorLowAngle119 omega : ℂ) / 2) = 1 := by
    calc
      _ = Complex.cos
          ((selectorLowAngle119 omega : ℂ) / 2 -
            (selectorLowAngle119 omega : ℂ) / 2) := by
              rw [Complex.cos_sub]
      _ = 1 := by simp
  calc
    _ = (Complex.cos ((selectorLowAngle119 omega : ℂ) / 2) *
          Complex.cos ((selectorLowAngle119 omega : ℂ) / 2) +
        Complex.sin ((selectorLowAngle119 omega : ℂ) / 2) *
          Complex.sin ((selectorLowAngle119 omega : ℂ) / 2)) *
        Complex.sin
          ((selectorHighAngle119 taylorOrder omega : ℂ) / 2) := by ring
    _ = 1 * Complex.sin
          ((selectorHighAngle119 taylorOrder omega : ℂ) / 2) := by
      rw [lowIdentity]
    _ = _ := by ring

theorem selectorLocalOperator119_one_one
    (taylorOrder : Nat) (omega : ℝ) :
    applyOperator (selectorLocalOperator119 taylorOrder omega)
        (basisKet (selectorBasis119 false false))
        (selectorBasis119 true true) = 0 := by
  unfold selectorLocalOperator119 historySelectorPreparationOperator
  simp only [operatorSequence, applyOperator_mul, Matrix.one_mul,
    selectorLocalParameters119, selectorPreparationParameters119,
    AngleExpr.eval]
  rw [applyOperator_analyticCnotOperator_state119 (1 : Fin 2) (0 : Fin 2)
    (by decide)]
  simp only [Function.comp_apply]
  rw [applyOperator_embedSingleQubitOperator_state]
  rw [applyOperator_analyticCnotOperator_state119 (1 : Fin 2) (0 : Fin 2)
    (by decide)]
  simp only [Function.comp_apply]
  simp_rw [applyOperator_embedSingleQubitOperator_state]
  simp [localRy, basisKet]
  ring

theorem selectorLocalOperator119_lambda_zero
    (taylorOrder : Nat) {omega : ℝ} (omegaNonnegative : 0 ≤ omega) :
    applyOperator (selectorLocalOperator119 taylorOrder omega)
        (basisKet (selectorBasis119 false false))
        (selectorBasis119 false false) =
      (Real.sqrt
        (HistoryBlockEncoding.HistoryLCU.lambda taylorOrder omega ⟨0, by decide⟩ /
          selectorAlpha119 taylorOrder omega) : ℂ) := by
  rw [selectorLocalOperator119_zero_zero]
  simpa [HistoryBlockEncoding.HistoryLCU.lambda] using
    congrArg (fun value : ℝ => (value : ℂ))
      (selectorBranchZeroAmplitude119 taylorOrder omegaNonnegative)

theorem selectorLocalOperator119_lambda_one
    (taylorOrder : Nat) {omega : ℝ} (omegaNonnegative : 0 ≤ omega) :
    applyOperator (selectorLocalOperator119 taylorOrder omega)
        (basisKet (selectorBasis119 false false))
        (selectorBasis119 true false) =
      (Real.sqrt
        (HistoryBlockEncoding.HistoryLCU.lambda taylorOrder omega ⟨1, by decide⟩ /
          selectorAlpha119 taylorOrder omega) : ℂ) := by
  rw [selectorLocalOperator119_zero_one]
  simpa [HistoryBlockEncoding.HistoryLCU.lambda] using
    congrArg (fun value : ℝ => (value : ℂ))
      (selectorBranchOneAmplitude119 taylorOrder omegaNonnegative)

theorem selectorLocalOperator119_lambda_two
    (taylorOrder : Nat) {omega : ℝ} (omegaNonnegative : 0 ≤ omega) :
    applyOperator (selectorLocalOperator119 taylorOrder omega)
        (basisKet (selectorBasis119 false false))
        (selectorBasis119 false true) =
      (Real.sqrt
        (HistoryBlockEncoding.HistoryLCU.lambda taylorOrder omega ⟨2, by decide⟩ /
          selectorAlpha119 taylorOrder omega) : ℂ) := by
  rw [selectorLocalOperator119_one_zero]
  exact congrArg (fun value : ℝ => (value : ℂ))
    (selectorBranchTwoAmplitude119 taylorOrder omegaNonnegative)

theorem selectorLocalOperator119_lambda_three
    (taylorOrder : Nat) {omega : ℝ} :
    applyOperator (selectorLocalOperator119 taylorOrder omega)
        (basisKet (selectorBasis119 false false))
        (selectorBasis119 true true) =
      (Real.sqrt
        (HistoryBlockEncoding.HistoryLCU.lambda taylorOrder omega ⟨3, by decide⟩ /
          selectorAlpha119 taylorOrder omega) : ℂ) := by
  rw [selectorLocalOperator119_one_one]
  simpa using congrArg (fun value : ℝ => (value : ℂ))
    (selectorBranchThreeAmplitude119 taylorOrder (omega := omega))

end

end ExecutableHistoryExecutableHistory
