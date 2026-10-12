import QLean.History.Implementation.HistoryPipelineH2QEntry

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open HistoryBlockEncoding

noncomputable section

/-- Sound branch weights when `omegaH <= 1`: the within-clock branch has
norm budget one because its idle sector contains a unit entry. -/
def correctedLambda119 (taylorOrder : Nat) : Fin 4 → ℝ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => Real.sqrt (taylorOrder + 1)
  | ⟨3, _⟩ => 0

def correctedAlpha119 (taylorOrder : Nat) : ℝ :=
  2 + Real.sqrt (taylorOrder + 1)

def correctedCastMatrix119
    {left right : Type*} (matrix : Matrix left right ℚ) :
    Matrix left right ℝ :=
  fun output input => matrix output input

def correctedBranchOperator119
    {Configuration : Type*} [DecidableEq Configuration]
    (p : HistorySpec.Parameters)
    (modelQ : Matrix Configuration Configuration ℚ) :
    Fin 4 → Matrix (HistorySpec.Index Configuration p)
      (HistorySpec.Index Configuration p) ℝ
  | ⟨0, _⟩ => correctedCastMatrix119 (HistorySpec.L0 p)
  | ⟨1, _⟩ => correctedCastMatrix119 (HistorySpec.L1 p modelQ)
  | ⟨2, _⟩ =>
      (Real.sqrt (p.taylorOrder + 1))⁻¹ •
        correctedCastMatrix119 (HistorySpec.L2 p)
  | ⟨3, _⟩ => 0

def correctedWeightedSuccessBlock119
    {Configuration : Type*} [DecidableEq Configuration]
    (p : HistorySpec.Parameters)
    (modelQ : Matrix Configuration Configuration ℚ) :=
  (correctedAlpha119 p.taylorOrder)⁻¹ •
    (correctedLambda119 p.taylorOrder ⟨0, by decide⟩ •
        correctedBranchOperator119 p modelQ ⟨0, by decide⟩ +
      correctedLambda119 p.taylorOrder ⟨1, by decide⟩ •
        correctedBranchOperator119 p modelQ ⟨1, by decide⟩ +
      correctedLambda119 p.taylorOrder ⟨2, by decide⟩ •
        correctedBranchOperator119 p modelQ ⟨2, by decide⟩ +
      correctedLambda119 p.taylorOrder ⟨3, by decide⟩ •
        correctedBranchOperator119 p modelQ ⟨3, by decide⟩)

def correctedNormalizedHistoryTarget119
    {Configuration : Type*} [DecidableEq Configuration]
    (p : HistorySpec.Parameters)
    (modelQ : Matrix Configuration Configuration ℚ) :=
  (correctedAlpha119 p.taylorOrder)⁻¹ •
    correctedCastMatrix119 (HistorySpec.H_hist p modelQ)

theorem correctedWeightedSuccessBlock_eq_normalizedHistoryTarget119
    {Configuration : Type*} [DecidableEq Configuration]
    (p : HistorySpec.Parameters)
    (modelQ : Matrix Configuration Configuration ℚ) :
    correctedWeightedSuccessBlock119 p modelQ =
      correctedNormalizedHistoryTarget119 p modelQ := by
  have orderPositive : (0 : ℝ) < p.taylorOrder + 1 := by
    exact_mod_cast (Nat.succ_pos p.taylorOrder)
  have sqrtNe : Real.sqrt (p.taylorOrder + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 orderPositive)
  ext output input
  simp [correctedWeightedSuccessBlock119, correctedNormalizedHistoryTarget119,
    correctedBranchOperator119, correctedLambda119, correctedAlpha119,
    correctedCastMatrix119, HistorySpec.H_hist,
    Matrix.add_apply, Matrix.smul_apply, sqrtNe]

def correctedTaylorCoefficientExact119
    (source : CommonSource119) (index : Nat) : ℚ :=
  -(3 * (source.qParameters.K : ℚ) * source.historyParameters.stepSize) /
    ((index + 1 : Nat) : ℚ)

/-- The corrected coefficient angle as closed finite syntax.  Its value is
the same real angle used by the analytic proof; no opaque `.const` is placed
in the numerical circuit. -/
def correctedTaylorCoefficientAngle119
    (source : CommonSource119) (index : Nat) :
    VerifiedCircuitCore.AngleExpr :=
  CanonicalHistoryAdapter.compileScientificAngle
    (.mul (scientificNat119 2)
      (.acos (scientificRat119
        (correctedTaylorCoefficientExact119 source index))))

theorem correctedTaylorCoefficientAngle119_value
    (source : CommonSource119) (index : Nat) :
    (correctedTaylorCoefficientAngle119 source index).uniformValue =
      2 * Real.arccos
        (-(omegaH119 source) / ((index + 1 : Nat) : ℝ)) := by
  have rationalValue :
      ((correctedTaylorCoefficientExact119 source index : ℚ) : ℝ) =
        -(omegaH119 source) / ((index + 1 : Nat) : ℝ) := by
    simp [correctedTaylorCoefficientExact119, omegaH119, generatorAlpha119]
  have numeratorDenominator :
      ((correctedTaylorCoefficientExact119 source index).num : ℝ) /
          ((correctedTaylorCoefficientExact119 source index).den : ℝ) =
        ((correctedTaylorCoefficientExact119 source index : ℚ) : ℝ) := by
    exact_mod_cast Rat.num_div_den
      (correctedTaylorCoefficientExact119 source index)
  simp [correctedTaylorCoefficientAngle119, scientificNat119,
    scientificRat119, CanonicalHistoryAdapter.compileScientificAngle,
    VerifiedCircuitCore.AngleExpr.uniformValue,
    VerifiedCircuitCore.AngleExpr.eval, numeratorDenominator, rationalValue]

theorem correctedTaylorCoefficient_clean_amplitude119
    (source : CommonSource119) (index : Nat) :
    cleanSignalAmplitude119 (correctedTaylorCoefficientAngle119 source index) =
      -(omegaH119 source) / ((index + 1 : Nat) : ℝ) := by
  have denominatorPositive : (0 : ℝ) < ((index + 1 : Nat) : ℝ) := by
    positivity
  have denominatorOne : (1 : ℝ) ≤ ((index + 1 : Nat) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le index))
  have omegaNonnegative : 0 ≤ omegaH119 source :=
    le_of_lt (omegaH119_positive source)
  have quotientNonnegative :
      0 ≤ omegaH119 source / ((index + 1 : Nat) : ℝ) :=
    div_nonneg omegaNonnegative (le_of_lt denominatorPositive)
  have quotientLeOne :
      omegaH119 source / ((index + 1 : Nat) : ℝ) ≤ 1 := by
    apply (div_le_one denominatorPositive).2
    exact le_trans source.scaledStepSmall denominatorOne
  have lower :
      (-1 : ℝ) ≤ -(omegaH119 source) / ((index + 1 : Nat) : ℝ) := by
    calc
      (-1 : ℝ) ≤ -(omegaH119 source /
          ((index + 1 : Nat) : ℝ)) := neg_le_neg quotientLeOne
      _ = -(omegaH119 source) / ((index + 1 : Nat) : ℝ) := by ring
  have upper :
      -(omegaH119 source) / ((index + 1 : Nat) : ℝ) ≤ 1 := by
    have nonpositive :
        -(omegaH119 source / ((index + 1 : Nat) : ℝ)) ≤ 0 :=
      neg_nonpos.mpr quotientNonnegative
    calc
      -(omegaH119 source) / ((index + 1 : Nat) : ℝ) =
          -(omegaH119 source / ((index + 1 : Nat) : ℝ)) := by ring
      _ ≤ 0 := nonpositive
      _ ≤ 1 := by norm_num
  unfold cleanSignalAmplitude119
  rw [correctedTaylorCoefficientAngle119_value]
  rw [show (2 * Real.arccos
      (-(omegaH119 source) / ((index + 1 : Nat) : ℝ))) / 2 =
      Real.arccos
        (-(omegaH119 source) / ((index + 1 : Nat) : ℝ)) by ring]
  exact Real.cos_arccos lower upper

theorem correctedAlpha_eq_selector_at_one119 (taylorOrder : Nat) :
    correctedAlpha119 taylorOrder = selectorAlpha119 taylorOrder 1 := by
  simp [correctedAlpha119, selectorAlpha119, HistoryLCU.alphaH]
  ring

end

end ExecutableHistoryExecutableHistory
