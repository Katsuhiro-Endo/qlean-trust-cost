import QLean.History.Implementation.HistoryPipelineExecutableHistoryAngles

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open HistoryBlockEncoding
open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

def scientificRat119 (value : ℚ) : ScientificAngleExpr :=
  .rational value.num value.den value.den_pos

def scientificNat119 (value : Nat) : ScientificAngleExpr :=
  .rational value 1 (by decide)

def selectorTailScientific119 (taylorOrder : Nat) : ScientificAngleExpr :=
  .sqrt (scientificNat119 (taylorOrder + 1))

def selectorAlphaScientific119 (taylorOrder : Nat) (omega : ℚ) :
    ScientificAngleExpr :=
  .add (.add (scientificNat119 1) (scientificRat119 omega))
    (selectorTailScientific119 taylorOrder)

def selectorHighScientific119 (taylorOrder : Nat) (omega : ℚ) :
    ScientificAngleExpr :=
  .mul (scientificNat119 2)
    (.acos (.sqrt (.div
      (.add (scientificNat119 1) (scientificRat119 omega))
      (selectorAlphaScientific119 taylorOrder omega))))

def selectorLowScientific119 (omega : ℚ) : ScientificAngleExpr :=
  .acos (.sqrt (.div (scientificNat119 1)
    (.add (scientificNat119 1) (scientificRat119 omega))))

def selectorTailWeight119 (taylorOrder : Nat) : ℝ :=
  Real.sqrt (taylorOrder + 1)

def selectorAlpha119 (taylorOrder : Nat) (omega : ℝ) : ℝ :=
  HistoryBlockEncoding.HistoryLCU.alphaH taylorOrder omega

def selectorHighAngle119 (taylorOrder : Nat) (omega : ℝ) : ℝ :=
  2 * Real.arccos
    (Real.sqrt ((1 + omega) / selectorAlpha119 taylorOrder omega))

def selectorLowAngle119 (omega : ℝ) : ℝ :=
  Real.arccos (Real.sqrt (1 / (1 + omega)))

theorem compile_selectorHighScientific119_value
    (taylorOrder : Nat) (omega : ℚ) :
    (CanonicalHistoryAdapter.compileScientificAngle
      (selectorHighScientific119 taylorOrder omega)).uniformValue =
      selectorHighAngle119 taylorOrder (omega : ℝ) := by
  have omega_num_den :
      (omega.num : ℝ) / (omega.den : ℝ) = (omega : ℝ) := by
    exact_mod_cast Rat.num_div_den omega
  simp [selectorHighScientific119, selectorAlphaScientific119,
    selectorTailScientific119, scientificNat119, scientificRat119,
    CanonicalHistoryAdapter.compileScientificAngle, AngleExpr.uniformValue, AngleExpr.eval,
    selectorHighAngle119, selectorAlpha119, HistoryBlockEncoding.HistoryLCU.alphaH,
    omega_num_den]

theorem compile_selectorLowScientific119_value (omega : ℚ) :
    (CanonicalHistoryAdapter.compileScientificAngle
      (selectorLowScientific119 omega)).uniformValue =
      selectorLowAngle119 (omega : ℝ) := by
  have omega_num_den :
      (omega.num : ℝ) / (omega.den : ℝ) = (omega : ℝ) := by
    exact_mod_cast Rat.num_div_den omega
  simp [selectorLowScientific119, scientificNat119, scientificRat119,
    CanonicalHistoryAdapter.compileScientificAngle, AngleExpr.uniformValue, AngleExpr.eval,
    selectorLowAngle119, omega_num_den]

def selectorPreparationParameters119 {qubits : Nat}
    (low high : Fin qubits) (different : high ≠ low)
    (taylorOrder : Nat) (omega : ℝ) :
    HistorySelectorPreparationParameters qubits where
  low := low
  high := high
  different := different
  firstHighAngle := .const (selectorHighAngle119 taylorOrder omega)
  firstLowAngle := .const (selectorLowAngle119 omega)
  secondLowAngle := .const (selectorLowAngle119 omega)

theorem selectorAlpha119_positive (taylorOrder : Nat) {omega : ℝ}
    (omegaNonnegative : 0 ≤ omega) :
    0 < selectorAlpha119 taylorOrder omega := by
  unfold selectorAlpha119 HistoryBlockEncoding.HistoryLCU.alphaH
  have tailNonnegative : 0 ≤ Real.sqrt ((taylorOrder : ℝ) + 1) :=
    Real.sqrt_nonneg _
  linarith

private theorem highRatio_nonnegative (taylorOrder : Nat) {omega : ℝ}
    (omegaNonnegative : 0 ≤ omega) :
    0 ≤ (1 + omega) / selectorAlpha119 taylorOrder omega := by
  exact div_nonneg (by linarith) (le_of_lt
    (selectorAlpha119_positive taylorOrder omegaNonnegative))

private theorem highRatio_le_one (taylorOrder : Nat) {omega : ℝ}
    (omegaNonnegative : 0 ≤ omega) :
    (1 + omega) / selectorAlpha119 taylorOrder omega ≤ 1 := by
  apply (div_le_one (selectorAlpha119_positive taylorOrder omegaNonnegative)).2
  unfold selectorAlpha119 HistoryBlockEncoding.HistoryLCU.alphaH
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

private theorem lowRatio_nonnegative {omega : ℝ} (omegaNonnegative : 0 ≤ omega) :
    0 ≤ 1 / (1 + omega) := by positivity

private theorem lowRatio_le_one {omega : ℝ} (omegaNonnegative : 0 ≤ omega) :
    1 / (1 + omega) ≤ 1 := by
  exact (div_le_one (by linarith)).2 (by linarith)

private theorem sqrt_unit_interval {x : ℝ} (xNonnegative : 0 ≤ x)
    (xLeOne : x ≤ 1) :
    -1 ≤ Real.sqrt x ∧ Real.sqrt x ≤ 1 := by
  have sqrtNonnegative : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have sqrtSquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt xNonnegative
  constructor
  · linarith
  · nlinarith

theorem selectorHigh_cos119 (taylorOrder : Nat) {omega : ℝ}
    (omegaNonnegative : 0 ≤ omega) :
    Real.cos (selectorHighAngle119 taylorOrder omega / 2) =
      Real.sqrt ((1 + omega) / selectorAlpha119 taylorOrder omega) := by
  have interval := sqrt_unit_interval
    (highRatio_nonnegative taylorOrder omegaNonnegative)
    (highRatio_le_one taylorOrder omegaNonnegative)
  unfold selectorHighAngle119
  rw [show (2 * Real.arccos
      (Real.sqrt ((1 + omega) / selectorAlpha119 taylorOrder omega))) / 2 =
      Real.arccos
        (Real.sqrt ((1 + omega) / selectorAlpha119 taylorOrder omega)) by ring]
  exact Real.cos_arccos interval.1 interval.2

theorem selectorHigh_sin119 (taylorOrder : Nat) {omega : ℝ}
    (omegaNonnegative : 0 ≤ omega) :
    Real.sin (selectorHighAngle119 taylorOrder omega / 2) =
      Real.sqrt
        (selectorTailWeight119 taylorOrder /
          selectorAlpha119 taylorOrder omega) := by
  have alphaPositive := selectorAlpha119_positive taylorOrder omegaNonnegative
  have ratioNonnegative := highRatio_nonnegative taylorOrder omegaNonnegative
  unfold selectorHighAngle119
  rw [show (2 * Real.arccos
      (Real.sqrt ((1 + omega) / selectorAlpha119 taylorOrder omega))) / 2 =
      Real.arccos
        (Real.sqrt ((1 + omega) / selectorAlpha119 taylorOrder omega)) by ring]
  rw [Real.sin_arccos, Real.sq_sqrt ratioNonnegative]
  congr 1
  unfold selectorAlpha119 selectorTailWeight119 HistoryBlockEncoding.HistoryLCU.alphaH
  field_simp [ne_of_gt alphaPositive]
  ring

theorem selectorLow_cos119 {omega : ℝ} (omegaNonnegative : 0 ≤ omega) :
    Real.cos (selectorLowAngle119 omega) =
      Real.sqrt (1 / (1 + omega)) := by
  have interval := sqrt_unit_interval
    (lowRatio_nonnegative omegaNonnegative)
    (lowRatio_le_one omegaNonnegative)
  unfold selectorLowAngle119
  exact Real.cos_arccos interval.1 interval.2

theorem selectorLow_sin119 {omega : ℝ} (omegaNonnegative : 0 ≤ omega) :
    Real.sin (selectorLowAngle119 omega) =
      Real.sqrt (omega / (1 + omega)) := by
  have ratioNonnegative := lowRatio_nonnegative omegaNonnegative
  unfold selectorLowAngle119
  rw [Real.sin_arccos, Real.sq_sqrt ratioNonnegative]
  congr 1
  field_simp [show (1 + omega) ≠ 0 by linarith]
  ring

theorem selectorBranchZeroAmplitude119 (taylorOrder : Nat) {omega : ℝ}
    (omegaNonnegative : 0 ≤ omega) :
    Real.cos (selectorHighAngle119 taylorOrder omega / 2) *
        Real.cos (selectorLowAngle119 omega) =
      Real.sqrt (1 / selectorAlpha119 taylorOrder omega) := by
  rw [selectorHigh_cos119 taylorOrder omegaNonnegative,
    selectorLow_cos119 omegaNonnegative]
  rw [← Real.sqrt_mul (highRatio_nonnegative taylorOrder omegaNonnegative)]
  congr 1
  field_simp [show (1 + omega) ≠ 0 by linarith]

theorem selectorBranchOneAmplitude119 (taylorOrder : Nat) {omega : ℝ}
    (omegaNonnegative : 0 ≤ omega) :
    Real.cos (selectorHighAngle119 taylorOrder omega / 2) *
        Real.sin (selectorLowAngle119 omega) =
      Real.sqrt (omega / selectorAlpha119 taylorOrder omega) := by
  rw [selectorHigh_cos119 taylorOrder omegaNonnegative,
    selectorLow_sin119 omegaNonnegative]
  rw [← Real.sqrt_mul (highRatio_nonnegative taylorOrder omegaNonnegative)]
  congr 1
  field_simp [show (1 + omega) ≠ 0 by linarith]

theorem selectorBranchTwoAmplitude119 (taylorOrder : Nat) {omega : ℝ}
    (omegaNonnegative : 0 ≤ omega) :
    Real.sin (selectorHighAngle119 taylorOrder omega / 2) =
      Real.sqrt
        (HistoryBlockEncoding.HistoryLCU.lambda taylorOrder omega ⟨2, by decide⟩ /
          selectorAlpha119 taylorOrder omega) := by
  change Real.sin (selectorHighAngle119 taylorOrder omega / 2) =
    Real.sqrt
      (selectorTailWeight119 taylorOrder /
        selectorAlpha119 taylorOrder omega)
  exact selectorHigh_sin119 taylorOrder omegaNonnegative

theorem selectorBranchThreeAmplitude119 (taylorOrder : Nat) {omega : ℝ} :
    Real.sin (selectorHighAngle119 taylorOrder omega / 2) * 0 =
      Real.sqrt
        (HistoryBlockEncoding.HistoryLCU.lambda taylorOrder omega ⟨3, by decide⟩ /
          selectorAlpha119 taylorOrder omega) := by
  change Real.sin (selectorHighAngle119 taylorOrder omega / 2) * 0 =
    Real.sqrt (0 / selectorAlpha119 taylorOrder omega)
  simp

end

end ExecutableHistoryExecutableHistory
