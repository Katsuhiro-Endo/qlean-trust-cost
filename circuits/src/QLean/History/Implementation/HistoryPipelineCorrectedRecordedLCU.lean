import QLean.History.Implementation.HistoryPipelineCorrectedScaledHistory

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix

noncomputable section

def correctedPREPAmplitude119
    (taylorOrder : Nat) (branch : Fin 4) : ℝ :=
  Real.sqrt
    (correctedLambda119 taylorOrder branch /
      correctedAlpha119 taylorOrder)

theorem correctedAlpha119_positive (taylorOrder : Nat) :
    0 < correctedAlpha119 taylorOrder := by
  unfold correctedAlpha119
  have nonnegative : 0 ≤ Real.sqrt (taylorOrder + 1) :=
    Real.sqrt_nonneg _
  linarith

theorem correctedLambda119_nonnegative
    (taylorOrder : Nat) (branch : Fin 4) :
    0 ≤ correctedLambda119 taylorOrder branch := by
  fin_cases branch <;> simp [correctedLambda119]

theorem correctedPREPAmplitude_square119
    (taylorOrder : Nat) (branch : Fin 4) :
    correctedPREPAmplitude119 taylorOrder branch *
        correctedPREPAmplitude119 taylorOrder branch =
      correctedLambda119 taylorOrder branch /
        correctedAlpha119 taylorOrder := by
  unfold correctedPREPAmplitude119
  rw [← pow_two]
  exact Real.sq_sqrt
    (div_nonneg (correctedLambda119_nonnegative taylorOrder branch)
      (le_of_lt (correctedAlpha119_positive taylorOrder)))

end

end ExecutableHistoryExecutableHistory
