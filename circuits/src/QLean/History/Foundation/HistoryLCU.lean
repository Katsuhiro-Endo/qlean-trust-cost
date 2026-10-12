import QLean.History.Foundation.HistorySpec
import QLean.Circuits.Foundation.PrimitiveOperatorSemantics

namespace HistoryBlockEncoding
namespace HistoryLCU

noncomputable section

/-- The four branch weights used by the history specification. -/
def lambda (taylorOrder : Nat) (omegaH : ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => omegaH
  | ⟨2, _⟩ => Real.sqrt (taylorOrder + 1)
  | ⟨3, _⟩ => 0

def alphaH (taylorOrder : Nat) (omegaH : ℝ) : ℝ :=
  1 + omegaH + Real.sqrt (taylorOrder + 1)

@[simp] theorem lambda_zero (taylorOrder : Nat) (omegaH : ℝ) :
    lambda taylorOrder omegaH ⟨0, by decide⟩ = 1 := rfl

@[simp] theorem lambda_one (taylorOrder : Nat) (omegaH : ℝ) :
    lambda taylorOrder omegaH ⟨1, by decide⟩ = omegaH := rfl

@[simp] theorem lambda_two (taylorOrder : Nat) (omegaH : ℝ) :
    lambda taylorOrder omegaH ⟨2, by decide⟩ = Real.sqrt (taylorOrder + 1) := rfl

@[simp] theorem lambda_three_zero (taylorOrder : Nat) (omegaH : ℝ) :
    lambda taylorOrder omegaH ⟨3, by decide⟩ = 0 := rfl

/-! The following names are the Lean-side recorded LCU implementation.  They
are deliberately aliases of the pure four-branch source above: the recorded
implementation is repaired to carry the zero fourth branch instead of a
fourth unit weight. -/

def recordedLambda (taylorOrder : Nat) (omegaH : ℝ) : Fin 4 → ℝ :=
  lambda taylorOrder omegaH

def recordedAlpha (taylorOrder : Nat) (omegaH : ℝ) : ℝ :=
  alphaH taylorOrder omegaH

def recordedPREPAmplitude (taylorOrder : Nat) (omegaH : ℝ) : Fin 4 → ℝ :=
  fun i => Real.sqrt
    (recordedLambda taylorOrder omegaH i /
      recordedAlpha taylorOrder omegaH)

def recordedUNPREPAmplitude (taylorOrder : Nat) (omegaH : ℝ) : Fin 4 → ℝ :=
  recordedPREPAmplitude taylorOrder omegaH

@[simp] theorem recordedLambda_fourth_zero (taylorOrder : Nat) (omegaH : ℝ) :
    recordedLambda taylorOrder omegaH ⟨3, by decide⟩ = 0 := by
  rfl

@[simp] theorem recordedAlpha_counterexample :
    recordedAlpha 0 1 = 3 := by
  norm_num [recordedAlpha, alphaH]

@[simp] theorem recordedPREPAmplitude_fourth_zero
    (taylorOrder : Nat) (omegaH : ℝ) :
    recordedPREPAmplitude taylorOrder omegaH ⟨3, by decide⟩ = 0 := by
  change Real.sqrt (0 / recordedAlpha taylorOrder omegaH) = 0
  simp

@[simp] theorem recordedUNPREPAmplitude_fourth_zero
    (taylorOrder : Nat) (omegaH : ℝ) :
    recordedUNPREPAmplitude taylorOrder omegaH ⟨3, by decide⟩ = 0 := by
  change recordedPREPAmplitude taylorOrder omegaH ⟨3, by decide⟩ = 0
  exact recordedPREPAmplitude_fourth_zero taylorOrder omegaH

/- A coefficient-only boundary for a recorded LCU layer.  The branch
   operators remain explicit parameters; this theorem does not define the
   mathematical history operator from a circuit product. -/

end

end HistoryLCU
end HistoryBlockEncoding
