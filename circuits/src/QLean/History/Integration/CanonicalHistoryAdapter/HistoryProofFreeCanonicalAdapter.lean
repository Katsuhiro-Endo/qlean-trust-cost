import QLean.Spectral.Analysis.HistoryBlock
import QLean.Spectral.Analysis.ControlledSubcircuit

set_option autoImplicit false

namespace CanonicalHistoryAdapter

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic

noncomputable section

def scientificEval (symbols : String → ℝ) : ScientificAngleExpr → ℝ
  | .rational numerator denominator _ =>
      (numerator : ℝ) / (denominator : ℝ)
  | .decimal value =>
      (value.mantissa : ℝ) / (10 : ℝ) ^ value.scale
  | .symbol name => symbols name
  | .pi => Real.pi
  | .add left right => scientificEval symbols left + scientificEval symbols right
  | .mul left right => scientificEval symbols left * scientificEval symbols right
  | .div numerator denominator =>
      scientificEval symbols numerator / scientificEval symbols denominator
  | .pow base exponent =>
      Real.rpow (scientificEval symbols base) (scientificEval symbols exponent)
  | .neg value => -scientificEval symbols value
  | .sqrt value => Real.sqrt (scientificEval symbols value)
  | .acos value => Real.arccos (scientificEval symbols value)

def ScientificAngleCore : ScientificAngleExpr → Prop
  | .rational _ _ _ | .decimal _ | .symbol _ | .pi => True
  | .add left right | .mul left right | .div left right =>
      ScientificAngleCore left ∧ ScientificAngleCore right
  | .pow _ _ => False
  | .neg value | .sqrt value | .acos value => ScientificAngleCore value

def compileScientificAngle : ScientificAngleExpr → VerifiedCircuitCore.AngleExpr
  | .rational numerator denominator positive =>
      .rational numerator denominator positive
  | .decimal value => .decimal value.mantissa value.scale
  | .symbol name => .symbol name
  | .pi => .pi
  | .add left right =>
      .add (compileScientificAngle left) (compileScientificAngle right)
  | .mul left right =>
      .mul (compileScientificAngle left) (compileScientificAngle right)
  | .div numerator denominator =>
      .div (compileScientificAngle numerator) (compileScientificAngle denominator)
  | .pow base exponent =>
      .const (scientificEval (fun _ => 0) (.pow base exponent))
  | .neg value => .neg (compileScientificAngle value)
  | .sqrt value => .sqrt (compileScientificAngle value)
  | .acos value => .acos (compileScientificAngle value)

/-! Raw executable angles intentionally contain no denominator proof.  The
    conversion below is total and fail-closed; `RawAngleCore143` is the
    independent admissibility predicate used to retain the scientific subset
    without putting a witness into the raw record. -/

end

end CanonicalHistoryAdapter
