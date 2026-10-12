import QLean.Circuits.Foundation.FiniteGateExport

/-! Shared QSP angle interfaces. Finite syntax certifies exportability,
not the accuracy of an externally supplied phase word. -/

set_option autoImplicit false
set_option warningAsError true

namespace VerifiedCircuitCore

class QSPCircuitAngle (AngleType : Type) where
  toCircuitAngle : AngleType → VerifiedCircuitCore.AngleExpr
  symbolFree : ∀ angle, (toCircuitAngle angle).IsSymbolFree

instance realQSPCircuitAngle : QSPCircuitAngle ℝ where
  toCircuitAngle := VerifiedCircuitCore.AngleExpr.const
  symbolFree := by intro _; trivial

/-- External finite syntax carries exportability, not an accuracy claim. -/
structure FinitePhaseAngle where
  expression : VerifiedCircuitCore.AngleExpr
  symbolFree : expression.IsSymbolFree
  exportable : expression.toFinite?.isSome = true

instance finiteQSPCircuitAngle : QSPCircuitAngle FinitePhaseAngle where
  toCircuitAngle := FinitePhaseAngle.expression
  symbolFree := FinitePhaseAngle.symbolFree

end VerifiedCircuitCore
