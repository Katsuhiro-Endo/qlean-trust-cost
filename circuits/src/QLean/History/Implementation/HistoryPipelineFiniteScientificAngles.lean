import QLean.History.Implementation.HistoryPipelineFiniteCorrectedP05

set_option autoImplicit false
set_option warningAsError true

/-!
Finite angle values computed directly from the rational scientific inputs.
The proof-only angle compiler also handles general symbolic/real expressions;
that generality makes it noncomputable. These four constructors use only its
finite, power-free fragment, and the equalities below connect both paths.
-/

namespace ExecutableHistoryFiniteScientificAngles

open VerifiedCircuitCore
open ExecutableHistoryExecutableHistory

def rational (value : ℚ) : AngleExpr :=
  .rational value.num value.den value.den_pos

def natural (value : Nat) : AngleExpr :=
  .rational value 1 (by decide)

def correctedCoefficient (source : AlignedCommonSource119)
    (index : Nat) : AngleExpr :=
  .mul (natural 2) (.acos (rational
    (-(3 * (source.qParameters.K : ℚ) * source.historyParameters.stepSize) /
      ((index + 1 : Nat) : ℚ))))

def correctedSelectorHigh (source : AlignedCommonSource119) : AngleExpr :=
  .mul (natural 2) (.acos (.sqrt (.div
    (.add (natural 1) (rational 1))
    (.add (.add (natural 1) (rational 1))
      (.sqrt (natural (source.historyParameters.taylorOrder + 1)))))))

def correctedSelectorLow : AngleExpr :=
  .acos (.sqrt (.div (natural 1) (.add (natural 1) (rational 1))))

def repairedIdle (source : AlignedCommonSource119) : AngleExpr :=
  .mul (natural 2) (.acos (.neg (.div (natural 1)
    (.sqrt (natural (source.historyParameters.taylorOrder + 1))))))

/-- The P15 idle coefficient is the fixed full-turn angle; it is distinct
from the order-dependent repaired-H3 idle angle above. -/
def idleCoefficient : AngleExpr :=
  .mul (natural 2) .pi

end ExecutableHistoryFiniteScientificAngles
