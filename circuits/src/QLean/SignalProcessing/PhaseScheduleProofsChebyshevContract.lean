import Mathlib
import QLean.History.Jennings.PureSpec

noncomputable section

namespace PhaseScheduleProofs

open JenningsHistory

structure ChebyshevTarget125 where
  delta : ℝ
  L : Nat
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  L_pos : 0 < L
  L_odd : L % 2 = 1

def chebyshevT125 (degree : Nat) (x : ℝ) : ℝ :=
  Polynomial.eval x (Polynomial.Chebyshev.T ℝ degree)

def chebyshevScale125 (target : ChebyshevTarget125) : ℝ :=
  Real.cosh (Real.arcosh (1 / target.delta) / (target.L : ℝ))

def chebyshevResponse125 (target : ChebyshevTarget125) (x : ℝ) : ℝ :=
  target.delta * chebyshevT125 target.L (chebyshevScale125 target * x)

end PhaseScheduleProofs
