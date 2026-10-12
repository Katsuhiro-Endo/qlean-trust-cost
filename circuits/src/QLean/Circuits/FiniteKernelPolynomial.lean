import VerifiedMath.Quantum.QSPFiniteRequest
import QLean.SignalProcessing.M13bApprovedOddQSPBridge

/-! Finite query planning. The bound is deliberately conservative; its causal
history-norm justification is separate from this executable data definition. -/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.FiniteKernelPolynomial

open VerifiedMath.Quantum.QSP

/-- A dimension-free-in-configuration bound derived from causal clock/order
height and the existing history block normalization bound. -/
def inverseBound (order clocks labels : Nat) : Nat :=
  (order + 4) ^ (clocks * labels)

theorem inverseBound_pos (order clocks labels : Nat) :
    0 < inverseBound order clocks labels := by
  unfold inverseBound
  positivity

def queryLowerBound (order clocks labels : Nat) (epsilon : ℚ) : Nat :=
  ⌊(inverseBound order clocks labels : ℚ) * 2 / epsilon⌋₊ + 1

def degree (order clocks labels : Nat) (epsilon : ℚ) : Nat :=
  KernelQSP.leastOddAtLeast126 (queryLowerBound order clocks labels epsilon)

theorem degree_pos (order clocks labels : Nat) (epsilon : ℚ) :
    0 < degree order clocks labels epsilon := by
  have lower := KernelQSP.leastOddAtLeast126_lower
    (queryLowerBound order clocks labels epsilon)
  unfold degree queryLowerBound at *
  omega

theorem degree_odd (order clocks labels : Nat) (epsilon : ℚ) :
    degree order clocks labels epsilon % 2 = 1 :=
  KernelQSP.leastOddAtLeast126_odd _

def expression (order clocks labels : Nat) (epsilon : ℚ) : PolynomialExpression :=
  let n := degree order clocks labels epsilon
  let delta := epsilon / 2
  let scale : ScalarExpression := .cosh
    (.div (.arcosh (.div (.rational 1) (.rational delta))) (.rational (n : ℚ)))
  .mul (.constant (.rational delta))
    (.compose (.chebyshev n) (.mul (.constant scale) .variable))

noncomputable def chebyshevTarget (order clocks labels : Nat) (epsilon : ℚ)
    (positive : 0 < epsilon) (small : epsilon < 2) :
    PhaseScheduleProofs.ChebyshevTarget125 where
  delta := (epsilon : ℝ) / 2
  L := degree order clocks labels epsilon
  delta_pos := by exact_mod_cast (div_pos positive (by norm_num : (0 : ℚ) < 2))
  delta_lt_one := by exact_mod_cast (show epsilon / 2 < 1 by linarith)
  L_pos := degree_pos order clocks labels epsilon
  L_odd := degree_odd order clocks labels epsilon

theorem expression_interpret (order clocks labels : Nat) (epsilon : ℚ)
    (positive : 0 < epsilon) (small : epsilon < 2) :
    (expression order clocks labels epsilon).interpret =
      SpectralSamplingProof.Analytic.chebyshevPolynomial041
        (chebyshevTarget order clocks labels epsilon positive small) := by
  simp [expression, PolynomialExpression.interpret, ScalarExpression.interpret,
    SpectralSamplingProof.Analytic.chebyshevPolynomial041,
    PhaseScheduleProofs.chebyshevScale125, chebyshevTarget]

/-- Constructing a request never evaluates a real coefficient or chooses a
degree. The erased fields prove the interpretation is an admissible QSP input. -/
def request (order clocks labels : Nat) (epsilon : ℚ)
    (positive : 0 < epsilon) (small : epsilon < 2) : FinitePolynomialRequest where
  expression := expression order clocks labels epsilon
  degree := degree order clocks labels epsilon
  degree_bound := by
    rw [expression_interpret order clocks labels epsilon positive small]
    exact SpectralSamplingProof.Analytic.chebyshevPolynomial041_natDegree_bound _
  parity_law := by
    intro x
    rw [expression_interpret order clocks labels epsilon positive small,
      degree_odd]
    simpa using SpectralSamplingProof.Analytic.chebyshevPolynomial041_parity
      (chebyshevTarget order clocks labels epsilon positive small) x
  bounded_on_unitInterval := by
    intro x lower upper
    rw [expression_interpret order clocks labels epsilon positive small]
    exact SpectralSamplingProof.Analytic.chebyshevPolynomial041_unit_bound _ x lower upper

theorem request_approved (order clocks labels : Nat) (epsilon : ℚ)
    (positive : 0 < epsilon) (small : epsilon < 2) :
    (request order clocks labels epsilon positive small).approved =
      M13bApprovedOddQSPBridge.approvedChebyshevPolynomial
        (chebyshevTarget order clocks labels epsilon positive small) := by
  apply approvedPolynomial_ext
  · exact expression_interpret order clocks labels epsilon positive small
  · rfl

theorem firstNatAbove_rat (value : ℚ) (nonnegative : 0 ≤ value) :
    Nat.find (exists_nat_gt (value : ℝ)) = ⌊value⌋₊ + 1 := by
  apply le_antisymm
  · apply Nat.find_min'
    exact_mod_cast Nat.lt_floor_add_one value
  · by_contra notBelow
    let n := Nat.find (exists_nat_gt (value : ℝ))
    have below : n < ⌊value⌋₊ + 1 := by omega
    have floorBound := Nat.floor_le nonnegative
    have nBound : (n : ℚ) ≤ (⌊value⌋₊ : ℚ) := by exact_mod_cast (show n ≤ ⌊value⌋₊ by omega)
    have realBound : (n : ℝ) ≤ (value : ℝ) := by exact_mod_cast nBound.trans floorBound
    exact (not_lt_of_ge realBound) (Nat.find_spec (exists_nat_gt (value : ℝ)))

end QLean.Circuits.FiniteKernelPolynomial
