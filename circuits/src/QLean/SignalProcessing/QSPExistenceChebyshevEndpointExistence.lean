import QLean.SignalProcessing.QSPExistenceShapedQSPWordSynthesis
import Mathlib
import QLean.History.Jennings.PureSpec
import QLean.SignalProcessing.PhaseScheduleProofsPhaseWordContract
import QLean.SignalProcessing.PhaseScheduleProofsChebyshevContract

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore
open JenningsHistory

noncomputable section

/-! The Chebyshev polynomial is kept as the actual polynomial input to the
    accepted general real-QSP boundary.  No phase data is stored here. -/

def chebyshevPolynomial041 (target : PhaseScheduleProofs.ChebyshevTarget125) :
    Polynomial ℝ :=
  Polynomial.C target.delta *
    (Polynomial.Chebyshev.T ℝ (target.L : ℤ)).comp
      (Polynomial.C (PhaseScheduleProofs.chebyshevScale125 target) * Polynomial.X)

theorem chebyshevPolynomial041_eval
    (target : PhaseScheduleProofs.ChebyshevTarget125) (x : ℝ) :
    Polynomial.eval x (chebyshevPolynomial041 target) =
      PhaseScheduleProofs.chebyshevResponse125 target x := by
  simp [chebyshevPolynomial041, PhaseScheduleProofs.chebyshevResponse125,
    PhaseScheduleProofs.chebyshevT125, PhaseScheduleProofs.chebyshevScale125,
    Polynomial.eval_comp, Polynomial.eval_mul]

theorem chebyshevTarget041_int_odd
    (target : PhaseScheduleProofs.ChebyshevTarget125) :
    Odd (target.L : ℤ) := by
  rcases Nat.even_or_odd target.L with he | ho
  · have hmod := target.L_odd
    rcases he with ⟨k, hk⟩
    omega
  · rcases ho with ⟨k, hk⟩
    refine ⟨(k : ℤ), ?_⟩
    exact_mod_cast hk

theorem chebyshevScale041_pos
    (target : PhaseScheduleProofs.ChebyshevTarget125) :
    0 < PhaseScheduleProofs.chebyshevScale125 target := by
  exact Real.cosh_pos _

theorem chebyshevPolynomial041_parity
    (target : PhaseScheduleProofs.ChebyshevTarget125) (x : ℝ) :
    Polynomial.eval (-x) (chebyshevPolynomial041 target) =
      -Polynomial.eval x (chebyshevPolynomial041 target) := by
  have hodd := chebyshevTarget041_int_odd target
  rw [chebyshevPolynomial041_eval, chebyshevPolynomial041_eval]
  unfold PhaseScheduleProofs.chebyshevResponse125 PhaseScheduleProofs.chebyshevT125
  rw [show PhaseScheduleProofs.chebyshevScale125 target * (-x) =
      -(PhaseScheduleProofs.chebyshevScale125 target * x) by ring]
  rw [Polynomial.Chebyshev.T_eval_neg]
  norm_num [Int.negOnePow_odd _ hodd]

theorem chebyshevPolynomial041_natDegree_bound
    (target : PhaseScheduleProofs.ChebyshevTarget125) :
    (chebyshevPolynomial041 target).natDegree ≤ target.L := by
  have hdelta : target.delta ≠ 0 := ne_of_gt target.delta_pos
  have hscale : PhaseScheduleProofs.chebyshevScale125 target ≠ 0 :=
    ne_of_gt (chebyshevScale041_pos target)
  have harg :
      ((target.L : ℤ).natAbs) = target.L := by simp
  have hinner :
      (Polynomial.C (PhaseScheduleProofs.chebyshevScale125 target) *
          (Polynomial.X : Polynomial ℝ)).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul hscale]
    simp
  have hcomp := Polynomial.natDegree_comp_le
    (p := Polynomial.Chebyshev.T ℝ (target.L : ℤ))
    (q := Polynomial.C (PhaseScheduleProofs.chebyshevScale125 target) *
      (Polynomial.X : Polynomial ℝ))
  rw [Polynomial.Chebyshev.natDegree_T, harg, hinner, Nat.mul_one] at hcomp
  calc
    (chebyshevPolynomial041 target).natDegree ≤
        (Polynomial.C target.delta).natDegree +
          ((Polynomial.Chebyshev.T ℝ (target.L : ℤ)).comp
            (Polynomial.C (PhaseScheduleProofs.chebyshevScale125 target) *
              (Polynomial.X : Polynomial ℝ))).natDegree := by
      exact Polynomial.natDegree_mul_le
    _ = ((Polynomial.Chebyshev.T ℝ (target.L : ℤ)).comp
          (Polynomial.C (PhaseScheduleProofs.chebyshevScale125 target) *
            (Polynomial.X : Polynomial ℝ))).natDegree := by
      simp
    _ ≤ target.L := hcomp

theorem chebyshevPolynomial041_unit_bound
    (target : PhaseScheduleProofs.ChebyshevTarget125) (x : ℝ)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    |Polynomial.eval x (chebyshevPolynomial041 target)| ≤ 1 := by
  rw [chebyshevPolynomial041_eval]
  unfold PhaseScheduleProofs.chebyshevResponse125 PhaseScheduleProofs.chebyshevT125
  let scale : ℝ := PhaseScheduleProofs.chebyshevScale125 target
  let y : ℝ := scale * x
  let t : ℝ := |y|
  have hscale : 0 < scale := by
    exact chebyshevScale041_pos target
  have hscale0 : 0 ≤ scale := le_of_lt hscale
  have hdelta0 : 0 ≤ target.delta := le_of_lt target.delta_pos
  have hdelta1 : target.delta ≤ 1 := by linarith [target.delta_lt_one]
  have hxt : |x| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hty : t ≤ scale := by
    dsimp [t, y]
    rw [abs_mul, abs_of_nonneg hscale0]
    calc
      scale * |x| ≤ scale * 1 :=
        mul_le_mul_of_nonneg_left hxt hscale0
      _ = scale := by ring
  have hbound_of_inner : t ≤ 1 →
      |target.delta * Polynomial.eval y
        (Polynomial.Chebyshev.T ℝ (target.L : ℤ))| ≤ 1 := by
    intro hinner
    have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one
      (target.L : ℤ) hinner
    have hprod := mul_le_mul_of_nonneg_left hT hdelta0
    calc
      |target.delta * Polynomial.eval y
          (Polynomial.Chebyshev.T ℝ (target.L : ℤ))| =
          target.delta * |Polynomial.eval y
            (Polynomial.Chebyshev.T ℝ (target.L : ℤ))| := by
              rw [abs_mul, abs_of_nonneg hdelta0]
      _ ≤ target.delta * 1 := hprod
      _ ≤ 1 := by simpa using hdelta1
  by_cases hinner : t ≤ 1
  · exact hbound_of_inner hinner
  · have ht1 : 1 ≤ t := le_of_not_ge hinner
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht1
    have ha0 : 0 ≤ Real.arcosh (1 / target.delta) := by
      exact Real.arcosh_nonneg (by
        rw [le_div_iff₀ target.delta_pos]
        linarith [target.delta_lt_one])
    have hL0 : 0 ≤ (target.L : ℝ) := by positivity
    have hLpos : 0 < (target.L : ℝ) := by
      exact_mod_cast target.L_pos
    have hLne : (target.L : ℝ) ≠ 0 := ne_of_gt hLpos
    have hdiv0 : 0 ≤ Real.arcosh (1 / target.delta) /
        (target.L : ℝ) := by positivity
    have hscale_repr : scale = Real.cosh
        (Real.arcosh (1 / target.delta) / (target.L : ℝ)) := by
      rfl
    have harc_scale : Real.arcosh scale =
        Real.arcosh (1 / target.delta) / (target.L : ℝ) := by
      rw [hscale_repr, Real.arcosh_cosh hdiv0]
    have harc : Real.arcosh t ≤
        Real.arcosh (1 / target.delta) / (target.L : ℝ) := by
      have h := (Real.arcosh_le_arcosh htpos hscale).2 hty
      simpa [harc_scale] using h
    have hmul : (target.L : ℝ) * Real.arcosh t ≤
        Real.arcosh (1 / target.delta) := by
      calc
        (target.L : ℝ) * Real.arcosh t ≤
            (target.L : ℝ) *
              (Real.arcosh (1 / target.delta) /
                (target.L : ℝ)) :=
          mul_le_mul_of_nonneg_left harc hL0
        _ = Real.arcosh (1 / target.delta) := by
          field_simp
    have hT_t : Polynomial.eval t
        (Polynomial.Chebyshev.T ℝ (target.L : ℤ)) =
        Real.cosh ((target.L : ℝ) * Real.arcosh t) := by
      calc
        Polynomial.eval t
            (Polynomial.Chebyshev.T ℝ (target.L : ℤ)) =
            Polynomial.eval (Real.cosh (Real.arcosh t))
              (Polynomial.Chebyshev.T ℝ (target.L : ℤ)) := by
                rw [Real.cosh_arcosh ht1]
        _ = Real.cosh ((target.L : ℝ) * Real.arcosh t) := by
          rw [Polynomial.Chebyshev.T_real_cosh]
          norm_num
    have hodd := chebyshevTarget041_int_odd target
    have hT_abs : |Polynomial.eval y
        (Polynomial.Chebyshev.T ℝ (target.L : ℤ))| =
        Real.cosh ((target.L : ℝ) * Real.arcosh t) := by
      by_cases hy : 0 ≤ y
      · have hyt : y = t := by
          dsimp [t]
          exact (abs_of_nonneg hy).symm
        rw [hyt, hT_t]
        exact abs_of_pos (Real.cosh_pos _)
      · have hy' : y < 0 := lt_of_not_ge hy
        have hyt : y = -t := by
          have habs : t = -y := by
            dsimp [t]
            exact abs_of_neg hy'
          linarith
        rw [hyt, Polynomial.Chebyshev.T_eval_neg]
        norm_num [Int.negOnePow_odd _ hodd, hT_t,
          abs_of_pos (Real.cosh_pos _)]
    have hcosh : Real.cosh ((target.L : ℝ) * Real.arcosh t) ≤
        Real.cosh (Real.arcosh (1 / target.delta)) := by
      rw [Real.cosh_le_cosh]
      simp only [abs_of_nonneg (mul_nonneg hL0
        (Real.arcosh_nonneg ht1)), abs_of_nonneg ha0]
      exact hmul
    have hcosh' : Real.cosh ((target.L : ℝ) * Real.arcosh t) ≤
        1 / target.delta := by
      calc
        Real.cosh ((target.L : ℝ) * Real.arcosh t) ≤
            Real.cosh (Real.arcosh (1 / target.delta)) := hcosh
        _ = 1 / target.delta := Real.cosh_arcosh (by
          rw [le_div_iff₀ target.delta_pos]
          linarith [target.delta_lt_one])
    calc
      |target.delta * Polynomial.eval y
          (Polynomial.Chebyshev.T ℝ (target.L : ℤ))| =
          target.delta * |Polynomial.eval y
            (Polynomial.Chebyshev.T ℝ (target.L : ℤ))| := by
              rw [abs_mul, abs_of_nonneg hdelta0]
      _ = target.delta * Real.cosh
          ((target.L : ℝ) * Real.arcosh t) := by rw [hT_abs]
      _ ≤ target.delta * (1 / target.delta) :=
        mul_le_mul_of_nonneg_left hcosh' hdelta0
      _ = 1 := by simp [ne_of_gt target.delta_pos]

def chebyshevGeneralInput041
    (target : PhaseScheduleProofs.ChebyshevTarget125) :
    GeneralRealQSPPolynomial127 where
  polynomial := chebyshevPolynomial041 target
  degree := target.L
  degree_bound := chebyshevPolynomial041_natDegree_bound target
  parity_law := by
    intro x
    have hodd : target.L % 2 = 1 := target.L_odd
    simp [hodd, chebyshevPolynomial041_parity]
  bounded_on_unitInterval := by
    intro x hx0 hx1
    exact chebyshevPolynomial041_unit_bound target x hx0 hx1

end
end SpectralSamplingProof.Analytic
