import QLean.SignalProcessing.QSPExistenceIntervalCompletionFactorization
import QLean.Spectral.Analysis.SignalTransformQSPExistenceSpecifications
import QLean.Spectral.Analysis.SignalTransformPhaseRecurrenceSpecifications

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## The evaluator-native target

The independent evaluator takes a success probability `s`; its first
coordinate is the source amplitude `sqrt (max 0 (1-s))`.  This target keeps
that convention explicit instead of silently treating `s` as the polynomial
variable. -/

def nativeQSPTarget024
    (input : GeneralRealQSPPolynomial127) :
    TargetScalarResponseSpecification where
  parameterDomain := fun s : ℝ => 0 ≤ s ∧ s ≤ 1
  response := fun s : ℝ =>
    Polynomial.eval (fixedPointSourceAmplitude s) input.polynomial
  parity := .unrestricted

theorem nativeQSPTarget024_parityLaw
    (input : GeneralRealQSPPolynomial127) :
    (nativeQSPTarget024 input).parityLaw := by
  trivial

/-! ## The accepted interval completion as a real paraunitary column -/

structure QSPPolynomialPair024
    (input : GeneralRealQSPPolynomial127) where
  P : Polynomial ℝ
  B : Polynomial ℝ
  C : Polynomial ℝ
  P_eq : P = input.polynomial
  identity :
    P ^ 2 + B ^ 2 +
        (1 - (Polynomial.X : Polynomial ℝ) ^ 2) * C ^ 2 = 1
  P_degree : P.natDegree ≤ input.degree
  B_degree : B.degree ≤ (input.degree : WithBot ℕ)
  C_degree : C.degree < (input.degree : WithBot ℕ)

noncomputable def completionWitness024
    (input : GeneralRealQSPPolynomial127) :
    IntervalCompletionWitness127 input :=
  Classical.choice (interval_completion_witness023 input)

noncomputable def completionPair024
    (input : GeneralRealQSPPolynomial127) :
    QSPPolynomialPair024 input where
  P := input.polynomial
  B := (completionWitness024 input).B
  C := (completionWitness024 input).C
  P_eq := rfl
  identity := by
    calc
      input.polynomial ^ 2 + (completionWitness024 input).B ^ 2 +
          (1 - (Polynomial.X : Polynomial ℝ) ^ 2) *
            (completionWitness024 input).C ^ 2 =
          input.polynomial ^ 2 + intervalResidual127 input := by
            rw [(completionWitness024 input).identity]
            ring
      _ = 1 := by
        simp [intervalResidual127]
  P_degree := input.degree_bound
  B_degree := (completionWitness024 input).B_degree
  C_degree := (completionWitness024 input).C_degree

theorem completionPair_eval_identity024
    (input : GeneralRealQSPPolynomial127) (x : ℝ) :
    (Polynomial.eval x (completionPair024 input).P) ^ 2 +
        (Polynomial.eval x (completionPair024 input).B) ^ 2 +
        (1 - x ^ 2) *
          (Polynomial.eval x (completionPair024 input).C) ^ 2 = 1 := by
  have h := congrArg (fun r : Polynomial ℝ => Polynomial.eval x r)
    (completionPair024 input).identity
  simpa using h

/-! ## Actual source-order interface and the remaining extraction obligation -/

/-! This is intentionally an obligation, not a postulated theorem.  The
    accepted boundary supplies no degree-reducing phase-extraction constructor
    connecting the paraunitary pair above to the actual evaluator-native word. -/

end

end SpectralSamplingProof.Analytic
