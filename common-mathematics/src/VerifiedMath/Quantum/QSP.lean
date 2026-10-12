import Mathlib

/-!
A circuit-independent, two-dimensional real-QSP response contract.  Its
matrix word has the same source-order convention as the physical compiler,
but mentions neither a circuit AST nor an application-specific reflection.
-/

set_option autoImplicit false

namespace VerifiedMath.Quantum.QSP

/-- Human-facing input for real-polynomial QSP.  The polynomial is specified
on the full signed interval; the circuit may evaluate it only on nonnegative
singular values.  Its parity agrees with the chosen query degree. -/
structure AdmissibleRealPolynomial where
  polynomial : Polynomial ℝ
  degree : Nat
  degree_bound : polynomial.natDegree ≤ degree
  parity_law : ∀ x : ℝ,
    Polynomial.eval (-x) polynomial =
      if degree % 2 = 0 then Polynomial.eval x polynomial
      else -Polynomial.eval x polynomial
  bounded_on_unitInterval : ∀ x : ℝ, -1 ≤ x → x ≤ 1 →
    |Polynomial.eval x polynomial| ≤ 1

/-- The same approved polynomial read on the physical singular-value domain.
No new polynomial or correctness assumption is introduced by this readout. -/
def AdmissibleRealPolynomial.singularValueResponse
    (input : AdmissibleRealPolynomial) (x : ℝ) : ℝ :=
  Polynomial.eval x input.polynomial

/-- The Hermitianized response used by the kernel-reflection construction is
not the polynomial synthesized by QSP.  It is this separate nonlinear
readout of that polynomial. -/
def AdmissibleRealPolynomial.hermitianizedResponse
    (input : AdmissibleRealPolynomial) (x : ℝ) : ℝ :=
  2 * input.singularValueResponse x ^ 2 - 1

inductive Direction where
  | forward
  | adjoint
  deriving DecidableEq, Repr

inductive Role where
  | source
  | target
  deriving DecidableEq, Repr

inductive Step (AngleType : Type) where
  | signal (direction : Direction)
  | projectorPhase (role : Role) (angle : AngleType)

abbrev Word (AngleType : Type) := List (Step AngleType)

/-- Application-independent phase source. The request consists solely of a
polynomial and its degree, parity, and interval-bound proofs. The angle type
is left abstract so a proof can use real phases while an executable caller
retains finite angle syntax. -/
abbrev PhaseProvider (AngleType : Type) :=
  AdmissibleRealPolynomial → Word AngleType

inductive Frame where
  | source
  | target
  deriving DecidableEq, Repr

def frameAfter {AngleType : Type} : Frame → Step AngleType → Option Frame
  | .source, .signal .forward => some .target
  | .target, .signal .adjoint => some .source
  | .source, .projectorPhase .source _ => some .source
  | .target, .projectorPhase .target _ => some .target
  | _, _ => none

inductive ValidWord {AngleType : Type} : Frame → Word AngleType → Frame → Prop where
  | nil (frame : Frame) : ValidWord frame [] frame
  | cons {current next final : Frame} {step : Step AngleType}
      {rest : Word AngleType}
      (transition : frameAfter current step = some next)
      (remaining : ValidWord next rest final) :
      ValidWord current (step :: rest) final

noncomputable section

abbrev Transfer := Matrix (Fin 2) (Fin 2) ℂ

private def sourceAmplitude (probability : ℝ) : ℝ :=
  Real.sqrt (max 0 (1 - probability))

private def targetAmplitude (probability : ℝ) : ℝ :=
  Real.sqrt (max 0 probability)

def signalTransfer (probability : ℝ) : Direction → Transfer
  | .forward => fun row column =>
      let bad : ℂ := sourceAmplitude probability
      let good : ℂ := targetAmplitude probability
      match row.val, column.val with
      | 0, 0 => bad
      | 0, _ => -good
      | _, 0 => good
      | _, _ => bad
  | .adjoint => fun row column =>
      let bad : ℂ := sourceAmplitude probability
      let good : ℂ := targetAmplitude probability
      match row.val, column.val with
      | 0, 0 => bad
      | 0, _ => good
      | _, 0 => -good
      | _, _ => bad

def projectorTransfer (role : Role) (angle : ℝ) : Transfer :=
  fun row column =>
    if row ≠ column then 0
    else match role with
      | .source => if row = (0 : Fin 2)
          then Complex.exp (Complex.I * (angle : ℂ)) else 1
      | .target => if row = (1 : Fin 2)
          then Complex.exp (Complex.I * (angle : ℂ)) else 1

def stepTransfer (probability : ℝ) : Step ℝ → Transfer
  | .signal direction => signalTransfer probability direction
  | .projectorPhase role angle => projectorTransfer role angle

/-- Head-to-tail execution, with each new operator multiplied on the left. -/
def wordTransfer (probability : ℝ) : Word ℝ → Transfer
  | [] => 1
  | step :: rest => wordTransfer probability rest * stepTransfer probability step

/-- The physical Hermitianization uses the real source amplitude squared.
It is not the generally different quantity `2 * ‖a‖^2 - 1`. -/
def hermitianResponse (word : Word ℝ) (sigma : ℝ) : ℝ :=
  2 * ((wordTransfer (sigma ^ 2) word) 0 0).re ^ 2 - 1

structure Request where
  target : ℝ → ℝ
  error : ℝ
  error_nonneg : 0 ≤ error

def Satisfies (request : Request) (word : Word ℝ) : Prop :=
  ValidWord .source word .target ∧
    ∀ sigma : ℝ, 0 ≤ sigma → sigma ≤ 1 →
      |hermitianResponse word sigma - request.target sigma| ≤ request.error

end

end VerifiedMath.Quantum.QSP
