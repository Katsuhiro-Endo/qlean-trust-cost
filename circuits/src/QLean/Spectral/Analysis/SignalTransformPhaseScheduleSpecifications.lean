import QLean.Spectral.Analysis.SignalTransformSpecifications
import QLean.Spectral.Analysis.SignalTransformScalarResponseSpecifications

/-! Exact two-dimensional transfer-matrix semantics used in the kernel proof. -/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## Common exact index and source-order vocabulary -/

/-- The two alternating projector roles must remain visible even when an
application happens to implement them using the same basis predicate. -/
inductive FixedPointProjectorRole where
  | source
  | target
  deriving DecidableEq, Repr

/-- Role-preserving fixed-point schedule step.  S3a keeps this richer word and
only then erases it to the current generic `ScientificPhaseStep` interface. -/
inductive FixedPointRoleAwarePhaseStep where
  | signal (direction : SignalDirection)
  | projectorPhase (role : FixedPointProjectorRole) (angle : ℝ)

/-! ## Independent two-dimensional scientific-word semantics -/

/-- The exact two-dimensional transfer matrix used to give mathematical
meaning to the role-aware scientific word.  Coordinate zero is the source
(`bad`) direction and coordinate one is the target (`good`) direction. -/
abbrev FixedPointTransferMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- A state in the independent two-dimensional transfer model. -/
abbrev FixedPointTransferState := Fin 2 → ℂ

def fixedPointSourceIndex : Fin 2 := ⟨0, by decide⟩

def fixedPointTargetIndex : Fin 2 := ⟨1, by decide⟩

/-- The source basis vector before the initial signal query. -/
def fixedPointSourceBasisState : FixedPointTransferState :=
  fun index => if index = fixedPointSourceIndex then 1 else 0

/-- Real source (`bad`) amplitude in the canonical two-dimensional signal
matrix.  `max` makes the evaluator total on all real inputs; the S1 parameter
domain later restricts its scientific use. -/
def fixedPointSourceAmplitude (successProbability : ℝ) : ℝ :=
  Real.sqrt (max 0 (1 - successProbability))

/-- Real target (`good`) amplitude in the canonical two-dimensional signal
matrix. -/
def fixedPointTargetAmplitude (successProbability : ℝ) : ℝ :=
  Real.sqrt (max 0 successProbability)

/-- Canonical signal transfer matrix
`[[bad,-good],[good,bad]]`.  Its adjoint direction is written explicitly rather
than delegated to any circuit/operator evaluator. -/
def fixedPointSignalTransferMatrix
    (successProbability : ℝ) (direction : SignalDirection) :
    FixedPointTransferMatrix :=
  fun row column =>
    let bad : ℂ := fixedPointSourceAmplitude successProbability
    let good : ℂ := fixedPointTargetAmplitude successProbability
    match direction, row.val, column.val with
    | .forward, 0, 0 => bad
    | .forward, 0, _ => -good
    | .forward, _, 0 => good
    | .forward, _, _ => bad
    | .adjoint, 0, 0 => bad
    | .adjoint, 0, _ => good
    | .adjoint, _, 0 => -good
    | .adjoint, _, _ => bad

/-- Exact role-sensitive projector phase.  A source phase acts on coordinate
zero and a target phase acts on coordinate one. -/
def fixedPointProjectorTransferMatrix
    (role : FixedPointProjectorRole) (angle : ℝ) :
    FixedPointTransferMatrix :=
  fun row column =>
    if row ≠ column then 0
    else
      match role with
      | .source =>
          if row = fixedPointSourceIndex
          then Complex.exp (Complex.I * (angle : ℂ))
          else 1
      | .target =>
          if row = fixedPointTargetIndex
          then Complex.exp (Complex.I * (angle : ℂ))
          else 1

/-- One independently evaluated scientific instruction. -/
def fixedPointRoleAwareStepTransferMatrix
    (successProbability : ℝ) :
    FixedPointRoleAwarePhaseStep → FixedPointTransferMatrix
  | .signal direction =>
      fixedPointSignalTransferMatrix successProbability direction
  | .projectorPhase role angle =>
      fixedPointProjectorTransferMatrix role angle

/-- Source execution order is head-to-tail.  Therefore each newly executed
matrix multiplies the accumulated operator on the left.  This definition is
the independent `operator_eq_product` normal form for an S3a word. -/
def fixedPointSourceOrderTransferMatrix
    (successProbability : ℝ)
    (steps : List FixedPointRoleAwarePhaseStep) : FixedPointTransferMatrix :=
  steps.foldl
    (fun accumulated step =>
      fixedPointRoleAwareStepTransferMatrix successProbability step *
        accumulated)
    1

theorem fixedPointSourceOrderTransferMatrix_append
    (successProbability : ℝ)
    (initialSteps finalSteps : List FixedPointRoleAwarePhaseStep) :
    fixedPointSourceOrderTransferMatrix successProbability
        (initialSteps ++ finalSteps) =
      finalSteps.foldl
        (fun accumulated step =>
          fixedPointRoleAwareStepTransferMatrix successProbability step *
            accumulated)
        (fixedPointSourceOrderTransferMatrix successProbability
          initialSteps) := by
  simp [fixedPointSourceOrderTransferMatrix, List.foldl_append]

/-- Final state obtained by applying the independently evaluated source-order
word to the source basis state. -/
def fixedPointEvaluatedState
    (successProbability : ℝ)
    (steps : List FixedPointRoleAwarePhaseStep) : FixedPointTransferState :=
  (fixedPointSourceOrderTransferMatrix successProbability steps).mulVec
    fixedPointSourceBasisState

/-- Complex source/failure amplitude produced by the exact 2D recurrence. -/
def fixedPointRealizedComplexFailureAmplitude
    (successProbability : ℝ)
    (steps : List FixedPointRoleAwarePhaseStep) : ℂ :=
  fixedPointEvaluatedState successProbability steps fixedPointSourceIndex

/-! ## Small, transparent state recurrence used to lock source order -/

/-- A named two-coordinate state.  This makes low-degree source-order checks
readable without treating a matrix product as the human-facing semantics. -/
def fixedPointPairState (source target : ℂ) : FixedPointTransferState :=
  fun index => if index = fixedPointSourceIndex then source else target

/-- Applying one forward signal query to named coordinates. -/
theorem fixedPointSignalTransferMatrix_forward_mulVec_pairState
    (successProbability : ℝ) (source target : ℂ) :
    (fixedPointSignalTransferMatrix successProbability .forward).mulVec
        (fixedPointPairState source target) =
      fixedPointPairState
        ((fixedPointSourceAmplitude successProbability : ℂ) * source -
          (fixedPointTargetAmplitude successProbability : ℂ) * target)
        ((fixedPointTargetAmplitude successProbability : ℂ) * source +
          (fixedPointSourceAmplitude successProbability : ℂ) * target) := by
  funext index
  fin_cases index
  · simp [fixedPointSignalTransferMatrix, fixedPointPairState,
      fixedPointSourceIndex, Matrix.mulVec, dotProduct]
    ring
  · simp [fixedPointSignalTransferMatrix, fixedPointPairState,
      fixedPointSourceIndex, Matrix.mulVec, dotProduct]

/-- Applying one adjoint signal query to named coordinates. -/
theorem fixedPointSignalTransferMatrix_adjoint_mulVec_pairState
    (successProbability : ℝ) (source target : ℂ) :
    (fixedPointSignalTransferMatrix successProbability .adjoint).mulVec
        (fixedPointPairState source target) =
      fixedPointPairState
        ((fixedPointSourceAmplitude successProbability : ℂ) * source +
          (fixedPointTargetAmplitude successProbability : ℂ) * target)
        (-(fixedPointTargetAmplitude successProbability : ℂ) * source +
          (fixedPointSourceAmplitude successProbability : ℂ) * target) := by
  funext index
  fin_cases index <;>
    simp [fixedPointSignalTransferMatrix, fixedPointPairState,
      fixedPointSourceIndex, Matrix.mulVec, dotProduct]

/-- Applying a source-projector phase to named coordinates. -/
theorem fixedPointProjectorTransferMatrix_source_mulVec_pairState
    (angle : ℝ) (source target : ℂ) :
    (fixedPointProjectorTransferMatrix .source angle).mulVec
        (fixedPointPairState source target) =
      fixedPointPairState
        (Complex.exp (Complex.I * (angle : ℂ)) * source) target := by
  funext index
  fin_cases index <;>
    simp [fixedPointProjectorTransferMatrix, fixedPointPairState,
      fixedPointSourceIndex, Matrix.mulVec, dotProduct]

/-- Applying a target-projector phase to named coordinates. -/
theorem fixedPointProjectorTransferMatrix_target_mulVec_pairState
    (angle : ℝ) (source target : ℂ) :
    (fixedPointProjectorTransferMatrix .target angle).mulVec
        (fixedPointPairState source target) =
      fixedPointPairState source
        (Complex.exp (Complex.I * (angle : ℂ)) * target) := by
  funext index
  fin_cases index <;>
    simp [fixedPointProjectorTransferMatrix, fixedPointPairState,
      fixedPointSourceIndex, fixedPointTargetIndex, Matrix.mulVec, dotProduct]

/-- Direct state recurrence in source execution order. -/
def fixedPointExecuteSteps
    (successProbability : ℝ)
    (steps : List FixedPointRoleAwarePhaseStep)
    (initialState : FixedPointTransferState) : FixedPointTransferState :=
  steps.foldl
    (fun state step =>
      (fixedPointRoleAwareStepTransferMatrix successProbability step).mulVec
        state)
    initialState

/-! ## Schedule-determined global phase and corrected scalar response -/

/-- Undo a known unit global phase before extracting a real scalar. -/
def phaseCorrectedRealFailureAmplitude
    (globalPhase amplitude : ℂ) : ℝ :=
  (star globalPhase * amplitude).re





end

end SpectralSamplingProof.Analytic
