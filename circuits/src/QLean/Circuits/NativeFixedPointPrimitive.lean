import QLean.SignalProcessing.NativeSignalQSVTActual
import QLean.Spectral.Analysis.SignalTransformPhaseScheduleSpecifications
import Mathlib
import QLean.SignalProcessing.KernelQSPKernelParameters

set_option autoImplicit false

/-!
# Primitive fixed-point word

This is the physical, role-preserving compilation of the independently
specified fixed-point source word.  Projector phases use the exact primitive
angle expression `AngleExpr.const angle`; no signed KernelQSP schedule and no
PrimitiveCompilation compiler are imported here.

`aFp` is deliberately the *uncompute* orientation.  Hence the execution-order
circuit `[aFp.reverse, R_target, aFp]` denotes the desired
`A† R_target A` when `A` is the source-order fixed-point compute word.
-/

namespace NativeFixedPointPrimitive

open JenningsHistory
open VerifiedCircuitCore
open ExecutableHistoryQbPlusCleanBlock
open NativeSignalQSVTActual
open SpectralSamplingProof.Analytic

/-- Finite syntax for a role-aware QSP program.  Closed rational, decimal,
and π expressions survive compilation to primitive gates. -/
inductive PhaseProgramStep where
  | signal (direction : VerifiedCircuitCore.SignalDirection)
  | projectorPhase (role : FixedPointProjectorRole) (angle : AngleExpr)

noncomputable def PhaseProgramStep.eval (symbolValue : String → ℝ) :
    PhaseProgramStep → FixedPointRoleAwarePhaseStep
  | .signal direction => .signal direction
  | .projectorPhase role angle => .projectorPhase role (angle.eval symbolValue)

def PhaseProgramStep.IsSymbolFree : PhaseProgramStep → Prop
  | .signal _ => True
  | .projectorPhase _ angle => angle.IsSymbolFree

def PhaseProgram.IsSymbolFree (steps : List PhaseProgramStep) : Prop :=
  ∀ step ∈ steps, step.IsSymbolFree

noncomputable def PhaseProgramStep.ofReal :
    FixedPointRoleAwarePhaseStep → PhaseProgramStep
  | .signal direction => .signal direction
  | .projectorPhase role angle => .projectorPhase role (.const angle)

@[simp] theorem PhaseProgramStep.eval_ofReal
    (symbolValue : String → ℝ) (step : FixedPointRoleAwarePhaseStep) :
    (PhaseProgramStep.ofReal step).eval symbolValue = step := by
  cases step with
  | signal direction => rfl
  | projectorPhase role angle => rfl

theorem PhaseProgramStep.ofReal_isSymbolFree
    (step : FixedPointRoleAwarePhaseStep) :
    (PhaseProgramStep.ofReal step).IsSymbolFree := by
  cases step with
  | signal direction => trivial
  | projectorPhase role angle => trivial

theorem PhaseProgram.ofReal_isSymbolFree
    (steps : List FixedPointRoleAwarePhaseStep) :
    PhaseProgram.IsSymbolFree (steps.map PhaseProgramStep.ofReal) := by
  intro step hstep
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hstep
  exact PhaseProgramStep.ofReal_isSymbolFree original

end NativeFixedPointPrimitive
