import QLean.Circuits.FiniteKernelCircuit
import QLean.Circuits.FiniteOuterResources
import QLean.SignalProcessing.QSPDefaultPhaseShape

/-! Exact resources without synthesis of phase angles. Numeric users may
use the planned result only after the decidable shape check passes. -/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.FiniteKernelCircuit

open VerifiedCircuitCore M13bFiniteOuterCompiler
open QLean.Circuits.FiniteScientificCircuitSource
open QLean.Circuits.CheckpointCircuits

def signalGateCount (input : Input) : Nat :=
  controlCost (input.source.outerPlan input.fits).layout
    (input.source.outerPlan input.fits).signalCircuit

def phaseGateCount (input : Input) : Nat :=
  controlCost (input.source.outerPlan input.fits).layout
    (input.source.imagePhaseCircuit input.fits .pi)

/-- Exact count before any angle-dependent simplification. Only the finite
request's degree and the actual signal/image-phase compiler costs are used. -/
def plannedGateCount (input : Input) : Nat :=
  11 + 4 * (input.polynomialRequest.degree * signalGateCount input +
    input.polynomialRequest.phaseCount * phaseGateCount input) + phaseGateCount input

theorem imagePhase_controlCost (input : Input) (angle : AngleExpr) :
    controlCost (input.source.outerPlan input.fits).layout
      (input.source.imagePhaseCircuit input.fits angle) = phaseGateCount input := by
  unfold phaseGateCount
  simp only [FiniteScientificSource.imagePhaseCircuit,
    NativeExactBasisPhase.booleanProgramPhaseCircuitExpr,
    controlCost_seq, controlCost_gate, leafCost_phase]

theorem programCost_cp03 {Angle : Type} [VerifiedCircuitCore.QSPCircuitAngle Angle]
    (word : VerifiedMath.Quantum.QSP.Word Angle) (signal phase : Nat) :
    programCost signal phase (cp03ProgramWord word) =
      VerifiedMath.Quantum.QSP.shapeCost signal phase
        (word.map VerifiedMath.Quantum.QSP.Step.shape) := by
  induction word with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | signal direction => cases direction <;> simpa [cp03ProgramWord, cp03ProgramStep,
          programCost, VerifiedMath.Quantum.QSP.shapeCost, VerifiedMath.Quantum.QSP.Step.shape] using ih
      | projectorPhase role angle => cases role <;> simpa [cp03ProgramWord, cp03ProgramStep,
          programCost, VerifiedMath.Quantum.QSP.shapeCost, VerifiedMath.Quantum.QSP.Step.shape] using ih

theorem plannedGateCount_exact {Angle : Type} [VerifiedCircuitCore.QSPCircuitAngle Angle]
    (input : Input) (provider : VerifiedMath.Quantum.QSP.FinitePhaseProvider Angle)
    (shape : (provider input.polynomialRequest).map VerifiedMath.Quantum.QSP.Step.shape =
      input.polynomialRequest.expectedShape) :
    plannedGateCount input = (kernelReflectionCircuit input provider).gateCount := by
  rw [kernelReflectionCircuit, Circuit.closeSymbolsPreserving, Circuit.gateCount_mapGates]
  rw [compile_gateCount (input.source.outerPlan input.fits) (phaseGateCount input)
    (imagePhase_controlCost input) (imagePhase_controlCost input)]
  rw [programCost_cp03, VerifiedMath.Quantum.QSP.shapeCost_of_planned _ _ shape]
  rfl

/-- The existence-based provider meets the same computable schedule shape.
No numerical angles are evaluated by this gate-count function. -/
theorem plannedGateCount_default (input : Input) :
    plannedGateCount input =
      (kernelReflectionCircuit input VerifiedMath.Quantum.QSP.defaultPhaseProvider).gateCount := by
  apply plannedGateCount_exact
  apply VerifiedMath.Quantum.QSP.defaultPhaseProvider_finite_odd_shape
  exact FiniteKernelPolynomial.degree_odd _ _ _ _

end QLean.Circuits.FiniteKernelCircuit
