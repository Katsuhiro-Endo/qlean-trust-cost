import QLean.Circuits.CheckpointCircuitImplementation
import QLean.Circuits.QSPProgramSyntax

/-! Conversion of a finite QSP program for CP03 and CP04. -/

set_option autoImplicit false
set_option warningAsError true

namespace QLean.Circuits.CheckpointCircuits

open VerifiedCircuitCore

/-- CP03 constructs the requested polynomial from PJ execution data and
converts the resulting generic QSP word. -/
noncomputable def cp03ProgramFromProvider
    {AngleType : Type} [VerifiedCircuitCore.QSPCircuitAngle AngleType]
    (request : M13bSpecification.KernelSynthesisRequest119)
    (phaseProvider : VerifiedMath.Quantum.QSP.PhaseProvider AngleType) :
    List NativeFixedPointPrimitive.PhaseProgramStep :=
  cp03ProgramWord
    (phaseProvider (M13bApprovedOddQSPBridge.approvedKernelPolynomial request))

theorem cp03ProgramStep_roleStepToGeneric
    (step : SpectralSamplingProof.Analytic.FixedPointRoleAwarePhaseStep) :
    cp03ProgramStep (VerifiedMath.Quantum.QSP.roleStepToGeneric step) =
      NativeFixedPointPrimitive.PhaseProgramStep.ofReal step := by
  cases step with
  | signal direction => cases direction <;> rfl
  | projectorPhase role angle => cases role <;> rfl

theorem cp03ProgramFromProvider_default_eq
    (request : M13bSpecification.KernelSynthesisRequest119) :
    cp03ProgramFromProvider request
        VerifiedMath.Quantum.QSP.defaultPhaseProvider =
      M13bApprovedOddQSPBridge.approvedKernelProgram request := by
  unfold cp03ProgramFromProvider
  rw [VerifiedMath.Quantum.QSP.defaultPhaseProvider_odd_steps
    (M13bApprovedOddQSPBridge.approvedKernelPolynomial request)
    (M13bApprovedOddQSPBridge.approvedKernelPolynomial_odd request)]
  have mapped : ∀ steps : List
      SpectralSamplingProof.Analytic.FixedPointRoleAwarePhaseStep,
      cp03ProgramWord (steps.map VerifiedMath.Quantum.QSP.roleStepToGeneric) =
        steps.map NativeFixedPointPrimitive.PhaseProgramStep.ofReal := by
    intro steps
    induction steps with
    | nil => rfl
    | cons step rest ih =>
        simp [cp03ProgramWord, cp03ProgramStep_roleStepToGeneric]
  simpa [M13bApprovedOddQSPBridge.approvedKernelProgram,
    M13bApprovedOddQSPBridge.approvedOddProgram] using
    mapped (SpectralSamplingProof.Analytic.approvedOddPhysicalWord
      (M13bApprovedOddQSPBridge.approvedKernelPolynomial request)
      (M13bApprovedOddQSPBridge.approvedKernelPolynomial_odd request))


end QLean.Circuits.CheckpointCircuits
