import QLean.SignalProcessing.NativeConcreteP18QSPWitness
import QLean.SignalProcessing.KernelReflectionRightSVTSpectralTransfer
import QLean.SignalProcessing.M13bUnitaritySemanticVerification
import QLean.SignalProcessing.QSPExistenceSignedEndpointSchedule
import QLean.SignalProcessing.M13bExternallyControlledCompute
import QLean.SignalProcessing.M13bHadamardStateSemantics
import QLean.SignalProcessing.M13bHermitianReflectionScalar
import QLean.SignalProcessing.M13bTwoFrameHermitianDilation

set_option autoImplicit false

/-!
# M13b executable candidate

This module fixes the non-circular input-to-circuit part of M13b.  It derives
the KernelQSP phase certificate and the primitive compute--phase--uncompute
circuit from executable P18 input data.  It intentionally does not assert the
remaining whole-spectrum clean-compression theorem.
-/

namespace M13bPrimitiveCandidate

open VerifiedCircuitCore
open DalzellDilation
open NativeConcreteP18QSPWitness

noncomputable section

/-- Executable data from which both the proved P18 block circuit and the
KernelReflection certified mathematical input are derived.  No target operator or
semantic equality is a field of this input. -/
structure ExecutableInput119 where
  source : ExecutableHistoryExecutableHistory.AlignedCommonSource119
  domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source
  fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source
  assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source
  circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
    source domain fits assumptions

/-- The independent KernelReflection mathematical instance derived from executable
P18 assumptions. -/
def certifiedInput119 (input : ExecutableInput119) :
    CertifiedM13Input
      (ExecutableHistoryExecutableP18.ExecutableD119 input.source)
      (ExecutableHistoryExecutableP18.ExecutableC119 input.source)
      (ExecutableHistoryExecutableP18.ExecutableR119 input.source)
      (ExecutableHistoryExecutableP18.ExecutableM119 input.source)
      (ExecutableHistoryExecutableP18.ExecutableLabels119 input.source) :=
  ExecutableHistoryExecutableP18.executableP18Input119 input.source input.assumptions

/-- KernelQSP parameters are derived from the certified input and requested
error budget. -/
noncomputable def kernelQSPParameters119 (input : ExecutableInput119)
    (epsilon : ℝ) (epsilon_pos : 0 < epsilon) (epsilon_lt_two : epsilon < 2) :
    KernelQSP.KernelGeneralParameters126 :=
  kernelFilterParameters130 (certifiedInput119 input)
    epsilon epsilon_pos epsilon_lt_two

/-- The independently specified outer-reflection filter.  Its nonzero
sector is `ρ = 2 F² - 1`, the scalar induced by reflecting a Hermitianized
success amplitude.  It remains separate from `compileQSVT119` until the
missing clean/frame compression theorem has been supplied. -/
noncomputable def idealKernelFilter119 (input : ExecutableInput119)
    (epsilon : ℝ) (epsilon_pos : 0 < epsilon) (epsilon_lt_two : epsilon < 2) :
    ℝ → ℝ :=
  M13bHermitianReflectionScalar.rhoFromInput
    (certifiedInput119 input) epsilon epsilon_pos epsilon_lt_two

/-- KernelReflection proves the spectral error estimate for the independently
specified filter.  This is a mathematical bound only; no circuit-semantics
equality is hidden in the statement. -/
theorem idealKernelFilter119_error_bound
    (input : ExecutableInput119)
    (epsilon : ℝ) (epsilon_pos : 0 < epsilon) (epsilon_lt_two : epsilon < 2)
    (v : EuclideanSpace ℝ
      (GramOperator.ExtendedIndex
        (ExecutableHistoryExecutableP18.ExecutableD119 input.source)
        (ExecutableHistoryExecutableP18.ExecutableC119 input.source)
        (ExecutableHistoryExecutableP18.ExecutableLabels119 input.source))) :
    ‖DalzellDilation.gramFilterAction130
        (GramOperator.gNuOperator (certifiedInput119 input).base.system
          (certifiedInput119 input).base.alpha (certifiedInput119 input).base.nu)
        (idealKernelFilter119 input epsilon epsilon_pos epsilon_lt_two) v -
      WithLp.toLp 2 ((GramOperator.idealKernelReflection
        (certifiedInput119 input).base.system (certifiedInput119 input).base.alpha
        (certifiedInput119 input).base.nu (certifiedInput119 input).base.hdet).mulVec
          v.ofLp)‖ ≤ epsilon * ‖v‖ := by
  exact M13bHermitianReflectionScalar.gNu_rho_reflection_bound
    (certifiedInput119 input) epsilon epsilon_pos epsilon_lt_two v

end

end M13bPrimitiveCandidate
