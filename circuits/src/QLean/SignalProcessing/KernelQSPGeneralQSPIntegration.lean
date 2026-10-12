import QLean.SignalProcessing.KernelQSPKernelParameters
import QLean.SignalProcessing.QSPExistenceSignedEndpointSchedule

namespace KernelQSPGeneralQSPIntegration

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open PhaseScheduleProofs
open JenningsHistory

noncomputable section

/-!
  This module is the endpoint/QSP adapter for the parameter-general kernel
  shell.  It deliberately uses the accepted signed real endpoint constructor;
  it does not assert the old YLC polynomial identity and it does not turn the
  complex completion into a universal Born identity.
-/

def kernelChebyshevTargetQSP126
    (params : KernelQSP.KernelGeneralParameters126) :
    PhaseScheduleProofs.ChebyshevTarget125 where
  delta := params.targetError
  L := KernelQSP.L_KRGeneral126 params
  delta_pos := params.targetError_pos
  delta_lt_one := params.targetError_lt_one
  L_pos := KernelQSP.L_KRGeneral126_pos params
  L_odd := KernelQSP.L_KRGeneral126_odd params

/-! The signed endpoint is exact on the real scalar domain.  Therefore the
    same closed data also satisfies the stricter internal `eta / 2` budget;
    the accepted endpoint theorem above remains the explicit `eta` boundary
    binding. -/

/-! Public kernel wrapper: no YLC identity or caller-supplied phase premise. -/

/-! q1/q3 are retained as endpoint regressions only. -/

end
end KernelQSPGeneralQSPIntegration
