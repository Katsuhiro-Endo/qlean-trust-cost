import QLean.SignalProcessing.M13bUnitaritySemanticVerification
import QLean.SignalProcessing.QSPExistenceSignedEndpointSchedule

/-!
# M13b: complementary-coordinate bridge for the selected KernelQSP target

The concrete two-frame primitive uses the complementary amplitude `g`, while
the M13b kernel theorem is stated in the success probability `sigma^2`.
This file proves that the *fixed*, selected KernelQSP Chebyshev target has
exactly the latter scalar value after the relation `g^2 + sigma^2 = 1` is
supplied.  It deliberately does not identify a circuit denotation with that
real scalar; that is the separate real-part extraction obligation.
-/

set_option autoImplicit false

namespace M13bChebyshevCoordinateBridge

open SpectralSamplingProof.Analytic

noncomputable section

/-- The KernelQSP Chebyshev target evaluated at the nonnegative complementary
amplitude is the fixed-point failure response evaluated at the associated
success probability. -/
theorem kernelQSP_chebyshev_response_at_complementary_amplitude
    (params : KernelQSP.KernelGeneralParameters126)
    (g sigma : ℝ)
    (g_nonneg : 0 ≤ g)
    (completion : g ^ 2 + sigma ^ 2 = 1) :
    PhaseScheduleProofs.chebyshevResponse125
        (KernelQSPGeneralQSPIntegration.kernelChebyshevTargetQSP126 params) g =
      fixedPointChebyshevFailureResponse
        (KernelQSP.fixedPointParametersGeneral126 params) (sigma ^ 2) := by
  have hcomplement : 1 - sigma ^ 2 = g ^ 2 := by
    nlinarith [completion]
  have hmax : max 0 (1 - sigma ^ 2) = g ^ 2 := by
    rw [hcomplement]
    exact max_eq_right (sq_nonneg g)
  have hsqrt : Real.sqrt (max 0 (1 - sigma ^ 2)) = g := by
    rw [hmax, Real.sqrt_sq_eq_abs, abs_of_nonneg g_nonneg]
  unfold PhaseScheduleProofs.chebyshevResponse125 PhaseScheduleProofs.chebyshevScale125
    fixedPointChebyshevFailureResponse
    KernelQSPGeneralQSPIntegration.kernelChebyshevTargetQSP126
    KernelQSP.fixedPointParametersGeneral126
  rw [hsqrt]
  rfl

end

end M13bChebyshevCoordinateBridge
