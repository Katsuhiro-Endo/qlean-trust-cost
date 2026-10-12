import QLean.Circuits.NativeFixedPointPrimitive
import QLean.SignalProcessing.NativeSignalQSVTActual
import QLean.SignalProcessing.KernelQSPGeneralQSPIntegration
import QLean.Spectral.Analysis.SignalTransformQSPExistenceSpecifications

/-!
# Lifting a one-step physical transfer model to arbitrary QSP words

The primitive compiler already fixes execution order.  This module isolates
the only physical hypothesis still needed to compare that word with the
independent two-dimensional evaluator: an invariant two-dimensional transfer
model for each compiled step.  A list induction then proves the comparison for
every QSP witness plan.
-/

namespace NativeQSPWitnessTransferModel

open VerifiedCircuitCore
open ExecutableHistoryQbPlusCleanBlock
open NativeSignalQSVTActual
open SpectralSamplingProof.Analytic
open NativeFixedPointPrimitive

noncomputable section

/-- The source-order two-dimensional matrix word, written with the same
execution convention as `compiledOperatorWord`. -/
noncomputable def abstractTransferWord
    (successProbability : ℝ)
    (steps : List FixedPointRoleAwarePhaseStep) : FixedPointTransferMatrix :=
  VerifiedCircuitCore.operatorSequence
    (steps.map (fixedPointRoleAwareStepTransferMatrix successProbability))

/- A one-step physical transfer witness lifts by list induction to the whole
source-order primitive word. -/
set_option maxHeartbeats 800000 in

end

end NativeQSPWitnessTransferModel
