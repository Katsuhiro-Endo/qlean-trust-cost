import QLean.SignalProcessing.NativeQSPWitnessTransferModel

/-!
# Two-frame physical semantics for non-normal signal block encodings

A single invariant `Fin 2` frame is too strong for a non-normal clean block:
a forward signal maps a right-singular sector to a left-singular sector.  This
module records the correct alternating source/target-frame interface and
proves the source-order list lift from its four one-step equations.
-/

namespace NativeQSPWitnessTwoFrameModel

open VerifiedCircuitCore
open ExecutableHistoryQbPlusCleanBlock
open NativeSignalQSVTActual
open SpectralSamplingProof.Analytic
open NativeFixedPointPrimitive

open NativeQSPWitnessTransferModel

noncomputable section

inductive ActiveFrame where
  | source
  | target
deriving DecidableEq

def frameAfter : ActiveFrame → FixedPointRoleAwarePhaseStep → Option ActiveFrame
  | .source, .signal .forward => some .target
  | .target, .signal .adjoint => some .source
  | .source, .projectorPhase .source _ => some .source
  | .target, .projectorPhase .target _ => some .target
  | _, _ => none

/-- A role-aware word is usable by the alternating two-frame realization only
when every step is applied in its designated frame. -/
inductive FrameWord : ActiveFrame → List FixedPointRoleAwarePhaseStep →
    ActiveFrame → Prop where
  | nil (frame : ActiveFrame) : FrameWord frame [] frame
  | cons {current next final : ActiveFrame}
      {step : FixedPointRoleAwarePhaseStep}
      {rest : List FixedPointRoleAwarePhaseStep}
      (transition : frameAfter current step = some next)
      (remaining : FrameWord next rest final) :
      FrameWord current (step :: rest) final

end

end NativeQSPWitnessTwoFrameModel
