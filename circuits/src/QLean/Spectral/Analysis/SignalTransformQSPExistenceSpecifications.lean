import QLean.Spectral.Analysis.SignalTransformPhaseScheduleSpecifications

/-!
# Certificate boundary for two-projector QSP phase synthesis

This module separates three statements which must not be conflated:

* the exact two-dimensional semantics of an arbitrary role-aware phase word;
* existence of some phase word realizing a requested scalar response;
* a particular analytic or numerical method for finding such a word.

In particular, the Yoder--Low--Chuang arccot formula is not part of the
definition of QSP implementability.  It may provide one witness, while a
numerical phase solver may provide another.  The realized response below is
definitionally tied to the independent transfer-matrix evaluator, so it
cannot be filled with the target response to make a certificate tautological.
-/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-- An ideal two-projector QSP word together with the unit global phase used
to read its real scalar response.  `steps` is in source execution order. -/
structure TwoProjectorQSPPhasePlan where
  steps : List FixedPointRoleAwarePhaseStep
  globalPhase : Complex
  globalPhase_unitNormSq : Complex.normSq globalPhase = 1

/-- Exact complex source/failure amplitude of an arbitrary ideal QSP word. -/
def TwoProjectorQSPPhasePlan.complexFailureAmplitude
    (plan : TwoProjectorQSPPhasePlan) (successProbability : Real) : Complex :=
  fixedPointRealizedComplexFailureAmplitude successProbability plan.steps

/-- Human-facing scalar response after removing the plan's certified unit
global phase.  No arbitrary response function is stored in the plan. -/
def TwoProjectorQSPPhasePlan.realizedScalarResponse
    (plan : TwoProjectorQSPPhasePlan) (successProbability : Real) : Real :=
  phaseCorrectedRealFailureAmplitude plan.globalPhase
    (plan.complexFailureAmplitude successProbability)

/-- A proof that one concrete ideal phase word realizes a requested scalar
response on its promised domain. -/
structure TwoProjectorQSPRealizationCertificate
    (target : TargetScalarResponseSpecification)
    (plan : TwoProjectorQSPPhasePlan) : Prop where
  response_matches : forall value,
    target.parameterDomain value ->
      plan.realizedScalarResponse value = target.response value
  parity_matches : target.parityLaw

/-! ## Fixed-point Chebyshev specialization without a closed-form dependency -/

end

end SpectralSamplingProof.Analytic
