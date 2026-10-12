import Mathlib
import QLean.History.Jennings.PureSpec
import QLean.SignalProcessing.PhaseScheduleProofsPhaseWordContract
import QLean.SignalProcessing.PhaseScheduleProofsChebyshevContract
import QLean.Spectral.Analysis.SignalTransformScalarResponseSpecifications
import QLean.Spectral.Analysis.SignalTransformSpecifications
import QLean.Spectral.Analysis.SignalTransformPhaseScheduleSpecifications
import QLean.Spectral.Analysis.SignalTransformPhaseRecurrenceSpecifications
import QLean.Spectral.Analysis.SignalTransformChebyshevRecurrenceCore
import QLean.Spectral.Analysis.SignalTransformQSPExistenceSpecifications

noncomputable section

open scoped BigOperators
open Complex
open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open PhaseScheduleProofs
open JenningsHistory

namespace KernelQSP

def leastOddAtLeast126 (lower : Nat) : Nat :=
  if lower % 2 = 1 then lower else lower + 1

lemma leastOddAtLeast126_lower (lower : Nat) :
    lower <= leastOddAtLeast126 lower := by
  by_cases h : lower % 2 = 1
  · simp [leastOddAtLeast126, h]
  · simp [leastOddAtLeast126, h]

lemma leastOddAtLeast126_odd (lower : Nat) :
    leastOddAtLeast126 lower % 2 = 1 := by
  by_cases h : lower % 2 = 1
  · simp [leastOddAtLeast126, h]
  · simp [leastOddAtLeast126, h]
    omega

/-! ## Parameter-general integration shell (the q3 path remains only as a
    regression object; these definitions do not constrain gap or eta). -/

structure KernelGeneralParameters126 where
  gap : ℝ
  targetError : ℝ
  gap_pos : 0 < gap
  gap_le_one : gap ≤ 1
  targetError_pos : 0 < targetError
  targetError_lt_one : targetError < 1

def gapEtaProductGeneral126 (params : KernelGeneralParameters126) : ℝ :=
  params.gap * params.targetError

/-- The real-valued analytic lower bound is converted to a Nat by the
    Archimedean property; it is not a caller-supplied query length. -/
noncomputable def queryLowerBoundGeneral126
    (params : KernelGeneralParameters126) : Nat :=
  Nat.find (exists_nat_gt
    (1 / gapEtaProductGeneral126 params))

lemma queryLowerBoundGeneral126_spec
    (params : KernelGeneralParameters126) :
    1 / gapEtaProductGeneral126 params <
      (queryLowerBoundGeneral126 params : ℝ) := by
  exact Nat.find_spec (exists_nat_gt
    (1 / gapEtaProductGeneral126 params))

lemma queryLowerBoundGeneral126_pos
    (params : KernelGeneralParameters126) :
    0 < queryLowerBoundGeneral126 params := by
  have hrec : 0 < 1 / gapEtaProductGeneral126 params := by
    unfold gapEtaProductGeneral126
    exact one_div_pos.mpr (mul_pos params.gap_pos params.targetError_pos)
  have hreal :
      (0 : ℝ) < (queryLowerBoundGeneral126 params : ℝ) := by
    have hspec := queryLowerBoundGeneral126_spec params
    linarith
  exact_mod_cast hreal

noncomputable def L_KRGeneral126
    (params : KernelGeneralParameters126) : Nat :=
  leastOddAtLeast126 (queryLowerBoundGeneral126 params)

lemma L_KRGeneral126_lower
    (params : KernelGeneralParameters126) :
    queryLowerBoundGeneral126 params ≤ L_KRGeneral126 params :=
  leastOddAtLeast126_lower _

lemma L_KRGeneral126_pos
    (params : KernelGeneralParameters126) :
    0 < L_KRGeneral126 params := by
  have hq := queryLowerBoundGeneral126_pos params
  have hl := L_KRGeneral126_lower params
  omega

lemma L_KRGeneral126_odd
    (params : KernelGeneralParameters126) :
    L_KRGeneral126 params % 2 = 1 :=
  leastOddAtLeast126_odd _

def fixedPointParametersGeneral126
    (params : KernelGeneralParameters126) :
    FixedPointChebyshevParameters where
  failureAmplitude := params.targetError
  queryLength := L_KRGeneral126 params
  failureAmplitude_positive := params.targetError_pos
  failureAmplitude_lt_one := params.targetError_lt_one
  queryLength_positive := L_KRGeneral126_pos params
  queryLength_odd := L_KRGeneral126_odd params

end KernelQSP
