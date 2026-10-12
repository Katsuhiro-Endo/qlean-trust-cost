import QLean.SignalProcessing.QSPExistenceSingleQuerySynthesis

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## Source-order bridge

`StandardWordStep034` is the proof-side name used by the accepted generic
polynomial synthesis.  The canonical evaluator has the role-aware step type;
this file only erases the proof-side abbreviation by an explicit, order
preserving map.  No response or certificate is stored in this map.
-/

def roleStepOfStandard035 : StandardWordStep034 → FixedPointRoleAwarePhaseStep
  | .signal => .signal .forward
  | .sourcePhase angle => .projectorPhase .source angle

def roleWordOfStandard035
    (word : List StandardWordStep034) :
    List FixedPointRoleAwarePhaseStep := word.map roleStepOfStandard035

theorem roleStepEval035
    (step : StandardWordStep034)
    (state : StandardQSPPolynomialState032) :
    standardPolynomialStep032 (roleStepOfStandard035 step) state =
      standardApplyWordStep034 step state := by
  cases step <;> rfl

theorem roleWordEval035
    (word : List StandardWordStep034)
    (state : StandardQSPPolynomialState032) :
    standardPolynomialSourceOrder032 (roleWordOfStandard035 word) state =
      standardWordEval034 word state := by
  induction word generalizing state with
  | nil => rfl
  | cons first rest ih =>
      change
        standardPolynomialSourceOrder032 (roleWordOfStandard035 rest)
            (standardPolynomialStep032
              (roleStepOfStandard035 first) state) =
          standardWordEval034 rest
            (standardApplyWordStep034 first state)
      rw [ih]
      exact congrArg (standardWordEval034 rest)
        (roleStepEval035 first state)

/-! ## Structural counts on the proof-side word -/

def standardSignalCount035 : List StandardWordStep034 → Nat
  | [] => 0
  | .signal :: rest => standardSignalCount035 rest + 1
  | .sourcePhase _ :: rest => standardSignalCount035 rest

def standardProjectorPhaseCount035 : List StandardWordStep034 → Nat
  | [] => 0
  | .signal :: rest => standardProjectorPhaseCount035 rest
  | .sourcePhase _ :: rest => standardProjectorPhaseCount035 rest + 1

theorem standardSignalCount035_append
    (left right : List StandardWordStep034) :
    standardSignalCount035 (left ++ right) =
      standardSignalCount035 left + standardSignalCount035 right := by
  induction left with
  | nil => simp [standardSignalCount035]
  | cons first rest ih =>
      cases first with
      | signal =>
          simp [standardSignalCount035, ih, Nat.add_comm]
          omega
      | sourcePhase angle =>
          simp [standardSignalCount035, ih, Nat.add_comm]

theorem standardProjectorPhaseCount035_append
    (left right : List StandardWordStep034) :
    standardProjectorPhaseCount035 (left ++ right) =
      standardProjectorPhaseCount035 left +
        standardProjectorPhaseCount035 right := by
  induction left with
  | nil => simp [standardProjectorPhaseCount035]
  | cons first rest ih =>
      cases first with
      | signal =>
          simp [standardProjectorPhaseCount035, ih, Nat.add_comm]
      | sourcePhase angle =>
          simp [standardProjectorPhaseCount035, ih, Nat.add_comm]
          omega

theorem roleWordSignalCount035
    (word : List StandardWordStep034) :
    signalCount127 (roleWordOfStandard035 word) =
      standardSignalCount035 word := by
  induction word with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | signal =>
          change signalCount127
              (.signal .forward :: roleWordOfStandard035 rest) =
            standardSignalCount035 rest + 1
          simp [signalCount127, ih]
      | sourcePhase angle =>
          change signalCount127
              (.projectorPhase .source angle :: roleWordOfStandard035 rest) =
            standardSignalCount035 rest
          simp [signalCount127, ih]

theorem roleWordProjectorPhaseCount035
    (word : List StandardWordStep034) :
    projectorPhaseCount127 (roleWordOfStandard035 word) =
      standardProjectorPhaseCount035 word := by
  induction word with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | signal =>
          change projectorPhaseCount127
              (.signal .forward :: roleWordOfStandard035 rest) =
            standardProjectorPhaseCount035 rest
          simp [projectorPhaseCount127, ih]
      | sourcePhase angle =>
          change projectorPhaseCount127
              (.projectorPhase .source angle :: roleWordOfStandard035 rest) =
            standardProjectorPhaseCount035 rest + 1
          simp [projectorPhaseCount127, ih]

/-! ## Count-carrying version of the accepted degree recursion

The accepted 034 theorem already proves the state recursion.  The theorem
below repeats only its structural induction while carrying the two exact
counts, so the later canonical plan cannot infer counts from metadata.
-/

theorem exists_standardWordWithCounts035 :
    ∀ d : ℕ, ∀ c : StandardAdmissibility034, c.degree = d →
      ∃ word : List StandardWordStep034,
        standardWordEval034 word standardQ0State032 = c.state ∧
          standardSignalCount035 word = d ∧
          standardProjectorPhaseCount035 word = d + 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro c hcd
      by_cases hd0 : d = 0
      · have hc0 : c.degree = 0 := by omega
        obtain ⟨angle, hangle⟩ := standardBaseState034_phase_exists c hc0
        refine ⟨[.sourcePhase angle], ?_, ?_, ?_⟩
        · simpa [standardWordEval034, standardApplyWordStep034] using hangle
        · simp [standardSignalCount035, hd0]
        · simp [standardProjectorPhaseCount035, hd0]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        have hcpos : 0 < c.degree := by omega
        let e : StandardAdmissibility034 :=
          standardExtractedAdmissible034 c hcpos
        have hedeg : e.degree = d - 1 := by
          change c.degree - 1 = d - 1
          omega
        obtain ⟨word, hword, hsignal, hphase⟩ :=
          ih (d - 1) (by omega) e hedeg
        refine ⟨word ++
          [.signal, .sourcePhase (-(standardTopAngle034 c hcpos))],
          ?_, ?_, ?_⟩
        · rw [standardWordEval034_append, hword]
          change standardSourcePhase032
              (standardPhase032 (-(standardTopAngle034 c hcpos)))
              (standardSignalForward032
                (standardExtractedState034 c hcpos)) = c.state
          rw [standardExtractedState034_forward_establishedBridge c hcpos]
          exact standardSourcePhase032_inverse_angle034
            (standardTopAngle034 c hcpos) c.state
        · rw [standardSignalCount035_append]
          simp [standardSignalCount035, hsignal]
          omega
        · rw [standardProjectorPhaseCount035_append]
          simp [standardProjectorPhaseCount035, hphase]
          omega

noncomputable def standardSourceWord035
    (input : GeneralRealQSPPolynomial127) :
    List StandardWordStep034 :=
  Classical.choose (exists_standardWordWithCounts035 input.degree
    (completionAdmissible034 input) rfl)

theorem standardSourceWord035_spec
    (input : GeneralRealQSPPolynomial127) :
    standardWordEval034 (standardSourceWord035 input) standardQ0State032 =
        completionStandardState033 input ∧
      standardSignalCount035 (standardSourceWord035 input) = input.degree ∧
      standardProjectorPhaseCount035 (standardSourceWord035 input) =
        input.degree + 1 := by
  have h := Classical.choose_spec
    (exists_standardWordWithCounts035 input.degree
      (completionAdmissible034 input) rfl)
  refine ⟨?_, h.2.1, h.2.2⟩
  simpa [standardSourceWord035, completionAdmissible034] using h.1

/-! ## Canonical plan -/

noncomputable def canonicalRoleWord035
    (input : GeneralRealQSPPolynomial127) :
    List FixedPointRoleAwarePhaseStep :=
  roleWordOfStandard035 (standardSourceWord035 input)

noncomputable def canonicalPlan035
    (input : GeneralRealQSPPolynomial127) : TwoProjectorQSPPhasePlan where
  steps := canonicalRoleWord035 input
  globalPhase := 1
  globalPhase_unitNormSq := by norm_num

theorem standardPhysicalQ0_eq_basis035
    (successProbability : ℝ) :
    standardPhysicalState032
        (fixedPointSourceAmplitude successProbability)
        (fixedPointTargetAmplitude successProbability) standardQ0State032 =
      fixedPointSourceBasisState := by
  funext index
  fin_cases index <;>
    simp [standardPhysicalState032, standardQ0State032,
      fixedPointSourceBasisState, fixedPointPairState,
      fixedPointSourceIndex]

theorem canonicalRoleWord035_source_eval
    (input : GeneralRealQSPPolynomial127)
    (successProbability : ℝ)
    (hs0 : 0 ≤ successProbability)
    (hs1 : successProbability ≤ 1) :
    fixedPointRealizedComplexFailureAmplitude successProbability
        (canonicalRoleWord035 input) =
      Polynomial.eval (fixedPointSourceAmplitude successProbability : ℂ)
        (completionStandardState033 input).sourceFactor := by
  have hword := standardSourceWord035_spec input
  have hstate :
      standardPolynomialSourceOrder032
          (canonicalRoleWord035 input) standardQ0State032 =
        completionStandardState033 input := by
    calc
      standardPolynomialSourceOrder032
          (canonicalRoleWord035 input) standardQ0State032 =
          standardWordEval034 (standardSourceWord035 input)
            standardQ0State032 :=
        roleWordEval035 (standardSourceWord035 input) standardQ0State032
      _ = completionStandardState033 input := hword.1
  have hphysical := standardPolynomialSourceOrder032_eval_matrix
    successProbability hs0 hs1 (canonicalRoleWord035 input)
      standardQ0State032
  rw [hstate, standardPhysicalQ0_eq_basis035 successProbability] at hphysical
  have hcoord := congrArg
    (fun state : FixedPointTransferState => state fixedPointSourceIndex)
    hphysical
  simpa [fixedPointRealizedComplexFailureAmplitude, fixedPointEvaluatedState,
    standardPhysicalState032, fixedPointPairState,
    fixedPointSourceIndex, fixedPointTargetIndex] using hcoord.symm

theorem canonicalPlan035_response_matches
    (input : GeneralRealQSPPolynomial127) :
    ∀ successProbability,
      (nativeQSPTarget024 input).parameterDomain successProbability →
        (canonicalPlan035 input).realizedScalarResponse successProbability =
          (nativeQSPTarget024 input).response successProbability := by
  intro successProbability hdomain
  have hs0 : 0 ≤ successProbability := hdomain.1
  have hs1 : successProbability ≤ 1 := hdomain.2
  have hsource := canonicalRoleWord035_source_eval input
    successProbability hs0 hs1
  change phaseCorrectedRealFailureAmplitude (1 : ℂ)
      (fixedPointRealizedComplexFailureAmplitude successProbability
        (canonicalRoleWord035 input)) =
    Polynomial.eval (fixedPointSourceAmplitude successProbability)
      input.polynomial
  rw [hsource]
  simp [phaseCorrectedRealFailureAmplitude]
  simpa [completionStandardState033, completionPair024] using
    completionStandardState033_real_readout input
      (fixedPointSourceAmplitude successProbability)

theorem canonicalCertificate035
    (input : GeneralRealQSPPolynomial127) :
    TwoProjectorQSPRealizationCertificate
      (nativeQSPTarget024 input) (canonicalPlan035 input) where
  response_matches := canonicalPlan035_response_matches input
  parity_matches := nativeQSPTarget024_parityLaw input

/-! ## Fully-applied source-order sanity positives and typed negatives -/

/-! Fully-applied admissible polynomial sanity inputs.  These are only
examples of the generic theorem; they do not replace its quantified input. -/

end
end SpectralSamplingProof.Analytic
