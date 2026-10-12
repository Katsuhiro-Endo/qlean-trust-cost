import QLean.SignalProcessing.QSPExistenceAlternatingScheduleNormalization

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## Shape carried by the standard one-query recursion

The accepted degree recursion appends one signal and one source phase.  The
definition below records that syntax in the angle list itself; counts are
proved from this shape rather than used to reconstruct it.
-/

def shapedStandardWord040 : List ℝ → List StandardWordStep034
  | [] => []
  | [angle] => [.sourcePhase angle]
  | angle :: rest =>
      [.sourcePhase angle, .signal] ++ shapedStandardWord040 rest

theorem shapedStandardWord040_append_single
    (angles : List ℝ) (hangles : angles ≠ []) (angle : ℝ) :
    shapedStandardWord040 (angles ++ [angle]) =
      shapedStandardWord040 angles ++
        [.signal, .sourcePhase angle] := by
  induction angles with
  | nil => simp_all
  | cons head tail ih =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [shapedStandardWord040, List.cons_append,
            List.nil_append]
          exact congrArg (fun tail =>
            [StandardWordStep034.sourcePhase head,
              StandardWordStep034.signal] ++ tail) (ih (by simp))

theorem shapedStandardWord040_signal_count
    (angles : List ℝ) :
    standardSignalCount035 (shapedStandardWord040 angles) =
      angles.length - 1 := by
  induction angles with
  | nil => rfl
  | cons head tail ih =>
      cases tail with
      | nil => simp [shapedStandardWord040, standardSignalCount035]
      | cons next rest =>
          rw [show shapedStandardWord040 (head :: next :: rest) =
            [.sourcePhase head, .signal] ++
              shapedStandardWord040 (next :: rest) by rfl]
          rw [standardSignalCount035_append]
          simp [standardSignalCount035, ih]
          omega

theorem shapedStandardWord040_phase_count
    (angles : List ℝ) :
    standardProjectorPhaseCount035 (shapedStandardWord040 angles) =
      angles.length := by
  induction angles with
  | nil => rfl
  | cons head tail ih =>
      cases tail with
      | nil => simp [shapedStandardWord040, standardProjectorPhaseCount035]
      | cons next rest =>
          rw [show shapedStandardWord040 (head :: next :: rest) =
            [.sourcePhase head, .signal] ++
              shapedStandardWord040 (next :: rest) by rfl]
          rw [standardProjectorPhaseCount035_append]
          simp [standardProjectorPhaseCount035, ih]
          omega

theorem roleWordOfStandard035_shaped
    (angles : List ℝ) :
    roleWordOfStandard035 (shapedStandardWord040 angles) =
      canonicalSourceWord037 angles := by
  induction angles with
  | nil => rfl
  | cons head tail ih =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [shapedStandardWord040, roleWordOfStandard035,
            List.map_cons,
            roleStepOfStandard035, canonicalSourceWord037,
            List.cons_append, List.nil_append]
          exact congrArg (fun tail =>
            [FixedPointRoleAwarePhaseStep.projectorPhase
                FixedPointProjectorRole.source head,
              FixedPointRoleAwarePhaseStep.signal
                VerifiedCircuitCore.SignalDirection.forward] ++ tail) ih

/-! Fully-applied symbolic shape positives.  The angles are variables; these
    are not finite fixtures and the equalities expose the syntax carried by
    the recursive witness. -/

/-! CHAT-039's count-only counterexample remains a negative: equal counts do
    not imply the canonical source order. -/

/-! The angle recursion carries both evaluation and exact syntax. -/

theorem exists_shaped_standardWord040 :
    ∀ d : ℕ, ∀ c : StandardAdmissibility034, c.degree = d →
      ∃ angles : List ℝ,
        angles.length = d + 1 ∧
          standardWordEval034 (shapedStandardWord040 angles)
            standardQ0State032 = c.state := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro c hcd
      by_cases hd0 : d = 0
      · have hc0 : c.degree = 0 := by omega
        obtain ⟨angle, hangle⟩ := standardBaseState034_phase_exists c hc0
        refine ⟨[angle], ?_, ?_⟩
        · simp [hd0]
        · simpa [shapedStandardWord040, standardWordEval034,
            standardApplyWordStep034] using hangle
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        have hcpos : 0 < c.degree := by omega
        let e : StandardAdmissibility034 :=
          standardExtractedAdmissible034 c hcpos
        have hedeg : e.degree = d - 1 := by
          change c.degree - 1 = d - 1
          omega
        obtain ⟨angles, hlen, hword⟩ :=
          ih (d - 1) (by omega) e hedeg
        have hne : angles ≠ [] := by
          intro hnil
          subst hnil
          simp at hlen
        let nextAngle : ℝ := -(standardTopAngle034 c hcpos)
        refine ⟨angles ++ [nextAngle], ?_, ?_⟩
        · simp [hlen]
          omega
        · rw [shapedStandardWord040_append_single angles hne nextAngle]
          rw [standardWordEval034_append, hword]
          change standardSourcePhase032
              (standardPhase032 (-(standardTopAngle034 c hcpos)))
              (standardSignalForward032
                (standardExtractedState034 c hcpos)) = c.state
          rw [standardExtractedState034_forward_establishedBridge c hcpos]
          exact standardSourcePhase032_inverse_angle034
            (standardTopAngle034 c hcpos) c.state

/-! ## Inverting the accepted gauge syntax

The inverse is purely syntactic.  It is not a second evaluator and introduces
no phase values: it merely undoes the plus/minus pi branch used by CHAT-038.
-/

def ungaugeCanonicalAngle040 (n j : Nat) (angle : ℝ) : ℝ :=
  if j = 0 then angle else
    if j + 1 < n then
      if j % 2 = 0 then angle - Real.pi else -angle + Real.pi
    else if j % 2 = 0 then angle - Real.pi else -angle

def ungaugeCanonicalAnglesAux040 : Nat → Nat → List ℝ → List ℝ
  | _, _, [] => []
  | n, j, angle :: rest =>
      ungaugeCanonicalAngle040 n j angle ::
        ungaugeCanonicalAnglesAux040 n (j + 1) rest

def ungaugeCanonicalAngles040 (angles : List ℝ) : List ℝ :=
  ungaugeCanonicalAnglesAux040 angles.length 0 angles

theorem ungaugeCanonicalAnglesAux040_length
    (n j : Nat) (angles : List ℝ) :
    (ungaugeCanonicalAnglesAux040 n j angles).length = angles.length := by
  induction angles generalizing j with
  | nil => rfl
  | cons head tail ih =>
      simp only [ungaugeCanonicalAnglesAux040, List.length_cons]
      rw [ih (j + 1)]

theorem gaugeCanonicalAngle037_ungaugeCanonicalAngle040
    (n j : Nat) (angle : ℝ) :
    gaugeCanonicalAngle037 n j
        (ungaugeCanonicalAngle040 n j angle) = angle := by
  by_cases hj : j = 0
  · simp [gaugeCanonicalAngle037, ungaugeCanonicalAngle040, hj]
  · by_cases hmid : j + 1 < n
    · by_cases heven : j % 2 = 0
      · simp [gaugeCanonicalAngle037, ungaugeCanonicalAngle040,
          hj, hmid, heven]
      · simp [gaugeCanonicalAngle037, ungaugeCanonicalAngle040,
          hj, hmid, heven]
    · by_cases heven : j % 2 = 0
      · simp [gaugeCanonicalAngle037, ungaugeCanonicalAngle040,
          hj, hmid, heven]
      · simp [gaugeCanonicalAngle037, ungaugeCanonicalAngle040,
          hj, hmid, heven]

theorem gaugeCanonicalAnglesAux037_ungaugeCanonicalAnglesAux040
    (n j : Nat) (angles : List ℝ) :
    gaugeCanonicalAnglesAux037 n j
        (ungaugeCanonicalAnglesAux040 n j angles) = angles := by
  induction angles generalizing j with
  | nil => rfl
  | cons head tail ih =>
      change gaugeCanonicalAngle037 n j
          (ungaugeCanonicalAngle040 n j head) ::
          gaugeCanonicalAnglesAux037 n (j + 1)
            (ungaugeCanonicalAnglesAux040 n (j + 1) tail) =
        head :: tail
      rw [gaugeCanonicalAngle037_ungaugeCanonicalAngle040]
      exact congrArg (List.cons head) (ih (j + 1))

theorem gaugeCanonicalAngles037_ungaugeCanonicalAngles040
    (angles : List ℝ) :
    gaugeCanonicalAngles037 (ungaugeCanonicalAngles040 angles) = angles := by
  unfold gaugeCanonicalAngles037 ungaugeCanonicalAngles040
  rw [ungaugeCanonicalAnglesAux040_length]
  exact gaugeCanonicalAnglesAux037_ungaugeCanonicalAnglesAux040
    angles.length 0 angles

theorem ungaugeCanonicalAngles040_length
    (angles : List ℝ) :
    (ungaugeCanonicalAngles040 angles).length = angles.length := by
  unfold ungaugeCanonicalAngles040
  exact ungaugeCanonicalAnglesAux040_length angles.length 0 angles

/-! ## Actual evaluator bridge for an explicitly shaped word -/

def planOfStandardWord040
    (word : List StandardWordStep034) : TwoProjectorQSPPhasePlan where
  steps := roleWordOfStandard035 word
  globalPhase := 1
  globalPhase_unitNormSq := by norm_num

theorem shapedWord040_source_eval
    (input : GeneralRealQSPPolynomial127)
    (word : List StandardWordStep034)
    (hstate : standardWordEval034 word standardQ0State032 =
      completionStandardState033 input)
    (successProbability : ℝ)
    (hs0 : 0 ≤ successProbability) (hs1 : successProbability ≤ 1) :
    fixedPointRealizedComplexFailureAmplitude successProbability
        (roleWordOfStandard035 word) =
      Polynomial.eval (fixedPointSourceAmplitude successProbability : ℂ)
        (completionStandardState033 input).sourceFactor := by
  have hphysical := standardPolynomialSourceOrder032_eval_matrix
    successProbability hs0 hs1 (roleWordOfStandard035 word)
      standardQ0State032
  rw [roleWordEval035 word standardQ0State032, hstate,
    standardPhysicalQ0_eq_basis035 successProbability] at hphysical
  have hcoord := congrArg
    (fun state : FixedPointTransferState => state fixedPointSourceIndex)
    hphysical
  simpa [fixedPointRealizedComplexFailureAmplitude, fixedPointEvaluatedState,
    standardPhysicalState032, fixedPointPairState,
    fixedPointSourceIndex, fixedPointTargetIndex] using hcoord.symm

theorem planOfStandardWord040_response_matches
    (input : GeneralRealQSPPolynomial127)
    (word : List StandardWordStep034)
    (hstate : standardWordEval034 word standardQ0State032 =
      completionStandardState033 input) :
    ∀ successProbability,
      (nativeQSPTarget024 input).parameterDomain successProbability →
        (planOfStandardWord040 word).realizedScalarResponse
            successProbability =
          (nativeQSPTarget024 input).response successProbability := by
  intro successProbability hdomain
  have hs0 : 0 ≤ successProbability := hdomain.1
  have hs1 : successProbability ≤ 1 := hdomain.2
  have hsource := shapedWord040_source_eval input word hstate
    successProbability hs0 hs1
  change phaseCorrectedRealFailureAmplitude (1 : ℂ)
      (fixedPointRealizedComplexFailureAmplitude successProbability
        (roleWordOfStandard035 word)) =
    Polynomial.eval (fixedPointSourceAmplitude successProbability)
      input.polynomial
  rw [hsource]
  simp [phaseCorrectedRealFailureAmplitude]
  simpa [completionStandardState033, completionPair024] using
    completionStandardState033_real_readout input
      (fixedPointSourceAmplitude successProbability)

theorem planOfStandardWord040_certificate
    (input : GeneralRealQSPPolynomial127)
    (word : List StandardWordStep034)
    (hstate : standardWordEval034 word standardQ0State032 =
      completionStandardState033 input) :
    TwoProjectorQSPRealizationCertificate
      (nativeQSPTarget024 input) (planOfStandardWord040 word) where
  response_matches := planOfStandardWord040_response_matches input word hstate
  parity_matches := nativeQSPTarget024_parityLaw input

/-! ## The shaped positive-degree witness -/

structure ShapedQSPWordSynthesis040
    (input : GeneralRealQSPPolynomial127) where
  angles : List ℝ
  angles_ge_two : 2 ≤ angles.length
  standardWord : List StandardWordStep034
  standardWord_shape :
    roleWordOfStandard035 standardWord =
      canonicalSourceWord037 (gaugeCanonicalAngles037 angles)
  state_match :
    standardWordEval034 standardWord standardQ0State032 =
      completionStandardState033 input
  signal_count : signalCount127 (roleWordOfStandard035 standardWord) =
    input.degree
  projector_phase_count :
    projectorPhaseCount127 (roleWordOfStandard035 standardWord) =
      input.degree + 1
  plan : TwoProjectorQSPPhasePlan
  plan_steps : plan.steps = roleWordOfStandard035 standardWord
  certificate :
    TwoProjectorQSPRealizationCertificate
      (nativeQSPTarget024 input) plan

theorem exists_shapedQSPWordSynthesis040
    (input : GeneralRealQSPPolynomial127) (hd : 0 < input.degree) :
    Nonempty (ShapedQSPWordSynthesis040 input) := by
  let c : StandardAdmissibility034 := completionAdmissible034 input
  obtain ⟨canonicalAngles, hlen, hstate⟩ :=
    exists_shaped_standardWord040 input.degree c rfl
  let angles : List ℝ := ungaugeCanonicalAngles040 canonicalAngles
  let word : List StandardWordStep034 :=
    shapedStandardWord040 canonicalAngles
  let plan : TwoProjectorQSPPhasePlan := planOfStandardWord040 word
  have hanglelen : angles.length = input.degree + 1 := by
    dsimp [angles]
    rw [ungaugeCanonicalAngles040_length, hlen]
  have hge : 2 ≤ angles.length := by
    rw [hanglelen]
    omega
  have hgauge : gaugeCanonicalAngles037 angles = canonicalAngles := by
    dsimp [angles]
    exact gaugeCanonicalAngles037_ungaugeCanonicalAngles040 canonicalAngles
  have hshape :
      roleWordOfStandard035 word =
        canonicalSourceWord037 (gaugeCanonicalAngles037 angles) := by
    dsimp [word]
    rw [hgauge]
    exact roleWordOfStandard035_shaped canonicalAngles
  have hsignal :
      signalCount127 (roleWordOfStandard035 word) = input.degree := by
    dsimp [word]
    rw [roleWordSignalCount035, shapedStandardWord040_signal_count,
      hlen]
    omega
  have hphase :
      projectorPhaseCount127 (roleWordOfStandard035 word) =
        input.degree + 1 := by
    dsimp [word]
    rw [roleWordProjectorPhaseCount035,
      shapedStandardWord040_phase_count, hlen]
  have hcert := planOfStandardWord040_certificate input word (by
    simpa [word, c, completionAdmissible034] using hstate)
  exact ⟨{
    angles := angles
    angles_ge_two := hge
    standardWord := word
    standardWord_shape := hshape
    state_match := by
      simpa [word, c, completionAdmissible034] using hstate
    signal_count := hsignal
    projector_phase_count := hphase
    plan := plan
    plan_steps := by rfl
    certificate := by
      exact hcert
  }⟩

end
end SpectralSamplingProof.Analytic
