import QLean.History.Implementation.HistoryPipelineFiniteScientificCircuitBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option warningAsError true

/-!
# Finite scientific corrected-P05 circuit bridge

The finite scientific P15/H3 word and the proof-only certified corrected-P05
plan use one circuit compiler. We compare the emitted primitive words through
their actual layout, Q placement and children, without identifying the
independent analytic parameter records.
-/

namespace ExecutableHistoryFiniteScientificP05Bridge

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open ExecutableHistoryFiniteScientificLayout
open ExecutableHistoryFiniteScientificH3
open ExecutableHistoryFiniteScientificAngles
open ExecutableHistoryFiniteScientificBridge
open ExecutableHistoryFiniteScientificComparatorBridge
open ExecutableHistoryFiniteScientificCircuitBridge
open ExecutableHistoryFiniteCorrectedP05

private def castQ10Control
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {p : ProbabilityGeneratorQProof.QParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂) (hw : w₁ = w₂)
    (control : HistoryTaylorQ10ControlEvidence
      (qubits := q₁) (generatorSignalWidth := s₁)
      (generatorWorkWidth := w₁) (dataWidth := d₁) p) :
    HistoryTaylorQ10ControlEvidence
      (qubits := q₂) (generatorSignalWidth := s₂)
      (generatorWorkWidth := w₂) (dataWidth := d₂) p := by
  cases hq
  cases hd
  cases hs
  cases hw
  exact control

private theorem frozenControlCast
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂) (hw : w₁ = w₂)
    (layout₁ : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters)
    (layout₂ : HistoryBlockLayout q₂ d₂ s₂
      (historyClockWorkspaceWidth parameters w₂) parameters)
    (widths₁ : ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
      p s₁ w₁ d₁)
    (widths₂ : ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
      p s₂ w₂ d₂)
    (layoutEq : castHistoryLayout hq hd hs hw layout₁ = layout₂) :
    castQ10Control hq hd hs hw
      (historyP15Q10ControlEvidence_ofFrozenLayout (layout := layout₁) widths₁) =
    historyP15Q10ControlEvidence_ofFrozenLayout (layout := layout₂) widths₂ := by
  cases hq
  cases hd
  cases hs
  cases hw
  cases layoutEq
  simp only [castQ10Control, castHistoryLayout]

private theorem finiteControl_eq_retyped
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    finiteHistoryQ10ControlEvidence119 source =
      historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := retypedFiniteLayout source domain)
        (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
          source.qParameters) := by
  rfl

private theorem finiteControl_eq_certified
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    castQ10Control
      (finiteScientificHistoryQubits119_eq source)
      (executableHistory_dataWidth119 source).symm
      (executableHistory_signalWidth119 source).symm
      (executableHistory_workWidth119 source).symm
      (finiteHistoryQ10ControlEvidence119 source) =
        (certifiedPlan source domain).p15Control := by
  rw [finiteControl_eq_retyped source domain]
  exact frozenControlCast
    (finiteScientificHistoryQubits119_eq source)
    (executableHistory_dataWidth119 source).symm
    (executableHistory_signalWidth119 source).symm
    (executableHistory_workWidth119 source).symm
    (retypedFiniteLayout source domain)
    (ExecutableLayout119 source domain)
    (ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths.canonical
      source.qParameters)
    (ExecutableAdmissible119 source domain).placementWidths
    (retypedFiniteLayout_eq_certified source domain)

private theorem p15CastCongr
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂) (hw : w₁ = w₂)
    (p : ProbabilityGeneratorQProof.QParameters)
    (layout₁ : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters)
    (layout₂ : HistoryBlockLayout q₂ d₂ s₂
      (historyClockWorkspaceWidth parameters w₂) parameters)
    (evidence₁ : HistoryTaylorL2Evidence layout₁)
    (evidence₂ : HistoryTaylorL2Evidence layout₂)
    (control₁ : HistoryTaylorQ10ControlEvidence
      (qubits := q₁) (generatorSignalWidth := s₁)
      (generatorWorkWidth := w₁) (dataWidth := d₁) p)
    (control₂ : HistoryTaylorQ10ControlEvidence
      (qubits := q₂) (generatorSignalWidth := s₂)
      (generatorWorkWidth := w₂) (dataWidth := d₂) p)
    (controlLayoutEq :
      (castQ10Control hq hd hs hw control₁).placement.externalLayout =
        control₂.placement.externalLayout)
    (layoutEq : castHistoryLayout hq hd hs hw layout₁ = layout₂)
    (angles : Fin parameters.taylorOrder → AngleExpr)
    (idleAngle : AngleExpr) :
    hq ▸ finiteHistoryTaylorPaddedCircuit119 p layout₁ evidence₁
      control₁ angles idleAngle =
    finiteHistoryTaylorPaddedCircuit119 p layout₂ evidence₂
      control₂ angles idleAngle := by
  cases hq
  cases hd
  cases hs
  cases hw
  cases layoutEq
  simp only [castHistoryLayout]
  simp only [castQ10Control] at controlLayoutEq
  unfold finiteHistoryTaylorPaddedCircuit119
  simp only [finiteHistoryTaylorControlledGenerator119]
  rw [controlLayoutEq]
  rfl

/-- The complete finite P15 primitive word agrees with the scientific
certified P15 word after the carrier-width equality. -/
theorem finiteScientificP15_eq_certified
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (finiteScientificHistoryQubits119_eq source) ▸
      finiteScientificTaylorCircuit119 source =
    finiteHistoryTaylorPaddedCircuit119
      (ScientificWidthGenericContract.correctedGeneratorParameters259
        (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
      (certifiedPlan source domain).layout
      (certifiedPlan source domain).p15Evidence
      (certifiedPlan source domain).p15Control
      (certifiedPlan source domain).coefficientAngles
      (certifiedPlan source domain).idleCoefficientAngle := by
  rw [finiteScientificP15_retyped source domain]
  exact p15CastCongr
    (finiteScientificHistoryQubits119_eq source)
    (executableHistory_dataWidth119 source).symm
    (executableHistory_signalWidth119 source).symm
    (executableHistory_workWidth119 source).symm
    source.qParameters
    (retypedFiniteLayout source domain)
    (ExecutableLayout119 source domain)
    (retypedL2Evidence source domain)
    (certifiedPlan source domain).p15Evidence
    (finiteHistoryQ10ControlEvidence119 source)
    (certifiedPlan source domain).p15Control
    (congrArg
      (fun control => control.placement.externalLayout)
      (finiteControl_eq_certified source domain))
    (retypedFiniteLayout_eq_certified source domain)
    (fun index => correctedCoefficient source index.val)
    idleCoefficient

private theorem correctedP05CastCongr
    {q₁ q₂ : Nat} (hq : q₁ = q₂)
    (selector₁ : HistorySelectorPreparationParameters q₁)
    (selector₂ : HistorySelectorPreparationParameters q₂)
    (p15₁ h3₁ : Circuit (PrimitiveGate q₁))
    (p15₂ h3₂ : Circuit (PrimitiveGate q₂))
    (selectorEq : hq ▸ selector₁ = selector₂)
    (p15Eq : hq ▸ p15₁ = p15₂)
    (h3Eq : hq ▸ h3₁ = h3₂) :
    hq ▸ finiteCorrectedP05Circuit119 selector₁ p15₁ h3₁ =
      finiteCorrectedP05Circuit119 selector₂ p15₂ h3₂ := by
  cases hq
  cases selectorEq
  cases p15Eq
  cases h3Eq
  rfl

/-- The same finite `Plan.compile` circuit is used by the numerical plan and
by the scientific certified plan. No equality of independent analytic
parameter records is assumed. -/
theorem finiteScientificCorrectedP05_eq_certified
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (finiteScientificHistoryQubits119_eq source) ▸
      finiteScientificCorrectedP05Circuit119 source =
        (certifiedPlan source domain).compile := by
  rw [finiteScientificCorrectedP05Circuit119_eq_parts]
  change (finiteScientificHistoryQubits119_eq source) ▸
      finiteCorrectedP05Circuit119
        (finiteScientificCorrectedP05Plan119 source).selector
        (finiteScientificTaylorCircuit119 source)
        (finiteScientificRepairedH3Circuit119 source) =
    finiteCorrectedP05Circuit119
      (certifiedPlan source domain).selector
      (finiteHistoryTaylorPaddedCircuit119
        (ScientificWidthGenericContract.correctedGeneratorParameters259
          (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
        (certifiedPlan source domain).layout
        (certifiedPlan source domain).p15Evidence
        (certifiedPlan source domain).p15Control
        (certifiedPlan source domain).coefficientAngles
        (certifiedPlan source domain).idleCoefficientAngle)
      (finiteRepairedH3Circuit119
        (certifiedPlan source domain).layout
        (certifiedPlan source domain).clockEvidence
        (certifiedPlan source domain).timeComparison
        (certifiedPlan source domain).idleEndComparison
        (certifiedPlan source domain).physicalClocks
        (certifiedPlan source domain).idleClockEnd
        (certifiedPlan source domain).binaryLabels
        (certifiedPlan source domain).repairedIdleAngle
        (certifiedPlan source domain).repairedCoefficientAngle)
  exact correctedP05CastCongr
    (finiteScientificHistoryQubits119_eq source)
    (finiteScientificCorrectedP05Plan119 source).selector
    (certifiedPlan source domain).selector
    (finiteScientificTaylorCircuit119 source)
    (finiteScientificRepairedH3Circuit119 source)
    (finiteHistoryTaylorPaddedCircuit119
      (ScientificWidthGenericContract.correctedGeneratorParameters259
        (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
      (certifiedPlan source domain).layout
      (certifiedPlan source domain).p15Evidence
      (certifiedPlan source domain).p15Control
      (certifiedPlan source domain).coefficientAngles
      (certifiedPlan source domain).idleCoefficientAngle)
    (finiteRepairedH3Circuit119
      (certifiedPlan source domain).layout
      (certifiedPlan source domain).clockEvidence
      (certifiedPlan source domain).timeComparison
      (certifiedPlan source domain).idleEndComparison
      (certifiedPlan source domain).physicalClocks
      (certifiedPlan source domain).idleClockEnd
      (certifiedPlan source domain).binaryLabels
      (certifiedPlan source domain).repairedIdleAngle
      (certifiedPlan source domain).repairedCoefficientAngle)
    (finiteScientificSelector_eq_certified source domain)
    (finiteScientificP15_eq_certified source domain)
    (finiteScientificH3_eq_certified source domain)

end ExecutableHistoryFiniteScientificP05Bridge
