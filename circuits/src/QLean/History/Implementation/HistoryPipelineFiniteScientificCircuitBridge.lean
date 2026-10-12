import QLean.History.Implementation.HistoryPipelineFiniteScientificComparatorBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option warningAsError true

/-!
# Finite scientific repaired-H3 circuit bridge

The H3 compiler reads physical wires, two comparison records and explicit
angle arguments. Its proof-evidence record also contains historical angle
metadata, but those fields are not read by this compiler. The theorem below
compares the emitted circuits, not the unused metadata records.
-/

namespace ExecutableHistoryFiniteScientificCircuitBridge

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
open ExecutableHistoryFiniteCorrectedP05

private theorem h3CastCongr
    {q₁ q₂ d₁ d₂ s₁ s₂ w₁ w₂ : Nat}
    {parameters : HistoryBlockParameters}
    (hq : q₁ = q₂) (hd : d₁ = d₂) (hs : s₁ = s₂) (hw : w₁ = w₂)
    (layout₁ : HistoryBlockLayout q₁ d₁ s₁
      (historyClockWorkspaceWidth parameters w₁) parameters)
    (layout₂ : HistoryBlockLayout q₂ d₂ s₂
      (historyClockWorkspaceWidth parameters w₂) parameters)
    (clock₁ : HistoryClockConcreteSourceOrderEvidence layout₁)
    (clock₂ : HistoryClockConcreteSourceOrderEvidence layout₂)
    (layoutEq : castHistoryLayout hq hd hs hw layout₁ = layout₂)
    (time₁ idle₁ : UnsignedLessThanXorSpec q₁
      (historyClockWidth parameters.timeSteps parameters.taylorOrder
        parameters.idlingSteps))
    (time₂ idle₂ : UnsignedLessThanXorSpec q₂
      (historyClockWidth parameters.timeSteps parameters.taylorOrder
        parameters.idlingSteps))
    (timeEq : hq ▸ time₁ = time₂) (idleEq : hq ▸ idle₁ = idle₂)
    (physicalClocks idleClockEnd binaryLabels : Nat)
    (idleAngle coefficientAngle : AngleExpr) :
    hq ▸ finiteRepairedH3Circuit119 layout₁ clock₁ time₁ idle₁
      physicalClocks idleClockEnd binaryLabels idleAngle coefficientAngle =
    finiteRepairedH3Circuit119 layout₂ clock₂ time₂ idle₂
      physicalClocks idleClockEnd binaryLabels idleAngle coefficientAngle := by
  cases hq
  cases hd
  cases hs
  cases hw
  cases layoutEq
  cases timeEq
  cases idleEq
  rfl

/-- The finite repaired-H3 primitive word is the certified word for the
same source after transporting only its carrier-width index. -/
theorem finiteScientificH3_eq_certified
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (finiteScientificHistoryQubits119_eq source) ▸
      finiteScientificRepairedH3Circuit119 source =
    finiteRepairedH3Circuit119
      (ExecutableLayout119 source domain)
      (ExecutableClockEvidence119 source domain)
      (ExecutableHistoryFiniteCorrectedP05.certifiedPlan source domain).timeComparison
      (ExecutableHistoryFiniteCorrectedP05.certifiedPlan source domain).idleEndComparison
      source.historyParameters.physicalClocks
      (historyIdleClockEnd source.historyParameters.physicalClocks
        source.historyParameters.taylorOrder
        (finiteScientificHistoryIdleSteps119 source))
      source.historyParameters.binaryLabels
      (repairedIdle source) idleCoefficient := by
  rw [finiteScientificH3_retyped source domain]
  exact h3CastCongr
    (finiteScientificHistoryQubits119_eq source)
    (executableHistory_dataWidth119 source).symm
    (executableHistory_signalWidth119 source).symm
    (executableHistory_workWidth119 source).symm
    (retypedFiniteLayout source domain)
    (ExecutableLayout119 source domain)
    (retypedClockEvidence source domain)
    (ExecutableClockEvidence119 source domain)
    (retypedFiniteLayout_eq_certified source domain)
    (finiteClockTimeComparison119 source)
    (finiteClockIdleEndComparison119 source)
    (ExecutableHistoryFiniteCorrectedP05.certifiedPlan source domain).timeComparison
    (ExecutableHistoryFiniteCorrectedP05.certifiedPlan source domain).idleEndComparison
    (finiteClockTimeComparison_eq_certified source domain)
    (finiteClockIdleEndComparison_eq_certified source domain)
    source.historyParameters.physicalClocks
    (historyIdleClockEnd source.historyParameters.physicalClocks
      source.historyParameters.taylorOrder
      (finiteScientificHistoryIdleSteps119 source))
    source.historyParameters.binaryLabels
    (repairedIdle source) idleCoefficient

end ExecutableHistoryFiniteScientificCircuitBridge
