import QLean.History.Implementation.HistoryPipelineQPlacedEntry

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryCleanInput

noncomputable section

abbrev ExecutableH2Q10Specification119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  historyP15ControlledQ10UnderstandingSpecification
    (ExecutableQParameters119 source domain)
    (ExecutableLayout119 source domain)
    (ExecutableAdmissible119 source domain).placementWidths

theorem executableH2Q10_clean_success_entry119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (output input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (outputConfiguration inputConfiguration :
      QConfiguration (ExecutableH2Q10Specification119 source domain).p)
    (controlTrue :
      input (ExecutableH2Q10Specification119 source domain).layout.control = true)
    (outsideEqual :
      restrictToOutsideWires
          (ExecutableH2Q10Specification119 source domain).layout.placement
          output =
        restrictToOutsideWires
          (ExecutableH2Q10Specification119 source domain).layout.placement
          input)
    (outputRestricted :
      restrictToPlacedWires
          (ExecutableH2Q10Specification119 source domain).layout.placement
          output =
        canonicalCoreSuccessBasis119
          (ExecutableH2Q10Specification119 source domain).p outputConfiguration)
    (inputRestricted :
      restrictToPlacedWires
          (ExecutableH2Q10Specification119 source domain).layout.placement
          input =
        canonicalCoreSuccessBasis119
          (ExecutableH2Q10Specification119 source domain).p inputConfiguration) :
    h2ControlledQ10CleanOperator
        (ExecutableH2Q10Specification119 source domain) output input =
      (HistoryBlockEncoding.QModel.configurationQMatrix
          outputConfiguration inputConfiguration : ℂ) /
        ((3 * (ExecutableH2Q10Specification119 source domain).p.K : Nat) : ℂ) := by
  unfold h2ControlledQ10CleanOperator r12ControlledSubcircuitCleanOperator
  rw [ExternallyControlledPrimitivePlan.semanticPlanOperator_eq_controlledWireLift]
  rw [externallyControlledWireLiftOperator_apply, if_pos controlTrue]
  rw [wireLiftOperator_apply, if_pos outsideEqual]
  simp only [mul_one]
  change r12ControlledSubcircuitSourceOperator
      (ExecutableH2Q10Specification119 source domain).symbolValue
      (ExecutableH2Q10Specification119 source domain).plan
      (restrictToPlacedWires
        (ExecutableH2Q10Specification119 source domain).layout.placement output)
      (restrictToPlacedWires
        (ExecutableH2Q10Specification119 source domain).layout.placement input) = _
  rw [(ExecutableH2Q10Specification119 source domain).sourcePlan_eq_q10]
  change reindexJointOperatorToCanonicalCore
      (q10ProbabilityGeneratorRecordedOperator
        (ExecutableH2Q10Specification119 source domain).p)
      (restrictToPlacedWires
        (ExecutableH2Q10Specification119 source domain).layout.placement output)
      (restrictToPlacedWires
        (ExecutableH2Q10Specification119 source domain).layout.placement input) = _
  rw [outputRestricted, inputRestricted]
  exact q10Recorded_core_success_entry119
    (ExecutableH2Q10Specification119 source domain).p
    outputConfiguration inputConfiguration

end

end ExecutableHistoryExecutableHistory
