import QLean.History.Implementation.HistoryPipelineH2PostLocality

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

theorem executableH2Q10_operator_local119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    OperatorPreservesOutside
      (Finset.univ.image
        (ExecutableH2Q10Specification119 source domain).layout.placement)
      (h2ControlledQ10CleanOperator
        (ExecutableH2Q10Specification119 source domain)) := by
  unfold h2ControlledQ10CleanOperator r12ControlledSubcircuitCleanOperator
  rw [ExternallyControlledPrimitivePlan.semanticPlanOperator_eq_controlledWireLift]
  exact externallyControlledWireLiftOperator_preservesOutsidePlacement _ _

theorem intermediate_unique_of_two_stage_locality119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (postSupport : Finset (Fin targetQubits))
    (post q10 : VerifiedCircuitCore.Operator (QubitBasis targetQubits))
    (postLocal : OperatorPreservesOutside postSupport post)
    (postDisjoint : ∀ wire, wire ∈ postSupport → ∀ source,
      wire ≠ placement source)
    (q10Local : OperatorPreservesOutside
      (Finset.univ.image placement) q10)
    (row input expected middle : QubitBasis targetQubits)
    (expectedOutside : restrictToOutsideWires placement expected =
      restrictToOutsideWires placement input)
    (postExpectedNonzero : post row expected ≠ 0)
    (postMiddleNonzero : post row middle ≠ 0)
    (q10MiddleNonzero : q10 middle input ≠ 0) :
    middle = expected := by
  apply (fullBasis_eq_iff_restrictions_eq placement _ _).2
  constructor
  · funext source
    have middleBit := postLocal row middle postMiddleNonzero
      (placement source) (by
        intro member
        exact (postDisjoint _ member source) rfl)
    have expectedBit := postLocal row expected postExpectedNonzero
      (placement source) (by
        intro member
        exact (postDisjoint _ member source) rfl)
    exact middleBit.symm.trans expectedBit
  · funext outside
    have middleBit := q10Local middle input q10MiddleNonzero outside.1 (by
      intro member
      rcases Finset.mem_image.mp member with ⟨placed, _, equal⟩
      exact outside.2 placed equal)
    exact middleBit.trans (congrFun expectedOutside outside).symm

end
end ExecutableHistoryExecutableHistory
