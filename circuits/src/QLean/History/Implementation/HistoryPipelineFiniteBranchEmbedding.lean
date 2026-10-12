import QLean.Circuits.Foundation.ComputableWireEmbedding
import QLean.History.Implementation.HistoryPipelineSumComposition

/-!
Finite realization of the physical branch embedding used by the H-history
composition.  Branch and logical-index meanings are unchanged; the only
replacement is finite inversion of the wire placement.
-/

set_option autoImplicit false
set_option warningAsError true

namespace ExecutableHistoryImplementationRole

open VerifiedCircuitCore
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryCore
open ExecutableHistoryQbPlusCleanBlock

/-- The control bit is the only nonzero outside bit of a branch. -/
def finiteBranchOutside119 {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (controlValue : Bool) : QubitBasis targetQubits :=
  fun wire => if wire = layout.control then controlValue else false

/-- A branch basis embedding using only finite placement lookup. -/
def finiteBranchBasisEmbedding119 {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (controlValue : Bool) :
    QubitBasis sourceQubits ↪ QubitBasis targetQubits :=
  finiteFixedOutsideBasisEmbedding layout.placement
    (finiteBranchOutside119 layout controlValue)

theorem finiteBranchBasisEmbedding119_eq
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (controlValue : Bool) :
    finiteBranchBasisEmbedding119 layout controlValue =
      fixedOutsideBasisEmbedding (externalLayout119 layout).placement
        (branchOutside119 layout controlValue) := by
  rw [finiteBranchBasisEmbedding119, finiteFixedOutsideBasisEmbedding_eq]
  rfl

/-- Exactly the finite data needed to encode an H-history branch basis. -/
structure FiniteHistoryBasisPlan119
    (d c R sourceQubits targetQubits : Nat) where
  layout : ControlLayout sourceQubits targetQubits
  historyBasis : JenningsHistory.HistoryIndex d c R → QubitBasis sourceQubits
  inrBasis : QubitBasis sourceQubits

/-- The source-to-physical-basis map does not require a circuit proof. -/
def finiteExtendedIndexBasisOfPlan119
    {d c R sourceQubits targetQubits : Nat}
    (plan : FiniteHistoryBasisPlan119 d c R sourceQubits targetQubits)
    (index : GramOperator.ExtendedIndex d c R) :
    QubitBasis targetQubits :=
  match index with
  | Sum.inl row =>
      finiteBranchBasisEmbedding119 plan.layout true (plan.historyBasis row)
  | Sum.inr _ =>
      finiteBranchBasisEmbedding119 plan.layout false plan.inrBasis

end ExecutableHistoryImplementationRole
