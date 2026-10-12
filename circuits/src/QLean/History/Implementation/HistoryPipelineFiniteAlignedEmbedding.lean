import QLean.History.Implementation.HistoryPipelineFiniteBranchEmbedding
import QLean.History.Implementation.HistoryPipelineAlignedPhysicalP18

/-! Finite realization of the H-history data-preparation embedding. -/

set_option autoImplicit false
set_option warningAsError true

namespace ExecutableHistoryAlignedPhysicalP18

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open ExecutableHistoryCore
open ExecutableHistoryQbPlusCleanBlock
open ExecutableHistoryImplementationRole

/-- Finite clean-block basis placement, with the old block meaning. -/
def finiteBlockBasis119 {n : Nat} (input : QubitBasis n) :
    QubitBasis (blockQubits119 n) :=
  finiteFixedOutsideBasisEmbedding (dataPlacement119 n) (fun _ => false) input

theorem finiteBlockBasis119_eq {n : Nat} (input : QubitBasis n) :
    finiteBlockBasis119 input = blockBasis119 input := by
  rw [finiteBlockBasis119, finiteFixedOutsideBasisEmbedding_eq]
  rfl

end ExecutableHistoryAlignedPhysicalP18
