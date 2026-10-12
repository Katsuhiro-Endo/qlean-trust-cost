import QLean.Circuits.FiniteSparsePreparationTransport
import QLean.Circuits.FiniteScientificPreparationBridge

/-! The finite sparse preparation is connected to the established P18
specification by its prepared zero-input state, never by equality of
preparation unitaries. All layout conditions are derived from the same input.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace QLean.Circuits.FiniteScientificSparsePreparationBridge

open VerifiedCircuitCore
open ExecutableHistoryExecutableHistory ExecutableHistoryExecutableP18
open ExecutableHistoryHistoryEmbedding ExecutableHistoryImplementationRole
open ExecutableHistoryCore
open QLean.Circuits.FiniteScientificCircuitSource
open QLean.Circuits.FiniteScientificPreparationBridge
open QLean.Circuits.FiniteSparsePreparationTransport

noncomputable section

theorem rhsPreparation_zeroKet_eq_canonical (input : FiniteScientificSource)
    (assumptions : ExecutableM13Assumptions119 input.layoutSource) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          input.rhsPreparation.circuit)
        (basisKet (fun _ => false : QubitBasis input.preparationQubits)) =
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (FiniteScientificSource.ofAlignedCommonSource
            input.layoutSource).rhsPreparation.circuit)
        (basisKet (fun _ => false)) := by
  have positive : 0 < input.initial.branchMass 0 0 := by
    have h := executable_sparse_root_pos input.layoutSource assumptions
    change 0 < (FiniteRationalConfigurationPreparation.SparseInitial.ofAmplitude
      input.initial.amplitude).branchMass 0 0 at h
    rw [branchMass_ofAmplitude_amplitude] at h
    exact h
  exact bPlusPreparation_zeroKet_eq_ofAmplitude input.initial input.rhsPlacement
    input.historyControlLayout.control (finite_rhs_sign_facts input) positive

/-- The physical zero column required by the generic aligned P18 theorem is
derived for the original sparse preparer, not only its dense adapter. -/
theorem rhsPreparation_aligned_zero_column (input : FiniteScientificSource)
    (domain : ExecutableHistoryDomain119 input.layoutSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (assumptions : ExecutableM13Assumptions119 input.layoutSource) :
    let child := executableInternalHHistory119 input.layoutSource domain fits
      assumptions (theoreticalCanonicalP18CircuitSource
        input.layoutSource domain fits assumptions)
    ∀ basis : QubitBasis
        (ExecutableHistoryAlignedPhysicalP18.AlignedDataQubits119 child),
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          input.rhsPreparation.circuit basis
          (zeroBasis119 (ExecutableHistoryAlignedPhysicalP18.AlignedDataQubits119 child)) =
        (ExecutableHistoryAlignedPhysicalP18Block.alignedPreparedAmplitude119
          child basis : ℂ) := by
  dsimp only
  intro basis
  have prepared := congrFun (rhsPreparation_zeroKet_eq_canonical input assumptions) basis
  have canonical := theoretical_rhsPreparation_aligned_zero_column
    input.layoutSource domain fits assumptions basis
  have column := prepared
  simp only [ExecutableHistoryQbPlusCleanBlock.applyOperator_basisKet119] at column
  exact column.trans canonical

theorem alignedP18_logical_block (input : FiniteScientificSource)
    (domain : ExecutableHistoryDomain119 input.layoutSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (assumptions : ExecutableM13Assumptions119 input.layoutSource)
    (output inputIndex : GramOperator.ExtendedIndex
      (ExecutableD119 input.layoutSource) (ExecutableC119 input.layoutSource)
      (ExecutableLabels119 input.layoutSource)) :
    let child := executableInternalHHistory119 input.layoutSource domain fits
      assumptions (theoreticalCanonicalP18CircuitSource
        input.layoutSource domain fits assumptions)
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (ExecutableHistoryAlignedPhysicalP18.alignedP18CircuitWithPreparation119
          child input.rhsPreparation)
        (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119 child output)
        (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119 child inputIndex) =
      (GramOperator.gNuOperator
        (executableP18Input119 input.layoutSource assumptions).base.system
        (executableP18Input119 input.layoutSource assumptions).base.alpha
        (executableP18Input119 input.layoutSource assumptions).base.nu
        output inputIndex : ℂ) := by
  dsimp only
  exact ExecutableHistoryAlignedPhysicalP18Block.alignedP18WithPreparation_logical_block119
    (executableInternalHHistory119 input.layoutSource domain fits assumptions
      (theoreticalCanonicalP18CircuitSource input.layoutSource domain fits assumptions))
    input.rhsPreparation (rhsPreparation_aligned_zero_column input domain fits assumptions)
    assumptions.one_le_nu output inputIndex

theorem hnuBranchWithAngle_denote (input : FiniteScientificSource)
    (domain : ExecutableHistoryDomain119 input.layoutSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (assumptions : ExecutableM13Assumptions119 input.layoutSource)
    (angle : AngleExpr) (angle_value : angle.uniformValue = hnuAngleF assumptions.nu) :
    let child := executableInternalHHistory119 input.layoutSource domain fits
      assumptions (theoreticalCanonicalP18CircuitSource
        input.layoutSource domain fits assumptions)
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (input.hnuBranchWithAngle angle).circuit =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (hnuExtensionNormalizedF child assumptions.nu).circuit := by
  exact theoreticalFiniteHnuBranchWithAngle_denote input.layoutSource domain fits
    assumptions angle angle_value

theorem p18WithAngle_denote (input : FiniteScientificSource)
    (domain : ExecutableHistoryDomain119 input.layoutSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (assumptions : ExecutableM13Assumptions119 input.layoutSource)
    (angle : AngleExpr) (angle_value : angle.uniformValue = hnuAngleF assumptions.nu) :
    let child := executableInternalHHistory119 input.layoutSource domain fits
      assumptions (theoreticalCanonicalP18CircuitSource
        input.layoutSource domain fits assumptions)
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (input.p18CircuitWithAngle angle) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (ExecutableHistoryAlignedPhysicalP18.alignedP18CircuitWithPreparation119
          child input.rhsPreparation) := by
  let child := executableInternalHHistory119 input.layoutSource domain fits
    assumptions (theoreticalCanonicalP18CircuitSource
      input.layoutSource domain fits assumptions)
  exact doubleWireLift_denote_congr
    (dataPlacement023 input.branchQubits)
    (ExecutableHistoryQbPlusCleanBlock.dataPlacement119 input.preparationQubits)
    (input.hnuBranchWithAngle angle).circuit
    (hnuExtensionNormalizedF child assumptions.nu).circuit
    (hnuBranchWithAngle_denote input domain fits assumptions angle angle_value)
    (ExecutableHistoryQbPlusCleanBlock.qBPlusBlockCircuit119 input.rhsPreparation)

/-- The actual finite P18 circuit with the original sparse preparer has the
independently specified Gram block on every logical row and column. -/
theorem p18WithAngle_logical_block (input : FiniteScientificSource)
    (domain : ExecutableHistoryDomain119 input.layoutSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (assumptions : ExecutableM13Assumptions119 input.layoutSource)
    (angle : AngleExpr) (angle_value : angle.uniformValue = hnuAngleF assumptions.nu)
    (output inputIndex : GramOperator.ExtendedIndex
      (ExecutableD119 input.layoutSource) (ExecutableC119 input.layoutSource)
      (ExecutableLabels119 input.layoutSource)) :
    let child := executableInternalHHistory119 input.layoutSource domain fits
      assumptions (theoreticalCanonicalP18CircuitSource
        input.layoutSource domain fits assumptions)
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (input.p18CircuitWithAngle angle)
        (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119 child output)
        (ExecutableHistoryAlignedPhysicalP18.alignedCleanEmbedding119 child inputIndex) =
      (GramOperator.gNuOperator
        (executableP18Input119 input.layoutSource assumptions).base.system
        (executableP18Input119 input.layoutSource assumptions).base.alpha
        (executableP18Input119 input.layoutSource assumptions).base.nu
        output inputIndex : ℂ) := by
  dsimp only
  rw [p18WithAngle_denote input domain fits assumptions angle angle_value]
  exact alignedP18_logical_block input domain fits assumptions output inputIndex

@[implicit_reducible] def sparseCommonP18Implementation (input : FiniteScientificSource)
    (domain : ExecutableHistoryDomain119 input.layoutSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (assumptions : ExecutableM13Assumptions119 input.layoutSource) :
    CommonP18Implementation input.layoutSource domain fits assumptions where
  signalCircuit := input.p18CircuitWithAngle (theoreticalExtensionAngle assumptions.nu)
  cleanBlock := by
    ext output inputIndex
    rw [NativeSingularPairTwoFrame.cleanBlock_basisKetEmbeddingMatrix_apply]
    exact p18WithAngle_logical_block input domain fits assumptions
      (theoreticalExtensionAngle assumptions.nu)
      (theoreticalExtensionAngle_value _) output inputIndex

/-- The proof instantiation uses the original finite source's plan, not its
dense amplitude presentation. The evidence above is constructed internally. -/
theorem sparseCommonOuterPlan_eq (input : FiniteScientificSource)
    (domain : ExecutableHistoryDomain119 input.layoutSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (assumptions : ExecutableM13Assumptions119 input.layoutSource) :
    letI := sparseCommonP18Implementation input domain fits assumptions
    theoreticalCommonOuterPlan input.layoutSource domain fits assumptions =
      input.outerPlanWithAngle (theoreticalExtensionAngle assumptions.nu) fits := by
  dsimp only
  unfold theoreticalCommonOuterPlan
  rfl

/-- The canonical scientific extension uses the same finite zero-angle
syntax as the numerical generator. Isolate this equality before instantiating
the large analytic input record. -/
theorem sparseCommonOuterPlan_nu_one (input : FiniteScientificSource)
    (domain : ExecutableHistoryDomain119 input.layoutSource)
    (fits : HistoryIndexFitsLayout119 input.layoutSource)
    (assumptions : ExecutableM13Assumptions119 input.layoutSource)
    (nu_one : assumptions.nu = 1) :
    letI := sparseCommonP18Implementation input domain fits assumptions
    theoreticalCommonOuterPlan input.layoutSource domain fits assumptions =
      input.outerPlan fits := by
  have angle : theoreticalExtensionAngle assumptions.nu = input.nuAngle := by
    rw [nu_one]
    simp [theoreticalExtensionAngle, FiniteScientificSource.nuAngle]
  exact (sparseCommonOuterPlan_eq input domain fits assumptions).trans
    (congrArg (fun value => input.outerPlanWithAngle value fits) angle)

end
end QLean.Circuits.FiniteScientificSparsePreparationBridge
