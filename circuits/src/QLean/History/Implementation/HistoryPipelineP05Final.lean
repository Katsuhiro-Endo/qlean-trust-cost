import QLean.History.Implementation.HistoryPipelineP05H1Target

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option warningAsError true

namespace ExecutableHistoryExecutableHistory

open Matrix
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open ExecutableHistoryHistoryEmbedding
open ExecutableHistoryHistoryCleanInput

noncomputable section

theorem correctedP05Component119_target_eq_physical
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (correctedP05Component119 source domain).target =
      repairedP05PhysicalOperator119 source domain := by
  rw [correctedP05Component119_target]
  unfold correctedP05Components119
  simp only [List.map_cons, List.map_nil]
  rw [historyH4CorrectedSelectorForwardComponent_target,
    historyP15FullCleanH2Component_target]
  change operatorSequence [
      h1SelectorRecordedOperator _,
      executableH2Target119 source domain,
      (repairedH3Component119 source domain).target,
      (historySelectorPreparationFromP50InverseExactComponent
        (historySelectorPreparationConcreteP50Children internalZeroSymbolEnvironment
          (correctedSelectorParameters119 source domain))).target] = _
  rw [repairedH3Component119_target,
    historySelectorPreparationFromP50InverseExactComponent_target]
  rw [repairedP05H1ForwardTarget119]
  simp [operatorSequence, repairedP05PhysicalOperator119,
    repairedSelectMiddle119, Matrix.mul_assoc]

theorem executableHistoryBasis119_correctedP05IdealInput
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    h4CorrectedIdealInputPredicate
        (correctedH4Specification119 source domain)
        (executableHistoryBasis119 source domain fits index) := by
  unfold h4CorrectedIdealInputPredicate
  constructor
  · unfold correctedH4Specification119
      historyH4CorrectedConcreteSpecification
      historyH4CorrectedCleanSpecificationOf
      historyH4CorrectedConcreteTaylorSpecification
    rw [h2TaylorIdealInputPredicate_eq_historyP15FullCleanInputPredicate]
    exact executableHistoryBasis119_p15FullCleanInput source domain fits index
  · change historyClockBranchUncomputedStrongOutputPredicate
      (ExecutableLayout119 source domain)
      (executableHistoryBasis119 source domain fits index)
    exact executableHistoryBasis119_correctedClockClean source domain fits index

theorem correctedP05Component119_entry_eq_normalized
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    Circuit.denote (primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)
        (correctedP05Component119 source domain).circuit
        (executableHistoryBasis119 source domain fits outputIndex)
        (executableHistoryBasis119 source domain fits inputIndex) =
      ((correctedNormalizedHistoryTarget119 source.historyParameters
        (commonModelQ119 source.toCommonSource119)
        outputIndex inputIndex : ℝ) : ℂ) := by
  have stateEqual := correctedP05Component119_correct_basisKet
    source domain
    (executableHistoryBasis119 source domain fits inputIndex)
    (executableHistoryBasis119_correctedP05IdealInput
      source domain fits inputIndex)
  rw [correctedP05Component119_target_eq_physical] at stateEqual
  have entryEqual := congrFun stateEqual
    (executableHistoryBasis119 source domain fits outputIndex)
  simp only [VerifiedCircuitCore.applyOperator_basisKet] at entryEqual
  calc
    _ = repairedP05PhysicalOperator119 source domain
        (executableHistoryBasis119 source domain fits outputIndex)
        (executableHistoryBasis119 source domain fits inputIndex) := entryEqual
    _ = _ := by
      rw [← correctedBranchHistoryBasis119_zero_eq_executable
          source domain fits outputIndex,
        ← correctedBranchHistoryBasis119_zero_eq_executable
          source domain fits inputIndex]
      exact repairedP05PhysicalOperator119_entry_eq_normalized
        source domain fits outputIndex inputIndex

theorem correctedP05Component119_entry_eq_scaledHistory
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    Circuit.denote (primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)
        (correctedP05Component119 source domain).circuit
        (executableHistoryBasis119 source domain fits outputIndex)
        (executableHistoryBasis119 source domain fits inputIndex) =
      ((JenningsHistory.scaledHistory
        (ExecutableHistoryReferenceM10Bridge.translatedSystem
          source.historyParameters
          (commonModelQ119 source.toCommonSource119)
          source.initial source.historyWellFormed)
        (correctedAlpha119 source.historyParameters.taylorOrder)
        (ExecutableHistoryReferenceM10Bridge.indexEquiv source.historyParameters
          outputIndex)
        (ExecutableHistoryReferenceM10Bridge.indexEquiv source.historyParameters
          inputIndex) : ℝ) : ℂ) := by
  rw [correctedP05Component119_entry_eq_normalized]
  congr 1
  exact (corrected_scaledHistory_entry_eq_normalizedTarget119
    source.historyParameters
    (commonModelQ119 source.toCommonSource119)
    source.initial source.historyWellFormed outputIndex inputIndex).symm

end

end ExecutableHistoryExecutableHistory
