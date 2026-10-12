import QLean.History.Implementation.HistoryPipelineP05MiddleLogical

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
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

def selectorBranchOfBasis119 (basis : QubitBasis 2) : Fin 4 where
  val := (if basis 0 then 1 else 0) + (if basis 1 then 2 else 0)
  isLt := by
    cases first : basis 0 <;> cases second : basis 1 <;>
      simp

def correctedSelectorBranchEquiv119 : Fin 4 ≃ QubitBasis 2 where
  toFun := correctedSelectorBranchBasis119
  invFun := selectorBranchOfBasis119
  left_inv := by
    intro branch
    fin_cases branch <;> rfl
  right_inv := by
    intro basis
    funext index
    fin_cases index <;>
      cases first : basis 0 <;> cases second : basis 1 <;>
        simp [selectorBranchOfBasis119, correctedSelectorBranchBasis119,
          selectorBasis119, first, second]

theorem mul_wireLiftOperator_fixedOutsideBasis_entry_two119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outsideOutput outsideInput : OutsideWire placement → Bool)
    (left : VerifiedCircuitCore.Operator (QubitBasis targetQubits))
    (operator : VerifiedCircuitCore.Operator (QubitBasis sourceQubits))
    (output input : QubitBasis sourceQubits) :
    (left * wireLiftOperator placement operator)
        (fixedOutsideBasisEmbedding placement outsideOutput output)
        (fixedOutsideBasisEmbedding placement outsideInput input) =
      ∑ middle : QubitBasis sourceQubits,
        left (fixedOutsideBasisEmbedding placement outsideOutput output)
            (fixedOutsideBasisEmbedding placement outsideInput middle) *
          operator middle input := by
  classical
  simp only [Matrix.mul_apply]
  rw [← (splitWireEmbeddingEquiv placement).symm.sum_comp]
  simp [wireLiftOperator_apply, splitWireEmbeddingEquiv,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro middle _
  simp [fixedOutsideBasisEmbedding,
    restrictToPlacedWires_mergePlacedAndOutsideBasis]

theorem wireLiftOperator_mul_fixedOutsideBasis_entry_two119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outsideOutput outsideInput : OutsideWire placement → Bool)
    (operator : VerifiedCircuitCore.Operator (QubitBasis sourceQubits))
    (right : VerifiedCircuitCore.Operator (QubitBasis targetQubits))
    (output input : QubitBasis sourceQubits) :
    (wireLiftOperator placement operator * right)
        (fixedOutsideBasisEmbedding placement outsideOutput output)
        (fixedOutsideBasisEmbedding placement outsideInput input) =
      ∑ middle : QubitBasis sourceQubits,
        operator output middle *
          right (fixedOutsideBasisEmbedding placement outsideOutput middle)
            (fixedOutsideBasisEmbedding placement outsideInput input) := by
  classical
  simp only [Matrix.mul_apply]
  rw [← (splitWireEmbeddingEquiv placement).symm.sum_comp]
  simp [wireLiftOperator_apply, splitWireEmbeddingEquiv,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro middle _
  simp [fixedOutsideBasisEmbedding,
    restrictToPlacedWires_mergePlacedAndOutsideBasis]

theorem executableHistoryBasis119_selector_zero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source)
    (selectorIndex : Fin 2) :
    executableHistoryBasis119 source domain fits index
      ((ExecutableLayout119 source domain).selector.wire selectorIndex) =
      false := by
  unfold executableHistoryBasis119
  rw [writeRegisterBits_apply_outside]
  · rw [writeRegisterBits_apply_outside]
    · rw [writeRegisterBits_apply_outside]
      · intro orderIndex equal
        exact (selector_wire_ne_historyNonselectorTail119
          (ExecutableLayout119 source domain) selectorIndex _
          (by
            simp [historyNonselectorTail119, historyRegisterWires])).symm equal
    · intro clockIndex equal
      exact (selector_wire_ne_historyNonselectorTail119
        (ExecutableLayout119 source domain) selectorIndex _
        (by
          simp [historyNonselectorTail119, historyRegisterWires])).symm equal
  · intro dataIndex equal
    exact (selector_wire_ne_historyNonselectorTail119
      (ExecutableLayout119 source domain) selectorIndex _
      (by
        simp [historyNonselectorTail119, historyRegisterWires])).symm equal

theorem correctedBranchHistoryBasis119_zero_eq_executable
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : OldHistoryIndex119 source) :
    correctedBranchHistoryBasis119 source domain fits ⟨0, by decide⟩ index =
      executableHistoryBasis119 source domain fits index := by
  apply (fullBasis_eq_iff_restrictions_eq
    (correctedSelectorPlacement119 source domain) _ _).2
  constructor
  · funext selectorIndex
    rw [correctedBranchHistoryBasis119_restrict_selector]
    change correctedSelectorBranchBasis119 ⟨0, by decide⟩ selectorIndex =
      executableHistoryBasis119 source domain fits index
        ((ExecutableLayout119 source domain).selector.wire selectorIndex)
    rw [executableHistoryBasis119_selector_zero]
    fin_cases selectorIndex <;> rfl
  · exact correctedBranchHistoryBasis119_restrict_outside
      source domain fits ⟨0, by decide⟩ index

theorem correctedSelectorInverseOperator_eq_wireLift119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    historySelectorPreparationInverseOperator internalZeroSymbolEnvironment
        (correctedSelectorParameters119 source domain) =
      wireLiftOperator (correctedSelectorPlacement119 source domain)
        (star (selectorLocalOperator119 source.historyParameters.taylorOrder 1)) := by
  unfold historySelectorPreparationInverseOperator
  rw [correctedSelectorOperator_eq_wireLift119]
  ext output input
  change (star (wireLiftOperator
      (correctedSelectorPlacement119 source domain)
      (selectorLocalOperator119 source.historyParameters.taylorOrder 1)))
        output input = _
  rw [Matrix.star_apply, wireLiftOperator_apply, wireLiftOperator_apply,
    Matrix.star_apply]
  by_cases outsideEqual :
      restrictToOutsideWires (correctedSelectorPlacement119 source domain) output =
        restrictToOutsideWires (correctedSelectorPlacement119 source domain) input
  · rw [if_pos outsideEqual, if_pos outsideEqual.symm]
    simp
  · rw [if_neg outsideEqual, if_neg (by
      intro reverse
      exact outsideEqual reverse.symm)]
    simp

noncomputable def repairedP05PhysicalOperator119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    VerifiedCircuitCore.Operator
      (QubitBasis (ExecutableRaw119 source).history.qubits) :=
  historySelectorPreparationInverseOperator internalZeroSymbolEnvironment
      (correctedSelectorParameters119 source domain) *
    repairedSelectMiddle119 source domain *
    historySelectorPreparationOperator internalZeroSymbolEnvironment
      (correctedSelectorParameters119 source domain)

theorem repairedP05PhysicalOperator119_entry_raw
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (outputIndex inputIndex : OldHistoryIndex119 source) :
    repairedP05PhysicalOperator119 source domain
        (correctedBranchHistoryBasis119 source domain fits ⟨0, by decide⟩
          outputIndex)
        (correctedBranchHistoryBasis119 source domain fits ⟨0, by decide⟩
          inputIndex) =
      ∑ inputSelector : QubitBasis 2,
        (∑ outputSelector : QubitBasis 2,
          (star (selectorLocalOperator119 source.historyParameters.taylorOrder 1))
              (selectorBasis119 false false) outputSelector *
            repairedSelectMiddle119 source domain
              (fixedOutsideBasisEmbedding
                (correctedSelectorPlacement119 source domain)
                (correctedSelectorOutside119 source domain
                  (executableHistoryBasis119 source domain fits outputIndex))
                outputSelector)
              (fixedOutsideBasisEmbedding
                (correctedSelectorPlacement119 source domain)
                (correctedSelectorOutside119 source domain
                  (executableHistoryBasis119 source domain fits inputIndex))
                inputSelector)) *
          selectorLocalOperator119 source.historyParameters.taylorOrder 1
            inputSelector (selectorBasis119 false false) := by
  unfold repairedP05PhysicalOperator119
  rw [correctedSelectorOperator_eq_wireLift119,
    correctedSelectorInverseOperator_eq_wireLift119]
  unfold correctedBranchHistoryBasis119
  rw [mul_wireLiftOperator_fixedOutsideBasis_entry_two119]
  apply Finset.sum_congr rfl
  intro inputSelector _
  rw [wireLiftOperator_mul_fixedOutsideBasis_entry_two119]
  rfl

end
end ExecutableHistoryExecutableHistory
