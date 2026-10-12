import QLean.History.Implementation.HistoryPipelineStateFromAmplitudeData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace ExecutableHistoryAlignedPhysicalP18Block

open Matrix
open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open ExecutableHistoryCore
open ExecutableHistoryQbPlusCleanBlock
open ExecutableHistoryImplementationRole
open ExecutableHistoryAlignedPhysicalP18
open ExecutableHistoryStateFromAmplitudeData

noncomputable section

variable {targetQubits : Nat}

def alignedPreparedAmplitude119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    QubitBasis (AlignedDataQubits119 child) → ℝ :=
  fun basis =>
    (stateFromAmplitude023 (HnuQubits119 child)
      (alignedLogicalAmplitude119 child) basis).re

theorem alignedPreparedAmplitude_on_embedding119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits)
    (index : GramOperator.ExtendedIndex d c R) :
    alignedPreparedAmplitude119 child (alignedDataEmbedding119 child index) =
      p18BPlus119 I index := by
  have hentry := stateFromAmplitude023_data_entry119
    (HnuQubits119 child)
    (Nat.zero_lt_of_lt child.layout.control.isLt)
    (alignedLogicalAmplitude119 child)
    (alignedLogicalAmplitude_energy119 child)
    (extendedIndexEmbeddingF child index)
  have hre := congrArg Complex.re hentry
  change (stateFromAmplitude023 (HnuQubits119 child)
      (alignedLogicalAmplitude119 child)
      (dataBasisEmbedding119 (HnuQubits119 child)
        (extendedIndexEmbeddingF child index))).re = _
  rw [hre]
  simp [alignedLogicalAmplitude119, paddedRealState119]

theorem alignedPreparedAmplitude_eq_zeroPadded119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    alignedPreparedAmplitude119 child =
      zeroPaddedAmplitude119 (alignedDataEmbedding119 child)
        (p18BPlus119 I) (fun _ => 0) := by
  funext basis
  classical
  by_cases hlogical : ∃ index : GramOperator.ExtendedIndex d c R,
      alignedDataEmbedding119 child index = basis
  · let index : GramOperator.ExtendedIndex d c R := Classical.choose hlogical
    have hindex : alignedDataEmbedding119 child index = basis :=
      Classical.choose_spec hlogical
    rw [← hindex, alignedPreparedAmplitude_on_embedding119]
    exact (zeroPaddedAmplitude119_on_embedding
      (alignedDataEmbedding119 child) (p18BPlus119 I) (fun _ => 0) index).symm
  · rw [zeroPaddedAmplitude119]
    simp only [hlogical]
    by_cases hdata : ∃ internal : QubitBasis (HnuQubits119 child),
        dataBasisEmbedding119 (HnuQubits119 child) internal = basis
    · let internal : QubitBasis (HnuQubits119 child) :=
        Classical.choose hdata
      have hinternal : dataBasisEmbedding119 (HnuQubits119 child) internal =
          basis := Classical.choose_spec hdata
      have hentry := stateFromAmplitude023_data_entry119
        (HnuQubits119 child)
        (Nat.zero_lt_of_lt child.layout.control.isLt)
        (alignedLogicalAmplitude119 child)
        (alignedLogicalAmplitude_energy119 child)
        internal
      have hre := congrArg Complex.re hentry
      change alignedPreparedAmplitude119 child basis = 0
      rw [← hinternal]
      change (stateFromAmplitude023 (HnuQubits119 child)
          (alignedLogicalAmplitude119 child)
          (dataBasisEmbedding119 (HnuQubits119 child) internal)).re = 0
      rw [hre]
      have hnotExtended : ¬ ∃ index : GramOperator.ExtendedIndex d c R,
          extendedIndexEmbeddingF child index = internal := by
        rintro ⟨index, equal⟩
        apply hlogical
        refine ⟨index, ?_⟩
        change dataBasisEmbedding119 (HnuQubits119 child)
            (extendedIndexEmbeddingF child index) = basis
        rw [equal, hinternal]
      simp [alignedLogicalAmplitude119, paddedRealState119, hnotExtended]
    · have hsupported := stateFromAmplitude023_imageSupported119
        (HnuQubits119 child)
        (Nat.zero_lt_of_lt child.layout.control.isLt)
        (alignedLogicalAmplitude119 child)
      have hzero := hsupported basis (by simpa using hdata)
      change (stateFromAmplitude023 (HnuQubits119 child)
        (alignedLogicalAmplitude119 child) basis).re = 0
      rw [hzero]
      rfl

theorem wireLiftOperator_fixedOutsideBasis_entry119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (operator : Operator (QubitBasis sourceQubits))
    (output input : QubitBasis sourceQubits) :
    wireLiftOperator placement operator
        (fixedOutsideBasisEmbedding placement outside output)
        (fixedOutsideBasisEmbedding placement outside input) =
      operator output input := by
  rw [wireLiftOperator_apply]
  rw [fixedOutsideBasisEmbedding_restrictF,
    fixedOutsideBasisEmbedding_restrictF]
  rw [fixedOutsideBasisEmbedding_hasFixedOutsideBasis,
    fixedOutsideBasisEmbedding_hasFixedOutsideBasis]
  simp

theorem mul_wireLiftOperator_fixedOutsideBasis_entry119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (left : Operator (QubitBasis targetQubits))
    (operator : Operator (QubitBasis sourceQubits))
    (output input : QubitBasis sourceQubits) :
    (left * wireLiftOperator placement operator)
        (fixedOutsideBasisEmbedding placement outside output)
        (fixedOutsideBasisEmbedding placement outside input) =
      ∑ middle : QubitBasis sourceQubits,
        left (fixedOutsideBasisEmbedding placement outside output)
            (fixedOutsideBasisEmbedding placement outside middle) *
  operator middle input := by
  classical
  simp only [Matrix.mul_apply]
  rw [← (splitWireEmbeddingEquiv placement).symm.sum_comp]
  simp [wireLiftOperator_apply, splitWireEmbeddingEquiv,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro middle _
  rw [fixedOutsideBasisEmbedding_hasFixedOutsideBasis]
  rw [fixedOutsideBasisEmbedding_restrictF]
  rfl

theorem sum_zeroPaddedAmplitude_mul119
    {ι physical : Type} [Fintype ι] [DecidableEq ι]
    [Fintype physical] [DecidableEq physical]
    (embedding : ι ↪ physical) (b : ι → ℝ)
    (f : physical → ℂ) :
    (∑ basis : physical,
        (zeroPaddedAmplitude119 embedding b (fun _ => 0) basis : ℂ) *
          f basis) =
      ∑ index : ι, (b index : ℂ) * f (embedding index) := by
  classical
  let rangePred : physical → Prop := Set.range embedding
  calc
    (∑ basis : physical,
        (zeroPaddedAmplitude119 embedding b (fun _ => 0) basis : ℂ) *
          f basis) =
        (∑ basis ∈ Finset.univ.filter rangePred,
          (zeroPaddedAmplitude119 embedding b (fun _ => 0) basis : ℂ) *
            f basis) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro basis _
      by_cases h : rangePred basis
      · rw [if_pos h]
      · rw [if_neg h]
        have hnot : ¬ ∃ index : ι, embedding index = basis := by
          intro existsIndex
          apply h
          exact existsIndex
        simp [zeroPaddedAmplitude119, hnot]
    _ = ∑ basis : {basis // rangePred basis},
          (zeroPaddedAmplitude119 embedding b (fun _ => 0) basis.1 : ℂ) *
            f basis.1 := by
      apply Finset.sum_subtype
      intro basis
      simp [rangePred]
    _ = ∑ index : ι, (b index : ℂ) * f (embedding index) := by
      symm
      let rangeEquiv : ι ≃ {basis // rangePred basis} :=
        { toFun := fun index => ⟨embedding index, ⟨index, rfl⟩⟩
          invFun := fun basis => Classical.choose basis.property
          left_inv := by
            intro index
            apply embedding.injective
            exact Classical.choose_spec
              (show ∃ source, embedding source = embedding index from ⟨index, rfl⟩)
          right_inv := by
            intro basis
            apply Subtype.ext
            exact Classical.choose_spec basis.property }
      apply Fintype.sum_equiv rangeEquiv
      intro index
      simp [rangeEquiv, rangePred, zeroPaddedAmplitude119]

theorem complexQbPlus_zeroPadded_mul_restrict119
    {ι physical : Type} [Fintype ι] [DecidableEq ι]
    [Fintype physical] [DecidableEq physical]
    (embedding : ι ↪ physical) (b : ι → ℝ)
    (right : Matrix physical physical ℂ)
    (logicalRight : Matrix ι ι ℂ)
    (rightRestrict : ∀ output input,
      right (embedding output) (embedding input) =
        logicalRight output input)
    (output input : ι) :
    (complexQbPlusMatrix119
        (zeroPaddedAmplitude119 embedding b (fun _ => 0)) * right)
        (embedding output) (embedding input) =
      (complexQbPlusMatrix119 b * logicalRight) output input := by
  classical
  calc
    (complexQbPlusMatrix119
        (zeroPaddedAmplitude119 embedding b (fun _ => 0)) * right)
        (embedding output) (embedding input) =
      right (embedding output) (embedding input) -
        (b output : ℂ) *
          ∑ middle : physical,
            (zeroPaddedAmplitude119 embedding b (fun _ => 0) middle : ℂ) *
              right middle (embedding input) := by
        simp only [Matrix.mul_apply, complexQbPlusMatrix119,
          JenningsHistory.qBPlusMatrix, zeroPaddedAmplitude119_on_embedding,
          Complex.ofReal_sub, Complex.ofReal_mul]
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
        congr 1
        · rw [Fintype.sum_eq_single (embedding output)]
          · simp
          · intro x hx
            simp [Ne.symm hx]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro middle _
          ring
    _ = right (embedding output) (embedding input) -
        (b output : ℂ) *
          ∑ middle : ι,
            (b middle : ℂ) * right (embedding middle) (embedding input) := by
      rw [sum_zeroPaddedAmplitude_mul119]
    _ = (complexQbPlusMatrix119 b * logicalRight) output input := by
      simp_rw [rightRestrict]
      simp only [Matrix.mul_apply, complexQbPlusMatrix119,
        JenningsHistory.qBPlusMatrix, Complex.ofReal_sub, Complex.ofReal_mul]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      congr 1
      · rw [Fintype.sum_eq_single output]
        · simp
        · intro x hx
          simp [Ne.symm hx]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro middle _
        ring

def realMatrixCast119 {ι : Type} (right : Matrix ι ι ℝ) :
    Matrix ι ι ℂ :=
  fun row col => (right row col : ℂ)

theorem complexQbPlus_mul_realCast119
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (right : Matrix ι ι ℝ) (output input : ι) :
    (complexQbPlusMatrix119 b * realMatrixCast119 right) output input =
      ((JenningsHistory.qBPlusMatrix b * right) output input : ℂ) := by
  change
    (∑ middle : ι,
        (JenningsHistory.qBPlusMatrix b output middle : ℂ) *
          (right middle input : ℂ)) =
      ((∑ middle : ι,
        JenningsHistory.qBPlusMatrix b output middle * right middle input : ℝ) : ℂ)
  push_cast
  rfl

theorem alignedHnu_logical_block119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits)
    (hnu : 1 ≤ I.base.nu)
    (output input : GramOperator.ExtendedIndex d c R) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (alignedHnu119 child).circuit
        (alignedDataEmbedding119 child output)
        (alignedDataEmbedding119 child input) =
      (JenningsHistory.dalzellExtendedH I.base.system I.base.alpha I.base.nu
        output input : ℂ) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      ((hnuExtensionNormalizedF child I.base.nu).circuit.mapGates
        (PrimitiveGate.mapWires (dataPlacement023 (HnuQubits119 child))))
      (fixedOutsideBasisEmbedding
        (dataPlacement023 (HnuQubits119 child)) dataOutsideZero023
        (extendedIndexEmbeddingF child output))
      (fixedOutsideBasisEmbedding
        (dataPlacement023 (HnuQubits119 child)) dataOutsideZero023
        (extendedIndexEmbeddingF child input)) = _
  rw [denote_mapPrimitiveWires_eq_wireLiftOperator]
  rw [wireLiftOperator_fixedOutsideBasis_entry119]
  exact hnuExtension_clean_blockF child hnu output input

/-- The P18 logical block is independent of which normalized preparation
circuit realizes the prescribed physical `bPlus` state from zero. In
particular, no equality of the new and old preparation unitaries is needed. -/
theorem alignedP18WithPreparation_logical_block119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits)
    (preparation : NormalizedCircuit (AlignedDataQubits119 child))
    (prepares : ∀ basis : QubitBasis (AlignedDataQubits119 child),
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          preparation.circuit basis
          (zeroBasis119 (AlignedDataQubits119 child)) =
        (alignedPreparedAmplitude119 child basis : ℂ))
    (hnu : 1 ≤ I.base.nu)
    (output input : GramOperator.ExtendedIndex d c R) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (alignedP18CircuitWithPreparation119 child preparation)
        (alignedCleanEmbedding119 child output)
        (alignedCleanEmbedding119 child input) =
      (GramOperator.gNuOperator I.base.system I.base.alpha I.base.nu
        output input : ℂ) := by
  have block : signalZeroBlock119
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (qBPlusBlockCircuit119 preparation)) =
      complexQbPlusMatrix119 (alignedPreparedAmplitude119 child) :=
    qBPlusBlockCircuit119_clean_block preparation
      (alignedPreparedAmplitude119 child) prepares
  have outer : Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (alignedP18CircuitWithPreparation119 child preparation)
        (alignedCleanEmbedding119 child output)
        (alignedCleanEmbedding119 child input) =
      (complexQbPlusMatrix119 (alignedPreparedAmplitude119 child) *
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (alignedHnu119 child).circuit)
        (alignedDataEmbedding119 child output)
        (alignedDataEmbedding119 child input) := by
    rw [alignedP18CircuitWithPreparation_denote119]
    change
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (qBPlusBlockCircuit119 preparation) *
          Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            ((alignedHnu119 child).circuit.mapGates
              (PrimitiveGate.mapWires
                (dataPlacement119 (AlignedDataQubits119 child)))))
          (blockBasis119 (alignedDataEmbedding119 child output))
          (blockBasis119 (alignedDataEmbedding119 child input)) = _
    rw [denote_mapPrimitiveWires_eq_wireLiftOperator]
    change
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (qBPlusBlockCircuit119 preparation) *
          wireLiftOperator (dataPlacement119 (AlignedDataQubits119 child))
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              (alignedHnu119 child).circuit))
        (fixedOutsideBasisEmbedding
          (dataPlacement119 (AlignedDataQubits119 child)) (fun _ => false)
          (alignedDataEmbedding119 child output))
        (fixedOutsideBasisEmbedding
          (dataPlacement119 (AlignedDataQubits119 child)) (fun _ => false)
          (alignedDataEmbedding119 child input)) = _
    rw [mul_wireLiftOperator_fixedOutsideBasis_entry119]
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro middle _
    exact congrArg
      (fun coefficient => coefficient *
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (alignedHnu119 child).circuit middle
          (alignedDataEmbedding119 child input))
      (by simpa [blockBasis119, signalZeroBlock119] using
        congrFun (congrFun block
          (alignedDataEmbedding119 child output)) middle)
  rw [outer, alignedPreparedAmplitude_eq_zeroPadded119]
  rw [complexQbPlus_zeroPadded_mul_restrict119
    (alignedDataEmbedding119 child) (p18BPlus119 I)
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (alignedHnu119 child).circuit)
    (realMatrixCast119
      (JenningsHistory.dalzellExtendedH I.base.system I.base.alpha I.base.nu))
    (alignedHnu_logical_block119 child hnu) output input]
  rw [complexQbPlus_mul_realCast119]
  rw [p18_qBPlus_dalzellExtendedH_eq_gNuOperatorF]

end
end ExecutableHistoryAlignedPhysicalP18Block
