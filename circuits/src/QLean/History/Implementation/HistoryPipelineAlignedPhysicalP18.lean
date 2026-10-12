import QLean.History.Implementation.HistoryPipelineReferenceM10Bridge
import QLean.History.Implementation.HistoryPipelineSumComposition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace ExecutableHistoryAlignedPhysicalP18

open Matrix
open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open ExecutableHistoryCore
open ExecutableHistoryQbPlusCleanBlock
open ExecutableHistoryImplementationRole

noncomputable section

variable {targetQubits : Nat}

abbrev HnuQubits119 {d c r m R : Nat}
    {I : P18Input119 d c r m R}
    (_child : InternalHHistoryCleanComponentF I targetQubits) : Nat :=
  targetQubits

def alignedLogicalAmplitude119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    QubitBasis (HnuQubits119 child) → ℝ :=
  fun basis =>
    (paddedRealState119 _ _ (extendedIndexEmbeddingF child)
      (p18BPlus119 I) basis).re

theorem alignedPaddedState_realCast119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    paddedRealState119 _ _ (extendedIndexEmbeddingF child)
        (p18BPlus119 I) =
      fun basis => (alignedLogicalAmplitude119 child basis : ℂ) := by
  funext basis
  by_cases h : ∃ i, extendedIndexEmbeddingF child i = basis
  · simp [alignedLogicalAmplitude119, paddedRealState119, h]
  · simp [alignedLogicalAmplitude119, paddedRealState119, h]

theorem alignedLogicalAmplitude_energy119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    realEnergy023 (alignedLogicalAmplitude119 child) = 1 := by
  calc
    realEnergy023 (alignedLogicalAmplitude119 child) =
        ∑ basis : QubitBasis (HnuQubits119 child),
          Complex.normSq ((alignedLogicalAmplitude119 child basis : ℂ)) := by
      simp [realEnergy023, Complex.normSq, pow_two]
    _ = ∑ basis : QubitBasis (HnuQubits119 child),
          Complex.normSq
            (paddedRealState119 _ _ (extendedIndexEmbeddingF child)
              (p18BPlus119 I) basis) := by
      rw [alignedPaddedState_realCast119 child]
    _ = 1 := by
      rw [paddedRealState119_normSq_sum]
      simpa [JenningsHistory.unitNorm, JenningsHistory.unitNormSquared,
        Fintype.sum_sum_type, pow_two] using p18BPlus119_unitNorm I

def alignedPreparation119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    NormalizedCircuit (prepWidth023 (HnuQubits119 child)) :=
  realPreparationCircuit023
    (Nat.zero_lt_of_lt child.layout.control.isLt)
    (alignedLogicalAmplitude119 child)
    (alignedLogicalAmplitude_energy119 child)

abbrev AlignedDataQubits119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) : Nat :=
  prepWidth023 (HnuQubits119 child)

abbrev AlignedTotalQubits119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) : Nat :=
  blockQubits119 (AlignedDataQubits119 child)

def alignedDataEmbedding119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    GramOperator.ExtendedIndex d c R ↪
      QubitBasis (AlignedDataQubits119 child) where
  toFun := fun index =>
    fixedOutsideBasisEmbedding
      (dataPlacement023 (HnuQubits119 child)) dataOutsideZero023
      (extendedIndexEmbeddingF child index)
  inj' := by
    intro left right h
    exact (extendedIndexEmbeddingF child).injective
      ((fixedOutsideBasisEmbedding
        (dataPlacement023 (HnuQubits119 child)) dataOutsideZero023).injective h)

def alignedCleanEmbedding119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    GramOperator.ExtendedIndex d c R ↪
      QubitBasis (AlignedTotalQubits119 child) where
  toFun := fun index => blockBasis119 (alignedDataEmbedding119 child index)
  inj' := by
    intro left right h
    exact (alignedDataEmbedding119 child).injective
      (blockBasis119_injective h)

def alignedQbPlusCircuit119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    Circuit (PrimitiveGate (AlignedTotalQubits119 child)) :=
  qBPlusBlockCircuit119 (alignedPreparation119 child)

def alignedHnu119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    NormalizedCircuit (AlignedDataQubits119 child) :=
  NormalizedCircuit.mapWires (dataPlacement023 (HnuQubits119 child))
    (hnuExtensionNormalizedF child I.base.nu)

def alignedLiftedHnu119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    NormalizedCircuit (AlignedTotalQubits119 child) :=
  NormalizedCircuit.mapWires (dataPlacement119 (AlignedDataQubits119 child))
    (alignedHnu119 child)

def alignedP18Circuit119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    Circuit (PrimitiveGate (AlignedTotalQubits119 child)) :=
  Circuit.sequence [
    (alignedLiftedHnu119 child).circuit,
    alignedQbPlusCircuit119 child]

/-- The same P18 physical assembly with an arbitrary normalized preparation
word. Correctness requires only its zero-input state, not equality with the
older preparation circuit on every input. -/
def alignedP18CircuitWithPreparation119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits)
    (preparation : NormalizedCircuit (AlignedDataQubits119 child)) :
    Circuit (PrimitiveGate (AlignedTotalQubits119 child)) :=
  Circuit.sequence [
    (alignedLiftedHnu119 child).circuit,
    qBPlusBlockCircuit119 preparation]

theorem alignedP18CircuitWithPreparation_denote119
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits)
    (preparation : NormalizedCircuit (AlignedDataQubits119 child)) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (alignedP18CircuitWithPreparation119 child preparation) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (qBPlusBlockCircuit119 preparation) *
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (alignedLiftedHnu119 child).circuit := by
  unfold alignedP18CircuitWithPreparation119
  rw [Circuit.denote_sequence_eq_operatorSequence]
  simp [operatorSequence]

end
end ExecutableHistoryAlignedPhysicalP18
