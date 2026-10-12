import QLean.SignalProcessing.NativeFiniteSignalEmbedding
import QLean.SignalProcessing.M13bQSVTLogicalEmbedding
import QLean.Circuits.Foundation.QubitBasisEncoding
import QLean.SignalProcessing.M13cSpecification
import QLean.Circuits.Foundation.ClassicalArithmeticCorrectnessAnalytic
import Mathlib
import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.History.Jennings.PureSpec
import QLean.SignalProcessing.PhaseScheduleProofsPhaseWordContract
import QLean.SignalProcessing.PhaseScheduleProofsChebyshevContract
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.PhaseShiftMacros
import QLean.History.HistoryEmbeddingNorm
import QLean.History.Jennings.ProofEstablishedBridge
import QLean.Circuits.Foundation.FinitePhaseTransformAnalytic
import QLean.Circuits.Foundation.CircuitListLemmas
import QLean.Circuits.Foundation.Foundations
import QLean.Circuits.Foundation.QuantumFourierAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic
import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.WireEmbeddingAnalytic
import QLean.Circuits.Foundation.ReversibleLogicCleanAnalytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkMultiControlledXCorrectnessAnalytic
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2
import QLean.Circuits.Foundation.QuantumFourier
import QLean.Circuits.Foundation.OperatorL2Error
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import QLean.Circuits.Foundation.Metrics
import QLean.Circuits.Foundation.ReversibleLogic
import QLean.Circuits.Foundation.WireEmbedding
import QLean.Circuits.Foundation.WireEmbeddingL2Analytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkClean
import QLean.Circuits.Foundation.ControlledConstantAdderAnalytic

/-! Finite enumeration of the extended history basis. -/

set_option autoImplicit false
set_option warningAsError true

namespace ScientificExtractionPhysicalSpecification

def finiteExtendedHistoryRows119 (d c R : Nat) :
    List (GramOperator.ExtendedIndex d c R) :=
  ((List.finRange c).flatMap fun clock =>
    (List.finRange R).flatMap fun order =>
      (List.finRange d).map fun state =>
        (Sum.inl ⟨clock, order, state⟩ :
          GramOperator.ExtendedIndex d c R))
  ++ [Sum.inr ()]

theorem finiteExtendedHistoryRows119_complete (d c R : Nat)
    (index : GramOperator.ExtendedIndex d c R) :
    index ∈ finiteExtendedHistoryRows119 d c R := by
  cases index with
  | inl row =>
      rcases row with ⟨clock, order, state⟩
      apply List.mem_append.mpr
      left
      apply List.mem_flatMap.mpr
      refine ⟨clock, by simp, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨order, by simp, ?_⟩
      apply List.mem_map.mpr
      exact ⟨state, by simp, rfl⟩
  | inr extension =>
      cases extension
      simp [finiteExtendedHistoryRows119]

theorem finiteExtendedHistoryRows119_nodup (d c R : Nat) :
    (finiteExtendedHistoryRows119 d c R).Nodup := by
  let encode : Fin c × (Fin R × Fin d) → GramOperator.ExtendedIndex d c R :=
    fun pair => Sum.inl ⟨pair.1, pair.2.1, pair.2.2⟩
  have encode_injective : Function.Injective encode := by
    intro left right equal
    have rowEqual := Sum.inl.inj equal
    apply Prod.ext
    · exact congrArg (fun row => row.clock) rowEqual
    · apply Prod.ext
      · exact congrArg (fun row => row.order) rowEqual
      · exact congrArg (fun row => row.state) rowEqual
  have product_nodup :
      ((List.finRange c).product
        ((List.finRange R).product (List.finRange d))).Nodup :=
    (List.nodup_finRange c).product
      ((List.nodup_finRange R).product (List.nodup_finRange d))
  have main_nodup := product_nodup.map encode_injective
  have extension_not_mem :
      (Sum.inr () : GramOperator.ExtendedIndex d c R) ∉
        ((List.finRange c).product
          ((List.finRange R).product (List.finRange d))).map encode := by
    simp [encode]
  have all_nodup := List.Nodup.concat extension_not_mem main_nodup
  simpa [List.concat_eq_append, finiteExtendedHistoryRows119, encode,
    List.product, List.map_flatMap, List.map_map, Function.comp_def] using
    all_nodup

end ScientificExtractionPhysicalSpecification
