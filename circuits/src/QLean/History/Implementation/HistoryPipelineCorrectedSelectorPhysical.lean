import QLean.History.Implementation.HistoryPipelineCorrectedRecordedLCU
import QLean.History.Implementation.HistoryPipelineCorrectedP05Circuit
import QLean.History.Implementation.HistoryPipelineExecutableP05Target
import QLean.History.Implementation.HistoryPipelineExecutableSelectorCircuit

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

noncomputable section

def correctedSelectorPlacement119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    Fin 2 ↪ Fin (ExecutableRaw119 source).history.qubits where
  toFun := (ExecutableLayout119 source domain).selector.wire
  inj' := (ExecutableLayout119 source domain).selector.injective

theorem correctedSelectorCircuit_denote_eq_map119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    Circuit.denote (primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)
        (historySelectorPreparationCircuit
          (correctedSelectorParameters119 source domain)) =
      Circuit.denote (primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)
        (Circuit.mapGates
          (PrimitiveGate.mapWires (correctedSelectorPlacement119 source domain))
          (historySelectorPreparationCircuit
            (selectorLocalParameters119 source.historyParameters.taylorOrder 1))) := by
  have highEval :
      (correctedSelectorHighAngleExpr119 source).eval
          internalZeroSymbolEnvironment =
        selectorHighAngle119 source.historyParameters.taylorOrder 1 := by
    change (correctedSelectorHighAngleExpr119 source).eval (fun _ => 0) = _
    exact correctedSelectorHighAngleExpr119_value source
  have lowEval :
      correctedSelectorLowAngleExpr119.eval internalZeroSymbolEnvironment =
        selectorLowAngle119 1 := by
    change correctedSelectorLowAngleExpr119.eval (fun _ => 0) = _
    exact correctedSelectorLowAngleExpr119_value
  simp [historySelectorPreparationCircuit,
    historySelectorPreparationGates, correctedSelectorParameters119,
    selectorLocalParameters119, selectorPreparationParameters119,
    historySelectorPreparationParametersAtLayout,
    correctedSelectorPlacement119, VerifiedCircuitCore.Circuit.mapGates,
    VerifiedCircuitCore.Circuit.denote, PrimitiveGate.mapWires,
    primitiveGateOperatorWithSymbols, highEval, lowEval]

theorem correctedSelectorOperator_eq_wireLift119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    historySelectorPreparationOperator internalZeroSymbolEnvironment
        (correctedSelectorParameters119 source domain) =
      wireLiftOperator (correctedSelectorPlacement119 source domain)
        (selectorLocalOperator119 source.historyParameters.taylorOrder 1) := by
  calc
    _ = Circuit.denote
          (primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)
          (historySelectorPreparationCircuit
            (correctedSelectorParameters119 source domain)) :=
      (historySelectorPreparationCircuit_correct _ _).symm
    _ = Circuit.denote
          (primitiveGateOperatorWithSymbols internalZeroSymbolEnvironment)
          (Circuit.mapGates
            (PrimitiveGate.mapWires
              (correctedSelectorPlacement119 source domain))
            (historySelectorPreparationCircuit
              (selectorLocalParameters119
                source.historyParameters.taylorOrder 1))) :=
      correctedSelectorCircuit_denote_eq_map119 source domain
    _ = wireLiftOperator (correctedSelectorPlacement119 source domain)
          (selectorLocalOperator119 source.historyParameters.taylorOrder 1) := by
      rw [denote_mapPrimitiveWires_eq_wireLiftOperator]
      rw [historySelectorPreparationCircuit_correct]
      rfl

def correctedSelectorOutside119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (basis : QubitBasis (ExecutableRaw119 source).history.qubits) :
    OutsideWire (correctedSelectorPlacement119 source domain) → Bool :=
  restrictToOutsideWires (correctedSelectorPlacement119 source domain) basis

def correctedSelectorBranchBasis119 (branch : Fin 4) : QubitBasis 2 :=
  selectorBasis119 (decide (branch.val % 2 = 1))
    (decide (branch.val / 2 = 1))

@[simp] theorem fixedOutsideStateEmbedding_apply_embedding119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (state : VerifiedCircuitCore.State (QubitBasis sourceQubits))
    (input : QubitBasis sourceQubits) :
    fixedOutsideStateEmbedding placement outside state
        (fixedOutsideBasisEmbedding placement outside input) =
      state input := by
  simp [fixedOutsideStateEmbedding, fixedOutsideBasisEmbedding]

theorem selectorLocalOperator_correctedAmplitude119
    (taylorOrder : Nat) (branch : Fin 4) :
    VerifiedCircuitCore.applyOperator
        (selectorLocalOperator119 taylorOrder 1)
        (VerifiedCircuitCore.basisKet (selectorBasis119 false false))
        (correctedSelectorBranchBasis119 branch) =
      (correctedPREPAmplitude119 taylorOrder branch : ℂ) := by
  fin_cases branch
  · change _ = (Real.sqrt
      (correctedLambda119 taylorOrder ⟨0, by decide⟩ /
        correctedAlpha119 taylorOrder) : ℂ)
    rw [show correctedLambda119 taylorOrder ⟨0, by decide⟩ =
        HistoryBlockEncoding.HistoryLCU.lambda taylorOrder 1 ⟨0, by decide⟩ by rfl,
      correctedAlpha_eq_selector_at_one119]
    exact selectorLocalOperator119_lambda_zero taylorOrder
      (omega := (1 : ℝ)) (by norm_num)
  · change _ = (Real.sqrt
      (correctedLambda119 taylorOrder ⟨1, by decide⟩ /
        correctedAlpha119 taylorOrder) : ℂ)
    rw [show correctedLambda119 taylorOrder ⟨1, by decide⟩ =
        HistoryBlockEncoding.HistoryLCU.lambda taylorOrder 1 ⟨1, by decide⟩ by rfl,
      correctedAlpha_eq_selector_at_one119]
    exact selectorLocalOperator119_lambda_one taylorOrder
      (omega := (1 : ℝ)) (by norm_num)
  · change _ = (Real.sqrt
      (correctedLambda119 taylorOrder ⟨2, by decide⟩ /
        correctedAlpha119 taylorOrder) : ℂ)
    rw [show correctedLambda119 taylorOrder ⟨2, by decide⟩ =
        HistoryBlockEncoding.HistoryLCU.lambda taylorOrder 1 ⟨2, by decide⟩ by rfl,
      correctedAlpha_eq_selector_at_one119]
    exact selectorLocalOperator119_lambda_two taylorOrder
      (omega := (1 : ℝ)) (by norm_num)
  · change _ = (Real.sqrt
      (correctedLambda119 taylorOrder ⟨3, by decide⟩ /
        correctedAlpha119 taylorOrder) : ℂ)
    rw [show correctedLambda119 taylorOrder ⟨3, by decide⟩ =
        HistoryBlockEncoding.HistoryLCU.lambda taylorOrder 1 ⟨3, by decide⟩ by rfl,
      correctedAlpha_eq_selector_at_one119]
    exact selectorLocalOperator119_lambda_three taylorOrder
      (omega := (1 : ℝ))

end

end ExecutableHistoryExecutableHistory
