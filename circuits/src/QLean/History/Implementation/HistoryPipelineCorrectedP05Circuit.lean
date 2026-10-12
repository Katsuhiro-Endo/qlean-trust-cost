import QLean.History.Implementation.HistoryPipelineCorrectedLCU
import QLean.History.Implementation.HistoryPipelineRepairedH3

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

/-- Selector angles for the sound LCU weights `(1, 1, sqrt (t+1), 0)`.
The existing selector preparation realizes these weights by specializing its
old `omega` parameter to one. -/
def correctedSelectorHighAngleExpr119 (source : AlignedCommonSource119) :
    VerifiedCircuitCore.AngleExpr :=
  CanonicalHistoryAdapter.compileScientificAngle
    (selectorHighScientific119 source.historyParameters.taylorOrder 1)

def correctedSelectorLowAngleExpr119 : VerifiedCircuitCore.AngleExpr :=
  CanonicalHistoryAdapter.compileScientificAngle
    (selectorLowScientific119 1)

theorem correctedSelectorHighAngleExpr119_value
    (source : AlignedCommonSource119) :
    (correctedSelectorHighAngleExpr119 source).uniformValue =
      selectorHighAngle119 source.historyParameters.taylorOrder 1 := by
  simpa [correctedSelectorHighAngleExpr119] using
    (compile_selectorHighScientific119_value
      source.historyParameters.taylorOrder (1 : ℚ))

theorem correctedSelectorLowAngleExpr119_value :
    correctedSelectorLowAngleExpr119.uniformValue = selectorLowAngle119 1 := by
  simpa [correctedSelectorLowAngleExpr119] using
    (compile_selectorLowScientific119_value (1 : ℚ))

noncomputable def correctedSelectorParameters119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  historySelectorPreparationParametersAtLayout
    (ExecutableLayout119 source domain)
    (correctedSelectorHighAngleExpr119 source)
    correctedSelectorLowAngleExpr119
    correctedSelectorLowAngleExpr119

/-- The independent corrected-H4 specification using the sound selector and
Taylor coefficient angles. -/
noncomputable def correctedH4Specification119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  historyH4CorrectedConcreteSpecification
    (ExecutableLayout119 source domain)
    (ScientificWidthGenericContract.correctedCleanEvidence259
      (ExecutableRaw119 source) (ExecutableAdmissible119 source domain))
    (ExecutableAdmissible119 source domain).placementWidths
    (fun index => correctedTaylorCoefficientAngle119
      source.toCommonSource119 index.val)
    compiledIdleCoefficientAngle119
    (correctedSelectorHighAngleExpr119 source)
    correctedSelectorLowAngleExpr119
    correctedSelectorLowAngleExpr119
    (ExecutableClockEvidence119 source domain)

private noncomputable def correctedH3FromP15ToTop119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols
        (qubits := (ExecutableRaw119 source).history.qubits) internalZeroSymbolEnvironment) where
  circuit := (repairedH3Component119 source domain).circuit
  target := (repairedH3Component119 source domain).target
  inputSubspace := SubspaceMapComponent.basisSpan
    (historyP15FullCleanOutputPredicate
      (layout := ExecutableLayout119 source domain)
      (ExecutableAdmissible119 source domain).placementWidths)
  outputSubspace := ⊤
  correct := by
    intro state _
    rw [(repairedH3Component119 source domain).correct]
  target_maps := by
    intro _ _
    exact Submodule.mem_top

/-- The inverse is built from the same two concrete P50 children as the
corrected forward H1, so PREP and UNPREP are definitionally paired. -/
private noncomputable def correctedSelectorInverseTop119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols
        (qubits := (ExecutableRaw119 source).history.qubits) internalZeroSymbolEnvironment) :=
  let parameters := correctedSelectorParameters119 source domain
  let child := historySelectorPreparationFromP50InverseExactComponent
    (historySelectorPreparationConcreteP50Children internalZeroSymbolEnvironment parameters)
  {
    circuit := child.circuit
    target := child.target
    inputSubspace := ⊤
    outputSubspace := ⊤
    correct := by
      intro state _
      rw [child.correct]
    target_maps := by
      intro _ _
      exact Submodule.mem_top
  }

/-- Actual PrimitiveGate children in source order:
corrected H1; corrected clean P15/H2; repaired H3; the matching H1 inverse. -/
noncomputable def correctedP05Components119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    List (SubspaceMapComponent
      (primitiveGateOperatorWithSymbols
        (qubits := (ExecutableRaw119 source).history.qubits) internalZeroSymbolEnvironment)) :=
  let layout := ExecutableLayout119 source domain
  let clean := ScientificWidthGenericContract.correctedCleanEvidence259
    (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)
  let widths := (ExecutableAdmissible119 source domain).placementWidths
  let clock := ExecutableClockEvidence119 source domain
  [historyH4CorrectedSelectorForwardComponent layout clean widths
      (fun index => correctedTaylorCoefficientAngle119
        source.toCommonSource119 index.val)
      compiledIdleCoefficientAngle119
      (correctedSelectorHighAngleExpr119 source)
      correctedSelectorLowAngleExpr119 correctedSelectorLowAngleExpr119 clock,
   historyP15FullCleanH2Component layout clean widths
      (fun index => correctedTaylorCoefficientAngle119
        source.toCommonSource119 index.val)
      compiledIdleCoefficientAngle119,
   correctedH3FromP15ToTop119 source domain,
   correctedSelectorInverseTop119 source domain]

theorem correctedP05Components119_chain
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    SubspaceMapComponent.SpaceChain
      (correctedP05Components119 source domain)
      (SubspaceMapComponent.basisSpan
        (h4CorrectedIdealInputPredicate
          (correctedH4Specification119 source domain))) ⊤ := by
  unfold correctedP05Components119 correctedH3FromP15ToTop119
    correctedSelectorInverseTop119 correctedH4Specification119
  exact .cons _ [_, _, _] _ _ _ rfl rfl
    (.cons _ [_, _] _ _ _ rfl rfl
      (.cons _ [_] _ _ _ rfl rfl
        (.cons _ [] _ _ _ rfl rfl (.nil _))))

/-- Sound repaired P05 assembled only from actual PrimitiveGate children and
their independently verified targets. -/
noncomputable def correctedP05Component119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  SubspaceMapComponent.sequenceAlong
    (correctedP05Components119_chain source domain)

theorem correctedP05Component119_source_order
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (correctedP05Component119 source domain).circuit =
      VerifiedCircuitCore.Circuit.sequence
        ((correctedP05Components119 source domain).map
          SubspaceMapComponent.circuit) := by
  rfl

theorem correctedP05Component119_target
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (correctedP05Component119 source domain).target =
      operatorSequence
        ((correctedP05Components119 source domain).map
          SubspaceMapComponent.target) := by
  exact SubspaceMapComponent.sequenceAlong_target _

theorem correctedP05Component119_correct_basisKet
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (input : QubitBasis (ExecutableRaw119 source).history.qubits)
    (inside : h4CorrectedIdealInputPredicate
      (correctedH4Specification119 source domain) input) :
    VerifiedCircuitCore.applyOperator
        (Circuit.denote
          (primitiveGateOperatorWithSymbols
            (qubits := (ExecutableRaw119 source).history.qubits) internalZeroSymbolEnvironment)
          (correctedP05Component119 source domain).circuit)
        (VerifiedCircuitCore.basisKet input) =
      VerifiedCircuitCore.applyOperator (correctedP05Component119 source domain).target
        (VerifiedCircuitCore.basisKet input) := by
  exact (correctedP05Component119 source domain).correct _
    (SubspaceMapComponent.basisKet_mem_basisSpan inside)

end

end ExecutableHistoryExecutableHistory
