import QLean.History.Implementation.HistoryPipelineHistoryCleanInput

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

/-! The accepted clean P15 restores the comparison and active work bits before
returning.  Consequently the old P16/H3 word cannot consume those live bits.
This replacement recomputes the two clock comparisons locally, uses them for
the physical and idle L2 branches, and uncomputes them before incrementing the
clock.  Every child is an actual `PrimitiveGate` compiler component. -/

noncomputable def repairedH3SelectorEquality119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  ClassicalReversibleStage.xorEqualityToConstantMinimumWorkExactComponent
    internalZeroSymbolEnvironment
    (historyRegisterWires (ExecutableLayout119 source domain).selector) [] 2
    (historyBranchWire (ExecutableLayout119 source domain))

noncomputable def repairedH3TimeComparison119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  historyLessThanConstantExactComponent internalZeroSymbolEnvironment
    (((ScientificWidthGenericContract.correctedCleanEvidence259
      (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)).clock
        ).clockTimeLessThan.toSpec)
    source.historyParameters.physicalClocks

noncomputable def repairedH3IdleEndComparison119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  historyLessThanConstantExactComponent internalZeroSymbolEnvironment
    (((ScientificWidthGenericContract.correctedCleanEvidence259
      (ExecutableRaw119 source) (ExecutableAdmissible119 source domain)).clock
        ).clockIdleEndLessThan.toSpec)
    (historyIdleClockEnd source.historyParameters.physicalClocks
      source.historyParameters.taylorOrder
      (ExecutableRaw119 source).history.idlingSteps)

noncomputable def repairedH3ActiveConjunction119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkExactComponent
    internalZeroSymbolEnvironment
    [historyBranchWire (ExecutableLayout119 source domain),
      historyLessThanTimeWire (ExecutableLayout119 source domain)] []
    (historyActiveWire (ExecutableLayout119 source domain))

def h3ConstantBitIndices119 (width constant : Nat) : List (Fin width) :=
  (List.ofFn (fun index : Fin width => index)).filter
    (fun index => constant.testBit index.val)

def repairedH3IdleOrderTargets119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (binaryLabels : Nat) : List (Fin qubits) :=
  (h3ConstantBitIndices119 (historyOrderWidth parameters.taylorOrder)
    (binaryLabels - 1)).map
    layout.order.wire

theorem repairedH3IdleOrderTargets119_mem_order
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (binaryLabels : Nat) (target : Fin qubits)
    (member : target ∈ repairedH3IdleOrderTargets119 layout binaryLabels) :
    target ∈ historyRegisterWires layout.order := by
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  exact List.mem_ofFn.mpr ⟨index, rfl⟩

/-- Source-order idle transformation with the logically required `K-1` XOR,
rather than an all-ones XOR that is sound only when `K` is a power of two. -/
noncomputable def repairedH3IdleTransformOperator119
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (evidence : HistoryIdleTransformEvidence layout)
    (binaryLabels : Nat) (angle : ℝ) :
    VerifiedCircuitCore.Operator (QubitBasis qubits) :=
  let idleConjunction :=
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyIdleFlag layout] []
      (historyActiveWire layout)).analyticOperator
  let orderFinalLabelXor := operatorSequence
    ((repairedH3IdleOrderTargets119 layout binaryLabels).map fun target =>
      reversibleAnalyticCnotOperator (historyActiveWire layout) target)
  operatorSequence [
    reversibleAnalyticCnotOperator
      (historyLessThanIdleEndWire layout) (historyIdleFlag layout),
    reversibleAnalyticCnotOperator
      (historyLessThanTimeWire layout) (historyIdleFlag layout),
    idleConjunction,
    orderFinalLabelXor,
    embedControlledSingleQubitOperator (historyActiveWire layout)
      layout.coefficientSignal evidence.active_ne_coefficient (localRy angle),
    idleConjunction,
    reversibleAnalyticCnotOperator
      (historyLessThanTimeWire layout) (historyIdleFlag layout),
    reversibleAnalyticCnotOperator
      (historyLessThanIdleEndWire layout) (historyIdleFlag layout)]

/-- The idle-clock part of `L2` carries the same branch normalization as the
active-clock part.  Thus its clean coefficient amplitude is
`-(sqrt (taylorOrder + 1))⁻¹`, rather than the legacy amplitude `-1`. -/
def repairedH3IdleScientific119
    (source : AlignedCommonSource119) : ScientificAngleExpr :=
  .mul (scientificNat119 2)
    (.acos (.neg (.div (scientificNat119 1)
      (.sqrt (scientificNat119
        (source.historyParameters.taylorOrder + 1))))))

/-- Closed finite syntax for the repaired idle-branch normalization. -/
def repairedH3IdleAngle119
    (source : AlignedCommonSource119) : VerifiedCircuitCore.AngleExpr :=
  CanonicalHistoryAdapter.compileScientificAngle
    (repairedH3IdleScientific119 source)

theorem repairedH3IdleAngle119_value
    (source : AlignedCommonSource119) :
    (repairedH3IdleAngle119 source).uniformValue =
      2 * Real.arccos (-(Real.sqrt
        (source.historyParameters.taylorOrder + 1))⁻¹) := by
  simp [repairedH3IdleAngle119, repairedH3IdleScientific119,
    scientificNat119, CanonicalHistoryAdapter.compileScientificAngle,
    VerifiedCircuitCore.AngleExpr.uniformValue,
    VerifiedCircuitCore.AngleExpr.eval]

theorem repairedH3Idle_clean_amplitude119
    (source : AlignedCommonSource119) :
    cleanSignalAmplitude119 (repairedH3IdleAngle119 source) =
      -(Real.sqrt (source.historyParameters.taylorOrder + 1))⁻¹ := by
  have orderPositive :
      (0 : ℝ) < source.historyParameters.taylorOrder + 1 := by
    exact_mod_cast Nat.succ_pos source.historyParameters.taylorOrder
  have sqrtPositive :
      0 < Real.sqrt (source.historyParameters.taylorOrder + 1) :=
    Real.sqrt_pos.2 orderPositive
  have sqrtOne :
      (1 : ℝ) ≤ Real.sqrt
        (source.historyParameters.taylorOrder + 1) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast Nat.succ_le_succ
      (Nat.zero_le source.historyParameters.taylorOrder)
  have inverseNonnegative :
      0 ≤ (Real.sqrt
        (source.historyParameters.taylorOrder + 1))⁻¹ :=
    le_of_lt (inv_pos.2 sqrtPositive)
  have inverseLeOne :
      (Real.sqrt
        (source.historyParameters.taylorOrder + 1))⁻¹ ≤ 1 := by
    exact (inv_le_one₀ sqrtPositive).2 sqrtOne
  have lower :
      (-1 : ℝ) ≤ -(Real.sqrt
        (source.historyParameters.taylorOrder + 1))⁻¹ := by
    exact neg_le_neg inverseLeOne
  have upper :
      -(Real.sqrt
        (source.historyParameters.taylorOrder + 1))⁻¹ ≤ 1 := by
    exact le_trans (neg_nonpos.mpr inverseNonnegative) (by norm_num)
  unfold cleanSignalAmplitude119
  rw [repairedH3IdleAngle119_value]
  rw [show (2 * Real.arccos (-(Real.sqrt
      (source.historyParameters.taylorOrder + 1))⁻¹)) / 2 =
      Real.arccos (-(Real.sqrt
        (source.historyParameters.taylorOrder + 1))⁻¹) by ring]
  exact Real.cos_arccos lower upper

noncomputable def repairedH3IdleTransform119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).idleTransform
  let idleEndToggle := historyCnotExactComponent (fun _ => 0)
    (historyLessThanIdleEndWire layout) (historyIdleFlag layout)
    evidence.idleEnd_ne_idle
  let timeToggle := historyCnotExactComponent (fun _ => 0)
    (historyLessThanTimeWire layout) (historyIdleFlag layout)
    evidence.time_ne_idle
  let idleConjunction :=
    ClassicalReversibleStage.xorConjunctionMinimumWorkExactComponent (fun _ => 0)
      [historyBranchWire layout, historyIdleFlag layout] []
      (historyActiveWire layout)
  let orderFinalLabelXor := ExactOperatorComponent.sequence
    ((repairedH3IdleOrderTargets119 layout
      source.historyParameters.binaryLabels).attach.map fun target =>
      historyCnotExactComponent (fun _ => 0) (historyActiveWire layout)
        target.1 (evidence.active_ne_order target.1
          (repairedH3IdleOrderTargets119_mem_order layout
            source.historyParameters.binaryLabels target.1 target.2)))
  let coefficientRotation := historyClockCoefficientRotationNormalizedStageComponent
    (historyActiveWire layout) layout.coefficientSignal
    evidence.active_ne_coefficient (repairedH3IdleAngle119 source)
  ExactOperatorComponent.sequence [
    idleEndToggle, timeToggle, idleConjunction, orderFinalLabelXor,
    coefficientRotation, idleConjunction, timeToggle, idleEndToggle]

theorem repairedH3IdleTransform119_target
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (repairedH3IdleTransform119 source domain).target =
      repairedH3IdleTransformOperator119
        (ExecutableLayout119 source domain)
        (ExecutableClockEvidence119 source domain).idleTransform
        source.historyParameters.binaryLabels
        (repairedH3IdleAngle119 source).uniformValue := by
  let layout := ExecutableLayout119 source domain
  let evidence := (ExecutableClockEvidence119 source domain).idleTransform
  let conjunctionStage :=
    ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyIdleFlag layout] []
      (historyActiveWire layout)
  have conjunctionTarget :
      (ClassicalReversibleStage.xorConjunctionMinimumWorkExactComponent
        (fun _ => 0) [historyBranchWire layout, historyIdleFlag layout] []
        (historyActiveWire layout)).target =
        conjunctionStage.analyticOperator :=
    ClassicalReversibleStage.primitiveExactOperatorComponent_target
      (fun _ => 0) conjunctionStage
  have orderTarget :
      (ExactOperatorComponent.sequence
        ((repairedH3IdleOrderTargets119 layout
          source.historyParameters.binaryLabels).attach.map fun target =>
          historyCnotExactComponent (fun _ => 0) (historyActiveWire layout)
            target.1 (evidence.active_ne_order target.1
              (repairedH3IdleOrderTargets119_mem_order layout
                source.historyParameters.binaryLabels target.1 target.2)))).target =
        operatorSequence
          ((repairedH3IdleOrderTargets119 layout
            source.historyParameters.binaryLabels).map fun target =>
            reversibleAnalyticCnotOperator (historyActiveWire layout) target) := by
    rw [ExactOperatorComponent.sequence_target_eq_operatorSequence]
    apply congrArg operatorSequence
    simp [historyCnotExactComponent]
  unfold repairedH3IdleTransform119
  rw [ExactOperatorComponent.sequence_target_eq_operatorSequence]
  simp only [List.map_cons, List.map_nil]
  rw [conjunctionTarget, orderTarget]
  unfold repairedH3IdleTransformOperator119
  rfl

/-- The active-clock `L2` branch carries a minus sign.  The accepted P16
evidence still exposes the legacy coefficient-zero angle, whose clean amplitude
is `-omegaH`; that is the wrong normalization for the corrected `L2` branch.
Use the independently compiled `2*pi` rotation, so a clean coefficient signal
acquires amplitude `-1`. -/
noncomputable def repairedH3CoefficientRotation119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :=
  historyClockCoefficientRotationExactComponent
    (historyActiveWire (ExecutableLayout119 source domain))
    (ExecutableLayout119 source domain).coefficientSignal
    (ExecutableClockEvidence119 source domain).coefficientControl_ne_signal
    compiledIdleCoefficientAngle119

noncomputable def repairedH3Components119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    List (VerifiedCircuitCore.ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := (ExecutableRaw119 source).history.qubits)
        internalZeroSymbolEnvironment)) :=
  let layout := ExecutableLayout119 source domain
  let clock := ExecutableClockEvidence119 source domain
  [repairedH3SelectorEquality119 source domain,
   repairedH3TimeComparison119 source domain,
   repairedH3IdleEndComparison119 source domain,
   repairedH3ActiveConjunction119 source domain,
   historyOrderUniformPreparationInverseExactComponent
      layout clock.uniformExternalControl,
   repairedH3ActiveConjunction119 source domain,
   repairedH3IdleTransform119 source domain,
   repairedH3ActiveConjunction119 source domain,
   repairedH3CoefficientRotation119 source domain,
   repairedH3ActiveConjunction119 source domain,
   repairedH3IdleEndComparison119 source domain,
   repairedH3TimeComparison119 source domain,
   historyProjectorControlExactComponent internalZeroSymbolEnvironment
      layout clock.projectorControl,
   historyControlledClockIncrementExactComponent internalZeroSymbolEnvironment
      layout clock.controlledIncrement,
   repairedH3SelectorEquality119 source domain]

noncomputable def repairedH3Component119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    VerifiedCircuitCore.ExactOperatorComponent
      (primitiveGateOperatorWithSymbols (qubits := (ExecutableRaw119 source).history.qubits)
        internalZeroSymbolEnvironment) :=
  VerifiedCircuitCore.ExactOperatorComponent.sequence
    (repairedH3Components119 source domain)

noncomputable def repairedH3RecordedTarget119
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    VerifiedCircuitCore.Operator
      (QubitBasis (ExecutableRaw119 source).history.qubits) :=
  operatorSequence
    ((repairedH3Components119 source domain).map
      VerifiedCircuitCore.ExactOperatorComponent.target)

theorem repairedH3SelectorEquality119_target
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (repairedH3SelectorEquality119 source domain).target =
      (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
        (historyRegisterWires (ExecutableLayout119 source domain).selector) [] 2
        (historyBranchWire (ExecutableLayout119 source domain))).analyticOperator := by
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_target _ _

theorem repairedH3ActiveConjunction119_target
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (repairedH3ActiveConjunction119 source domain).target =
      (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
        [historyBranchWire (ExecutableLayout119 source domain),
          historyLessThanTimeWire (ExecutableLayout119 source domain)] []
        (historyActiveWire (ExecutableLayout119 source domain))).analyticOperator := by
  exact ClassicalReversibleStage.primitiveExactOperatorComponent_target _ _

theorem repairedH3CoefficientRotation119_target
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (repairedH3CoefficientRotation119 source domain).target =
      embedControlledSingleQubitOperator
        (historyActiveWire (ExecutableLayout119 source domain))
        (ExecutableLayout119 source domain).coefficientSignal
        (ExecutableClockEvidence119 source domain).coefficientControl_ne_signal
        (localRy compiledIdleCoefficientAngle119.uniformValue) := by
  rfl

theorem repairedH3Component119_target
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (repairedH3Component119 source domain).target =
      repairedH3RecordedTarget119 source domain := by
  unfold repairedH3Component119 repairedH3RecordedTarget119
  exact VerifiedCircuitCore.ExactOperatorComponent.sequence_target_eq_operatorSequence
    (repairedH3Components119 source domain)

theorem repairedH3Component119_source_order
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (repairedH3Component119 source domain).circuit =
      VerifiedCircuitCore.Circuit.sequence
        ((repairedH3Components119 source domain).map
          VerifiedCircuitCore.ExactOperatorComponent.circuit) := by
  rfl

end
end ExecutableHistoryExecutableHistory
