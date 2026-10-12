import QLean.Spectral.Circuits.HistoryP15Q10Placement

/-!
# P15 pre-Q10 preservation of the concrete Q10 input boundary

The four actual P15 auxiliary circuits are rebuilt with the conjunction of
their history-phase predicate and the concrete placed Q10 all-zero predicate.
The proof uses only the frozen layout, the already-constructed placement, and
the direct XOR actions of the four compiled children.  No parent component or
QSP witness is assumed.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

private def historyP15Q10PhysicalPlacedWires
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    List (Fin qubits) :=
  historyRegisterWires layout.generatorSignal ++
    historyRegisterWires (historyGeneratorWorkRegister layout) ++
    historyRegisterWires layout.data

private theorem historyP15GeneratorWork_ne_liveWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (generatorIndex : Fin generatorWorkWidth) (wire : Fin qubits)
    (live : wire ∈ historyTaylorBeforeGeneratorLiveWires layout) :
    (historyGeneratorWorkRegister layout).wire generatorIndex ≠ wire := by
  simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
    List.not_mem_nil, or_false] at live
  rcases live with rfl | rfl | rfl | rfl
  · intro equal
    unfold historyGeneratorWorkRegister historyBranchWire historyWorkspaceSlice at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    simp only [Fin.val_zero, Nat.zero_add, Nat.add_zero] at valuesEqual
    have generatorFits := Nat.le_max_left generatorWorkWidth
      (historyStructuralPoolWidth parameters)
    unfold historySharedPoolWidth at valuesEqual
    omega
  · intro equal
    unfold historyGeneratorWorkRegister historyLessThanTimeWire
      historyWorkspaceSlice at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    simp only [Fin.val_zero, Nat.zero_add, Nat.add_zero] at valuesEqual
    have generatorFits := Nat.le_max_left generatorWorkWidth
      (historyStructuralPoolWidth parameters)
    unfold historySharedPoolWidth at valuesEqual
    omega
  · intro equal
    unfold historyGeneratorWorkRegister historyLessThanIdleEndWire
      historyWorkspaceSlice at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    simp only [Fin.val_zero, Nat.zero_add, Nat.add_zero] at valuesEqual
    have generatorFits := Nat.le_max_left generatorWorkWidth
      (historyStructuralPoolWidth parameters)
    unfold historySharedPoolWidth at valuesEqual
    omega
  · intro equal
    unfold historyGeneratorWorkRegister historyActiveWire historyWorkspaceSlice at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    simp only [Fin.val_zero, Nat.zero_add, Nat.add_zero] at valuesEqual
    have generatorFits := Nat.le_max_left generatorWorkWidth
      (historyStructuralPoolWidth parameters)
    unfold historySharedPoolWidth at valuesEqual
    omega

private theorem historyP15ControlledWork_ne_liveWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (workIndex : Fin 2) (wire : Fin qubits)
    (live : wire ∈ historyTaylorBeforeGeneratorLiveWires layout) :
    (historyControlledWork layout).wire workIndex ≠ wire := by
  simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
    List.not_mem_nil, or_false] at live
  rcases live with rfl | rfl | rfl | rfl
  · intro equal
    unfold historyControlledWork historyBranchWire historyWorkspaceSlice at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    simp only [Fin.val_zero, Nat.add_zero] at valuesEqual
    omega
  · intro equal
    unfold historyControlledWork historyLessThanTimeWire historyWorkspaceSlice at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    simp only [Fin.val_zero, Nat.add_zero] at valuesEqual
    omega
  · intro equal
    unfold historyControlledWork historyLessThanIdleEndWire
      historyWorkspaceSlice at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    simp only [Fin.val_zero, Nat.add_zero] at valuesEqual
    omega
  · intro equal
    unfold historyControlledWork historyActiveWire historyWorkspaceSlice at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    simp only [Fin.val_zero, Nat.add_zero] at valuesEqual
    omega

private theorem historyP15LiveWire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (wire : Fin qubits)
    (live : wire ∈ historyTaylorBeforeGeneratorLiveWires layout) :
    wire ∈ historyRegisterWires layout.workspace := by
  simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
    List.not_mem_nil, or_false] at live
  rcases live with rfl | rfl | rfl | rfl
  · exact historyBranchWire_mem_workspace layout
  · exact historyLessThanTimeWire_mem_workspace layout
  · exact historyLessThanIdleEndWire_mem_workspace layout
  · exact historyActiveWire_mem_workspace layout

private theorem historyP15LiveWire_outsidePhysicalPlacement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (wire : Fin qubits)
    (live : wire ∈ historyTaylorBeforeGeneratorLiveWires layout) :
    wire ∉ historyP15Q10PhysicalPlacedWires layout := by
  let selectorWires := historyRegisterWires layout.selector
  let dataWires := historyRegisterWires layout.data
  let clockWires := historyRegisterWires layout.clock
  let orderWires := historyRegisterWires layout.order
  let generatorWires := historyRegisterWires layout.generatorSignal
  let reservedWires := [layout.coefficientSignal, layout.orderBoundarySignal,
    layout.projectorSignal, layout.clockBoundarySignal]
  let workspaceWires := historyRegisterWires layout.workspace
  have normalized :
      (selectorWires ++ (dataWires ++ (clockWires ++ (orderWires ++
        (generatorWires ++ (reservedWires ++ workspaceWires)))))).Nodup := by
    simpa [selectorWires, dataWires, clockWires, orderWires, generatorWires,
      reservedWires, workspaceWires, List.append_assoc] using layout.allWiresNodup
  have selectorSplit := List.nodup_append.mp normalized
  have dataSplit := List.nodup_append.mp selectorSplit.2.1
  have clockSplit := List.nodup_append.mp dataSplit.2.1
  have orderSplit := List.nodup_append.mp clockSplit.2.1
  have generatorSplit := List.nodup_append.mp orderSplit.2.1
  have liveWorkspace : wire ∈ workspaceWires := by
    exact historyP15LiveWire_mem_workspace layout wire live
  intro placed
  unfold historyP15Q10PhysicalPlacedWires at placed
  rcases List.mem_append.mp placed with initialMember | dataMember
  · rcases List.mem_append.mp initialMember with generatorMember | workMember
    · exact generatorSplit.2.2 _ generatorMember _ (by simp [liveWorkspace])
        rfl
    · simp only [historyRegisterWires, List.mem_ofFn] at workMember
      rcases workMember with ⟨generatorIndex, equal⟩
      exact historyP15GeneratorWork_ne_liveWire layout generatorIndex wire live
        (equal.trans rfl)
  · exact dataSplit.2.2 _ dataMember _ (by simp [liveWorkspace]) rfl

/-- Every one of the four P15 live targets lies outside the concrete Q10
placement obtained from the same frozen layout. -/
theorem historyP15Q10LiveWire_ne_placement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (wire : Fin qubits)
    (live : wire ∈ historyTaylorBeforeGeneratorLiveWires layout)
    (source : Fin (p.ancillaWidth + p.systemWidth)) :
    wire ≠ (historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths).placement.embedding.placement source := by
  intro equal
  apply historyP15LiveWire_outsidePhysicalPlacement layout wire live
  have member :
      (historyP15Q10ControlEvidence_ofFrozenLayout
        (layout := layout) widths).placement.embedding.placement source ∈
        List.ofFn (historyP15Q10ControlEvidence_ofFrozenLayout
          (layout := layout) widths).placement.embedding.placement := by
    simp only [List.mem_ofFn]
    exact ⟨source, rfl⟩
  rw [historyP15Q10Placement_sourceOrder (layout := layout) widths] at member
  exact equal ▸ member

/-- Every one of the four P15 live targets lies outside both concrete
controlled-compiler work wires. -/
theorem historyP15Q10LiveWire_ne_compilerWork
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (wire : Fin qubits)
    (live : wire ∈ historyTaylorBeforeGeneratorLiveWires layout) :
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    wire ≠ evidence.cleanWorkValid.work₀ ∧
      wire ≠ evidence.cleanWorkValid.work₁ := by
  dsimp only
  constructor
  · change wire ≠ (historyControlledWork layout).wire 0
    exact (historyP15ControlledWork_ne_liveWire layout 0 wire live).symm
  · change wire ≠ (historyControlledWork layout).wire 1
    exact (historyP15ControlledWork_ne_liveWire layout 1 wire live).symm

/-- The concrete Q10 input predicate attached to the frozen H2 placement. -/
def historyP15Q10PlacedInputPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    QubitBasis qubits → Prop :=
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  externallyControlledPlacedInputPredicate evidence.cleanWorkValid
    (ProbabilityGeneratorQProof.q10CanonicalCoreAllZeroInputPredicate p)

/-- A P15 auxiliary XOR preserves the full concrete Q10 input boundary. -/
theorem historyP15Q10PlacedInputPredicate_xorLiveWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (wire : Fin qubits)
    (live : wire ∈ historyTaylorBeforeGeneratorLiveWires layout)
    (value : Bool) (input : QubitBasis qubits)
    (inside : historyP15Q10PlacedInputPredicate
      (layout := layout) widths input) :
    historyP15Q10PlacedInputPredicate (layout := layout) widths
      (xorWire wire value input) := by
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  have compilerDifferent := historyP15Q10LiveWire_ne_compilerWork
    (layout := layout) widths wire live
  unfold historyP15Q10PlacedInputPredicate
    externallyControlledPlacedInputPredicate at inside ⊢
  constructor
  · exact externallyControlledCleanWorkPredicate_xorWire_of_ne
      evidence.cleanWorkValid wire value input inside.1
      compilerDifferent.1 compilerDifferent.2
  · rw [restrictToPlacedWires_xorWire_outside]
    · exact inside.2
    · exact historyP15Q10LiveWire_ne_placement
        (layout := layout) widths wire live

/-- Conjoin an H phase boundary with the placed Q10 all-zero boundary. -/
def historyP15WithQ10Input
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (phase : QubitBasis qubits → Prop) (basis : QubitBasis qubits) : Prop :=
  phase basis ∧ historyP15Q10PlacedInputPredicate (layout := layout) widths basis

noncomputable def historyP15SelectorEqualityWithQ10Component
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  ClassicalReversibleStage.xorEqualityToConstantMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    (historyRegisterWires layout.selector) [] 1
    (historyBranchWire layout) (by simp [historyRegisterWires])
    (historyTaylorSelectorEqualityLayout_nodup layout)
    (historyP15WithQ10Input (layout := layout) widths
      (historyTaylorAuxiliaryBoundaryPredicate layout))
    (historyP15WithQ10Input (layout := layout) widths
      (historyTaylorAfterSelectorPredicate layout))
    (by simp [historyP15WithQ10Input,
      ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input inside
      constructor
      · exact historyTaylorSelectorEqualityBasisAction_maps_phase
          layout input inside.1
      · simpa [ClassicalReversibleStage.equalityToConstantDirectBasisAction] using
          historyP15Q10PlacedInputPredicate_xorLiveWire
            (layout := layout) widths (historyBranchWire layout)
            (by simp [historyTaylorBeforeGeneratorLiveWires])
            (ClassicalReversibleStage.littleEndianRegisterEqualsNat
              (historyRegisterWires layout.selector) 1 input) input inside.2)

noncomputable def historyP15TimeComparisonWithQ10Component
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (preEvidence : HistoryP15PreQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  let comparison := preEvidence.clockTimeLessThan.toSpec
  historyP15LessThanConstantCleanStageBetween comparison parameters.timeSteps
    (historyP15WithQ10Input (layout := layout) widths
      (historyTaylorAfterSelectorPredicate layout))
    (historyP15WithQ10Input (layout := layout) widths
      (historyTaylorAfterTimeComparisonPredicate layout))
    (by
      intro input inside
      have clean := historyTaylorAfterSelectorPredicate_p41Clean
        layout input inside.1
      exact ⟨clean.2, clean.1⟩)
    (by
      intro input inside
      constructor
      · simpa [comparison, HistoryP15LessThanEvidence.toSpec,
          historyTaylorTimeComparisonBasisAction,
          historyTaylorClockLessThanTimeValue,
          historyLessThanConstantDirectBasisAction] using
          historyTaylorTimeComparisonBasisAction_maps_phase layout input inside.1
      · simpa [comparison, HistoryP15LessThanEvidence.toSpec,
          historyLessThanConstantDirectBasisAction] using
          historyP15Q10PlacedInputPredicate_xorLiveWire
            (layout := layout) widths (historyLessThanTimeWire layout)
            (by simp [historyTaylorBeforeGeneratorLiveWires])
            (unsignedLessThanBits
              (comparison.lhs.read input)
              (fun index => parameters.timeSteps.testBit index.val))
            input inside.2)

noncomputable def historyP15IdleEndComparisonWithQ10Component
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (preEvidence : HistoryP15PreQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  let comparison := preEvidence.clockIdleEndLessThan.toSpec
  let constant := historyIdleClockEnd parameters.timeSteps
    parameters.taylorOrder parameters.idlingSteps
  historyP15LessThanConstantCleanStageBetween comparison constant
    (historyP15WithQ10Input (layout := layout) widths
      (historyTaylorAfterTimeComparisonPredicate layout))
    (historyP15WithQ10Input (layout := layout) widths
      (historyTaylorAfterIdleEndComparisonPredicate layout))
    (by
      intro input inside
      have clean := historyTaylorAfterTimeComparisonPredicate_p41Clean
        layout input inside.1
      exact ⟨clean.2, clean.1⟩)
    (by
      intro input inside
      constructor
      · simpa [comparison, constant, HistoryP15LessThanEvidence.toSpec,
          historyTaylorIdleEndComparisonBasisAction,
          historyTaylorClockLessThanIdleEndValue,
          historyLessThanConstantDirectBasisAction] using
          historyTaylorIdleEndComparisonBasisAction_maps_phase layout input inside.1
      · simpa [comparison, constant, HistoryP15LessThanEvidence.toSpec,
          historyLessThanConstantDirectBasisAction] using
          historyP15Q10PlacedInputPredicate_xorLiveWire
            (layout := layout) widths (historyLessThanIdleEndWire layout)
            (by simp [historyTaylorBeforeGeneratorLiveWires])
            (unsignedLessThanBits
              (comparison.lhs.read input)
              (fun index => constant.testBit index.val)) input inside.2)

noncomputable def historyP15ActiveConjunctionWithQ10Component
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  ClassicalReversibleStage.xorConjunctionMinimumWorkCleanSubspaceMapComponentBetween
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
    [historyBranchWire layout, historyLessThanTimeWire layout] []
    (historyActiveWire layout) (by simp)
    (historyTaylorActiveConjunctionLayout_nodup layout)
    (historyP15WithQ10Input (layout := layout) widths
      (historyTaylorAfterIdleEndComparisonPredicate layout))
    (historyP15WithQ10Input (layout := layout) widths
      (historyTaylorBeforeGeneratorBoundaryPredicate layout))
    (by simp [historyP15WithQ10Input,
      ClassicalReversibleStage.minimumWorkCleanPredicate])
    (by
      intro input inside
      constructor
      · exact historyTaylorActiveConjunctionBasisAction_maps_phase
          layout input inside.1
      · simpa [ClassicalReversibleStage.conjunctionDirectBasisAction] using
          historyP15Q10PlacedInputPredicate_xorLiveWire
            (layout := layout) widths (historyActiveWire layout)
            (by simp [historyTaylorBeforeGeneratorLiveWires])
            (ClassicalReversibleStage.allWiresTrue
              [historyBranchWire layout, historyLessThanTimeWire layout] input)
            input inside.2)

def historyP15PreQ10WithInvariantComponents
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (preEvidence : HistoryP15PreQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  [historyP15SelectorEqualityWithQ10Component layout widths,
   historyP15TimeComparisonWithQ10Component layout preEvidence widths,
   historyP15IdleEndComparisonWithQ10Component layout preEvidence widths,
   historyP15ActiveConjunctionWithQ10Component layout widths]

theorem historyP15PreQ10WithInvariantComponents_chain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (preEvidence : HistoryP15PreQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    SubspaceMapComponent.SpaceChain
      (historyP15PreQ10WithInvariantComponents layout preEvidence widths)
      (SubspaceMapComponent.basisSpan
        (historyP15WithQ10Input (layout := layout) widths
          (historyTaylorAuxiliaryBoundaryPredicate layout)))
      (SubspaceMapComponent.basisSpan
        (historyP15WithQ10Input (layout := layout) widths
          (historyTaylorBeforeGeneratorBoundaryPredicate layout))) := by
  exact .cons _ _ _ _ _ rfl rfl
    (.cons _ _ _ _ _ rfl rfl
      (.cons _ _ _ _ _ rfl rfl
        (.cons _ [] _ _ _ rfl rfl (.nil _))))

private structure HistoryP15Q10ReadOnlyFacts
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  placedOutsideSelector : ∀ wire,
    wire ∈ historyP15Q10PhysicalPlacedWires layout →
      wire ∉ historyRegisterWires layout.selector
  placedOutsideClock : ∀ wire,
    wire ∈ historyP15Q10PhysicalPlacedWires layout →
      wire ∉ historyRegisterWires layout.clock
  workspaceOutsidePlaced : ∀ wire,
    wire ∈ historyRegisterWires layout.workspace →
    wire ∉ historyRegisterWires (historyGeneratorWorkRegister layout) →
      wire ∉ historyP15Q10PhysicalPlacedWires layout

private theorem historyP15Q10ReadOnlyFacts_of_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    HistoryP15Q10ReadOnlyFacts layout := by
  let selectorWires := historyRegisterWires layout.selector
  let dataWires := historyRegisterWires layout.data
  let clockWires := historyRegisterWires layout.clock
  let orderWires := historyRegisterWires layout.order
  let generatorWires := historyRegisterWires layout.generatorSignal
  let reservedWires := [layout.coefficientSignal, layout.orderBoundarySignal,
    layout.projectorSignal, layout.clockBoundarySignal]
  let workspaceWires := historyRegisterWires layout.workspace
  have normalized :
      (selectorWires ++ (dataWires ++ (clockWires ++ (orderWires ++
        (generatorWires ++ (reservedWires ++ workspaceWires)))))).Nodup := by
    simpa [selectorWires, dataWires, clockWires, orderWires, generatorWires,
      reservedWires, workspaceWires, List.append_assoc] using layout.allWiresNodup
  have selectorSplit := List.nodup_append.mp normalized
  have dataSplit := List.nodup_append.mp selectorSplit.2.1
  have clockSplit := List.nodup_append.mp dataSplit.2.1
  have orderSplit := List.nodup_append.mp clockSplit.2.1
  have generatorSplit := List.nodup_append.mp orderSplit.2.1
  have generatorWorkMemberWorkspace : ∀ wire,
      wire ∈ historyRegisterWires (historyGeneratorWorkRegister layout) →
        wire ∈ workspaceWires := by
    intro wire member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨index, rfl⟩
    exact historyGeneratorWorkRegister_wire_mem_workspace layout index
  refine {
    placedOutsideSelector := ?_
    placedOutsideClock := ?_
    workspaceOutsidePlaced := ?_ }
  · intro wire placed selectorMember
    have tailMember : wire ∈ dataWires ++ (clockWires ++ (orderWires ++
        (generatorWires ++ (reservedWires ++ workspaceWires)))) := by
      unfold historyP15Q10PhysicalPlacedWires at placed
      rcases List.mem_append.mp placed with initialMember | dataMember
      · rcases List.mem_append.mp initialMember with generatorMember | workMember
        · change wire ∈ generatorWires at generatorMember
          exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr
            (List.mem_append.mpr (.inr
              (List.mem_append.mpr (.inl generatorMember)))))))
        · have workspaceMember := generatorWorkMemberWorkspace wire workMember
          exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr
            (List.mem_append.mpr (.inr (List.mem_append.mpr (.inr
              (List.mem_append.mpr (.inr workspaceMember)))))))))
      · change wire ∈ dataWires at dataMember
        exact List.mem_append.mpr (.inl dataMember)
    exact selectorSplit.2.2 _ selectorMember _ tailMember rfl
  · intro wire placed clockMember
    unfold historyP15Q10PhysicalPlacedWires at placed
    rcases List.mem_append.mp placed with initialMember | dataMember
    · rcases List.mem_append.mp initialMember with generatorMember | workMember
      · change wire ∈ generatorWires at generatorMember
        exact clockSplit.2.2 _ clockMember _
          (by exact List.mem_append.mpr (.inr
            (List.mem_append.mpr (.inl generatorMember)))) rfl
      · have workspaceMember := generatorWorkMemberWorkspace wire workMember
        exact clockSplit.2.2 _ clockMember _
          (by exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr
            (List.mem_append.mpr (.inr workspaceMember)))))) rfl
    · change wire ∈ dataWires at dataMember
      change wire ∈ clockWires at clockMember
      exact dataSplit.2.2 _ dataMember _
        (by exact List.mem_append.mpr (.inl clockMember)) rfl
  · intro wire workspaceMember outsideGeneratorWork placed
    unfold historyP15Q10PhysicalPlacedWires at placed
    rcases List.mem_append.mp placed with initialMember | dataMember
    · rcases List.mem_append.mp initialMember with generatorMember | workMember
      · change wire ∈ generatorWires at generatorMember
        change wire ∈ workspaceWires at workspaceMember
        exact generatorSplit.2.2 _ generatorMember _
          (by exact List.mem_append_right _ workspaceMember) rfl
      · exact outsideGeneratorWork workMember
    · change wire ∈ dataWires at dataMember
      change wire ∈ workspaceWires at workspaceMember
      exact dataSplit.2.2 _ dataMember _
        (by exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr
          (List.mem_append.mpr (.inr
            (List.mem_append.mpr (.inr workspaceMember)))))))) rfl

/-- The live P15 phase boundary is read-only for every operator supported on
the constructed Q10 placement. -/
theorem historyP15BeforeGeneratorPredicate_stableOutsideQ10Placement
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth)
    (input output : QubitBasis qubits)
    (inside : historyTaylorBeforeGeneratorBoundaryPredicate layout input)
    (sameOutside : ∀ wire,
      wire ∉ Finset.univ.image
          (historyP15Q10ControlEvidence_ofFrozenLayout
            (layout := layout) widths).placement.embedding.placement →
        output wire = input wire) :
    historyTaylorBeforeGeneratorBoundaryPredicate layout output := by
  let facts := historyP15Q10ReadOnlyFacts_of_nodup layout
  have outsideOfNotPlaced (wire : Fin qubits)
      (notPlaced : wire ∉ historyP15Q10PhysicalPlacedWires layout) :
      wire ∉ Finset.univ.image
        (historyP15Q10ControlEvidence_ofFrozenLayout
          (layout := layout) widths).placement.embedding.placement := by
    intro member
    rcases Finset.mem_image.mp member with ⟨source, _, rfl⟩
    apply notPlaced
    have placedMember :
        (historyP15Q10ControlEvidence_ofFrozenLayout
          (layout := layout) widths).placement.embedding.placement source ∈
          List.ofFn (historyP15Q10ControlEvidence_ofFrozenLayout
            (layout := layout) widths).placement.embedding.placement := by
      simp only [List.mem_ofFn]
      exact ⟨source, rfl⟩
    rw [historyP15Q10Placement_sourceOrder (layout := layout) widths]
      at placedMember
    exact placedMember
  have selectorSame : ∀ wire,
      wire ∈ historyRegisterWires layout.selector → output wire = input wire := by
    intro wire member
    apply sameOutside wire
    apply outsideOfNotPlaced wire
    exact fun placed => facts.placedOutsideSelector wire placed member
  have clockSame : layout.clock.read output = layout.clock.read input := by
    funext index
    apply sameOutside (layout.clock.wire index)
    apply outsideOfNotPlaced
    exact fun placed => facts.placedOutsideClock _ placed
      (by simp [historyRegisterWires])
  have liveSame : ∀ wire,
      wire ∈ historyTaylorBeforeGeneratorLiveWires layout →
        output wire = input wire := by
    intro wire member
    exact sameOutside wire (outsideOfNotPlaced wire
      (historyP15LiveWire_outsidePhysicalPlacement layout wire member))
  rcases inside with ⟨branch, lessTime, lessIdle, active, remaining⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [liveSame (historyBranchWire layout)
      (by simp [historyTaylorBeforeGeneratorLiveWires]), branch]
    exact (ClassicalReversibleStage.littleEndianRegisterEqualsNat_congr
      (historyRegisterWires layout.selector) 1 output input selectorSame).symm
  · rw [liveSame (historyLessThanTimeWire layout)
      (by simp [historyTaylorBeforeGeneratorLiveWires]), lessTime]
    unfold historyTaylorClockLessThanTimeValue
    exact congrArg
      (fun bits => unsignedLessThanBits bits
        (fun index => parameters.timeSteps.testBit index.val)) clockSame.symm
  · rw [liveSame (historyLessThanIdleEndWire layout)
      (by simp [historyTaylorBeforeGeneratorLiveWires]), lessIdle]
    unfold historyTaylorClockLessThanIdleEndValue
    exact congrArg
      (fun bits => unsignedLessThanBits bits (fun index =>
        (historyIdleClockEnd parameters.timeSteps parameters.taylorOrder
          parameters.idlingSteps).testBit index.val)) clockSame.symm
  · rw [liveSame (historyActiveWire layout)
      (by simp [historyTaylorBeforeGeneratorLiveWires]), active,
      liveSame (historyBranchWire layout)
        (by simp [historyTaylorBeforeGeneratorLiveWires]),
      liveSame (historyLessThanTimeWire layout)
        (by simp [historyTaylorBeforeGeneratorLiveWires])]
  · intro index outside
    have originalZero := remaining index outside
    rw [sameOutside (layout.workspace.wire index), originalZero]
    apply outsideOfNotPlaced
    apply facts.workspaceOutsidePlaced (layout.workspace.wire index)
    · simp [historyRegisterWires]
    · intro generatorMember
      apply outside
      unfold historyTaylorControlledQ10OwnedWorkspaceWires
      exact List.mem_append_right _ (List.mem_append_left _ generatorMember)

/-- The already-green controlled Q10 component, restricted only by the
read-only live P15 phase invariant. -/
noncomputable def historyP15Q10LiveBoundarySubspaceMapComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
    (layout := layout) widths
  let component :=
    historyTaylorControlledProbabilityGeneratorQ10CleanBoundarySubspaceMapComponent
      p evidence
  let inputPredicate := historyP15Q10PlacedInputPredicate
    (layout := layout) widths
  let outputPredicate := externallyControlledPlacedOutputPredicate
    evidence.cleanWorkValid
    (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p)
  component.restrictBasisSpanWithInvariant
    (Finset.univ.image evidence.placement.embedding.placement)
    (by
      rw [historyTaylorControlledProbabilityGeneratorQ10CleanBoundary_target]
      exact ExternallyControlledPrimitivePlan.semanticPlanOperator_preservesOutsidePlacement
          ProbabilityGeneratorQProof.internalZeroSymbolEnvironment
          evidence.placement.externalLayout _)
    inputPredicate outputPredicate
    (historyTaylorBeforeGeneratorBoundaryPredicate layout)
    (by
      intro input inputInside
      rw [(historyTaylorControlledProbabilityGeneratorQ10CleanBoundary_spaces
        p evidence).1]
      exact SubspaceMapComponent.basisKet_mem_basisSpan inputInside)
    (by
      have qSpaces :=
        historyTaylorControlledProbabilityGeneratorQ10CleanBoundary_spaces
          p evidence
      exact And.right qSpaces)
    (historyP15BeforeGeneratorPredicate_stableOutsideQ10Placement
      (layout := layout) widths)

theorem historyP15Q10LiveBoundary_spaces
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    let component := historyP15Q10LiveBoundarySubspaceMapComponent layout widths
    component.inputSubspace = SubspaceMapComponent.basisSpan
        (fun input =>
          historyP15Q10PlacedInputPredicate (layout := layout) widths input ∧
          historyTaylorBeforeGeneratorBoundaryPredicate layout input) ∧
      component.outputSubspace = SubspaceMapComponent.basisSpan
        (fun output =>
          externallyControlledPlacedOutputPredicate evidence.cleanWorkValid
              (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p)
              output ∧
            historyTaylorBeforeGeneratorBoundaryPredicate layout output) := by
  dsimp only
  unfold historyP15Q10LiveBoundarySubspaceMapComponent
  exact SubspaceMapComponent.restrictBasisSpanWithInvariant_spaces
    _ _ _ _ _ _ _ _ _

def historyP15ThroughQ10Components
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (preEvidence : HistoryP15PreQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  historyP15PreQ10WithInvariantComponents layout preEvidence widths ++
    [historyP15Q10LiveBoundarySubspaceMapComponent layout widths]

theorem historyP15ThroughQ10Components_chain
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (preEvidence : HistoryP15PreQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    SubspaceMapComponent.SpaceChain
      (historyP15ThroughQ10Components layout preEvidence widths)
      (SubspaceMapComponent.basisSpan
        (historyP15WithQ10Input (layout := layout) widths
          (historyTaylorAuxiliaryBoundaryPredicate layout)))
      (SubspaceMapComponent.basisSpan
        (fun output =>
          externallyControlledPlacedOutputPredicate evidence.cleanWorkValid
              (ProbabilityGeneratorQProof.q10CanonicalCoreWorkCleanPredicate p)
              output ∧
            historyTaylorBeforeGeneratorBoundaryPredicate layout output)) := by
  dsimp only
  let phase := historyTaylorBeforeGeneratorBoundaryPredicate layout
  let inputPredicate := historyP15Q10PlacedInputPredicate
    (layout := layout) widths
  let middle := SubspaceMapComponent.basisSpan
    (historyP15WithQ10Input (layout := layout) widths phase)
  let rightMiddle := SubspaceMapComponent.basisSpan
    (fun input => inputPredicate input ∧ phase input)
  have middleEq : middle = rightMiddle := by
    apply congrArg SubspaceMapComponent.basisSpan
    funext input
    apply propext
    exact and_comm
  have rightSpaces := historyP15Q10LiveBoundary_spaces layout widths
  have rightChain : SubspaceMapComponent.SpaceChain
      [historyP15Q10LiveBoundarySubspaceMapComponent layout widths]
      middle
      (historyP15Q10LiveBoundarySubspaceMapComponent
        layout widths).outputSubspace := by
    exact .cons _ [] middle _ _
      (rightSpaces.1.trans middleEq.symm) rfl (.nil _)
  have appended := SubspaceMapComponent.SpaceChain.append
    (historyP15PreQ10WithInvariantComponents_chain
      layout preEvidence widths) rightChain
  rw [rightSpaces.2] at appended
  simpa [historyP15ThroughQ10Components] using appended

noncomputable def historyP15ThroughQ10SubspaceMapComponent
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (preEvidence : HistoryP15PreQ10Evidence layout)
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :=
  SubspaceMapComponent.sequenceAlong
    (historyP15ThroughQ10Components_chain layout preEvidence widths)

end

end SpectralSamplingProof.Components
