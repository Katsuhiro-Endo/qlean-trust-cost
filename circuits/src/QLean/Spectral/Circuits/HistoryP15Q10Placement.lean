import QLean.Spectral.Circuits.HistoryP15PreQ10Clean
import QLean.Spectral.Circuits.HistoryTaylorQ10CleanLink

/-!
# Constructive P15/Q10 placement checkpoint

This module constructs the exact controlled-Q10 placement and its two clean
compiler-work wires from the frozen `HistoryBlockLayout`.  The only additional
input is the mathematical width bridge to the generic Q parameters.  No
operator, circuit, or component existence is assumed.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

private def historyP15Q10PlacedWires
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    List (Fin qubits) :=
  historyRegisterWires layout.generatorSignal ++
    historyRegisterWires (historyGeneratorWorkRegister layout) ++
    historyRegisterWires layout.data

private theorem historyP15GeneratorWork_ne_controlledWork
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (generatorIndex : Fin generatorWorkWidth) (workIndex : Fin 2) :
    (historyGeneratorWorkRegister layout).wire generatorIndex ≠
      (historyControlledWork layout).wire workIndex := by
  intro equal
  unfold historyGeneratorWorkRegister historyControlledWork
    historyWorkspaceSlice at equal
  have indexEqual := layout.workspace.injective equal
  have rawValuesEqual := congrArg Fin.val indexEqual
  have valuesEqual : generatorIndex.val =
      historySharedPoolWidth parameters generatorWorkWidth + workIndex.val := by
    simpa only [Nat.zero_add] using rawValuesEqual
  have generatorFits := Nat.le_max_left generatorWorkWidth
    (historyStructuralPoolWidth parameters)
  unfold historySharedPoolWidth at valuesEqual
  omega

private theorem historyP15ControlledWork_ne_active
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (workIndex : Fin 2) :
    (historyControlledWork layout).wire workIndex ≠ historyActiveWire layout := by
  intro equal
  unfold historyControlledWork historyActiveWire historyWorkspaceSlice at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  change historySharedPoolWidth parameters generatorWorkWidth + workIndex.val =
    historySharedPoolWidth parameters generatorWorkWidth + 5 at valuesEqual
  omega

private theorem historyP15GeneratorWork_ne_active
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (generatorIndex : Fin generatorWorkWidth) :
    (historyGeneratorWorkRegister layout).wire generatorIndex ≠
      historyActiveWire layout := by
  intro equal
  unfold historyGeneratorWorkRegister historyActiveWire
    historyWorkspaceSlice at equal
  have indexEqual := layout.workspace.injective equal
  have rawValuesEqual := congrArg Fin.val indexEqual
  have valuesEqual : generatorIndex.val =
      historySharedPoolWidth parameters generatorWorkWidth + 5 := by
    simpa only [Fin.val_zero, Nat.zero_add, Nat.add_zero] using rawValuesEqual
  have generatorFits := Nat.le_max_left generatorWorkWidth
    (historyStructuralPoolWidth parameters)
  unfold historySharedPoolWidth at valuesEqual
  omega

private structure HistoryP15Q10LayoutFacts
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  placedNodup : (historyP15Q10PlacedWires layout).Nodup
  activeOutside : historyActiveWire layout ∉ historyP15Q10PlacedWires layout
  controlledOutside : ∀ index : Fin 2,
    (historyControlledWork layout).wire index ∉ historyP15Q10PlacedWires layout
  controlled_ne_active : ∀ index : Fin 2,
    (historyControlledWork layout).wire index ≠ historyActiveWire layout

private theorem historyP15Q10LayoutFacts_of_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    HistoryP15Q10LayoutFacts layout := by
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
      reservedWires, workspaceWires, List.append_assoc] using
      layout.allWiresNodup
  have selectorSplit := List.nodup_append.mp normalized
  have dataSplit := List.nodup_append.mp selectorSplit.2.1
  have clockSplit := List.nodup_append.mp dataSplit.2.1
  have orderSplit := List.nodup_append.mp clockSplit.2.1
  have generatorSplit := List.nodup_append.mp orderSplit.2.1
  have dataGeneratorSeparated :
      ∀ data ∈ dataWires, ∀ generator ∈ generatorWires,
        data ≠ generator := by
    intro data dataMember generator generatorMember
    exact dataSplit.2.2 data dataMember generator (by simp [generatorMember])
  have dataWorkspaceSeparated :
      ∀ data ∈ dataWires, ∀ workspace ∈ workspaceWires,
        data ≠ workspace := by
    intro data dataMember workspace workspaceMember
    exact dataSplit.2.2 data dataMember workspace (by simp [workspaceMember])
  have generatorWorkspaceSeparated :
      ∀ generator ∈ generatorWires, ∀ workspace ∈ workspaceWires,
        generator ≠ workspace := by
    intro generator generatorMember workspace workspaceMember
    exact generatorSplit.2.2 generator generatorMember workspace
      (by simp [workspaceMember])
  have generatorWorkMemberWorkspace : ∀ wire,
      wire ∈ historyRegisterWires (historyGeneratorWorkRegister layout) →
        wire ∈ workspaceWires := by
    intro wire member
    simp only [historyRegisterWires, List.mem_ofFn] at member
    rcases member with ⟨index, rfl⟩
    exact historyGeneratorWorkRegister_wire_mem_workspace layout index
  have activeMemberWorkspace : historyActiveWire layout ∈ workspaceWires :=
    historyActiveWire_mem_workspace layout
  have controlledMemberWorkspace : ∀ index : Fin 2,
      (historyControlledWork layout).wire index ∈ workspaceWires := by
    intro index
    exact historyControlledWork_wire_mem_workspace layout index
  refine {
    placedNodup := ?_
    activeOutside := ?_
    controlledOutside := ?_
    controlled_ne_active := historyP15ControlledWork_ne_active layout }
  · unfold historyP15Q10PlacedWires
    apply List.nodup_append.mpr
    refine ⟨?_, dataSplit.1, ?_⟩
    · apply List.nodup_append.mpr
      refine ⟨generatorSplit.1, historyRegisterWires_nodup _, ?_⟩
      intro generator generatorMember work workMember
      exact generatorWorkspaceSeparated generator generatorMember work
        (generatorWorkMemberWorkspace work workMember)
    · intro wire prefixMember data dataMember
      rcases List.mem_append.mp prefixMember with generatorMember | workMember
      · exact (dataGeneratorSeparated data dataMember wire generatorMember).symm
      · exact (dataWorkspaceSeparated data dataMember wire
          (generatorWorkMemberWorkspace wire workMember)).symm
  · intro member
    unfold historyP15Q10PlacedWires at member
    rcases List.mem_append.mp member with prefixMember | dataMember
    · rcases List.mem_append.mp prefixMember with generatorMember | workMember
      · exact generatorWorkspaceSeparated _ generatorMember _
          activeMemberWorkspace rfl
      · simp only [historyRegisterWires, List.mem_ofFn] at workMember
        rcases workMember with ⟨index, equal⟩
        exact historyP15GeneratorWork_ne_active layout index (equal.trans rfl)
    · exact dataWorkspaceSeparated _ dataMember _ activeMemberWorkspace rfl
  · intro workIndex member
    unfold historyP15Q10PlacedWires at member
    rcases List.mem_append.mp member with prefixMember | dataMember
    · rcases List.mem_append.mp prefixMember with generatorMember |
        generatorWorkMember
      · exact generatorWorkspaceSeparated _ generatorMember _
          (controlledMemberWorkspace workIndex) rfl
      · simp only [historyRegisterWires, List.mem_ofFn] at generatorWorkMember
        rcases generatorWorkMember with ⟨generatorIndex, equal⟩
        exact historyP15GeneratorWork_ne_controlledWork layout generatorIndex
          workIndex (equal.trans rfl)
    · exact dataWorkspaceSeparated _ dataMember _
        (controlledMemberWorkspace workIndex) rfl

/-- The exact Q placement constructed from the frozen history register order. -/
noncomputable def historyP15Q10PlacementEvidence_ofFrozenLayout
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    HistoryTaylorQ10PlacementEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p := by
  let facts := historyP15Q10LayoutFacts_of_nodup layout
  let wires := historyP15Q10PlacedWires layout
  have length_eq : wires.length = p.ancillaWidth + p.systemWidth := by
    simpa [wires, historyP15Q10PlacedWires, historyRegisterWires,
      Nat.add_assoc] using
      widths.sourceWidth_eq.symm
  let placement : Fin (p.ancillaWidth + p.systemWidth) ↪ Fin qubits :=
    wireEmbeddingOfNodupList wires length_eq facts.placedNodup
  refine {
    widths := widths
    signal := layout.generatorSignal
    generatorWork := historyGeneratorWorkRegister layout
    data := layout.data
    activeWire := historyActiveWire layout
    compilerWork := historyControlledWork layout
    embedding := { placement := placement }
    placement_sourceOrder := ?_
    control_ne_placed := ?_ }
  · change List.ofFn placement = wires
    exact wireEmbeddingOfNodupList_ofFn wires length_eq facts.placedNodup
  · intro source equal
    apply facts.activeOutside
    have member : placement source ∈ List.ofFn placement := by
      simp only [List.mem_ofFn]
      exact ⟨source, rfl⟩
    rw [wireEmbeddingOfNodupList_ofFn wires length_eq facts.placedNodup] at member
    rw [equal]
    exact member

set_option maxHeartbeats 800000 in
theorem historyP15Q10PlacementEvidence_sourceOrder
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    List.ofFn
        (historyP15Q10PlacementEvidence_ofFrozenLayout
          (layout := layout) widths).embedding.placement =
      historyP15Q10PlacedWires layout := by
  exact (historyP15Q10PlacementEvidence_ofFrozenLayout
    (layout := layout) widths).placement_sourceOrder

/-- The two compiler-work wires and the external control are also derived from
the frozen history layout; no clean Q10 component is supplied as data. -/
noncomputable def historyP15Q10ControlEvidence_ofFrozenLayout
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    HistoryTaylorQ10ControlEvidence
      (qubits := qubits) (generatorSignalWidth := generatorSignalWidth)
      (generatorWorkWidth := generatorWorkWidth) (dataWidth := dataWidth) p := by
  let facts := historyP15Q10LayoutFacts_of_nodup layout
  let placement := historyP15Q10PlacementEvidence_ofFrozenLayout
    (layout := layout) widths
  refine {
    placement := placement
    cleanWorkValid := {
      work₀ := (historyControlledWork layout).wire 0
      work₁ := (historyControlledWork layout).wire 1
      controlWork_eq := by
        simp [placement, historyP15Q10PlacementEvidence_ofFrozenLayout,
          HistoryTaylorQ10PlacementEvidence.externalLayout,
          historyTaylorQ10RegisterWires]
      work₀_ne_control := facts.controlled_ne_active 0
      work₁_ne_control := facts.controlled_ne_active 1
      work₀_ne_work₁ := by
        intro equal
        have indexEqual := (historyControlledWork layout).injective equal
        exact Fin.zero_ne_one indexEqual
      work₀_ne_placed := by
        intro source equal
        apply facts.controlledOutside 0
        have member : placement.embedding.placement source ∈
            historyP15Q10PlacedWires layout := by
          rw [← historyP15Q10PlacementEvidence_sourceOrder
            (layout := layout) widths]
          simp only [List.mem_ofFn]
          exact ⟨source, rfl⟩
        exact equal.symm ▸ member
      work₁_ne_placed := by
        intro source equal
        apply facts.controlledOutside 1
        have member : placement.embedding.placement source ∈
            historyP15Q10PlacedWires layout := by
          rw [← historyP15Q10PlacementEvidence_sourceOrder
            (layout := layout) widths]
          simp only [List.mem_ofFn]
          exact ⟨source, rfl⟩
        exact equal.symm ▸ member } }

theorem historyP15Q10Placement_sourceOrder
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    let evidence := historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths
    List.ofFn evidence.placement.embedding.placement =
      historyRegisterWires layout.generatorSignal ++
        historyRegisterWires (historyGeneratorWorkRegister layout) ++
        historyRegisterWires layout.data := by
  exact historyP15Q10PlacementEvidence_sourceOrder (layout := layout) widths

theorem historyP15Q10Placement_compilerWork
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    {p : ProbabilityGeneratorQProof.QParameters}
    {layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters}
    (widths :
      ProbabilityGeneratorQProof.QParameters.ProbabilityGeneratorCanonicalPlacementWidths
        p generatorSignalWidth generatorWorkWidth dataWidth) :
    (historyP15Q10ControlEvidence_ofFrozenLayout
      (layout := layout) widths).placement.externalLayout.controlWork =
        historyRegisterWires (historyControlledWork layout) := by
  rfl

end

end SpectralSamplingProof.Components
