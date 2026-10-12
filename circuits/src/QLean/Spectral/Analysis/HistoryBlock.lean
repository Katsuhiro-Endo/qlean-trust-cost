import QLean.Spectral.Analysis.R12OperatorDag
import QLean.Circuits.Foundation.ClassicalArithmeticCorrectnessAnalytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkClean
import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic
import QLean.Circuits.Foundation.ControlledConstantAdderAnalytic
import QLean.Circuits.Foundation.Foundations
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.QuantumFourierAnalytic
import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.ReversibleLogicCleanAnalytic
import QLean.Circuits.Foundation.OperatorLocalityAnalytic
import QLean.Circuits.Foundation.UniformPreparationAnalytic

/-! Register layouts, parameters, and independent operator targets
for history block encoding. -/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore
open VerifiedCircuitCore.ClassicalReversibleStage

/-- Python `int.bit_length` と一致する、正のTaylor次数用のorder register幅。 -/
def historyOrderWidth (order : Nat) : Nat :=
  max 1 (Nat.log2 order + 1)

/-- idling blockが使用する全binary order label数。 -/
def historyIdleBlockSize (order : Nat) : Nat :=
  2 ^ historyOrderWidth order

/-- endpoint idling copy数をbinary order block数へ変換する。 -/
def historyIdleClockBlocks (order idlingSteps : Nat) : Nat :=
  (idlingSteps + 1) / historyIdleBlockSize order

/-- physical time clockに続くidling clockの終端。 -/
def historyIdleClockEnd (timeSteps order idlingSteps : Nat) : Nat :=
  timeSteps + historyIdleClockBlocks order idlingSteps

/-- history clock registerの幅。終端直前のlabelを表せる最小の正幅を採る。 -/
def historyClockWidth (timeSteps order idlingSteps : Nat) : Nat :=
  max 1 (Nat.log2 (historyIdleClockEnd timeSteps order idlingSteps - 1) + 1)

/--
P05を規定する数学parameter。実数fieldは解析対象であり、recorded angle列は
`ScientificAngleExpr`として別に保持して自由な浮動小数注入を避ける。
-/
structure HistoryBlockParameters where
  timeSteps : Nat
  taylorOrder : Nat
  idlingSteps : Nat
  historyBlocks : Nat
  timeStepsPositive : 0 < timeSteps
  taylorOrderPositive : 0 < taylorOrder
  idlingFitsBinaryBlocks :
    (idlingSteps + 1) % historyIdleBlockSize taylorOrder = 0
  duration : ℝ
  targetStateError : ℝ
  stepSize : ℝ
  omegaH : ℝ
  historyBlockScale : ℝ
  gTaylor : ℝ
  targetStateErrorPositive : 0 < targetStateError
  stepSizePositive : 0 < stepSize
  omegaHNonnegative : 0 ≤ omegaH
  selectorPreparationAngles : Fin 3 → ScientificAngleExpr
  coefficientAngles : Fin taylorOrder → ScientificAngleExpr
  idleCoefficientAngle : ScientificAngleExpr

/-- register一本を物理wire列として読む。 -/
def historyRegisterWires {qubits width : Nat}
    (register : Register qubits width) : List (Fin qubits) :=
  List.ofFn register.wire

theorem historyRegisterWires_nodup {qubits width : Nat}
    (register : Register qubits width) :
    (historyRegisterWires register).Nodup := by
  exact List.nodup_ofFn.mpr register.injective

/--
P05の型付きregister配置。可変幅signal/data/workをfieldに残し、全registerの
injectivityに加えて相互disjointnessを一つの`Nodup`証拠で固定する。
-/
structure HistoryBlockLayout (qubits dataWidth generatorSignalWidth workspaceWidth : Nat)
    (parameters : HistoryBlockParameters) where
  selector : Register qubits 2
  data : Register qubits dataWidth
  clock : Register qubits
    (historyClockWidth parameters.timeSteps parameters.taylorOrder parameters.idlingSteps)
  order : Register qubits (historyOrderWidth parameters.taylorOrder)
  generatorSignal : Register qubits generatorSignalWidth
  coefficientSignal : Fin qubits
  orderBoundarySignal : Fin qubits
  projectorSignal : Fin qubits
  clockBoundarySignal : Fin qubits
  workspace : Register qubits workspaceWidth
  allWiresNodup :
    (historyRegisterWires selector ++
      historyRegisterWires data ++
      historyRegisterWires clock ++
      historyRegisterWires order ++
      historyRegisterWires generatorSignal ++
      [coefficientSignal, orderBoundarySignal, projectorSignal,
        clockBoundarySignal] ++
      historyRegisterWires workspace).Nodup

/-- Largest binary label width used by the frozen P16 structural arithmetic. -/
def historyMaximumLabelWidth (parameters : HistoryBlockParameters) : Nat :=
  max
    (historyClockWidth parameters.timeSteps parameters.taylorOrder
      parameters.idlingSteps)
    (historyOrderWidth parameters.taylorOrder)

/-- Positive-width Cuccaro tail index for the frozen clock register. -/
def historyClockTailWidth (parameters : HistoryBlockParameters) : Nat :=
  historyClockWidth parameters.timeSteps parameters.taylorOrder
    parameters.idlingSteps - 1

/-- Positive-width Cuccaro tail index for the Taylor order register. -/
def historyOrderTailWidth (parameters : HistoryBlockParameters) : Nat :=
  historyOrderWidth parameters.taylorOrder - 1

/-- The clock width is definitionally positive and therefore is one more than
its Cuccaro tail width. -/
theorem historyClockTailWidth_succ (parameters : HistoryBlockParameters) :
    historyClockTailWidth parameters + 1 =
      historyClockWidth parameters.timeSteps parameters.taylorOrder
        parameters.idlingSteps := by
  unfold historyClockTailWidth historyClockWidth
  omega

theorem historyOrderTailWidth_succ (parameters : HistoryBlockParameters) :
    historyOrderTailWidth parameters + 1 =
      historyOrderWidth parameters.taylorOrder := by
  unfold historyOrderTailWidth historyOrderWidth
  omega

/-- Equality work reserved by the frozen `emit_eq_const` convention. -/
def historyEqualityWorkWidth (parameters : HistoryBlockParameters) : Nat :=
  historyMaximumLabelWidth parameters - 2

/-- Shared structural pool before generator-work aliasing is taken into account. -/
def historyStructuralPoolWidth (parameters : HistoryBlockParameters) : Nat :=
  5 +
    2 * historyClockWidth parameters.timeSteps parameters.taylorOrder
      parameters.idlingSteps +
    historyEqualityWorkWidth parameters +
    2 * historyMaximumLabelWidth parameters

/-- The generator work and structural work alias one pool in the frozen source. -/
def historySharedPoolWidth (parameters : HistoryBlockParameters)
    (generatorWorkWidth : Nat) : Nat :=
  max generatorWorkWidth (historyStructuralPoolWidth parameters)

/-- Shared pool, two controlled-subcircuit ancillas, and four live P16 flags. -/
def historyClockWorkspaceWidth (parameters : HistoryBlockParameters)
    (generatorWorkWidth : Nat) : Nat :=
  historySharedPoolWidth parameters generatorWorkWidth + 6

/-- Typed slice of the single workspace register used by the frozen P16 layout. -/
def historyWorkspaceSlice
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (offset width : Nat) (fits : offset + width ≤ workspaceWidth) :
    Register qubits width where
  wire index := layout.workspace.wire ⟨offset + index.val, by omega⟩
  injective := by
    intro left right equal
    apply Fin.ext
    have := layout.workspace.injective equal
    simpa using congrArg Fin.val this

theorem historyWorkspaceSlice_wire_mem
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (offset width : Nat) (fits : offset + width ≤ workspaceWidth)
    (index : Fin width) :
    (historyWorkspaceSlice layout offset width fits).wire index ∈
      historyRegisterWires layout.workspace := by
  simp only [historyRegisterWires, List.mem_ofFn]
  exact ⟨⟨offset + index.val, by omega⟩, rfl⟩

/-- Every selector wire is disjoint from every wire of the frozen workspace. -/
theorem HistoryBlockLayout.selector_wire_ne_workspace_wire
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (selectorIndex : Fin 2) (workspaceIndex : Fin workspaceWidth) :
    layout.selector.wire selectorIndex ≠
      layout.workspace.wire workspaceIndex := by
  have split := List.nodup_append.mp layout.allWiresNodup
  have selectorMember : layout.selector.wire selectorIndex ∈
      historyRegisterWires layout.selector :=
    List.mem_ofFn.mpr ⟨selectorIndex, rfl⟩
  have prefixMember : layout.selector.wire selectorIndex ∈
      historyRegisterWires layout.selector ++
        historyRegisterWires layout.data ++ historyRegisterWires layout.clock ++
        historyRegisterWires layout.order ++
        historyRegisterWires layout.generatorSignal ++
        [layout.coefficientSignal, layout.orderBoundarySignal,
          layout.projectorSignal, layout.clockBoundarySignal] :=
    List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ selectorMember))))
  exact split.2.2 _ prefixMember _
    (List.mem_ofFn.mpr ⟨workspaceIndex, rfl⟩)

/-- A workspace member cannot be either H1 selector wire. -/
theorem HistoryBlockLayout.workspace_wire_not_mem_selector_support
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (wire : Fin qubits)
    (member : wire ∈ historyRegisterWires layout.workspace) :
    wire ∉ ({layout.selector.wire 0, layout.selector.wire 1} :
      Finset (Fin qubits)) := by
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨workspaceIndex, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · exact (layout.selector_wire_ne_workspace_wire 0 workspaceIndex).symm
  · exact (layout.selector_wire_ne_workspace_wire 1 workspaceIndex).symm

/-- Every clock wire is disjoint from every workspace wire. -/
theorem HistoryBlockLayout.clock_wire_ne_workspace_wire
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (clockIndex : Fin (historyClockWidth parameters.timeSteps
      parameters.taylorOrder parameters.idlingSteps))
    (workspaceIndex : Fin workspaceWidth) :
    layout.clock.wire clockIndex ≠ layout.workspace.wire workspaceIndex := by
  have split := List.nodup_append.mp layout.allWiresNodup
  have clockMember : layout.clock.wire clockIndex ∈
      historyRegisterWires layout.clock :=
    List.mem_ofFn.mpr ⟨clockIndex, rfl⟩
  have prefixMember : layout.clock.wire clockIndex ∈
      historyRegisterWires layout.selector ++
        historyRegisterWires layout.data ++ historyRegisterWires layout.clock ++
        historyRegisterWires layout.order ++
        historyRegisterWires layout.generatorSignal ++
        [layout.coefficientSignal, layout.orderBoundarySignal,
          layout.projectorSignal, layout.clockBoundarySignal] :=
    List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _
        (List.mem_append_right _ clockMember)))
  exact split.2.2 _ prefixMember _
    (List.mem_ofFn.mpr ⟨workspaceIndex, rfl⟩)

/-- The two P15 post-generator signal targets are disjoint from every selector
wire, clock wire, and workspace wire.  This is a typed consequence of the one
frozen-layout `Nodup` certificate, not a representative-width calculation. -/
theorem HistoryBlockLayout.postGeneratorSignal_separated
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (signal : Fin qubits)
    (signalMember : signal ∈
      [layout.coefficientSignal, layout.orderBoundarySignal]) :
    (∀ index : Fin 2, layout.selector.wire index ≠ signal) ∧
      (∀ index : Fin (historyClockWidth parameters.timeSteps
        parameters.taylorOrder parameters.idlingSteps),
        layout.clock.wire index ≠ signal) ∧
      (∀ index : Fin workspaceWidth,
        layout.workspace.wire index ≠ signal) := by
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
  have reservedSplit := List.nodup_append.mp generatorSplit.2.1
  have reservedMember : signal ∈ reservedWires := by
    have extended := List.mem_append_left
      [layout.projectorSignal, layout.clockBoundarySignal] signalMember
    simpa [reservedWires] using extended
  have reservedInSelectorTail : signal ∈
      dataWires ++ (clockWires ++ (orderWires ++
        (generatorWires ++ (reservedWires ++ workspaceWires)))) := by
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ reservedMember))))
  refine ⟨?_, ?_, ?_⟩
  · intro index
    exact selectorSplit.2.2 _
      (by
        exact List.mem_ofFn.mpr ⟨index, rfl⟩) _ reservedInSelectorTail
  · intro index
    exact clockSplit.2.2 _
      (by
        exact List.mem_ofFn.mpr ⟨index, rfl⟩) _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ reservedMember)))
  · intro index
    exact (reservedSplit.2.2 _ reservedMember _
      (by
        exact List.mem_ofFn.mpr ⟨index, rfl⟩)).symm

/-- Order-register wires are disjoint from selector, clock, reserved signals,
and workspace.  This packages exactly the outside facts needed to show that
the pure degree increment preserves the H2 stable boundary. -/
theorem HistoryBlockLayout.orderWire_separated
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (orderIndex : Fin (historyOrderWidth parameters.taylorOrder)) :
    (∀ selectorIndex : Fin 2,
      layout.order.wire orderIndex ≠ layout.selector.wire selectorIndex) ∧
    (∀ clockIndex : Fin (historyClockWidth parameters.timeSteps
      parameters.taylorOrder parameters.idlingSteps),
      layout.order.wire orderIndex ≠ layout.clock.wire clockIndex) ∧
    (∀ signal ∈ [layout.coefficientSignal, layout.orderBoundarySignal],
      layout.order.wire orderIndex ≠ signal) ∧
    (∀ workspaceIndex : Fin workspaceWidth,
      layout.order.wire orderIndex ≠ layout.workspace.wire workspaceIndex) := by
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro selectorIndex
    exact (selectorSplit.2.2 _
      (by
        exact List.mem_ofFn.mpr ⟨selectorIndex, rfl⟩) _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _
          (List.mem_ofFn.mpr ⟨orderIndex, rfl⟩))))).symm
  · intro clockIndex
    exact (clockSplit.2.2 _
      (by
        exact List.mem_ofFn.mpr ⟨clockIndex, rfl⟩) _
      (List.mem_append_left _
        (List.mem_ofFn.mpr ⟨orderIndex, rfl⟩))).symm
  · intro signal signalMember
    have reservedMember : signal ∈ reservedWires := by
      have extended := List.mem_append_left
        [layout.projectorSignal, layout.clockBoundarySignal] signalMember
      simpa [reservedWires] using extended
    exact orderSplit.2.2 _ (List.mem_ofFn.mpr ⟨orderIndex, rfl⟩) _
      (List.mem_append_right _ (List.mem_append_left _ reservedMember))
  · intro workspaceIndex
    exact orderSplit.2.2 _ (List.mem_ofFn.mpr ⟨orderIndex, rfl⟩) _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_ofFn.mpr ⟨workspaceIndex, rfl⟩)))

/-- A workspace XOR does not alter the H1 selector predicate. -/
theorem HistoryBlockLayout.selectorEqualsNat_xorWire_workspace
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (target : Fin qubits) (member : target ∈ historyRegisterWires layout.workspace)
    (value : Bool) (basis : QubitBasis qubits) (constant : Nat) :
    littleEndianRegisterEqualsNat (historyRegisterWires layout.selector)
        constant (xorWire target value basis) =
      littleEndianRegisterEqualsNat (historyRegisterWires layout.selector)
        constant basis := by
  apply littleEndianRegisterEqualsNat_congr
  intro wire wireMember
  simp only [historyRegisterWires, List.mem_ofFn] at wireMember member
  rcases wireMember with ⟨selectorIndex, rfl⟩
  rcases member with ⟨workspaceIndex, rfl⟩
  exact xorWire_apply_other _ _
    (layout.selector_wire_ne_workspace_wire selectorIndex workspaceIndex) _ _

/-- A workspace XOR does not alter the typed clock word. -/
theorem HistoryBlockLayout.clock_read_xorWire_workspace
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (target : Fin qubits) (member : target ∈ historyRegisterWires layout.workspace)
    (value : Bool) (basis : QubitBasis qubits) :
    layout.clock.read (xorWire target value basis) = layout.clock.read basis := by
  funext clockIndex
  simp only [historyRegisterWires, List.mem_ofFn] at member
  rcases member with ⟨workspaceIndex, rfl⟩
  exact xorWire_apply_other _ _
    (layout.clock_wire_ne_workspace_wire clockIndex workspaceIndex) _ _

/-- Prefix of the aliased shared pool occupied by the probability-generator's
own work ancillas during P15.  It is distinct from the two external-control
compiler work wires allocated after the shared pool. -/
def historyGeneratorWorkRegister
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits generatorWorkWidth :=
  historyWorkspaceSlice layout 0 generatorWorkWidth (by
    have workFits := Nat.le_max_left generatorWorkWidth
      (historyStructuralPoolWidth parameters)
    unfold historyClockWorkspaceWidth historySharedPoolWidth
    omega)

/-- Every placed Q10 internal generator-work wire belongs to the aliased
workspace prefix. -/
theorem historyGeneratorWorkRegister_wire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin generatorWorkWidth) :
    (historyGeneratorWorkRegister layout).wire index ∈
      historyRegisterWires layout.workspace := by
  unfold historyGeneratorWorkRegister
  apply historyWorkspaceSlice_wire_mem

/-- Two ancillas used by source-faithful controlled-subcircuit compilation. -/
def historyUniformControlWork
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits 2 :=
  historyWorkspaceSlice layout 0 2 (by
    unfold historyClockWorkspaceWidth
    omega)

theorem historyUniformControlWork_wire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin 2) :
    (historyUniformControlWork layout).wire index ∈
      historyRegisterWires layout.workspace := by
  unfold historyUniformControlWork
  apply historyWorkspaceSlice_wire_mem

/-- Equality flag at shared-pool offset two. -/
def historyEqualityFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Fin qubits :=
  (historyWorkspaceSlice layout 2 1 (by
    unfold historyClockWorkspaceWidth
    omega)).wire 0

/-- Temporary AND target controlling the coefficient projector. -/
def historyCoefficientControl
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Fin qubits :=
  (historyWorkspaceSlice layout 3 1 (by
    unfold historyClockWorkspaceWidth
    omega)).wire 0

/-- Idle-region parity flag at shared-pool offset four. -/
def historyIdleFlag
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Fin qubits :=
  (historyWorkspaceSlice layout 4 1 (by
    unfold historyClockWorkspaceWidth
    omega)).wire 0

/-- Constant-mask register used by each frozen P16 less-than call. -/
def historyBoundRegister
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits
      (historyClockWidth parameters.timeSteps parameters.taylorOrder
        parameters.idlingSteps) :=
  historyWorkspaceSlice layout 5 _ (by
    have structuralFits := Nat.le_max_right generatorWorkWidth
      (historyStructuralPoolWidth parameters)
    unfold historyClockWorkspaceWidth historySharedPoolWidth
    unfold historyStructuralPoolWidth at structuralFits ⊢
    omega)

/-- Borrow register immediately following the bound register. -/
def historyBorrowRegister
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits
      (historyClockWidth parameters.timeSteps parameters.taylorOrder
        parameters.idlingSteps) :=
  let clockWidth := historyClockWidth parameters.timeSteps parameters.taylorOrder
    parameters.idlingSteps
  historyWorkspaceSlice layout (5 + clockWidth) clockWidth (by
    have structuralFits := Nat.le_max_right generatorWorkWidth
      (historyStructuralPoolWidth parameters)
    unfold historyClockWorkspaceWidth historySharedPoolWidth
    unfold historyStructuralPoolWidth at structuralFits ⊢
    omega)

theorem historyBoundRegister_wire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyClockWidth parameters.timeSteps
      parameters.taylorOrder parameters.idlingSteps)) :
    (historyBoundRegister layout).wire index ∈
      historyRegisterWires layout.workspace := by
  unfold historyBoundRegister
  apply historyWorkspaceSlice_wire_mem

theorem historyBorrowRegister_wire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyClockWidth parameters.timeSteps
      parameters.taylorOrder parameters.idlingSteps)) :
    (historyBorrowRegister layout).wire index ∈
      historyRegisterWires layout.workspace := by
  unfold historyBorrowRegister
  apply historyWorkspaceSlice_wire_mem

/-- Equality work follows both clock-width registers. -/
def historyEqualityWork
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits (historyEqualityWorkWidth parameters) :=
  let clockWidth := historyClockWidth parameters.timeSteps parameters.taylorOrder
    parameters.idlingSteps
  historyWorkspaceSlice layout (5 + 2 * clockWidth)
    (historyEqualityWorkWidth parameters) (by
      have structuralFits := Nat.le_max_right generatorWorkWidth
        (historyStructuralPoolWidth parameters)
      unfold historyClockWorkspaceWidth historySharedPoolWidth
      unfold historyStructuralPoolWidth at structuralFits ⊢
      omega)

/-- Frozen P42 uses exactly the low clock-width prefix of the masked-constant
pool as its Cuccaro addend register. -/
def historyClockMaskedConstantRegister
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits (historyClockTailWidth parameters + 1) :=
  let clockWidth := historyClockWidth parameters.timeSteps parameters.taylorOrder
    parameters.idlingSteps
  historyWorkspaceSlice layout
    (5 + 2 * clockWidth + historyEqualityWorkWidth parameters +
      historyMaximumLabelWidth parameters)
    (historyClockTailWidth parameters + 1) (by
      rw [historyClockTailWidth_succ]
      have structuralFits := Nat.le_max_right generatorWorkWidth
        (historyStructuralPoolWidth parameters)
      unfold historyClockWorkspaceWidth historySharedPoolWidth
      unfold historyStructuralPoolWidth at structuralFits ⊢
      unfold historyMaximumLabelWidth
      omega)

theorem historyClockMaskedConstantRegister_wire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyClockTailWidth parameters + 1)) :
    (historyClockMaskedConstantRegister layout).wire index ∈
      historyRegisterWires layout.workspace := by
  unfold historyClockMaskedConstantRegister
  apply historyWorkspaceSlice_wire_mem

/-- Frozen P15 comparisons use the low order-width prefix of the increment
pool as their temporary constant register. -/
def historyOrderBoundRegister
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits (historyOrderWidth parameters.taylorOrder) :=
  let clockWidth := historyClockWidth parameters.timeSteps parameters.taylorOrder
    parameters.idlingSteps
  historyWorkspaceSlice layout
    (5 + 2 * clockWidth + historyEqualityWorkWidth parameters)
    (historyOrderWidth parameters.taylorOrder) (by
      have structuralFits := Nat.le_max_right generatorWorkWidth
        (historyStructuralPoolWidth parameters)
      unfold historyClockWorkspaceWidth historySharedPoolWidth
      unfold historyStructuralPoolWidth at structuralFits ⊢
      unfold historyMaximumLabelWidth
      omega)

/-- Frozen P15 comparisons and the controlled degree increment share the low
order-width prefix of the masked-constant pool. -/
def historyOrderMaskedConstantRegister
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits (historyOrderWidth parameters.taylorOrder) :=
  let clockWidth := historyClockWidth parameters.timeSteps parameters.taylorOrder
    parameters.idlingSteps
  historyWorkspaceSlice layout
    (5 + 2 * clockWidth + historyEqualityWorkWidth parameters +
      historyMaximumLabelWidth parameters)
    (historyOrderWidth parameters.taylorOrder) (by
      have structuralFits := Nat.le_max_right generatorWorkWidth
        (historyStructuralPoolWidth parameters)
      unfold historyClockWorkspaceWidth historySharedPoolWidth
      unfold historyStructuralPoolWidth at structuralFits ⊢
      unfold historyMaximumLabelWidth
      omega)

/-- The P15 Cuccaro degree increment uses the first increment-pool wire as its
carry, matching the frozen Python emitter. -/
def historyOrderIncrementCarry
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Fin qubits :=
  let clockWidth := historyClockWidth parameters.timeSteps parameters.taylorOrder
    parameters.idlingSteps
  (historyWorkspaceSlice layout
    (5 + 2 * clockWidth + historyEqualityWorkWidth parameters) 1 (by
      have structuralFits := Nat.le_max_right generatorWorkWidth
        (historyStructuralPoolWidth parameters)
      unfold historyClockWorkspaceWidth historySharedPoolWidth
      unfold historyStructuralPoolWidth at structuralFits ⊢
      omega)).wire 0

/-- Taylor order accumulator recast to the positive-width Cuccaro index. -/
def historyOrderAccumulatorRegister
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits (historyOrderTailWidth parameters + 1) := by
  rw [historyOrderTailWidth_succ]
  exact layout.order

/-- Masked constant prefix recast to the same Cuccaro index. -/
def historyOrderIncrementAddendRegister
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits (historyOrderTailWidth parameters + 1) := by
  rw [historyOrderTailWidth_succ]
  exact historyOrderMaskedConstantRegister layout

/-- Frozen P42 reads only the first increment-work wire as its Cuccaro carry. -/
def historyClockIncrementCarry
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Fin qubits :=
  let clockWidth := historyClockWidth parameters.timeSteps parameters.taylorOrder
    parameters.idlingSteps
  (historyWorkspaceSlice layout
    (5 + 2 * clockWidth + historyEqualityWorkWidth parameters) 1 (by
      have structuralFits := Nat.le_max_right generatorWorkWidth
        (historyStructuralPoolWidth parameters)
      unfold historyClockWorkspaceWidth historySharedPoolWidth
      unfold historyStructuralPoolWidth at structuralFits ⊢
      omega)).wire 0

theorem historyClockIncrementCarry_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyClockIncrementCarry layout ∈
      historyRegisterWires layout.workspace := by
  unfold historyClockIncrementCarry
  apply historyWorkspaceSlice_wire_mem

/-- Clock accumulator recast to the positive-width Cuccaro index convention. -/
def historyClockAccumulatorRegister
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits (historyClockTailWidth parameters + 1) := by
  rw [historyClockTailWidth_succ]
  exact layout.clock

/-- Two ancillas allocated after the aliased shared pool. -/
def historyControlledWork
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Register qubits 2 :=
  historyWorkspaceSlice layout
    (historySharedPoolWidth parameters generatorWorkWidth) 2 (by
      unfold historyClockWorkspaceWidth
      omega)

/-- Four live flags following controlled work, in frozen allocation order. -/
def historyBranchWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Fin qubits :=
  (historyWorkspaceSlice layout
    (historySharedPoolWidth parameters generatorWorkWidth + 2) 1 (by
      unfold historyClockWorkspaceWidth
      omega)).wire 0

def historyLessThanTimeWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Fin qubits :=
  (historyWorkspaceSlice layout
    (historySharedPoolWidth parameters generatorWorkWidth + 3) 1 (by
      unfold historyClockWorkspaceWidth
      omega)).wire 0

def historyLessThanIdleEndWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Fin qubits :=
  (historyWorkspaceSlice layout
    (historySharedPoolWidth parameters generatorWorkWidth + 4) 1 (by
      unfold historyClockWorkspaceWidth
      omega)).wire 0

def historyActiveWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Fin qubits :=
  (historyWorkspaceSlice layout
    (historySharedPoolWidth parameters generatorWorkWidth + 5) 1 (by
      unfold historyClockWorkspaceWidth
      omega)).wire 0

theorem historyBranchWire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyBranchWire layout ∈ historyRegisterWires layout.workspace := by
  unfold historyBranchWire
  apply historyWorkspaceSlice_wire_mem

theorem historyLessThanTimeWire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyLessThanTimeWire layout ∈ historyRegisterWires layout.workspace := by
  unfold historyLessThanTimeWire
  apply historyWorkspaceSlice_wire_mem

theorem historyLessThanIdleEndWire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyLessThanIdleEndWire layout ∈
      historyRegisterWires layout.workspace := by
  unfold historyLessThanIdleEndWire
  apply historyWorkspaceSlice_wire_mem

theorem historyActiveWire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyActiveWire layout ∈ historyRegisterWires layout.workspace := by
  unfold historyActiveWire
  apply historyWorkspaceSlice_wire_mem

/-- Human-facing P15 auxiliary clean boundary.  The frozen source aliases Q10
internal work, arithmetic scratch, predicate flags, and controlled-subcircuit
work inside one workspace register.  All of it is zero at H2 entry and restored
at H2 exit, although individual wires may be live at internal source-order
boundaries. -/
def historyTaylorAuxiliaryBoundaryPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  ∀ index, basis (layout.workspace.wire index) = false

/-- The four auxiliary flags intentionally live at the unique controlled-Q10
boundary, in their frozen allocation/source-computation order. -/
def historyTaylorBeforeGeneratorLiveWires
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    List (Fin qubits) :=
  [historyBranchWire layout, historyLessThanTimeWire layout,
    historyLessThanIdleEndWire layout, historyActiveWire layout]

theorem historyBranchWire_ne_lessThanTimeWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyBranchWire layout ≠ historyLessThanTimeWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

theorem historyBranchWire_ne_lessThanIdleEndWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyBranchWire layout ≠ historyLessThanIdleEndWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

theorem historyBranchWire_ne_activeWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyBranchWire layout ≠ historyActiveWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

theorem historyLessThanTimeWire_ne_lessThanIdleEndWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyLessThanTimeWire layout ≠ historyLessThanIdleEndWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

theorem historyLessThanTimeWire_ne_activeWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyLessThanTimeWire layout ≠ historyActiveWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

theorem historyLessThanIdleEndWire_ne_activeWire
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    historyLessThanIdleEndWire layout ≠ historyActiveWire layout := by
  intro equal
  change layout.workspace.wire _ = layout.workspace.wire _ at equal
  have indexEqual := layout.workspace.injective equal
  have valuesEqual := congrArg Fin.val indexEqual
  dsimp at valuesEqual
  omega

theorem historyTaylorSelectorEqualityLayout_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    (historyRegisterWires layout.selector ++ [] ++
      [historyBranchWire layout]).Nodup := by
  simp only [List.append_nil]
  apply List.nodup_append.mpr
  refine ⟨historyRegisterWires_nodup layout.selector, by simp, ?_⟩
  intro selectorWire selectorMember branchWire branchMember
  simp only [List.mem_singleton] at branchMember
  subst branchWire
  simp only [historyRegisterWires, List.mem_ofFn] at selectorMember
  rcases selectorMember with ⟨selectorIndex, rfl⟩
  have branchMember := historyBranchWire_mem_workspace layout
  simp only [historyRegisterWires, List.mem_ofFn] at branchMember
  rcases branchMember with ⟨workspaceIndex, equal⟩
  intro selectorEqualsBranch
  exact layout.selector_wire_ne_workspace_wire selectorIndex workspaceIndex
    (selectorEqualsBranch.trans equal.symm)

theorem historyTaylorActiveConjunctionLayout_nodup
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    ([historyBranchWire layout, historyLessThanTimeWire layout] ++ [] ++
      [historyActiveWire layout]).Nodup := by
  simp [historyBranchWire_ne_lessThanTimeWire layout,
    historyBranchWire_ne_activeWire layout,
    historyLessThanTimeWire_ne_activeWire layout]

/-- Every typed slice wholly inside the aliased shared pool is disjoint from
the four flags allocated after the two external-control work wires. -/
theorem historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
    {qubits dataWidth generatorSignalWidth generatorWorkWidth width : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (offset : Nat)
    (fits : offset + width ≤
      historyClockWorkspaceWidth parameters generatorWorkWidth)
    (insideShared : offset + width ≤
      historySharedPoolWidth parameters generatorWorkWidth)
    (index : Fin width) :
    (historyWorkspaceSlice layout offset width fits).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
  simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
    List.not_mem_nil, or_false]
  intro member
  rcases member with equal | equal | equal | equal
  · change layout.workspace.wire _ = layout.workspace.wire _ at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    dsimp at valuesEqual
    omega
  · change layout.workspace.wire _ = layout.workspace.wire _ at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    dsimp at valuesEqual
    omega
  · change layout.workspace.wire _ = layout.workspace.wire _ at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    dsimp at valuesEqual
    omega
  · change layout.workspace.wire _ = layout.workspace.wire _ at equal
    have indexEqual := layout.workspace.injective equal
    have valuesEqual := congrArg Fin.val indexEqual
    dsimp at valuesEqual
    omega

theorem historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyClockWidth parameters.timeSteps
      parameters.taylorOrder parameters.idlingSteps)) :
    (historyBoundRegister layout).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyBoundRegister
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  have structuralFits := Nat.le_max_right generatorWorkWidth
    (historyStructuralPoolWidth parameters)
  unfold historySharedPoolWidth
  unfold historyStructuralPoolWidth at structuralFits ⊢
  omega

theorem historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin (historyClockWidth parameters.timeSteps
      parameters.taylorOrder parameters.idlingSteps)) :
    (historyBorrowRegister layout).wire index ∉
      historyTaylorBeforeGeneratorLiveWires layout := by
  unfold historyBorrowRegister
  apply historyWorkspaceSlice_wire_not_mem_beforeGeneratorLiveWires
  have structuralFits := Nat.le_max_right generatorWorkWidth
    (historyStructuralPoolWidth parameters)
  unfold historySharedPoolWidth
  unfold historyStructuralPoolWidth at structuralFits ⊢
  omega

/-- Workspace wires whose zero/restoration contract is owned by the unique
controlled-Q10 child rather than the surrounding auxiliary chains. -/
def historyTaylorControlledQ10OwnedWorkspaceWires
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    List (Fin qubits) :=
  historyRegisterWires (historyGeneratorWorkRegister layout) ++
    historyRegisterWires (historyControlledWork layout)

/-- Fixed-width mathematical comparison used at the first P41 occurrence.
The separate width-sufficiency bridge identifies this with the ordinary
natural-number inequality and prevents silent constant truncation. -/
def historyTaylorClockLessThanTimeValue
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  unsignedLessThanBits (layout.clock.read basis)
    (fun index => parameters.timeSteps.testBit index.val)

/-- Fixed-width mathematical comparison with the frozen end of the idling
clock interval. -/
def historyTaylorClockLessThanIdleEndValue
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  unsignedLessThanBits (layout.clock.read basis)
    (fun index =>
      (historyIdleClockEnd parameters.timeSteps parameters.taylorOrder
        parameters.idlingSteps).testBit index.val)

/-- Human-facing first P41 action. -/
def historyTaylorTimeComparisonBasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : QubitBasis qubits :=
  xorWire (historyLessThanTimeWire layout)
    (historyTaylorClockLessThanTimeValue layout basis) basis

/-- Human-facing second P41 action. -/
def historyTaylorIdleEndComparisonBasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : QubitBasis qubits :=
  xorWire (historyLessThanIdleEndWire layout)
    (historyTaylorClockLessThanIdleEndValue layout basis) basis

noncomputable def historyTaylorTimeComparisonOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (historyTaylorTimeComparisonBasisAction layout)

noncomputable def historyTaylorIdleEndComparisonOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (historyTaylorIdleEndComparisonBasisAction layout)

/-- All workspace wires except the explicitly live prefix are zero.  This is
the small human-facing invariant shared by the four pre-generator phases; it
does not expose the comparator's transient borrow computation. -/
def historyTaylorWorkspaceZeroExcept
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (live : List (Fin qubits)) (basis : QubitBasis qubits) : Prop :=
  ∀ index, layout.workspace.wire index ∉ live →
    basis (layout.workspace.wire index) = false

/-- Reading the all-zero outer workspace predicate through a named member. -/
theorem historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits)
    (inside : historyTaylorAuxiliaryBoundaryPredicate layout basis)
    (wire : Fin qubits) (member : wire ∈ historyRegisterWires layout.workspace) :
    basis wire = false := by
  rcases List.mem_ofFn.mp member with ⟨index, rfl⟩
  exact inside index

/-- Source-order variant of the preceding lemma: append the newly computed
flag after the flags that were already live. -/
theorem historyTaylorWorkspaceZeroExcept_xorWire_append
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (live : List (Fin qubits)) (target : Fin qubits) (value : Bool)
    (basis : QubitBasis qubits)
    (inside : historyTaylorWorkspaceZeroExcept layout live basis) :
    historyTaylorWorkspaceZeroExcept layout (live ++ [target])
      (xorWire target value basis) := by
  intro index outside
  rw [xorWire_apply_other target (layout.workspace.wire index)]
  · exact inside index (by
      intro member
      exact outside (List.mem_append_left _ member))
  · intro equal
    exact outside (List.mem_append_right _ (by simp [equal]))

theorem historyTaylorWorkspaceZeroExcept_mono
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (smaller larger : List (Fin qubits)) (basis : QubitBasis qubits)
    (subset : ∀ wire, wire ∈ smaller → wire ∈ larger)
    (inside : historyTaylorWorkspaceZeroExcept layout smaller basis) :
    historyTaylorWorkspaceZeroExcept layout larger basis := by
  intro index outside
  exact inside index (fun member => outside (subset _ member))

theorem historyTaylorWorkspaceZeroExcept_apply_of_mem
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (live : List (Fin qubits)) (basis : QubitBasis qubits)
    (inside : historyTaylorWorkspaceZeroExcept layout live basis)
    (wire : Fin qubits) (member : wire ∈ historyRegisterWires layout.workspace)
    (outside : wire ∉ live) :
    basis wire = false := by
  rcases List.mem_ofFn.mp member with ⟨index, rfl⟩
  exact inside index outside

/-- Any named typed slice of the shared workspace is zero whenever every one
of its wires lies outside the currently live phase list.  This is the bridge
used to obtain P41 rhs/borrow clean premises without exposing slice offsets in
the human-facing H2 specification. -/
theorem historyTaylorWorkspaceZeroExcept_slice
    {qubits dataWidth generatorSignalWidth generatorWorkWidth width : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (live : List (Fin qubits)) (basis : QubitBasis qubits)
    (inside : historyTaylorWorkspaceZeroExcept layout live basis)
    (slice : Register qubits width)
    (sliceInside : ∀ index, slice.wire index ∈
      historyRegisterWires layout.workspace)
    (sliceOutsideLive : ∀ index, slice.wire index ∉ live) :
    ∀ index, slice.read basis index = false := by
  intro index
  unfold Register.read
  rcases List.mem_ofFn.mp (sliceInside index) with ⟨workspaceIndex, equal⟩
  rw [← equal]
  exact inside workspaceIndex (by simpa [equal] using sliceOutsideLive index)

/-- The P41 constant register is zero at any phase whose live-wire list is
disjoint from the register.  This exposes the actual clean premise of the
recorded comparator instead of hiding it behind a circuit-specific wrapper. -/
theorem historyBoundRegister_zero_of_workspaceZeroExcept
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (live : List (Fin qubits)) (basis : QubitBasis qubits)
    (inside : historyTaylorWorkspaceZeroExcept layout live basis)
    (outside : ∀ index, (historyBoundRegister layout).wire index ∉ live) :
    ∀ index, (historyBoundRegister layout).read basis index = false :=
  historyTaylorWorkspaceZeroExcept_slice layout live basis inside
    (historyBoundRegister layout) (historyBoundRegister_wire_mem_workspace layout)
    outside

/-- The transient P41 borrow register is likewise zero at every such phase. -/
theorem historyBorrowRegister_zero_of_workspaceZeroExcept
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (live : List (Fin qubits)) (basis : QubitBasis qubits)
    (inside : historyTaylorWorkspaceZeroExcept layout live basis)
    (outside : ∀ index, (historyBorrowRegister layout).wire index ∉ live) :
    ∀ index, (historyBorrowRegister layout).read basis index = false :=
  historyTaylorWorkspaceZeroExcept_slice layout live basis inside
    (historyBorrowRegister layout) (historyBorrowRegister_wire_mem_workspace layout)
    outside

/-- Human-facing P40 action: XOR the branch flag iff the two-bit selector is
the little-endian label one.  The minimum-work compiler AST is intentionally
absent from this definition. -/
def historyTaylorSelectorEqualityBasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : QubitBasis qubits :=
  ClassicalReversibleStage.equalityToConstantDirectBasisAction
    (historyRegisterWires layout.selector) 1 (historyBranchWire layout) basis

/-- Linear extension of the P40 direct action. -/
noncomputable def historyTaylorSelectorEqualityOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (historyTaylorSelectorEqualityBasisAction layout)

/-- Human-facing P43 action at the controlled-Q10 boundary. -/
def historyTaylorActiveConjunctionBasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : QubitBasis qubits :=
  ClassicalReversibleStage.conjunctionDirectBasisAction
    [historyBranchWire layout, historyLessThanTimeWire layout]
    (historyActiveWire layout) basis

/-- Linear extension of the boundary P43 action. -/
noncomputable def historyTaylorActiveConjunctionOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (historyTaylorActiveConjunctionBasisAction layout)

/-! ### H2 post-generator mathematical actions -/

/-- The invalid-clock contribution is toggled precisely on branch one and at
or beyond the idling-clock end. -/
def historyTaylorInvalidClockCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  basis (historyBranchWire layout) &&
    !basis (historyLessThanIdleEndWire layout)

def historyTaylorInvalidClockBasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : QubitBasis qubits :=
  xorWire layout.coefficientSignal
    (historyTaylorInvalidClockCondition layout basis) basis

noncomputable def historyTaylorInvalidClockOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (historyTaylorInvalidClockBasisAction layout)

/-- The source X--Toffoli--X word has exactly the direct invalid-clock action. -/
theorem historyTaylorInvalidClockSourceAction_eq_direct
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (branch_ne_ltIdleEnd :
      historyBranchWire layout ≠ historyLessThanIdleEndWire layout)
    (branch_ne_coefficientSignal :
      historyBranchWire layout ≠ layout.coefficientSignal)
    (ltIdleEnd_ne_coefficientSignal :
      historyLessThanIdleEndWire layout ≠ layout.coefficientSignal)
    (input : QubitBasis qubits) :
    let flip := ClassicalReversibleInstruction.xorOne
      (historyLessThanIdleEndWire layout)
    let use := ClassicalReversibleInstruction.xorDoublyControlled
      (historyBranchWire layout) (historyLessThanIdleEndWire layout)
      layout.coefficientSignal branch_ne_ltIdleEnd
      branch_ne_coefficientSignal ltIdleEnd_ne_coefficientSignal
    flip.basisAction (use.basisAction (flip.basisAction input)) =
      historyTaylorInvalidClockBasisAction layout input := by
  dsimp only
  funext wire
  by_cases wireCoefficient : wire = layout.coefficientSignal
  · subst wire
    simp [ClassicalReversibleInstruction.basisAction,
      historyTaylorInvalidClockBasisAction,
      historyTaylorInvalidClockCondition, xorWire,
      branch_ne_ltIdleEnd, ltIdleEnd_ne_coefficientSignal,
      ltIdleEnd_ne_coefficientSignal.symm]
  · by_cases wireIdleEnd : wire = historyLessThanIdleEndWire layout
    · subst wire
      simp [ClassicalReversibleInstruction.basisAction,
        historyTaylorInvalidClockBasisAction, xorWire,
        branch_ne_ltIdleEnd, ltIdleEnd_ne_coefficientSignal,
        ltIdleEnd_ne_coefficientSignal.symm]
    · simp [ClassicalReversibleInstruction.basisAction,
        historyTaylorInvalidClockBasisAction, xorWire,
        wireCoefficient, wireIdleEnd, branch_ne_ltIdleEnd,
        ltIdleEnd_ne_coefficientSignal,
        ltIdleEnd_ne_coefficientSignal.symm]

/-- Operator form of the preceding source-word equality. -/
theorem historyTaylorInvalidClockSourceOperator_eq_direct
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (branch_ne_ltIdleEnd :
      historyBranchWire layout ≠ historyLessThanIdleEndWire layout)
    (branch_ne_coefficientSignal :
      historyBranchWire layout ≠ layout.coefficientSignal)
    (ltIdleEnd_ne_coefficientSignal :
      historyLessThanIdleEndWire layout ≠ layout.coefficientSignal) :
    let flip := ClassicalReversibleInstruction.xorOne
      (historyLessThanIdleEndWire layout)
    let use := ClassicalReversibleInstruction.xorDoublyControlled
      (historyBranchWire layout) (historyLessThanIdleEndWire layout)
      layout.coefficientSignal branch_ne_ltIdleEnd
      branch_ne_coefficientSignal ltIdleEnd_ne_coefficientSignal
    operatorSequence
      [deterministicOperator flip.basisAction,
       deterministicOperator use.basisAction,
       deterministicOperator flip.basisAction] =
      historyTaylorInvalidClockOperator layout := by
  dsimp only
  rw [show [deterministicOperator
          (ClassicalReversibleInstruction.xorOne
            (historyLessThanIdleEndWire layout)).basisAction,
        deterministicOperator
          (ClassicalReversibleInstruction.xorDoublyControlled
            (historyBranchWire layout) (historyLessThanIdleEndWire layout)
            layout.coefficientSignal branch_ne_ltIdleEnd
            branch_ne_coefficientSignal
            ltIdleEnd_ne_coefficientSignal).basisAction,
        deterministicOperator
          (ClassicalReversibleInstruction.xorOne
            (historyLessThanIdleEndWire layout)).basisAction] =
      [(ClassicalReversibleInstruction.xorOne
          (historyLessThanIdleEndWire layout)).basisAction,
       (ClassicalReversibleInstruction.xorDoublyControlled
          (historyBranchWire layout) (historyLessThanIdleEndWire layout)
          layout.coefficientSignal branch_ne_ltIdleEnd
          branch_ne_coefficientSignal ltIdleEnd_ne_coefficientSignal).basisAction,
       (ClassicalReversibleInstruction.xorOne
          (historyLessThanIdleEndWire layout)).basisAction].map
        deterministicOperator by rfl]
  rw [operatorSequence_deterministicOperator]
  unfold historyTaylorInvalidClockOperator
  apply congrArg deterministicOperator
  funext input
  exact historyTaylorInvalidClockSourceAction_eq_direct layout
    branch_ne_ltIdleEnd branch_ne_coefficientSignal
    ltIdleEnd_ne_coefficientSignal input

/-- Fixed-width direct comparison of the order word with the Taylor order. -/
def historyTaylorOrderLessThanTaylorOrderValue
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  unsignedLessThanBits (layout.order.read basis)
    (fun index => parameters.taylorOrder.testBit index.val)

/-- Taylor-order boundary: branch one, physical-time clock, and order at or
beyond the Taylor order. -/
def historyTaylorOrderBoundaryCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  basis (historyBranchWire layout) &&
    historyTaylorClockLessThanTimeValue layout basis &&
    !historyTaylorOrderLessThanTaylorOrderValue layout basis

def historyTaylorOrderBoundaryBasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : QubitBasis qubits :=
  xorWire layout.orderBoundarySignal
    (historyTaylorOrderBoundaryCondition layout basis) basis

noncomputable def historyTaylorOrderBoundaryOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (historyTaylorOrderBoundaryBasisAction layout)

/-- The idling interval lies between the two clock predicates. -/
def historyTaylorIdleIntervalCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  historyTaylorClockLessThanIdleEndValue layout basis !=
    historyTaylorClockLessThanTimeValue layout basis

/-- Idle boundary: branch one, a clock in the idling interval, and the last
binary order label. -/
def historyTaylorIdleBoundaryCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  basis (historyBranchWire layout) &&
    historyTaylorIdleIntervalCondition layout basis &&
    littleEndianRegisterEqualsNat (historyRegisterWires layout.order)
      (historyIdleBlockSize parameters.taylorOrder - 1) basis

def historyTaylorIdleBoundaryBasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : QubitBasis qubits :=
  xorWire layout.orderBoundarySignal
    (historyTaylorIdleBoundaryCondition layout basis) basis

noncomputable def historyTaylorIdleBoundaryOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (historyTaylorIdleBoundaryBasisAction layout)

/-- Degree/order increments exactly on branch one before the idle-clock end. -/
def historyTaylorDegreeIncrementCondition
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Bool :=
  basis (historyBranchWire layout) &&
    historyTaylorClockLessThanIdleEndValue layout basis

noncomputable def historyTaylorDegreeIncrementBasisAction
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : QubitBasis qubits :=
  predicateControlledAddMod2PowBasisAction
    (historyTaylorDegreeIncrementCondition layout) layout.order 1 basis

noncomputable def historyTaylorDegreeIncrementOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Operator (QubitBasis qubits) :=
  predicateControlledAddMod2PowOperator
    (historyTaylorDegreeIncrementCondition layout) layout.order 1

/-- One Taylor coefficient rotation selected directly by branch, clock and
order, with no equality/conjunction work flag in the specification. -/
noncomputable def historyTaylorCoefficientIterationOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) (index : Fin parameters.taylorOrder) :
    Operator (QubitBasis qubits) :=
  predicateControlledSingleQubitOperator
    (fun basis =>
      basis (historyBranchWire layout) &&
        historyTaylorClockLessThanTimeValue layout basis &&
        littleEndianRegisterEqualsNat (historyRegisterWires layout.order)
          (index.val + 1) basis)
    layout.coefficientSignal (localRy angle.uniformValue)

/-- Source-order product of the independently selected Taylor rotations. -/
noncomputable def historyTaylorCoefficientLoopOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angles : Fin parameters.taylorOrder → AngleExpr) :
    Operator (QubitBasis qubits) :=
  operatorSequence ((List.finRange parameters.taylorOrder).map
    (fun index => historyTaylorCoefficientIterationOperator layout
      (angles index) index))

/-- One independently stated coefficient rotation in the idling interval. -/
noncomputable def historyTaylorIdleCoefficientOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (angle : AngleExpr) : Operator (QubitBasis qubits) :=
  predicateControlledSingleQubitOperator
    (fun basis => basis (historyBranchWire layout) &&
      historyTaylorIdleIntervalCondition layout basis)
    layout.coefficientSignal (localRy angle.uniformValue)

/-- Boundary after P40 has computed only the selector-branch flag. -/
def historyTaylorAfterSelectorPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyBranchWire layout) =
      littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 1 basis ∧
    historyTaylorWorkspaceZeroExcept layout
      [historyBranchWire layout] basis

/-- Boundary after the first P41 has additionally computed `clock < T`. -/
def historyTaylorAfterTimeComparisonPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyBranchWire layout) =
      littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 1 basis ∧
    basis (historyLessThanTimeWire layout) =
      historyTaylorClockLessThanTimeValue layout basis ∧
    historyTaylorWorkspaceZeroExcept layout
      [historyBranchWire layout, historyLessThanTimeWire layout] basis

/-- Boundary after the second P41 has both fixed-width clock predicates. -/
def historyTaylorAfterIdleEndComparisonPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyBranchWire layout) =
      littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 1 basis ∧
    basis (historyLessThanTimeWire layout) =
      historyTaylorClockLessThanTimeValue layout basis ∧
    basis (historyLessThanIdleEndWire layout) =
      historyTaylorClockLessThanIdleEndValue layout basis ∧
    historyTaylorWorkspaceZeroExcept layout
      [historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] basis

/-- The first comparison starts from the recorded comparator's genuine clean
boundary: both its constant register and its borrow register are zero. -/
theorem historyTaylorAfterSelectorPredicate_p41Clean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits)
    (inside : historyTaylorAfterSelectorPredicate layout basis) :
    (∀ index, (historyBoundRegister layout).read basis index = false) ∧
      (∀ index, (historyBorrowRegister layout).read basis index = false) := by
  constructor
  · apply historyBoundRegister_zero_of_workspaceZeroExcept layout
      [historyBranchWire layout] basis inside.2
    intro index member
    have outside :=
      historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires layout index
    apply outside
    have equal : (historyBoundRegister layout).wire index =
        historyBranchWire layout := by simpa using member
    simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
      List.not_mem_nil, or_false]
    exact Or.inl equal
  · apply historyBorrowRegister_zero_of_workspaceZeroExcept layout
      [historyBranchWire layout] basis inside.2
    intro index member
    have outside :=
      historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires layout index
    apply outside
    have equal : (historyBorrowRegister layout).wire index =
        historyBranchWire layout := by simpa using member
    simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
      List.not_mem_nil, or_false]
    exact Or.inl equal

/-- The second P41 occurrence has the same explicit clean comparator boundary
after the first comparison flag has become live. -/
theorem historyTaylorAfterTimeComparisonPredicate_p41Clean
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits)
    (inside : historyTaylorAfterTimeComparisonPredicate layout basis) :
    (∀ index, (historyBoundRegister layout).read basis index = false) ∧
      (∀ index, (historyBorrowRegister layout).read basis index = false) := by
  constructor
  · apply historyBoundRegister_zero_of_workspaceZeroExcept layout
      [historyBranchWire layout, historyLessThanTimeWire layout] basis inside.2.2
    intro index member
    have outside :=
      historyBoundRegister_wire_not_mem_beforeGeneratorLiveWires layout index
    apply outside
    have equal : (historyBoundRegister layout).wire index =
          historyBranchWire layout ∨
        (historyBoundRegister layout).wire index =
          historyLessThanTimeWire layout := by simpa using member
    rcases equal with equal | equal
    · change (historyBoundRegister layout).wire index ∈
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout, historyActiveWire layout]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl equal
    · change (historyBoundRegister layout).wire index ∈
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout, historyActiveWire layout]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inl equal)
  · apply historyBorrowRegister_zero_of_workspaceZeroExcept layout
      [historyBranchWire layout, historyLessThanTimeWire layout] basis inside.2.2
    intro index member
    have outside :=
      historyBorrowRegister_wire_not_mem_beforeGeneratorLiveWires layout index
    apply outside
    have equal : (historyBorrowRegister layout).wire index =
          historyBranchWire layout ∨
        (historyBorrowRegister layout).wire index =
          historyLessThanTimeWire layout := by simpa using member
    rcases equal with equal | equal
    · change (historyBorrowRegister layout).wire index ∈
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout, historyActiveWire layout]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl equal
    · change (historyBorrowRegister layout).wire index ∈
        [historyBranchWire layout, historyLessThanTimeWire layout,
          historyLessThanIdleEndWire layout, historyActiveWire layout]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inl equal)

/-- Human-facing source-reachable predicate at the single controlled-Q10
occurrence.  It says exactly what the four before stages computed and requires
all other workspace wires to be zero.  The after list must return this predicate
to `historyTaylorAuxiliaryBoundaryPredicate`. -/
def historyTaylorBeforeGeneratorBoundaryPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyBranchWire layout) =
      littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 1 basis ∧
    basis (historyLessThanTimeWire layout) =
      historyTaylorClockLessThanTimeValue layout basis ∧
    basis (historyLessThanIdleEndWire layout) =
      historyTaylorClockLessThanIdleEndValue layout basis ∧
    basis (historyActiveWire layout) =
      (basis (historyBranchWire layout) &&
        basis (historyLessThanTimeWire layout)) ∧
    historyTaylorWorkspaceZeroExcept layout
      (historyTaylorBeforeGeneratorLiveWires layout ++
        historyTaylorControlledQ10OwnedWorkspaceWires layout) basis

/-- Stable auxiliary boundary for the post-generator groups.  The branch and
two clock flags stay live; active/equality/idle/coefficient controls and all
other auxiliary work are zero.  Q10-owned work remains a separate conjunct in
the H2 understanding specification. -/
def historyTaylorPostGeneratorStablePredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyBranchWire layout) =
      littleEndianRegisterEqualsNat
        (historyRegisterWires layout.selector) 1 basis ∧
    basis (historyLessThanTimeWire layout) =
      historyTaylorClockLessThanTimeValue layout basis ∧
    basis (historyLessThanIdleEndWire layout) =
      historyTaylorClockLessThanIdleEndValue layout basis ∧
    historyTaylorWorkspaceZeroExcept layout
      ([historyBranchWire layout, historyLessThanTimeWire layout,
        historyLessThanIdleEndWire layout] ++
        historyTaylorControlledQ10OwnedWorkspaceWires layout) basis

/-- The common post-generator invariant depends only on wires outside either
reserved post signal.  This extensional form, rather than the XOR-specialized
corollary below, is what permits coherent one-qubit rotations on the signal. -/
theorem historyTaylorPostGeneratorStablePredicate_of_agreesOutsideSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (signal : Fin qubits)
    (signalMember : signal ∈
      [layout.coefficientSignal, layout.orderBoundarySignal])
    (input output : QubitBasis qubits)
    (inside : historyTaylorPostGeneratorStablePredicate layout input)
    (sameOutside : ∀ wire, wire ≠ signal → output wire = input wire) :
    historyTaylorPostGeneratorStablePredicate layout output := by
  have separated := layout.postGeneratorSignal_separated signal signalMember
  have workspaceOutside (index : Fin
      (historyClockWorkspaceWidth parameters generatorWorkWidth)) :
      layout.workspace.wire index ≠ signal :=
    separated.2.2 index
  have branchOutside : historyBranchWire layout ≠ signal := by
    have member := historyBranchWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨index, equal⟩
    exact equal.symm ▸ workspaceOutside index
  have timeOutside : historyLessThanTimeWire layout ≠ signal := by
    have member := historyLessThanTimeWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨index, equal⟩
    exact equal.symm ▸ workspaceOutside index
  have idleOutside : historyLessThanIdleEndWire layout ≠ signal := by
    have member := historyLessThanIdleEndWire_mem_workspace layout
    rcases List.mem_ofFn.mp member with ⟨index, equal⟩
    exact equal.symm ▸ workspaceOutside index
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      output (historyBranchWire layout) = input (historyBranchWire layout) :=
        sameOutside _ branchOutside
      _ = littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 1 input := inside.1
      _ = littleEndianRegisterEqualsNat
          (historyRegisterWires layout.selector) 1 output := by
        apply littleEndianRegisterEqualsNat_congr
        intro wire member
        simp only [historyRegisterWires, List.mem_ofFn] at member
        rcases member with ⟨index, rfl⟩
        exact (sameOutside _ (separated.1 index)).symm
  · calc
      output (historyLessThanTimeWire layout) =
          input (historyLessThanTimeWire layout) :=
        sameOutside _ timeOutside
      _ = historyTaylorClockLessThanTimeValue layout input := inside.2.1
      _ = historyTaylorClockLessThanTimeValue layout output := by
        unfold historyTaylorClockLessThanTimeValue
        apply congrArg₂ unsignedLessThanBits
        · funext index
          exact (sameOutside _ (separated.2.1 index)).symm
        · rfl
  · calc
      output (historyLessThanIdleEndWire layout) =
          input (historyLessThanIdleEndWire layout) :=
        sameOutside _ idleOutside
      _ = historyTaylorClockLessThanIdleEndValue layout input := inside.2.2.1
      _ = historyTaylorClockLessThanIdleEndValue layout output := by
        unfold historyTaylorClockLessThanIdleEndValue
        apply congrArg₂ unsignedLessThanBits
        · funext index
          exact (sameOutside _ (separated.2.1 index)).symm
        · rfl
  · intro index outside
    calc
      output (layout.workspace.wire index) =
          input (layout.workspace.wire index) :=
        sameOutside _ (workspaceOutside index)
      _ = false := inside.2.2.2 index outside

/-- Updating either post-generator signal leaves the common auxiliary
boundary invariant.  The signal value itself is deliberately unrestricted by
that boundary. -/
theorem historyTaylorPostGeneratorStablePredicate_xorSignal
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (signal : Fin qubits)
    (signalMember : signal ∈
      [layout.coefficientSignal, layout.orderBoundarySignal])
    (value : Bool) (basis : QubitBasis qubits)
    (inside : historyTaylorPostGeneratorStablePredicate layout basis) :
    historyTaylorPostGeneratorStablePredicate layout
      (xorWire signal value basis) := by
  have separated := layout.postGeneratorSignal_separated signal signalMember
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [xorWire_apply_other signal (historyBranchWire layout)]
    · exact inside.1.trans (by
        apply littleEndianRegisterEqualsNat_congr
        intro wire member
        simp only [historyRegisterWires, List.mem_ofFn] at member
        rcases member with ⟨index, rfl⟩
        exact (xorWire_apply_other signal (layout.selector.wire index)
          (separated.1 index) _ _).symm)
    · intro equal
      have member : historyBranchWire layout ∈
          historyRegisterWires layout.workspace :=
        historyBranchWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨index, member⟩
      exact separated.2.2 index (member.trans equal)
  · rw [xorWire_apply_other signal (historyLessThanTimeWire layout)]
    · rw [inside.2.1]
      unfold historyTaylorClockLessThanTimeValue
      apply congrArg₂ unsignedLessThanBits
      · funext index
        exact (xorWire_apply_other signal (layout.clock.wire index)
          (separated.2.1 index) _ _).symm
      · rfl
    · intro equal
      have member := historyLessThanTimeWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨index, member⟩
      exact separated.2.2 index (member.trans equal)
  · rw [xorWire_apply_other signal (historyLessThanIdleEndWire layout)]
    · rw [inside.2.2.1]
      unfold historyTaylorClockLessThanIdleEndValue
      apply congrArg₂ unsignedLessThanBits
      · funext index
        exact (xorWire_apply_other signal (layout.clock.wire index)
          (separated.2.1 index) _ _).symm
      · rfl
    · intro equal
      have member := historyLessThanIdleEndWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨index, member⟩
      exact separated.2.2 index (member.trans equal)
  · intro index outside
    rw [xorWire_apply_other signal (layout.workspace.wire index)]
    · exact inside.2.2.2 index outside
    · exact separated.2.2 index

/-- The independent invalid-clock action preserves the common post-generator
auxiliary boundary. -/
theorem historyTaylorInvalidClockBasisAction_maps_stable
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits)
    (inside : historyTaylorPostGeneratorStablePredicate layout basis) :
    historyTaylorPostGeneratorStablePredicate layout
      (historyTaylorInvalidClockBasisAction layout basis) := by
  exact historyTaylorPostGeneratorStablePredicate_xorSignal
    layout layout.coefficientSignal (by simp)
    (historyTaylorInvalidClockCondition layout basis) basis inside

/-- The independently stated physical-Taylor order-boundary action changes
only its reserved signal and therefore preserves the common post boundary. -/
theorem historyTaylorOrderBoundaryBasisAction_maps_stable
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits)
    (inside : historyTaylorPostGeneratorStablePredicate layout basis) :
    historyTaylorPostGeneratorStablePredicate layout
      (historyTaylorOrderBoundaryBasisAction layout basis) := by
  exact historyTaylorPostGeneratorStablePredicate_xorSignal
    layout layout.orderBoundarySignal (by simp)
    (historyTaylorOrderBoundaryCondition layout basis) basis inside

/-- The independently stated idling-block boundary action changes the same
reserved signal and preserves the common post boundary. -/
theorem historyTaylorIdleBoundaryBasisAction_maps_stable
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits)
    (inside : historyTaylorPostGeneratorStablePredicate layout basis) :
    historyTaylorPostGeneratorStablePredicate layout
      (historyTaylorIdleBoundaryBasisAction layout basis) := by
  exact historyTaylorPostGeneratorStablePredicate_xorSignal
    layout layout.orderBoundarySignal (by simp)
    (historyTaylorIdleBoundaryCondition layout basis) basis inside

/-- Predicate-controlled degree increment changes only the typed order
register and therefore preserves the common post-generator stable boundary. -/
theorem historyTaylorDegreeIncrementBasisAction_maps_stable
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits)
    (inside : historyTaylorPostGeneratorStablePredicate layout basis) :
    historyTaylorPostGeneratorStablePredicate layout
      (historyTaylorDegreeIncrementBasisAction layout basis) := by
  let output := historyTaylorDegreeIncrementBasisAction layout basis
  have outsideOrder (wire : Fin qubits)
      (outside : ∀ index, wire ≠ layout.order.wire index) :
      output wire = basis wire := by
    exact predicateControlledAddMod2PowBasisAction_apply_outside
      (historyTaylorDegreeIncrementCondition layout) layout.order 1 basis wire
      outside
  refine ⟨?_, ?_, ?_, ?_⟩
  · change output (historyBranchWire layout) = _
    rw [outsideOrder (historyBranchWire layout)]
    · rw [inside.1]
      apply littleEndianRegisterEqualsNat_congr
      intro wire member
      simp only [historyRegisterWires, List.mem_ofFn] at member
      rcases member with ⟨index, rfl⟩
      change basis (layout.selector.wire index) =
        output (layout.selector.wire index)
      exact (outsideOrder (layout.selector.wire index) (by
        intro orderIndex equal
        exact (layout.orderWire_separated orderIndex).1 index equal.symm)).symm
    · intro orderIndex equal
      have member := historyBranchWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (member.trans equal).symm
  · change output (historyLessThanTimeWire layout) = _
    rw [outsideOrder (historyLessThanTimeWire layout)]
    · rw [inside.2.1]
      unfold historyTaylorClockLessThanTimeValue
      apply congrArg₂ unsignedLessThanBits
      · funext clockIndex
        exact (outsideOrder (layout.clock.wire clockIndex) (by
          intro orderIndex equal
          exact (layout.orderWire_separated orderIndex).2.1 clockIndex
            equal.symm)).symm
      · rfl
    · intro orderIndex equal
      have member := historyLessThanTimeWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (member.trans equal).symm
  · change output (historyLessThanIdleEndWire layout) = _
    rw [outsideOrder (historyLessThanIdleEndWire layout)]
    · rw [inside.2.2.1]
      unfold historyTaylorClockLessThanIdleEndValue
      apply congrArg₂ unsignedLessThanBits
      · funext clockIndex
        exact (outsideOrder (layout.clock.wire clockIndex) (by
          intro orderIndex equal
          exact (layout.orderWire_separated orderIndex).2.1 clockIndex
            equal.symm)).symm
      · rfl
    · intro orderIndex equal
      have member := historyLessThanIdleEndWire_mem_workspace layout
      rcases List.mem_ofFn.mp member with ⟨workspaceIndex, member⟩
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        (member.trans equal).symm
  · intro workspaceIndex outside
    change output (layout.workspace.wire workspaceIndex) = false
    rw [outsideOrder (layout.workspace.wire workspaceIndex)]
    · exact inside.2.2.2 workspaceIndex outside
    · intro orderIndex equal
      exact (layout.orderWire_separated orderIndex).2.2.2 workspaceIndex
        equal.symm

/-- Pure P40 phase transition, independent of its compiler circuit. -/
theorem historyTaylorSelectorEqualityBasisAction_maps_phase
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAuxiliaryBoundaryPredicate layout input) :
    historyTaylorAfterSelectorPredicate layout
      (historyTaylorSelectorEqualityBasisAction layout input) := by
  let value := littleEndianRegisterEqualsNat
    (historyRegisterWires layout.selector) 1 input
  have branchZero : input (historyBranchWire layout) = false :=
    historyTaylorAuxiliaryBoundaryPredicate_apply_of_mem layout input inside
      (historyBranchWire layout) (historyBranchWire_mem_workspace layout)
  constructor
  · unfold historyTaylorSelectorEqualityBasisAction
    rw [ClassicalReversibleStage.equalityToConstantDirectBasisAction_apply_target,
      branchZero]
    simp only [Bool.false_bne]
    unfold ClassicalReversibleStage.equalityToConstantDirectBasisAction
    rw [layout.selectorEqualsNat_xorWire_workspace
      (historyBranchWire layout) (historyBranchWire_mem_workspace layout)]
  · have empty : historyTaylorWorkspaceZeroExcept layout [] input := by
      intro index _
      exact inside index
    simpa [historyTaylorSelectorEqualityBasisAction,
      ClassicalReversibleStage.equalityToConstantDirectBasisAction] using
      historyTaylorWorkspaceZeroExcept_xorWire_append layout []
        (historyBranchWire layout) value input empty

/-- Pure first-P41 phase transition. -/
theorem historyTaylorTimeComparisonBasisAction_maps_phase
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAfterSelectorPredicate layout input) :
    historyTaylorAfterTimeComparisonPredicate layout
      (historyTaylorTimeComparisonBasisAction layout input) := by
  let target := historyLessThanTimeWire layout
  let value := historyTaylorClockLessThanTimeValue layout input
  have targetZero : input target = false :=
    historyTaylorWorkspaceZeroExcept_apply_of_mem layout
      [historyBranchWire layout] input inside.2 target
      (historyLessThanTimeWire_mem_workspace layout) (by
        intro member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        exact historyBranchWire_ne_lessThanTimeWire layout member.symm)
  refine ⟨?_, ?_, ?_⟩
  · unfold historyTaylorTimeComparisonBasisAction
    rw [xorWire_apply_other _ (historyBranchWire layout)
      (historyBranchWire_ne_lessThanTimeWire layout), inside.1]
    rw [layout.selectorEqualsNat_xorWire_workspace target
      (historyLessThanTimeWire_mem_workspace layout)]
  · unfold historyTaylorTimeComparisonBasisAction
    rw [xorWire_apply_same, targetZero]
    simp only [Bool.false_bne]
    unfold historyTaylorClockLessThanTimeValue
    rw [layout.clock_read_xorWire_workspace target
      (historyLessThanTimeWire_mem_workspace layout)]
  · simpa [historyTaylorTimeComparisonBasisAction, target, value] using
      historyTaylorWorkspaceZeroExcept_xorWire_append layout
        [historyBranchWire layout] target value input inside.2

/-- Pure second-P41 phase transition. -/
theorem historyTaylorIdleEndComparisonBasisAction_maps_phase
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAfterTimeComparisonPredicate layout input) :
    historyTaylorAfterIdleEndComparisonPredicate layout
      (historyTaylorIdleEndComparisonBasisAction layout input) := by
  let target := historyLessThanIdleEndWire layout
  let value := historyTaylorClockLessThanIdleEndValue layout input
  have targetZero : input target = false :=
    historyTaylorWorkspaceZeroExcept_apply_of_mem layout
      [historyBranchWire layout, historyLessThanTimeWire layout]
      input inside.2.2 target (historyLessThanIdleEndWire_mem_workspace layout)
      (by
        intro member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with equal | equal
        · exact historyBranchWire_ne_lessThanIdleEndWire layout equal.symm
        · exact historyLessThanTimeWire_ne_lessThanIdleEndWire layout equal.symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold historyTaylorIdleEndComparisonBasisAction
    rw [xorWire_apply_other _ (historyBranchWire layout)
      (historyBranchWire_ne_lessThanIdleEndWire layout), inside.1]
    rw [layout.selectorEqualsNat_xorWire_workspace target
      (historyLessThanIdleEndWire_mem_workspace layout)]
  · unfold historyTaylorIdleEndComparisonBasisAction
    rw [xorWire_apply_other _ (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_ne_lessThanIdleEndWire layout), inside.2.1]
    unfold historyTaylorClockLessThanTimeValue
    rw [layout.clock_read_xorWire_workspace target
      (historyLessThanIdleEndWire_mem_workspace layout)]
  · unfold historyTaylorIdleEndComparisonBasisAction
    rw [xorWire_apply_same, targetZero]
    simp only [Bool.false_bne]
    unfold historyTaylorClockLessThanIdleEndValue
    rw [layout.clock_read_xorWire_workspace target
      (historyLessThanIdleEndWire_mem_workspace layout)]
  · simpa [historyTaylorIdleEndComparisonBasisAction, target, value] using
      historyTaylorWorkspaceZeroExcept_xorWire_append layout
        [historyBranchWire layout, historyLessThanTimeWire layout]
        target value input inside.2.2

/-- Pure P43 phase transition to the unique controlled-Q10 boundary. -/
theorem historyTaylorActiveConjunctionBasisAction_maps_phase
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorAfterIdleEndComparisonPredicate layout input) :
    historyTaylorBeforeGeneratorBoundaryPredicate layout
      (historyTaylorActiveConjunctionBasisAction layout input) := by
  let active := historyActiveWire layout
  let live := [historyBranchWire layout, historyLessThanTimeWire layout,
    historyLessThanIdleEndWire layout]
  let value := ClassicalReversibleStage.allWiresTrue
    [historyBranchWire layout, historyLessThanTimeWire layout] input
  have activeZero : input active = false :=
    historyTaylorWorkspaceZeroExcept_apply_of_mem layout live input
      inside.2.2.2 active (historyActiveWire_mem_workspace layout) (by
        change historyActiveWire layout ∉
          [historyBranchWire layout, historyLessThanTimeWire layout,
            historyLessThanIdleEndWire layout]
        intro member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with equal | equal | equal
        · exact historyBranchWire_ne_activeWire layout equal.symm
        · exact historyLessThanTimeWire_ne_activeWire layout equal.symm
        · exact historyLessThanIdleEndWire_ne_activeWire layout equal.symm)
  have zeroFour : historyTaylorWorkspaceZeroExcept layout
      (historyTaylorBeforeGeneratorLiveWires layout)
      (historyTaylorActiveConjunctionBasisAction layout input) := by
    simpa [historyTaylorActiveConjunctionBasisAction,
      ClassicalReversibleStage.conjunctionDirectBasisAction,
      historyTaylorBeforeGeneratorLiveWires, live, active, value] using
      historyTaylorWorkspaceZeroExcept_xorWire_append layout live active value
        input inside.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold historyTaylorActiveConjunctionBasisAction
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other _ _
      (historyBranchWire layout) (historyBranchWire_ne_activeWire layout),
      inside.1]
    unfold ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [layout.selectorEqualsNat_xorWire_workspace active
      (historyActiveWire_mem_workspace layout)]
  · unfold historyTaylorActiveConjunctionBasisAction
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other _ _
      (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_ne_activeWire layout), inside.2.1]
    unfold historyTaylorClockLessThanTimeValue
    unfold ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [layout.clock_read_xorWire_workspace active
      (historyActiveWire_mem_workspace layout)]
  · unfold historyTaylorActiveConjunctionBasisAction
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other _ _
      (historyLessThanIdleEndWire layout)
      (historyLessThanIdleEndWire_ne_activeWire layout), inside.2.2.1]
    unfold historyTaylorClockLessThanIdleEndValue
    unfold ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [layout.clock_read_xorWire_workspace active
      (historyActiveWire_mem_workspace layout)]
  · unfold historyTaylorActiveConjunctionBasisAction
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target,
      activeZero,
      ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other _ _
        (historyBranchWire layout) (historyBranchWire_ne_activeWire layout),
      ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other _ _
        (historyLessThanTimeWire layout)
        (historyLessThanTimeWire_ne_activeWire layout)]
    simp [ClassicalReversibleStage.allWiresTrue,
      ClassicalReversibleStage.readWires]
  · apply historyTaylorWorkspaceZeroExcept_mono layout
      (historyTaylorBeforeGeneratorLiveWires layout)
      (historyTaylorBeforeGeneratorLiveWires layout ++
        historyTaylorControlledQ10OwnedWorkspaceWires layout)
      _ (fun wire member => List.mem_append_left _ member) zeroFour

/-- Reapplying the same P43 direct action after controlled-Q10 removes the
active flag and reaches the stable post-generator boundary. -/
theorem historyTaylorActiveConjunctionBasisAction_unmaps_phase
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (input : QubitBasis qubits)
    (inside : historyTaylorBeforeGeneratorBoundaryPredicate layout input) :
    historyTaylorPostGeneratorStablePredicate layout
      (historyTaylorActiveConjunctionBasisAction layout input) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold historyTaylorActiveConjunctionBasisAction
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other _ _
      (historyBranchWire layout) (historyBranchWire_ne_activeWire layout),
      inside.1]
    unfold ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [layout.selectorEqualsNat_xorWire_workspace
      (historyActiveWire layout) (historyActiveWire_mem_workspace layout)]
  · unfold historyTaylorActiveConjunctionBasisAction
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other _ _
      (historyLessThanTimeWire layout)
      (historyLessThanTimeWire_ne_activeWire layout), inside.2.1]
    unfold historyTaylorClockLessThanTimeValue
    unfold ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [layout.clock_read_xorWire_workspace
      (historyActiveWire layout) (historyActiveWire_mem_workspace layout)]
  · unfold historyTaylorActiveConjunctionBasisAction
    rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other _ _
      (historyLessThanIdleEndWire layout)
      (historyLessThanIdleEndWire_ne_activeWire layout), inside.2.2.1]
    unfold historyTaylorClockLessThanIdleEndValue
    unfold ClassicalReversibleStage.conjunctionDirectBasisAction
    rw [layout.clock_read_xorWire_workspace
      (historyActiveWire layout) (historyActiveWire_mem_workspace layout)]
  · intro index outside
    by_cases activeEqual : layout.workspace.wire index = historyActiveWire layout
    · unfold historyTaylorActiveConjunctionBasisAction
      rw [activeEqual,
        ClassicalReversibleStage.conjunctionDirectBasisAction_apply_target,
        inside.2.2.2.1]
      simp [ClassicalReversibleStage.allWiresTrue,
        ClassicalReversibleStage.readWires]
    · unfold historyTaylorActiveConjunctionBasisAction
      rw [ClassicalReversibleStage.conjunctionDirectBasisAction_apply_other _ _
        (layout.workspace.wire index) activeEqual]
      apply inside.2.2.2.2 index
      intro member
      apply outside
      rcases List.mem_append.mp member with live | owned
      · simp only [historyTaylorBeforeGeneratorLiveWires, List.mem_cons,
          List.not_mem_nil, or_false] at live
        rcases live with live | live | live | live
        · exact List.mem_append_left _ (by simp [live])
        · exact List.mem_append_left _ (by simp [live])
        · exact List.mem_append_left _ (by simp [live])
        · exact (activeEqual live).elim
      · exact List.mem_append_right _ owned

theorem historyControlledWork_wire_mem_workspace
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (index : Fin 2) :
    (historyControlledWork layout).wire index ∈
      historyRegisterWires layout.workspace := by
  unfold historyControlledWork
  apply historyWorkspaceSlice_wire_mem

/-- P14の2-wire selector preparationを規定するsymbolic angle/layout。 -/
structure HistorySelectorPreparationParameters (qubits : Nat) where
  low : Fin qubits
  high : Fin qubits
  different : high ≠ low
  firstHighAngle : AngleExpr
  firstLowAngle : AngleExpr
  secondLowAngle : AngleExpr

/-- The frozen P14 placement on the two-wire history selector register. -/
def historySelectorPreparationParametersAtLayout
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (firstHighAngle firstLowAngle secondLowAngle : AngleExpr) :
    HistorySelectorPreparationParameters qubits where
  low := layout.selector.wire ⟨0, by decide⟩
  high := layout.selector.wire ⟨1, by decide⟩
  different := by
    intro equal
    have indexEqual := layout.selector.injective equal
    have differentIndices : (⟨1, by decide⟩ : Fin 2) ≠ ⟨0, by decide⟩ := by
      decide
    exact differentIndices indexEqual
  firstHighAngle := firstHighAngle
  firstLowAngle := firstLowAngle
  secondLowAngle := secondLowAngle

/-- The first zero-control P50 occurrence in the frozen two-wire gray-code
selector preparation. -/
noncomputable def historySelectorHighRotationOperator {qubits : Nat}
    (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    Operator (QubitBasis qubits) :=
  embedSingleQubitOperator parameters.high
    (localRy (parameters.firstHighAngle.eval symbolValue))

/-- The second P50 occurrence: the source-faithful one-control Ry expansion
`Ry; CNOT; Ry; CNOT`.  This strict recorded target does not assume that the
two recorded half-angle expressions are ideal negatives. -/
noncomputable def historySelectorLowControlledRotationRecordedOperator
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    Operator (QubitBasis qubits) :=
  operatorSequence [
    embedSingleQubitOperator parameters.low
      (localRy (parameters.firstLowAngle.eval symbolValue)),
    analyticCnotOperator parameters.high parameters.low,
    embedSingleQubitOperator parameters.low
      (localRy (parameters.secondLowAngle.eval symbolValue)),
    analyticCnotOperator parameters.high parameters.low]

/-- P14の5段recorded selector preparationに対応する独立作用素。 -/
noncomputable def historySelectorPreparationOperator {qubits : Nat}
    (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    Operator (QubitBasis qubits) :=
  operatorSequence [
    embedSingleQubitOperator parameters.high
      (localRy (parameters.firstHighAngle.eval symbolValue)),
    embedSingleQubitOperator parameters.low
      (localRy (parameters.firstLowAngle.eval symbolValue)),
    analyticCnotOperator parameters.high parameters.low,
    embedSingleQubitOperator parameters.low
      (localRy (parameters.secondLowAngle.eval symbolValue)),
    analyticCnotOperator parameters.high parameters.low]

/-- The two selector wires are the complete change-support of H1.  Reading a
control does not add a changed wire to this support. -/
def historySelectorPreparationSupport {qubits : Nat}
    (parameters : HistorySelectorPreparationParameters qubits) :
    Finset (Fin qubits) :=
  {parameters.high, parameters.low}

@[simp] theorem historySelectorPreparationParametersAtLayout_support
    {qubits dataWidth generatorSignalWidth workspaceWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      workspaceWidth parameters)
    (firstHighAngle firstLowAngle secondLowAngle : AngleExpr) :
    historySelectorPreparationSupport
        (historySelectorPreparationParametersAtLayout layout
          firstHighAngle firstLowAngle secondLowAngle) =
      ({layout.selector.wire 0, layout.selector.wire 1} :
        Finset (Fin qubits)) := by
  ext wire
  simp [historySelectorPreparationSupport,
    historySelectorPreparationParametersAtLayout, or_comm]

/-- The independent P14 target is the source-order composition of its two P50
rotation-emitter occurrences. -/
theorem historySelectorPreparationOperator_eq_rotationChildren
    {qubits : Nat} (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    historySelectorPreparationOperator symbolValue parameters =
      operatorSequence [
        historySelectorHighRotationOperator symbolValue parameters,
        historySelectorLowControlledRotationRecordedOperator
          symbolValue parameters] := by
  unfold historySelectorPreparationOperator
  unfold historySelectorHighRotationOperator
  unfold historySelectorLowControlledRotationRecordedOperator
  rw [show ([
      embedSingleQubitOperator parameters.high
        (localRy (parameters.firstHighAngle.eval symbolValue)),
      embedSingleQubitOperator parameters.low
        (localRy (parameters.firstLowAngle.eval symbolValue)),
      analyticCnotOperator parameters.high parameters.low,
      embedSingleQubitOperator parameters.low
        (localRy (parameters.secondLowAngle.eval symbolValue)),
      analyticCnotOperator parameters.high parameters.low] :
        List (Operator (QubitBasis qubits))) =
      [embedSingleQubitOperator parameters.high
        (localRy (parameters.firstHighAngle.eval symbolValue))] ++ [
      embedSingleQubitOperator parameters.low
        (localRy (parameters.firstLowAngle.eval symbolValue)),
      analyticCnotOperator parameters.high parameters.low,
      embedSingleQubitOperator parameters.low
        (localRy (parameters.secondLowAngle.eval symbolValue)),
      analyticCnotOperator parameters.high parameters.low] by rfl]
  rw [operatorSequence_append]
  simp [operatorSequence]

/-- P14逆実行の独立targetはrecorded targetの随伴。 -/
noncomputable def historySelectorPreparationInverseOperator {qubits : Nat}
    (symbolValue : String → ℝ)
    (parameters : HistorySelectorPreparationParameters qubits) :
    Operator (QubitBasis qubits) :=
  Matrix.conjTranspose (historySelectorPreparationOperator symbolValue parameters)

/-- P15でP17の前後に現れる補助stage family。 -/
inductive HistoryTaylorAuxStageFamily where
  | selectorEquality
  | clockPredicate
  | orderBoundaryPredicate
  | controlledLogic
  | orderIncrement
  | coefficientEquality
  | coefficientRotation
  | idlingCoefficientRotation
  deriving DecidableEq, Repr

/-- Shared semantic leaf contract used by one P15 auxiliary stage.  These
names are application-independent; stable P identifiers are attached only by
the catalog layer. -/
inductive HistoryTaylorAuxLeafContract where
  | equality
  | lessThan
  | controlledIncrement
  | conjunction
  | controlledRotation
  deriving DecidableEq, Repr

/-- P15のP17以外の一段を、family tagと独立作用素で表す。 -/
structure HistoryTaylorAuxStageSpec
    (basis : Type*) [Fintype basis] [DecidableEq basis] where
  family : HistoryTaylorAuxStageFamily
  leafContract : HistoryTaylorAuxLeafContract
  target : Operator basis
  cleanTarget : Operator basis

/--
P16 固有の constant comparison target。dirty rhs register を隠さず、constant XOR、
full-dirty register comparator、同じ XOR の三作用素積として定義する。
-/
noncomputable def historyLessThanConstantOperator {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat) :
    Operator (QubitBasis qubits) :=
  let xorTarget :=
    (ClassicalReversibleStage.xorConstant
      (List.ofFn spec.rhs.wire) constant).analyticOperator
  operatorSequence [xorTarget, unsignedLessThanXorDirtyOperator spec, xorTarget]

/-- Human-facing clean action of one frozen constant-comparison occurrence.
The temporary rhs mask register is absent from this definition: it only reads
the lhs word and XORs the target by the fixed-width predicate `lhs < constant`.
This is the extensional specification that the recorded mask--compare--unmask
word must implement when rhs and borrow enter at zero. -/
def historyLessThanConstantDirectBasisAction {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat)
    (input : QubitBasis qubits) : QubitBasis qubits :=
  xorWire spec.target
    (unsignedLessThanBits (spec.lhs.read input)
      (fun index => constant.testBit index.val)) input

/-- Direct deterministic operator corresponding to
`historyLessThanConstantDirectBasisAction`. -/
noncomputable def historyLessThanConstantDirectOperator {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat) :
    Operator (QubitBasis qubits) :=
  deterministicOperator (historyLessThanConstantDirectBasisAction spec constant)

/-- Clean entry boundary for a constant comparison: both the ripple borrow
and the temporary rhs mask register are zero. -/
def historyLessThanConstantCleanInputPredicate {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width)
    (input : QubitBasis qubits) : Prop :=
  (∀ index, spec.borrow.read input index = false) ∧
    ∀ index, spec.rhs.read input index = false

/-- Clean exit boundary is definitionally the same zero-work condition. -/
abbrev historyLessThanConstantCleanOutputPredicate {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) :
    QubitBasis qubits → Prop :=
  historyLessThanConstantCleanInputPredicate spec

/-- Frozen P16 idle-wrap transformation.  The order register receives the
all-ones XOR selected by the clean `active` flag, and the same flag controls
the recorded coefficient rotation. -/
noncomputable def historyIdleTransformOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (active_ne_coefficient :
      historyActiveWire layout ≠ layout.coefficientSignal)
    (angle : ℝ) : Operator (QubitBasis qubits) :=
  let idleConjunction :=
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyIdleFlag layout] []
      (historyActiveWire layout)).analyticOperator
  let orderAllOnesXor := operatorSequence
    ((historyRegisterWires layout.order).map fun target =>
      reversibleAnalyticCnotOperator (historyActiveWire layout) target)
  operatorSequence [
    reversibleAnalyticCnotOperator
      (historyLessThanIdleEndWire layout) (historyIdleFlag layout),
    reversibleAnalyticCnotOperator
      (historyLessThanTimeWire layout) (historyIdleFlag layout),
    idleConjunction,
    orderAllOnesXor,
    embedControlledSingleQubitOperator (historyActiveWire layout)
      layout.coefficientSignal active_ne_coefficient (localRy angle),
    idleConjunction,
    reversibleAnalyticCnotOperator
      (historyLessThanTimeWire layout) (historyIdleFlag layout),
    reversibleAnalyticCnotOperator
      (historyLessThanIdleEndWire layout) (historyIdleFlag layout)]

/-- Frozen P16 degree-zero projector stage.  Equality and conjunction work are
computed, used once, and uncomputed in the exact source order. -/
noncomputable def historyProjectorControlOperator
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) :
    Operator (QubitBasis qubits) :=
  let degreeZeroEquality :=
    (ClassicalReversibleStage.xorEqualityToConstantIntoTargetMinimumWork
      (historyRegisterWires layout.order)
      (historyRegisterWires (historyEqualityWork layout)) 0
      (historyEqualityFlag layout)).analyticOperator
  let projectorConjunction :=
    (ClassicalReversibleStage.xorConjunctionIntoTargetMinimumWork
      [historyBranchWire layout, historyEqualityFlag layout] []
      (historyCoefficientControl layout)).analyticOperator
  operatorSequence [
    reversibleAnalyticCnotOperator
      (historyBranchWire layout) layout.projectorSignal,
    degreeZeroEquality,
    projectorConjunction,
    reversibleAnalyticCnotOperator
      (historyCoefficientControl layout) layout.projectorSignal,
    projectorConjunction,
    degreeZeroEquality]

/-- Both temporary projector work flags are zero at the I06 boundary. -/
def historyProjectorControlCleanPredicate
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters)
    (basis : QubitBasis qubits) : Prop :=
  basis (historyEqualityFlag layout) = false ∧
    basis (historyCoefficientControl layout) = false

end SpectralSamplingProof.Analytic
