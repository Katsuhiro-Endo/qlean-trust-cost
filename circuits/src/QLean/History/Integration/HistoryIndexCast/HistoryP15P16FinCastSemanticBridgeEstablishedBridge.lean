import QLean.History.Integration.HistoryRawSchema.HistoryP15P16EvidenceDerivation
import QLean.History.Integration.IndexedHistoryProvider.HistoryProviderIndexedChildEstablishedBridge

set_option autoImplicit false

namespace HistoryIndexCast

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open HistoryAnalyticParameterExistence194
open HistoryRawSchema

theorem raw_clock_wire_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (layout203 raw admissible).clock.wire = raw.clockWire := by
  rfl

theorem raw_order_wire_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (layout203 raw admissible).order.wire = raw.orderWire := by
  rfl

theorem raw_bound_wire_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (historyBoundRegister (layout203 raw admissible)).wire =
      rawBoundWire203 raw := by
  funext index
  apply Fin.ext
  rfl

theorem raw_borrow_wire_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (historyBorrowRegister (layout203 raw admissible)).wire =
      rawBorrowWire203 raw := by
  funext index
  apply Fin.ext
  rfl

theorem raw_order_bound_wire_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (historyOrderBoundRegister (layout203 raw admissible)).wire =
      rawOrderBoundWire203 raw := by
  funext index
  apply Fin.ext
  rfl

theorem raw_order_masked_wire_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (historyOrderMaskedConstantRegister (layout203 raw admissible)).wire =
      rawOrderMaskedWire203 raw := by
  funext index
  apply Fin.ext
  rfl

theorem raw_clock_less_than_time_wire_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    historyLessThanTimeWire (layout203 raw admissible) =
      rawLessThanTimeWire203 raw := by
  apply Fin.ext
  rfl

theorem raw_clock_less_than_idle_end_wire_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    historyLessThanIdleEndWire (layout203 raw admissible) =
      rawLessThanIdleEndWire203 raw := by
  apply Fin.ext
  rfl

theorem raw_equality_flag_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    historyEqualityFlag (layout203 raw admissible) =
      rawEqualityFlag203 raw := by
  apply Fin.ext
  rfl

theorem raw_coefficient_control_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    historyCoefficientControl (layout203 raw admissible) =
      rawCoefficientControl203 raw := by
  apply Fin.ext
  rfl

theorem raw_idle_flag_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    historyIdleFlag (layout203 raw admissible) =
      rawIdleFlag203 raw := by
  apply Fin.ext
  rfl

theorem raw_order_carry_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    historyOrderIncrementCarry (layout203 raw admissible) =
      rawOrderCarry203 raw := by
  apply Fin.ext
  rfl

theorem raw_active_wire_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    historyActiveWire (layout203 raw admissible) =
      rawActiveWire203 raw := by
  apply Fin.ext
  rfl

theorem raw_clock_carry_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    historyClockIncrementCarry (layout203 raw admissible) =
      rawClockCarry203 raw := by
  apply Fin.ext
  rfl

theorem raw_branch_wire_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    historyBranchWire (layout203 raw admissible) =
      rawBranchWire203 raw := by
  apply Fin.ext
  rfl

theorem raw_coefficient_signal_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (layout203 raw admissible).coefficientSignal = raw.coefficientSignal := by
  rfl

theorem raw_order_boundary_signal_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (layout203 raw admissible).orderBoundarySignal = raw.orderBoundarySignal := by
  rfl

theorem raw_projector_signal_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (layout203 raw admissible).projectorSignal = raw.projectorSignal := by
  rfl

theorem raw_uniform_work_zero_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (historyUniformControlWork (layout203 raw admissible)).wire 0 =
      raw.workspaceWire ⟨0, by unfold rawWorkspaceWidth203; omega⟩ := by
  apply Fin.ext
  rfl

theorem raw_uniform_work_one_eq
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (historyUniformControlWork (layout203 raw admissible)).wire 1 =
      raw.workspaceWire ⟨1, by unfold rawWorkspaceWidth203; omega⟩ := by
  apply Fin.ext
  rfl

theorem raw_order_accumulator_wire_eq_early
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (historyOrderAccumulatorRegister (layout203 raw admissible)).wire =
      raw.orderWire := by
  funext index
  apply Fin.ext
  rfl

theorem raw_order_addend_wire_eq_early
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (historyOrderIncrementAddendRegister (layout203 raw admissible)).wire =
      rawOrderIncrementAddend203 raw := by
  funext index
  apply Fin.ext
  rfl

theorem raw_clock_accumulator_wire_eq_early
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (historyClockAccumulatorRegister (layout203 raw admissible)).wire =
      raw.clockWire := by
  funext index
  apply Fin.ext
  rfl

theorem raw_clock_addend_wire_eq_early
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    (historyClockMaskedConstantRegister (layout203 raw admissible)).wire =
      rawClockIncrementAddend203 raw := by
  funext index
  apply Fin.ext
  rfl

theorem clock_time_less_than_evidence207
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryTaylorLessThanEvidence
      (layout203 raw admissible).clock
      (historyBoundRegister (layout203 raw admissible))
      (historyBorrowRegister (layout203 raw admissible))
      (historyLessThanTimeWire (layout203 raw admissible)) := by
  let source := admissible.clockTimeLessThan
  exact {
    widthPositive := source.widthPositive
    lhsRhsDifferent := by
      intro left right
      simpa only [raw_clock_wire_eq raw admissible,
        raw_bound_wire_eq raw admissible, raw_borrow_wire_eq raw admissible]
        using source.lhsRhsDifferent left right
    lhsBorrowDifferent := by
      intro left right
      simpa only [raw_clock_wire_eq raw admissible,
        raw_bound_wire_eq raw admissible, raw_borrow_wire_eq raw admissible]
        using source.lhsBorrowDifferent left right
    rhsBorrowDifferent := by
      intro left right
      simpa only [raw_clock_wire_eq raw admissible,
        raw_bound_wire_eq raw admissible, raw_borrow_wire_eq raw admissible]
        using source.rhsBorrowDifferent left right
    targetLhsDifferent := by
      intro index
      simpa only [raw_clock_less_than_time_wire_eq raw admissible,
        raw_clock_wire_eq raw admissible, raw_bound_wire_eq raw admissible]
        using source.targetLhsDifferent index
    targetRhsDifferent := by
      intro index
      simpa only [raw_clock_less_than_time_wire_eq raw admissible,
        raw_bound_wire_eq raw admissible]
        using source.targetRhsDifferent index
    targetBorrowDifferent := by
      intro index
      simpa only [raw_clock_less_than_time_wire_eq raw admissible,
        raw_clock_wire_eq raw admissible, raw_borrow_wire_eq raw admissible]
        using source.targetBorrowDifferent index }

theorem clock_idle_end_less_than_evidence207
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryTaylorLessThanEvidence
      (layout203 raw admissible).clock
      (historyBoundRegister (layout203 raw admissible))
      (historyBorrowRegister (layout203 raw admissible))
      (historyLessThanIdleEndWire (layout203 raw admissible)) := by
  let source := admissible.clockIdleEndLessThan
  exact {
    widthPositive := source.widthPositive
    lhsRhsDifferent := by
      intro left right
      simpa only [raw_clock_wire_eq raw admissible,
        raw_bound_wire_eq raw admissible, raw_borrow_wire_eq raw admissible]
        using source.lhsRhsDifferent left right
    lhsBorrowDifferent := by
      intro left right
      simpa only [raw_clock_wire_eq raw admissible,
        raw_bound_wire_eq raw admissible, raw_borrow_wire_eq raw admissible]
        using source.lhsBorrowDifferent left right
    rhsBorrowDifferent := by
      intro left right
      simpa only [raw_clock_wire_eq raw admissible,
        raw_bound_wire_eq raw admissible, raw_borrow_wire_eq raw admissible]
        using source.rhsBorrowDifferent left right
    targetLhsDifferent := by
      intro index
      simpa only [raw_clock_less_than_idle_end_wire_eq raw admissible,
        raw_clock_wire_eq raw admissible, raw_bound_wire_eq raw admissible]
        using source.targetLhsDifferent index
    targetRhsDifferent := by
      intro index
      simpa only [raw_clock_less_than_idle_end_wire_eq raw admissible,
        raw_bound_wire_eq raw admissible]
        using source.targetRhsDifferent index
    targetBorrowDifferent := by
      intro index
      simpa only [raw_clock_less_than_idle_end_wire_eq raw admissible,
        raw_clock_wire_eq raw admissible, raw_borrow_wire_eq raw admissible]
        using source.targetBorrowDifferent index }

theorem degree_order_less_than_evidence207
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryTaylorLessThanEvidence
      (layout203 raw admissible).order
      (historyOrderBoundRegister (layout203 raw admissible))
      (historyOrderMaskedConstantRegister (layout203 raw admissible))
      (historyEqualityFlag (layout203 raw admissible)) := by
  let source := admissible.degreeOrderLessThan
  exact {
    widthPositive := source.widthPositive
    lhsRhsDifferent := by
      intro left right
      simpa only [raw_order_wire_eq raw admissible,
        raw_order_bound_wire_eq raw admissible, raw_order_masked_wire_eq raw admissible]
        using source.lhsRhsDifferent left right
    lhsBorrowDifferent := by
      intro left right
      simpa only [raw_order_wire_eq raw admissible,
        raw_order_bound_wire_eq raw admissible, raw_order_masked_wire_eq raw admissible]
        using source.lhsBorrowDifferent left right
    rhsBorrowDifferent := by
      intro left right
      simpa only [raw_order_wire_eq raw admissible,
        raw_order_bound_wire_eq raw admissible, raw_order_masked_wire_eq raw admissible]
        using source.rhsBorrowDifferent left right
    targetLhsDifferent := by
      intro index
      simpa only [raw_equality_flag_eq raw admissible,
        raw_order_wire_eq raw admissible, raw_order_bound_wire_eq raw admissible]
        using source.targetLhsDifferent index
    targetRhsDifferent := by
      intro index
      simpa only [raw_equality_flag_eq raw admissible,
        raw_order_bound_wire_eq raw admissible]
        using source.targetRhsDifferent index
    targetBorrowDifferent := by
      intro index
      simpa only [raw_equality_flag_eq raw admissible,
        raw_order_wire_eq raw admissible, raw_order_masked_wire_eq raw admissible]
        using source.targetBorrowDifferent index }

theorem degree_increment_evidence207
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryTaylorDegreeIncrementEvidence (layout203 raw admissible) := by
  let source := admissible.degreeIncrement
  exact {
    addend_accumulator_disjoint := by
      intro left right
      simpa only [raw_order_addend_wire_eq_early raw admissible,
        raw_order_accumulator_wire_eq_early raw admissible]
        using source.addendAccumulatorDisjoint left right
    carry_ne_addend := by
      intro index
      simpa only [raw_order_carry_eq raw admissible,
        raw_order_addend_wire_eq_early raw admissible]
        using source.carryNeAddend index
    carry_ne_accumulator := by
      intro index
      simpa only [raw_order_carry_eq raw admissible,
        raw_order_accumulator_wire_eq_early raw admissible]
        using source.carryNeAccumulator index
    control_ne_addend := by
      intro index
      simpa only [raw_active_wire_eq raw admissible,
        raw_order_addend_wire_eq_early raw admissible]
        using source.controlNeAddend index
    control_ne_accumulator := by
      intro index
      simpa only [raw_active_wire_eq raw admissible,
        raw_order_accumulator_wire_eq_early raw admissible]
        using source.controlNeAccumulator index
    control_ne_carry := by
      simpa only [raw_active_wire_eq raw admissible,
        raw_order_carry_eq raw admissible]
        using source.controlNeCarry }

theorem clock_increment_evidence207
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryControlledClockIncrementEvidence (layout203 raw admissible) := by
  let source := admissible.clockIncrement
  exact {
    masked_clock_disjoint := by
      intro left right
      simpa only [raw_clock_addend_wire_eq_early raw admissible,
        raw_clock_accumulator_wire_eq_early raw admissible,
        rawClockAccumulator203]
        using source.maskedAccumulatorDisjoint left right
    carry_ne_masked := by
      intro index
      simpa only [raw_clock_carry_eq raw admissible,
        raw_clock_addend_wire_eq_early raw admissible]
        using source.carryNeMasked index
    carry_ne_clock := by
      intro index
      simpa only [raw_clock_carry_eq raw admissible,
        raw_clock_accumulator_wire_eq_early raw admissible,
        rawClockAccumulator203]
        using source.carryNeAccumulator index
    branch_ne_masked := by
      intro index
      simpa only [raw_branch_wire_eq raw admissible,
        raw_clock_addend_wire_eq_early raw admissible]
        using source.branchNeMasked index
    branch_ne_clock := by
      intro index
      simpa only [raw_branch_wire_eq raw admissible,
        raw_clock_accumulator_wire_eq_early raw admissible,
        rawClockAccumulator203]
        using source.branchNeAccumulator index
    branch_ne_carry := by
      simpa only [raw_branch_wire_eq raw admissible,
        raw_clock_carry_eq raw admissible]
        using source.branchNeCarry }

def history_taylor_l2_evidence207
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryTaylorL2Evidence (layout203 raw admissible) := by
  exact {
    clockTimeLessThan := clock_time_less_than_evidence207 raw admissible
    clockIdleEndLessThan := clock_idle_end_less_than_evidence207 raw admissible
    degreeOrderLessThan := degree_order_less_than_evidence207 raw admissible
    degreeIncrement := degree_increment_evidence207 raw admissible
    branch_ne_ltIdleEnd := by
      simpa only [raw_branch_wire_eq raw admissible,
        raw_clock_less_than_idle_end_wire_eq raw admissible]
        using admissible.branchNeIdleEnd
    branch_ne_coefficientSignal := by
      simpa only [raw_branch_wire_eq raw admissible,
        raw_coefficient_signal_eq raw admissible]
        using admissible.branchNeCoefficientSignal
    ltIdleEnd_ne_coefficientSignal := by
      simpa only [raw_clock_less_than_idle_end_wire_eq raw admissible,
        raw_coefficient_signal_eq raw admissible]
        using admissible.lessThanIdleEndNeCoefficientSignal
    active_ne_equality := by
      simpa only [raw_active_wire_eq raw admissible,
        raw_equality_flag_eq raw admissible]
        using admissible.activeNeEquality
    active_ne_orderBoundary := by
      simpa only [raw_active_wire_eq raw admissible,
        raw_order_boundary_signal_eq raw admissible]
        using admissible.activeNeOrderBoundary
    equality_ne_orderBoundary := by
      simpa only [raw_equality_flag_eq raw admissible,
        raw_order_boundary_signal_eq raw admissible]
        using admissible.equalityNeOrderBoundary
    ltIdleEnd_ne_idle := by
      simpa only [raw_clock_less_than_idle_end_wire_eq raw admissible,
        raw_idle_flag_eq raw admissible]
        using admissible.lessThanIdleNeIdle
    ltTime_ne_idle := by
      simpa only [raw_clock_less_than_time_wire_eq raw admissible,
        raw_idle_flag_eq raw admissible]
        using admissible.lessThanTimeNeIdle
    active_ne_coefficientSignal := by
      simpa only [raw_active_wire_eq raw admissible,
        raw_coefficient_signal_eq raw admissible]
        using admissible.activeNeCoefficientSignal
    coefficientControl_ne_coefficientSignal := by
      simpa only [raw_coefficient_control_eq raw admissible,
        raw_coefficient_signal_eq raw admissible]
        using admissible.coefficientControlNeCoefficientSignal
    coefficientAngles := raw.rawCoefficientAngles
    idleCoefficientAngle := raw.rawIdleCoefficientAngle }

theorem history_idle_transform_evidence207
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryIdleTransformEvidence (layout203 raw admissible) := by
  exact {
    idleEnd_ne_idle := by
      simpa only [raw_clock_less_than_idle_end_wire_eq raw admissible,
        raw_idle_flag_eq raw admissible]
        using admissible.lessThanIdleNeIdle
    time_ne_idle := by
      simpa only [raw_clock_less_than_time_wire_eq raw admissible,
        raw_idle_flag_eq raw admissible]
        using admissible.lessThanTimeNeIdle
    active_ne_order := by
      intro target member
      simp only [historyRegisterWires, List.mem_ofFn] at member
      rcases member with ⟨index, rfl⟩
      simpa only [raw_active_wire_eq raw admissible,
        raw_order_wire_eq raw admissible]
        using admissible.uniformActiveNeOrder index
    active_ne_coefficient := by
      simpa only [raw_active_wire_eq raw admissible,
        raw_coefficient_signal_eq raw admissible]
        using admissible.activeNeCoefficientSignal }

theorem history_order_uniform_external_control_evidence207
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryOrderUniformExternalControlEvidence (layout203 raw admissible) := by
  exact {
    active_ne_order := by
      intro source
      simpa only [raw_active_wire_eq raw admissible,
        raw_order_wire_eq raw admissible]
        using admissible.uniformActiveNeOrder source
    work₀_ne_active := by
      simpa only [raw_uniform_work_zero_eq raw admissible,
        raw_active_wire_eq raw admissible]
        using admissible.uniformWork₀NeActive
    work₁_ne_active := by
      simpa only [raw_uniform_work_one_eq raw admissible,
        raw_active_wire_eq raw admissible]
        using admissible.uniformWork₁NeActive
    work₀_ne_order := by
      intro source
      simpa only [raw_uniform_work_zero_eq raw admissible,
        raw_order_wire_eq raw admissible]
        using admissible.uniformWork₀NeOrder source
    work₁_ne_order := by
      intro source
      simpa only [raw_uniform_work_one_eq raw admissible,
        raw_order_wire_eq raw admissible]
        using admissible.uniformWork₁NeOrder source }

theorem history_projector_control_evidence207
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryProjectorControlEvidence (layout203 raw admissible) := by
  exact {
    branch_ne_projector := by
      simpa only [raw_branch_wire_eq raw admissible,
        raw_projector_signal_eq raw admissible]
        using admissible.projectorBranchNeProjector
    coefficientControl_ne_projector := by
      simpa only [raw_coefficient_control_eq raw admissible,
        raw_projector_signal_eq raw admissible]
        using admissible.projectorCoefficientControlNeProjector }

def history_clock_concrete_source_order_evidence207
    (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryClockConcreteSourceOrderEvidence (layout203 raw admissible) := by
  exact {
    uniformExternalControl :=
      history_order_uniform_external_control_evidence207 raw admissible
    idleTransform := history_idle_transform_evidence207 raw admissible
    coefficientControl_ne_signal := by
      simpa only [raw_active_wire_eq raw admissible,
        raw_coefficient_signal_eq raw admissible]
        using admissible.activeNeCoefficientSignal
    projectorControl := history_projector_control_evidence207 raw admissible
    controlledIncrement := clock_increment_evidence207 raw admissible
    idleCoefficientAngle := raw.rawIdleCoefficientAngle
    coefficientAngle := raw.rawCoefficientAngles ⟨0, admissible.taylorOrderPositive⟩ }

end HistoryIndexCast
