import QLean.History.Implementation.HistoryPipelineFiniteScientificBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option warningAsError true

/-!
# Finite scientific comparator bridge

The two finite clock-comparison records are shown to use exactly the same
operand registers, borrow work and result wire as the certified scientific
history plan. These are equalities of concrete wire layouts, not assumptions
about the analytic target.
-/

namespace ExecutableHistoryFiniteScientificComparatorBridge

open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open ExecutableHistoryFiniteScientificLayout
open ExecutableHistoryFiniteScientificH3
open ExecutableHistoryFiniteCorrectedP05
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open VerifiedCircuitCore

private theorem registerExt {qubits width : Nat}
    (left right : Register qubits width)
    (wireEq : ∀ index, left.wire index = right.wire index) :
    left = right := by
  cases left with
  | mk leftWire leftInjective =>
    cases right with
    | mk rightWire rightInjective =>
      have hWire : leftWire = rightWire := funext wireEq
      subst rightWire
      rfl

private theorem specExt {qubits width : Nat}
    (left right : UnsignedLessThanXorSpec qubits width)
    (lhsEq : left.lhs = right.lhs)
    (rhsEq : left.rhs = right.rhs)
    (borrowEq : left.borrow = right.borrow)
    (targetEq : left.target = right.target) : left = right := by
  cases left with
  | mk lp ll lr lb lt llr llb lrb ltl ltr ltb =>
    cases right with
    | mk rp rl rr rb rt rlr rlb rrb rtl rtr rtb =>
      dsimp at lhsEq rhsEq borrowEq targetEq
      subst rl
      subst rr
      subst rb
      subst rt
      rfl

private theorem specCastLhs {n m width : Nat} (h : n = m)
    (spec : UnsignedLessThanXorSpec n width) :
    (h ▸ spec).lhs = h ▸ spec.lhs := by
  cases h
  rfl

private theorem specCastRhs {n m width : Nat} (h : n = m)
    (spec : UnsignedLessThanXorSpec n width) :
    (h ▸ spec).rhs = h ▸ spec.rhs := by
  cases h
  rfl

private theorem specCastBorrow {n m width : Nat} (h : n = m)
    (spec : UnsignedLessThanXorSpec n width) :
    (h ▸ spec).borrow = h ▸ spec.borrow := by
  cases h
  rfl

private theorem specCastTarget {n m width : Nat} (h : n = m)
    (spec : UnsignedLessThanXorSpec n width) :
    (h ▸ spec).target = Fin.cast h spec.target := by
  cases h
  rfl

private theorem castRegisterWireVal {n m width : Nat} (h : n = m)
    (register : Register n width) (bit : Fin width) :
    ((h ▸ register).wire bit).val = (register.wire bit).val := by
  cases h
  rfl

/-- The finite time-bound comparator is the certified comparator after the
carrier-width equality is applied. -/
theorem finiteClockTimeComparison_eq_certified
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (finiteScientificHistoryQubits119_eq source) ▸
      finiteClockTimeComparison119 source =
        (ExecutableHistoryFiniteCorrectedP05.certifiedPlan source domain).timeComparison := by
  apply specExt
  · rw [specCastLhs]
    apply registerExt
    intro bit
    apply Fin.ext
    rw [castRegisterWireVal]
    exact finiteScientificHistoryClockWire119_scientific_val source domain bit
  · rw [specCastRhs]
    apply registerExt
    intro bit
    apply Fin.ext
    rw [castRegisterWireVal]
    exact finiteScientificHistoryWorkspaceWire119_scientific_val source domain
      ⟨5 + bit.val, by
        change 5 + bit.val <
          historyClockWorkspaceWidth (finiteCircuitShapeParameters119 source)
            source.qParameters.generatorWorkWidth
        have hBit : bit.val < finiteScientificHistoryClockWidth119 source :=
          bit.isLt
        have hClock : finiteScientificHistoryClockWidth119 source =
            historyClockWidth (finiteCircuitShapeParameters119 source).timeSteps
              (finiteCircuitShapeParameters119 source).taylorOrder
              (finiteCircuitShapeParameters119 source).idlingSteps := rfl
        rw [hClock] at hBit
        try rw [hClock]
        have hStructural := Nat.le_max_right
          source.qParameters.generatorWorkWidth
          (historyStructuralPoolWidth (finiteCircuitShapeParameters119 source))
        unfold historyClockWorkspaceWidth historySharedPoolWidth at ⊢
        unfold historyStructuralPoolWidth at hStructural ⊢
        omega⟩
  · rw [specCastBorrow]
    apply registerExt
    intro bit
    apply Fin.ext
    rw [castRegisterWireVal]
    exact finiteScientificHistoryWorkspaceWire119_scientific_val source domain
      ⟨5 + finiteScientificHistoryClockWidth119 source + bit.val, by
        change 5 + finiteScientificHistoryClockWidth119 source + bit.val <
          historyClockWorkspaceWidth (finiteCircuitShapeParameters119 source)
            source.qParameters.generatorWorkWidth
        have hBit : bit.val < finiteScientificHistoryClockWidth119 source :=
          bit.isLt
        have hClock : finiteScientificHistoryClockWidth119 source =
            historyClockWidth (finiteCircuitShapeParameters119 source).timeSteps
              (finiteCircuitShapeParameters119 source).taylorOrder
              (finiteCircuitShapeParameters119 source).idlingSteps := rfl
        rw [hClock] at hBit
        try rw [hClock]
        have hStructural := Nat.le_max_right
          source.qParameters.generatorWorkWidth
          (historyStructuralPoolWidth (finiteCircuitShapeParameters119 source))
        unfold historyClockWorkspaceWidth historySharedPoolWidth at ⊢
        unfold historyStructuralPoolWidth at hStructural ⊢
        omega⟩
  · rw [specCastTarget]
    apply Fin.ext
    exact finiteScientificHistoryWorkspaceWire119_scientific_val source domain
      ⟨historySharedPoolWidth (finiteCircuitShapeParameters119 source)
         source.qParameters.generatorWorkWidth + 3, by
        change historySharedPoolWidth (finiteCircuitShapeParameters119 source)
            source.qParameters.generatorWorkWidth + 3 <
          historyClockWorkspaceWidth (finiteCircuitShapeParameters119 source)
            source.qParameters.generatorWorkWidth
        unfold historyClockWorkspaceWidth
        omega⟩

/-- The finite idle-end comparator shares the same three registers and its
distinct result wire with the certified scientific comparator. -/
theorem finiteClockIdleEndComparison_eq_certified
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    (finiteScientificHistoryQubits119_eq source) ▸
      finiteClockIdleEndComparison119 source =
        (ExecutableHistoryFiniteCorrectedP05.certifiedPlan source domain).idleEndComparison := by
  apply specExt
  · have hTime := congrArg UnsignedLessThanXorSpec.lhs
      (finiteClockTimeComparison_eq_certified source domain)
    rw [specCastLhs] at hTime ⊢
    exact hTime
  · have hTime := congrArg UnsignedLessThanXorSpec.rhs
      (finiteClockTimeComparison_eq_certified source domain)
    rw [specCastRhs] at hTime ⊢
    exact hTime
  · have hTime := congrArg UnsignedLessThanXorSpec.borrow
      (finiteClockTimeComparison_eq_certified source domain)
    rw [specCastBorrow] at hTime ⊢
    exact hTime
  · rw [specCastTarget]
    apply Fin.ext
    exact finiteScientificHistoryWorkspaceWire119_scientific_val source domain
      ⟨historySharedPoolWidth (finiteCircuitShapeParameters119 source)
         source.qParameters.generatorWorkWidth + 4, by
        change historySharedPoolWidth (finiteCircuitShapeParameters119 source)
            source.qParameters.generatorWorkWidth + 4 <
          historyClockWorkspaceWidth (finiteCircuitShapeParameters119 source)
            source.qParameters.generatorWorkWidth
        unfold historyClockWorkspaceWidth
        omega⟩

end ExecutableHistoryFiniteScientificComparatorBridge
