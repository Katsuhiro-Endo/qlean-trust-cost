import QLean.History.Implementation.HistoryPipelineQbPlusCleanBlock
import QLean.History.Implementation.HistoryPipelineReducingRealPreparation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace ExecutableHistoryImplementationRole

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open ExecutableHistoryCore
open ExecutableHistoryQbPlusCleanBlock

noncomputable section

variable {targetQubits : Nat}

/-! The only deliberately unresolved physical point is the internal H-history
    child below.  Its carrier, placement and clean block are structural data;
    no caller-supplied target, operator, equality or bridge is exposed by the
    eventual circuit wrapper. -/
structure InternalHHistoryCleanComponentF
    {d c r m R : Nat} (I : P18Input119 d c r m R)
    (targetQubits : Nat) where
  sourceQubits : Nat
  layout : ControlLayout sourceQubits targetQubits
  circuit : NormalizedCircuit sourceQubits
  embedding : JenningsHistory.HistoryIndex d c R ↪ QubitBasis sourceQubits
  inrBasis : QubitBasis sourceQubits
  clean_block : ∀ row col,
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) circuit.circuit
        (embedding row) (embedding col) =
      (JenningsHistory.scaledHistory I.base.system I.base.alpha row col : ℝ)

theorem fixedOutsideBasisEmbedding_outside_valueF
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (internal : QubitBasis sourceQubits)
    (wire : Fin targetQubits)
    (h : ∀ source, placement source ≠ wire) :
    fixedOutsideBasisEmbedding placement outside internal wire =
      outside ⟨wire, h⟩ := by
  simp [fixedOutsideBasisEmbedding, mergePlacedAndOutsideBasis, h]

theorem fixedOutsideBasisEmbedding_restrictF
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (internal : QubitBasis sourceQubits) :
    restrictToPlacedWires placement
        ((fixedOutsideBasisEmbedding placement outside) internal) = internal := by
  change restrictToPlacedWires placement
      (mergePlacedAndOutsideBasis placement internal outside) = internal
  exact restrictToPlacedWires_mergePlacedAndOutsideBasis _ _ _

theorem branchOutside_distinctF
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) :
    branchOutside119 layout true ≠ branchOutside119 layout false := by
  intro h
  have hc := congrFun h (externalControlOutside119 (externalLayout119 layout))
  rw [branchOutside119_control, branchOutside119_control] at hc
  cases hc

def extendedIndexEmbeddingF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    GramOperator.ExtendedIndex d c R ↪
      QubitBasis targetQubits where
  toFun := fun index => match index with
    | Sum.inl row =>
        fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
          (branchOutside119 child.layout true) (child.embedding row)
    | Sum.inr _ =>
        fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
          (branchOutside119 child.layout false) child.inrBasis
  inj' := by
    intro left right h
    cases left with
    | inl left =>
        cases right with
        | inl right =>
            change fixedOutsideBasisEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout true) (child.embedding left) =
              fixedOutsideBasisEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout true) (child.embedding right) at h
            exact congrArg (fun row =>
              (Sum.inl row : GramOperator.ExtendedIndex d c R))
              (child.embedding.injective
                ((fixedOutsideBasisEmbedding
                  (externalLayout119 child.layout).placement
                  (branchOutside119 child.layout true)).injective h))
        | inr right =>
            change fixedOutsideBasisEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout true) (child.embedding left) =
              fixedOutsideBasisEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout false) child.inrBasis at h
            exfalso
            apply branchOutside_distinctF child.layout
            calc
              branchOutside119 child.layout true =
                  restrictToOutsideWires (externalLayout119 child.layout).placement
                    (fixedOutsideBasisEmbedding
                      (externalLayout119 child.layout).placement
                      (branchOutside119 child.layout true)
                      (child.embedding left)) := by
                    symm
                    exact fixedOutsideBasisEmbedding_hasFixedOutsideBasis _ _ _
              _ = restrictToOutsideWires (externalLayout119 child.layout).placement
                    (fixedOutsideBasisEmbedding
                      (externalLayout119 child.layout).placement
                      (branchOutside119 child.layout false) child.inrBasis) := by
                    rw [h]
              _ = branchOutside119 child.layout false :=
                    fixedOutsideBasisEmbedding_hasFixedOutsideBasis _ _ _
    | inr left =>
        cases right with
        | inl right =>
            change fixedOutsideBasisEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout false) child.inrBasis =
              fixedOutsideBasisEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout true) (child.embedding right) at h
            exfalso
            apply branchOutside_distinctF child.layout
            calc
              branchOutside119 child.layout true =
                  restrictToOutsideWires (externalLayout119 child.layout).placement
                    (fixedOutsideBasisEmbedding
                      (externalLayout119 child.layout).placement
                      (branchOutside119 child.layout true)
                      (child.embedding right)) := by
                    symm
                    exact fixedOutsideBasisEmbedding_hasFixedOutsideBasis _ _ _
              _ = restrictToOutsideWires (externalLayout119 child.layout).placement
                    (fixedOutsideBasisEmbedding
                      (externalLayout119 child.layout).placement
                      (branchOutside119 child.layout false) child.inrBasis) := by
                    rw [h]
              _ = branchOutside119 child.layout false :=
                    fixedOutsideBasisEmbedding_hasFixedOutsideBasis _ _ _
        | inr right =>
            cases left
            cases right
            rfl

theorem branchEmbedding_work_valueF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits)
    (controlValue : Bool) (internal : QubitBasis child.sourceQubits)
    (slot : Fin 2) :
    fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
        (branchOutside119 child.layout controlValue) internal
        (child.layout.work slot) = false := by
  let h : ∀ source,
      (externalLayout119 child.layout).placement source ≠
        child.layout.work slot := by
    intro source hs
    exact child.layout.work_ne_placed slot source hs.symm
  calc
    fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
        (branchOutside119 child.layout controlValue) internal
        (child.layout.work slot) =
        branchOutside119 child.layout controlValue
          ⟨child.layout.work slot, h⟩ :=
      fixedOutsideBasisEmbedding_outside_valueF _ _ _ _ h
    _ = false := branchOutside119_work child.layout controlValue slot

theorem branchEmbedding_control_valueF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits)
    (controlValue : Bool) (internal : QubitBasis child.sourceQubits) :
    fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
        (branchOutside119 child.layout controlValue) internal child.layout.control =
      controlValue := by
  let h : ∀ source,
      (externalLayout119 child.layout).placement source ≠ child.layout.control := by
    intro source hs
    exact child.layout.control_ne_placed source hs.symm
  calc
    fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
        (branchOutside119 child.layout controlValue) internal child.layout.control =
        branchOutside119 child.layout controlValue
          ⟨child.layout.control, h⟩ :=
      fixedOutsideBasisEmbedding_outside_valueF _ _ _ _ h
    _ = controlValue := branchOutside119_control child.layout controlValue

theorem fixedEmbedding_not_agreesExceptF
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (left right : QubitBasis sourceQubits)
    (target : Fin targetQubits)
    (target_not_placed : ∀ source, placement source ≠ target)
    (different : left ≠ right) :
    ¬ agreesExcept target
        ((fixedOutsideBasisEmbedding placement outside) left)
        ((fixedOutsideBasisEmbedding placement outside) right) := by
  intro h
  apply different
  calc
    left = restrictToPlacedWires placement
        ((fixedOutsideBasisEmbedding placement outside) left) :=
      (fixedOutsideBasisEmbedding_restrictF placement outside left).symm
    _ = restrictToPlacedWires placement
        ((fixedOutsideBasisEmbedding placement outside) right) := by
      funext source
      exact h (placement source) (target_not_placed source)
    _ = right := fixedOutsideBasisEmbedding_restrictF placement outside right

def hnuAngleF (nu : ℝ) : ℝ := 2 * Real.arccos nu⁻¹

def hnuControlCircuitF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    Circuit (PrimitiveGate targetQubits) :=
  (controlCircuit child.layout child.circuit).circuit

def hnuRotationCircuitF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) (nu : ℝ) :
    Circuit (PrimitiveGate targetQubits) :=
  Circuit.boolMultiControlledRy
    [(child.layout.control, false)]
    [child.layout.work 0]
    (child.layout.work 1)
    (.const (hnuAngleF nu))

theorem hnuRotation_layout_nodupF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    ([(child.layout.control, false)].map Prod.fst ++
      [child.layout.work 0] ++ [child.layout.work 1]).Nodup := by
  change (child.layout.control :: child.layout.work 0 ::
    [child.layout.work 1]).Nodup
  apply List.nodup_cons.mpr
  constructor
  · intro h
    simp at h
    rcases h with h | h
    · exact (child.layout.work_ne_control 0) h.symm
    · exact (child.layout.work_ne_control 1) h.symm
  · apply List.nodup_cons.mpr
    constructor
    · intro h
      simp at h
      have h01 : (0 : Fin 2) = 1 := child.layout.work_injective h
      omega
    · simp

theorem hnuRotation_entryF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) (nu : ℝ)
    (controlValue : Bool) (left right : QubitBasis child.sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (hnuRotationCircuitF child nu)
        ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
          (branchOutside119 child.layout controlValue)) left)
        ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
          (branchOutside119 child.layout controlValue)) right) =
      if controlValue then
        (if left = right then (1 : ℂ) else 0)
      else
        (if left = right then
          (Real.cos (hnuAngleF nu / 2) : ℂ) else 0) := by
  rw [hnuRotationCircuitF]
  have hsparse := boolMultiControlledRy_apply_sparse
    [(child.layout.control, false)] [child.layout.work 0]
    (child.layout.work 1) (AngleExpr.const (hnuAngleF nu))
    ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
      (branchOutside119 child.layout controlValue)) left)
    ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
      (branchOutside119 child.layout controlValue)) right)
    (by norm_num)
    (hnuRotation_layout_nodupF child)
    (by
      intro wire hwire
      simp at hwire
      subst wire
      exact branchEmbedding_work_valueF child controlValue right 0)
  rw [hsparse]
  by_cases hEq : left = right
  · subst right
    have hagree : agreesExcept (child.layout.work 1)
        ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
          (branchOutside119 child.layout controlValue)) left)
        ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
          (branchOutside119 child.layout controlValue)) left) := by
      intro wire _
      rfl
    rw [boolControlledRyAmplitude, if_pos hagree]
    cases controlValue with
    | false =>
        have hctrl : boolControlsSatisfied
            [(child.layout.control, false)]
            ((fixedOutsideBasisEmbedding
              (externalLayout119 child.layout).placement
              (branchOutside119 child.layout false)) left) = true := by
          simp [boolControlsSatisfied, branchEmbedding_control_valueF]
        rw [hctrl]
        rw [branchEmbedding_work_valueF child false left 1]
        simp
        rw [show (AngleExpr.const (hnuAngleF nu)).uniformValue =
            hnuAngleF nu by rfl]
        simp [localRy]
    | true =>
        have hctrl : ¬ boolControlsSatisfied
            [(child.layout.control, false)]
            ((fixedOutsideBasisEmbedding
              (externalLayout119 child.layout).placement
              (branchOutside119 child.layout true)) left) = true := by
          simp [boolControlsSatisfied, branchEmbedding_control_valueF]
        rw [if_neg hctrl]
        simp [branchEmbedding_work_valueF]
  · have hnot : ¬ agreesExcept (child.layout.work 1)
        ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
          (branchOutside119 child.layout controlValue)) left)
        ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
          (branchOutside119 child.layout controlValue)) right) := by
      exact fixedEmbedding_not_agreesExceptF
        (externalLayout119 child.layout).placement
        (branchOutside119 child.layout controlValue)
        left right (child.layout.work 1)
        (fun source equal => child.layout.work_ne_placed 1 source equal.symm)
        hEq
    rw [boolControlledRyAmplitude, if_neg hnot]
    simp [hEq]

theorem hnuRotation_mixed_entryF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) (nu : ℝ)
    (outputValue inputValue : Bool) (different : outputValue ≠ inputValue)
    (left right : QubitBasis child.sourceQubits) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (hnuRotationCircuitF child nu)
        ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
          (branchOutside119 child.layout outputValue)) left)
        ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
          (branchOutside119 child.layout inputValue)) right) = 0 := by
  rw [hnuRotationCircuitF]
  have hsparse := boolMultiControlledRy_apply_sparse
    [(child.layout.control, false)] [child.layout.work 0]
    (child.layout.work 1) (AngleExpr.const (hnuAngleF nu))
    ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
      (branchOutside119 child.layout outputValue)) left)
    ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
      (branchOutside119 child.layout inputValue)) right)
    (by norm_num)
    (hnuRotation_layout_nodupF child)
    (by
      intro wire hwire
      simp at hwire
      subst wire
      exact branchEmbedding_work_valueF child inputValue right 0)
  rw [hsparse, boolControlledRyAmplitude]
  have hnot : ¬ agreesExcept (child.layout.work 1)
      ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
        (branchOutside119 child.layout outputValue)) left)
      ((fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
        (branchOutside119 child.layout inputValue)) right) := by
    intro hagree
    have hc := hagree child.layout.control
      (Ne.symm (child.layout.work_ne_control 1))
    have hv : outputValue = inputValue := by
      calc
        outputValue =
            fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
              (branchOutside119 child.layout outputValue) left
              child.layout.control :=
          (branchEmbedding_control_valueF child outputValue left).symm
        _ = fixedOutsideBasisEmbedding (externalLayout119 child.layout).placement
              (branchOutside119 child.layout inputValue) right
              child.layout.control := hc
        _ = inputValue := branchEmbedding_control_valueF child inputValue right
    exact different hv
  rw [if_neg hnot]

theorem hnuRotation_apply_fixedOutside_mixedF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) (nu : ℝ)
    (outputValue inputValue : Bool) (different : outputValue ≠ inputValue)
    (state : State (QubitBasis child.sourceQubits))
    (output : QubitBasis child.sourceQubits) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (hnuRotationCircuitF child nu))
        (fixedOutsideStateEmbedding
          (externalLayout119 child.layout).placement
          (branchOutside119 child.layout inputValue) state)
        (fixedOutsideBasisEmbedding
          (externalLayout119 child.layout).placement
          (branchOutside119 child.layout outputValue) output) = 0 := by
  let placement := (externalLayout119 child.layout).placement
  let inputOutside := branchOutside119 child.layout inputValue
  let outputBasis := fixedOutsideBasisEmbedding placement
    (branchOutside119 child.layout outputValue) output
  unfold applyOperator Matrix.mulVec dotProduct
  simp only [fixedOutsideStateEmbedding]
  apply Finset.sum_eq_zero
  intro input _
  by_cases hout : restrictToOutsideWires placement input = inputOutside
  · have inputEq : fixedOutsideBasisEmbedding placement inputOutside
        (restrictToPlacedWires placement input) = input := by
      change mergePlacedAndOutsideBasis placement
          (restrictToPlacedWires placement input) inputOutside = input
      rw [← hout]
      exact mergePlacedAndOutsideBasis_restrict _ _
    have hentry :
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (hnuRotationCircuitF child nu) outputBasis input = 0 := by
      rw [← inputEq]
      exact hnuRotation_mixed_entryF child nu outputValue inputValue
        different output (restrictToPlacedWires placement input)
    rw [hentry]
    simp
  · have hout' : ¬ restrictToOutsideWires
        (externalLayout119 child.layout).placement input =
        branchOutside119 child.layout inputValue := by
      simpa [placement, inputOutside] using hout
    simp [hout']

theorem hnuRotation_apply_fixedOutsideF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) (nu : ℝ)
    (controlValue : Bool) (state : State (QubitBasis child.sourceQubits))
    (output : QubitBasis child.sourceQubits) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (hnuRotationCircuitF child nu))
        (fixedOutsideStateEmbedding
          (externalLayout119 child.layout).placement
          (branchOutside119 child.layout controlValue) state)
        (fixedOutsideBasisEmbedding
          (externalLayout119 child.layout).placement
          (branchOutside119 child.layout controlValue) output) =
      if controlValue then state output
      else (Real.cos (hnuAngleF nu / 2) : ℂ) * state output := by
  classical
  let placement := (externalLayout119 child.layout).placement
  let outside := branchOutside119 child.layout controlValue
  let outputBasis := fixedOutsideBasisEmbedding placement outside output
  have houtputOutside : restrictToOutsideWires placement outputBasis = outside := by
    exact fixedOutsideBasisEmbedding_hasFixedOutsideBasis _ _ _
  unfold applyOperator Matrix.mulVec dotProduct
  simp only [fixedOutsideStateEmbedding]
  calc
    (∑ input : QubitBasis targetQubits,
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (hnuRotationCircuitF child nu) outputBasis input *
          (if restrictToOutsideWires placement input = outside then
            state (restrictToPlacedWires placement input) else 0)) =
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (hnuRotationCircuitF child nu) outputBasis outputBasis *
          (if restrictToOutsideWires placement outputBasis = outside then
            state (restrictToPlacedWires placement outputBasis) else 0) := by
      refine @Finset.sum_eq_single
        (QubitBasis targetQubits) ℂ inferInstance
        (Finset.univ : Finset (QubitBasis targetQubits))
        (fun input =>
          Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              (hnuRotationCircuitF child nu) outputBasis input *
            (if restrictToOutsideWires placement input = outside then
              state (restrictToPlacedWires placement input) else 0))
        outputBasis ?_ ?_
      · intro input _ hne
        by_cases hout : restrictToOutsideWires placement input = outside
        · have inputEq : fixedOutsideBasisEmbedding placement outside
              (restrictToPlacedWires placement input) = input := by
            change mergePlacedAndOutsideBasis placement
                (restrictToPlacedWires placement input) outside = input
            rw [← hout]
            exact mergePlacedAndOutsideBasis_restrict _ _
          have hInternal : output ≠ restrictToPlacedWires placement input := by
            intro heq
            apply hne
            calc
              input = fixedOutsideBasisEmbedding placement outside
                  (restrictToPlacedWires placement input) := inputEq.symm
              _ = fixedOutsideBasisEmbedding placement outside output := by rw [heq]
              _ = outputBasis := rfl
          have hentry :
              Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                  (hnuRotationCircuitF child nu) outputBasis input = 0 := by
            rw [← inputEq]
            rw [hnuRotation_entryF child nu controlValue output
              (restrictToPlacedWires placement input)]
            simp [hInternal]
          simp [hout, hentry]
        · simp [hout]
      · simp
    _ = if controlValue then state output
        else (Real.cos (hnuAngleF nu / 2) : ℂ) * state output := by
      rw [houtputOutside]
      rw [hnuRotation_entryF child nu controlValue output output]
      rw [fixedOutsideBasisEmbedding_restrictF]
      cases controlValue <;> simp [hnuAngleF]

theorem hnuControl_apply_inlF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits)
    (row : JenningsHistory.HistoryIndex d c R) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (hnuControlCircuitF child))
        (basisKet (extendedIndexEmbeddingF child (Sum.inl row))) =
      fixedOutsideStateEmbedding
        (externalLayout119 child.layout).placement
        (branchOutside119 child.layout true)
        (applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            child.circuit.circuit)
          (basisKet (child.embedding row))) := by
  change applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (hnuControlCircuitF child))
      (basisKet (fixedOutsideBasisEmbedding
        (externalLayout119 child.layout).placement
        (branchOutside119 child.layout true) (child.embedding row))) = _
  rw [← fixedOutsideStateEmbedding_basisKet]
  simpa [hnuControlCircuitF] using
    (controlCircuit_fixedOutsideState119 (fun _ => 0) child.layout
      child.circuit true (basisKet (child.embedding row)))

theorem hnuControl_apply_inrF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (hnuControlCircuitF child))
        (basisKet (extendedIndexEmbeddingF child (Sum.inr ()))) =
      fixedOutsideStateEmbedding
        (externalLayout119 child.layout).placement
        (branchOutside119 child.layout false)
        (basisKet child.inrBasis) := by
  change applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (hnuControlCircuitF child))
      (basisKet (fixedOutsideBasisEmbedding
        (externalLayout119 child.layout).placement
        (branchOutside119 child.layout false) child.inrBasis)) = _
  rw [← fixedOutsideStateEmbedding_basisKet]
  simpa [hnuControlCircuitF] using
    (controlCircuit_fixedOutsideState119 (fun _ => 0) child.layout
      child.circuit false (basisKet child.inrBasis))

def hnuExtensionCircuitF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) (nu : ℝ) :
    Circuit (PrimitiveGate targetQubits) :=
  Circuit.sequence [hnuControlCircuitF child, hnuRotationCircuitF child nu]

theorem hnuExtensionCircuitF_denote
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) (nu : ℝ) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (hnuExtensionCircuitF child nu) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (hnuRotationCircuitF child nu) *
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (hnuControlCircuitF child) := by
  unfold hnuExtensionCircuitF
  rw [Circuit.denote_sequence_eq_operatorSequence]
  simp [operatorSequence]

theorem hnu_inv_boundsF
    (nu : ℝ) (hnu : 1 ≤ nu) : -1 ≤ nu⁻¹ ∧ nu⁻¹ ≤ 1 := by
  have hpos : 0 < nu := lt_of_lt_of_le zero_lt_one hnu
  constructor
  · have hinv : 0 ≤ nu⁻¹ := le_of_lt (inv_pos.mpr hpos)
    linarith
  · exact (inv_le_one₀ hpos).2 hnu

theorem hnu_cos_halfF
    (nu : ℝ) (hnu : 1 ≤ nu) :
    Real.cos (hnuAngleF nu / 2) = nu⁻¹ := by
  have hangle : hnuAngleF nu / 2 = Real.arccos nu⁻¹ := by
    unfold hnuAngleF
    ring
  rw [hangle]
  exact Real.cos_arccos (hnu_inv_boundsF nu hnu).1
    (hnu_inv_boundsF nu hnu).2

theorem hnuExtension_clean_blockF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits)
    (hnu : 1 ≤ I.base.nu)
    (output input : GramOperator.ExtendedIndex d c R) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (hnuExtensionCircuitF child I.base.nu)
        (extendedIndexEmbeddingF child output)
        (extendedIndexEmbeddingF child input) =
      (JenningsHistory.dalzellExtendedH I.base.system I.base.alpha I.base.nu
        output input : ℂ) := by
  have hbasis := (applyOperator_basisKet119
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (hnuExtensionCircuitF child I.base.nu))
    (extendedIndexEmbeddingF child output)
    (extendedIndexEmbeddingF child input)).symm
  rw [hbasis]
  rw [hnuExtensionCircuitF_denote, applyOperator_mul]
  cases output with
  | inl output =>
      cases input with
      | inl input =>
          rw [hnuControl_apply_inlF]
          change applyOperator
              (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                (hnuRotationCircuitF child I.base.nu))
              (fixedOutsideStateEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout true)
                (applyOperator
                  (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                    child.circuit.circuit)
                  (basisKet (child.embedding input))))
              (fixedOutsideBasisEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout true)
                (child.embedding output)) = _
          rw [hnuRotation_apply_fixedOutsideF]
          rw [applyOperator_basisKet119]
          rw [child.clean_block]
          simp [JenningsHistory.dalzellExtendedH]
      | inr input =>
          cases input
          rw [hnuControl_apply_inrF]
          change applyOperator
              (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                (hnuRotationCircuitF child I.base.nu))
              (fixedOutsideStateEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout false)
                (basisKet child.inrBasis))
              (fixedOutsideBasisEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout true)
                (child.embedding output)) = _
          rw [hnuRotation_apply_fixedOutside_mixedF child I.base.nu
            true false (by decide)]
          simp [JenningsHistory.dalzellExtendedH]
  | inr outputUnit =>
      cases input with
      | inl input =>
          rw [hnuControl_apply_inlF]
          change applyOperator
              (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                (hnuRotationCircuitF child I.base.nu))
              (fixedOutsideStateEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout true)
                (applyOperator
                  (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                    child.circuit.circuit)
                  (basisKet (child.embedding input))))
              (fixedOutsideBasisEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout false)
                child.inrBasis) = _
          rw [hnuRotation_apply_fixedOutside_mixedF child I.base.nu
            false true (by decide)]
          simp [JenningsHistory.dalzellExtendedH]
      | inr input =>
          cases input
          rw [hnuControl_apply_inrF]
          change applyOperator
              (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                (hnuRotationCircuitF child I.base.nu))
              (fixedOutsideStateEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout false)
                (basisKet child.inrBasis))
              (fixedOutsideBasisEmbedding
                (externalLayout119 child.layout).placement
                (branchOutside119 child.layout false)
                child.inrBasis) = _
          rw [hnuRotation_apply_fixedOutsideF]
          rw [hnu_cos_halfF I.base.nu hnu]
          simp [basisKet, JenningsHistory.dalzellExtendedH]

theorem hnuRotationCircuitF_normalized
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) (nu : ℝ) :
    IsNormalizedCircuit (hnuRotationCircuitF child nu) := by
  intro gate member
  cases gate <;>
    simp [ControlledCircuitCompilerV2.IsNormalizedPrimitive]

theorem hnuExtensionCircuitF_normalized
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) (nu : ℝ) :
    IsNormalizedCircuit (hnuExtensionCircuitF child nu) := by
  intro gate member
  simp [hnuExtensionCircuitF, Circuit.flatten] at member
  rcases member with member | member
  · exact (controlCircuit child.layout child.circuit).normalized gate member
  · exact hnuRotationCircuitF_normalized child nu gate member

def hnuExtensionNormalizedF
    {d c r m R : Nat} {I : P18Input119 d c r m R}
    (child : InternalHHistoryCleanComponentF I targetQubits) (nu : ℝ) :
    NormalizedCircuit targetQubits :=
  { circuit := hnuExtensionCircuitF child nu
    normalized := hnuExtensionCircuitF_normalized child nu }

theorem qBPlus_dalzellExtendedH_eq_gNuOperatorF
    {d c r m R : Nat}
    (system : JenningsHistory.HistorySpec d c r m R)
    (alpha nu : ℝ) :
    JenningsHistory.qBPlusMatrix (JenningsHistory.dalzellBPlus system) *
        JenningsHistory.dalzellExtendedH system alpha nu =
      GramOperator.gNuOperator system alpha nu := by
  rfl

theorem p18_qBPlus_dalzellExtendedH_eq_gNuOperatorF
    {d c r m R : Nat} (I : P18Input119 d c r m R) :
    JenningsHistory.qBPlusMatrix (p18BPlus119 I) *
        JenningsHistory.dalzellExtendedH I.base.system I.base.alpha I.base.nu =
      GramOperator.gNuOperator I.base.system I.base.alpha I.base.nu := by
  rw [p18BPlus119_eq_dalzell]
  exact qBPlus_dalzellExtendedH_eq_gNuOperatorF
    I.base.system I.base.alpha I.base.nu

end
end ExecutableHistoryImplementationRole
