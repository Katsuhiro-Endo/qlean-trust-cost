import QLean.History.Implementation.HistoryPipelineAlignedPhysicalP18

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace ExecutableHistoryStateFromAmplitudeData

open Matrix
open VerifiedCircuitCore
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open ExecutableHistoryCore

noncomputable section

theorem fixedOutsideStateEmbedding_merge_apply119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (state : State (QubitBasis sourceQubits))
    (input : QubitBasis sourceQubits) :
    fixedOutsideStateEmbedding placement outside state
        (mergePlacedAndOutsideBasis placement input outside) = state input := by
  rw [fixedOutsideStateEmbedding,
    if_pos (restrictToOutsideWires_mergePlacedAndOutsideBasis
      placement input outside),
    restrictToPlacedWires_mergePlacedAndOutsideBasis]

theorem fixedOutsideStateEmbedding_merge_apply_ne119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside expected : OutsideWire placement → Bool)
    (different : outside ≠ expected)
    (state : State (QubitBasis sourceQubits))
    (input : QubitBasis sourceQubits) :
    fixedOutsideStateEmbedding placement expected state
        (mergePlacedAndOutsideBasis placement input outside) = 0 := by
  rw [fixedOutsideStateEmbedding, if_neg]
  simpa only [restrictToOutsideWires_mergePlacedAndOutsideBasis] using different

def topControlOutside119 (n : Nat) :
    OutsideWire (lowerPlacement119 n) :=
  ⟨topControl119 n, by
    intro source equal
    have hvalue := congrArg (fun value : Fin (n + 3) => value.val) equal
    simp [lowerPlacement119, topControl119] at hvalue
    omega⟩

theorem branchOutside_true_ne_false119 (n : Nat) :
    (fun wire : OutsideWire (lowerPlacement119 n) =>
      if wire.1 = topControl119 n then true else false) ≠
    (fun wire : OutsideWire (lowerPlacement119 n) =>
      if wire.1 = topControl119 n then false else false) := by
  intro equal
  have hvalue := congrFun equal (topControlOutside119 n)
  simp [topControlOutside119] at hvalue

theorem imageSupported119.smul {n : Nat} (scalar : ℂ)
    {state : State (QubitBasis (prepWidth023 n))}
    (hstate : imageSupported119 state) :
    imageSupported119 (scalar • state) := by
  intro basis notImage
  simp [hstate basis notImage]

theorem imageSupported119.add {n : Nat}
    {left right : State (QubitBasis (prepWidth023 n))}
    (hleft : imageSupported119 left) (hright : imageSupported119 right) :
    imageSupported119 (left + right) := by
  intro basis notImage
  simp [hleft basis notImage, hright basis notImage]

theorem dataBasisEmbedding119_succ_decompose (n : Nat)
    (input : QubitBasis (n + 1)) :
    dataBasisEmbedding119 (n + 1) input =
      mergePlacedAndOutsideBasis (lowerPlacement119 (prepWidth023 n))
        (dataBasisEmbedding119 n (fun wire => input wire.castSucc))
        (fun wire => if wire.1 = topControl119 (prepWidth023 n)
          then input (Fin.last n) else false) := by
  apply (fullBasis_eq_iff_restrictions_eq
    (lowerPlacement119 (prepWidth023 n)) _ _).2
  constructor
  · funext wire
    rw [restrictToPlacedWires_mergePlacedAndOutsideBasis]
    change mergePlacedAndOutsideBasis (dataPlacement023 (n + 1)) input
        dataOutsideZero023 (lowerPlacement119 (prepWidth023 n) wire) =
      mergePlacedAndOutsideBasis (dataPlacement023 n)
        (fun source => input source.castSucc) dataOutsideZero023 wire
    by_cases h : ∃ source : Fin n, dataPlacement023 n source = wire
    · let source : Fin n := Classical.choose h
      have hsource : dataPlacement023 n source = wire := Classical.choose_spec h
      have hsucc : dataPlacement023 (n + 1) source.castSucc =
          lowerPlacement119 (prepWidth023 n) wire := by
        apply Fin.ext
        simp [dataPlacement023, lowerPlacement119, source, hsource]
      have hsuccExists : ∃ source' : Fin (n + 1),
          dataPlacement023 (n + 1) source' =
            lowerPlacement119 (prepWidth023 n) wire := ⟨source.castSucc, hsucc⟩
      unfold mergePlacedAndOutsideBasis
      rw [dif_pos h, dif_pos hsuccExists]
      congr 1
      apply (dataPlacement023 (n + 1)).injective
      exact (Classical.choose_spec hsuccExists).trans hsucc.symm
    · have hsuccNone : ¬ ∃ source : Fin (n + 1),
          dataPlacement023 (n + 1) source =
            lowerPlacement119 (prepWidth023 n) wire := by
        rintro ⟨source, hsource⟩
        by_cases hlt : source.val < n
        · apply h
          refine ⟨⟨source.val, hlt⟩, ?_⟩
          apply Fin.ext
          have hvalue := congrArg
            (fun value : Fin (prepWidth023 (n + 1)) => value.val) hsource
          simp [dataPlacement023, hlt, lowerPlacement119] at hvalue
          exact hvalue
        · have hlast : source.val = n := by omega
          have hvalue := congrArg
            (fun value : Fin (prepWidth023 (n + 1)) => value.val) hsource
          simp [dataPlacement023, hlt, lowerPlacement119] at hvalue
          have hwire := wire.isLt
          omega
      simp [mergePlacedAndOutsideBasis, h, hsuccNone, dataOutsideZero023]
  · funext wire
    rw [restrictToOutsideWires_mergePlacedAndOutsideBasis]
    change mergePlacedAndOutsideBasis (dataPlacement023 (n + 1)) input
        dataOutsideZero023 wire.1 =
      (if wire.1 = topControl119 (prepWidth023 n)
        then input (Fin.last n) else false)
    by_cases htop : wire.1 = topControl119 (prepWidth023 n)
    · have hlast : dataPlacement023 (n + 1) (Fin.last n) = wire.1 := by
        rw [htop]
        apply Fin.ext
        simp [dataPlacement023, topControl119]
      have hexists : ∃ source : Fin (n + 1),
          dataPlacement023 (n + 1) source = wire.1 := ⟨Fin.last n, hlast⟩
      unfold mergePlacedAndOutsideBasis
      rw [dif_pos hexists, if_pos htop]
      congr 1
      apply (dataPlacement023 (n + 1)).injective
      exact (Classical.choose_spec hexists).trans hlast.symm
    · have hnone : ¬ ∃ source : Fin (n + 1),
          dataPlacement023 (n + 1) source = wire.1 := by
        rintro ⟨source, hsource⟩
        by_cases hlt : source.val < n
        · apply wire.property (dataPlacement023 n ⟨source.val, hlt⟩)
          apply Fin.ext
          have hvalue := congrArg
            (fun value : Fin (prepWidth023 (n + 1)) => value.val) hsource
          simp [dataPlacement023, hlt, lowerPlacement119] at hvalue
          exact hvalue
        · apply htop
          apply Fin.ext
          have hlast : source.val = n := by omega
          have hvalue := congrArg
            (fun value : Fin (prepWidth023 (n + 1)) => value.val) hsource
          simp [dataPlacement023, hlt] at hvalue
          exact hvalue.symm
      simp [mergePlacedAndOutsideBasis, htop, hnone, dataOutsideZero023]

theorem lowerBranchEmbedding_imageSupported119 (n : Nat)
    (controlValue : Bool)
    (state : State (QubitBasis (prepWidth023 n)))
    (hstate : imageSupported119 state) :
    imageSupported119 (n := n + 1)
      (fixedOutsideStateEmbedding
        (lowerPlacement119 (prepWidth023 n))
        (fun wire => if wire.1 = topControl119 (prepWidth023 n)
          then controlValue else false)
        state) := by
  intro output notImage
  let branchOutside : OutsideWire
      (lowerPlacement119 (prepWidth023 n)) → Bool :=
    fun wire => if wire.1 = topControl119 (prepWidth023 n)
      then controlValue else false
  by_cases houtside : restrictToOutsideWires
      (lowerPlacement119 (prepWidth023 n)) output = branchOutside
  · rw [fixedOutsideStateEmbedding, if_pos]
    · let internal := restrictToPlacedWires
          (lowerPlacement119 (prepWidth023 n)) output
      by_cases hinternal : ∃ input : QubitBasis n,
          dataBasisEmbedding119 n input = internal
      · let input : QubitBasis n := Classical.choose hinternal
        have hinput : dataBasisEmbedding119 n input = internal :=
          Classical.choose_spec hinternal
        let successor : QubitBasis (n + 1) :=
          combineHighestSelector controlValue input
        have pairEq := (splitHighestSelectorEquiv n).apply_symm_apply
          (controlValue, input)
        have highEq : successor (Fin.last n) = controlValue := by
          exact congrArg Prod.fst pairEq
        have lowEq : (fun wire => successor wire.castSucc) = input := by
          exact congrArg Prod.snd pairEq
        have successorEmbedding :=
          dataBasisEmbedding119_succ_decompose n successor
        rw [lowEq, highEq] at successorEmbedding
        have outputMerge : mergePlacedAndOutsideBasis
            (lowerPlacement119 (prepWidth023 n)) internal branchOutside =
            output := by
          rw [← houtside]
          exact mergePlacedAndOutsideBasis_restrict _ _
        have embeddingEq : dataBasisEmbedding119 (n + 1) successor =
            output := by
          rw [successorEmbedding, hinput, outputMerge]
        exact (notImage successor embeddingEq).elim
      · exact hstate internal (by simpa [internal] using hinternal)
    · exact houtside
  · change ¬ restrictToOutsideWires
        (lowerPlacement119 (prepWidth023 n)) output =
        (fun wire => if wire.1 = topControl119 (prepWidth023 n)
          then controlValue else false) at houtside
    unfold fixedOutsideStateEmbedding
    split
    · rename_i equal
      exact (houtside equal).elim
    · rfl

theorem stateFromAmplitude023_imageSupported119 :
    ∀ n (_positive : 0 < n) (amplitude : QubitBasis n → ℝ),
      imageSupported119 (stateFromAmplitude023 n amplitude) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro _positive amplitude
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              change imageSupported119 (n := 1)
                (fixedOutsideStateEmbedding (topPlacement119 0)
                  (topOutsideZero119 0)
                  (q1CosSinState119 (q1SignedAngle023 amplitude)))
              intro basis notImage
              by_cases houtside : restrictToOutsideWires
                  (topPlacement119 0) basis = topOutsideZero119 0
              · exfalso
                let internal := restrictToPlacedWires (topPlacement119 0) basis
                apply notImage internal
                apply (fullBasis_eq_iff_restrictions_eq
                  (topPlacement119 0) _ _).2
                constructor
                · change restrictToPlacedWires (topPlacement119 0)
                      (mergePlacedAndOutsideBasis (topPlacement119 0)
                        internal (topOutsideZero119 0)) = _
                  rw [restrictToPlacedWires_mergePlacedAndOutsideBasis]
                · change restrictToOutsideWires (topPlacement119 0)
                      (mergePlacedAndOutsideBasis (topPlacement119 0)
                        internal (topOutsideZero119 0)) = _
                  rw [restrictToOutsideWires_mergePlacedAndOutsideBasis]
                  exact houtside.symm
              · unfold fixedOutsideStateEmbedding
                split
                · rename_i equal
                  exact (houtside equal).elim
                · rfl
          | succ k =>
              simp only [stateFromAmplitude023]
              apply imageSupported119.add
              · apply imageSupported119.smul
                exact lowerBranchEmbedding_imageSupported119 (k + 1) false
                  _ (ih (k + 1) (by omega) (by omega) _)
              · apply imageSupported119.smul
                exact lowerBranchEmbedding_imageSupported119 (k + 1) true
                  _ (ih (k + 1) (by omega) (by omega) _)

theorem stateFromAmplitude023_data_entry119 :
    ∀ n (_positive : 0 < n) (amplitude : QubitBasis n → ℝ),
      realEnergy023 amplitude = 1 →
        ∀ input : QubitBasis n,
          stateFromAmplitude023 n amplitude (dataBasisEmbedding119 n input) =
            (amplitude input : ℂ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro _positive amplitude normOne input
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              change fixedOutsideStateEmbedding (topPlacement119 0)
                  (topOutsideZero119 0)
                  (q1CosSinState119 (q1SignedAngle023 amplitude))
                  (mergePlacedAndOutsideBasis (topPlacement119 0) input
                    (topOutsideZero119 0)) = _
              rw [fixedOutsideStateEmbedding,
                if_pos (restrictToOutsideWires_mergePlacedAndOutsideBasis
                  (topPlacement119 0) input (topOutsideZero119 0)),
                restrictToPlacedWires_mergePlacedAndOutsideBasis]
              exact congrFun (q1SignedState023 normOne) input
          | succ k =>
              let lower : QubitBasis (k + 1) :=
                fun wire => input wire.castSucc
              let highest : Bool := input (Fin.last (k + 1))
              have inputEq : combineHighestSelector highest lower = input := by
                exact (splitHighestSelectorEquiv (k + 1)).symm_apply_apply input
              rw [dataBasisEmbedding119_succ_decompose (k + 1) input]
              simp only [stateFromAmplitude023, Pi.add_apply, Pi.smul_apply]
              cases hhighest : highest with
              | false =>
                  have hinputHighest : input (Fin.last (k + 1)) = false := by
                    exact hhighest
                  have hleft := ih (k + 1) (by omega)
                    (by omega)
                    (normalizedBranchAmplitude023 false amplitude)
                    (normalizedBranchAmplitude023_norm false amplitude)
                    lower
                  have houtside :
                      (fun wire : OutsideWire
                        (lowerPlacement119 (prepWidth023 (k + 1))) =>
                        if wire.1 = topControl119 (prepWidth023 (k + 1))
                          then input (Fin.last (k + 1)) else false) =
                      (fun wire : OutsideWire
                        (lowerPlacement119 (prepWidth023 (k + 1))) =>
                        if wire.1 = topControl119 (prepWidth023 (k + 1))
                          then false else false) := by
                    funext wire
                    simp [hinputHighest]
                  rw [houtside,
                    fixedOutsideStateEmbedding_merge_apply119,
                    fixedOutsideStateEmbedding_merge_apply_ne119
                      (different :=
                        (branchOutside_true_ne_false119
                          (prepWidth023 (k + 1))).symm),
                    hleft]
                  simp only [smul_eq_mul, mul_zero, add_zero]
                  norm_cast
                  rw [normalizedBranchAmplitude023_mul_norm]
                  unfold branchAmplitude119
                  have hcombine : combineHighestSelector false lower = input := by
                    rw [← hhighest]
                    exact inputEq
                  rw [hcombine]
              | true =>
                  have hinputHighest : input (Fin.last (k + 1)) = true := by
                    exact hhighest
                  have hright := ih (k + 1) (by omega)
                    (by omega)
                    (normalizedBranchAmplitude023 true amplitude)
                    (normalizedBranchAmplitude023_norm true amplitude)
                    lower
                  have houtside :
                      (fun wire : OutsideWire
                        (lowerPlacement119 (prepWidth023 (k + 1))) =>
                        if wire.1 = topControl119 (prepWidth023 (k + 1))
                          then input (Fin.last (k + 1)) else false) =
                      (fun wire : OutsideWire
                        (lowerPlacement119 (prepWidth023 (k + 1))) =>
                        if wire.1 = topControl119 (prepWidth023 (k + 1))
                          then true else false) := by
                    funext wire
                    simp [hinputHighest]
                  rw [houtside,
                    fixedOutsideStateEmbedding_merge_apply_ne119
                      (different := branchOutside_true_ne_false119
                        (prepWidth023 (k + 1))),
                    fixedOutsideStateEmbedding_merge_apply119,
                    hright]
                  simp only [smul_eq_mul, mul_zero, zero_add]
                  norm_cast
                  rw [normalizedBranchAmplitude023_mul_norm]
                  unfold branchAmplitude119
                  have hcombine : combineHighestSelector true lower = input := by
                    rw [← hhighest]
                    exact inputEq
                  rw [hcombine]

end
end ExecutableHistoryStateFromAmplitudeData
