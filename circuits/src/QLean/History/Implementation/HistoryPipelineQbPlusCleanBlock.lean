import QLean.History.Implementation.HistoryPipelineHistoryExtendedBlocks

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace ExecutableHistoryQbPlusCleanBlock

open VerifiedCircuitCore
open VerifiedCircuitCore.ControlledCircuitCompilerV2
open ExecutableHistoryCore

noncomputable section

/-! The block register contains a preparation register, an independent scratch
    register, and one signal wire.  The signal is the last wire. -/

def blockQubits119 (n : Nat) : Nat := n + n + 1

def dataWire119 (n : Nat) (i : Fin n) : Fin (blockQubits119 n) :=
  ⟨i.1, by dsimp [blockQubits119]; omega⟩

def scratchWire119 (n : Nat) (i : Fin n) : Fin (blockQubits119 n) :=
  ⟨n + i.1, by dsimp [blockQubits119]; omega⟩

def signalWire119 (n : Nat) : Fin (blockQubits119 n) :=
  ⟨n + n, by dsimp [blockQubits119]; omega⟩

def dataPlacement119 (n : Nat) : Fin n ↪ Fin (blockQubits119 n) :=
  { toFun := dataWire119 n
    inj' := by
      intro i j h
      apply Fin.ext
      exact congrArg (fun z : Fin (blockQubits119 n) => z.val) h }

def dataControls119 (n : Nat) : List (Fin (blockQubits119 n) × Bool) :=
  (List.finRange n).map
    (fun i => (dataWire119 n i, false))

def dataScratch119 (n : Nat) : List (Fin (blockQubits119 n)) :=
  (List.finRange n).map (scratchWire119 n)

theorem dataControls119_length (n : Nat) :
    (dataControls119 n).length = n := by
  simp [dataControls119]

theorem dataScratch119_length (n : Nat) :
    (dataScratch119 n).length = n := by
  simp [dataScratch119]

theorem dataControls119_fst_nodup (n : Nat) :
    (dataControls119 n).map Prod.fst |>.Nodup := by
  unfold dataControls119
  simp only [List.map_map]
  apply List.Nodup.map
  · intro i j h
    apply Fin.ext
    exact congrArg (fun z : Fin (blockQubits119 n) => z.val) h
  · exact List.nodup_finRange n

theorem dataScratch119_nodup (n : Nat) :
    (dataScratch119 n).Nodup := by
  unfold dataScratch119
  apply List.Nodup.map
  · intro i j h
    apply Fin.ext
    have hv := congrArg (fun z : Fin (blockQubits119 n) => z.val) h
    dsimp [scratchWire119] at hv
    omega
  · exact List.nodup_finRange n

theorem dataWire119_ne_scratchWire119 {n : Nat}
    (i j : Fin n) : dataWire119 n i ≠ scratchWire119 n j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [dataWire119, scratchWire119] at hv
  omega

theorem dataWire119_ne_signalWire119 {n : Nat}
    (i : Fin n) : dataWire119 n i ≠ signalWire119 n := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [dataWire119, signalWire119] at hv
  omega

theorem scratchWire119_ne_signalWire119 {n : Nat}
    (i : Fin n) : scratchWire119 n i ≠ signalWire119 n := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [scratchWire119, signalWire119] at hv
  omega

theorem dataControlLayout119_nodup (n : Nat) :
    ((dataControls119 n).map Prod.fst ++ dataScratch119 n ++
      [signalWire119 n]).Nodup := by
  rw [List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.nodup_append]
    refine ⟨dataControls119_fst_nodup n, dataScratch119_nodup n, ?_⟩
    intro a ha b hb
    rcases List.mem_map.1 ha with ⟨p, hp, rfl⟩
    rcases List.mem_map.1 hp with ⟨i, hi, rfl⟩
    rcases List.mem_map.1 hb with ⟨j, hj, rfl⟩
    exact dataWire119_ne_scratchWire119 i j
  · intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_map.1 ha with ⟨p, hp, rfl⟩
      rcases List.mem_map.1 hp with ⟨i, hi, rfl⟩
      exact dataWire119_ne_signalWire119 i
    · rcases List.mem_map.1 ha with ⟨i, hi, rfl⟩
      exact scratchWire119_ne_signalWire119 i

def zeroDataSignalFlip119 (n : Nat) :
    Circuit (PrimitiveGate (blockQubits119 n)) :=
  Circuit.boolMultiControlledRy (dataControls119 n) (dataScratch119 n)
    (signalWire119 n) AngleExpr.pi

theorem zeroDataSignalFlip119_enoughScratch (n : Nat) :
    (dataControls119 n).length ≤ (dataScratch119 n).length + 1 := by
  rw [dataControls119_length, dataScratch119_length]
  omega

def liftedPreparation119 {n : Nat}
    (preparation : NormalizedCircuit n) :
    NormalizedCircuit (blockQubits119 n) :=
  NormalizedCircuit.mapWires (dataPlacement119 n) preparation

def unliftedPreparation119 {n : Nat}
    (preparation : NormalizedCircuit n) :
    NormalizedCircuit (blockQubits119 n) :=
  (liftedPreparation119 preparation).inverse

def qBPlusBlockCircuit119 {n : Nat}
    (preparation : NormalizedCircuit n) :
    Circuit (PrimitiveGate (blockQubits119 n)) :=
  Circuit.sequence [
    (unliftedPreparation119 preparation).circuit,
    zeroDataSignalFlip119 n,
    (liftedPreparation119 preparation).circuit]

def blockBasis119 {n : Nat} (input : QubitBasis n) :
    QubitBasis (blockQubits119 n) :=
  fixedOutsideBasisEmbedding (dataPlacement119 n) (fun _ => false) input

theorem blockBasis119_injective {n : Nat} :
    Function.Injective (blockBasis119 (n := n)) := by
  intro input output h
  calc
    input = restrictToPlacedWires (dataPlacement119 n)
        (blockBasis119 input) := by
          symm
          change restrictToPlacedWires (dataPlacement119 n)
              (mergePlacedAndOutsideBasis (dataPlacement119 n) input
                (fun _ => false)) = input
          exact restrictToPlacedWires_mergePlacedAndOutsideBasis _ _ _
    _ = restrictToPlacedWires (dataPlacement119 n)
        (blockBasis119 output) := by rw [h]
    _ = output := by
          change restrictToPlacedWires (dataPlacement119 n)
              (mergePlacedAndOutsideBasis (dataPlacement119 n) output
                (fun _ => false)) = output
          exact restrictToPlacedWires_mergePlacedAndOutsideBasis _ _ _

theorem blockBasis119_data {n : Nat} (input : QubitBasis n)
    (wire : Fin n) :
    blockBasis119 input (dataWire119 n wire) = input wire := by
  classical
  unfold blockBasis119 fixedOutsideBasisEmbedding
  change mergePlacedAndOutsideBasis (dataPlacement119 n) input
      (fun _ => false) (dataWire119 n wire) = input wire
  by_cases h : ∃ source, dataPlacement119 n source = dataWire119 n wire
  · have hc : Classical.choose h = wire := by
      apply (dataPlacement119 n).injective
      calc
        dataPlacement119 n (Classical.choose h) = dataWire119 n wire :=
          Classical.choose_spec h
        _ = dataPlacement119 n wire := rfl
    simp [mergePlacedAndOutsideBasis, h, hc]
  · exact (h ⟨wire, rfl⟩).elim

theorem blockBasis119_scratch {n : Nat} (input : QubitBasis n)
    (wire : Fin n) :
    blockBasis119 input (scratchWire119 n wire) = false := by
  classical
  unfold blockBasis119 fixedOutsideBasisEmbedding
  change mergePlacedAndOutsideBasis (dataPlacement119 n) input
      (fun _ => false) (scratchWire119 n wire) = false
  have hno : ¬ ∃ source, dataPlacement119 n source = scratchWire119 n wire := by
    rintro ⟨source, hsource⟩
    exact dataWire119_ne_scratchWire119 source wire hsource
  simp [mergePlacedAndOutsideBasis, hno]

theorem blockBasis119_signal {n : Nat} (input : QubitBasis n) :
    blockBasis119 input (signalWire119 n) = false := by
  classical
  unfold blockBasis119 fixedOutsideBasisEmbedding
  change mergePlacedAndOutsideBasis (dataPlacement119 n) input
      (fun _ => false) (signalWire119 n) = false
  have hno : ¬ ∃ source, dataPlacement119 n source = signalWire119 n := by
    rintro ⟨source, hsource⟩
    exact dataWire119_ne_signalWire119 source hsource
  simp [mergePlacedAndOutsideBasis, hno]

theorem blockBasis119_agreesExcept_signal {n : Nat}
    (output input : QubitBasis n) :
    agreesExcept (signalWire119 n) (blockBasis119 output)
      (blockBasis119 input) ↔ output = input := by
  constructor
  · intro h
    funext wire
    have hwire := h (dataWire119 n wire) (dataWire119_ne_signalWire119 wire)
    simpa only [blockBasis119_data] using hwire
  · intro h
    subst input
    intro wire _
    rfl

theorem dataControls119_satisfied_iff {n : Nat}
    (input : QubitBasis n) :
    boolControlsSatisfied (dataControls119 n) (blockBasis119 input) =
      if input = zeroBasis119 n then true else false := by
  classical
  by_cases hzero : input = zeroBasis119 n
  · have hall : boolControlsSatisfied (dataControls119 n)
        (blockBasis119 input) = true := by
      subst input
      unfold boolControlsSatisfied
      apply (List.all_eq_true).2
      intro control hcontrol
      rcases List.mem_map.1 hcontrol with ⟨i, hi, hcontrol⟩
      subst control
      simp [blockBasis119_data, zeroBasis119]
    rw [hall]
    simp [hzero]
  · have hnot : boolControlsSatisfied (dataControls119 n)
        (blockBasis119 input) ≠ true := by
      intro hall
      have hcontrol := (List.all_eq_true.1 hall)
      have hinput : ∀ i : Fin n, input i = false := by
        intro i
        have hmem : (dataWire119 n i, false) ∈ dataControls119 n := by
          simp [dataControls119]
        have hone := hcontrol (dataWire119 n i, false) hmem
        simpa [blockBasis119_data] using hone
      apply hzero
      funext i
      simpa [zeroBasis119] using hinput i
    have hfalse : boolControlsSatisfied (dataControls119 n)
        (blockBasis119 input) = false := by
      cases hv : boolControlsSatisfied (dataControls119 n)
          (blockBasis119 input) with
      | false => rfl
      | true => exact (hnot hv).elim
    rw [hfalse]
    simp [hzero]

def signalZeroBlock119 {n : Nat}
    (operator : Operator (QubitBasis (blockQubits119 n))) :
    Matrix (QubitBasis n) (QubitBasis n) ℂ :=
  fun output input => operator (blockBasis119 output) (blockBasis119 input)

def zeroProjectorComplement119 (n : Nat) :
    Matrix (QubitBasis n) (QubitBasis n) ℂ := by
  classical
  exact fun output input =>
    (if output = input then (1 : ℂ) else 0) -
      (if output = zeroBasis119 n then (1 : ℂ) else 0) *
        (if input = zeroBasis119 n then (1 : ℂ) else 0)

def complexQbPlusMatrix119 {ι : Type} (b : ι → ℝ) :
    Matrix ι ι ℂ := by
  classical
  exact fun output input => (JenningsHistory.qBPlusMatrix b output input : ℂ)

theorem liftedPreparation119_denote {n : Nat}
    (preparation : NormalizedCircuit n) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (liftedPreparation119 preparation).circuit =
      wireLiftOperator (dataPlacement119 n)
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          preparation.circuit) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (preparation.circuit.mapGates (PrimitiveGate.mapWires
        (dataPlacement119 n))) = _
  exact denote_mapPrimitiveWires_eq_wireLiftOperator (fun _ => 0)
    (dataPlacement119 n) preparation.circuit

theorem star_wireLiftOperator119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (operator : Operator (QubitBasis sourceQubits)) :
    star (wireLiftOperator placement operator) =
      wireLiftOperator placement (star operator) := by
  classical
  ext output input
  by_cases houtside :
      restrictToOutsideWires placement output =
        restrictToOutsideWires placement input
  · simp [wireLiftOperator_apply, houtside]
  · simp [wireLiftOperator_apply, houtside]
    intro h
    exact (houtside h.symm).elim

theorem unliftedPreparation119_denote {n : Nat}
    (preparation : NormalizedCircuit n) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (unliftedPreparation119 preparation).circuit =
      star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (liftedPreparation119 preparation).circuit) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      (Circuit.reverse PrimitiveGate.inverse
        (liftedPreparation119 preparation).circuit) = _
  rw [primitiveCircuit_denote_reverse]

theorem qBPlusBlockCircuit119_denote {n : Nat}
    (preparation : NormalizedCircuit n) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (qBPlusBlockCircuit119 preparation) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (liftedPreparation119 preparation).circuit *
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (zeroDataSignalFlip119 n) *
        star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (liftedPreparation119 preparation).circuit) := by
  unfold qBPlusBlockCircuit119
  rw [Circuit.denote_sequence_eq_operatorSequence]
  simp [operatorSequence, unliftedPreparation119_denote, mul_assoc]

theorem zeroDataSignalFlip119_block_entry {n : Nat}
    (output input : QubitBasis n) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (zeroDataSignalFlip119 n)
        (blockBasis119 output) (blockBasis119 input) =
      (if output = input then (1 : ℂ) else 0) -
        (if output = zeroBasis119 n then (1 : ℂ) else 0) *
          (if input = zeroBasis119 n then (1 : ℂ) else 0) := by
  rw [zeroDataSignalFlip119]
  rw [boolMultiControlledRy_apply_sparse
    (dataControls119 n) (dataScratch119 n) (signalWire119 n)
    AngleExpr.pi (blockBasis119 output) (blockBasis119 input)
    (zeroDataSignalFlip119_enoughScratch n)
    (dataControlLayout119_nodup n)]
  · by_cases hEq : output = input
    · subst input
      by_cases hZero : output = zeroBasis119 n
      · subst output
        have hagree :
            agreesExcept (signalWire119 n) (blockBasis119 (zeroBasis119 n))
              (blockBasis119 (zeroBasis119 n)) :=
          (blockBasis119_agreesExcept_signal _ _).2 rfl
        have hctrl :
            boolControlsSatisfied (dataControls119 n)
              (blockBasis119 (zeroBasis119 n)) = true := by
          rw [dataControls119_satisfied_iff]
          simp
        have hsig : blockBasis119 (zeroBasis119 n) (signalWire119 n) = false :=
          blockBasis119_signal _
        rw [boolControlledRyAmplitude, if_pos hagree, if_pos hctrl, hsig]
        rw [show AngleExpr.pi.uniformValue = Real.pi by rfl]
        simp [localRy]
      · simp [boolControlledRyAmplitude, blockBasis119_agreesExcept_signal,
          dataControls119_satisfied_iff, blockBasis119_signal,
          hZero]
    · have hNotAgree :
          ¬ agreesExcept (signalWire119 n) (blockBasis119 output)
            (blockBasis119 input) := by
        intro hAgree
        exact hEq ((blockBasis119_agreesExcept_signal output input).1 hAgree)
      rw [boolControlledRyAmplitude, if_neg hNotAgree]
      simp only [if_neg hEq]
      by_cases hOutZero : output = zeroBasis119 n
      · have hInZero : ¬ input = zeroBasis119 n := by
          intro hIn
          exact hEq (hOutZero.trans hIn.symm)
        simp [hOutZero, hInZero]
      · simp [hOutZero]
  · intro wire hwire
    rcases List.mem_map.1 hwire with ⟨i, hi, rfl⟩
    exact blockBasis119_scratch input i

theorem fixedOutsideDataBasis119 {n : Nat} (input : QubitBasis n) :
    fixedOutsideStateEmbedding (dataPlacement119 n) (fun _ => false)
        (basisKet input) = basisKet (blockBasis119 input) := by
  rw [fixedOutsideStateEmbedding_basisKet]
  rfl

theorem unliftedPreparation119_apply_blockBasis {n : Nat}
    (preparation : NormalizedCircuit n) (input : QubitBasis n) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (unliftedPreparation119 preparation).circuit)
        (basisKet (blockBasis119 input)) =
      fixedOutsideStateEmbedding (dataPlacement119 n) (fun _ => false)
        (applyOperator
          (star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            preparation.circuit)) (basisKet input)) := by
  rw [← fixedOutsideDataBasis119 input, unliftedPreparation119_denote,
    liftedPreparation119_denote, star_wireLiftOperator119,
    applyOperator_wireLift_fixedOutsideState119]

theorem zeroDataSignalFlip119_clean_action {n : Nat}
    (state : State (QubitBasis n)) (output : QubitBasis n) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (zeroDataSignalFlip119 n))
        (fixedOutsideStateEmbedding (dataPlacement119 n) (fun _ => false)
          state) (blockBasis119 output) =
      applyOperator (zeroProjectorComplement119 n) state output := by
  unfold applyOperator Matrix.mulVec dotProduct
  rw [← (splitWireEmbeddingEquiv (dataPlacement119 n)).symm.sum_comp]
  have hentry (input : QubitBasis n) :
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (zeroDataSignalFlip119 n) (blockBasis119 output)
            (mergePlacedAndOutsideBasis (dataPlacement119 n) input
              (fun _ => false)) =
        applyOperator (zeroProjectorComplement119 n)
          (basisKet input) output := by
    rw [show mergePlacedAndOutsideBasis (dataPlacement119 n) input
        (fun _ => false) = blockBasis119 input by rfl]
    unfold applyOperator Matrix.mulVec dotProduct basisKet
    simp [zeroDataSignalFlip119_block_entry,
      zeroProjectorComplement119]
  simp [fixedOutsideStateEmbedding, splitWireEmbeddingEquiv,
    Fintype.sum_prod_type, hentry]

theorem applyOperator_basisKet119 {α : Type} [Fintype α] [DecidableEq α]
    (operator : Matrix α α ℂ)
    (output input : α) :
    applyOperator operator (basisKet input) output = operator output input := by
  unfold applyOperator Matrix.mulVec dotProduct basisKet
  simp

theorem wireLiftOperator_apply_blockBasis119 {n : Nat}
    (operator : Operator (QubitBasis n)) (state : State (QubitBasis (blockQubits119 n)))
    (output : QubitBasis n) :
    applyOperator (wireLiftOperator (dataPlacement119 n) operator) state
        (blockBasis119 output) =
      ∑ input : QubitBasis n, operator output input * state (blockBasis119 input) := by
  have hPlaced :
      restrictToPlacedWires (dataPlacement119 n) (blockBasis119 output) = output := by
    change restrictToPlacedWires (dataPlacement119 n)
        (mergePlacedAndOutsideBasis (dataPlacement119 n) output
          (fun _ => false)) = output
    exact restrictToPlacedWires_mergePlacedAndOutsideBasis _ _ _
  have hOutside :
      restrictToOutsideWires (dataPlacement119 n) (blockBasis119 output) =
        (fun _ => false) := by
    change restrictToOutsideWires (dataPlacement119 n)
        (mergePlacedAndOutsideBasis (dataPlacement119 n) output
          (fun _ => false)) = (fun _ => false)
    exact restrictToOutsideWires_mergePlacedAndOutsideBasis _ _ _
  have hMerge (input : QubitBasis n) :
      mergePlacedAndOutsideBasis (dataPlacement119 n) input
        (fun _ => false) = blockBasis119 input := by
    rfl
  unfold applyOperator Matrix.mulVec dotProduct
  rw [← (splitWireEmbeddingEquiv (dataPlacement119 n)).symm.sum_comp]
  simp [wireLiftOperator_apply, splitWireEmbeddingEquiv,
    Fintype.sum_prod_type, hPlaced, hOutside, hMerge]

def pointProjector119 {α : Type} [DecidableEq α] (e : α) : Matrix α α ℂ :=
  fun i j => if i = e ∧ j = e then 1 else 0

theorem sandwich_pointProjector119 {α : Type} [Fintype α] [DecidableEq α]
    (operator right : Matrix α α ℂ) (e i j : α) :
    (operator * pointProjector119 e * right) i j =
      operator i e * right e j := by
  classical
  simp only [Matrix.mul_apply]
  have inner (x : α) :
      (∑ y, operator i y * pointProjector119 e y x) =
        (if x = e then operator i e else 0) := by
    by_cases hx : x = e
    · subst x
      simp [pointProjector119]
    · simp [pointProjector119, hx]
  calc
    (∑ x, (∑ y, operator i y * pointProjector119 e y x) * right x j) =
        ∑ x, (if x = e then operator i e else 0) * right x j := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [inner]
    _ = operator i e * right e j := by simp

theorem zeroProjectorComplement119_as_sub (n : Nat) :
    zeroProjectorComplement119 n =
      1 - pointProjector119 (zeroBasis119 n) := by
  classical
  ext output input
  by_cases ho : output = zeroBasis119 n <;>
    by_cases hi : input = zeroBasis119 n <;>
      simp [zeroProjectorComplement119, pointProjector119,
        Matrix.one_apply, ho, hi, eq_comm]

theorem conjugated_zeroProjectorComplement119 {n : Nat}
    (operator : Operator (QubitBasis n))
    (unitaryRight : operator * star operator = 1) :
    operator * zeroProjectorComplement119 n * star operator =
      fun output input =>
        (if output = input then (1 : ℂ) else 0) -
          operator output (zeroBasis119 n) *
            star operator (zeroBasis119 n) input := by
  rw [zeroProjectorComplement119_as_sub]
  calc
    operator * (1 - pointProjector119 (zeroBasis119 n)) * star operator =
        (operator * 1 - operator * pointProjector119 (zeroBasis119 n)) *
          star operator := by rw [mul_sub]
    _ = operator * star operator -
          (operator * pointProjector119 (zeroBasis119 n)) * star operator := by
      rw [sub_mul, mul_one]
    _ = 1 - (operator * pointProjector119 (zeroBasis119 n)) * star operator := by
      rw [unitaryRight]
    _ = fun output input =>
        (if output = input then (1 : ℂ) else 0) -
          operator output (zeroBasis119 n) *
            star operator (zeroBasis119 n) input := by
      ext output input
      change (if output = input then (1 : ℂ) else 0) -
          (operator * pointProjector119 (zeroBasis119 n) * star operator)
            output input = _
      rw [sandwich_pointProjector119]

theorem preparation119_unitary_right {n : Nat}
    (preparation : NormalizedCircuit n) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) preparation.circuit *
        star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          preparation.circuit) = 1 := by
  have hmem :
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) preparation.circuit ∈
        Matrix.unitaryGroup (QubitBasis n) ℂ :=
    primitiveCircuit_denote_mem_unitaryGroup (fun _ => 0) preparation.circuit
  have hleft :
      star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) preparation.circuit) *
          Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) preparation.circuit = 1 :=
    (Matrix.mem_unitaryGroup_iff').1 hmem
  have hright := (Matrix.mem_unitaryGroup_iff).1 hmem
  exact hright

theorem qBPlusBlockCircuit119_clean_block_unconjugated {n : Nat}
    (preparation : NormalizedCircuit n) :
    signalZeroBlock119
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (qBPlusBlockCircuit119 preparation)) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          preparation.circuit * zeroProjectorComplement119 n *
        star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          preparation.circuit) := by
  rw [qBPlusBlockCircuit119_denote]
  have hstar (input : QubitBasis n) :
      applyOperator
          (star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (liftedPreparation119 preparation).circuit))
          (basisKet (blockBasis119 input)) =
        fixedOutsideStateEmbedding (dataPlacement119 n) (fun _ => false)
          (applyOperator
            (star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              preparation.circuit)) (basisKet input)) := by
    rw [← unliftedPreparation119_denote]
    exact unliftedPreparation119_apply_blockBasis preparation input
  ext output input
  change
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (liftedPreparation119 preparation).circuit *
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (zeroDataSignalFlip119 n) *
      star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (liftedPreparation119 preparation).circuit))
      (blockBasis119 output) (blockBasis119 input) =
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        preparation.circuit * zeroProjectorComplement119 n *
      star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        preparation.circuit)) output input
  calc
    _ = applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (liftedPreparation119 preparation).circuit *
          Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (zeroDataSignalFlip119 n) *
          star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (liftedPreparation119 preparation).circuit))
        (basisKet (blockBasis119 input)) (blockBasis119 output) := by
          symm
          exact applyOperator_basisKet119 _ _ _
    _ = applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (liftedPreparation119 preparation).circuit)
        (applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (zeroDataSignalFlip119 n))
          (applyOperator
            (star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              (liftedPreparation119 preparation).circuit))
            (basisKet (blockBasis119 input)))) (blockBasis119 output) := by
          rw [applyOperator_mul, applyOperator_mul]
    _ = applyOperator
        (wireLiftOperator (dataPlacement119 n)
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            preparation.circuit))
        (applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (zeroDataSignalFlip119 n))
          (fixedOutsideStateEmbedding (dataPlacement119 n) (fun _ => false)
            (applyOperator
              (star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                preparation.circuit)) (basisKet input))))
        (blockBasis119 output) := by
          rw [hstar, liftedPreparation119_denote]
    _ = ∑ x : QubitBasis n,
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            preparation.circuit output x *
          (applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
              (zeroDataSignalFlip119 n))
            (fixedOutsideStateEmbedding (dataPlacement119 n) (fun _ => false)
              (applyOperator
                (star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                  preparation.circuit)) (basisKet input)))
            (blockBasis119 x)) := by
          rw [wireLiftOperator_apply_blockBasis119]
    _ = ∑ x : QubitBasis n,
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            preparation.circuit output x *
          (applyOperator (zeroProjectorComplement119 n)
            (applyOperator
              (star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                preparation.circuit)) (basisKet input)) x) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [zeroDataSignalFlip119_clean_action]
    _ = applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          preparation.circuit * zeroProjectorComplement119 n *
          star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            preparation.circuit))
        (basisKet input) output := by
          change applyOperator
              (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                preparation.circuit)
            (applyOperator (zeroProjectorComplement119 n)
              (applyOperator
                (star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                  preparation.circuit)) (basisKet input))) output =
            applyOperator
              (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                preparation.circuit * zeroProjectorComplement119 n *
                star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                  preparation.circuit))
              (basisKet input) output
          rw [← applyOperator_mul, ← applyOperator_mul]
    _ = (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          preparation.circuit * zeroProjectorComplement119 n *
          star (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            preparation.circuit)) output input := by
          exact applyOperator_basisKet119 _ _ _

theorem qBPlusBlockCircuit119_clean_block {n : Nat}
    (preparation : NormalizedCircuit n)
    (amplitude : QubitBasis n → ℝ)
    (prepares : ∀ input : QubitBasis n,
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        preparation.circuit) input (zeroBasis119 n) = (amplitude input : ℂ)) :
    signalZeroBlock119
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (qBPlusBlockCircuit119 preparation)) =
      complexQbPlusMatrix119 amplitude := by
  rw [qBPlusBlockCircuit119_clean_block_unconjugated]
  have hconj := conjugated_zeroProjectorComplement119
    (n := n)
    (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) preparation.circuit)
    (preparation119_unitary_right preparation)
  rw [hconj]
  ext output input
  have hcast (value : ℝ) :
      ({ re := value, im := 0 } : ℂ) = (value : ℂ) := by
    apply Complex.ext <;> rfl
  by_cases h : output = input <;>
    simp [complexQbPlusMatrix119, JenningsHistory.qBPlusMatrix, prepares, star, h,
      hcast]

/-! The reversed list is retained as a typed regression.  The public
    qBPlus construction uses `[UNPREP, SELECT, PREP]`; this sibling has the
    opposite denotation and is not identified with the projector block. -/

/-! This is the exact same-raw specialization that is justified by the
    current preparation API: it is a block on the physical preparation
    carrier.  A later logical restriction must additionally prove support
    invariance of that preparation on the encoded data subspace. -/

end
end ExecutableHistoryQbPlusCleanBlock
