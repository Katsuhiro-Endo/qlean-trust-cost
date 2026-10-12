import QLean.History.Integration.HistoryAssemblyExistenceAdapter
import QLean.History.Integration.HistoryAssemblyComponentIntegration
import QLean.History.Integration.HistoryAdmissibility
import QLean.History.Integration.ScientificWidthGenericContract
import QLean.History.Integration.HistoryAssemblyP15P44Adapter
import QLean.SignalProcessing.KernelReflectionRightSVTSpectralTransfer
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2
import QLean.Circuits.Foundation.ConstructionMultiControlledRotationCorrectness

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace ExecutableHistoryCore

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open VerifiedCircuitCore.ControlledCircuitCompilerV2

noncomputable section

abbrev P18Input119 (d c r m R : Nat) :=
  DalzellDilation.CertifiedM13Input d c r m R

def p18System119 {d c r m R : Nat} (I : P18Input119 d c r m R) :
    JenningsHistory.HistorySpec d c r m R :=
  I.base.system

def p18BPlus119 {d c r m R : Nat} (I : P18Input119 d c r m R) :
    GramOperator.ExtendedVector d c R :=
  GramOperator.bPlus (p18System119 I)

theorem p18BPlus119_unitNorm {d c r m R : Nat}
    (I : P18Input119 d c r m R) :
    JenningsHistory.unitNorm (p18BPlus119 I) := by
  exact I.base.hb

theorem p18BPlus119_eq_dalzell {d c r m R : Nat}
    (I : P18Input119 d c r m R) :
    p18BPlus119 I = JenningsHistory.dalzellBPlus I.base.system := by
  rfl

/-! CHAT-020: finite carrier and exact zero-padding, before the circuit layer. -/

def paddedRealState119 (ι : Type) [Fintype ι] (q : Nat)
    (embedding : ι ↪ QubitBasis q) (amplitude : ι → ℝ) :
    State (QubitBasis q) :=
  fun basis =>
    if h : ∃ i, embedding i = basis then
      (amplitude (Classical.choose h) : ℂ)
    else 0

theorem paddedRealState119_on_image (ι : Type) [Fintype ι] (q : Nat)
    (embedding : ι ↪ QubitBasis q) (amplitude : ι → ℝ) (i : ι) :
    paddedRealState119 ι q embedding amplitude (embedding i) =
      (amplitude i : ℂ) := by
  classical
  unfold paddedRealState119
  split
  · next h =>
      have hchoose : Classical.choose h = i := by
        apply embedding.injective
        exact (Classical.choose_spec h).trans (by rfl)
      change (amplitude (Classical.choose h) : ℂ) = (amplitude i : ℂ)
      exact congrArg (fun value => (amplitude value : ℂ)) hchoose
  · next h =>
      exfalso
      exact h ⟨i, rfl⟩

theorem paddedRealState119_off_image (ι : Type) [Fintype ι] (q : Nat)
    (embedding : ι ↪ QubitBasis q) (amplitude : ι → ℝ)
    (basis : QubitBasis q) (notImage : ∀ i, embedding i ≠ basis) :
    paddedRealState119 ι q embedding amplitude basis = 0 := by
  classical
  simp [paddedRealState119, notImage]

theorem paddedRealState119_normSq_sum (ι : Type) [Fintype ι] (q : Nat)
    (embedding : ι ↪ QubitBasis q) (amplitude : ι → ℝ) :
    (∑ basis : QubitBasis q,
      Complex.normSq (paddedRealState119 ι q embedding amplitude basis)) =
      ∑ i : ι, amplitude i ^ 2 := by
  classical
  let image : Finset (QubitBasis q) := Finset.univ.image embedding
  have image_subset : image ⊆ Finset.univ := by
    intro basis hb
    exact Finset.mem_univ basis
  have image_sum :
      image.sum (fun basis =>
          Complex.normSq (paddedRealState119 ι q embedding amplitude basis)) =
        ∑ i : ι, Complex.normSq
          (paddedRealState119 ι q embedding amplitude (embedding i)) := by
    unfold image
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact embedding.injective hij
  have outside_zero :
      ∀ basis ∈ Finset.univ, basis ∉ image →
        Complex.normSq (paddedRealState119 ι q embedding amplitude basis) = 0 := by
    intro basis hb hnot
    have hz : paddedRealState119 ι q embedding amplitude basis = 0 :=
      paddedRealState119_off_image ι q embedding amplitude basis (by
        intro i hEq
        apply hnot
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hEq⟩)
    rw [hz]
    exact Complex.normSq_zero
  have total_image :
      image.sum (fun basis =>
          Complex.normSq (paddedRealState119 ι q embedding amplitude basis)) =
        ∑ basis : QubitBasis q,
          Complex.normSq (paddedRealState119 ι q embedding amplitude basis) := by
    exact Finset.sum_subset image_subset outside_zero
  rw [← total_image, image_sum]
  simp only [paddedRealState119_on_image]
  simp [pow_two]

/-! CHAT-021: the one-qubit base case for real amplitudes.  This is a
concrete base theorem for the later binary split; it does not provide the
general recursive preparation theorem by fiat. -/

def q1Zero119 : QubitBasis 1 := fun _ => false

def q1CosSinState119 (angle : ℝ) : State (QubitBasis 1) :=
  fun basis => if basis 0 then (Real.sin (angle / 2) : ℂ)
    else (Real.cos (angle / 2) : ℂ)

def q1RyCircuit119 (angle : ℝ) : Circuit (PrimitiveGate 1) :=
  .gate (.ry (.const angle) ⟨0, by decide⟩)

theorem q1RyCircuit119_prepares (angle : ℝ) :
    applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (q1RyCircuit119 angle))
      (basisKet (q1Zero119)) = q1CosSinState119 angle := by
  funext output
  classical
  have output_ext : output = (fun _ => output 0) := by
    funext wire
    have : wire = (0 : Fin 1) := Fin.eq_zero wire
    simp [this]
  have remainder_eq_all :
      ∀ (left right : {wire : Fin 1 // wire ≠ (⟨0, by decide⟩ : Fin 1)} → Bool),
        left = right := by
    intro left right
    funext wire
    exact (wire.property (Fin.eq_zero wire.1)).elim
  letI : IsEmpty {wire : Fin 1 // wire ≠ (⟨0, by decide⟩ : Fin 1)} :=
    ⟨fun wire => wire.property (Fin.eq_zero wire.1)⟩
  letI : Subsingleton
      ({wire : Fin 1 // wire ≠ (⟨0, by decide⟩ : Fin 1)} → Bool) :=
    ⟨fun left right => by
      funext wire
      exact isEmptyElim wire⟩
  have remainder_true_false :
      (fun wire : {wire : Fin 1 // wire ≠ (⟨0, by decide⟩ : Fin 1)} => true) =
        (fun _ => false) :=
    Subsingleton.elim _ _
  rw [output_ext]
  cases h : output 0 with
  | false =>
      simp [q1RyCircuit119, q1CosSinState119, q1Zero119, Circuit.denote,
        primitiveGateOperatorWithSymbols, embedSingleQubitOperator, splitWireEquiv,
        Matrix.kronecker, Matrix.reindex, applyOperator, basisKet,
        Matrix.mulVec, dotProduct, localRy, Matrix.one_apply]
  | true =>
      simp [q1RyCircuit119, q1CosSinState119, q1Zero119, Circuit.denote,
        primitiveGateOperatorWithSymbols, embedSingleQubitOperator, splitWireEquiv,
        Matrix.kronecker, Matrix.reindex, applyOperator, basisKet,
        Matrix.mulVec, dotProduct, localRy, Matrix.one_apply]
      intro hneq
      exact (hneq (by
        funext wire
        exact (wire.property (Fin.eq_zero wire.1)).elim)).elim

/-! The scalar part of the binary split is independent of the circuit
construction.  It records the exact relation needed for the leading Ry. -/

def branchAmplitude119 {n : Nat} (highest : Bool)
    (amplitude : QubitBasis (n + 1) → ℝ) : QubitBasis n → ℝ :=
  fun lower => amplitude (combineHighestSelector highest lower)

theorem branchSquareSum_add119 {n : Nat}
    (amplitude : QubitBasis (n + 1) → ℝ) :
    (∑ lower : QubitBasis n,
      branchAmplitude119 false amplitude lower ^ 2) +
      ∑ lower : QubitBasis n,
        branchAmplitude119 true amplitude lower ^ 2 =
      ∑ basis : QubitBasis (n + 1), amplitude basis ^ 2 := by
  have split_sum :
      (∑ basis : QubitBasis (n + 1), amplitude basis ^ 2) =
        ∑ pair : Bool × QubitBasis n,
          amplitude (combineHighestSelector pair.1 pair.2) ^ 2 := by
    apply Fintype.sum_equiv (splitHighestSelectorEquiv n)
    intro basis
    have h : combineHighestSelector (basis (Fin.last n))
        (fun index => basis index.castSucc) = basis := by
      exact (splitHighestSelectorEquiv n).symm_apply_apply basis
    change amplitude basis ^ 2 =
      amplitude (combineHighestSelector (basis (Fin.last n))
        (fun index => basis index.castSucc)) ^ 2
    rw [h]
  rw [split_sum]
  simp [branchAmplitude119, Fintype.sum_prod_type, add_comm]

def branchNorm119 {n : Nat} (highest : Bool)
    (amplitude : QubitBasis (n + 1) → ℝ) : ℝ :=
  Real.sqrt (∑ lower : QubitBasis n,
    branchAmplitude119 highest amplitude lower ^ 2)

theorem branchNorm_sq_add119 {n : Nat}
    (amplitude : QubitBasis (n + 1) → ℝ)
    (normOne : (∑ basis : QubitBasis (n + 1), amplitude basis ^ 2) = 1) :
    branchNorm119 false amplitude ^ 2 + branchNorm119 true amplitude ^ 2 = 1 := by
  have nonneg (highest : Bool) :
      0 ≤ ∑ lower : QubitBasis n,
        branchAmplitude119 highest amplitude lower ^ 2 := by
    exact Finset.sum_nonneg (fun lower _ => sq_nonneg _)
  rw [branchNorm119, branchNorm119, Real.sq_sqrt (nonneg false),
    Real.sq_sqrt (nonneg true), branchSquareSum_add119, normOne]

/-! CHAT-022: the V2 controlled composition has two explicit clean work
wires.  The logical state therefore lives in the clean-work block of an
`n + 3` register: `n` lower wires, one leading control, and two work wires. -/

def lowerPlacement119 (n : Nat) : Fin n ↪ Fin (n + 3) :=
  { toFun := fun wire => ⟨wire.1, by omega⟩
    inj' := by
      intro left right equal
      apply Fin.ext
      exact congrArg (fun value : Fin (n + 3) => value.val) equal }

def topControl119 (n : Nat) : Fin (n + 3) :=
  ⟨n, by omega⟩

def branchControlLayout119 (n : Nat) : ControlLayout n (n + 3) :=
  { placement := lowerPlacement119 n
    control := topControl119 n
    work := fun slot => ⟨n + slot.1 + 1, by omega⟩
    control_ne_placed := by
      intro source equal
      have values : n = source.1 :=
        congrArg (fun value : Fin (n + 3) => value.val) equal
      omega
    work_injective := by
      intro left right equal
      apply Fin.ext
      have values : n + left.1 + 1 = n + right.1 + 1 :=
        congrArg (fun value : Fin (n + 3) => value.val) equal
      omega
    work_ne_control := by
      intro slot equal
      have values : n + slot.1 + 1 = n :=
        congrArg (fun value : Fin (n + 3) => value.val) equal
      omega
    work_ne_placed := by
      intro slot source equal
      have values : n + slot.1 + 1 = source.1 :=
        congrArg (fun value : Fin (n + 3) => value.val) equal
      omega }

def lowerCircuitLift119 {n : Nat}
    (source : NormalizedCircuit n) : NormalizedCircuit (n + 3) :=
  NormalizedCircuit.mapWires (lowerPlacement119 n) source

def relativeCircuit119 {n : Nat}
    (left right : NormalizedCircuit n) : NormalizedCircuit n :=
  NormalizedCircuit.seq (NormalizedCircuit.inverse left) right

def controlledRelativeCircuit119 {n : Nat}
    (left right : NormalizedCircuit n) : Circuit (PrimitiveGate (n + 3)) :=
  (controlCircuit (branchControlLayout119 n)
      (relativeCircuit119 left right)).circuit

def topPlacement119 (n : Nat) : Fin 1 ↪ Fin (n + 3) :=
  { toFun := fun _ => topControl119 n
    inj' := by
      intro left right _
      exact Fin.eq_of_val_eq (by simp) }

def leadingRyCircuit119 (n : Nat) (angle : ℝ) :
    Circuit (PrimitiveGate (n + 3)) :=
  (q1RyCircuit119 angle).mapGates (PrimitiveGate.mapWires (topPlacement119 n))

def branchCompositionCircuit119 {n : Nat} (angle : ℝ)
    (left right : NormalizedCircuit n) : Circuit (PrimitiveGate (n + 3)) :=
  Circuit.sequence [
    leadingRyCircuit119 n angle,
    (lowerCircuitLift119 left).circuit,
    controlledRelativeCircuit119 left right]

theorem applyOperator_wireLift_fixedOutsideState119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (operator : Operator (QubitBasis sourceQubits))
    (state : State (QubitBasis sourceQubits)) :
    applyOperator (wireLiftOperator placement operator)
        (fixedOutsideStateEmbedding placement outside state) =
      fixedOutsideStateEmbedding placement outside
        (applyOperator operator state) := by
  funext output
  unfold applyOperator Matrix.mulVec dotProduct
  by_cases outputOutside :
      restrictToOutsideWires placement output = outside
  · simp only [fixedOutsideStateEmbedding, outputOutside, if_true]
    rw [← (splitWireEmbeddingEquiv placement).symm.sum_comp]
    simp [outputOutside, wireLiftOperator_apply, splitWireEmbeddingEquiv,
      Fintype.sum_prod_type]
  · simp only [fixedOutsideStateEmbedding, outputOutside, if_false]
    apply Finset.sum_eq_zero
    intro input _
    by_cases inputOutside :
        restrictToOutsideWires placement input = outside
    · have different :
          restrictToOutsideWires placement output ≠
            restrictToOutsideWires placement input := by
        intro equal
        apply outputOutside
        exact equal.trans inputOutside
      rw [wireLiftOperator_apply, if_neg different]
      simp [inputOutside]
    · simp [inputOutside, wireLiftOperator_apply]

def externalControlOutside119
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits) :
    OutsideWire layout.placement :=
  ⟨layout.control, fun source equal =>
    layout.control_ne_placed source equal.symm⟩

theorem restrictToOutsideWires_externalControl119
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (input : QubitBasis targetQubits) :
    restrictToOutsideWires layout.placement input
        (externalControlOutside119 layout) = input layout.control := by
  rfl

theorem externallyControlledWireLift_fixedOutsideState119
    {sourceQubits targetQubits : Nat}
    (layout : ExternallyControlledCircuitLayout sourceQubits targetQubits)
    (outside : OutsideWire layout.placement → Bool)
    (controlValue : Bool)
    (outsideControlValue :
      outside (externalControlOutside119 layout) = controlValue)
    (operator : Operator (QubitBasis sourceQubits))
    (state : State (QubitBasis sourceQubits)) :
    applyOperator (externallyControlledWireLiftOperator layout operator)
        (fixedOutsideStateEmbedding layout.placement outside state) =
      if controlValue then
        fixedOutsideStateEmbedding layout.placement outside
          (applyOperator operator state)
    else
        fixedOutsideStateEmbedding layout.placement outside state := by
  cases controlValue with
  | false =>
      have outsideControlFalse :
          outside (externalControlOutside119 layout) = false :=
        outsideControlValue
      have control_of_outside :
          ∀ input : QubitBasis targetQubits,
            restrictToOutsideWires layout.placement input = outside →
              input layout.control = outside (externalControlOutside119 layout) := by
        intro input inputOutside
        have equal := congrFun inputOutside (externalControlOutside119 layout)
        simpa [restrictToOutsideWires_externalControl119] using equal
      funext output
      unfold applyOperator Matrix.mulVec dotProduct
      by_cases outputOutside :
          restrictToOutsideWires layout.placement output = outside
      · simp [fixedOutsideStateEmbedding, outputOutside]
        calc
          (∑ input,
              if restrictToOutsideWires layout.placement input = outside then
                externallyControlledWireLiftOperator layout operator output input *
                  state (restrictToPlacedWires layout.placement input)
              else 0) =
            (if restrictToOutsideWires layout.placement output = outside then
                externallyControlledWireLiftOperator layout operator output output *
                  state (restrictToPlacedWires layout.placement output)
              else 0) := by
            refine Finset.sum_eq_single output (s := Finset.univ) ?_ ?_
            · intro input _ different
              by_cases inputOutside :
                  restrictToOutsideWires layout.placement input = outside
              · have inputControl : input layout.control = false := by
                  exact (control_of_outside input inputOutside).trans
                    outsideControlFalse
                simp [externallyControlledWireLiftOperator, inputOutside,
                  inputControl, different.symm]
              · simp [inputOutside]
            · simp
          _ = state (restrictToPlacedWires layout.placement output) := by
            have outputControl : output layout.control = false := by
              exact (control_of_outside output outputOutside).trans
                outsideControlFalse
            simp [externallyControlledWireLiftOperator, outputOutside,
              outputControl]
      · simp [fixedOutsideStateEmbedding, outputOutside]
        apply Finset.sum_eq_zero
        intro input _
        by_cases inputOutside :
            restrictToOutsideWires layout.placement input = outside
        · have different : input ≠ output := by
            intro equal
            apply outputOutside
            subst input
            exact inputOutside
          have inputControl : input layout.control = false := by
            exact (control_of_outside input inputOutside).trans
              outsideControlFalse
          simp [externallyControlledWireLiftOperator, inputOutside,
            inputControl, different.symm]
        · simp [inputOutside]
  | true =>
      have outsideControlTrue :
          outside (externalControlOutside119 layout) = true :=
        outsideControlValue
      have control_of_outside :
          ∀ input : QubitBasis targetQubits,
            restrictToOutsideWires layout.placement input = outside →
              input layout.control = outside (externalControlOutside119 layout) := by
        intro input inputOutside
        have equal := congrFun inputOutside (externalControlOutside119 layout)
        simpa [restrictToOutsideWires_externalControl119] using equal
      have external_on_embedding :
          applyOperator (externallyControlledWireLiftOperator layout operator)
              (fixedOutsideStateEmbedding layout.placement outside state) =
            applyOperator (wireLiftOperator layout.placement operator)
              (fixedOutsideStateEmbedding layout.placement outside state) := by
        funext output
        unfold applyOperator Matrix.mulVec dotProduct
        apply Finset.sum_congr rfl
        intro input _
        by_cases inputOutside :
            restrictToOutsideWires layout.placement input = outside
        · have inputControl : input layout.control = true := by
            exact (control_of_outside input inputOutside).trans
              outsideControlTrue
          simp [externallyControlledWireLiftOperator, inputControl]
        · simp [externallyControlledWireLiftOperator, fixedOutsideStateEmbedding,
            inputOutside]
      calc
        applyOperator (externallyControlledWireLiftOperator layout operator)
            (fixedOutsideStateEmbedding layout.placement outside state) =
          applyOperator (wireLiftOperator layout.placement operator)
            (fixedOutsideStateEmbedding layout.placement outside state) :=
          external_on_embedding
        _ = fixedOutsideStateEmbedding layout.placement outside
            (applyOperator operator state) :=
          applyOperator_wireLift_fixedOutsideState119 layout.placement outside
            operator state

def externalLayout119
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) :
    ExternallyControlledCircuitLayout sourceQubits targetQubits :=
  { placement := layout.placement
    control := layout.control
    controlWork := [layout.work 0, layout.work 1]
    control_ne_placed := layout.control_ne_placed }

def externalPlan119 {qubits : Nat}
    (source : NormalizedPrimitiveGate qubits) :
    ExternallyControlledPrimitivePlan qubits :=
  match source.1 with
  | .x target => .x target
  | .h target => .h target
  | .ry angle target => .ry angle target
  | .phaseShift angle target => .phaseShift angle target
  | .cnot control target different => .cnot control target different
  | .toffoli control₀ control₁ target controlsDifferent firstDifferent secondDifferent =>
      .toffoli control₀ control₁ target controlsDifferent firstDifferent secondDifferent

def externalPrimitiveOperator119
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    Operator (QubitBasis targetQubits) :=
  ExternallyControlledPrimitivePlan.semanticOperator symbolValue
    (externalLayout119 layout) (externalPlan119 source)

theorem externalPrimitiveOperator119_eq_wireLift
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    externalPrimitiveOperator119 symbolValue layout source =
      externallyControlledWireLiftOperator (externalLayout119 layout)
        (ExternallyControlledPrimitivePlan.sourceOperator symbolValue
          (externalPlan119 source)) := by
  exact ExternallyControlledPrimitivePlan.semanticOperator_eq_controlledWireLift
    symbolValue (externalLayout119 layout) (externalPlan119 source)

theorem controlPrimitiveTarget_eq_strictOperator119
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits) :
    controlPrimitiveTarget symbolValue layout source =
      (externalPlan119 source).strictOperator symbolValue (externalLayout119 layout) := by
  rcases source with ⟨source, normalized⟩
  cases source <;> rfl

def externalValid119
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits) :
    (externalLayout119 layout).CleanWorkValid :=
  { work₀ := layout.work 0
    work₁ := layout.work 1
    controlWork_eq := rfl
    work₀_ne_control := layout.work_ne_control 0
    work₁_ne_control := layout.work_ne_control 1
    work₀_ne_work₁ := by
      intro equal
      have values : (0 : Fin 2) = 1 := layout.work_injective equal
      omega
    work₀_ne_placed := by
      intro source
      exact layout.work_ne_placed 0 source
    work₁_ne_placed := by
      intro source
      exact layout.work_ne_placed 1 source }

def branchOutside119
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (controlValue : Bool) :
    OutsideWire (externalLayout119 layout).placement → Bool :=
  fun wire => if wire.1 = layout.control then controlValue else false

theorem branchOutside119_control
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (controlValue : Bool) :
      branchOutside119 layout controlValue
      (externalControlOutside119 (externalLayout119 layout)) = controlValue := by
  simp [branchOutside119, externalControlOutside119, externalLayout119]

theorem branchOutside119_work
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (controlValue : Bool) (slot : Fin 2) :
      branchOutside119 layout controlValue
      ⟨layout.work slot, fun source equal =>
        layout.work_ne_placed slot source equal.symm⟩ = false := by
  have different : layout.work slot ≠ layout.control := layout.work_ne_control slot
  simp [branchOutside119, different]

theorem fixedOutsideStateEmbedding_mem_basisSpan119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (predicate : QubitBasis targetQubits → Prop)
    (predicate_of_outside : ∀ basis,
      restrictToOutsideWires placement basis = outside → predicate basis)
    (state : State (QubitBasis sourceQubits)) :
    fixedOutsideStateEmbedding placement outside state ∈
      SubspaceMapComponent.basisSpan predicate := by
  have expansion :
      fixedOutsideStateEmbedding placement outside state =
        ∑ input : QubitBasis sourceQubits,
          state input • basisKet
            (mergePlacedAndOutsideBasis placement input outside) := by
    funext output
    by_cases outputOutside :
        restrictToOutsideWires placement output = outside
    · rw [fixedOutsideStateEmbedding, if_pos outputOutside]
      let chosen := restrictToPlacedWires placement output
      have outputEq :
          mergePlacedAndOutsideBasis placement chosen outside = output := by
        simpa [chosen, outputOutside] using
          (mergePlacedAndOutsideBasis_restrict placement output)
      rw [Finset.sum_apply]
      symm
      calc
        (∑ input : QubitBasis sourceQubits,
          (state input • basisKet
            (mergePlacedAndOutsideBasis placement input outside)) output) =
            (state chosen • basisKet
              (mergePlacedAndOutsideBasis placement chosen outside)) output := by
          refine @Finset.sum_eq_single (QubitBasis sourceQubits) ℂ inferInstance
            (Finset.univ : Finset (QubitBasis sourceQubits))
            (fun input => (state input • basisKet
              (mergePlacedAndOutsideBasis placement input outside)) output) chosen ?_ ?_
          · intro input _ different
            have output_ne :
                output ≠ mergePlacedAndOutsideBasis placement input outside := by
              intro equal
              apply different
              have placed := congrArg (restrictToPlacedWires placement) equal
              simpa [chosen] using placed.symm
            simp [basisKet, output_ne]
          · simp [basisKet, outputEq, chosen]
        _ = state (restrictToPlacedWires placement output) := by
          simp [basisKet, outputEq, chosen]
    · rw [fixedOutsideStateEmbedding, if_neg outputOutside]
      rw [Finset.sum_apply]
      symm
      apply Finset.sum_eq_zero
      intro input _
      have output_ne :
          output ≠ mergePlacedAndOutsideBasis placement input outside := by
        intro equal
        apply outputOutside
        rw [equal]
        exact restrictToOutsideWires_mergePlacedAndOutsideBasis placement input outside
      simp [basisKet, output_ne]
  rw [expansion]
  apply Submodule.sum_mem
  intro input _
  apply (SubspaceMapComponent.basisSpan predicate).smul_mem _
  apply SubspaceMapComponent.basisKet_mem_basisSpan
  apply predicate_of_outside
  exact restrictToOutsideWires_mergePlacedAndOutsideBasis placement input outside

theorem branchEmbedding119_mem_cleanSpan
    {sourceQubits targetQubits : Nat}
    (layout : ControlLayout sourceQubits targetQubits)
    (controlValue : Bool)
    (state : State (QubitBasis sourceQubits)) :
    fixedOutsideStateEmbedding (externalLayout119 layout).placement
        (branchOutside119 layout controlValue) state ∈
      SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate (externalValid119 layout)) := by
  apply fixedOutsideStateEmbedding_mem_basisSpan119
    (externalLayout119 layout).placement
    (branchOutside119 layout controlValue)
    (externallyControlledCleanWorkPredicate (externalValid119 layout))
  intro basis outsideEq
  constructor
  · have equal := congrFun outsideEq
      ⟨(externalValid119 layout).work₀,
        fun source equal => (externalValid119 layout).work₀_ne_placed source equal.symm⟩
    change basis ((externalValid119 layout).work₀) = false
    change basis ((externalValid119 layout).work₀) =
      branchOutside119 layout controlValue
        ⟨(externalValid119 layout).work₀,
          fun source equal => (externalValid119 layout).work₀_ne_placed source equal.symm⟩ at equal
    rw [equal]
    simp [branchOutside119, externalValid119, externalLayout119,
      layout.work_ne_control 0]
  · have equal := congrFun outsideEq
      ⟨(externalValid119 layout).work₁,
        fun source equal => (externalValid119 layout).work₁_ne_placed source equal.symm⟩
    change basis ((externalValid119 layout).work₁) = false
    change basis ((externalValid119 layout).work₁) =
      branchOutside119 layout controlValue
        ⟨(externalValid119 layout).work₁,
          fun source equal => (externalValid119 layout).work₁_ne_placed source equal.symm⟩ at equal
    rw [equal]
    simp [branchOutside119, externalValid119, externalLayout119,
      layout.work_ne_control 1]

theorem controlPrimitiveTarget_fixedOutsideState119
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedPrimitiveGate sourceQubits)
    (controlValue : Bool)
    (state : State (QubitBasis sourceQubits)) :
    applyOperator (controlPrimitiveTarget symbolValue layout source)
        (fixedOutsideStateEmbedding (externalLayout119 layout).placement
          (branchOutside119 layout controlValue) state) =
      if controlValue then
        fixedOutsideStateEmbedding (externalLayout119 layout).placement
          (branchOutside119 layout controlValue)
          (applyOperator
            (ExternallyControlledPrimitivePlan.sourceOperator symbolValue
              (externalPlan119 source)) state)
      else
        fixedOutsideStateEmbedding (externalLayout119 layout).placement
          (branchOutside119 layout controlValue) state := by
  rw [controlPrimitiveTarget_eq_strictOperator119]
  rw [(externalPlan119 source).strictOperator_apply_eq_semanticOperator_of_mem
    symbolValue (externalLayout119 layout) (externalValid119 layout)
    (fixedOutsideStateEmbedding (externalLayout119 layout).placement
      (branchOutside119 layout controlValue) state)]
  change applyOperator (externalPrimitiveOperator119 symbolValue layout source)
      (fixedOutsideStateEmbedding (externalLayout119 layout).placement
        (branchOutside119 layout controlValue) state) = _
  rw [externalPrimitiveOperator119_eq_wireLift symbolValue layout source]
  · simpa [externalPrimitiveOperator119] using
      (externallyControlledWireLift_fixedOutsideState119
        (externalLayout119 layout)
        (branchOutside119 layout controlValue)
        controlValue
        (branchOutside119_control layout controlValue)
        (ExternallyControlledPrimitivePlan.sourceOperator symbolValue
          (externalPlan119 source)) state)
  · exact branchEmbedding119_mem_cleanSpan layout controlValue state

theorem controlCircuit_fixedOutsideState119
    {sourceQubits targetQubits : Nat}
    (symbolValue : String → ℝ)
    (layout : ControlLayout sourceQubits targetQubits)
    (source : NormalizedCircuit sourceQubits)
    (controlValue : Bool)
    (state : State (QubitBasis sourceQubits)) :
    applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlCircuit layout source).circuit)
      (fixedOutsideStateEmbedding (externalLayout119 layout).placement
        (branchOutside119 layout controlValue) state) =
      if controlValue then
        fixedOutsideStateEmbedding (externalLayout119 layout).placement
          (branchOutside119 layout controlValue)
          (applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
            source.circuit) state)
      else
        fixedOutsideStateEmbedding (externalLayout119 layout).placement
          (branchOutside119 layout controlValue) state := by
  rcases source with ⟨circuit, normalized⟩
  induction circuit generalizing state with
  | identity =>
      change applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (.identity : Circuit (PrimitiveGate targetQubits)))
          (fixedOutsideStateEmbedding (externalLayout119 layout).placement
            (branchOutside119 layout controlValue) state) = _
      simp [Circuit.denote, applyOperator]
  | gate sourceGate =>
      have sourceNormalized : VerifiedCircuitCore.IsNormalizedPrimitive sourceGate :=
        normalized sourceGate (by simp [Circuit.flatten])
      change applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
            (controlPrimitive layout ⟨sourceGate, sourceNormalized⟩).circuit)
          (fixedOutsideStateEmbedding (externalLayout119 layout).placement
            (branchOutside119 layout controlValue) state) = _
      rw [controlPrimitive_normalized_correct]
      have sourceOperatorEq :
          ExternallyControlledPrimitivePlan.sourceOperator symbolValue
              (externalPlan119 ⟨sourceGate, sourceNormalized⟩) =
            Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
              (.gate sourceGate) := by
        cases sourceGate <;> rfl
      rw [← sourceOperatorEq]
      exact controlPrimitiveTarget_fixedOutsideState119 symbolValue layout
        ⟨sourceGate, sourceNormalized⟩ controlValue state
  | seq first second firstInduction secondInduction =>
      have firstNormalized : IsNormalizedCircuit first := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      have secondNormalized : IsNormalizedCircuit second := by
        intro gate member
        exact normalized gate (by simp [Circuit.flatten, member])
      change applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
            (.seq
              (controlCircuit layout ⟨first, firstNormalized⟩).circuit
              (controlCircuit layout ⟨second, secondNormalized⟩).circuit))
          (fixedOutsideStateEmbedding (externalLayout119 layout).placement
            (branchOutside119 layout controlValue) state) = _
      rw [Circuit.denote_seq, applyOperator_mul]
      rw [firstInduction state firstNormalized]
      cases controlValue with
      | false =>
          simpa [applyOperator_mul] using
            (secondInduction state secondNormalized)
      | true =>
          simpa [applyOperator_mul] using
            (secondInduction (applyOperator (Circuit.denote
                (primitiveGateOperatorWithSymbols symbolValue) first) state)
              secondNormalized)
  | «repeat» count body inductionHypothesis =>
      cases count with
      | zero =>
          change applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
              (.identity : Circuit (PrimitiveGate targetQubits)))
              (fixedOutsideStateEmbedding (externalLayout119 layout).placement
                (branchOutside119 layout controlValue) state) = _
          simp [Circuit.denote, applyOperator]
      | succ count =>
          have bodyNormalized : IsNormalizedCircuit body := by
            intro gate member
            exact normalized gate (by
              simp [Circuit.flatten, List.replicate_succ, member])
          change applyOperator
              (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
                (.repeat (Nat.succ count)
                  (controlCircuit layout ⟨body, bodyNormalized⟩).circuit))
              (fixedOutsideStateEmbedding (externalLayout119 layout).placement
                (branchOutside119 layout controlValue) state) = _
          rw [Circuit.denote_repeat]
          have powerInduction : ∀ k : Nat, ∀ s : State (QubitBasis sourceQubits),
              applyOperator
                  ((Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
                    (controlCircuit layout ⟨body, bodyNormalized⟩).circuit) ^ k)
                  (fixedOutsideStateEmbedding (externalLayout119 layout).placement
                    (branchOutside119 layout controlValue) s) =
                if controlValue then
                  fixedOutsideStateEmbedding (externalLayout119 layout).placement
                    (branchOutside119 layout controlValue)
                    (applyOperator
                      ((Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) body) ^ k) s)
                else
                  fixedOutsideStateEmbedding (externalLayout119 layout).placement
                    (branchOutside119 layout controlValue) s := by
            intro k
            induction k with
            | zero =>
                intro s
                simp [applyOperator]
            | succ k inductionStep =>
                intro s
                rw [pow_succ, applyOperator_mul]
                rw [inductionHypothesis s bodyNormalized]
                cases controlValue with
                | false =>
                    simpa using inductionStep s
                | true =>
                    simpa [pow_succ, applyOperator_mul] using inductionStep
                      (applyOperator (Circuit.denote
                        (primitiveGateOperatorWithSymbols symbolValue) body) s)
          exact powerInduction (Nat.succ count) state

def zeroBasis119 (n : Nat) : QubitBasis n := fun _ => false

def allZeroTop119 (n : Nat) (controlValue : Bool) : QubitBasis (n + 3) :=
  fun wire => if wire = topControl119 n then controlValue else false

def topOutsideZero119 (n : Nat) : OutsideWire (topPlacement119 n) → Bool :=
  fun _ => false

theorem topEmbedding_basis119_pre (n : Nat) (controlValue : Bool) :
    fixedOutsideStateEmbedding (topPlacement119 n) (topOutsideZero119 n)
        (basisKet (fun _ : Fin 1 => controlValue)) =
      basisKet (allZeroTop119 n controlValue) := by
  rw [fixedOutsideStateEmbedding_basisKet]
  congr 1
  apply (fullBasis_eq_iff_restrictions_eq (topPlacement119 n) _ _).2
  constructor
  · change restrictToPlacedWires (topPlacement119 n)
        (mergePlacedAndOutsideBasis (topPlacement119 n)
          (fun _ : Fin 1 => controlValue) (topOutsideZero119 n)) = _
    rw [restrictToPlacedWires_mergePlacedAndOutsideBasis]
    funext wire
    change controlValue = allZeroTop119 n controlValue (topPlacement119 n wire)
    simp [allZeroTop119, topControl119, topPlacement119]
  · change restrictToOutsideWires (topPlacement119 n)
        (mergePlacedAndOutsideBasis (topPlacement119 n)
          (fun _ : Fin 1 => controlValue) (topOutsideZero119 n)) = _
    rw [restrictToOutsideWires_mergePlacedAndOutsideBasis]
    funext wire
    change false = if wire.1 = topControl119 n then controlValue else false
    have different : wire.1 ≠ topControl119 n := by
      intro equal
      exact wire.property 0 (by simpa [topPlacement119] using equal.symm)
    simp [different]

theorem lowerEmbedding_basis119_pre (n : Nat) (controlValue : Bool) :
    fixedOutsideStateEmbedding (lowerPlacement119 n)
        (fun wire => if wire.1 = topControl119 n then controlValue else false)
        (basisKet (zeroBasis119 n)) =
      basisKet (allZeroTop119 n controlValue) := by
  rw [fixedOutsideStateEmbedding_basisKet]
  congr 1
  apply (fullBasis_eq_iff_restrictions_eq (lowerPlacement119 n) _ _).2
  constructor
  · change restrictToPlacedWires (lowerPlacement119 n)
        (mergePlacedAndOutsideBasis (lowerPlacement119 n)
          (zeroBasis119 n)
          (fun wire => if wire.1 = topControl119 n then controlValue else false)) = _
    rw [restrictToPlacedWires_mergePlacedAndOutsideBasis]
    funext wire
    change false = if lowerPlacement119 n wire = topControl119 n then
      controlValue else false
    have different : lowerPlacement119 n wire ≠ topControl119 n := by
      intro equal
      have values : wire.1 = n :=
        congrArg (fun value : Fin (n + 3) => value.1) equal
      omega
    simp [different]
  · change restrictToOutsideWires (lowerPlacement119 n)
        (mergePlacedAndOutsideBasis (lowerPlacement119 n)
          (zeroBasis119 n)
          (fun wire => if wire.1 = topControl119 n then controlValue else false)) = _
    rw [restrictToOutsideWires_mergePlacedAndOutsideBasis]
    funext wire
    change (if wire.1 = topControl119 n then controlValue else false) =
      allZeroTop119 n controlValue wire.1
    rfl

theorem lowerCircuitLift119_denote
    {n : Nat} (symbolValue : String → ℝ)
    (source : NormalizedCircuit n) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (lowerCircuitLift119 source).circuit =
      wireLiftOperator (lowerPlacement119 n)
        (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) source.circuit) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (source.circuit.mapGates (PrimitiveGate.mapWires (lowerPlacement119 n))) = _
  exact denote_mapPrimitiveWires_eq_wireLiftOperator symbolValue
    (lowerPlacement119 n) source.circuit

theorem leadingRyCircuit119_denote
    (n : Nat) (angle : ℝ) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (leadingRyCircuit119 n angle) =
      wireLiftOperator (topPlacement119 n)
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (q1RyCircuit119 angle)) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
      ((q1RyCircuit119 angle).mapGates
        (PrimitiveGate.mapWires (topPlacement119 n))) = _
  exact denote_mapPrimitiveWires_eq_wireLiftOperator (fun _ => 0)
    (topPlacement119 n) (q1RyCircuit119 angle)

def q1One119 : QubitBasis 1 := fun _ => true

theorem q1CosSinState119_decompose (angle : ℝ) :
    q1CosSinState119 angle =
      (Real.cos (angle / 2) : ℂ) • basisKet (q1Zero119) +
        (Real.sin (angle / 2) : ℂ) • basisKet (q1One119) := by
  funext output
  cases h : output 0 with
  | false =>
      have outputEq : output = q1Zero119 := by
        funext wire
        have wireZero : wire = (0 : Fin 1) := Fin.eq_zero wire
        rw [wireZero, q1Zero119]
        exact h
      have zeroNeOne : q1Zero119 ≠ q1One119 := by
        intro equal
        have value := congrFun equal (0 : Fin 1)
        cases value
      have zeroAtZero : q1Zero119 (0 : Fin 1) = false := rfl
      rw [outputEq]
      simp [q1CosSinState119, basisKet, zeroNeOne, zeroAtZero]
  | true =>
      have outputEq : output = q1One119 := by
        funext wire
        have wireZero : wire = (0 : Fin 1) := Fin.eq_zero wire
        rw [wireZero, q1One119]
        exact h
      have zeroNeOne : q1Zero119 ≠ q1One119 := by
        intro equal
        have value := congrFun equal (0 : Fin 1)
        cases value
      have oneAtZero : q1One119 (0 : Fin 1) = true := rfl
      have oneNeZero : q1One119 ≠ q1Zero119 := Ne.symm zeroNeOne
      rw [outputEq]
      simp [q1CosSinState119, basisKet, oneAtZero, oneNeZero]

theorem fixedOutsideStateEmbedding_smul119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (scalar : ℂ) (state : State (QubitBasis sourceQubits)) :
    fixedOutsideStateEmbedding placement outside (scalar • state) =
      scalar • fixedOutsideStateEmbedding placement outside state := by
  funext basis
  simp [fixedOutsideStateEmbedding]

theorem fixedOutsideStateEmbedding_add119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool)
    (left right : State (QubitBasis sourceQubits)) :
    fixedOutsideStateEmbedding placement outside (left + right) =
      fixedOutsideStateEmbedding placement outside left +
        fixedOutsideStateEmbedding placement outside right := by
  funext basis
  by_cases outsideEqual : restrictToOutsideWires placement basis = outside
  · simp [fixedOutsideStateEmbedding, outsideEqual, Pi.add_apply]
  · simp [fixedOutsideStateEmbedding, outsideEqual, Pi.add_apply]

theorem leadingRy_on_zero_top119 (n : Nat) (angle : ℝ) :
    applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (leadingRyCircuit119 n angle))
      (basisKet (allZeroTop119 n false)) =
      (Real.cos (angle / 2) : ℂ) • basisKet (allZeroTop119 n false) +
        (Real.sin (angle / 2) : ℂ) • basisKet (allZeroTop119 n true) := by
  rw [leadingRyCircuit119_denote]
  rw [← topEmbedding_basis119_pre n false]
  rw [applyOperator_wireLift_fixedOutsideState119]
  have q1prepared :
      applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
            (q1RyCircuit119 angle))
          (basisKet (fun _ : Fin 1 => false)) =
        q1CosSinState119 angle := by
    have zeroEq : (fun _ : Fin 1 => false) = q1Zero119 := rfl
    rw [zeroEq]
    exact q1RyCircuit119_prepares angle
  rw [q1prepared]
  rw [q1CosSinState119_decompose, fixedOutsideStateEmbedding_add119,
    fixedOutsideStateEmbedding_smul119, fixedOutsideStateEmbedding_smul119]
  have zeroEq : q1Zero119 = (fun _ : Fin 1 => false) := rfl
  have oneEq : q1One119 = (fun _ : Fin 1 => true) := rfl
  rw [zeroEq, oneEq]
  rw [topEmbedding_basis119_pre, topEmbedding_basis119_pre]

theorem leadingRy_on_zero_branches119 (n : Nat) (angle : ℝ) :
    applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (leadingRyCircuit119 n angle))
      (basisKet (allZeroTop119 n false)) =
      (Real.cos (angle / 2) : ℂ) •
          fixedOutsideStateEmbedding (lowerPlacement119 n)
            (fun wire => if wire.1 = topControl119 n then false else false)
            (basisKet (zeroBasis119 n)) +
        (Real.sin (angle / 2) : ℂ) •
          fixedOutsideStateEmbedding (lowerPlacement119 n)
            (fun wire => if wire.1 = topControl119 n then true else false)
            (basisKet (zeroBasis119 n)) := by
  rw [leadingRy_on_zero_top119]
  rw [lowerEmbedding_basis119_pre n false, lowerEmbedding_basis119_pre n true]

theorem topEmbedding_basis119 (n : Nat) (controlValue : Bool) :
    fixedOutsideStateEmbedding (topPlacement119 n) (topOutsideZero119 n)
        (basisKet (fun _ : Fin 1 => controlValue)) =
      basisKet (allZeroTop119 n controlValue) := by
  rw [fixedOutsideStateEmbedding_basisKet]
  congr 1
  apply (fullBasis_eq_iff_restrictions_eq (topPlacement119 n) _ _).2
  constructor
  · change restrictToPlacedWires (topPlacement119 n)
        (mergePlacedAndOutsideBasis (topPlacement119 n)
          (fun _ : Fin 1 => controlValue) (topOutsideZero119 n)) = _
    rw [restrictToPlacedWires_mergePlacedAndOutsideBasis]
    funext wire
    change controlValue = allZeroTop119 n controlValue (topPlacement119 n wire)
    simp [allZeroTop119, topControl119, topPlacement119]
  · change restrictToOutsideWires (topPlacement119 n)
        (mergePlacedAndOutsideBasis (topPlacement119 n)
          (fun _ : Fin 1 => controlValue) (topOutsideZero119 n)) = _
    rw [restrictToOutsideWires_mergePlacedAndOutsideBasis]
    funext wire
    change false = if wire.1 = topControl119 n then controlValue else false
    have different : wire.1 ≠ topControl119 n := by
      intro equal
      exact wire.property 0 (by simpa [topPlacement119] using equal.symm)
    simp [different]

theorem relativeCircuit119_denote
    {n : Nat} (symbolValue : String → ℝ)
    (left right : NormalizedCircuit n) :
    Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (relativeCircuit119 left right).circuit =
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) right.circuit *
        star (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) left.circuit) := by
  change Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
      (Circuit.seq (Circuit.reverse PrimitiveGate.inverse left.circuit)
        right.circuit) = _
  rw [Circuit.denote_seq, primitiveCircuit_denote_reverse]

theorem relativeCircuit119_cancel_left
    {n : Nat} (symbolValue : String → ℝ)
    (left right : NormalizedCircuit n)
    (state : State (QubitBasis n)) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (relativeCircuit119 left right).circuit)
        (applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) left.circuit) state) =
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) right.circuit) state := by
  rw [relativeCircuit119_denote, applyOperator_mul]
  have hleftMem :
      Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) left.circuit ∈
        Matrix.unitaryGroup (QubitBasis n) ℂ :=
    primitiveCircuit_denote_mem_unitaryGroup symbolValue left.circuit
  have hleft :
      star (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) left.circuit) *
          Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) left.circuit = 1 :=
    (Matrix.mem_unitaryGroup_iff').1 hleftMem
  have hcancel :
      applyOperator (star (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        left.circuit))
        (applyOperator (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          left.circuit) state) = state := by
    rw [← applyOperator_mul]
    change Matrix.mulVec
      (star (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        left.circuit) *
          Circuit.denote (primitiveGateOperatorWithSymbols symbolValue) left.circuit)
        state = state
    rw [hleft]
    simp
  rw [hcancel]

theorem controlledRelativeCircuit119_fixedOutsideState
    {n : Nat} (symbolValue : String → ℝ)
    (left right : NormalizedCircuit n)
    (controlValue : Bool) (state : State (QubitBasis n)) :
    applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
        (controlledRelativeCircuit119 left right))
      (fixedOutsideStateEmbedding
        (externalLayout119 (branchControlLayout119 n)).placement
        (branchOutside119 (branchControlLayout119 n) controlValue) state) =
      if controlValue then
        fixedOutsideStateEmbedding
          (externalLayout119 (branchControlLayout119 n)).placement
          (branchOutside119 (branchControlLayout119 n) controlValue)
          (applyOperator
            (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
              (relativeCircuit119 left right).circuit) state)
      else
        fixedOutsideStateEmbedding
          (externalLayout119 (branchControlLayout119 n)).placement
          (branchOutside119 (branchControlLayout119 n) controlValue) state := by
  simpa [controlledRelativeCircuit119] using
    (controlCircuit_fixedOutsideState119 symbolValue
      (branchControlLayout119 n) (relativeCircuit119 left right)
      controlValue state)

theorem branchCompositionCircuit119_denote
    {n : Nat} (angle : ℝ) (left right : NormalizedCircuit n) :
    Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (branchCompositionCircuit119 angle left right) =
      Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (controlledRelativeCircuit119 left right) *
        wireLiftOperator (lowerPlacement119 n)
          (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) left.circuit) *
        Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (leadingRyCircuit119 n angle) := by
  unfold branchCompositionCircuit119
  rw [Circuit.denote_sequence_eq_operatorSequence]
  simp [operatorSequence, lowerCircuitLift119_denote]

theorem branchCompositionCircuit119_prepares
    {n : Nat} (angle : ℝ)
    (left right : NormalizedCircuit n)
    (u w : State (QubitBasis n))
    (leftPrepares :
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) left.circuit)
        (basisKet (zeroBasis119 n)) = u)
    (rightPrepares :
      applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) right.circuit)
        (basisKet (zeroBasis119 n)) = w) :
    applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (branchCompositionCircuit119 angle left right))
      (basisKet (allZeroTop119 n false)) =
      (Real.cos (angle / 2) : ℂ) •
          fixedOutsideStateEmbedding (lowerPlacement119 n)
            (fun wire => if wire.1 = topControl119 n then false else false) u +
        (Real.sin (angle / 2) : ℂ) •
          fixedOutsideStateEmbedding (lowerPlacement119 n)
            (fun wire => if wire.1 = topControl119 n then true else false) w := by
  rw [branchCompositionCircuit119_denote]
  rw [applyOperator_mul, applyOperator_mul]
  rw [leadingRy_on_zero_branches119]
  rw [applyOperator_add, applyOperator_smul, applyOperator_smul]
  rw [applyOperator_wireLift_fixedOutsideState119,
    applyOperator_wireLift_fixedOutsideState119]
  rw [applyOperator_add, applyOperator_smul, applyOperator_smul]
  have branchPlacementEq :
      lowerPlacement119 n =
        (externalLayout119 (branchControlLayout119 n)).placement := by
    rfl
  rw [branchPlacementEq]
  have outsideFalse :
      (fun wire : OutsideWire
          (externalLayout119 (branchControlLayout119 n)).placement =>
        if wire.1 = topControl119 n then false else false) =
        branchOutside119 (branchControlLayout119 n) false := by
    rfl
  have outsideTrue :
      (fun wire : OutsideWire
          (externalLayout119 (branchControlLayout119 n)).placement =>
        if wire.1 = topControl119 n then true else false) =
        branchOutside119 (branchControlLayout119 n) true := by
    rfl
  rw [outsideFalse, outsideTrue]
  rw [controlledRelativeCircuit119_fixedOutsideState,
    controlledRelativeCircuit119_fixedOutsideState]
  simp
  rw [relativeCircuit119_cancel_left]
  rw [leftPrepares, rightPrepares]

theorem explicitBranchEmbedding119_mem_cleanSpan
    {n : Nat} (controlValue : Bool) (state : State (QubitBasis n)) :
    fixedOutsideStateEmbedding (lowerPlacement119 n)
        (fun wire => if wire.1 = topControl119 n then controlValue else false)
        state ∈
      SubspaceMapComponent.basisSpan
        (externallyControlledCleanWorkPredicate
          (externalValid119 (branchControlLayout119 n))) := by
  have h := branchEmbedding119_mem_cleanSpan
    (branchControlLayout119 n) controlValue state
  convert h using 1
  funext wire
  rfl

def prepWidth023 : Nat → Nat
  | 0 => 0
  | n + 1 => prepWidth023 n + 3

def prepWorkCount023 (n : Nat) : Nat := 2 * n

theorem prepWidth023_eq_data_plus_work (n : Nat) :
    prepWidth023 n = n + prepWorkCount023 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [prepWidth023, prepWorkCount023, ih]
      omega

theorem prepWidth023_ge (n : Nat) : n ≤ prepWidth023 n := by
  rw [prepWidth023_eq_data_plus_work]
  exact Nat.le_add_right n _

def dataPlacement023 : (n : Nat) → Fin n ↪ Fin (prepWidth023 n)
  | 0 =>
      { toFun := fun i => Fin.elim0 i
        inj' := by
          intro i j
          exact Fin.elim0 i }
  | n + 1 =>
      { toFun := fun i =>
          if h : i.val < n then
            ⟨(dataPlacement023 n ⟨i.val, h⟩).val, by
              have hlt := (dataPlacement023 n ⟨i.val, h⟩).isLt
              rw [prepWidth023]
              omega⟩
          else
            ⟨prepWidth023 n, by
              rw [prepWidth023]
              omega⟩
        inj' := by
          intro i j hij
          by_cases hi : i.val < n
          · by_cases hj : j.val < n
            · have hlow :
                  dataPlacement023 n ⟨i.val, hi⟩ =
                    dataPlacement023 n ⟨j.val, hj⟩ := by
                  apply Fin.ext
                  have hraw :=
                    congrArg
                      (fun z : Fin (prepWidth023 (n + 1)) => z.val) hij
                  simpa [hi, hj] using hraw
              have hfin : (⟨i.val, hi⟩ : Fin n) = ⟨j.val, hj⟩ :=
                (dataPlacement023 n).injective hlow
              have hval : i.val = j.val :=
                congrArg (fun z : Fin n => z.val) hfin
              exact Fin.ext hval
            · have hval := congrArg (fun z : Fin (prepWidth023 (n + 1)) => z.val) hij
              simp [hi, hj] at hval
              have hlow := (dataPlacement023 n ⟨i.val, hi⟩).isLt
              have hwidth : n ≤ prepWidth023 n := prepWidth023_ge n
              omega
          · by_cases hj : j.val < n
            · have hval := congrArg (fun z : Fin (prepWidth023 (n + 1)) => z.val) hij
              simp [hi, hj] at hval
              have hlow := (dataPlacement023 n ⟨j.val, hj⟩).isLt
              have hwidth : n ≤ prepWidth023 n := prepWidth023_ge n
              omega
            · have hi' : i.val = n := by omega
              have hj' : j.val = n := by omega
              exact Fin.ext (by omega) }

def dataOutsideZero023 {n : Nat} :
    OutsideWire (dataPlacement023 n) → Bool := fun _ => false

def realEnergy023 {n : Nat} (amplitude : QubitBasis n → ℝ) : ℝ :=
  ∑ basis : QubitBasis n, amplitude basis ^ 2

def zeroAmplitude023 (n : Nat) : QubitBasis n → ℝ :=
  fun basis => if basis = zeroBasis119 n then 1 else 0

theorem zeroAmplitude023_norm (n : Nat) : realEnergy023 (zeroAmplitude023 n) = 1 := by
  classical
  simp [realEnergy023, zeroAmplitude023, pow_two]

theorem q1EnergySplit023 (v : QubitBasis 1 → ℝ) :
    realEnergy023 v = v q1Zero119 ^ 2 + v q1One119 ^ 2 := by
  have h := branchSquareSum_add119 (n := 0) v
  have hzero :
      (splitHighestSelectorEquiv 0).symm (false, default) = q1Zero119 := by
    funext wire
    have hw : wire = (0 : Fin 1) := Fin.eq_zero wire
    subst wire
    rfl
  have hone :
      (splitHighestSelectorEquiv 0).symm (true, default) = q1One119 := by
    funext wire
    have hw : wire = (0 : Fin 1) := Fin.eq_zero wire
    subst wire
    rfl
  have h' := h.symm
  simp only [branchAmplitude119, combineHighestSelector,
    Fintype.sum_unique] at h'
  have hzeroV := congrArg (fun z : QubitBasis 1 => v z ^ 2) hzero
  have honeV := congrArg (fun z : QubitBasis 1 => v z ^ 2) hone
  calc
    (∑ b : QubitBasis 1, v b ^ 2) =
        v ((splitHighestSelectorEquiv 0).symm (false, default)) ^ 2 +
          v ((splitHighestSelectorEquiv 0).symm (true, default)) ^ 2 := h'
    _ = v q1Zero119 ^ 2 + v q1One119 ^ 2 := by rw [hzeroV, honeV]

def q1SignedAngle023 (v : QubitBasis 1 → ℝ) : ℝ :=
  if 0 ≤ v q1One119 then
    2 * Real.arccos (v q1Zero119)
  else
    -(2 * Real.arccos (v q1Zero119))

theorem q1SignedAngle023_cos {v : QubitBasis 1 → ℝ}
    (normOne : realEnergy023 v = 1) :
    Real.cos (q1SignedAngle023 v / 2) = v q1Zero119 := by
  have hpair : v q1Zero119 ^ 2 + v q1One119 ^ 2 = 1 := by
    rw [← q1EnergySplit023 v]
    exact normOne
  have hlow : -1 ≤ v q1Zero119 := by
    nlinarith [sq_nonneg (v q1One119)]
  have hhigh : v q1Zero119 ≤ 1 := by
    nlinarith [sq_nonneg (v q1One119)]
  by_cases hsign : 0 ≤ v q1One119
  · simp only [q1SignedAngle023, if_pos hsign]
    rw [show (2 * Real.arccos (v q1Zero119)) / 2 =
      Real.arccos (v q1Zero119) by ring]
    exact Real.cos_arccos hlow hhigh
  · simp only [q1SignedAngle023, if_neg hsign]
    rw [show -(2 * Real.arccos (v q1Zero119)) / 2 =
      -(Real.arccos (v q1Zero119)) by ring, Real.cos_neg]
    exact Real.cos_arccos hlow hhigh

theorem q1SignedAngle023_sin {v : QubitBasis 1 → ℝ}
    (normOne : realEnergy023 v = 1) :
    Real.sin (q1SignedAngle023 v / 2) = v q1One119 := by
  have hpair : v q1Zero119 ^ 2 + v q1One119 ^ 2 = 1 := by
    rw [← q1EnergySplit023 v]
    exact normOne
  have hlow : -1 ≤ v q1Zero119 := by
    nlinarith [sq_nonneg (v q1One119)]
  have hhigh : v q1Zero119 ≤ 1 := by
    nlinarith [sq_nonneg (v q1One119)]
  have hsqrt :
      Real.sqrt (1 - v q1Zero119 ^ 2) = |v q1One119| := by
    rw [show 1 - v q1Zero119 ^ 2 = v q1One119 ^ 2 by nlinarith [hpair],
      Real.sqrt_sq_eq_abs]
  by_cases hsign : 0 ≤ v q1One119
  · simp only [q1SignedAngle023, if_pos hsign]
    rw [show (2 * Real.arccos (v q1Zero119)) / 2 =
      Real.arccos (v q1Zero119) by ring, Real.sin_arccos, hsqrt,
      abs_of_nonneg hsign]
  · have hnegative : v q1One119 < 0 := lt_of_not_ge hsign
    simp only [q1SignedAngle023, if_neg hsign]
    rw [show -(2 * Real.arccos (v q1Zero119)) / 2 =
      -(Real.arccos (v q1Zero119)) by ring, Real.sin_neg,
      Real.sin_arccos, hsqrt, abs_of_neg hnegative]
    ring

theorem q1SignedState023 {v : QubitBasis 1 → ℝ}
    (normOne : realEnergy023 v = 1) :
    q1CosSinState119 (q1SignedAngle023 v) =
      (fun basis => (v basis : ℂ)) := by
  funext basis
  cases hbit : basis 0 with
  | false =>
      have hbasis : basis = q1Zero119 := by
        funext wire
        have hw : wire = (0 : Fin 1) := Fin.eq_zero wire
        subst wire
        exact hbit
      rw [hbasis]
      change (Real.cos (q1SignedAngle023 v / 2) : ℂ) =
        (v q1Zero119 : ℂ)
      rw [q1SignedAngle023_cos normOne]
  | true =>
      have hbasis : basis = q1One119 := by
        funext wire
        have hw : wire = (0 : Fin 1) := Fin.eq_zero wire
        subst wire
        exact hbit
      rw [hbasis]
      change (Real.sin (q1SignedAngle023 v / 2) : ℂ) =
        (v q1One119 : ℂ)
      rw [q1SignedAngle023_sin normOne]

def normalizedBranchAmplitude023 {n : Nat} (highest : Bool)
    (amplitude : QubitBasis (n + 1) → ℝ) : QubitBasis n → ℝ :=
  if _ : branchNorm119 highest amplitude = 0 then
    zeroAmplitude023 n
  else
    fun lower =>
      branchAmplitude119 highest amplitude lower /
        branchNorm119 highest amplitude

theorem branchNorm_sq_eq_energy023 {n : Nat}
    (highest : Bool) (amplitude : QubitBasis (n + 1) → ℝ) :
    branchNorm119 highest amplitude ^ 2 =
      ∑ lower : QubitBasis n,
        branchAmplitude119 highest amplitude lower ^ 2 := by
  unfold branchNorm119
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg (fun lower _ => sq_nonneg _)

theorem branchAmplitude_zero_of_norm_zero023 {n : Nat}
    (highest : Bool) (amplitude : QubitBasis (n + 1) → ℝ)
    (normZero : branchNorm119 highest amplitude = 0)
    (lower : QubitBasis n) :
    branchAmplitude119 highest amplitude lower = 0 := by
  have energyZero :
      (∑ lower' : QubitBasis n,
        branchAmplitude119 highest amplitude lower' ^ 2) = 0 := by
    rw [← branchNorm_sq_eq_energy023 highest amplitude, normZero]
    simp
  have termLe :
      branchAmplitude119 highest amplitude lower ^ 2 ≤
        ∑ lower' : QubitBasis n,
          branchAmplitude119 highest amplitude lower' ^ 2 := by
    exact Finset.single_le_sum
      (fun b _ => sq_nonneg (branchAmplitude119 highest amplitude b))
      (Finset.mem_univ lower)
  have termZero : branchAmplitude119 highest amplitude lower ^ 2 = 0 := by
    nlinarith
  exact sq_eq_zero_iff.mp termZero

theorem normalizedBranchAmplitude023_norm {n : Nat}
    (highest : Bool) (amplitude : QubitBasis (n + 1) → ℝ) :
    realEnergy023 (normalizedBranchAmplitude023 highest amplitude) = 1 := by
  classical
  by_cases normZero : branchNorm119 highest amplitude = 0
  · simp only [normalizedBranchAmplitude023, dif_pos normZero]
    exact zeroAmplitude023_norm n
  · have energyNonneg :
        0 ≤ ∑ lower : QubitBasis n,
          branchAmplitude119 highest amplitude lower ^ 2 := by
      exact Finset.sum_nonneg (fun lower _ => sq_nonneg _)
    have energyNe :
        (∑ lower : QubitBasis n,
          branchAmplitude119 highest amplitude lower ^ 2) ≠ 0 := by
      intro energyZero
      apply normZero
      unfold branchNorm119
      rw [energyZero]
      simp
    have energyPos :
        0 < ∑ lower : QubitBasis n,
          branchAmplitude119 highest amplitude lower ^ 2 :=
      lt_of_le_of_ne energyNonneg (Ne.symm energyNe)
    have normSq := branchNorm_sq_eq_energy023 highest amplitude
    have hsum :
        (∑ lower : QubitBasis n,
          (branchAmplitude119 highest amplitude lower /
            branchNorm119 highest amplitude) ^ 2) =
          (∑ lower : QubitBasis n,
            branchAmplitude119 highest amplitude lower ^ 2) /
            branchNorm119 highest amplitude ^ 2 := by
      simp_rw [div_pow]
      rw [← Finset.sum_div]
    unfold realEnergy023 normalizedBranchAmplitude023
    rw [dif_neg normZero, hsum, normSq]
    field_simp [normZero]

theorem normalizedBranchAmplitude023_mul_norm {n : Nat}
    (highest : Bool) (amplitude : QubitBasis (n + 1) → ℝ)
    (lower : QubitBasis n) :
    branchNorm119 highest amplitude *
        normalizedBranchAmplitude023 highest amplitude lower =
      branchAmplitude119 highest amplitude lower := by
  classical
  by_cases normZero : branchNorm119 highest amplitude = 0
  · rw [normZero, zero_mul]
    exact (branchAmplitude_zero_of_norm_zero023 highest amplitude normZero lower).symm
  · simp only [normalizedBranchAmplitude023, dif_neg normZero]
    field_simp [normZero]

def stateFromAmplitude023 : (n : Nat) →
    (QubitBasis n → ℝ) → State (QubitBasis (prepWidth023 n))
  | 0, _ => 0
  | 1, amplitude =>
      fixedOutsideStateEmbedding (topPlacement119 0) (topOutsideZero119 0)
        (q1CosSinState119 (q1SignedAngle023 amplitude))
  | n + 2, amplitude =>
      (branchNorm119 false amplitude : ℂ) •
          fixedOutsideStateEmbedding
            (lowerPlacement119 (prepWidth023 (n + 1)))
            (fun wire => if wire.1 = topControl119 (prepWidth023 (n + 1))
              then false else false)
            (stateFromAmplitude023 (n + 1)
              (normalizedBranchAmplitude023 false amplitude)) +
        (branchNorm119 true amplitude : ℂ) •
          fixedOutsideStateEmbedding
            (lowerPlacement119 (prepWidth023 (n + 1)))
            (fun wire => if wire.1 = topControl119 (prepWidth023 (n + 1))
              then true else false)
            (stateFromAmplitude023 (n + 1)
              (normalizedBranchAmplitude023 true amplitude))

theorem leadingRyCircuit119_isNormalized023 (n : Nat) (angle : ℝ) :
    ControlledCircuitCompilerV2.IsNormalizedCircuit
      (leadingRyCircuit119 n angle) := by
  intro gate member
  cases gate <;> simp [ControlledCircuitCompilerV2.IsNormalizedPrimitive]

def baseNormalizedCircuit023 (amplitude : QubitBasis 1 → ℝ) :
    NormalizedCircuit (prepWidth023 1) :=
  { circuit := leadingRyCircuit119 0 (q1SignedAngle023 amplitude)
    normalized := leadingRyCircuit119_isNormalized023 0
      (q1SignedAngle023 amplitude) }

theorem baseState_embedding023 (amplitude : QubitBasis 1 → ℝ) :
    fixedOutsideStateEmbedding (topPlacement119 0) (topOutsideZero119 0)
        (q1CosSinState119 (q1SignedAngle023 amplitude)) =
      (Real.cos (q1SignedAngle023 amplitude / 2) : ℂ) •
          basisKet (allZeroTop119 0 false) +
        (Real.sin (q1SignedAngle023 amplitude / 2) : ℂ) •
          basisKet (allZeroTop119 0 true) := by
  rw [q1CosSinState119_decompose,
    fixedOutsideStateEmbedding_add119,
    fixedOutsideStateEmbedding_smul119,
    fixedOutsideStateEmbedding_smul119,
    show q1Zero119 = (fun _ : Fin 1 => false) by rfl,
    show q1One119 = (fun _ : Fin 1 => true) by rfl,
    topEmbedding_basis119, topEmbedding_basis119]

theorem basePreparation023 {amplitude : QubitBasis 1 → ℝ} :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
          (baseNormalizedCircuit023 amplitude).circuit)
        (basisKet (zeroBasis119 (prepWidth023 1))) =
      stateFromAmplitude023 1 amplitude := by
  unfold stateFromAmplitude023
  simp only [prepWidth023]
  change applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
        (leadingRyCircuit119 0 (q1SignedAngle023 amplitude)))
      (basisKet (zeroBasis119 (prepWidth023 1))) = _
  have hzero :
    zeroBasis119 (prepWidth023 1) =
        allZeroTop119 0 false := by
    funext wire
    change false = if wire = topControl119 0 then false else false
    simp
  rw [hzero, leadingRy_on_zero_top119, baseState_embedding023]

theorem branchCompositionCircuit119_isNormalized023 {n : Nat} (angle : ℝ)
    (left right : NormalizedCircuit n) :
    ControlledCircuitCompilerV2.IsNormalizedCircuit
      (branchCompositionCircuit119 angle left right) := by
  intro gate member
  simp only [branchCompositionCircuit119, Circuit.flatten_sequence,
    List.mem_flatMap] at member
  rcases member with ⟨circuit, circuits, gateMember⟩
  simp at circuits
  rcases circuits with h | h | h
  · subst circuit
    exact leadingRyCircuit119_isNormalized023 n angle gate gateMember
  · subst circuit
    exact (lowerCircuitLift119 left).normalized gate gateMember
  · subst circuit
    exact (controlCircuit (branchControlLayout119 n)
      (relativeCircuit119 left right)).normalized gate gateMember

theorem branchAngle_cos023 {n : Nat}
    {amplitude : QubitBasis (n + 1) → ℝ}
    (normOne : realEnergy023 amplitude = 1) :
    Real.cos (Real.arccos (branchNorm119 false amplitude)) =
      branchNorm119 false amplitude := by
  have hsum := branchNorm_sq_add119 amplitude normOne
  have hleft : 0 ≤ branchNorm119 false amplitude := Real.sqrt_nonneg _
  have hright : 0 ≤ branchNorm119 true amplitude := Real.sqrt_nonneg _
  have hleft_le : branchNorm119 false amplitude ≤ 1 := by
    nlinarith [sq_nonneg (branchNorm119 true amplitude)]
  exact Real.cos_arccos (by linarith) hleft_le

theorem branchAngle_sin023 {n : Nat}
    {amplitude : QubitBasis (n + 1) → ℝ}
    (normOne : realEnergy023 amplitude = 1) :
    Real.sin (Real.arccos (branchNorm119 false amplitude)) =
      branchNorm119 true amplitude := by
  have hsum := branchNorm_sq_add119 amplitude normOne
  have hleft : 0 ≤ branchNorm119 false amplitude := Real.sqrt_nonneg _
  have hright : 0 ≤ branchNorm119 true amplitude := Real.sqrt_nonneg _
  have hleft_le : branchNorm119 false amplitude ≤ 1 := by
    nlinarith [sq_nonneg (branchNorm119 true amplitude)]
  rw [Real.sin_arccos,
    show 1 - branchNorm119 false amplitude ^ 2 =
      branchNorm119 true amplitude ^ 2 by nlinarith [hsum],
    Real.sqrt_sq_eq_abs, abs_of_nonneg hright]

def cleanSpanPredicate023 : QubitBasis (prepWidth023 1) → Prop :=
  externallyControlledCleanWorkPredicate
    (externalValid119 (branchControlLayout119 0))

inductive CleanWorkTrace023 : (n : Nat) →
    State (QubitBasis (prepWidth023 n)) → Prop
  | zero (state : State (QubitBasis (prepWidth023 0))) :
      CleanWorkTrace023 0 state
  | one (state : State (QubitBasis (prepWidth023 1)))
      (clean : state ∈ SubspaceMapComponent.basisSpan
        cleanSpanPredicate023) :
      CleanWorkTrace023 1 state
  | step {n : Nat}
      {amplitude : QubitBasis (n + 2) → ℝ}
      {state : State (QubitBasis (prepWidth023 (n + 2)))}
      {left right : State (QubitBasis (prepWidth023 (n + 1)))}
      (decomposition : HEq state
        ((branchNorm119 false amplitude : ℂ) •
            fixedOutsideStateEmbedding (lowerPlacement119
              (prepWidth023 (n + 1)))
              (fun wire => if wire.1 = topControl119
                (prepWidth023 (n + 1)) then false else false) left +
          (branchNorm119 true amplitude : ℂ) •
            fixedOutsideStateEmbedding (lowerPlacement119
              (prepWidth023 (n + 1)))
              (fun wire => if wire.1 = topControl119
                (prepWidth023 (n + 1)) then true else false) right))
      (leftTrace : CleanWorkTrace023 (n + 1) left)
      (rightTrace : CleanWorkTrace023 (n + 1) right) :
      CleanWorkTrace023 (n + 2) state

structure RealPreparationWitness023 (n : Nat)
    (amplitude : QubitBasis n → ℝ) where
  circuit : NormalizedCircuit (prepWidth023 n)
  prepares :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0)) circuit.circuit)
        (basisKet (zeroBasis119 (prepWidth023 n))) =
      stateFromAmplitude023 n amplitude
  clean : CleanWorkTrace023 n (stateFromAmplitude023 n amplitude)

theorem branchComposition_zeroInput023 {n : Nat} :
    basisKet (zeroBasis119 (n + 3)) =
      basisKet (allZeroTop119 n false) := by
  congr 1
  funext wire
  change false = if wire = topControl119 n then false else false
  simp

theorem stateFromAmplitude023_succ_heq (n : Nat)
    (amplitude : QubitBasis (n + 1 + 1) → ℝ) :
    HEq (stateFromAmplitude023 (n + 1 + 1) amplitude)
      ((branchNorm119 false amplitude : ℂ) •
          fixedOutsideStateEmbedding (lowerPlacement119
            (prepWidth023 (n + 1)))
            (fun wire => if wire.1 = topControl119
              (prepWidth023 (n + 1)) then false else false)
            (stateFromAmplitude023 (n + 1)
              (normalizedBranchAmplitude023 false amplitude)) +
        (branchNorm119 true amplitude : ℂ) •
          fixedOutsideStateEmbedding (lowerPlacement119
            (prepWidth023 (n + 1)))
            (fun wire => if wire.1 = topControl119
              (prepWidth023 (n + 1)) then true else false)
            (stateFromAmplitude023 (n + 1)
              (normalizedBranchAmplitude023 true amplitude))) := by
  change HEq
    ((branchNorm119 false amplitude : ℂ) •
        fixedOutsideStateEmbedding (lowerPlacement119
          (prepWidth023 (n + 1)))
          (fun wire => if wire.1 = topControl119
            (prepWidth023 (n + 1)) then false else false)
          (stateFromAmplitude023 (n + 1)
            (normalizedBranchAmplitude023 false amplitude)) +
      (branchNorm119 true amplitude : ℂ) •
        fixedOutsideStateEmbedding (lowerPlacement119
          (prepWidth023 (n + 1)))
          (fun wire => if wire.1 = topControl119
            (prepWidth023 (n + 1)) then true else false)
          (stateFromAmplitude023 (n + 1)
            (normalizedBranchAmplitude023 true amplitude)))
    ((branchNorm119 false amplitude : ℂ) •
        fixedOutsideStateEmbedding (lowerPlacement119
          (prepWidth023 (n + 1)))
          (fun wire => if wire.1 = topControl119
            (prepWidth023 (n + 1)) then false else false)
          (stateFromAmplitude023 (n + 1)
            (normalizedBranchAmplitude023 false amplitude)) +
      (branchNorm119 true amplitude : ℂ) •
        fixedOutsideStateEmbedding (lowerPlacement119
          (prepWidth023 (n + 1)))
          (fun wire => if wire.1 = topControl119
            (prepWidth023 (n + 1)) then true else false)
          (stateFromAmplitude023 (n + 1)
            (normalizedBranchAmplitude023 true amplitude)))
  rfl

theorem baseCleanTrace023 (amplitude : QubitBasis 1 → ℝ) :
    CleanWorkTrace023 1 (stateFromAmplitude023 1 amplitude) := by
  change CleanWorkTrace023 1
    (fixedOutsideStateEmbedding (topPlacement119 0) (topOutsideZero119 0)
      (q1CosSinState119 (q1SignedAngle023 amplitude)))
  apply CleanWorkTrace023.one
  change fixedOutsideStateEmbedding (topPlacement119 0) (topOutsideZero119 0)
      (q1CosSinState119 (q1SignedAngle023 amplitude)) ∈
    SubspaceMapComponent.basisSpan
      (externallyControlledCleanWorkPredicate
        (externalValid119 (branchControlLayout119 0)))
  rw [baseState_embedding023]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    rw [← lowerEmbedding_basis119_pre 0 false]
    exact explicitBranchEmbedding119_mem_cleanSpan false
      (basisKet (zeroBasis119 0))
  · apply Submodule.smul_mem
    rw [← lowerEmbedding_basis119_pre 0 true]
    exact explicitBranchEmbedding119_mem_cleanSpan true
      (basisKet (zeroBasis119 0))

theorem existsRealPreparationSucc023 :
    ∀ n (amplitude : QubitBasis (n + 1) → ℝ),
      realEnergy023 amplitude = 1 →
        Nonempty (RealPreparationWitness023 (n + 1) amplitude) := by
  intro n
  induction n with
  | zero =>
      intro amplitude normOne
      exact ⟨{
        circuit := baseNormalizedCircuit023 amplitude
        prepares := basePreparation023
        clean := baseCleanTrace023 amplitude }⟩
  | succ n ih =>
      intro amplitude normOne
      have leftNormOne :
          realEnergy023 (normalizedBranchAmplitude023 false amplitude) = 1 :=
        normalizedBranchAmplitude023_norm false amplitude
      have rightNormOne :
          realEnergy023 (normalizedBranchAmplitude023 true amplitude) = 1 :=
        normalizedBranchAmplitude023_norm true amplitude
      rcases ih (normalizedBranchAmplitude023 false amplitude) leftNormOne with
        ⟨leftWitness⟩
      rcases ih (normalizedBranchAmplitude023 true amplitude) rightNormOne with
        ⟨rightWitness⟩
      let angle : ℝ := 2 * Real.arccos (branchNorm119 false amplitude)
      have hcos : Real.cos (angle / 2) = branchNorm119 false amplitude := by
        dsimp [angle]
        rw [show (2 * Real.arccos (branchNorm119 false amplitude)) / 2 =
          Real.arccos (branchNorm119 false amplitude) by ring]
        exact branchAngle_cos023 normOne
      have hsin : Real.sin (angle / 2) = branchNorm119 true amplitude := by
        dsimp [angle]
        rw [show (2 * Real.arccos (branchNorm119 false amplitude)) / 2 =
          Real.arccos (branchNorm119 false amplitude) by ring]
        exact branchAngle_sin023 normOne
      generalize hw : prepWidth023 (n + 1 + 1) = physicalWidth at *
      have hwidth : physicalWidth = prepWidth023 (n + 1) + 3 := by
        rw [← hw, prepWidth023]
      cases hwidth
      let circuit : NormalizedCircuit (prepWidth023 (n + 1) + 3) :=
        { circuit := branchCompositionCircuit119 angle
            leftWitness.circuit rightWitness.circuit
          normalized := branchCompositionCircuit119_isNormalized023 angle
            leftWitness.circuit rightWitness.circuit }
      have hprep := branchCompositionCircuit119_prepares angle
        leftWitness.circuit rightWitness.circuit
        (stateFromAmplitude023 (n + 1)
          (normalizedBranchAmplitude023 false amplitude))
        (stateFromAmplitude023 (n + 1)
          (normalizedBranchAmplitude023 true amplitude))
        leftWitness.prepares rightWitness.prepares
      have hprepZero :
          applyOperator
              (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ => 0))
                (branchCompositionCircuit119 angle leftWitness.circuit
                  rightWitness.circuit))
              (basisKet (zeroBasis119 (prepWidth023 (n + 1) + 3))) =
            (Real.cos (angle / 2) : ℂ) •
                fixedOutsideStateEmbedding (lowerPlacement119
                  (prepWidth023 (n + 1)))
                  (fun wire => if wire.1 = topControl119
                    (prepWidth023 (n + 1)) then false else false)
                  (stateFromAmplitude023 (n + 1)
                    (normalizedBranchAmplitude023 false amplitude)) +
              (Real.sin (angle / 2) : ℂ) •
                fixedOutsideStateEmbedding (lowerPlacement119
                  (prepWidth023 (n + 1)))
                  (fun wire => if wire.1 = topControl119
                    (prepWidth023 (n + 1)) then true else false)
                  (stateFromAmplitude023 (n + 1)
                    (normalizedBranchAmplitude023 true amplitude)) := by
        rw [branchComposition_zeroInput023
          (n := prepWidth023 (n + 1))]
        exact hprep
      have hprepZeroNorm := hprepZero
      rw [hcos, hsin] at hprepZeroNorm
      have hfalseOutside :
          (fun wire : OutsideWire (lowerPlacement119
              (prepWidth023 (n + 1))) =>
            if wire.1 = topControl119 (prepWidth023 (n + 1))
            then false else false) =
            (fun _ => false) := by
        funext wire
        simp
      rw [hfalseOutside] at hprepZeroNorm
      refine ⟨{
        circuit := circuit
        prepares := ?_
        clean := ?_ }⟩
      · dsimp [circuit]
        convert hprepZeroNorm using 1
        · exact congrArg (fun q : Nat => State (QubitBasis q)) hw
        · rfl
        · simpa using stateFromAmplitude023_succ_heq n amplitude
      · exact CleanWorkTrace023.step
          (amplitude := amplitude)
          (stateFromAmplitude023_succ_heq n amplitude)
          leftWitness.clean rightWitness.clean

theorem existsRealPreparation023 {n : Nat}
    (positive : 0 < n) (amplitude : QubitBasis n → ℝ)
    (normOne : realEnergy023 amplitude = 1) :
    Nonempty (RealPreparationWitness023 n amplitude) := by
  cases n with
  | zero => omega
  | succ k =>
      simpa using existsRealPreparationSucc023 k amplitude normOne

noncomputable def realPreparationCircuit023 {n : Nat}
    (positive : 0 < n) (amplitude : QubitBasis n → ℝ)
    (normOne : realEnergy023 amplitude = 1) :
    NormalizedCircuit (prepWidth023 n) :=
  (Classical.choice (existsRealPreparation023 positive amplitude normOne)).circuit

/-! CHAT-024: instantiate the arbitrary-width real preparation with the
    actual P18 padded carrier.  The real amplitude is extracted from the
    already-defined zero-padded state; no circuit or correctness claim is
    placed in the input data. -/

end
end ExecutableHistoryCore
