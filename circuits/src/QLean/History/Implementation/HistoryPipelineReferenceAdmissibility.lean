import QLean.History.Implementation.HistoryPipelineReferenceRawValueConstructorV3

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace HistoryPipelineReferenceAdmissibility041

open Matrix
open HistoryBlockEncoding
open VerifiedCircuitCore
open HistoryPipelineReferenceRawCompiler
open HistoryPipelineReferenceRawSemanticCompiler
open HistoryPipelineReferenceEntryDecoder
open HistoryPipelineReferenceRawValueConstructor
open HistoryPipelineReferenceRawValueConstructorV2
open HistoryPipelineReferenceRawValueConstructorV3

noncomputable section

/-- Independent executable-layout parameters layered over the mathematical
history data.  The probability-generator parameters and the number of
history blocks are deliberately not identified with the Taylor order or the
number of binary labels. -/
structure ReferenceData041 {Configuration : Type*} [Fintype Configuration]
    extends ReferenceData040 (Configuration := Configuration) where
  qParameters : ProbabilityGeneratorQProof.QParameters
  historyBlocks : Nat
  historyBlocksPositive : 0 < historyBlocks

def referenceData041Base
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    ReferenceData040 (Configuration := Configuration) :=
  { parameters := data.parameters
    modelQ := data.modelQ
    initial := data.initial
    omegaH := data.omegaH
    nu := data.nu }

def generatorParameters041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    ProbabilityGeneratorQProof.QParameters :=
  data.qParameters

def rawHistoryBlocks041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) : Nat :=
  data.historyBlocks

def rawIdlingSteps041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) : Nat :=
  rawHistoryBlocks041 data *
      SpectralSamplingProof.Analytic.historyIdleBlockSize
        (rawTaylorOrder036 (referenceData041Base data)) - 1

def structuralPool041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) : ℕ :=
  HistoryRawSchema.rawStructuralPoolWidth203
    (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data)

def workspaceWidth041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) : ℕ :=
  HistoryRawSchema.rawWorkspaceWidth203
    (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data)
    (generatorParameters041 data).generatorWorkWidth

def workspaceBase041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) : ℕ :=
  structuralPool041 data

def semanticBase041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) : ℕ :=
  workspaceBase041 data + workspaceWidth041 data

def qubits041
    {Configuration : Type*} [Fintype Configuration]
  (data : ReferenceData041 (Configuration := Configuration)) : ℕ :=
  (generatorParameters041 data).ancillaWidth +
    (generatorParameters041 data).systemWidth + 1 +
    semanticBase041 data + (generatorParameters041 data).generatorDataWidth +
    SpectralSamplingProof.Analytic.historyClockWidth
      (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data) +
    rawOrderWidth036 (referenceData041Base data) + (generatorParameters041 data).generatorSignalWidth + 4

def selectorWire041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Fin 2 → Fin (qubits041 data) :=
  fun wire => ⟨wire.val, by
    dsimp [qubits041, semanticBase041, workspaceBase041, workspaceWidth041,
      structuralPool041, generatorParameters041]
    omega⟩

def workspaceWire041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Fin (workspaceWidth041 data) → Fin (qubits041 data) :=
  fun wire => ⟨workspaceBase041 data + wire.val, by
    dsimp [qubits041, semanticBase041, workspaceBase041]
    omega⟩

def dataWire041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Fin ((generatorParameters041 data).generatorDataWidth) → Fin (qubits041 data) :=
  fun wire => ⟨semanticBase041 data + wire.val, by
    dsimp [qubits041]
    omega⟩

def clockWire041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Fin (SpectralSamplingProof.Analytic.historyClockWidth
      (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data)) →
      Fin (qubits041 data) :=
  fun wire => ⟨semanticBase041 data + (generatorParameters041 data).generatorDataWidth +
      wire.val, by
    dsimp [qubits041]
    omega⟩

def orderWire041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Fin (rawOrderWidth036 (referenceData041Base data)) → Fin (qubits041 data) :=
  fun wire => ⟨semanticBase041 data + (generatorParameters041 data).generatorDataWidth +
      SpectralSamplingProof.Analytic.historyClockWidth
        (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data) +
      wire.val, by
    dsimp [qubits041]
    omega⟩

def generatorSignalWire041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Fin ((generatorParameters041 data).generatorSignalWidth) → Fin (qubits041 data) :=
  fun wire => ⟨semanticBase041 data + (generatorParameters041 data).generatorDataWidth +
      SpectralSamplingProof.Analytic.historyClockWidth
        (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data) +
      rawOrderWidth036 (referenceData041Base data) + wire.val, by
    dsimp [qubits041]
    omega⟩

theorem offset_blocks_disjoint041
    {n m q b₁ b₂ : ℕ}
    {f : Fin n → Fin q} {g : Fin m → Fin q}
    (hf : ∀ i, (f i).val = b₁ + i.val)
    (hg : ∀ i, (g i).val = b₂ + i.val)
    (hsep : b₁ + n ≤ b₂) :
    ∀ a ∈ List.ofFn f, ∀ b ∈ List.ofFn g, a ≠ b := by
  intro a ha b hb hab
  obtain ⟨i, hi⟩ := (List.mem_ofFn).1 ha
  obtain ⟨j, hj⟩ := (List.mem_ofFn).1 hb
  have hv : (f i).val = (g j).val := by
    rw [hi, hj, hab]
  have hil : i.val < n := i.isLt
  have hjl : 0 ≤ j.val := Nat.zero_le _
  rw [hf i, hg j] at hv
  omega

theorem offset_blocks_disjoint_ordered041
    {n m q b₁ b₂ : ℕ}
    {f : Fin n → Fin q} {g : Fin m → Fin q}
    (hf : ∀ i, (f i).val = b₁ + i.val)
    (hg : ∀ i, (g i).val = b₂ + i.val)
    (hsep : b₁ + n ≤ b₂ ∨ b₂ + m ≤ b₁) :
    ∀ a ∈ List.ofFn f, ∀ b ∈ List.ofFn g, a ≠ b := by
  rcases hsep with hsep | hsep
  · exact offset_blocks_disjoint041 hf hg hsep
  · intro a ha b hb hab
    have hrev : b ≠ a :=
      offset_blocks_disjoint041 hg hf hsep b hb a ha
    exact hrev hab.symm

theorem nodup_append041
    {α : Type*} {left right : List α}
    (left_nodup : left.Nodup) (right_nodup : right.Nodup)
    (separate : ∀ a ∈ left, ∀ b ∈ right, a ≠ b) :
    (left ++ right).Nodup := by
  exact (List.nodup_append).2 ⟨left_nodup, right_nodup, separate⟩

theorem disjoint_append_right041
    {α : Type*} {left right₁ right₂ : List α}
    (h₁ : ∀ a ∈ left, ∀ b ∈ right₁, a ≠ b)
    (h₂ : ∀ a ∈ left, ∀ b ∈ right₂, a ≠ b) :
    ∀ a ∈ left, ∀ b ∈ right₁ ++ right₂, a ≠ b := by
  intro a ha b hb
  rw [List.mem_append] at hb
  rcases hb with hb | hb
  · exact h₁ a ha b hb
  · exact h₂ a ha b hb

theorem offset_block_self_nodup041
    {n q b : ℕ} {f : Fin n → Fin q}
    (hf : ∀ i, (f i).val = b + i.val) :
    (List.ofFn f).Nodup := by
  exact (List.nodup_ofFn).2 (by
    intro i j hij
    apply Fin.ext
    have hv : (f i).val = (f j).val := congrArg Fin.val hij
    rw [hf i, hf j] at hv
    omega)

theorem block_nodup041
    {n q b : ℕ} {f : Fin n → Fin q}
    (hf : ∀ i, (f i).val = b + i.val) :
    (List.ofFn f).Nodup :=
  offset_block_self_nodup041 hf

def referenceHistoryP15P16Raw041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    HistoryRawSchema.HistoryP15P16Raw203 :=
  let old := referenceHistoryP15P16Raw040 (referenceData041Base data)
  { qubits := qubits041 data
    dataWidth := (generatorParameters041 data).generatorDataWidth
    generatorSignalWidth := (generatorParameters041 data).generatorSignalWidth
    generatorWorkWidth := (generatorParameters041 data).generatorWorkWidth
    timeSteps := old.timeSteps
    taylorOrder := old.taylorOrder
    idlingSteps := rawIdlingSteps041 data
    historyBlocks := rawHistoryBlocks041 data
    duration := old.duration
    targetStateError := old.targetStateError
    stepSize := old.stepSize
    omegaH := old.omegaH
    historyBlockScale := old.historyBlockScale
    gTaylor := old.gTaylor
    analyticQ := old.analyticQ
    analyticH := old.analyticH
    analyticTolerance := old.analyticTolerance
    analyticSelectorAngles := old.analyticSelectorAngles
    analyticCoefficientAngles := old.analyticCoefficientAngles
    analyticIdleAngle := old.analyticIdleAngle
    selectorPreparationAngles := old.selectorPreparationAngles
    coefficientAngles := old.coefficientAngles
    idleCoefficientAngle := old.idleCoefficientAngle
    rawCoefficientAngles := old.rawCoefficientAngles
    rawIdleCoefficientAngle := old.rawIdleCoefficientAngle
    selectorHighAngle := old.selectorHighAngle
    selectorLowAngle := old.selectorLowAngle
    selectorSecondLowAngle := old.selectorSecondLowAngle
    selectorWire := selectorWire041 data
    dataWire := dataWire041 data
    clockWire := clockWire041 data
    orderWire := orderWire041 data
    generatorSignalWire := generatorSignalWire041 data
    coefficientSignal := ⟨semanticBase041 data +
      (generatorParameters041 data).generatorDataWidth +
      SpectralSamplingProof.Analytic.historyClockWidth
        (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data) +
      rawOrderWidth036 (referenceData041Base data) + (generatorParameters041 data).generatorSignalWidth, by
      dsimp [qubits041]
      omega⟩
    orderBoundarySignal := ⟨semanticBase041 data +
      (generatorParameters041 data).generatorDataWidth +
      SpectralSamplingProof.Analytic.historyClockWidth
        (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data) +
      rawOrderWidth036 (referenceData041Base data) + (generatorParameters041 data).generatorSignalWidth + 1, by
      dsimp [qubits041]
      omega⟩
    projectorSignal := ⟨semanticBase041 data +
      (generatorParameters041 data).generatorDataWidth +
      SpectralSamplingProof.Analytic.historyClockWidth
        (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data) +
      rawOrderWidth036 (referenceData041Base data) + (generatorParameters041 data).generatorSignalWidth + 2, by
      dsimp [qubits041]
      omega⟩
    clockBoundarySignal := ⟨semanticBase041 data +
      (generatorParameters041 data).generatorDataWidth +
      SpectralSamplingProof.Analytic.historyClockWidth
        (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data) +
      rawOrderWidth036 (referenceData041Base data) + (generatorParameters041 data).generatorSignalWidth + 3, by
      dsimp [qubits041]
      omega⟩
    workspaceWire := workspaceWire041 data }

def signalWire041
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Fin 4 → Fin (qubits041 data) :=
  fun wire => ⟨semanticBase041 data + (generatorParameters041 data).generatorDataWidth +
      SpectralSamplingProof.Analytic.historyClockWidth
        (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data) +
      rawOrderWidth036 (referenceData041Base data) + (generatorParameters041 data).generatorSignalWidth + wire.val, by
    dsimp [qubits041]
    omega⟩

theorem history041_allWiresNodup
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    (List.ofFn (selectorWire041 data) ++
      List.ofFn (dataWire041 data) ++
      List.ofFn (clockWire041 data) ++
      List.ofFn (orderWire041 data) ++
      List.ofFn (generatorSignalWire041 data) ++
      List.ofFn (signalWire041 data) ++
      List.ofFn (workspaceWire041 data)).Nodup := by
  have hs : (List.ofFn (selectorWire041 data)).Nodup := by
    apply block_nodup041 (f := selectorWire041 data) (b := 0)
    intro i
    simp [selectorWire041]
  have hd : (List.ofFn (dataWire041 data)).Nodup := by
    apply block_nodup041 (f := dataWire041 data)
      (b := semanticBase041 data)
    intro i
    simp [dataWire041]
  have hc : (List.ofFn (clockWire041 data)).Nodup := by
    apply block_nodup041 (f := clockWire041 data)
      (b := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth)
    intro i
    simp [clockWire041]
  have ho : (List.ofFn (orderWire041 data)).Nodup := by
    apply block_nodup041 (f := orderWire041 data)
      (b := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data))
    intro i
    simp [orderWire041]
  have hg : (List.ofFn (generatorSignalWire041 data)).Nodup := by
    apply block_nodup041 (f := generatorSignalWire041 data)
      (b := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data))
    intro i
    simp [generatorSignalWire041]
  have hf : (List.ofFn (signalWire041 data)).Nodup := by
    apply block_nodup041 (f := signalWire041 data)
      (b := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data) +
        (generatorParameters041 data).generatorSignalWidth)
    intro i
    simp [signalWire041]
  have hw : (List.ofFn (workspaceWire041 data)).Nodup := by
    apply block_nodup041 (f := workspaceWire041 data)
      (b := workspaceBase041 data)
    intro i
    simp [workspaceWire041]
  have hsd : ∀ a ∈ List.ofFn (selectorWire041 data),
      ∀ b ∈ List.ofFn (dataWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := selectorWire041 data) (g := dataWire041 data)
      (b₁ := 0) (b₂ := semanticBase041 data)
    · intro i
      simp [selectorWire041]
    · intro i
      rfl
    · left
      dsimp [semanticBase041, workspaceBase041, structuralPool041,
        workspaceWidth041]
      unfold HistoryRawSchema.rawStructuralPoolWidth203
      omega
  have hsc : ∀ a ∈ List.ofFn (selectorWire041 data),
      ∀ b ∈ List.ofFn (clockWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := selectorWire041 data) (g := clockWire041 data)
      (b₁ := 0) (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth)
    · intro i
      simp [selectorWire041]
    · intro i
      rfl
    · left
      dsimp [semanticBase041, workspaceBase041, structuralPool041,
        workspaceWidth041]
      unfold HistoryRawSchema.rawStructuralPoolWidth203
      omega
  have hso : ∀ a ∈ List.ofFn (selectorWire041 data),
      ∀ b ∈ List.ofFn (orderWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := selectorWire041 data) (g := orderWire041 data)
      (b₁ := 0) (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data))
    · intro i
      simp [selectorWire041]
    · intro i
      rfl
    · left
      dsimp [semanticBase041, workspaceBase041, structuralPool041,
        workspaceWidth041]
      unfold HistoryRawSchema.rawStructuralPoolWidth203
      omega
  have hsg : ∀ a ∈ List.ofFn (selectorWire041 data),
      ∀ b ∈ List.ofFn (generatorSignalWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := selectorWire041 data) (g := generatorSignalWire041 data)
      (b₁ := 0) (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data))
    · intro i
      simp [selectorWire041]
    · intro i
      rfl
    · left
      dsimp [semanticBase041, workspaceBase041, structuralPool041,
        workspaceWidth041]
      unfold HistoryRawSchema.rawStructuralPoolWidth203
      omega
  have hsf : ∀ a ∈ List.ofFn (selectorWire041 data),
      ∀ b ∈ List.ofFn (signalWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := selectorWire041 data) (g := signalWire041 data)
      (b₁ := 0) (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data) +
        (generatorParameters041 data).generatorSignalWidth)
    · intro i
      simp [selectorWire041]
    · intro i
      rfl
    · left
      dsimp [semanticBase041, workspaceBase041, structuralPool041,
        workspaceWidth041]
      unfold HistoryRawSchema.rawStructuralPoolWidth203
      omega
  have hsw : ∀ a ∈ List.ofFn (selectorWire041 data),
      ∀ b ∈ List.ofFn (workspaceWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := selectorWire041 data) (g := workspaceWire041 data)
      (b₁ := 0) (b₂ := workspaceBase041 data)
    · intro i
      simp [selectorWire041]
    · intro i
      rfl
    · left
      dsimp [workspaceBase041, structuralPool041]
      unfold HistoryRawSchema.rawStructuralPoolWidth203
      omega
  have hdc : ∀ a ∈ List.ofFn (dataWire041 data),
      ∀ b ∈ List.ofFn (clockWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := dataWire041 data) (g := clockWire041 data)
      (b₁ := semanticBase041 data)
      (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth)
    · intro i
      rfl
    · intro i
      rfl
    · left
      omega
  have hdo : ∀ a ∈ List.ofFn (dataWire041 data),
      ∀ b ∈ List.ofFn (orderWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := dataWire041 data) (g := orderWire041 data)
      (b₁ := semanticBase041 data)
      (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data))
    · intro i
      rfl
    · intro i
      rfl
    · left
      omega
  have hdg : ∀ a ∈ List.ofFn (dataWire041 data),
      ∀ b ∈ List.ofFn (generatorSignalWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := dataWire041 data) (g := generatorSignalWire041 data)
      (b₁ := semanticBase041 data)
      (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data))
    · intro i
      rfl
    · intro i
      rfl
    · left
      omega
  have hdf : ∀ a ∈ List.ofFn (dataWire041 data),
      ∀ b ∈ List.ofFn (signalWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := dataWire041 data) (g := signalWire041 data)
      (b₁ := semanticBase041 data)
      (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data) +
        (generatorParameters041 data).generatorSignalWidth)
    · intro i
      rfl
    · intro i
      rfl
    · left
      omega
  have hdw : ∀ a ∈ List.ofFn (dataWire041 data),
      ∀ b ∈ List.ofFn (workspaceWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := dataWire041 data) (g := workspaceWire041 data)
      (b₁ := semanticBase041 data) (b₂ := workspaceBase041 data)
    · intro i
      rfl
    · intro i
      rfl
    · right
      dsimp [semanticBase041, workspaceBase041]
      omega
  have hco : ∀ a ∈ List.ofFn (clockWire041 data),
      ∀ b ∈ List.ofFn (orderWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := clockWire041 data) (g := orderWire041 data)
      (b₁ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth)
      (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data))
    · intro i
      rfl
    · intro i
      rfl
    · left
      omega
  have hcg : ∀ a ∈ List.ofFn (clockWire041 data),
      ∀ b ∈ List.ofFn (generatorSignalWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := clockWire041 data) (g := generatorSignalWire041 data)
      (b₁ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth)
      (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data))
    · intro i
      rfl
    · intro i
      rfl
    · left
      omega
  have hcf : ∀ a ∈ List.ofFn (clockWire041 data),
      ∀ b ∈ List.ofFn (signalWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := clockWire041 data) (g := signalWire041 data)
      (b₁ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth)
      (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data) +
        (generatorParameters041 data).generatorSignalWidth)
    · intro i
      rfl
    · intro i
      rfl
    · left
      omega
  have hcw : ∀ a ∈ List.ofFn (clockWire041 data),
      ∀ b ∈ List.ofFn (workspaceWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := clockWire041 data) (g := workspaceWire041 data)
      (b₁ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth)
      (b₂ := workspaceBase041 data)
    · intro i
      rfl
    · intro i
      rfl
    · right
      dsimp [semanticBase041, workspaceBase041]
      omega
  have hog : ∀ a ∈ List.ofFn (orderWire041 data),
      ∀ b ∈ List.ofFn (generatorSignalWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := orderWire041 data) (g := generatorSignalWire041 data)
      (b₁ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data))
      (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data))
    · intro i
      rfl
    · intro i
      rfl
    · left
      omega
  have hof : ∀ a ∈ List.ofFn (orderWire041 data),
      ∀ b ∈ List.ofFn (signalWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := orderWire041 data) (g := signalWire041 data)
      (b₁ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data))
      (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data) +
        (generatorParameters041 data).generatorSignalWidth)
    · intro i
      rfl
    · intro i
      rfl
    · left
      omega
  have how : ∀ a ∈ List.ofFn (orderWire041 data),
      ∀ b ∈ List.ofFn (workspaceWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := orderWire041 data) (g := workspaceWire041 data)
      (b₁ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data))
      (b₂ := workspaceBase041 data)
    · intro i
      rfl
    · intro i
      rfl
    · right
      dsimp [semanticBase041, workspaceBase041]
      omega
  have hgf : ∀ a ∈ List.ofFn (generatorSignalWire041 data),
      ∀ b ∈ List.ofFn (signalWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := generatorSignalWire041 data) (g := signalWire041 data)
      (b₁ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data))
      (b₂ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data) +
        (generatorParameters041 data).generatorSignalWidth)
    · intro i
      rfl
    · intro i
      rfl
    · left
      omega
  have hgw : ∀ a ∈ List.ofFn (generatorSignalWire041 data),
      ∀ b ∈ List.ofFn (workspaceWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := generatorSignalWire041 data) (g := workspaceWire041 data)
      (b₁ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data))
      (b₂ := workspaceBase041 data)
    · intro i
      rfl
    · intro i
      rfl
    · right
      dsimp [semanticBase041, workspaceBase041]
      omega
  have hfw : ∀ a ∈ List.ofFn (signalWire041 data),
      ∀ b ∈ List.ofFn (workspaceWire041 data), a ≠ b := by
    apply offset_blocks_disjoint_ordered041
      (f := signalWire041 data) (g := workspaceWire041 data)
      (b₁ := semanticBase041 data +
        (generatorParameters041 data).generatorDataWidth +
        SpectralSamplingProof.Analytic.historyClockWidth
          (rawTimeSteps036 (referenceData041Base data)) (rawTaylorOrder036 (referenceData041Base data))
          (rawIdlingSteps041 data) + rawOrderWidth036 (referenceData041Base data) +
        (generatorParameters041 data).generatorSignalWidth)
      (b₂ := workspaceBase041 data)
    · intro i
      rfl
    · intro i
      rfl
    · right
      dsimp [semanticBase041, workspaceBase041]
      omega
  have hgf_nodup :
      (List.ofFn (generatorSignalWire041 data) ++
        List.ofFn (signalWire041 data)).Nodup :=
    nodup_append041 hg hf hgf
  have hogf : ∀ a ∈ List.ofFn (orderWire041 data),
      ∀ b ∈ List.ofFn (generatorSignalWire041 data) ++
        List.ofFn (signalWire041 data), a ≠ b :=
    disjoint_append_right041 hog hof
  have hogf_nodup :
      (List.ofFn (orderWire041 data) ++
        (List.ofFn (generatorSignalWire041 data) ++
          List.ofFn (signalWire041 data))).Nodup :=
    nodup_append041 ho hgf_nodup hogf
  have hco_nodup :
      (List.ofFn (clockWire041 data) ++
        (List.ofFn (orderWire041 data) ++
          (List.ofFn (generatorSignalWire041 data) ++
            List.ofFn (signalWire041 data)))).Nodup := by
    apply nodup_append041 hc hogf_nodup
    exact disjoint_append_right041 hco
      (disjoint_append_right041 hcg hcf)
  have hdco_nodup :
      (List.ofFn (dataWire041 data) ++
        (List.ofFn (clockWire041 data) ++
          (List.ofFn (orderWire041 data) ++
            (List.ofFn (generatorSignalWire041 data) ++
              List.ofFn (signalWire041 data))))).Nodup := by
    apply nodup_append041 hd hco_nodup
    exact disjoint_append_right041 hdc
      (disjoint_append_right041 hdo
        (disjoint_append_right041 hdg hdf))
  have hnonworkspace_nodup :
      (List.ofFn (selectorWire041 data) ++
        (List.ofFn (dataWire041 data) ++
          (List.ofFn (clockWire041 data) ++
            (List.ofFn (orderWire041 data) ++
              (List.ofFn (generatorSignalWire041 data) ++
                List.ofFn (signalWire041 data)))))).Nodup := by
    apply nodup_append041 hs hdco_nodup
    exact disjoint_append_right041 hsd
      (disjoint_append_right041 hsc
        (disjoint_append_right041 hso
          (disjoint_append_right041 hsg hsf)))
  have hnonworkspace_w :
      ∀ a ∈ (List.ofFn (selectorWire041 data) ++
        (List.ofFn (dataWire041 data) ++
          (List.ofFn (clockWire041 data) ++
            (List.ofFn (orderWire041 data) ++
              (List.ofFn (generatorSignalWire041 data) ++
                List.ofFn (signalWire041 data)))))) ,
      ∀ b ∈ List.ofFn (workspaceWire041 data), a ≠ b := by
    intro a ha b hb
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · exact hsw a ha b hb
    · rw [List.mem_append] at ha
      rcases ha with ha | ha
      · exact hdw a ha b hb
      · rw [List.mem_append] at ha
        rcases ha with ha | ha
        · exact hcw a ha b hb
        · rw [List.mem_append] at ha
          rcases ha with ha | ha
          · exact how a ha b hb
          · rw [List.mem_append] at ha
            rcases ha with ha | ha
            · exact hgw a ha b hb
            · exact hfw a ha b hb
  simpa [List.append_assoc] using
    (nodup_append041 hnonworkspace_nodup hw hnonworkspace_w)

theorem selectorWire041_injective
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Function.Injective (selectorWire041 data) := by
  intro a b h
  apply Fin.ext
  have hv : (selectorWire041 data a).val =
      (selectorWire041 data b).val := congrArg Fin.val h
  dsimp [selectorWire041] at hv
  omega

theorem dataWire041_injective
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Function.Injective (dataWire041 data) := by
  intro a b h
  apply Fin.ext
  have hv : (dataWire041 data a).val =
      (dataWire041 data b).val := congrArg Fin.val h
  dsimp [dataWire041] at hv
  omega

theorem clockWire041_injective
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Function.Injective (clockWire041 data) := by
  intro a b h
  apply Fin.ext
  have hv : (clockWire041 data a).val =
      (clockWire041 data b).val := congrArg Fin.val h
  dsimp [clockWire041] at hv
  omega

theorem orderWire041_injective
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Function.Injective (orderWire041 data) := by
  intro a b h
  apply Fin.ext
  have hv : (orderWire041 data a).val =
      (orderWire041 data b).val := congrArg Fin.val h
  dsimp [orderWire041] at hv
  omega

theorem generatorSignalWire041_injective
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Function.Injective (generatorSignalWire041 data) := by
  intro a b h
  apply Fin.ext
  have hv : (generatorSignalWire041 data a).val =
      (generatorSignalWire041 data b).val := congrArg Fin.val h
  dsimp [generatorSignalWire041] at hv
  omega

theorem workspaceWire041_injective
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    Function.Injective (workspaceWire041 data) := by
  intro a b h
  apply Fin.ext
  have hv : (workspaceWire041 data a).val =
      (workspaceWire041 data b).val := congrArg Fin.val h
  dsimp [workspaceWire041] at hv
  omega

theorem history041_allWiresNodup_raw
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration)) :
    (List.ofFn (referenceHistoryP15P16Raw041 data).selectorWire ++
      List.ofFn (referenceHistoryP15P16Raw041 data).dataWire ++
      List.ofFn (referenceHistoryP15P16Raw041 data).clockWire ++
      List.ofFn (referenceHistoryP15P16Raw041 data).orderWire ++
      List.ofFn (referenceHistoryP15P16Raw041 data).generatorSignalWire ++
      [(referenceHistoryP15P16Raw041 data).coefficientSignal,
        (referenceHistoryP15P16Raw041 data).orderBoundarySignal,
        (referenceHistoryP15P16Raw041 data).projectorSignal,
        (referenceHistoryP15P16Raw041 data).clockBoundarySignal] ++
      List.ofFn (referenceHistoryP15P16Raw041 data).workspaceWire).Nodup := by
  change (List.ofFn (selectorWire041 data) ++
      List.ofFn (dataWire041 data) ++
      List.ofFn (clockWire041 data) ++
      List.ofFn (orderWire041 data) ++
      List.ofFn (generatorSignalWire041 data) ++
      List.ofFn (signalWire041 data) ++
      List.ofFn (workspaceWire041 data)).Nodup
  exact history041_allWiresNodup data

end
end HistoryPipelineReferenceAdmissibility041
