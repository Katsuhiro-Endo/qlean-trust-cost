import QLean.History.Implementation.HistoryPipelineFiniteScientificWidth

set_option autoImplicit false
set_option warningAsError true

/-!
Finite, parameter-derived history-wire coordinates. The existing data,
clock and order coordinates live in `HistoryPipelineFiniteScientificWidth`;
this module supplies the remaining selector, workspace, generator-signal
and four distinguished signal wires. It does not evaluate analytic angles.
-/

namespace ExecutableHistoryExecutableP18

open ExecutableHistoryExecutableHistory
open HistoryPipelineReferenceAdmissibility041
open SpectralSamplingProof.Analytic
open VerifiedCircuitCore

def finiteScientificHistoryStructuralPool119
    (source : AlignedCommonSource119) : Nat :=
  HistoryRawSchema.rawStructuralPoolWidth203
    source.historyParameters.physicalClocks
    source.historyParameters.taylorOrder
    (finiteScientificHistoryIdleSteps119 source)

def finiteScientificHistoryWorkspaceWidth119
    (source : AlignedCommonSource119) : Nat :=
  HistoryRawSchema.rawWorkspaceWidth203
    source.historyParameters.physicalClocks
    source.historyParameters.taylorOrder
    (finiteScientificHistoryIdleSteps119 source)
    source.qParameters.generatorWorkWidth

def finiteScientificHistorySignalBase119
    (source : AlignedCommonSource119) : Nat :=
  finiteScientificHistoryDataBase119 source +
    source.qParameters.generatorDataWidth +
    finiteScientificHistoryClockWidth119 source +
    finiteScientificHistoryOrderWidth119 source

def finiteScientificHistorySelectorWire119
    (source : AlignedCommonSource119) (bit : Fin 2) :
    Fin (finiteScientificHistoryQubits119 source) :=
  ⟨bit.val, by
    dsimp [finiteScientificHistoryQubits119,
      finiteScientificHistoryIdleSteps119]
    omega⟩

def finiteScientificHistoryWorkspaceWire119
    (source : AlignedCommonSource119)
    (bit : Fin (finiteScientificHistoryWorkspaceWidth119 source)) :
    Fin (finiteScientificHistoryQubits119 source) :=
  ⟨finiteScientificHistoryStructuralPool119 source + bit.val, by
    dsimp [finiteScientificHistoryStructuralPool119,
      finiteScientificHistoryWorkspaceWidth119,
      finiteScientificHistoryQubits119,
      finiteScientificHistoryIdleSteps119]
    omega⟩

def finiteScientificHistoryGeneratorSignalWire119
    (source : AlignedCommonSource119)
    (bit : Fin source.qParameters.generatorSignalWidth) :
    Fin (finiteScientificHistoryQubits119 source) :=
  ⟨finiteScientificHistorySignalBase119 source + bit.val, by
    dsimp [finiteScientificHistorySignalBase119,
      finiteScientificHistoryDataBase119,
      finiteScientificHistoryQubits119,
      finiteScientificHistoryClockWidth119,
      finiteScientificHistoryOrderWidth119,
      finiteScientificHistoryIdleSteps119]
    omega⟩

def finiteScientificHistoryDistinguishedSignalWire119
    (source : AlignedCommonSource119) (slot : Fin 4) :
    Fin (finiteScientificHistoryQubits119 source) :=
  ⟨finiteScientificHistorySignalBase119 source +
    source.qParameters.generatorSignalWidth + slot.val, by
    dsimp [finiteScientificHistorySignalBase119,
      finiteScientificHistoryDataBase119,
      finiteScientificHistoryQubits119,
      finiteScientificHistoryClockWidth119,
      finiteScientificHistoryOrderWidth119,
      finiteScientificHistoryIdleSteps119]
    omega⟩

theorem finiteScientificHistorySelectorWire119_injective
    (source : AlignedCommonSource119) :
    Function.Injective (finiteScientificHistorySelectorWire119 source) := by
  intro left right equal
  apply Fin.ext
  simpa [finiteScientificHistorySelectorWire119] using congrArg Fin.val equal

theorem finiteScientificHistoryWorkspaceWire119_injective
    (source : AlignedCommonSource119) :
    Function.Injective (finiteScientificHistoryWorkspaceWire119 source) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  dsimp [finiteScientificHistoryWorkspaceWire119] at values
  omega

theorem finiteScientificHistoryGeneratorSignalWire119_injective
    (source : AlignedCommonSource119) :
    Function.Injective
      (finiteScientificHistoryGeneratorSignalWire119 source) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  dsimp [finiteScientificHistoryGeneratorSignalWire119] at values
  omega

theorem finiteScientificHistorySelectorWire119_scientific_val
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) (bit : Fin 2) :
    (finiteScientificHistorySelectorWire119 source bit).val =
      ((ExecutableLayout119 source domain).selector.wire bit).val := by
  change (finiteScientificHistorySelectorWire119 source bit).val =
    (selectorWire041 (referenceData119 source) bit).val
  rfl

theorem finiteScientificHistoryWorkspaceWire119_scientific_val
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (bit : Fin (finiteScientificHistoryWorkspaceWidth119 source)) :
    (finiteScientificHistoryWorkspaceWire119 source bit).val =
      ((ExecutableLayout119 source domain).workspace.wire bit).val := by
  change (finiteScientificHistoryWorkspaceWire119 source bit).val =
    (workspaceWire041 (referenceData119 source) bit).val
  simp [finiteScientificHistoryWorkspaceWire119,
    finiteScientificHistoryStructuralPool119,
    finiteScientificHistoryIdleSteps119, workspaceWire041,
    workspaceBase041, structuralPool041, rawIdlingSteps041,
    rawHistoryBlocks041, referenceData119, referenceData041Base,
    HistoryPipelineReferenceRawValueConstructor.rawTimeSteps036,
    HistoryPipelineReferenceRawValueConstructor.rawTaylorOrder036]

theorem finiteScientificHistoryGeneratorSignalWire119_scientific_val
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (bit : Fin source.qParameters.generatorSignalWidth) :
    (finiteScientificHistoryGeneratorSignalWire119 source bit).val =
      ((ExecutableLayout119 source domain).generatorSignal.wire bit).val := by
  change (finiteScientificHistoryGeneratorSignalWire119 source bit).val =
    (generatorSignalWire041 (referenceData119 source) bit).val
  simp [finiteScientificHistoryGeneratorSignalWire119,
    finiteScientificHistorySignalBase119,
    finiteScientificHistoryDataBase119,
    finiteScientificHistoryClockWidth119,
    finiteScientificHistoryOrderWidth119,
    finiteScientificHistoryIdleSteps119, generatorSignalWire041,
    semanticBase041, workspaceBase041, structuralPool041,
    workspaceWidth041, rawIdlingSteps041, rawHistoryBlocks041,
    generatorParameters041, referenceData119, referenceData041Base,
    HistoryPipelineReferenceRawValueConstructor.rawTimeSteps036,
    HistoryPipelineReferenceRawValueConstructor.rawTaylorOrder036,
    HistoryPipelineReferenceRawValueConstructor.rawOrderWidth036]

/-- Slot 0/1/2/3 is respectively the coefficient, order-boundary,
projector and clock-boundary signal of the certified layout. -/
theorem finiteScientificHistoryDistinguishedSignalWire119_scientific_val
    (source : AlignedCommonSource119) (slot : Fin 4) :
    (finiteScientificHistoryDistinguishedSignalWire119 source slot).val =
      (signalWire041 (referenceData119 source) slot).val := by
  simp [finiteScientificHistoryDistinguishedSignalWire119,
    finiteScientificHistorySignalBase119,
    finiteScientificHistoryDataBase119,
    finiteScientificHistoryClockWidth119,
    finiteScientificHistoryOrderWidth119,
    finiteScientificHistoryIdleSteps119, signalWire041,
    semanticBase041, workspaceBase041, structuralPool041,
    workspaceWidth041, rawIdlingSteps041, rawHistoryBlocks041,
    generatorParameters041, referenceData119, referenceData041Base,
    HistoryPipelineReferenceRawValueConstructor.rawTimeSteps036,
    HistoryPipelineReferenceRawValueConstructor.rawTaylorOrder036,
    HistoryPipelineReferenceRawValueConstructor.rawOrderWidth036]

end ExecutableHistoryExecutableP18
