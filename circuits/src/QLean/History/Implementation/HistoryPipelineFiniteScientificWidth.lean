import QLean.History.Implementation.HistoryPipelineCanonicalHistoryEmbedding

/-! Numerical history-carrier width, extracted from the scientific integer
parameters without evaluating the noncomputable raw angle record. -/

set_option autoImplicit false
set_option warningAsError true

namespace ExecutableHistoryExecutableP18

open ExecutableHistoryExecutableHistory
open ExecutableHistoryHistoryEmbedding
open HistoryPipelineReferenceAdmissibility041
open VerifiedCircuitCore

def finiteScientificHistoryIdleSteps119
    (source : AlignedCommonSource119) : Nat :=
  source.historyBlocks *
    SpectralSamplingProof.Analytic.historyIdleBlockSize
      source.historyParameters.taylorOrder - 1

def finiteScientificHistoryQubits119
    (source : AlignedCommonSource119) : Nat :=
  let p := source.qParameters
  let time := source.historyParameters.physicalClocks
  let order := source.historyParameters.taylorOrder
  let idle := finiteScientificHistoryIdleSteps119 source
  let pool := HistoryRawSchema.rawStructuralPoolWidth203 time order idle
  let workspace := HistoryRawSchema.rawWorkspaceWidth203
    time order idle p.generatorWorkWidth
  p.ancillaWidth + p.systemWidth + 1 + pool + workspace +
    p.generatorDataWidth +
    SpectralSamplingProof.Analytic.historyClockWidth time order idle +
    SpectralSamplingProof.Analytic.historyOrderWidth order +
    p.generatorSignalWidth + 4

theorem finiteScientificHistoryQubits119_eq
    (source : AlignedCommonSource119) :
    finiteScientificHistoryQubits119 source =
      (ExecutableRaw119 source).history.qubits := by
  simp only [finiteScientificHistoryQubits119,
    finiteScientificHistoryIdleSteps119,
    ExecutableRaw119, executableRawInput119, executableHistoryRaw119,
    referenceHistoryP15P16Raw041, qubits041, semanticBase041,
    workspaceBase041, workspaceWidth041, structuralPool041,
    rawIdlingSteps041, rawHistoryBlocks041, generatorParameters041,
    referenceData119, referenceData041Base,
    HistoryPipelineReferenceRawValueConstructor.rawTimeSteps036,
    HistoryPipelineReferenceRawValueConstructor.rawTaylorOrder036,
    HistoryPipelineReferenceRawValueConstructor.rawOrderWidth036]
  omega

def finiteScientificHistoryDataBase119
    (source : AlignedCommonSource119) : Nat :=
  let time := source.historyParameters.physicalClocks
  let order := source.historyParameters.taylorOrder
  let idle := finiteScientificHistoryIdleSteps119 source
  HistoryRawSchema.rawStructuralPoolWidth203 time order idle +
    HistoryRawSchema.rawWorkspaceWidth203 time order idle
      source.qParameters.generatorWorkWidth

def finiteScientificHistoryClockWidth119
    (source : AlignedCommonSource119) : Nat :=
  SpectralSamplingProof.Analytic.historyClockWidth
    source.historyParameters.physicalClocks
    source.historyParameters.taylorOrder
    (finiteScientificHistoryIdleSteps119 source)

def finiteScientificHistoryOrderWidth119
    (source : AlignedCommonSource119) : Nat :=
  SpectralSamplingProof.Analytic.historyOrderWidth
    source.historyParameters.taylorOrder

def finiteScientificHistoryDataWire119
    (source : AlignedCommonSource119)
    (bit : Fin source.qParameters.generatorDataWidth) :
    Fin (finiteScientificHistoryQubits119 source) :=
  ⟨finiteScientificHistoryDataBase119 source + bit.val, by
    dsimp [finiteScientificHistoryDataBase119,
      finiteScientificHistoryQubits119]
    omega⟩

theorem finiteScientificHistoryDataWire119_injective
    (source : AlignedCommonSource119) :
    Function.Injective (finiteScientificHistoryDataWire119 source) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  dsimp [finiteScientificHistoryDataWire119] at values
  omega

def finiteScientificHistoryDataRegister119
    (source : AlignedCommonSource119) :
    Register (finiteScientificHistoryQubits119 source)
      source.qParameters.generatorDataWidth where
  wire := finiteScientificHistoryDataWire119 source
  injective := finiteScientificHistoryDataWire119_injective source

def finiteScientificHistoryClockWire119
    (source : AlignedCommonSource119)
    (bit : Fin (finiteScientificHistoryClockWidth119 source)) :
    Fin (finiteScientificHistoryQubits119 source) :=
  ⟨finiteScientificHistoryDataBase119 source +
    source.qParameters.generatorDataWidth + bit.val, by
    dsimp [finiteScientificHistoryDataBase119,
      finiteScientificHistoryQubits119,
      finiteScientificHistoryClockWidth119]
    omega⟩

def finiteScientificHistoryOrderWire119
    (source : AlignedCommonSource119)
    (bit : Fin (finiteScientificHistoryOrderWidth119 source)) :
    Fin (finiteScientificHistoryQubits119 source) :=
  ⟨finiteScientificHistoryDataBase119 source +
    source.qParameters.generatorDataWidth +
    finiteScientificHistoryClockWidth119 source + bit.val, by
    dsimp [finiteScientificHistoryDataBase119,
      finiteScientificHistoryQubits119,
      finiteScientificHistoryClockWidth119,
      finiteScientificHistoryOrderWidth119]
    omega⟩

theorem finiteScientificHistoryClockWire119_injective
    (source : AlignedCommonSource119) :
    Function.Injective (finiteScientificHistoryClockWire119 source) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  dsimp [finiteScientificHistoryClockWire119] at values
  omega

theorem finiteScientificHistoryOrderWire119_injective
    (source : AlignedCommonSource119) :
    Function.Injective (finiteScientificHistoryOrderWire119 source) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  dsimp [finiteScientificHistoryOrderWire119] at values
  omega

def finiteScientificHistoryClockRegister119
    (source : AlignedCommonSource119) :
    Register (finiteScientificHistoryQubits119 source)
      (finiteScientificHistoryClockWidth119 source) where
  wire := finiteScientificHistoryClockWire119 source
  injective := finiteScientificHistoryClockWire119_injective source

def finiteScientificHistoryOrderRegister119
    (source : AlignedCommonSource119) :
    Register (finiteScientificHistoryQubits119 source)
      (finiteScientificHistoryOrderWidth119 source) where
  wire := finiteScientificHistoryOrderWire119 source
  injective := finiteScientificHistoryOrderWire119_injective source

theorem finiteScientificHistoryDataWire119_scientific_val
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (bit : Fin source.qParameters.generatorDataWidth) :
    (finiteScientificHistoryDataWire119 source bit).val =
      ((ExecutableLayout119 source domain).data.wire
        (Fin.cast (executableHistory_dataWidth119 source).symm bit)).val := by
  change (finiteScientificHistoryDataWire119 source bit).val =
    (dataWire041 (referenceData119 source)
      (Fin.cast (executableHistory_dataWidth119 source).symm bit)).val
  simp [finiteScientificHistoryDataWire119,
    finiteScientificHistoryDataBase119,
    finiteScientificHistoryIdleSteps119, dataWire041,
    semanticBase041, workspaceBase041, structuralPool041,
    workspaceWidth041, rawIdlingSteps041, rawHistoryBlocks041,
    generatorParameters041, referenceData119, referenceData041Base,
    HistoryPipelineReferenceRawValueConstructor.rawTimeSteps036,
    HistoryPipelineReferenceRawValueConstructor.rawTaylorOrder036]

theorem finiteScientificHistoryDataWire119_scientific_eq
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (bit : Fin source.qParameters.generatorDataWidth) :
    Fin.cast (finiteScientificHistoryQubits119_eq source)
        (finiteScientificHistoryDataWire119 source bit) =
      (ExecutableLayout119 source domain).data.wire
        (Fin.cast (executableHistory_dataWidth119 source).symm bit) := by
  apply Fin.ext
  exact finiteScientificHistoryDataWire119_scientific_val source domain bit

theorem finiteScientificHistoryClockWire119_scientific_val
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (bit : Fin (finiteScientificHistoryClockWidth119 source)) :
    (finiteScientificHistoryClockWire119 source bit).val =
      ((ExecutableLayout119 source domain).clock.wire bit).val := by
  change (finiteScientificHistoryClockWire119 source bit).val =
    (clockWire041 (referenceData119 source) bit).val
  simp [finiteScientificHistoryClockWire119,
    finiteScientificHistoryDataBase119,
    finiteScientificHistoryIdleSteps119, clockWire041,
    semanticBase041, workspaceBase041, structuralPool041,
    workspaceWidth041, rawIdlingSteps041, rawHistoryBlocks041,
    generatorParameters041, referenceData119, referenceData041Base,
    HistoryPipelineReferenceRawValueConstructor.rawTimeSteps036,
    HistoryPipelineReferenceRawValueConstructor.rawTaylorOrder036]

theorem finiteScientificHistoryOrderWire119_scientific_val
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (bit : Fin (finiteScientificHistoryOrderWidth119 source)) :
    (finiteScientificHistoryOrderWire119 source bit).val =
      ((ExecutableLayout119 source domain).order.wire bit).val := by
  change (finiteScientificHistoryOrderWire119 source bit).val =
    (orderWire041 (referenceData119 source) bit).val
  simp [finiteScientificHistoryOrderWire119,
    finiteScientificHistoryDataBase119,
    finiteScientificHistoryClockWidth119,
    finiteScientificHistoryIdleSteps119, orderWire041,
    semanticBase041, workspaceBase041, structuralPool041,
    workspaceWidth041, rawIdlingSteps041, rawHistoryBlocks041,
    generatorParameters041, referenceData119, referenceData041Base,
    HistoryPipelineReferenceRawValueConstructor.rawTimeSteps036,
    HistoryPipelineReferenceRawValueConstructor.rawTaylorOrder036,
    HistoryPipelineReferenceRawValueConstructor.rawOrderWidth036]

theorem finiteScientificHistoryClockWire119_scientific_eq
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (bit : Fin (finiteScientificHistoryClockWidth119 source)) :
    Fin.cast (finiteScientificHistoryQubits119_eq source)
        (finiteScientificHistoryClockWire119 source bit) =
      (ExecutableLayout119 source domain).clock.wire bit := by
  apply Fin.ext
  exact finiteScientificHistoryClockWire119_scientific_val source domain bit

theorem finiteScientificHistoryOrderWire119_scientific_eq
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (bit : Fin (finiteScientificHistoryOrderWidth119 source)) :
    Fin.cast (finiteScientificHistoryQubits119_eq source)
        (finiteScientificHistoryOrderWire119 source bit) =
      (ExecutableLayout119 source domain).order.wire bit := by
  apply Fin.ext
  exact finiteScientificHistoryOrderWire119_scientific_val source domain bit

/-- The data/clock/order history word can be computed without constructing
the raw real-angle record or the proof-bearing corrected component. -/
def finiteScientificCanonicalHistoryBasis119
    (source : AlignedCommonSource119)
    (fits : HistoryIndexFitsLayout119 source)
    (index : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    QubitBasis (finiteScientificHistoryQubits119 source) :=
  let oldIndex := canonicalOldHistoryIndex119 source index
  finiteHistoryBasisAtRegisters
    (finiteScientificHistoryDataRegister119 source)
    (finiteScientificHistoryClockRegister119 source)
    (finiteScientificHistoryOrderRegister119 source)
    (fun bit => ProbabilityGeneratorQProof.delimiterEncoding
      oldIndex.state.configuration bit)
    (clockBits119 source fits oldIndex)
    (orderBits119 source fits oldIndex)

private theorem finiteScientificDataBits119_eq
    (source : AlignedCommonSource119)
    (configuration : ProbabilityGeneratorQProof.QConfiguration
      source.qParameters)
    (bit : Fin (ExecutableRaw119 source).history.dataWidth) :
    ProbabilityGeneratorQProof.delimiterEncoding configuration
        (Fin.cast (executableHistory_dataWidth119 source) bit) =
      dataBits119 source configuration bit := by
  rfl

/-- The computed history word is the established scientific word after the
proved change of qubit-width representation. -/
theorem finiteScientificCanonicalHistoryBasis119_scientific_eq
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source)
    (index : JenningsHistory.HistoryIndex
      (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source))
    (wire : Fin (ExecutableRaw119 source).history.qubits) :
    finiteScientificCanonicalHistoryBasis119 source fits index
        (Fin.cast (finiteScientificHistoryQubits119_eq source).symm wire) =
      canonicalHistoryPhysicalBasis119 source domain fits index wire := by
  unfold finiteScientificCanonicalHistoryBasis119
    canonicalHistoryPhysicalBasis119 finiteHistoryBasisAtRegisters
  exact writeRegisterBitsFinite_transport
    (finiteScientificHistoryQubits119_eq source)
    (executableHistory_dataWidth119 source).symm
    (finiteScientificHistoryDataRegister119 source)
    (ExecutableLayout119 source domain).data
    (finiteScientificHistoryDataWire119_scientific_eq source domain)
    _ _
    (by intro bit
        exact finiteScientificDataBits119_eq source
          (canonicalOldHistoryIndex119 source index).state.configuration bit)
    _ _
    (by intro nextWire
        exact writeRegisterBitsFinite_transport
          (finiteScientificHistoryQubits119_eq source) rfl
          (finiteScientificHistoryClockRegister119 source)
          (ExecutableLayout119 source domain).clock
          (finiteScientificHistoryClockWire119_scientific_eq source domain)
          _ _ (by intro bit; rfl) _ _
          (by intro lastWire
              exact writeRegisterBitsFinite_transport
                (finiteScientificHistoryQubits119_eq source) rfl
                (finiteScientificHistoryOrderRegister119 source)
                (ExecutableLayout119 source domain).order
                (finiteScientificHistoryOrderWire119_scientific_eq source domain)
                _ _ (by intro bit; rfl) _ _ (by intro bit; rfl) lastWire)
          nextWire)
    wire

end ExecutableHistoryExecutableP18
