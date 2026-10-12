import QLean.History.Implementation.HistoryPipelineReferenceAdmissibility
import QLean.History.Implementation.HistoryPipelineExecutableSelectorAngles
import QLean.History.Implementation.HistoryPipelineExecutableGenerator

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace ExecutableHistoryExecutableHistory

open Matrix
open HistoryBlockEncoding
open VerifiedCircuitCore
open ProbabilityGeneratorQProof
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open HistoryPipelineReferenceRawCompiler
open HistoryPipelineReferenceRawValueConstructor
open HistoryPipelineReferenceRawValueConstructorV2
open HistoryPipelineReferenceRawValueConstructorV3
open HistoryPipelineReferenceAdmissibility041

noncomputable section

/-- One source for the history and generator, with their scientific
parameters kept independent.  Register compatibility is established by the
explicit synchronized layout below, not by identifying unrelated numbers. -/
structure AlignedCommonSource119 extends CommonSource119 where
  independentParameterLayout : Unit := ()

def omegaRat119 (source : AlignedCommonSource119) : ℚ :=
  (3 * (source.qParameters.K : ℚ)) * source.historyParameters.stepSize

theorem omegaRat119_cast (source : AlignedCommonSource119) :
    (omegaRat119 source : ℝ) = omegaH119 source.toCommonSource119 := by
  simp [omegaRat119, omegaH119, generatorAlpha119]

def referenceData119 (source : AlignedCommonSource119) :
    ReferenceData041 (Configuration := QConfiguration source.qParameters) :=
  { parameters := source.historyParameters
    modelQ := commonModelQ119 source.toCommonSource119
    initial := source.initial
    omegaH := omegaH119 source.toCommonSource119
    nu := source.targetStateError
    qParameters := source.qParameters
    historyBlocks := source.historyBlocks
    historyBlocksPositive := source.historyBlocksPositive }

theorem qParameters_eq119 (left right : QParameters)
    (q_eq : left.q = right.q) (K_eq : left.K = right.K) : left = right := by
  cases left
  cases right
  simp_all

theorem generatorParameters119_eq (source : AlignedCommonSource119) :
    generatorParameters041 (referenceData119 source) = source.qParameters := by
  rfl

def selectorScientific119 (source : AlignedCommonSource119) :
    Fin 3 → ScientificAngleExpr := fun index =>
  if index.val = 0 then
    selectorHighScientific119 source.historyParameters.taylorOrder
      (omegaRat119 source)
  else
    selectorLowScientific119 (omegaRat119 source)

def selectorRaw119 (source : AlignedCommonSource119) :
    Fin 3 → VerifiedCircuitCore.AngleExpr := fun index =>
  CanonicalHistoryAdapter.compileScientificAngle (selectorScientific119 source index)

def executableHistoryRaw119 (source : AlignedCommonSource119) :
    HistoryRawSchema.HistoryP15P16Raw203 :=
  let data := referenceData119 source
  let old := referenceHistoryP15P16Raw041 data
  { old with
    targetStateError := source.targetStateError
    stepSize := (source.historyParameters.stepSize : ℝ)
    omegaH := omegaH119 source.toCommonSource119
    historyBlockScale := selectorAlpha119
      source.historyParameters.taylorOrder
      (omegaH119 source.toCommonSource119)
    gTaylor := generatorAlpha119 source.qParameters
    analyticQ := generatorAlpha119 source.qParameters
    analyticH := (source.historyParameters.stepSize : ℝ)
    analyticTolerance := source.targetStateError
    analyticSelectorAngles := fun index =>
      (selectorRaw119 source index).uniformValue
    analyticCoefficientAngles := fun index =>
      (compiledTaylorCoefficientAngle119 index).uniformValue
    analyticIdleAngle := compiledIdleCoefficientAngle119.uniformValue
    selectorPreparationAngles := selectorScientific119 source
    coefficientAngles := fun index => taylorCoefficientAngle119 index.val
    idleCoefficientAngle := idleCoefficientAngle119
    rawCoefficientAngles := fun index =>
      compiledTaylorCoefficientAngle119 index.val
    rawIdleCoefficientAngle := compiledIdleCoefficientAngle119
    selectorHighAngle := selectorRaw119 source ⟨0, by decide⟩
    selectorLowAngle := selectorRaw119 source ⟨1, by decide⟩
    selectorSecondLowAngle := selectorRaw119 source ⟨2, by decide⟩ }

/-- The Taylor order of the executable history record comes only from the
history specification; it is not identified with the grid width. -/
@[simp] theorem executableHistoryRaw119_taylorOrder
    (source : AlignedCommonSource119) :
    (executableHistoryRaw119 source).taylorOrder =
      source.historyParameters.taylorOrder := by
  rfl

/-- The stored history-block field is the terminal idle-clock block count.
It is independent of both the particle cap and the binary order-register
size. -/
@[simp] theorem executableHistoryRaw119_historyBlocks
    (source : AlignedCommonSource119) :
    (executableHistoryRaw119 source).historyBlocks = source.historyBlocks := by
  rfl

theorem selectorRaw119_high_value (source : AlignedCommonSource119) :
    (selectorRaw119 source ⟨0, by decide⟩).uniformValue =
      selectorHighAngle119 source.historyParameters.taylorOrder
        (omegaH119 source.toCommonSource119) := by
  rw [← omegaRat119_cast source]
  simpa [selectorRaw119, selectorScientific119] using
    compile_selectorHighScientific119_value
      source.historyParameters.taylorOrder (omegaRat119 source)

theorem selectorRaw119_low_value (source : AlignedCommonSource119)
    (index : Fin 3) (nonzero : index.val ≠ 0) :
    (selectorRaw119 source index).uniformValue =
      selectorLowAngle119 (omegaH119 source.toCommonSource119) := by
  rw [← omegaRat119_cast source]
  simpa [selectorRaw119, selectorScientific119, nonzero] using
    compile_selectorLowScientific119_value (omegaRat119 source)

structure ExecutableHistoryDomain119 (source : AlignedCommonSource119) where
  analyticDomain :
    HistoryAnalyticParameterExistence194.HistoryAnalyticBaseDomain194
    (HistoryRawSchema.analyticBase203 (executableHistoryRaw119 source))

theorem workspaceWire041_eq_iff119
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration))
    (left right : Fin (workspaceWidth041 data)) :
    workspaceWire041 data left = workspaceWire041 data right ↔ left = right :=
  (workspaceWire041_injective data).eq_iff

theorem workspaceWire041_ne_iff119
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration))
    (left right : Fin (workspaceWidth041 data)) :
    workspaceWire041 data left ≠ workspaceWire041 data right ↔ left ≠ right :=
  not_congr (workspaceWire041_eq_iff119 data left right)

theorem workspaceWire041_ne_of_val_ne119
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration))
    (left right : Fin (workspaceWidth041 data))
    (different : left.val ≠ right.val) :
    workspaceWire041 data left ≠ workspaceWire041 data right := by
  intro h
  apply different
  exact congrArg Fin.val ((workspaceWire041_injective data) h)

theorem signalWire041_ne_workspace119
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration))
    (signal : Fin 4) (work : Fin (workspaceWidth041 data)) :
    signalWire041 data signal ≠ workspaceWire041 data work := by
  intro h
  have hv := congrArg Fin.val h
  simp [signalWire041, workspaceWire041, semanticBase041] at hv
  omega

theorem clockWire041_ne_workspace119
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration))
    (clock : Fin (historyClockWidth (rawTimeSteps036 (referenceData041Base data))
      (rawTaylorOrder036 (referenceData041Base data)) (rawIdlingSteps041 data)))
    (work : Fin (workspaceWidth041 data)) :
    clockWire041 data clock ≠ workspaceWire041 data work := by
  intro h
  have hv := congrArg Fin.val h
  simp [clockWire041, workspaceWire041, semanticBase041] at hv
  omega

theorem orderWire041_ne_workspace119
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData041 (Configuration := Configuration))
    (order : Fin (rawOrderWidth036 (referenceData041Base data)))
    (work : Fin (workspaceWidth041 data)) :
    orderWire041 data order ≠ workspaceWire041 data work := by
  intro h
  have hv := congrArg Fin.val h
  simp [orderWire041, workspaceWire041, semanticBase041] at hv
  omega

theorem executableHistoryRaw119_admissible
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source) :
    HistoryRawSchema.HistoryP15P16Admissible203
      (executableHistoryRaw119 source) := by
  let data := referenceData119 source
  have blocksPositive : 0 < rawHistoryBlocks041 data := by
    simpa [data, referenceData119, rawHistoryBlocks041] using
      source.historyBlocksPositive
  have idleSizePositive :
      0 < historyIdleBlockSize (rawTaylorOrder036 (referenceData041Base data)) := by
    unfold historyIdleBlockSize historyOrderWidth
    positivity
  have idleProductPositive :
      0 < rawHistoryBlocks041 data *
        historyIdleBlockSize (rawTaylorOrder036 (referenceData041Base data)) :=
    Nat.mul_pos blocksPositive idleSizePositive
  refine {
    timeStepsPositive := ?_
    taylorOrderPositive := ?_
    idlingFitsBinaryBlocks := ?_
    targetStateErrorPositive := ?_
    stepSizePositive := ?_
    omegaHNonnegative := ?_
    analyticDomain := domain.analyticDomain
    analyticTolerancePositive := ?_
    selectorInjective := ?_
    dataInjective := ?_
    clockInjective := ?_
    orderInjective := ?_
    generatorSignalInjective := ?_
    workspaceInjective := ?_
    allWiresNodup := ?_
    clockTimeLessThan := ?_
    clockIdleEndLessThan := ?_
    degreeOrderLessThan := ?_
    degreeIncrement := ?_
    clockIncrement := ?_
    uniformActiveNeOrder := ?_
    uniformWork₀NeActive := ?_
    uniformWork₁NeActive := ?_
    uniformWork₀NeOrder := ?_
    uniformWork₁NeOrder := ?_
    projectorBranchNeProjector := ?_
    projectorCoefficientControlNeProjector := ?_
    branchNeIdleEnd := ?_
    branchNeCoefficientSignal := ?_
    lessThanIdleEndNeCoefficientSignal := ?_
    activeNeEquality := ?_
    activeNeOrderBoundary := ?_
    equalityNeOrderBoundary := ?_
    lessThanIdleNeIdle := ?_
    lessThanTimeNeIdle := ?_
    activeNeCoefficientSignal := ?_
    coefficientControlNeCoefficientSignal := ?_ }
  · change 0 < source.historyParameters.physicalClocks
    exact source.historyWellFormed.1
  · change 0 < source.historyParameters.taylorOrder
    exact source.historyWellFormed.2.1
  · have productOne : 1 ≤ rawHistoryBlocks041 data *
        historyIdleBlockSize (rawTaylorOrder036 (referenceData041Base data)) := by omega
    change (rawIdlingSteps041 data + 1) %
      historyIdleBlockSize (rawTaylorOrder036 (referenceData041Base data)) = 0
    change (rawHistoryBlocks041 data *
        historyIdleBlockSize (rawTaylorOrder036 (referenceData041Base data)) - 1 + 1) %
      historyIdleBlockSize (rawTaylorOrder036 (referenceData041Base data)) = 0
    rw [Nat.sub_add_cancel productOne]
    simp
  · simpa [executableHistoryRaw119] using source.targetStateErrorPositive
  · simpa [executableHistoryRaw119] using source.stepPositive
  · exact le_of_lt (omegaH119_positive source.toCommonSource119)
  · simpa [executableHistoryRaw119] using source.targetStateErrorPositive
  · change Function.Injective (selectorWire041 data)
    exact selectorWire041_injective data
  · change Function.Injective (dataWire041 data)
    exact dataWire041_injective data
  · change Function.Injective (clockWire041 data)
    exact clockWire041_injective data
  · change Function.Injective (orderWire041 data)
    exact orderWire041_injective data
  · change Function.Injective (generatorSignalWire041 data)
    exact generatorSignalWire041_injective data
  · change Function.Injective (workspaceWire041 data)
    exact workspaceWire041_injective data
  · change
      (List.ofFn (referenceHistoryP15P16Raw041 data).selectorWire ++
        List.ofFn (referenceHistoryP15P16Raw041 data).dataWire ++
        List.ofFn (referenceHistoryP15P16Raw041 data).clockWire ++
        List.ofFn (referenceHistoryP15P16Raw041 data).orderWire ++
        List.ofFn (referenceHistoryP15P16Raw041 data).generatorSignalWire ++
        [(referenceHistoryP15P16Raw041 data).coefficientSignal,
          (referenceHistoryP15P16Raw041 data).orderBoundarySignal,
          (referenceHistoryP15P16Raw041 data).projectorSignal,
          (referenceHistoryP15P16Raw041 data).clockBoundarySignal] ++
        List.ofFn (referenceHistoryP15P16Raw041 data).workspaceWire).Nodup
    exact history041_allWiresNodup_raw data
  · constructor
    · simp [executableHistoryRaw119, data, referenceData119, historyClockWidth]
    · intro left right
      change clockWire041 data left ≠ workspaceWire041 data _
      exact clockWire041_ne_workspace119 data left _
    · intro left right
      change clockWire041 data left ≠ workspaceWire041 data _
      exact clockWire041_ne_workspace119 data left _
    · intro left right
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawBoundWire203, HistoryRawSchema.rawBorrowWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
    · intro index
      change workspaceWire041 data _ ≠ clockWire041 data index
      exact (clockWire041_ne_workspace119 data index _).symm
    · intro index
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      rw [workspaceWire041_ne_iff119]
      intro h
      have hv := congrArg Fin.val h
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth,
        HistoryRawSchema.rawLessThanTimeWire203, HistoryRawSchema.rawBoundWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
    · intro index
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth,
        HistoryRawSchema.rawLessThanTimeWire203, HistoryRawSchema.rawBorrowWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
  · constructor
    · simp [executableHistoryRaw119, data, referenceData119, historyClockWidth]
    · intro left right
      change clockWire041 data left ≠ workspaceWire041 data _
      exact clockWire041_ne_workspace119 data left _
    · intro left right
      change clockWire041 data left ≠ workspaceWire041 data _
      exact clockWire041_ne_workspace119 data left _
    · intro left right
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth,
        HistoryRawSchema.rawBoundWire203, HistoryRawSchema.rawBorrowWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
    · intro index
      change workspaceWire041 data _ ≠ clockWire041 data index
      exact (clockWire041_ne_workspace119 data index _).symm
    · intro index
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth,
        HistoryRawSchema.rawLessThanIdleEndWire203, HistoryRawSchema.rawBoundWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
    · intro index
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth,
        HistoryRawSchema.rawLessThanIdleEndWire203, HistoryRawSchema.rawBorrowWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
  · constructor
    · simp [executableHistoryRaw119, data, referenceData119, historyOrderWidth]
    · intro left right
      change orderWire041 data left ≠ workspaceWire041 data _
      exact orderWire041_ne_workspace119 data left _
    · intro left right
      change orderWire041 data left ≠ workspaceWire041 data _
      exact orderWire041_ne_workspace119 data left _
    · intro left right
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth, historyOrderWidth,
        HistoryRawSchema.rawOrderBoundWire203, HistoryRawSchema.rawOrderMaskedWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
    · intro index
      change workspaceWire041 data _ ≠ orderWire041 data index
      exact (orderWire041_ne_workspace119 data index _).symm
    · intro index
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth, historyOrderWidth,
        HistoryRawSchema.rawEqualityFlag203, HistoryRawSchema.rawOrderBoundWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
    · intro index
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth, historyOrderWidth,
        HistoryRawSchema.rawEqualityFlag203, HistoryRawSchema.rawOrderMaskedWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
  · constructor
    · intro left right
      change workspaceWire041 data _ ≠ orderWire041 data right
      exact (orderWire041_ne_workspace119 data right _).symm
    · intro index
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth, historyOrderWidth,
        HistoryRawSchema.rawOrderCarry203, HistoryRawSchema.rawOrderMaskedWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
    · intro index
      change workspaceWire041 data _ ≠ orderWire041 data index
      exact (orderWire041_ne_workspace119 data index _).symm
    · intro index
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, HistoryRawSchema.rawOrderTailWidth203,
        historyClockWidth, historyOrderWidth,
        HistoryRawSchema.rawActiveWire203, HistoryRawSchema.rawOrderMaskedWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
    · intro index
      change workspaceWire041 data _ ≠ orderWire041 data index
      exact (orderWire041_ne_workspace119 data index _).symm
    · change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth, historyOrderWidth,
        HistoryRawSchema.rawActiveWire203, HistoryRawSchema.rawOrderCarry203,
        HistoryRawSchema.rawSlice203] at hv
      omega
  · constructor
    · intro left right
      change workspaceWire041 data _ ≠ clockWire041 data right
      exact (clockWire041_ne_workspace119 data right _).symm
    · intro index
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth, historyOrderWidth,
        HistoryRawSchema.rawClockCarry203, HistoryRawSchema.rawOrderCarry203,
        HistoryRawSchema.rawClockMaskedWire203, HistoryRawSchema.rawSlice203] at hv
      omega
    · intro index
      change workspaceWire041 data _ ≠ clockWire041 data index
      exact (clockWire041_ne_workspace119 data index _).symm
    · intro index
      change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, HistoryRawSchema.rawClockTailWidth203,
        historyClockWidth, historyOrderWidth,
        HistoryRawSchema.rawBranchWire203, HistoryRawSchema.rawClockMaskedWire203,
        HistoryRawSchema.rawSlice203] at hv
      omega
    · intro index
      change workspaceWire041 data _ ≠ clockWire041 data index
      exact (clockWire041_ne_workspace119 data index _).symm
    · change workspaceWire041 data _ ≠ workspaceWire041 data _
      intro h
      have hi := (workspaceWire041_injective data) h
      have hv := congrArg Fin.val hi
      dsimp [executableHistoryRaw119, data, referenceData119,
        referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base,
        HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawMaximumLabelWidth203,
        HistoryRawSchema.rawEqualityWorkWidth203, historyClockWidth, historyOrderWidth,
        HistoryRawSchema.rawBranchWire203, HistoryRawSchema.rawClockCarry203,
        HistoryRawSchema.rawOrderCarry203, HistoryRawSchema.rawSlice203] at hv
      omega
  · intro index
    change workspaceWire041 data _ ≠ orderWire041 data index
    exact (orderWire041_ne_workspace119 data index _).symm
  · change workspaceWire041 data _ ≠ workspaceWire041 data _
    apply workspaceWire041_ne_of_val_ne119
    simp [executableHistoryRaw119, data, referenceData119,
      referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
      referenceHistoryP15P16Raw040Base, HistoryRawSchema.rawActiveWire203,
      HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawSlice203]
  · change workspaceWire041 data _ ≠ workspaceWire041 data _
    apply workspaceWire041_ne_of_val_ne119
    simp [executableHistoryRaw119, data, referenceData119,
      referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
      referenceHistoryP15P16Raw040Base, HistoryRawSchema.rawActiveWire203,
      HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawSlice203]
  · intro index
    change workspaceWire041 data _ ≠ orderWire041 data index
    exact (orderWire041_ne_workspace119 data index _).symm
  · intro index
    change workspaceWire041 data _ ≠ orderWire041 data index
    exact (orderWire041_ne_workspace119 data index _).symm
  · change workspaceWire041 data _ ≠ signalWire041 data ⟨2, by decide⟩
    exact (signalWire041_ne_workspace119 data ⟨2, by decide⟩ _).symm
  · change workspaceWire041 data _ ≠ signalWire041 data ⟨2, by decide⟩
    exact (signalWire041_ne_workspace119 data ⟨2, by decide⟩ _).symm
  · change workspaceWire041 data _ ≠ workspaceWire041 data _
    apply workspaceWire041_ne_of_val_ne119
    simp [executableHistoryRaw119, data, referenceData119,
      referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
      referenceHistoryP15P16Raw040Base, HistoryRawSchema.rawBranchWire203,
      HistoryRawSchema.rawLessThanIdleEndWire203, HistoryRawSchema.rawStructuralPoolWidth203,
      HistoryRawSchema.rawSlice203]
  · change workspaceWire041 data _ ≠ signalWire041 data ⟨0, by decide⟩
    exact (signalWire041_ne_workspace119 data ⟨0, by decide⟩ _).symm
  · change workspaceWire041 data _ ≠ signalWire041 data ⟨0, by decide⟩
    exact (signalWire041_ne_workspace119 data ⟨0, by decide⟩ _).symm
  · change workspaceWire041 data _ ≠ workspaceWire041 data _
    apply workspaceWire041_ne_of_val_ne119
    simp [executableHistoryRaw119, data, referenceData119,
      referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
      referenceHistoryP15P16Raw040Base, HistoryRawSchema.rawActiveWire203,
      HistoryRawSchema.rawEqualityFlag203, HistoryRawSchema.rawStructuralPoolWidth203,
      HistoryRawSchema.rawSlice203]
  · change workspaceWire041 data _ ≠ signalWire041 data ⟨1, by decide⟩
    exact (signalWire041_ne_workspace119 data ⟨1, by decide⟩ _).symm
  · change workspaceWire041 data _ ≠ signalWire041 data ⟨1, by decide⟩
    exact (signalWire041_ne_workspace119 data ⟨1, by decide⟩ _).symm
  · change workspaceWire041 data _ ≠ workspaceWire041 data _
    apply workspaceWire041_ne_of_val_ne119
    simp [executableHistoryRaw119, data, referenceData119,
      referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
      referenceHistoryP15P16Raw040Base,
      HistoryRawSchema.rawLessThanIdleEndWire203, HistoryRawSchema.rawIdleFlag203,
      HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawSlice203]
  · change workspaceWire041 data _ ≠ workspaceWire041 data _
    apply workspaceWire041_ne_of_val_ne119
    simp [executableHistoryRaw119, data, referenceData119,
      referenceHistoryP15P16Raw041, referenceHistoryP15P16Raw040,
      referenceHistoryP15P16Raw040Base,
      HistoryRawSchema.rawLessThanTimeWire203, HistoryRawSchema.rawIdleFlag203,
      HistoryRawSchema.rawStructuralPoolWidth203, HistoryRawSchema.rawSlice203]
    omega
  · change workspaceWire041 data _ ≠ signalWire041 data ⟨0, by decide⟩
    exact (signalWire041_ne_workspace119 data ⟨0, by decide⟩ _).symm
  · change workspaceWire041 data _ ≠ signalWire041 data ⟨0, by decide⟩
    exact (signalWire041_ne_workspace119 data ⟨0, by decide⟩ _).symm

end
end ExecutableHistoryExecutableHistory
