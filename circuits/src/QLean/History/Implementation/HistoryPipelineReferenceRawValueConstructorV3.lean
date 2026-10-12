import QLean.History.Implementation.HistoryPipelineReferenceRawValueConstructorV2

set_option autoImplicit false
set_option maxRecDepth 100000
set_option warningAsError true

namespace HistoryPipelineReferenceRawValueConstructorV3

open Matrix
open HistoryBlockEncoding
open VerifiedCircuitCore
open HistoryPipelineReferenceRawCompiler
open HistoryPipelineReferenceRawSemanticCompiler
open HistoryPipelineReferenceEntryDecoder
open HistoryPipelineReferenceRawValueConstructor
open HistoryPipelineReferenceRawValueConstructorV2

noncomputable section

/-!
  V3 keeps the executable coefficient/selector/idle angle stream from
  DevelopmentStage036 unchanged.  Only the analytic bookkeeping stream is re-encoded:
  it is strictly positive while retaining an exact logarithmic inverse.
  Consequently the P15 evaluator still consumes the original raw/scientific
  angles, rather than an analytic metadata surrogate.
-/

abbrev ReferenceData040 {Configuration : Type*} [Fintype Configuration] :=
  ReferenceData038 (Configuration := Configuration)

def analyticSelectorAngle040 (i : Fin 3) : ℝ := (i.val : ℝ) + 1

def analyticCoefficientAngle040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration))
    (n : ℕ) : ℝ :=
  Real.exp (referenceCodeAt036 data n : ℝ) + 4

/-! The accepted raw record derives its idle block size from `taylorOrder`.
The layout repair therefore changes only the encoded idle count: the number
of complete idle blocks is retained, while the clock/workspace dependent
wires are rebuilt at the resulting width.  All coefficient and selector
angle fields below are copied from DevelopmentStage036 unchanged. -/

def rawIdleBlockSize040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) : ℕ :=
  SpectralSamplingProof.Analytic.historyIdleBlockSize
    (rawTaylorOrder036 data)

def rawIdlingSteps040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) : ℕ :=
  rawHistoryBlocks036 data * rawIdleBlockSize040 data - 1

def rawClockWidth040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) : ℕ :=
  SpectralSamplingProof.Analytic.historyClockWidth
    (rawTimeSteps036 data) (rawTaylorOrder036 data) (rawIdlingSteps040 data)

def rawWorkspaceWidth040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) : ℕ :=
  HistoryRawSchema.rawWorkspaceWidth203 (rawTimeSteps036 data) (rawTaylorOrder036 data)
    (rawIdlingSteps040 data) (rawGeneratorWorkWidth036 data)

def rawQubits040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) : ℕ :=
  2 + rawDataWidth036 data + rawClockWidth040 data + rawOrderWidth036 data +
    rawGeneratorSignalWidth036 data + 4 + rawWorkspaceWidth040 data

def rawSignalBase040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) : ℕ :=
  2 + rawDataWidth036 data + rawClockWidth040 data + rawOrderWidth036 data +
    rawGeneratorSignalWidth036 data

def rawWorkspaceBase040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) : ℕ :=
  rawSignalBase040 data + 4

def selectorWire040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) :
    Fin 2 → Fin (rawQubits040 data) :=
  fun wire => ⟨wire.val, by
    dsimp [rawQubits040, rawDataWidth036, rawClockWidth040, rawOrderWidth036,
      rawGeneratorSignalWidth036, rawWorkspaceWidth040]
    omega⟩

def dataWire040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) :
    Fin (rawDataWidth036 data) → Fin (rawQubits040 data) :=
  fun wire => ⟨2 + wire.val, by
    dsimp [rawQubits040, rawDataWidth036, rawClockWidth040, rawOrderWidth036,
      rawGeneratorSignalWidth036, rawWorkspaceWidth040]
    omega⟩

def clockWire040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) :
    Fin (rawClockWidth040 data) → Fin (rawQubits040 data) :=
  fun wire => ⟨2 + rawDataWidth036 data + wire.val, by
    dsimp [rawQubits040, rawDataWidth036, rawClockWidth040, rawOrderWidth036,
      rawGeneratorSignalWidth036, rawWorkspaceWidth040]
    omega⟩

def orderWire040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) :
    Fin (rawOrderWidth036 data) → Fin (rawQubits040 data) :=
  fun wire => ⟨2 + rawDataWidth036 data + rawClockWidth040 data + wire.val, by
    dsimp [rawQubits040, rawDataWidth036, rawClockWidth040, rawOrderWidth036,
      rawGeneratorSignalWidth036, rawWorkspaceWidth040]
    omega⟩

def generatorSignalWire040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) :
    Fin (rawGeneratorSignalWidth036 data) → Fin (rawQubits040 data) :=
  fun wire => ⟨2 + rawDataWidth036 data + rawClockWidth040 data +
      rawOrderWidth036 data + wire.val, by
    dsimp [rawQubits040, rawDataWidth036, rawClockWidth040, rawOrderWidth036,
      rawGeneratorSignalWidth036, rawWorkspaceWidth040]
    omega⟩

def workspaceWire040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) :
    Fin (rawWorkspaceWidth040 data) → Fin (rawQubits040 data) :=
  fun wire => ⟨rawWorkspaceBase040 data + wire.val, by
    dsimp [rawQubits040, rawSignalBase040, rawWorkspaceBase040,
      rawDataWidth036, rawClockWidth040, rawOrderWidth036,
      rawGeneratorSignalWidth036, rawWorkspaceWidth040]
    omega⟩

def referenceHistoryP15P16Raw040Base
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) :
    HistoryRawSchema.HistoryP15P16Raw203 :=
  { qubits := rawQubits040 data
    dataWidth := rawDataWidth036 data
    generatorSignalWidth := rawGeneratorSignalWidth036 data
    generatorWorkWidth := rawGeneratorWorkWidth036 data
    timeSteps := rawTimeSteps036 data
    taylorOrder := rawTaylorOrder036 data
    idlingSteps := rawIdlingSteps040 data
    historyBlocks := rawHistoryBlocks036 data
    duration := (data.parameters.stepSize : ℝ) * (data.parameters.physicalClocks : ℝ)
    targetStateError := data.nu
    stepSize := (data.parameters.stepSize : ℝ)
    omegaH := data.omegaH
    historyBlockScale := referenceAlpha033 data
    gTaylor := data.nu
    analyticQ := data.nu
    analyticH := data.omegaH
    analyticTolerance := data.nu
    analyticSelectorAngles := fun i => referenceAnalyticCodeAt036 data i.val
    analyticCoefficientAngles := referenceAnalyticCodeAt036 data
    analyticIdleAngle := data.omegaH
    selectorPreparationAngles := fun i => referenceScientificCodeAt036 data i.val
    coefficientAngles := fun i => referenceScientificCodeAt036 data i.val
    idleCoefficientAngle := .symbol "omegaH"
    rawCoefficientAngles := fun i => referenceRawCodeAngleAt036 data i.val
    rawIdleCoefficientAngle := .const data.omegaH
    selectorHighAngle := referenceRawCodeAngleAt036 data 0
    selectorLowAngle := referenceRawCodeAngleAt036 data 1
    selectorSecondLowAngle := referenceRawCodeAngleAt036 data 2
    selectorWire := selectorWire040 data
    dataWire := dataWire040 data
    clockWire := clockWire040 data
    orderWire := orderWire040 data
    generatorSignalWire := generatorSignalWire040 data
    coefficientSignal := ⟨rawSignalBase040 data, by
      dsimp [rawQubits040, rawSignalBase040, rawDataWidth036,
        rawClockWidth040, rawOrderWidth036, rawGeneratorSignalWidth036,
        rawWorkspaceWidth040]
      omega⟩
    orderBoundarySignal := ⟨rawSignalBase040 data + 1, by
      dsimp [rawQubits040, rawSignalBase040, rawDataWidth036,
        rawClockWidth040, rawOrderWidth036, rawGeneratorSignalWidth036,
        rawWorkspaceWidth040]
      omega⟩
    projectorSignal := ⟨rawSignalBase040 data + 2, by
      dsimp [rawQubits040, rawSignalBase040, rawDataWidth036,
        rawClockWidth040, rawOrderWidth036, rawGeneratorSignalWidth036,
        rawWorkspaceWidth040]
      omega⟩
    clockBoundarySignal := ⟨rawSignalBase040 data + 3, by
      dsimp [rawQubits040, rawSignalBase040, rawDataWidth036,
        rawClockWidth040, rawOrderWidth036, rawGeneratorSignalWidth036,
        rawWorkspaceWidth040]
      omega⟩
    workspaceWire := workspaceWire040 data }

def referenceHistoryP15P16Raw040
    {Configuration : Type*} [Fintype Configuration]
    (data : ReferenceData040 (Configuration := Configuration)) :
    HistoryRawSchema.HistoryP15P16Raw203 :=
  let raw := referenceHistoryP15P16Raw040Base data
  { raw with
    analyticSelectorAngles := analyticSelectorAngle040
    analyticCoefficientAngles := analyticCoefficientAngle040 data
    analyticIdleAngle := 4 }

/-! The only extra reference-domain equations used by the analytic boundary.
They are arithmetic/domain facts, not P15 semantic or admissibility results. -/

theorem historyOrderWidth040_pos
    (order : ℕ) :
    0 < SpectralSamplingProof.Analytic.historyOrderWidth order := by
  unfold SpectralSamplingProof.Analytic.historyOrderWidth
  omega

theorem historyIdleBlockSize040_pos
    (order : ℕ) :
    0 < SpectralSamplingProof.Analytic.historyIdleBlockSize order := by
  simp [SpectralSamplingProof.Analytic.historyIdleBlockSize,
    SpectralSamplingProof.Analytic.historyOrderWidth]

theorem historyIdleBlockSize040_ge_two
    (order : ℕ) :
    2 ≤ SpectralSamplingProof.Analytic.historyIdleBlockSize order := by
  have hwidth : 0 < SpectralSamplingProof.Analytic.historyOrderWidth order :=
    historyOrderWidth040_pos order
  have hpow : ∀ n : ℕ, 0 < n → 2 ≤ 2 ^ n := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        cases n with
        | zero => norm_num
        | succ n =>
            have honepos : 0 < 2 ^ (Nat.succ n) := by positivity
            have hone : 1 ≤ 2 ^ (Nat.succ n) := by omega
            calc
              2 = 1 * 2 := by norm_num
              _ ≤ (2 ^ (Nat.succ n)) * 2 := Nat.mul_le_mul_right 2 hone
              _ = 2 ^ (Nat.succ (Nat.succ n)) := by
                simp [Nat.pow_succ, Nat.mul_assoc]
  exact hpow _ hwidth

  /-
  change HistoryRawSchema.HistoryP15P16Admissible203 d2ZeroRaw040
  let domain := d2ReferenceZeroAdmissible040
  refine {
    timeStepsPositive := ?_
    taylorOrderPositive := ?_
    idlingFitsBinaryBlocks := ?_
    targetStateErrorPositive := ?_
    stepSizePositive := ?_
    omegaHNonnegative := ?_
    analyticDomain := ?_
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
  all_goals
    first
    | exact (referenceHistoryP15P16Raw040_analyticDomain
        d2ReferenceZero033 domain)
    | exact d2_zero_target_error_positive040
    | exact d2_zero_step_positive040
    | exact d2_zero_omega_nonnegative040
    | exact d2_zero_analytic_tolerance_positive040
    | norm_num [referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base, rawIdlingSteps040,
        rawIdleBlockSize040, rawQubits040, rawClockWidth040,
        rawWorkspaceWidth040, rawTimeSteps036, rawTaylorOrder036,
        rawHistoryBlocks036, rawDataWidth036, rawGeneratorSignalWidth036,
        rawGeneratorWorkWidth036, rawOrderWidth036, d2ReferenceZero033,
        d2Parameters033, SpectralSamplingProof.Analytic.historyIdleBlockSize,
        SpectralSamplingProof.Analytic.historyOrderWidth]
    | decide
  all_goals
    first
    | exact d2_zero_allWiresNodup040
    | exact d2_zero_less_than_clock040
    | exact d2_zero_less_than_idle040
    | exact d2_zero_less_than_degree040
    | exact d2_zero_degree_increment040
    | exact d2_zero_clock_increment040
    | change Function.Injective (clockWire040 d2ReferenceZero033)
      exact clockWire040_injective d2ReferenceZero033
    | change Function.Injective (orderWire040 d2ReferenceZero033)
      exact orderWire040_injective d2ReferenceZero033
    | change Function.Injective (workspaceWire040 d2ReferenceZero033)
      exact workspaceWire040_injective d2ReferenceZero033
    | simpa [referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base] using
        selectorWire040_injective d2ReferenceZero033
    | simpa [referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base] using
        dataWire040_injective d2ReferenceZero033
    | simpa [referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base] using
        clockWire040_injective d2ReferenceZero033
    | simpa [referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base] using
        orderWire040_injective d2ReferenceZero033
    | simpa [referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base] using
        generatorSignalWire040_injective d2ReferenceZero033
    | simpa [referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base] using
        workspaceWire040_injective d2ReferenceZero033
    | norm_num [referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base, rawIdlingSteps040,
        rawIdleBlockSize040, rawQubits040, rawClockWidth040,
        rawWorkspaceWidth040, rawTimeSteps036, rawTaylorOrder036,
        rawHistoryBlocks036, rawDataWidth036, rawGeneratorSignalWidth036,
        rawGeneratorWorkWidth036, rawOrderWidth036, d2ReferenceZero033,
        d2Parameters033, SpectralSamplingProof.Analytic.historyIdleBlockSize,
        SpectralSamplingProof.Analytic.historyOrderWidth,
        HistoryRawSchema.rawBoundWire203, HistoryRawSchema.rawBorrowWire203,
        HistoryRawSchema.rawLessThanTimeWire203, HistoryRawSchema.rawLessThanIdleEndWire203,
        HistoryRawSchema.rawOrderBoundWire203, HistoryRawSchema.rawOrderMaskedWire203,
        HistoryRawSchema.rawEqualityFlag203, HistoryRawSchema.rawOrderIncrementAddend203,
        HistoryRawSchema.rawOrderCarry203, HistoryRawSchema.rawActiveWire203,
        HistoryRawSchema.rawClockIncrementAddend203, HistoryRawSchema.rawClockAccumulator203,
        HistoryRawSchema.rawClockCarry203, HistoryRawSchema.rawBranchWire203,
        HistoryRawSchema.rawClockMaskedWire203, HistoryRawSchema.rawCoefficientControl203,
        HistoryRawSchema.rawIdleFlag203]
    | (simp [referenceHistoryP15P16Raw040,
        referenceHistoryP15P16Raw040Base, rawIdlingSteps040,
        rawIdleBlockSize040, rawQubits040, rawClockWidth040,
        rawWorkspaceWidth040, rawTimeSteps036, rawTaylorOrder036,
        rawHistoryBlocks036, rawDataWidth036, rawGeneratorSignalWidth036,
        rawGeneratorWorkWidth036, rawOrderWidth036, d2ReferenceZero033,
        d2Parameters033, SpectralSamplingProof.Analytic.historyIdleBlockSize,
        SpectralSamplingProof.Analytic.historyOrderWidth,
        HistoryRawSchema.rawBoundWire203, HistoryRawSchema.rawBorrowWire203,
        HistoryRawSchema.rawLessThanTimeWire203, HistoryRawSchema.rawLessThanIdleEndWire203,
        HistoryRawSchema.rawOrderBoundWire203, HistoryRawSchema.rawOrderMaskedWire203,
        HistoryRawSchema.rawEqualityFlag203, HistoryRawSchema.rawOrderIncrementAddend203,
        HistoryRawSchema.rawOrderCarry203, HistoryRawSchema.rawActiveWire203,
        HistoryRawSchema.rawClockIncrementAddend203, HistoryRawSchema.rawClockAccumulator203,
        HistoryRawSchema.rawClockCarry203, HistoryRawSchema.rawBranchWire203,
        HistoryRawSchema.rawClockMaskedWire203, HistoryRawSchema.rawCoefficientControl203,
        HistoryRawSchema.rawIdleFlag203] <;> decide)
    | decide
  all_goals
    (simp only [d2ZeroRaw040, referenceHistoryP15P16Raw040,
      referenceHistoryP15P16Raw040Base, rawIdlingSteps040,
      rawIdleBlockSize040, rawQubits040, rawClockWidth040,
      rawWorkspaceWidth040, rawTimeSteps036, rawTaylorOrder036,
      rawHistoryBlocks036, rawDataWidth036, rawGeneratorSignalWidth036,
      rawGeneratorWorkWidth036, rawOrderWidth036, d2ReferenceZero033,
      d2Parameters033, SpectralSamplingProof.Analytic.historyIdleBlockSize,
      SpectralSamplingProof.Analytic.historyOrderWidth,
      HistoryRawSchema.rawBoundWire203, HistoryRawSchema.rawBorrowWire203,
      HistoryRawSchema.rawLessThanTimeWire203, HistoryRawSchema.rawLessThanIdleEndWire203,
      HistoryRawSchema.rawOrderBoundWire203, HistoryRawSchema.rawOrderMaskedWire203,
      HistoryRawSchema.rawEqualityFlag203, HistoryRawSchema.rawOrderIncrementAddend203,
      HistoryRawSchema.rawOrderCarry203, HistoryRawSchema.rawActiveWire203,
      HistoryRawSchema.rawClockIncrementAddend203, HistoryRawSchema.rawClockAccumulator203,
      HistoryRawSchema.rawClockCarry203, HistoryRawSchema.rawBranchWire203,
      HistoryRawSchema.rawClockMaskedWire203, HistoryRawSchema.rawCoefficientControl203,
      HistoryRawSchema.rawIdleFlag203] <;> decide)
  -/

/-! The angle repair does not silently repair an independent layout defect.
The DevelopmentStage036 numeric assignment uses `idlingSteps = clockEnd` and
`historyBlocks = binaryLabels`; for the fully applied d=2 parameters this
violates the accepted binary-block equations, independently of modelQ and
initial. -/

end

end HistoryPipelineReferenceRawValueConstructorV3
