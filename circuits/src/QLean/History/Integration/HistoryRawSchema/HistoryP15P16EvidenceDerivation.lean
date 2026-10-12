import QLean.History.HistoryAnalyticParameters194
import QLean.Spectral.Analysis.R12OperatorDag
import QLean.Circuits.Foundation.Foundations
import QLean.Spectral.Circuits.HistoryBlock
import QLean.Spectral.Circuits.HistoryTaylorBlock
import QLean.Spectral.Circuits.HistoryTaylorQ10CleanLink
import QLean.Spectral.Analysis.HistoryClockCheckpointSpecifications
import QLean.Spectral.Circuits.HistoryClockClean
import QLean.Circuits.Foundation.Combinators
import QLean.Circuits.Foundation.Gates
import QLean.Circuits.Foundation.PrimitiveGateProofs
import QLean.Circuits.Foundation.QuantumFourier
import QLean.Circuits.Foundation.QuantumFourierAnalytic
import QLean.Circuits.Foundation.QubitBasisEncoding
import QLean.Circuits.Foundation.OperatorL2Error
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import QLean.Circuits.Foundation.ReversibleLogic
import QLean.Circuits.Foundation.ReversibleLogicCleanAnalytic
import QLean.Circuits.Foundation.UniformPreparationCorrectness
import QLean.Circuits.Foundation.ShuklaVedulaUniformCorrectness
import QLean.Circuits.Foundation.WireEmbedding
import QLean.Circuits.Foundation.BitonicNetworkAnalytic
import QLean.Circuits.Foundation.EqualityBranchLessThanAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStage
import QLean.Circuits.Foundation.ControlledConstantAdder
import QLean.Circuits.Foundation.PrimitiveOperatorSemantics
import QLean.Circuits.Foundation.FinitePhaseTransformAnalytic
import QLean.Generator.Implementation.ProbabilityGeneratorCoreExactAdapter
import Mathlib
import QLean.Circuits.Foundation.ReversibleLogicAnalytic
import QLean.Circuits.Foundation.ControlledCircuitCompilerV2
import QLean.Circuits.Foundation.PhaseShiftMacros
import QLean.Circuits.Foundation.ControlledHadamard
import QLean.Circuits.Foundation.Metrics
import QLean.Circuits.Foundation.WireEmbeddingAnalytic
import QLean.Circuits.Foundation.ClassicalReversibleStageAnalytic
import QLean.Circuits.Foundation.ClassicalMinimumWorkMultiControlledXCorrectnessAnalytic
import QLean.Spectral.Circuits.ControlledSubcircuit
import QLean.Generator.Implementation.OracleCanonicalFullStageCompiler
import QLean.Generator.Implementation.QVerifiedTopComponents
import QLean.Generator.Implementation.QVerifiedArithmeticComponents
import QLean.Circuits.Foundation.ControlledRotationMacros
import QLean.History.Integration.IndexedHistoryProvider.HistoryProviderIndexedChildEstablishedBridge

set_option autoImplicit false

namespace HistoryRawSchema

open VerifiedCircuitCore
open SpectralSamplingProof
open SpectralSamplingProof.Analytic
open SpectralSamplingProof.Components
open HistoryAnalyticParameterExistence194

/-!
The raw packet is deliberately proof-free: it records numeric values, exact
angle syntax, and physical-wire functions only.  The admissibility predicate
contains elementary numeric and wire inequalities, but does not contain any
accepted Taylor/clock evidence, circuit, target, correctness, or occurrence
object.  This is the boundary that the failed 202 proposal did not provide.
-/

def rawEqualityWorkWidth203 (timeSteps taylorOrder idlingSteps : Nat) : Nat :=
  max (historyClockWidth timeSteps taylorOrder idlingSteps)
      (historyOrderWidth taylorOrder) - 2

def rawMaximumLabelWidth203 (timeSteps taylorOrder idlingSteps : Nat) : Nat :=
  max (historyClockWidth timeSteps taylorOrder idlingSteps)
      (historyOrderWidth taylorOrder)

def rawStructuralPoolWidth203
    (timeSteps taylorOrder idlingSteps : Nat) : Nat :=
  5 + 2 * historyClockWidth timeSteps taylorOrder idlingSteps +
    rawEqualityWorkWidth203 timeSteps taylorOrder idlingSteps +
    2 * rawMaximumLabelWidth203 timeSteps taylorOrder idlingSteps

def rawWorkspaceWidth203
    (timeSteps taylorOrder idlingSteps generatorWorkWidth : Nat) : Nat :=
  max generatorWorkWidth
      (rawStructuralPoolWidth203 timeSteps taylorOrder idlingSteps) + 6

def rawOrderTailWidth203 (taylorOrder : Nat) : Nat :=
  historyOrderWidth taylorOrder - 1

def rawClockTailWidth203 (timeSteps taylorOrder idlingSteps : Nat) : Nat :=
  historyClockWidth timeSteps taylorOrder idlingSteps - 1

structure HistoryP15P16Raw203 where
  qubits : Nat
  dataWidth : Nat
  generatorSignalWidth : Nat
  generatorWorkWidth : Nat
  timeSteps : Nat
  taylorOrder : Nat
  idlingSteps : Nat
  historyBlocks : Nat
  duration : ℝ
  targetStateError : ℝ
  stepSize : ℝ
  omegaH : ℝ
  historyBlockScale : ℝ
  gTaylor : ℝ
  analyticQ : ℝ
  analyticH : ℝ
  analyticTolerance : ℝ
  analyticSelectorAngles : Fin 3 → ℝ
  analyticCoefficientAngles : Nat → ℝ
  analyticIdleAngle : ℝ
  selectorPreparationAngles : Fin 3 → ScientificAngleExpr
  coefficientAngles : Fin taylorOrder → ScientificAngleExpr
  idleCoefficientAngle : ScientificAngleExpr
  rawCoefficientAngles : Fin taylorOrder → VerifiedCircuitCore.AngleExpr
  rawIdleCoefficientAngle : VerifiedCircuitCore.AngleExpr
  selectorHighAngle : VerifiedCircuitCore.AngleExpr
  selectorLowAngle : VerifiedCircuitCore.AngleExpr
  selectorSecondLowAngle : VerifiedCircuitCore.AngleExpr
  selectorWire : Fin 2 → Fin qubits
  dataWire : Fin dataWidth → Fin qubits
  clockWire : Fin (historyClockWidth timeSteps taylorOrder idlingSteps) → Fin qubits
  orderWire : Fin (historyOrderWidth taylorOrder) → Fin qubits
  generatorSignalWire : Fin generatorSignalWidth → Fin qubits
  coefficientSignal : Fin qubits
  orderBoundarySignal : Fin qubits
  projectorSignal : Fin qubits
  clockBoundarySignal : Fin qubits
  workspaceWire : Fin
    (rawWorkspaceWidth203 timeSteps taylorOrder idlingSteps generatorWorkWidth) →
    Fin qubits

def analyticBase203 (raw : HistoryP15P16Raw203) :
    HistoryAnalyticParameters194 :=
  { q := raw.analyticQ
    h := raw.analyticH
    duration := raw.duration
    stepSize := raw.stepSize
    timeSteps := raw.timeSteps
    idlingSteps := raw.idlingSteps
    idlingBlockSize := historyIdleBlockSize raw.taylorOrder
    historyBlocks := raw.historyBlocks
    selectorCount := 3
    selectorAngles := raw.analyticSelectorAngles
    coefficientAngles := raw.analyticCoefficientAngles
    idleAngle := raw.analyticIdleAngle }

def rawSlice203 (raw : HistoryP15P16Raw203) (offset width : Nat)
    (fits : offset + width ≤
      rawWorkspaceWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps
        raw.generatorWorkWidth) : Fin width → Fin raw.qubits :=
  fun index => raw.workspaceWire ⟨offset + index.val, by omega⟩

def rawBoundWire203 (raw : HistoryP15P16Raw203) :
    Fin (historyClockWidth raw.timeSteps raw.taylorOrder raw.idlingSteps) →
      Fin raw.qubits :=
  rawSlice203 raw 5 _ (by
    have h := Nat.le_max_right raw.generatorWorkWidth
      (rawStructuralPoolWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps)
    unfold rawWorkspaceWidth203 rawStructuralPoolWidth203 at h ⊢
    unfold rawEqualityWorkWidth203 rawMaximumLabelWidth203 at h ⊢
    omega)

def rawBorrowWire203 (raw : HistoryP15P16Raw203) :
    Fin (historyClockWidth raw.timeSteps raw.taylorOrder raw.idlingSteps) →
      Fin raw.qubits :=
  rawSlice203 raw (5 + historyClockWidth raw.timeSteps raw.taylorOrder raw.idlingSteps)
    _ (by
      have h := Nat.le_max_right raw.generatorWorkWidth
        (rawStructuralPoolWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps)
      unfold rawWorkspaceWidth203 rawStructuralPoolWidth203 at h ⊢
      unfold rawEqualityWorkWidth203 rawMaximumLabelWidth203 at h ⊢
      omega)

def rawEqualityFlag203 (raw : HistoryP15P16Raw203) : Fin raw.qubits :=
  raw.workspaceWire ⟨2, by unfold rawWorkspaceWidth203; omega⟩

def rawCoefficientControl203 (raw : HistoryP15P16Raw203) : Fin raw.qubits :=
  raw.workspaceWire ⟨3, by unfold rawWorkspaceWidth203; omega⟩

def rawIdleFlag203 (raw : HistoryP15P16Raw203) : Fin raw.qubits :=
  raw.workspaceWire ⟨4, by unfold rawWorkspaceWidth203; omega⟩

def rawBranchWire203 (raw : HistoryP15P16Raw203) : Fin raw.qubits :=
  raw.workspaceWire ⟨
    max raw.generatorWorkWidth
      (rawStructuralPoolWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps) + 2,
    by unfold rawWorkspaceWidth203; omega⟩

def rawLessThanTimeWire203 (raw : HistoryP15P16Raw203) : Fin raw.qubits :=
  raw.workspaceWire ⟨
    max raw.generatorWorkWidth
      (rawStructuralPoolWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps) + 3,
    by unfold rawWorkspaceWidth203; omega⟩

def rawLessThanIdleEndWire203 (raw : HistoryP15P16Raw203) : Fin raw.qubits :=
  raw.workspaceWire ⟨
    max raw.generatorWorkWidth
      (rawStructuralPoolWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps) + 4,
    by unfold rawWorkspaceWidth203; omega⟩

def rawActiveWire203 (raw : HistoryP15P16Raw203) : Fin raw.qubits :=
  raw.workspaceWire ⟨
    max raw.generatorWorkWidth
      (rawStructuralPoolWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps) + 5,
    by unfold rawWorkspaceWidth203; omega⟩

def rawOrderBoundWire203 (raw : HistoryP15P16Raw203) :
    Fin (historyOrderWidth raw.taylorOrder) → Fin raw.qubits :=
  rawSlice203 raw
    (5 + 2 * historyClockWidth raw.timeSteps raw.taylorOrder raw.idlingSteps +
      rawEqualityWorkWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps) _ (by
      have h := Nat.le_max_right raw.generatorWorkWidth
        (rawStructuralPoolWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps)
      unfold rawWorkspaceWidth203 rawStructuralPoolWidth203 at h ⊢
      unfold rawEqualityWorkWidth203 rawMaximumLabelWidth203 at h ⊢
      omega)

def rawOrderMaskedWire203 (raw : HistoryP15P16Raw203) :
    Fin (historyOrderWidth raw.taylorOrder) → Fin raw.qubits :=
  rawSlice203 raw
    (5 + 2 * historyClockWidth raw.timeSteps raw.taylorOrder raw.idlingSteps +
      rawEqualityWorkWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps +
      rawMaximumLabelWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps) _ (by
      have h := Nat.le_max_right raw.generatorWorkWidth
        (rawStructuralPoolWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps)
      unfold rawWorkspaceWidth203 rawStructuralPoolWidth203 at h ⊢
      unfold rawEqualityWorkWidth203 rawMaximumLabelWidth203 at h ⊢
      omega)

def rawOrderIncrementAddend203 (raw : HistoryP15P16Raw203) :
    Fin (rawOrderTailWidth203 raw.taylorOrder + 1) → Fin raw.qubits :=
  fun index => rawOrderMaskedWire203 raw
    (Fin.cast (by
      have hwidth : 0 < historyOrderWidth raw.taylorOrder := by
        unfold historyOrderWidth
        omega
      unfold rawOrderTailWidth203
      omega) index)

def rawOrderCarry203 (raw : HistoryP15P16Raw203) : Fin raw.qubits :=
  raw.workspaceWire ⟨
    5 + 2 * historyClockWidth raw.timeSteps raw.taylorOrder raw.idlingSteps +
      rawEqualityWorkWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps,
    by
      have h := Nat.le_max_right raw.generatorWorkWidth
        (rawStructuralPoolWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps)
      unfold rawWorkspaceWidth203 rawStructuralPoolWidth203 at h ⊢
      unfold rawEqualityWorkWidth203 rawMaximumLabelWidth203 at h ⊢
      omega⟩

def rawClockMaskedWire203 (raw : HistoryP15P16Raw203) :
    Fin (historyClockWidth raw.timeSteps raw.taylorOrder raw.idlingSteps) →
      Fin raw.qubits :=
  rawSlice203 raw
    (5 + 2 * historyClockWidth raw.timeSteps raw.taylorOrder raw.idlingSteps +
      rawEqualityWorkWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps +
      rawMaximumLabelWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps) _ (by
      have h := Nat.le_max_right raw.generatorWorkWidth
        (rawStructuralPoolWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps)
      unfold rawWorkspaceWidth203 rawStructuralPoolWidth203 at h ⊢
      unfold rawEqualityWorkWidth203 rawMaximumLabelWidth203 at h ⊢
      omega)

def rawClockIncrementAddend203 (raw : HistoryP15P16Raw203) :
    Fin (rawClockTailWidth203 raw.timeSteps raw.taylorOrder raw.idlingSteps + 1) →
      Fin raw.qubits :=
  fun index => rawClockMaskedWire203 raw
    (Fin.cast (by
      have hwidth : 0 < historyClockWidth raw.timeSteps raw.taylorOrder
          raw.idlingSteps := by
        unfold historyClockWidth
        omega
      unfold rawClockTailWidth203
      omega) index)

def rawClockCarry203 (raw : HistoryP15P16Raw203) : Fin raw.qubits :=
  rawOrderCarry203 raw

def rawClockAccumulator203 (raw : HistoryP15P16Raw203) :
    Fin (historyClockWidth raw.timeSteps raw.taylorOrder raw.idlingSteps) →
      Fin raw.qubits := raw.clockWire

structure RawLessThanEvidence203 {qubits width : Nat}
    (lhs rhs borrow : Fin width → Fin qubits) (target : Fin qubits) where
  widthPositive : 0 < width
  lhsRhsDifferent : ∀ left right, lhs left ≠ rhs right
  lhsBorrowDifferent : ∀ left right, lhs left ≠ borrow right
  rhsBorrowDifferent : ∀ left right, rhs left ≠ borrow right
  targetLhsDifferent : ∀ index, target ≠ lhs index
  targetRhsDifferent : ∀ index, target ≠ rhs index
  targetBorrowDifferent : ∀ index, target ≠ borrow index

structure RawDegreeIncrementEvidence203 {qubits width : Nat}
    (addend accumulator : Fin width → Fin qubits)
    (carry control : Fin qubits) where
  addendAccumulatorDisjoint : ∀ left right, addend left ≠ accumulator right
  carryNeAddend : ∀ index, carry ≠ addend index
  carryNeAccumulator : ∀ index, carry ≠ accumulator index
  controlNeAddend : ∀ index, control ≠ addend index
  controlNeAccumulator : ∀ index, control ≠ accumulator index
  controlNeCarry : control ≠ carry

structure RawClockIncrementEvidence203 {qubits width : Nat}
    (masked accumulator : Fin width → Fin qubits)
    (carry branch : Fin qubits) where
  maskedAccumulatorDisjoint : ∀ left right, masked left ≠ accumulator right
  carryNeMasked : ∀ index, carry ≠ masked index
  carryNeAccumulator : ∀ index, carry ≠ accumulator index
  branchNeMasked : ∀ index, branch ≠ masked index
  branchNeAccumulator : ∀ index, branch ≠ accumulator index
  branchNeCarry : branch ≠ carry

structure HistoryP15P16Admissible203 (raw : HistoryP15P16Raw203) : Prop where
  timeStepsPositive : 0 < raw.timeSteps
  taylorOrderPositive : 0 < raw.taylorOrder
  idlingFitsBinaryBlocks :
    (raw.idlingSteps + 1) % historyIdleBlockSize raw.taylorOrder = 0
  targetStateErrorPositive : 0 < raw.targetStateError
  stepSizePositive : 0 < raw.stepSize
  omegaHNonnegative : 0 ≤ raw.omegaH
  analyticDomain : HistoryAnalyticBaseDomain194 (analyticBase203 raw)
  analyticTolerancePositive : 0 < raw.analyticTolerance
  selectorInjective : Function.Injective raw.selectorWire
  dataInjective : Function.Injective raw.dataWire
  clockInjective : Function.Injective raw.clockWire
  orderInjective : Function.Injective raw.orderWire
  generatorSignalInjective : Function.Injective raw.generatorSignalWire
  workspaceInjective : Function.Injective raw.workspaceWire
  allWiresNodup :
    (List.ofFn raw.selectorWire ++ List.ofFn raw.dataWire ++
      List.ofFn raw.clockWire ++ List.ofFn raw.orderWire ++
      List.ofFn raw.generatorSignalWire ++
      [raw.coefficientSignal, raw.orderBoundarySignal,
        raw.projectorSignal, raw.clockBoundarySignal] ++
      List.ofFn raw.workspaceWire).Nodup
  clockTimeLessThan : RawLessThanEvidence203 raw.clockWire
    (rawBoundWire203 raw) (rawBorrowWire203 raw)
    (rawLessThanTimeWire203 raw)
  clockIdleEndLessThan : RawLessThanEvidence203 raw.clockWire
    (rawBoundWire203 raw) (rawBorrowWire203 raw)
    (rawLessThanIdleEndWire203 raw)
  degreeOrderLessThan : RawLessThanEvidence203 raw.orderWire
    (rawOrderBoundWire203 raw) (rawOrderMaskedWire203 raw)
    (rawEqualityFlag203 raw)
  degreeIncrement : RawDegreeIncrementEvidence203
    (rawOrderIncrementAddend203 raw) raw.orderWire
    (rawOrderCarry203 raw) (rawActiveWire203 raw)
  clockIncrement : RawClockIncrementEvidence203
    (rawClockIncrementAddend203 raw) (rawClockAccumulator203 raw)
    (rawClockCarry203 raw) (rawBranchWire203 raw)
  uniformActiveNeOrder : ∀ source,
    rawActiveWire203 raw ≠ raw.orderWire source
  uniformWork₀NeActive :
    raw.workspaceWire ⟨0, by unfold rawWorkspaceWidth203; omega⟩ ≠
      rawActiveWire203 raw
  uniformWork₁NeActive :
    raw.workspaceWire ⟨1, by unfold rawWorkspaceWidth203; omega⟩ ≠
      rawActiveWire203 raw
  uniformWork₀NeOrder : ∀ source,
    raw.workspaceWire ⟨0, by unfold rawWorkspaceWidth203; omega⟩ ≠
      raw.orderWire source
  uniformWork₁NeOrder : ∀ source,
    raw.workspaceWire ⟨1, by unfold rawWorkspaceWidth203; omega⟩ ≠
      raw.orderWire source
  projectorBranchNeProjector : rawBranchWire203 raw ≠ raw.projectorSignal
  projectorCoefficientControlNeProjector :
    rawCoefficientControl203 raw ≠ raw.projectorSignal
  branchNeIdleEnd : rawBranchWire203 raw ≠ rawLessThanIdleEndWire203 raw
  branchNeCoefficientSignal : rawBranchWire203 raw ≠ raw.coefficientSignal
  lessThanIdleEndNeCoefficientSignal :
    rawLessThanIdleEndWire203 raw ≠ raw.coefficientSignal
  activeNeEquality : rawActiveWire203 raw ≠ rawEqualityFlag203 raw
  activeNeOrderBoundary : rawActiveWire203 raw ≠ raw.orderBoundarySignal
  equalityNeOrderBoundary : rawEqualityFlag203 raw ≠ raw.orderBoundarySignal
  lessThanIdleNeIdle : rawLessThanIdleEndWire203 raw ≠ rawIdleFlag203 raw
  lessThanTimeNeIdle : rawLessThanTimeWire203 raw ≠ rawIdleFlag203 raw
  activeNeCoefficientSignal : rawActiveWire203 raw ≠ raw.coefficientSignal
  coefficientControlNeCoefficientSignal :
    rawCoefficientControl203 raw ≠ raw.coefficientSignal

def parameters203 (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) : HistoryBlockParameters :=
  { timeSteps := raw.timeSteps
    taylorOrder := raw.taylorOrder
    idlingSteps := raw.idlingSteps
    historyBlocks := raw.historyBlocks
    timeStepsPositive := admissible.timeStepsPositive
    taylorOrderPositive := admissible.taylorOrderPositive
    idlingFitsBinaryBlocks := admissible.idlingFitsBinaryBlocks
    duration := raw.duration
    targetStateError := raw.targetStateError
    stepSize := raw.stepSize
    omegaH := raw.omegaH
    historyBlockScale := raw.historyBlockScale
    gTaylor := raw.gTaylor
    targetStateErrorPositive := admissible.targetStateErrorPositive
    stepSizePositive := admissible.stepSizePositive
    omegaHNonnegative := admissible.omegaHNonnegative
    selectorPreparationAngles := raw.selectorPreparationAngles
    coefficientAngles := raw.coefficientAngles
    idleCoefficientAngle := raw.idleCoefficientAngle }

def layout203 (raw : HistoryP15P16Raw203)
    (admissible : HistoryP15P16Admissible203 raw) :
    HistoryBlockLayout raw.qubits raw.dataWidth raw.generatorSignalWidth
      (historyClockWorkspaceWidth (parameters203 raw admissible)
        raw.generatorWorkWidth) (parameters203 raw admissible) :=
  { selector := { wire := raw.selectorWire, injective := admissible.selectorInjective }
    data := { wire := raw.dataWire, injective := admissible.dataInjective }
    clock := { wire := raw.clockWire, injective := admissible.clockInjective }
    order := { wire := raw.orderWire, injective := admissible.orderInjective }
    generatorSignal :=
      { wire := raw.generatorSignalWire, injective := admissible.generatorSignalInjective }
    coefficientSignal := raw.coefficientSignal
    orderBoundarySignal := raw.orderBoundarySignal
    projectorSignal := raw.projectorSignal
    clockBoundarySignal := raw.clockBoundarySignal
    workspace := { wire := raw.workspaceWire, injective := admissible.workspaceInjective }
    allWiresNodup := by
      change (List.ofFn raw.selectorWire ++ List.ofFn raw.dataWire ++
        List.ofFn raw.clockWire ++ List.ofFn raw.orderWire ++
        List.ofFn raw.generatorSignalWire ++
        [raw.coefficientSignal, raw.orderBoundarySignal,
          raw.projectorSignal, raw.clockBoundarySignal] ++
        List.ofFn raw.workspaceWire).Nodup
      exact admissible.allWiresNodup }

/-
The next stage is intentionally not fabricated here.  The accepted evidence
constructors require a dependent `Fin.cast` bridge for the Cuccaro tail
registers, and the split establishedBridge contract assigns that semantic bridge to
the next review stage.  This compiled packet records the precise
raw/admissibility boundary while avoiding a false completed proof.
-/

end HistoryRawSchema
