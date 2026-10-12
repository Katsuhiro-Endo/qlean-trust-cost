import QLean.Generator.Analysis.UnderstandingSpecifications
import QLean.Spectral.Analysis.ControlledSubcircuit
import QLean.Spectral.Analysis.HistoryBlock

/-!
# Human-facing mathematical specifications for H1--H4

The history system is specified independently of circuit syntax.  H1 is the
selector preparation, H2 is the Taylor/probability-generator block with one
distinguished externally-controlled Q10 child, H3 is the seven-stage
clock/idling block, and H4 is the source-faithful product
`H1; H2; H3; H1⁻¹`.

The Q10 source operator, its placed full-dirty controlled extension, and its
clean-work controlled meaning are deliberately separate objects.
-/

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-! ## H1 selector preparation -/

/-- Mathematical data needed by the two-wire history-selector preparation. -/
structure H1SelectorUnderstandingSpecification (qubits : Nat) where
  symbolValue : String → ℝ
  parameters : HistorySelectorPreparationParameters qubits

/-- H1 recorded target in source execution order. -/
def h1SelectorRecordedOperator {qubits : Nat}
    (spec : H1SelectorUnderstandingSpecification qubits) :
    Operator (QubitBasis qubits) :=
  historySelectorPreparationOperator spec.symbolValue spec.parameters

/-! ## H2 distinguished controlled-Q10 child -/

/--
Pure placement contract for the one controlled-Q10 occurrence in H2.

The source plan must equal Q10 after the explicitly supplied mathematical
change of basis.  The placed source-wire order is split into Q signal,
Q generator-work, and Q system/data regions.  The external control and the
two compiler-work wires are properties of `layout`, not implicit conventions.
-/
structure H2ControlledQ10UnderstandingSpecification (targetQubits : Nat) where
  p : ProbabilityGeneratorQProof.QParameters
  symbolValue : String → ℝ
  layout : ExternallyControlledCircuitLayout
    (p.ancillaWidth + p.systemWidth) targetQubits
  cleanWorkValid : layout.CleanWorkValid
  plan : List
    (ExternallyControlledPrimitivePlan (p.ancillaWidth + p.systemWidth))
  sourceReindex :
    Operator (ProbabilityGeneratorQProof.JointBasis
      p.ancillaWidth p.systemWidth) →
      Operator (QubitBasis (p.ancillaWidth + p.systemWidth))
  sourcePlan_eq_q10 :
    r12ControlledSubcircuitSourceOperator symbolValue plan =
      sourceReindex
        (ProbabilityGeneratorQProof.q10ProbabilityGeneratorRecordedOperator p)
  sourceInputPredicate : QubitBasis (p.ancillaWidth + p.systemWidth) → Prop
  sourceOutputPredicate : QubitBasis (p.ancillaWidth + p.systemWidth) → Prop
  sourceInputImpliesOutput : ∀ basis,
    sourceInputPredicate basis → sourceOutputPredicate basis
  sourceBoundary : ∀ input output,
    sourceInputPredicate input → ¬ sourceOutputPredicate output →
      r12ControlledSubcircuitSourceOperator symbolValue plan output input = 0
  signalWires : List (Fin targetQubits)
  generatorWorkWires : List (Fin targetQubits)
  dataWires : List (Fin targetQubits)
  signalWires_length : signalWires.length = p.generatorSignalWidth
  generatorWorkWires_length : generatorWorkWires.length = p.generatorWorkWidth
  dataWires_length : dataWires.length = p.generatorDataWidth
  placementSourceOrder : List.ofFn layout.placement =
    signalWires ++ generatorWorkWires ++ dataWires

/-- Clean-work semantic external-control target on the same placement. -/
def h2ControlledQ10CleanOperator {targetQubits : Nat}
    (spec : H2ControlledQ10UnderstandingSpecification targetQubits) :
    Operator (QubitBasis targetQubits) :=
  r12ControlledSubcircuitCleanOperator
    spec.symbolValue spec.layout spec.plan

/-- The exact common input/output predicate for the controlled-Q10 work. -/
def h2ControlledQ10CleanPredicate {targetQubits : Nat}
    (spec : H2ControlledQ10UnderstandingSpecification targetQubits)
    (basis : QubitBasis targetQubits) : Prop :=
  externallyControlledCleanWorkPredicate spec.cleanWorkValid basis

/-- The full placed Q11 all-zero ancilla input boundary, factored into the
signal input sector and the internally restored generator-work sector. -/
def h2ControlledQ10BlockEncodingInputPredicate {targetQubits : Nat}
    (spec : H2ControlledQ10UnderstandingSpecification targetQubits)
    (basis : QubitBasis targetQubits) : Prop :=
  spec.sourceInputPredicate
    (restrictToPlacedWires spec.layout.placement basis)

/-- Complete coherent input boundary of the controlled-Q10 child. -/
def h2ControlledQ10IdealInputPredicate {targetQubits : Nat}
    (spec : H2ControlledQ10UnderstandingSpecification targetQubits)
    (basis : QubitBasis targetQubits) : Prop :=
  h2ControlledQ10CleanPredicate spec basis ∧
    h2ControlledQ10BlockEncodingInputPredicate spec basis

/-! ## H2 Taylor/probability-generator block -/

/--
The post-generator half of H2 is not one opaque stage list.  Its eight fields
are the independently reviewable source-level groups at Python lines 696--807.
Each group still retains its dirty and clean stage targets; flattening is a
derived compatibility view used only by the existing sequence component.
-/
structure H2TaylorPostGeneratorUnderstandingSpecification (qubits : Nat) where
  /-- Uncompute the active control used by the unique controlled-Q10 call. -/
  restoreGeneratorActive :
    List (HistoryTaylorAuxStageSpec (QubitBasis qubits))
  /-- Mark an invalid clock value in the coefficient signal. -/
  invalidClockSignal :
    List (HistoryTaylorAuxStageSpec (QubitBasis qubits))
  /-- Compute the Taylor-order boundary contribution. -/
  orderBoundarySignal :
    List (HistoryTaylorAuxStageSpec (QubitBasis qubits))
  /-- Compute the idle-block boundary contribution. -/
  idleBoundarySignal :
    List (HistoryTaylorAuxStageSpec (QubitBasis qubits))
  /-- Conditionally increment the Taylor degree/order register. -/
  degreeIncrement :
    List (HistoryTaylorAuxStageSpec (QubitBasis qubits))
  /-- The finite Taylor-coefficient controlled-rotation loop. -/
  taylorCoefficientRotations :
    List (HistoryTaylorAuxStageSpec (QubitBasis qubits))
  /-- The single idling-coefficient controlled rotation. -/
  idleCoefficientRotation :
    List (HistoryTaylorAuxStageSpec (QubitBasis qubits))
  /-- Uncompute the two clock predicates and selector equality flag. -/
  restoreEntryFlags :
    List (HistoryTaylorAuxStageSpec (QubitBasis qubits))
  /-- Clean mathematical action of `restoreGeneratorActive`. -/
  restoreGeneratorActiveClean : Operator (QubitBasis qubits)
  /-- Clean mathematical action of `invalidClockSignal`. -/
  invalidClockSignalClean : Operator (QubitBasis qubits)
  /-- Clean mathematical action of `orderBoundarySignal`. -/
  orderBoundarySignalClean : Operator (QubitBasis qubits)
  /-- Clean mathematical action of `idleBoundarySignal`. -/
  idleBoundarySignalClean : Operator (QubitBasis qubits)
  /-- Clean mathematical action of `degreeIncrement`. -/
  degreeIncrementClean : Operator (QubitBasis qubits)
  /-- Clean mathematical action of `taylorCoefficientRotations`. -/
  taylorCoefficientRotationsClean : Operator (QubitBasis qubits)
  /-- Clean mathematical action of `idleCoefficientRotation`. -/
  idleCoefficientRotationClean : Operator (QubitBasis qubits)
  /-- Clean mathematical action of `restoreEntryFlags`. -/
  restoreEntryFlagsClean : Operator (QubitBasis qubits)

/-- Eight clean group targets in human source order. -/
def H2TaylorPostGeneratorUnderstandingSpecification.cleanSourceOperators
    {qubits : Nat}
    (spec : H2TaylorPostGeneratorUnderstandingSpecification qubits) :
    List (Operator (QubitBasis qubits)) :=
  [spec.restoreGeneratorActiveClean,
   spec.invalidClockSignalClean,
   spec.orderBoundarySignalClean,
   spec.idleBoundarySignalClean,
   spec.degreeIncrementClean,
   spec.taylorCoefficientRotationsClean,
   spec.idleCoefficientRotationClean,
   spec.restoreEntryFlagsClean]

/--
Human-facing H2 plan.  The controlled-Q10 node occurs exactly once between
the pre-generator list and the nested post-generator specification.
-/
structure H2TaylorUnderstandingSpecification (qubits : Nat) where
  beforeControlledQ10 : List (HistoryTaylorAuxStageSpec (QubitBasis qubits))
  controlledQ10 : H2ControlledQ10UnderstandingSpecification qubits
  postGenerator : H2TaylorPostGeneratorUnderstandingSpecification qubits
  /-- Boundary condition for P40/P41/P42/P43/P50 auxiliary work and live
  flags.  It is intentionally independent of Q10 compiler/internal work,
  which is specified by `controlledQ10`. -/
  auxiliaryBoundaryPredicate : QubitBasis qubits → Prop
  /-- Auxiliary boundary after selector equality (P40). -/
  afterSelectorPredicate : QubitBasis qubits → Prop
  /-- Auxiliary boundary after `clock < timeSteps` (first P41). -/
  afterTimeComparisonPredicate : QubitBasis qubits → Prop
  /-- Auxiliary boundary after `clock < idleEnd` (second P41). -/
  afterIdleEndComparisonPredicate : QubitBasis qubits → Prop
  /-- Source-reachable P15 predicate immediately before and after the unique
  controlled-Q10 occurrence.  Unlike `auxiliaryBoundaryPredicate`, it records
  the live branch/clock/active flags computed by the before list.  Q10 reads
  the active flag but preserves this predicate; the after list uncomputes it
  back to the public auxiliary boundary. -/
  centralAuxiliaryPredicate : QubitBasis qubits → Prop
  /-- Stable auxiliary boundary used between the eight post-generator
  groups after the Q10 active flag has been uncomputed. -/
  postGeneratorStablePredicate : QubitBasis qubits → Prop

/-- H2 clean source list.  The auxiliary mathematical stages are unchanged;
the unique Q10 occurrence is replaced by its clean-work controlled meaning. -/
def h2TaylorCleanSourceOperators {qubits : Nat}
    (spec : H2TaylorUnderstandingSpecification qubits) :
    List (Operator (QubitBasis qubits)) :=
  spec.beforeControlledQ10.map HistoryTaylorAuxStageSpec.cleanTarget ++
    [h2ControlledQ10CleanOperator spec.controlledQ10] ++
    spec.postGenerator.cleanSourceOperators

/-- Clean H2 operator, still with exactly one controlled-Q10 occurrence. -/
def h2TaylorCleanOperator {qubits : Nat}
    (spec : H2TaylorUnderstandingSpecification qubits) :
    Operator (QubitBasis qubits) :=
  operatorSequence (h2TaylorCleanSourceOperators spec)

/-- H2 inputs on which the controlled-Q10 child may additionally be read via
the Q11 success block.  Compiler work and Q internal work are restored; only
the signal-prefix zero condition is added at the input boundary. -/
def h2TaylorIdealInputPredicate {qubits : Nat}
    (spec : H2TaylorUnderstandingSpecification qubits)
    (basis : QubitBasis qubits) : Prop :=
  h2ControlledQ10IdealInputPredicate spec.controlledQ10 basis ∧
    spec.auxiliaryBoundaryPredicate basis

/-! ## H3 clock/idling block -/

/-! ## H4 full history block -/

end

end SpectralSamplingProof.Analytic
