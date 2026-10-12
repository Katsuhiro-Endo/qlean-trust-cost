import QLean.Correspondence.GeneralRepresentationTransport
import QLean.Correspondence.HistoryLinearSystemTransport
import QLean.Correspondence.KernelReflectionTransport
import QLean.Correspondence.BenchmarkHistoryCorrespondence
import QLean.SignalProcessing.JenningsM13AnalyticBounds
import QLean.MathematicalSpecifications.Targets
import QLean.MathematicalSpecifications.TargetReuseProofs
import QLean.Correspondence.CheckpointReadout

/-!
# Parameter-general independent data derived from executable inputs

This module is correspondence code.  It constructs independent mathematical
records from the same freely varying data that emits the primitive circuit;
it does not add a target equality or a circuit-correctness field.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000

namespace QLean.Correspondence.GeneralCheckpointData

open Matrix
open QLean.MathematicalSpecifications
open QLean.MathematicalSpecifications.CoalescingWalkModel
open QLean.MathematicalSpecifications.PublicCheckpoints
open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open ProbabilityGeneratorQProof
open VerifiedCircuitCore
open QLean.Correspondence.CheckpointReadout

noncomputable section

/-- Place every delimiter word in the data register and set every generator
ancilla to zero.  Invalid delimiter words are included, not filtered out. -/
def generatorPhysicalBasis (parameters : CoalescingWalkModel.Parameters)
    (word : Targets.DelimiterWord parameters) :
    QubitBasis (QLean.Circuits.CheckpointCircuits.generatorQubits
      (GeneralRepresentationTransport.parametersToCircuit parameters)) :=
  jointBasisToCore
    (combineBasis
      (allZeroAncilla
        (GeneralRepresentationTransport.parametersToCircuit parameters).ancillaWidth)
      (GeneralRepresentationTransport.delimiterWordEquiv parameters word))

private theorem generatorPhysicalBasis_injective
    (parameters : CoalescingWalkModel.Parameters) :
    Function.Injective (generatorPhysicalBasis parameters) := by
  intro left right equal
  change jointBasisToCore
      (combineBasis
        (allZeroAncilla
          (GeneralRepresentationTransport.parametersToCircuit parameters).ancillaWidth)
        (GeneralRepresentationTransport.delimiterWordEquiv parameters left)) =
    jointBasisToCore
      (combineBasis
        (allZeroAncilla
          (GeneralRepresentationTransport.parametersToCircuit parameters).ancillaWidth)
        (GeneralRepresentationTransport.delimiterWordEquiv parameters right)) at equal
  have jointEqual :
      combineBasis
          (allZeroAncilla
            (GeneralRepresentationTransport.parametersToCircuit parameters).ancillaWidth)
          (GeneralRepresentationTransport.delimiterWordEquiv parameters left) =
        combineBasis
          (allZeroAncilla
            (GeneralRepresentationTransport.parametersToCircuit parameters).ancillaWidth)
          (GeneralRepresentationTransport.delimiterWordEquiv parameters right) := by
    funext wire
    have valueEqual := congrFun equal (wireToCanonicalFin wire)
    simpa [jointBasisToCore] using valueEqual
  apply (GeneralRepresentationTransport.delimiterWordEquiv parameters).injective
  simpa [combineBasis, systemPart] using congrArg systemPart jointEqual

def generatorPhysicalEmbedding (parameters : CoalescingWalkModel.Parameters) :
    Targets.DelimiterWord parameters ↪
      QubitBasis (QLean.Circuits.CheckpointCircuits.generatorQubits
        (GeneralRepresentationTransport.parametersToCircuit parameters)) :=
  ⟨generatorPhysicalBasis parameters, generatorPhysicalBasis_injective parameters⟩

/-- The generator is read on the same delimiter-plus-zero-ancilla placement
at its input and output. -/
def generatorBinding (parameters : CoalescingWalkModel.Parameters) :
    VerifiedMath.BlockReadout.SquareBinding (Targets.DelimiterWord parameters)
      (QubitBasis (QLean.Circuits.CheckpointCircuits.generatorQubits
        (GeneralRepresentationTransport.parametersToCircuit parameters))) where
  inputEmbedding := generatorPhysicalEmbedding parameters
  outputEmbedding := generatorPhysicalEmbedding parameters

/-- The concrete shared-core basis adapter is lossless. -/
theorem coreBasisToJoint_jointBasisToCore
    {ancillaQubits systemQubits : Nat}
    (basis : JointBasis ancillaQubits systemQubits) :
    coreBasisToJoint (jointBasisToCore basis) = basis := by
  funext wire
  simp [coreBasisToJoint, jointBasisToCore]

/-- Reading a zero-ancilla block after transporting a Q-specific operator to
the shared core is exactly the original Q success block.  This small adapter
keeps the public CP01 theorem independent of the internal basis encoding. -/
theorem generatorBlock_reindexJointOperator
    (parameters : CoalescingWalkModel.Parameters)
    (operator : ProbabilityGeneratorQProof.Operator (JointBasis
      (GeneralRepresentationTransport.parametersToCircuit parameters).ancillaWidth
      (GeneralRepresentationTransport.parametersToCircuit parameters).systemWidth)) :
    generatorBlock (generatorBinding parameters)
        (reindexJointOperatorToCanonicalCore operator) =
      fun output input =>
        qubitSuccessBlock
          (allZeroAncilla
            (GeneralRepresentationTransport.parametersToCircuit parameters).ancillaWidth)
          operator
          (GeneralRepresentationTransport.delimiterWordEquiv parameters output)
          (GeneralRepresentationTransport.delimiterWordEquiv parameters input) := by
  funext output input
  simp [generatorBlock, squareBlock, VerifiedMath.BlockReadout.squareBlock,
    generatorBinding, generatorPhysicalEmbedding, generatorPhysicalBasis,
    reindexJointOperatorToCanonicalCore, qubitSuccessBlock,
    jointBasisCoreEquiv]
  simp only [coreBasisToJoint_jointBasisToCore]

/-- The independent lattice parameters carrying exactly the freely varying
`q,K` of an executable history source. -/
def modelParameters (source : AlignedCommonSource119) :
    CoalescingWalkModel.Parameters where
  q := source.qParameters.q
  K := source.qParameters.K
  q_pos := source.qParameters.q_pos
  K_pos := source.qParameters.K_pos

/-- Configuration representation induced solely by the common `q,K`. -/
def configurationEquiv (source : AlignedCommonSource119) :
    CoalescingWalkModel.Configuration (modelParameters source) ≃
      ProbabilityGeneratorQProof.QConfiguration source.qParameters :=
  GeneralRepresentationTransport.configurationEquiv (modelParameters source)

/-- The independent real initial vector represented by the source's exact
rational values. -/
def mathematicalInitial (source : AlignedCommonSource119) :
    CoalescingWalkModel.Configuration (modelParameters source) → ℝ :=
  fun configuration => (source.initial (configurationEquiv source configuration) : ℝ)

/-- Mathematical input represented exactly by an executable common source.
The tolerance is the source's declared scientific state budget. -/
def mathematicalInput (source : AlignedCommonSource119) :
    CoalescingWalkModel.Input (modelParameters source) where
  initial := mathematicalInitial source
  duration := (source.historyParameters.physicalClocks : ℝ) *
    (source.historyParameters.stepSize : ℝ)
  tolerance := source.targetStateError

/-- The independent history-matrix parameters corresponding to the same
source. -/
def historyMatrixParameters (source : AlignedCommonSource119) :
    PublicCheckpoints.HistoryMatrixParameters where
  model := modelParameters source
  clockCount := source.historyParameters.clockEnd
  taylorOrder := source.historyParameters.taylorOrder
  physicalSteps := source.historyParameters.physicalClocks
  orderCount := source.historyParameters.binaryLabels
  step := (source.historyParameters.stepSize : ℝ)

/-- The history range conditions follow from the source's structural
well-formedness, not from circuit correctness. -/
theorem historyMatrixConditions (source : AlignedCommonSource119) :
    PublicCheckpoints.HistoryMatrixConditions (historyMatrixParameters source) where
  order_lt := source.historyWellFormed.2.2.2.1
  physical_pos := source.historyWellFormed.1
  physical_lt := source.historyWellFormed.2.2.2.2

/-- Complete equation data obtained only when the scientific initial state is
needed by the right-hand side.  CP02 itself uses `historyMatrixParameters`
and therefore does not depend on this declaration. -/
def historyEquationData (source : AlignedCommonSource119) :=
  historyDataWithProofs (historyMatrixParameters source)
    (mathematicalInput source) (historyMatrixConditions source).order_lt
    (historyMatrixConditions source).physical_pos
    (historyMatrixConditions source).physical_lt

/-- Enumeration of the independent configuration alphabet by the exact
finite state index used in the executable Jennings system. -/
def stateEquiv (source : AlignedCommonSource119) :
    CoalescingWalkModel.Configuration (modelParameters source) ≃
      Fin (ExecutableD119 source) :=
  (configurationEquiv source).trans
    (Fintype.equivFin
      (ProbabilityGeneratorQProof.QConfiguration source.qParameters))

theorem executable_generator_eq_independent_reindex
    (source : AlignedCommonSource119) :
    (executableSystem119 source).generator =
      (HistoryLinearSystemTransport.toCircuitData
        (stateEquiv source)
        (historyEquationData source)).generator := by
  funext output input
  let outputConfiguration :=
    (Fintype.equivFin
      (ProbabilityGeneratorQProof.QConfiguration source.qParameters)).symm output
  let inputConfiguration :=
    (Fintype.equivFin
      (ProbabilityGeneratorQProof.QConfiguration source.qParameters)).symm input
  let outputMathematical := (configurationEquiv source).symm outputConfiguration
  let inputMathematical := (configurationEquiv source).symm inputConfiguration
  change ((ExecutableHistoryExecutableHistory.commonModelQ119
      source.toCommonSource119 outputConfiguration inputConfiguration : ℚ) : ℝ) =
    CoalescingWalkModel.generator outputMathematical inputMathematical
  have transported :=
    GeneralRepresentationTransport.generator_transport
      (modelParameters source) outputMathematical inputMathematical
  have outputTransport :
      GeneralRepresentationTransport.configurationEquiv
          (modelParameters source) outputMathematical = outputConfiguration :=
    Equiv.apply_symm_apply _ _
  have inputTransport :
      GeneralRepresentationTransport.configurationEquiv
          (modelParameters source) inputMathematical = inputConfiguration :=
    Equiv.apply_symm_apply _ _
  rw [outputTransport, inputTransport] at transported
  unfold ExecutableHistoryExecutableHistory.commonModelQ119
  change
    ((ProbabilityGeneratorQProof.configurationProbabilityGenerator
      outputConfiguration inputConfiguration : ℚ) : ℝ) = _
  exact transported

theorem executable_initial_eq_independent_reindex
    (source : AlignedCommonSource119) :
    (executableSystem119 source).initial =
      (HistoryLinearSystemTransport.toCircuitData
        (stateEquiv source)
        (historyEquationData source)).initial := by
  funext index
  simp only [executableSystem119,
    ExecutableHistoryReferenceM10Bridge.translatedSystem,
    HistoryLinearSystemTransport.toCircuitData, stateEquiv,
    historyEquationData, historyDataWithProofs, historyMatrixDataWithProofs,
    historyMatrixParameters, mathematicalInput, mathematicalInitial]
  let e := GeneralRepresentationTransport.configurationEquiv
    (modelParameters source)
  let f := Fintype.equivFin
    (ProbabilityGeneratorQProof.QConfiguration source.qParameters)
  change ((source.initial (f.symm index) : ℚ) : ℝ) =
    ((source.initial (e ((e.trans f).symm index)) : ℚ) : ℝ)
  change ((source.initial (f.symm index) : ℚ) : ℝ) =
    ((source.initial (e (e.symm (f.symm index))) : ℚ) : ℝ)
  rw [e.apply_symm_apply]

/-- Exact identification of the source-emitted Jennings system with the
independently defined history data, for arbitrary source parameters. -/
theorem executableSystem_eq_independent_reindex
    (source : AlignedCommonSource119) :
    executableSystem119 source =
      HistoryLinearSystemTransport.toCircuitData
        (stateEquiv source)
        (historyEquationData source) := by
  apply QLean.Correspondence.BenchmarkHistoryCorrespondence.historySpec_ext
  · rfl
  · exact executable_generator_eq_independent_reindex source
  · exact executable_initial_eq_independent_reindex source

/-- The independent history-index transport attached to a source. -/
def historyIndexEquiv (source : AlignedCommonSource119) :
    HistoryMatrixIndex (historyMatrixParameters source) ≃
      JenningsHistory.HistoryIndex (ExecutableD119 source)
        (ExecutableC119 source) (ExecutableLabels119 source) :=
  HistoryLinearSystemTransport.indexEquiv (stateEquiv source)

/-- Minimal independent kernel-reflection parameters corresponding to the
same freely varying executable source and its certified spectral scale. -/
def kernelReflectionParameters (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source) :
    PublicCheckpoints.KernelReflectionParameters where
  toHistoryMatrixParameters := historyMatrixParameters source
  input := mathematicalInput source
  alphaH := executableAlpha119 source
  nu := assumptions.nu

/-- Independent kernel conditions are consequences of the executable
scientific assumptions after exact representation transport. -/
theorem kernelReflectionConditions (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source) :
    PublicCheckpoints.KernelReflectionConditions
      (kernelReflectionParameters source assumptions) where
  toHistoryMatrixConditions := historyMatrixConditions source
  initial_nonzero := by
    intro mathematicalInitialZero
    dsimp only [kernelReflectionParameters, historyMatrixParameters,
      mathematicalInput] at mathematicalInitialZero
    apply assumptions.sourceInitial_nonzero
    funext executableConfiguration
    have atConfiguration := congrFun mathematicalInitialZero
      ((configurationEquiv source).symm executableConfiguration)
    have castZero : ((source.initial executableConfiguration : ℚ) : ℝ) = 0 := by
      dsimp only [mathematicalInitial] at atConfiguration
      rw [Equiv.apply_symm_apply] at atConfiguration
      change ((source.initial executableConfiguration : ℚ) : ℝ) = 0 at atConfiguration
      exact atConfiguration
    change source.initial executableConfiguration = (0 : ℚ)
    exact_mod_cast castZero
  alphaH_pos := assumptions.hAlphaPos
  nu_pos := assumptions.hNuPos
  kernel_invertible := by
    let data := historyEquationData source
    apply QLean.Correspondence.KernelReflectionTransport.independentInvertibility
      (stateEquiv source) data (executableAlpha119 source) assumptions.nu
    rw [← executableSystem_eq_independent_reindex source]
    exact assumptions.hdet

/-- Independent and executable scalar-extended coordinates. -/
def extendedIndexEquiv (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source) :
    PublicCheckpoints.KernelExtendedIndex
        (kernelReflectionParameters source assumptions) ≃
      GramOperator.ExtendedIndex (ExecutableD119 source)
        (ExecutableC119 source) (ExecutableLabels119 source) :=
  QLean.Correspondence.KernelReflectionTransport.extendedIndexEquiv
    (stateEquiv source)

/-- Exact representation equality between the executable ideal reflection
and the independent target built from the same source, alpha, and nu. -/
theorem executableIdealReflection_eq_independent_reindex
    (source : AlignedCommonSource119)
    (assumptions : ExecutableM13Assumptions119 source) :
    GramOperator.idealKernelReflection (executableSystem119 source)
        (executableAlpha119 source) assumptions.nu assumptions.hdet =
      Matrix.reindexAlgEquiv ℝ ℝ (extendedIndexEquiv source assumptions)
        (Targets.kernelReflectionMatrix
          (kernelReflectionParameters source assumptions)
          (kernelReflectionConditions source assumptions)) := by
  rw [Targets.kernelReflectionMatrix_eq_kernelReflectionFor]
  let data := historyEquationData source
  exact QLean.Correspondence.KernelReflectionTransport.idealReflection_eq_reindex_of_data_eq
    (stateEquiv source) data (executableSystem119 source)
      (executableAlpha119 source) assumptions.nu
      (executableSystem_eq_independent_reindex source) assumptions.hdet
      (kernelReflectionConditions source assumptions).kernel_invertible

end

end QLean.Correspondence.GeneralCheckpointData
