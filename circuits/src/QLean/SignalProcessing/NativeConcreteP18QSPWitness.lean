import QLean.SignalProcessing.RootConcreteImagePhaseLayout
import QLean.SignalProcessing.NativeEmbeddingImagePhaseP18
import QLean.Circuits.NativeFixedPointPrimitive
import QLean.SignalProcessing.NativeSignalQSVTActual
import QLean.SignalProcessing.KernelQSPGeneralQSPIntegration
import QLean.Spectral.Analysis.SignalTransformQSPExistenceSpecifications
import QLean.SignalProcessing.NativeQSPWitnessTwoFrameModel
import QLean.SignalProcessing.NativeSingularPairTwoFrame

/-!
# Concrete widened primitive compiler for a P18 two-frame QSP witness

The old register is the actual P18 signal register. It is embedded as the
first block of a new `n + (n + 1)` register, whose remaining wires implement
the exact finite-image source/target projector phases. This module proves
only source-order circuit and denotation facts; it deliberately does not claim
the missing physical two-frame intertwining for P18.
-/

namespace NativeConcreteP18QSPWitness

open VerifiedCircuitCore
open VerifiedCircuitCore.NativeEmbeddingImagePhase
open NativeSignalQSVTActual
open SpectralSamplingProof.Analytic
open NativeQSPWitnessTwoFrameModel
open NativeQSPWitnessTransferModel
open NativeSingularPairTwoFrame

noncomputable section

/-- The same basis-ket action before specializing the old-register input to
the selected image. -/
theorem standardEmbeddingImagePhaseCircuit_apply_clean_basisKet_of_input
    {β : Type*} [Fintype β] [DecidableEq β] {n : Nat}
    (symbolValue : String → ℝ) (embedding : β ↪ QubitBasis n)
    (angle : ℝ) (input : QubitBasis n) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (standardEmbeddingImagePhaseCircuit embedding angle))
        (basisKet
          (fixedOutsideBasisEmbedding (standardImagePhasePlacement n)
            (fun _ => false) input)) =
      (if ∃ logical : β, input = embedding logical then
        Complex.exp (Complex.I * (angle : ℂ)) else 1) •
        basisKet
          (fixedOutsideBasisEmbedding (standardImagePhasePlacement n)
            (fun _ => false) input) := by
  unfold standardEmbeddingImagePhaseCircuit
  rw [embeddingImagePhaseCircuit_apply_basisKet symbolValue
    (standardImagePhasePlacement n) embedding
    (standardImagePhaseScratches n) (standardImagePhaseFlag n) angle
    (fixedOutsideBasisEmbedding (standardImagePhasePlacement n)
      (fun _ => false) input)]
  · simp [fixedOutsideBasisEmbedding]
  · intro controls member
    exact standardImagePhase_enoughScratch embedding member
  · intro controls member
    exact standardImagePhase_layoutNodup embedding member
  · exact standardImagePhaseFlag_outside_scratches n
  · intro wire member
    exact fixedOutsideBasisEmbedding_zero_apply_outside
      (standardImagePhasePlacement n) input wire
      (fun source => standardImagePhaseScratches_outside n wire member source)
  · exact fixedOutsideBasisEmbedding_zero_apply_outside
      (standardImagePhasePlacement n) input (standardImagePhaseFlag n)
      (fun source => standardImagePhaseFlag_outside n source)

theorem fixedOutsideStateEmbedding_smul119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool) (scalar : ℂ)
    (state : State (QubitBasis sourceQubits)) :
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

theorem fixedOutsideStateEmbedding_finset_sum119
    {sourceQubits targetQubits : Nat} {ι : Type*} [DecidableEq ι]
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (outside : OutsideWire placement → Bool) (terms : Finset ι)
    (states : ι → State (QubitBasis sourceQubits)) :
    fixedOutsideStateEmbedding placement outside (∑ item ∈ terms, states item) =
      ∑ item ∈ terms, fixedOutsideStateEmbedding placement outside (states item) := by
  induction terms using Finset.induction_on with
  | empty =>
      funext basis
      simp [fixedOutsideStateEmbedding]
  | @insert item terms absent inductionHypothesis =>
      rw [Finset.sum_insert absent, Finset.sum_insert absent,
        fixedOutsideStateEmbedding_add119, inductionHypothesis]

theorem applyOperator_finset_sum119 {basis ι : Type*}
    [Fintype basis] [DecidableEq basis] [DecidableEq ι]
    (operator : Operator basis) (terms : Finset ι) (states : ι → State basis) :
    applyOperator operator (∑ item ∈ terms, states item) =
      ∑ item ∈ terms, applyOperator operator (states item) := by
  induction terms using Finset.induction_on with
  | empty => simp [applyOperator_zero]
  | @insert item terms absent inductionHypothesis =>
      rw [Finset.sum_insert absent, Finset.sum_insert absent,
        applyOperator_add, inductionHypothesis]

theorem state_eq_sum_smul_basisKet119 {basis : Type*}
    [Fintype basis] [DecidableEq basis] (state : State basis) :
    state = ∑ input : basis, state input • basisKet input := by
  ext output
  simp [basisKet]

theorem sourceImagePhaseOperator_apply_basisKet119
    {β : Type*} [Fintype β] [DecidableEq β] {n : Nat}
    (embedding : β ↪ QubitBasis n) (angle : ℝ) (input : QubitBasis n) :
    applyOperator (sourceImagePhaseOperator embedding angle) (basisKet input) =
      (if ∃ logical : β, input = embedding logical then
        Complex.exp (Complex.I * (angle : ℂ)) else 1) • basisKet input := by
  ext output
  rw [applyOperator_basisKet]
  by_cases equal : output = input
  · subst output
    simp [sourceImagePhaseOperator, basisKet]
  · simp [sourceImagePhaseOperator, basisKet, equal]

/-- The independently defined source-image phase is precisely the generic
projector phase for its computational-basis embedding. -/
theorem sourceImagePhaseOperator_eq_imagePhaseOperator_basisKetEmbedding119
    {β : Type*} [Fintype β] [DecidableEq β] {n : Nat}
    (embedding : β ↪ QubitBasis n) (angle : ℝ) :
    sourceImagePhaseOperator embedding angle =
      imagePhaseOperator (basisKetEmbeddingMatrix embedding) angle := by
  classical
  ext output input
  unfold imagePhaseOperator sourceImagePhaseOperator
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [cleanProjector_basisKetEmbeddingMatrix_entry]
  by_cases same : output = input
  · subst output
    by_cases inside : ∃ logical : β, input = embedding logical
    · simp [inside]
    · simp [inside]
  · simp [same]

/-- On the entire clean added-ancilla subspace, the primitive standard phase
is exactly the old-register independent image-phase operator. -/
theorem standardEmbeddingImagePhaseCircuit_apply_clean_fixedOutsideState
    {β : Type*} [Fintype β] [DecidableEq β] {n : Nat}
    (symbolValue : String → ℝ) (embedding : β ↪ QubitBasis n)
    (angle : ℝ) (state : State (QubitBasis n)) :
    applyOperator
        (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
          (standardEmbeddingImagePhaseCircuit embedding angle))
        (fixedOutsideStateEmbedding (standardImagePhasePlacement n)
          (fun _ => false) state) =
      fixedOutsideStateEmbedding (standardImagePhasePlacement n)
        (fun _ => false)
        (applyOperator (sourceImagePhaseOperator embedding angle) state) := by
  classical
  let phase : QubitBasis n → ℂ := fun input =>
    if ∃ logical : β, input = embedding logical then
      Complex.exp (Complex.I * (angle : ℂ)) else 1
  have expansion : state = ∑ input : QubitBasis n, state input • basisKet input :=
    state_eq_sum_smul_basisKet119 state
  nth_rewrite 1 [expansion]
  rw [fixedOutsideStateEmbedding_finset_sum119]
  simp_rw [fixedOutsideStateEmbedding_smul119]
  rw [applyOperator_finset_sum119]
  simp_rw [applyOperator_smul]
  calc
    ∑ input, state input •
        applyOperator
          (Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
            (standardEmbeddingImagePhaseCircuit embedding angle))
          (fixedOutsideStateEmbedding (standardImagePhasePlacement n)
            (fun _ => false) (basisKet input)) =
        ∑ input, state input •
          (phase input • fixedOutsideStateEmbedding (standardImagePhasePlacement n)
            (fun _ => false) (basisKet input)) := by
          apply Finset.sum_congr rfl
          intro input _
          rw [fixedOutsideStateEmbedding_basisKet]
          rw [standardEmbeddingImagePhaseCircuit_apply_clean_basisKet_of_input
            symbolValue embedding angle input]
    _ = ∑ input, state input •
          fixedOutsideStateEmbedding (standardImagePhasePlacement n)
            (fun _ => false) (phase input • basisKet input) := by
          apply Finset.sum_congr rfl
          intro input _
          rw [fixedOutsideStateEmbedding_smul119]
    _ = fixedOutsideStateEmbedding (standardImagePhasePlacement n)
          (fun _ => false)
          (∑ input, state input • (phase input • basisKet input)) := by
          rw [fixedOutsideStateEmbedding_finset_sum119]
          simp_rw [fixedOutsideStateEmbedding_smul119]
    _ = fixedOutsideStateEmbedding (standardImagePhasePlacement n)
          (fun _ => false)
          (∑ input, state input •
            applyOperator (sourceImagePhaseOperator embedding angle)
              (basisKet input)) := by
          apply congrArg (fixedOutsideStateEmbedding
            (standardImagePhasePlacement n) (fun _ => false))
          apply Finset.sum_congr rfl
          intro input _
          rw [sourceImagePhaseOperator_apply_basisKet119]
    _ = fixedOutsideStateEmbedding (standardImagePhasePlacement n)
          (fun _ => false)
          (applyOperator (sourceImagePhaseOperator embedding angle)
            (∑ input, state input • basisKet input)) := by
          congr 1
          rw [applyOperator_finset_sum119]
          simp_rw [applyOperator_smul]
    _ = fixedOutsideStateEmbedding (standardImagePhasePlacement n)
          (fun _ => false)
          (applyOperator (sourceImagePhaseOperator embedding angle) state) := by
          exact congrArg
            (fun current => fixedOutsideStateEmbedding
              (standardImagePhasePlacement n) (fun _ => false)
              (applyOperator (sourceImagePhaseOperator embedding angle) current))
            expansion.symm

/-- Wire lifting commutes with the linear embedding into a fixed clean added
ancilla block.  This is a full-state statement, not merely an entrywise clean
compression. -/
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

/-- The concrete widened width attached to the actual P18 signal register. -/
abbrev widenedP18Qubits119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) : Nat :=
  let n := ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource
  n + (n + 1)

/-- The finite clean coordinate space of the actual P18 signal block. -/
abbrev executableSignalCleanIndex119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119) :=
  GramOperator.ExtendedIndex (ExecutableHistoryExecutableP18.ExecutableD119 source)
    (ExecutableHistoryExecutableP18.ExecutableC119 source)
    (ExecutableHistoryExecutableP18.ExecutableLabels119 source)

/-- The source signal-zero computational-basis embedding, regarded as its
canonical linear isometry. -/
def executableSignalSourceKetEmbedding119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) :
    Matrix (QubitBasis (ExecutableSignalP18Qubits119 source domain fits assumptions
      circuitSource)) (executableSignalCleanIndex119 source) ℂ :=
  basisKetEmbeddingMatrix
    (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)

/-- Complex form of the actual P18 clean block `gNu`. -/
def executableGNuOperator119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source) :
    Operator (executableSignalCleanIndex119 source) :=
  fun output input =>
    (GramOperator.gNuOperator (ExecutableHistoryExecutableP18.executableSystem119 source)
      (ExecutableHistoryExecutableP18.executableAlpha119 source) assumptions.nu output input : ℂ)

theorem executableSignalSourceKetEmbedding119_isometry
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) :
    Matrix.conjTranspose
        (executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource) *
      executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource = 1 :=
  basisKetEmbeddingMatrix_isometry
    (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)

/-- The mathematical singular-pair data required for the strict branch of the
actual P18 clean block.  It records only singular equations for the proved
`gNu` compression; it adds no cross-image or dilation witness. -/
structure ExecutableP18StrictSingularPair119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source) where
  sigma : ℝ
  g : ℝ
  v : Column (executableSignalCleanIndex119 source)
  u : Column (executableSignalCleanIndex119 source)
  singular_forward : (executableGNuOperator119 source assumptions).mulVec v =
    (sigma : ℂ) • u
  singular_adjoint :
    (Matrix.conjTranspose (executableGNuOperator119 source assumptions)).mulVec u =
      (sigma : ℂ) • v
  sigma_nonneg : 0 ≤ sigma
  g_nonneg : 0 ≤ g
  completion : g ^ 2 + sigma ^ 2 = 1
  g_ne_zero : g ≠ 0

/-- Actual P18 signal circuit, wire-lifted into the concrete standard layout. -/
def widenedSignalCircuit119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) :
    Circuit (PrimitiveGate (widenedP18Qubits119 source domain fits assumptions
      circuitSource)) :=
  executableSignalP18WireLiftCircuit119 source domain fits assumptions circuitSource
    (standardImagePhasePlacement
      (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))

/-- Concrete exact source-projector phase on the signal-zero physical image. -/
def widenedSourcePhase119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) (angle : ℝ) :
    Circuit (PrimitiveGate (widenedP18Qubits119 source domain fits assumptions
      circuitSource)) :=
  standardEmbeddingImagePhaseCircuit
    (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
    angle

/-- Concrete exact target-role phase on the same clean signal-zero image.
In the square two-frame block encoding the roles differ by frame ordering, not
by the physical image on which the projector acts. -/
def widenedTargetPhase119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) (angle : ℝ) :
    Circuit (PrimitiveGate (widenedP18Qubits119 source domain fits assumptions
      circuitSource)) :=
  standardEmbeddingImagePhaseCircuit
    (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
    angle

/-- One source-order role-aware QSP instruction compiled to the concrete
widened primitive register. -/
def widenedStep119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions) :
    FixedPointRoleAwarePhaseStep ->
      Circuit (PrimitiveGate (widenedP18Qubits119 source domain fits assumptions
        circuitSource))
  | .signal .forward =>
      widenedSignalCircuit119 source domain fits assumptions circuitSource
  | .signal .adjoint =>
      (widenedSignalCircuit119 source domain fits assumptions circuitSource).reverse
        PrimitiveGate.inverse
  | .projectorPhase .source angle =>
      widenedSourcePhase119 source domain fits assumptions circuitSource angle
  | .projectorPhase .target angle =>
      widenedTargetPhase119 source domain fits assumptions circuitSource angle

/-- Ambient operator of one widened primitive step. -/
def widenedStepOperator119
    (symbolValue : String -> ℝ)
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions)
    (step : FixedPointRoleAwarePhaseStep) :
    Operator (QubitBasis (widenedP18Qubits119 source domain fits assumptions
      circuitSource)) :=
  Circuit.denote (primitiveGateOperatorWithSymbols symbolValue)
    (widenedStep119 source domain fits assumptions circuitSource step)

/-- Taking a wire lift commutes with conjugate transpose. -/
theorem star_wireLiftOperator119
    {sourceQubits targetQubits : Nat}
    (placement : Fin sourceQubits ↪ Fin targetQubits)
    (operator : Operator (QubitBasis sourceQubits)) :
    star (wireLiftOperator placement operator) =
      wireLiftOperator placement (star operator) := by
  classical
  ext output input
  by_cases outsideEqual :
      restrictToOutsideWires placement output =
        restrictToOutsideWires placement input
  · simp [wireLiftOperator_apply, outsideEqual]
  · simp [wireLiftOperator_apply, outsideEqual]
    intro h
    exact (outsideEqual h.symm).elim

/-- Apply the standard zero-added-ancilla lift to every column of a two-frame
matrix. -/
def widenedFrameLift119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions)
    (frame : Matrix
      (QubitBasis (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (Fin 2) ℂ) :
    Matrix (QubitBasis (widenedP18Qubits119 source domain fits assumptions
      circuitSource)) (Fin 2) ℂ :=
  fun output column =>
    fixedOutsideStateEmbedding
      (standardImagePhasePlacement
        (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (fun _ => false) (fun input => frame input column) output

/-- The zero-added-ancilla lift is linear in the two frame columns, including
right multiplication by a transfer matrix. -/
theorem widenedFrameLift119_mul
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions)
    (frame : Matrix
      (QubitBasis (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (Fin 2) ℂ)
    (right : Matrix (Fin 2) (Fin 2) ℂ) :
    widenedFrameLift119 source domain fits assumptions circuitSource (frame * right) =
      widenedFrameLift119 source domain fits assumptions circuitSource frame * right := by
  classical
  ext output column
  by_cases outsideClean :
      restrictToOutsideWires
        (standardImagePhasePlacement
          (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
        output = (fun _ => false)
  · simp [widenedFrameLift119, fixedOutsideStateEmbedding, Matrix.mul_apply,
      outsideClean]
  · simp [widenedFrameLift119, fixedOutsideStateEmbedding, Matrix.mul_apply,
      outsideClean]

/-- The concrete source-role primitive phase acts on every lifted frame
column as the old-register source-image phase. -/
theorem widenedSourcePhase_mul_widenedFrameLift119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions)
    (angle : ℝ)
    (frame : Matrix
      (QubitBasis (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (Fin 2) ℂ) :
    widenedStepOperator119 (fun _ : String => 0) source domain fits assumptions
        circuitSource (.projectorPhase .source angle) *
      widenedFrameLift119 source domain fits assumptions circuitSource frame =
      widenedFrameLift119 source domain fits assumptions circuitSource
        (sourceImagePhaseOperator
          (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
          angle * frame) := by
  unfold widenedStepOperator119 widenedStep119 widenedSourcePhase119
  ext output column
  change applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ : String => 0))
        (standardEmbeddingImagePhaseCircuit
          (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
          angle))
      (fixedOutsideStateEmbedding
        (standardImagePhasePlacement
          (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
        (fun _ => false) (fun input => frame input column)) output = _
  rw [standardEmbeddingImagePhaseCircuit_apply_clean_fixedOutsideState]
  rfl

/-- The target-role primitive uses the same physical clean image and hence
has the same lifted old-register action; the target role is represented by
the target-frame column ordering. -/
theorem widenedTargetPhase_mul_widenedFrameLift119
    (source : ExecutableHistoryExecutableHistory.AlignedCommonSource119)
    (domain : ExecutableHistoryExecutableHistory.ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (assumptions : ExecutableHistoryExecutableP18.ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableHistoryExecutableP18.ExecutableP18CircuitSource119
      source domain fits assumptions)
    (angle : ℝ)
    (frame : Matrix
      (QubitBasis (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
      (Fin 2) ℂ) :
    widenedStepOperator119 (fun _ : String => 0) source domain fits assumptions
        circuitSource (.projectorPhase .target angle) *
      widenedFrameLift119 source domain fits assumptions circuitSource frame =
      widenedFrameLift119 source domain fits assumptions circuitSource
        (sourceImagePhaseOperator
          (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
          angle * frame) := by
  unfold widenedStepOperator119 widenedStep119 widenedTargetPhase119
  ext output column
  change applyOperator
      (Circuit.denote (primitiveGateOperatorWithSymbols (fun _ : String => 0))
        (standardEmbeddingImagePhaseCircuit
          (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource)
          angle))
      (fixedOutsideStateEmbedding
        (standardImagePhasePlacement
          (ExecutableSignalP18Qubits119 source domain fits assumptions circuitSource))
        (fun _ => false) (fun input => frame input column)) output = _
  rw [standardEmbeddingImagePhaseCircuit_apply_clean_fixedOutsideState]
  rfl

/-- On the abstract strict pair, the common clean-image phase gives the
source-role diagonal action: it phases `S0` and fixes `S1`. -/
theorem strictFrame_source_phase119 {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    [DecidableEq (Fin 2)] (data : StrictSingularPairData basis clean)
    (angle : ℝ) :
    imagePhaseOperator data.E angle * sourceFrame data =
      sourceFrame data * fixedPointProjectorTransferMatrix .source angle := by
  unfold sourceFrame
  rw [operator_mul_twoColumnFrame,
    imagePhase_apply_of_projector_one data.E angle (sourceZero data)
      (cleanProjector_sourceZero data),
    imagePhase_apply_of_projector_zero data.E angle (sourceOne data)
      (cleanProjector_sourceOne_zero data)]
  ext output column
  fin_cases column <;>
    simp [twoColumnFrame, fixedPointProjectorTransferMatrix, Matrix.mul_apply,
      fixedPointSourceIndex, mul_comm]

/-- The same physical clean-image phase gives the target-role diagonal
action after the target frame reverses the two column roles. -/
theorem strictFrame_target_phase119 {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    [DecidableEq (Fin 2)] (data : StrictSingularPairData basis clean)
    (angle : ℝ) :
    imagePhaseOperator data.E angle * targetFrame data =
      targetFrame data * fixedPointProjectorTransferMatrix .target angle := by
  unfold targetFrame
  rw [operator_mul_twoColumnFrame,
    imagePhase_apply_of_projector_zero data.E angle (targetZero data)
      (cleanProjector_targetZero_zero data),
    imagePhase_apply_of_projector_one data.E angle (targetOne data)
      (cleanProjector_targetOne data)]
  ext output column
  fin_cases column <;>
    simp [twoColumnFrame, fixedPointProjectorTransferMatrix, Matrix.mul_apply,
      fixedPointTargetIndex, mul_comm]

/-- In the strict branch, the target amplitude of the canonical transfer
matrix is the chosen nonnegative singular value. -/
theorem fixedPointTargetAmplitude_strictPair119
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    fixedPointTargetAmplitude (pair.sigma ^ 2) = pair.sigma := by
  unfold fixedPointTargetAmplitude
  rw [max_eq_right (sq_nonneg pair.sigma)]
  simpa [abs_of_nonneg pair.sigma_nonneg] using
    (Real.sqrt_sq_eq_abs pair.sigma)

/-- Completion and the nonnegative complementary amplitude identify the
source amplitude of the canonical transfer matrix. -/
theorem fixedPointSourceAmplitude_strictPair119
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    fixedPointSourceAmplitude (pair.sigma ^ 2) = pair.g := by
  have complementary : 1 - pair.sigma ^ 2 = pair.g ^ 2 := by
    nlinarith [pair.completion]
  unfold fixedPointSourceAmplitude
  rw [complementary, max_eq_right (sq_nonneg pair.g)]
  simpa [abs_of_nonneg pair.g_nonneg] using
    (Real.sqrt_sq_eq_abs pair.g)

/-- The strict pair rotation is the forward fixed-point signal transfer at
success probability `sigma^2`. -/
theorem strictPair_forward_transfer119
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    singularTransferMatrix pair.sigma pair.g =
      fixedPointSignalTransferMatrix (pair.sigma ^ 2) .forward := by
  have sourceAmplitude := fixedPointSourceAmplitude_strictPair119 pair
  have targetAmplitude := fixedPointTargetAmplitude_strictPair119 pair
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [singularTransferMatrix, fixedPointSignalTransferMatrix,
      sourceAmplitude, targetAmplitude]

/-- The adjoint rotation is the corresponding adjoint fixed-point signal
transfer matrix. -/
theorem strictPair_adjoint_transfer119
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    Matrix.conjTranspose (singularTransferMatrix pair.sigma pair.g) =
      fixedPointSignalTransferMatrix (pair.sigma ^ 2) .adjoint := by
  have sourceAmplitude := fixedPointSourceAmplitude_strictPair119 pair
  have targetAmplitude := fixedPointTargetAmplitude_strictPair119 pair
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [singularTransferMatrix, Matrix.conjTranspose_apply,
      fixedPointSignalTransferMatrix, sourceAmplitude, targetAmplitude]

/-- Frame-valid words compose in source execution order. -/
theorem frameWord_append119
    {initial middle final : ActiveFrame}
    {left right : List FixedPointRoleAwarePhaseStep}
    (leftWord : FrameWord initial left middle)
    (rightWord : FrameWord middle right final) :
    FrameWord initial (left ++ right) final := by
  induction leftWord generalizing final with
  | nil frame => simpa using rightWord
  | @cons current next _ step rest transition remaining inductionHypothesis =>
      simp only [List.cons_append]
      exact FrameWord.cons transition (inductionHypothesis rightWord)

/-- The active frame after an alternating PhaseScheduleProofs word.  The empty and
one-angle words remain in the source frame; every following signal toggles
the frame. -/
def alternatingFinalFrame119 : Nat → ActiveFrame
  | count => if count = 0 then .source
    else if count % 2 = 0 then .target else .source

/-- KernelQSP's alternating phase schedule is a well-formed two-frame word.
This is a syntactic role/direction fact, independent of its scalar response
certificate. -/
theorem alternatingFixedWord037_frameWord119 (angles : List ℝ) :
    FrameWord .source (alternatingFixedWord037 angles)
      (alternatingFinalFrame119 angles.length) := by
  induction angles using List.reverseRecOn with
  | nil =>
      simpa [alternatingFixedWord037, alternatingAnglesWord037,
        alternatingAnglesWord037Aux, phaseScheduleProofsWordToFixed037,
        alternatingFinalFrame119] using (FrameWord.nil .source)
  | append_singleton angles angle ih =>
      by_cases empty : angles = []
      · subst angles
        simpa [alternatingFixedWord037, alternatingAnglesWord037,
          alternatingAnglesWord037Aux, phaseScheduleProofsWordToFixed037,
          phaseScheduleProofsStepToFixed037, alternatingFinalFrame119] using
          (FrameWord.cons (by rfl) (FrameWord.nil .source))
      · rw [alternatingFixedWord037_append_single angles empty angle]
        have hlength : angles.length ≠ 0 := by
          simpa using empty
        have tailWord :
            FrameWord (alternatingFinalFrame119 angles.length)
              [.signal (phaseScheduleProofsDirectionToFixed037
                  (JenningsHistory.alternatingDirection (angles.length - 1))),
                .projectorPhase (phaseScheduleProofsRoleToFixed037
                  (if angles.length % 2 = 0 then .source else .target)) angle]
              (alternatingFinalFrame119 (angles.length + 1)) := by
          by_cases even : angles.length % 2 = 0
          · have previousOdd : (angles.length - 1) % 2 = 1 := by omega
            have nextOdd : (angles.length + 1) % 2 = 1 := by omega
            have signalTransition :
                frameAfter (alternatingFinalFrame119 angles.length)
                  (.signal (phaseScheduleProofsDirectionToFixed037
                    (JenningsHistory.alternatingDirection (angles.length - 1)))) =
                  some (alternatingFinalFrame119 (angles.length + 1)) := by
              simp [alternatingFinalFrame119, JenningsHistory.alternatingDirection,
                phaseScheduleProofsDirectionToFixed037, frameAfter, hlength, even,
                previousOdd, nextOdd]
            have phaseTransition :
                frameAfter (alternatingFinalFrame119 (angles.length + 1))
                  (.projectorPhase (phaseScheduleProofsRoleToFixed037
                    (if angles.length % 2 = 0 then .source else .target)) angle) =
                  some (alternatingFinalFrame119 (angles.length + 1)) := by
              simp [alternatingFinalFrame119, phaseScheduleProofsRoleToFixed037,
                frameAfter, hlength, even, nextOdd]
            exact FrameWord.cons signalTransition
              (FrameWord.cons phaseTransition (FrameWord.nil _))
          · have odd : angles.length % 2 = 1 := by omega
            have previousEven : (angles.length - 1) % 2 = 0 := by omega
            have nextEven : (angles.length + 1) % 2 = 0 := by omega
            have signalTransition :
                frameAfter (alternatingFinalFrame119 angles.length)
                  (.signal (phaseScheduleProofsDirectionToFixed037
                    (JenningsHistory.alternatingDirection (angles.length - 1)))) =
                  some (alternatingFinalFrame119 (angles.length + 1)) := by
              simp [alternatingFinalFrame119, JenningsHistory.alternatingDirection,
                phaseScheduleProofsDirectionToFixed037, frameAfter, hlength, odd,
                previousEven, nextEven]
            have phaseTransition :
                frameAfter (alternatingFinalFrame119 (angles.length + 1))
                  (.projectorPhase (phaseScheduleProofsRoleToFixed037
                    (if angles.length % 2 = 0 then .source else .target)) angle) =
                  some (alternatingFinalFrame119 (angles.length + 1)) := by
              simp [alternatingFinalFrame119, phaseScheduleProofsRoleToFixed037,
                frameAfter, hlength, odd, nextEven]
            exact FrameWord.cons signalTransition
              (FrameWord.cons phaseTransition (FrameWord.nil _))
        simpa using frameWord_append119 ih tailWord

end

end NativeConcreteP18QSPWitness
