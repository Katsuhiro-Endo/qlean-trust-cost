import QLean.SignalProcessing.JenningsM13AlgebraicCore
import QLean.SignalProcessing.NativeSingularPairTwoFrame
import QLean.Circuits.Foundation.OperatorL2Error
import QLean.Analysis.StateNormBounds

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option warningAsError true

namespace JenningsM13AnalyticBounds

open Matrix
open JenningsHistory
open ExecutableHistoryExecutableHistory
open ExecutableHistoryExecutableP18
open JenningsM13AlgebraicCore
open VerifiedCircuitCore
open NativeSingularPairTwoFrame
open M15bPhysicalSpecification
open ScientificErrorBudgetSpecification
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Every admissible grid/particle parameter record has at least one legal
configuration: the singleton containing the first lattice site. -/
def canonicalQConfiguration (parameters : ProbabilityGeneratorQProof.QParameters) :
    ProbabilityGeneratorQProof.QConfiguration parameters := by
  let firstSite : ProbabilityGeneratorQProof.QSite parameters :=
    ⟨0, by simp [ProbabilityGeneratorQProof.QParameters.G]⟩
  refine ⟨{firstSite}, ?_⟩
  constructor
  · simp
  · have oneLe : 1 ≤ parameters.K :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt parameters.K_pos)
    simpa using oneLe

/-- The real Euclidean norm used by M13 is exactly the square root of its
finite coordinate energy. -/
theorem sqrt_unitNormSquared_eq_euclideanNorm
    {index : Type*} [Fintype index] (vector : index → ℝ) :
    Real.sqrt (unitNormSquared vector) =
      ‖(WithLp.toLp 2 vector : EuclideanSpace ℝ index)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [unitNormSquared, pow_two]

/-- The concrete L2 operator norm supplies the inverse-action bound required
by the certified M13 interface. -/
theorem inverse_l2_bound
    {index : Type*} [Fintype index] [DecidableEq index]
    (matrix : Matrix index index ℝ) (vector : index → ℝ) :
    Real.sqrt (unitNormSquared (matrix⁻¹.mulVec vector)) ≤
      ‖matrix⁻¹‖ * Real.sqrt (unitNormSquared vector) := by
  rw [sqrt_unitNormSquared_eq_euclideanNorm,
    sqrt_unitNormSquared_eq_euclideanNorm]
  simpa using matrix⁻¹.l2_opNorm_mulVec
    (WithLp.toLp 2 vector : EuclideanSpace ℝ index)

/-- Complexify a real history vector without changing coordinates. -/
def complexifyHistoryVector {index : Type*} (vector : index → ℝ) :
    State index := fun i => (vector i : ℂ)

theorem stateL2Norm_complexifyHistoryVector
    {index : Type*} [Fintype index] (vector : index → ℝ) :
    stateL2Norm (complexifyHistoryVector vector) =
      Real.sqrt (unitNormSquared vector) := by
  simp [stateL2Norm, complexifyHistoryVector, unitNormSquared,
    Complex.normSq_ofReal]

/-- Clean compression by a computational-basis embedding cannot increase the
L2 norm of a state when the physical operator is unitary. -/
theorem cleanBlock_stateL2Norm_le
    {logical physical : Type*} [Fintype logical] [Fintype physical]
    [DecidableEq logical] [DecidableEq physical]
    [Nonempty logical] [Nonempty physical]
    (operator : Operator physical) (embedding : logical ↪ physical)
    (unitary : operator ∈ Matrix.unitaryGroup physical ℂ)
    (state : State logical) :
    stateL2Norm ((cleanBlock operator
      (basisKetEmbeddingMatrix embedding)).mulVec state) ≤
      stateL2Norm state := by
  let E := basisKetEmbeddingMatrix embedding
  have projectionLe :=
    stateL2Norm_conjTranspose_basisKetEmbedding_le119 embedding
      (operator.mulVec (E.mulVec state))
  have unitaryNorm :
      stateL2Norm (operator.mulVec (E.mulVec state)) =
        stateL2Norm (E.mulVec state) := by
    exact stateL2Norm_applyOperator_eq_of_mem_unitaryGroup unitary _
  have embeddingNorm : stateL2Norm (E.mulVec state) = stateL2Norm state :=
    stateL2Norm_mulVec_eq_of_isometry E
      (basisKetEmbeddingMatrix_isometry embedding) state
  simpa [cleanBlock, E, Matrix.mulVec_mulVec, Matrix.mul_assoc] using
    projectionLe.trans_eq (unitaryNorm.trans embeddingNorm)

def complexifyHistoryMatrix {index : Type*}
    (matrix : Matrix index index ℝ) : Operator index :=
  fun row col => (matrix row col : ℂ)

theorem complexifyHistoryMatrix_mulVec
    {index : Type*} [Fintype index]
    (matrix : Matrix index index ℝ) (vector : index → ℝ) :
    (complexifyHistoryMatrix matrix).mulVec
        (complexifyHistoryVector vector) =
      complexifyHistoryVector (matrix.mulVec vector) := by
  classical
  ext row
  simp [complexifyHistoryMatrix, complexifyHistoryVector,
    Matrix.mulVec, dotProduct, Complex.ofReal_sum]

def executableHistoryEmbeddingMatrix
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source) :
    Matrix (QubitBasis (ExecutableRaw119 source).history.qubits)
      (HistoryIndex (ExecutableD119 source) (ExecutableC119 source)
        (ExecutableLabels119 source)) ℂ :=
  basisKetEmbeddingMatrix
    (executableP18HistoryEmbedding119 source domain fits)

def executableHistoryCleanBlock
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source) :
    Operator (HistoryIndex (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :=
  cleanBlock
    (Circuit.denote (primitiveGateOperatorWithSymbols ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
      (correctedP05Component119 source domain).circuit)
    (executableHistoryEmbeddingMatrix source domain fits)

theorem executableHistoryCleanBlock_eq_scaledHistory
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source) :
    executableHistoryCleanBlock source domain fits =
      complexifyHistoryMatrix
        (scaledHistory (executableSystem119 source)
          (executableAlpha119 source)) := by
  classical
  ext row col
  unfold executableHistoryCleanBlock executableHistoryEmbeddingMatrix
  rw [cleanBlock_basisKetEmbeddingMatrix_apply]
  let oldRow := (ExecutableHistoryReferenceM10Bridge.indexEquiv
    source.historyParameters).symm row
  let oldCol := (ExecutableHistoryReferenceM10Bridge.indexEquiv
    source.historyParameters).symm col
  change Circuit.denote (primitiveGateOperatorWithSymbols ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
      (correctedP05Component119 source domain).circuit
      (ExecutableHistoryHistoryEmbedding.executableHistoryBasis119 source domain fits oldRow)
      (ExecutableHistoryHistoryEmbedding.executableHistoryBasis119 source domain fits oldCol) = _
  simpa [complexifyHistoryMatrix, oldRow, oldCol,
    executableSystem119, executableAlpha119] using
    correctedP05Component119_entry_eq_scaledHistory
      source domain fits oldRow oldCol

theorem executableScaledHistory_sqrt_contraction
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (vector : HistoryVector (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    Real.sqrt (unitNormSquared
      ((scaledHistory (executableSystem119 source)
        (executableAlpha119 source)).mulVec vector)) ≤
      Real.sqrt (unitNormSquared vector) := by
  let logical := HistoryIndex (ExecutableD119 source) (ExecutableC119 source)
    (ExecutableLabels119 source)
  let physical := QubitBasis (ExecutableRaw119 source).history.qubits
  have clockPositive : 0 < ExecutableC119 source := by
    exact source.historyWellFormed.clockEnd_pos
  have labelPositive : 0 < ExecutableLabels119 source := by
    exact source.historyWellFormed.binaryLabels_pos
  letI : Nonempty (ProbabilityGeneratorQProof.QConfiguration
      source.qParameters) := ⟨canonicalQConfiguration source.qParameters⟩
  have statePositive : 0 < ExecutableD119 source := by
    exact Fintype.card_pos
  letI : Nonempty logical := ⟨
    { clock := ⟨0, clockPositive⟩
      order := ⟨0, labelPositive⟩
      state := ⟨0, statePositive⟩ }
  ⟩
  letI : Nonempty physical := inferInstance
  let embedding := executableP18HistoryEmbedding119 source domain fits
  let operator := Circuit.denote (primitiveGateOperatorWithSymbols
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment)
    (correctedP05Component119 source domain).circuit
  have unitary : operator ∈ Matrix.unitaryGroup physical ℂ := by
    exact primitiveCircuit_denote_mem_unitaryGroup
      ProbabilityGeneratorQProof.internalZeroSymbolEnvironment _
  have compressed := cleanBlock_stateL2Norm_le operator embedding unitary
    (complexifyHistoryVector vector)
  rw [show cleanBlock operator (basisKetEmbeddingMatrix embedding) =
      complexifyHistoryMatrix
        (scaledHistory (executableSystem119 source)
          (executableAlpha119 source)) by
      simpa [operator, embedding, executableHistoryCleanBlock,
        executableHistoryEmbeddingMatrix] using
        executableHistoryCleanBlock_eq_scaledHistory source domain fits,
    complexifyHistoryMatrix_mulVec,
    stateL2Norm_complexifyHistoryVector,
    stateL2Norm_complexifyHistoryVector] at compressed
  exact compressed

theorem executableScaledHistory_contraction
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (vector : HistoryVector (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    unitNormSquared
      ((scaledHistory (executableSystem119 source)
        (executableAlpha119 source)).mulVec vector) ≤
      unitNormSquared vector := by
  have rootBound := executableScaledHistory_sqrt_contraction
    source domain fits vector
  have leftNonnegative := unitNormSquared_nonnegative
    ((scaledHistory (executableSystem119 source)
      (executableAlpha119 source)).mulVec vector)
  have rightNonnegative := unitNormSquared_nonnegative vector
  have leftRootNonnegative : 0 ≤ Real.sqrt (unitNormSquared
      ((scaledHistory (executableSystem119 source)
        (executableAlpha119 source)).mulVec vector)) := Real.sqrt_nonneg _
  have rightRootNonnegative :
      0 ≤ Real.sqrt (unitNormSquared vector) := Real.sqrt_nonneg _
  nlinarith [Real.sq_sqrt leftNonnegative, Real.sq_sqrt rightNonnegative]

theorem scaledHistory_mulVec_m13XAlpha_eq_normalizedRhs
    {d c r m R : Nat} (system : HistorySpec d c r m R)
    (alpha : ℝ) (x : HistoryVector d c R)
    (rawSpec : linearApply (historyMatrix system) x = historyRhs system)
    (alphaNonzero : alpha ≠ 0) (rhsNonzero : rhsNorm system ≠ 0) :
    (scaledHistory system alpha).mulVec (ConcreteHistoryInput.m13XAlpha system alpha x) =
      normalizedRhs system := by
  funext row
  have rowSpec :
      (∑ col, historyMatrix system row col * x col) = historyRhs system row := by
    simpa [linearApply, Matrix.mulVec, dotProduct] using congrFun rawSpec row
  unfold scaledHistory ConcreteHistoryInput.m13XAlpha normalizedRhs
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ col, historyMatrix system row col / alpha *
        (alpha / rhsNorm system * x col)) =
        (∑ col, historyMatrix system row col * x col) / rhsNorm system := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro col _
      field_simp [alphaNonzero, rhsNonzero]
    _ = historyRhs system row / rhsNorm system := by rw [rowSpec]

theorem m13XAlpha_eq_scaledHistory_inverse_mulVec_normalizedRhs
    {d c r m R : Nat} (system : HistorySpec d c r m R)
    (alpha : ℝ) (x : HistoryVector d c R)
    (rawSpec : linearApply (historyMatrix system) x = historyRhs system)
    (alphaNonzero : alpha ≠ 0) (rhsNonzero : rhsNorm system ≠ 0) :
    ConcreteHistoryInput.m13XAlpha system alpha x =
      (scaledHistory system alpha)⁻¹.mulVec (normalizedRhs system) := by
  have scaledDet : IsUnit (Matrix.det (scaledHistory system alpha)) := by
    apply isUnit_iff_ne_zero.mpr
    exact Matrix.det_ne_zero_of_left_inverse
      (JenningsHistoryWellPosed.scaledHistoryLeftInverse_mul
        system alpha alphaNonzero)
  have leftInverse : (scaledHistory system alpha)⁻¹ *
      scaledHistory system alpha = 1 := Matrix.nonsing_inv_mul _ scaledDet
  have relation := scaledHistory_mulVec_m13XAlpha_eq_normalizedRhs
    system alpha x rawSpec alphaNonzero rhsNonzero
  calc
    ConcreteHistoryInput.m13XAlpha system alpha x =
        (1 : HistoryMatrix d c R).mulVec
          (ConcreteHistoryInput.m13XAlpha system alpha x) := by rw [Matrix.one_mulVec]
    _ = ((scaledHistory system alpha)⁻¹ *
          scaledHistory system alpha).mulVec
          (ConcreteHistoryInput.m13XAlpha system alpha x) := by rw [leftInverse]
    _ = (scaledHistory system alpha)⁻¹.mulVec
        ((scaledHistory system alpha).mulVec
          (ConcreteHistoryInput.m13XAlpha system alpha x)) := by
      rw [Matrix.mulVec_mulVec]
    _ = (scaledHistory system alpha)⁻¹.mulVec (normalizedRhs system) := by
      rw [relation]

def executableHistoryInverseNorm119
    (source : AlignedCommonSource119) : ℝ :=
  ‖(scaledHistory (executableSystem119 source)
    (executableAlpha119 source))⁻¹‖

theorem executableHistoryInverseBound119
    (source : AlignedCommonSource119)
    (vector : HistoryVector (ExecutableD119 source) (ExecutableC119 source)
      (ExecutableLabels119 source)) :
    Real.sqrt (unitNormSquared
      (((scaledHistory (executableSystem119 source)
        (executableAlpha119 source))⁻¹).mulVec vector)) ≤
      executableHistoryInverseNorm119 source *
        Real.sqrt (unitNormSquared vector) := by
  exact inverse_l2_bound _ vector

theorem executableM13Core_one_le_xNorm
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (core : ExecutableM13AlgebraicCore119 source) :
    1 ≤ Real.sqrt (unitNormSquared
      (ConcreteHistoryInput.m13XAlpha (executableSystem119 source)
        (executableAlpha119 source) core.x)) := by
  let xAlpha := ConcreteHistoryInput.m13XAlpha (executableSystem119 source)
    (executableAlpha119 source) core.x
  have imageRelation :
      (scaledHistory (executableSystem119 source)
        (executableAlpha119 source)).mulVec xAlpha =
        normalizedRhs (executableSystem119 source) := by
    exact scaledHistory_mulVec_m13XAlpha_eq_normalizedRhs
      (executableSystem119 source) (executableAlpha119 source) core.x
      core.hraw core.hAlpha core.hrhs
  have contraction := executableScaledHistory_contraction
    source domain fits xAlpha
  have normalizedUnit : unitNorm (normalizedRhs (executableSystem119 source)) :=
    normalizedRhs_unitNorm_of_ne_zero (executableSystem119 source) core.hrhs
  rw [imageRelation, normalizedUnit] at contraction
  have xNonnegative : 0 ≤ unitNormSquared xAlpha :=
    unitNormSquared_nonnegative xAlpha
  have rootSquare : (Real.sqrt (unitNormSquared xAlpha)) ^ 2 =
      unitNormSquared xAlpha := Real.sq_sqrt xNonnegative
  have rootNonnegative : 0 ≤ Real.sqrt (unitNormSquared xAlpha) :=
    Real.sqrt_nonneg _
  change 1 ≤ Real.sqrt (unitNormSquared xAlpha)
  nlinarith

theorem executableM13Core_xNorm_le_inverseNorm
    (source : AlignedCommonSource119)
    (core : ExecutableM13AlgebraicCore119 source) :
    Real.sqrt (unitNormSquared
      (ConcreteHistoryInput.m13XAlpha (executableSystem119 source)
        (executableAlpha119 source) core.x)) ≤
      executableHistoryInverseNorm119 source := by
  have relation :=
    m13XAlpha_eq_scaledHistory_inverse_mulVec_normalizedRhs
      (executableSystem119 source) (executableAlpha119 source) core.x
      core.hraw core.hAlpha core.hrhs
  have bound := executableHistoryInverseBound119 source
    (normalizedRhs (executableSystem119 source))
  have normalizedUnit : unitNorm (normalizedRhs (executableSystem119 source)) :=
    normalizedRhs_unitNorm_of_ne_zero (executableSystem119 source) core.hrhs
  have normalizedSqrt : Real.sqrt (unitNormSquared
      (normalizedRhs (executableSystem119 source))) = 1 := by
    rw [normalizedUnit]
    norm_num
  rw [normalizedSqrt] at bound
  rw [relation]
  simpa [executableHistoryInverseNorm119] using bound

/-- All quantitative fields of the legacy M13 input record are generated
from the proved history equation and the actual P05 circuit.  The only
scientific data condition is that the declared initial vector is nonzero. -/
def executableM13Assumptions119_of_initialNonzero
    (source : AlignedCommonSource119)
    (domain : ExecutableHistoryDomain119 source)
    (fits : ExecutableHistoryHistoryEmbedding.HistoryIndexFitsLayout119 source)
    (state : ProbabilityGeneratorQProof.QConfiguration source.qParameters)
    (initialNonzero : source.initial state ≠ 0) :
    ExecutableM13Assumptions119 source := by
  let core := executableM13AlgebraicCore119 source state initialNonzero
  let inverseNorm := executableHistoryInverseNorm119 source
  have oneLeX : 1 ≤ Real.sqrt (unitNormSquared
      (ConcreteHistoryInput.m13XAlpha (executableSystem119 source)
        (executableAlpha119 source) core.x)) :=
    executableM13Core_one_le_xNorm source domain fits core
  have xLeInverse : Real.sqrt (unitNormSquared
      (ConcreteHistoryInput.m13XAlpha (executableSystem119 source)
        (executableAlpha119 source) core.x)) ≤ inverseNorm := by
    exact executableM13Core_xNorm_le_inverseNorm source core
  have oneLeInverse : 1 ≤ inverseNorm := le_trans oneLeX xLeInverse
  refine {
    nu := core.nu
    x := core.x
    hwell := core.hwell
    hdet := core.hdet
    hraw := core.hraw
    hrhs := core.hrhs
    sourceInitial_nonzero := by
      intro sourceInitialZero
      exact initialNonzero (congrFun sourceInitialZero state)
    hAlpha := core.hAlpha
    hNu := core.hNu
    hNuPos := core.hNuPos
    hAlphaPos := core.hAlphaPos
    hb := core.hb
    hXPos := core.hXPos
    historyInverseNorm := inverseNorm
    historyInverseNorm_nonneg := norm_nonneg _
    historyInverseBound := ?_
    one_le_nu := ?_
    nu_le_xNorm := ?_
    xNorm_le_historyInverseNorm := xLeInverse
    nu_le_historyInverseNorm := ?_
    historyContraction := ?_
    kappaH := inverseNorm
    kappaH_pos := lt_of_lt_of_le zero_lt_one oneLeInverse
    historyInverseNorm_le_kappaH := le_rfl }
  · exact executableHistoryInverseBound119 source
  · change 1 ≤ (1 : ℝ)
    norm_num
  · change 1 ≤ Real.sqrt (unitNormSquared
      (ConcreteHistoryInput.m13XAlpha (executableSystem119 source)
        (executableAlpha119 source) core.x))
    exact oneLeX
  · change 1 ≤ inverseNorm
    exact oneLeInverse
  · exact executableScaledHistory_contraction source domain fits

end
end JenningsM13AnalyticBounds
