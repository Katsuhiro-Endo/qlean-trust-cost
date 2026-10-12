import QLean.SignalProcessing.M13bFiniteOuterIntertwining
import QLean.SignalProcessing.M13bQSVTLogicalEmbedding

/-! Logical compression of an arbitrary signal frame.  The outer compiler's
action is supplied separately; no property of the legacy signal is used. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace M13bFiniteLogicalCompression

open VerifiedCircuitCore NativeConcreteP18QSPWitness NativeSignalQSVTActual
open NativeSingularPairTwoFrame NativeEmbeddingImagePhase M13bQSVTLogicalEmbedding
open ExecutableHistoryExecutableHistory ExecutableHistoryExecutableP18
open ExecutableHistoryHistoryEmbedding M13bFiniteOuterIntertwining
open M13bExternallyControlledCompute M13bHermitianOuterScalar

noncomputable section

theorem matrix_mulVec_basisKet
    {row column : Type*} [Fintype column] [DecidableEq column]
    (matrix : Matrix row column ℂ) (input : column) :
    matrix.mulVec (basisKet input) = fun output => matrix output input := by
  ext output
  simp [Matrix.mulVec, dotProduct, basisKet]

theorem adjoint_basisKetEmbeddingMatrix_mulVec_apply
    {basis clean : Type*} [Fintype basis] [Fintype clean]
    [DecidableEq basis] [DecidableEq clean]
    (embedding : clean ↪ basis) (state : State basis) (logical : clean) :
    ((Matrix.conjTranspose (basisKetEmbeddingMatrix embedding)).mulVec state) logical =
      state (embedding logical) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    basisKetEmbeddingMatrix]
  rw [Finset.sum_eq_single (embedding logical)]
  · simp
  · intro output _ unequal
    simp [unequal]
  · simp

theorem adjoint_three_stage
    {logical signal widened physical : Type*}
    [Fintype logical] [Fintype signal] [Fintype widened] [Fintype physical]
    [DecidableEq signal] [DecidableEq widened]
    (base : Matrix signal logical ℂ) (lift : Matrix widened signal ℂ)
    (control : Matrix physical widened ℂ) (column : Column signal)
    (hlift : Matrix.conjTranspose lift * lift = 1)
    (hcontrol : Matrix.conjTranspose control * control = 1) :
    (Matrix.conjTranspose (control * lift * base)).mulVec
      (control.mulVec (lift.mulVec column)) = (Matrix.conjTranspose base).mulVec column := by
  have cancel : Matrix.conjTranspose (control * lift * base) * (control * lift) =
      Matrix.conjTranspose base := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc
      _ = Matrix.conjTranspose base *
          (Matrix.conjTranspose lift * (Matrix.conjTranspose control * control) * lift) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.conjTranspose base * (Matrix.conjTranspose lift * lift) := by
            rw [hcontrol]
            simp only [Matrix.mul_one]
      _ = Matrix.conjTranspose base := by rw [hlift, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, cancel]

def liftedFrame
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (frame : Matrix (QubitBasis (ExecutableSignalP18Qubits119
      source domain fits assumptions circuitSource)) (Fin 2) ℂ) :=
  controlFrame (widenedFrameLift119 source domain fits assumptions circuitSource frame)

theorem liftedFrame_false_factor
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (frame : Matrix (QubitBasis (ExecutableSignalP18Qubits119
      source domain fits assumptions circuitSource)) (Fin 2) ℂ) (column : Fin 2) :
    (fun output => liftedFrame source domain fits assumptions circuitSource frame
      output (false, column)) =
    (basisKetEmbeddingMatrix (fixedOutsideBasisEmbedding
      (m13bExternalControlLayout (widenedP18Qubits119 source domain fits assumptions circuitSource)).placement
      (m13bControlOutside (widenedP18Qubits119 source domain fits assumptions circuitSource) false))).mulVec
        ((basisKetEmbeddingMatrix (fixedOutsideBasisEmbedding
          (standardImagePhasePlacement (ExecutableSignalP18Qubits119
            source domain fits assumptions circuitSource)) (fun _ => false))).mulVec
          (fun input => frame input column)) := by
  rw [fixedOutside_basisKetEmbeddingMatrix_mulVec, fixedOutside_basisKetEmbeddingMatrix_mulVec]
  rfl

theorem logicalEmbedding_liftedFrame_columns
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (frame : Matrix (QubitBasis (ExecutableSignalP18Qubits119
      source domain fits assumptions circuitSource)) (Fin 2) ℂ)
    (branch : Bool) (column : Fin 2) :
    (Matrix.conjTranspose (qsvtLogicalEmbedding119 domain fits circuitSource)).mulVec
      (fun output => liftedFrame source domain fits assumptions circuitSource frame
        output (branch, column)) =
    if branch then 0 else
      (Matrix.conjTranspose (executableSignalSourceKetEmbedding119
        source domain fits assumptions circuitSource)).mulVec (fun input => frame input column) := by
  cases branch
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [liftedFrame_false_factor, qsvtLogicalEmbedding119_factor]
    exact adjoint_three_stage _ _ _ _
      (basisKetEmbeddingMatrix_isometry _) (basisKetEmbeddingMatrix_isometry _)
  · simp only [↓reduceIte]
    ext logical
    change ((Matrix.conjTranspose (basisKetEmbeddingMatrix
      (qsvtLogicalBasisEmbedding119 domain fits circuitSource))).mulVec _) logical = 0
    rw [adjoint_basisKetEmbeddingMatrix_mulVec_apply]
    apply M13bHermitianSuccessReflection.controlledState_zero_at_wrong_control
      (widenedP18Qubits119 source domain fits assumptions circuitSource) true
    have control := m13bControlledBasis_control
      (widenedP18Qubits119 source domain fits assumptions circuitSource) false
      (fixedOutsideBasisEmbedding
        (standardImagePhasePlacement (ExecutableSignalP18Qubits119
          source domain fits assumptions circuitSource)) (fun _ => false)
        (executableSignalSourceEmbedding119 source domain fits assumptions circuitSource logical))
    simpa [qsvtLogicalBasisEmbedding119, m13bControlledBasis] using control

theorem logicalEmbedding_source_column
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (frame : Matrix (QubitBasis (ExecutableSignalP18Qubits119
      source domain fits assumptions circuitSource)) (Fin 2) ℂ)
    (vector : Column (executableSignalCleanIndex119 source))
    (sourceColumn : (executableSignalSourceKetEmbedding119
      source domain fits assumptions circuitSource).mulVec vector = fun output => frame output 0) :
    (qsvtLogicalEmbedding119 domain fits circuitSource).mulVec vector =
      fun output => liftedFrame source domain fits assumptions circuitSource frame output (false, 0) := by
  rw [liftedFrame_false_factor, qsvtLogicalEmbedding119_factor,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sourceColumn]

/-- Read a scalar response from any invariant frame.  Both frame facts must
be proved for the actual physical embedding; a target equality is not assumed. -/
theorem compressed_action_of_frame
    {physical logical index : Type*}
    [Fintype physical] [Fintype logical] [Fintype index]
    [DecidableEq physical] [DecidableEq logical] [DecidableEq index]
    (embedding : Matrix physical logical ℂ) (frame : Matrix physical index ℂ)
    (operator : Matrix physical physical ℂ) (transfer : Matrix index index ℂ)
    (vector : Column logical) (sourceIndex : index)
    (action : operator * frame = frame * transfer)
    (prepared : embedding.mulVec vector = frame.mulVec (basisKet sourceIndex))
    (columns : ∀ i, (Matrix.conjTranspose embedding).mulVec (fun output => frame output i) =
      if i = sourceIndex then vector else 0) :
    (Matrix.conjTranspose embedding * operator * embedding).mulVec vector =
      transfer sourceIndex sourceIndex • vector := by
  have compressed : (Matrix.conjTranspose embedding * frame * transfer).mulVec
      (basisKet sourceIndex) = transfer sourceIndex sourceIndex • vector := by
    rw [← Matrix.mulVec_mulVec, matrix_mulVec_basisKet]
    change (Matrix.conjTranspose embedding * frame).mulVec
      (fun i => transfer i sourceIndex) = _
    have frameColumn (i : index) :
        (Matrix.conjTranspose embedding * frame).mulVec (basisKet i) =
          (Matrix.conjTranspose embedding).mulVec (fun output => frame output i) := by
      rw [← Matrix.mulVec_mulVec, matrix_mulVec_basisKet]
    rw [state_eq_sum_smul_basisKet119 (fun i => transfer i sourceIndex), Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul, frameColumn, columns]
    rw [Finset.sum_eq_single sourceIndex]
    · simp
    · intro other _ unequal
      simp [unequal]
    · simp
  rw [← Matrix.mulVec_mulVec, prepared, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, action, ← Matrix.mul_assoc]
  exact compressed

end
end M13bFiniteLogicalCompression
