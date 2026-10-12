import QLean.SignalProcessing.M13bFiniteLogicalCompression
import QLean.SignalProcessing.M13bFiniteCommonBoundary

/-! Read the new outer circuit on the same independent logical source.
The strict and endpoint cases use a common abstract compression lemma. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace M13bFiniteCommonCompression

open VerifiedCircuitCore NativeConcreteP18QSPWitness NativeSignalQSVTActual
open NativeSingularPairTwoFrame NativeEmbeddingImagePhase M13bQSVTLogicalEmbedding
open ExecutableHistoryExecutableHistory ExecutableHistoryExecutableP18
open ExecutableHistoryHistoryEmbedding M13bFiniteOuterIntertwining M13bFiniteOuterTwoFrame
open M13bFiniteLogicalCompression M13bFiniteCommonTwoFrame M13bFiniteCommonOuter
open M13bFiniteCommonBoundary M13bHermitianOuterScalar M13bGramBoundaryWitness
open M13bGramBasisStrictPair
open QLean.Circuits.FiniteScientificPreparationBridge
open NativeQSPWitnessTwoFrameModel NativeQSPWitnessTransferModel SpectralSamplingProof.Analytic

noncomputable section

theorem signalFrame_compressed_action
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (frame : Matrix (QubitBasis (ExecutableSignalP18Qubits119
      source domain fits assumptions circuitSource)) (Fin 2) ℂ)
    (operator : Operator (QubitBasis (widenedP18Qubits119
      source domain fits assumptions circuitSource + 3)))
    (transfer : Matrix ControlTransferIndex119 ControlTransferIndex119 ℂ)
    (vector : Column (executableSignalCleanIndex119 source))
    (action : controlLeftProduct operator
        (widenedFrameLift119 source domain fits assumptions circuitSource frame) =
      controlRightProduct (widenedFrameLift119 source domain fits assumptions circuitSource frame) transfer)
    (prepared : (executableSignalSourceKetEmbedding119
      source domain fits assumptions circuitSource).mulVec vector = fun output => frame output 0)
    (columns : ∀ column : Fin 2,
      (Matrix.conjTranspose (executableSignalSourceKetEmbedding119
        source domain fits assumptions circuitSource)).mulVec (fun output => frame output column) =
          if column = 0 then vector else 0) :
    (cleanBlock operator (qsvtLogicalEmbedding119 domain fits circuitSource)).mulVec vector =
      transfer controlSourceBasis119 controlSourceBasis119 • vector := by
  apply compressed_action_of_frame
    (qsvtLogicalEmbedding119 domain fits circuitSource)
    (liftedFrame source domain fits assumptions circuitSource frame)
    operator transfer vector controlSourceBasis119 action
  · rw [matrix_mulVec_basisKet]
    exact logicalEmbedding_source_column source domain fits assumptions circuitSource frame vector prepared
  · rintro ⟨branch, column⟩
    rw [logicalEmbedding_liftedFrame_columns]
    cases branch <;> fin_cases column <;>
      simp [columns, controlSourceBasis119, fixedPointSourceIndex]

def commonLogicalBlock
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (program : List NativeFixedPointPrimitive.PhaseProgramStep) :
    Operator (executableSignalCleanIndex119 source) :=
  cleanBlock (circuitDenotation ((theoreticalCommonOuterPlan source domain fits assumptions).compile
      program .pi))
    (qsvtLogicalEmbedding119 domain fits
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions))

theorem commonStrict_embedding
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (pair : ExecutableP18StrictSingularPair119 source assumptions) :
    executableSignalSourceKetEmbedding119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions) =
    (theoreticalCommonP18StrictPairData source domain fits assumptions pair).E := by
  change basisKetEmbeddingMatrix (executableSignalSourceEmbedding119
    source domain fits assumptions (theoreticalCanonicalP18CircuitSource source domain fits assumptions)) = _
  rw [theoreticalCommonSourceEmbedding_eq_aligned]
  rfl

theorem strictFrame_source_column {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) :
    data.E.mulVec data.v = fun output => sourceFrame data output 0 := by
  rfl

theorem strictFrame_adjoint_columns {basis clean : Type*}
    [Fintype basis] [Fintype clean] [DecidableEq basis] [DecidableEq clean]
    (data : StrictSingularPairData basis clean) (column : Fin 2) :
    (Matrix.conjTranspose data.E).mulVec (fun output => sourceFrame data output column) =
      if column = 0 then data.v else 0 := by
  fin_cases column
  · exact adjointEmbedding_sourceZero data
  · exact adjointEmbedding_sourceOne_zero data

theorem commonStrict_compressed_action
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (pair : ExecutableP18StrictSingularPair119 source assumptions)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (wellFormed : FrameWord .source
      (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))) .target) :
    (commonLogicalBlock source domain fits assumptions program).mulVec pair.v =
      (((2 * (programTransfer (pair.sigma ^ 2) program
        fixedPointSourceIndex fixedPointSourceIndex).re ^ 2 - 1 : ℝ) : ℂ)) • pair.v := by
  let data := theoreticalCommonP18StrictPairData source domain fits assumptions pair
  have prepared : (executableSignalSourceKetEmbedding119 source domain fits assumptions
      (theoreticalCanonicalP18CircuitSource source domain fits assumptions)).mulVec pair.v =
      fun output => sourceFrame data output 0 := by
    rw [commonStrict_embedding source domain fits assumptions pair]
    exact strictFrame_source_column data
  have columns (column : Fin 2) :
      (Matrix.conjTranspose (executableSignalSourceKetEmbedding119 source domain fits assumptions
        (theoreticalCanonicalP18CircuitSource source domain fits assumptions))).mulVec
          (fun output => sourceFrame data output column) =
        if column = 0 then pair.v else 0 := by
    rw [commonStrict_embedding source domain fits assumptions pair]
    exact strictFrame_adjoint_columns data column
  have compressed := signalFrame_compressed_action source domain fits assumptions
    (theoreticalCanonicalP18CircuitSource source domain fits assumptions)
    (sourceFrame data) _ _ pair.v
    (commonStrict_outer_intertwines source domain fits assumptions pair program wellFormed)
    prepared columns
  have scalar := sameDirectionHermitianOuterScalar119
    (programTransfer (pair.sigma ^ 2) program)
    (M13bUnitaritySemanticVerification.strict_transfer_word_unitary pair _)
  exact compressed.trans (congrArg (fun coefficient : ℂ => coefficient • pair.v) scalar)

theorem boundaryFrame_source_column
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (j : executableSignalCleanIndex119 source) :
    (executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource).mulVec
      (boundaryGramVector119 source assumptions j) =
      fun output => boundarySourceFrame119 source domain fits assumptions circuitSource j output 0 := by
  rfl

theorem boundaryFrame_adjoint_columns
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    (circuitSource : ExecutableP18CircuitSource119 source domain fits assumptions)
    (j : executableSignalCleanIndex119 source) (column : Fin 2) :
    (Matrix.conjTranspose (executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource)).mulVec
      (fun output => boundarySourceFrame119 source domain fits assumptions circuitSource j output column) =
      if column = 0 then boundaryGramVector119 source assumptions j else 0 := by
  fin_cases column
  · change (Matrix.conjTranspose (executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource)).mulVec
      ((executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource).mulVec _) = _
    rw [Matrix.mulVec_mulVec, executableSignalSourceKetEmbedding119_isometry, Matrix.one_mulVec]
    rfl
  · change (Matrix.conjTranspose (executableSignalSourceKetEmbedding119 source domain fits assumptions circuitSource)).mulVec 0 = 0
    exact Matrix.mulVec_zero _

theorem commonBoundary_compressed_action
    (source : AlignedCommonSource119) (domain : ExecutableHistoryDomain119 source)
    (fits : HistoryIndexFitsLayout119 source) (assumptions : ExecutableM13Assumptions119 source)
    [QLean.Circuits.FiniteScientificPreparationBridge.CommonP18Implementation source domain fits assumptions]
    (j : executableSignalCleanIndex119 source)
    (endpoint : DalzellDilation.gramEigenvalue130 (executableGramOperator119 source assumptions) j = 1)
    (program : List NativeFixedPointPrimitive.PhaseProgramStep)
    (wellFormed : FrameWord .source
      (program.map (NativeFixedPointPrimitive.PhaseProgramStep.eval (fun _ : String => 0))) .target) :
    (commonLogicalBlock source domain fits assumptions program).mulVec
      (boundaryGramVector119 source assumptions j) =
      (((2 * (programTransfer 1 program fixedPointSourceIndex fixedPointSourceIndex).re ^ 2 - 1 : ℝ) : ℂ)) •
        boundaryGramVector119 source assumptions j := by
  let circuitSource := theoreticalCanonicalP18CircuitSource source domain fits assumptions
  have compressed := signalFrame_compressed_action source domain fits assumptions circuitSource
    (boundarySourceFrame119 source domain fits assumptions circuitSource j) _ _
    (boundaryGramVector119 source assumptions j)
    (commonBoundary_outer_intertwines source domain fits assumptions j endpoint program wellFormed)
    (boundaryFrame_source_column source domain fits assumptions circuitSource j)
    (boundaryFrame_adjoint_columns source domain fits assumptions circuitSource j)
  have scalar := sameDirectionHermitianOuterScalar119 (programTransfer 1 program)
    (M13bGramBoundaryTransferUnitary.boundary_transfer_word_unitary _)
  exact compressed.trans (congrArg (fun coefficient : ℂ =>
    coefficient • boundaryGramVector119 source assumptions j) scalar)

end
end M13bFiniteCommonCompression
