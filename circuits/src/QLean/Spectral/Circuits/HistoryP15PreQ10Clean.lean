import QLean.Spectral.Circuits.HistoryBlock
import QLean.Generator.Implementation.PrimitiveCoreSemanticsAdapter
import QLean.Circuits.Foundation.ClassicalMinimumWorkClean
import QLean.Circuits.Foundation.Combinators

/-!
# Constructive P15 pre-Q10 clean checkpoint

This module isolates the four actual auxiliary occurrences immediately before
the unique controlled-Q10 call.  It constructs their coherent clean maps from
the compiled children and composes them as a typed `SpaceChain`.  No existence
of a P15 parent component is assumed.
-/

namespace SpectralSamplingProof.Components

open VerifiedCircuitCore
open SpectralSamplingProof.Analytic

noncomputable section

/-- Physical inequalities needed by one source-faithful masked comparison. -/
structure HistoryP15LessThanEvidence
    {qubits width : Nat}
    (lhs rhs borrow : Register qubits width) (target : Fin qubits) where
  widthPositive : 0 < width
  lhsRhsDifferent : ∀ left right, lhs.wire left ≠ rhs.wire right
  lhsBorrowDifferent : ∀ left right, lhs.wire left ≠ borrow.wire right
  rhsBorrowDifferent : ∀ left right, rhs.wire left ≠ borrow.wire right
  targetLhsDifferent : ∀ index, target ≠ lhs.wire index
  targetRhsDifferent : ∀ index, target ≠ rhs.wire index
  targetBorrowDifferent : ∀ index, target ≠ borrow.wire index

def HistoryP15LessThanEvidence.toSpec
    {qubits width : Nat}
    {lhs rhs borrow : Register qubits width} {target : Fin qubits}
    (evidence : HistoryP15LessThanEvidence lhs rhs borrow target) :
    UnsignedLessThanXorSpec qubits width where
  widthPositive := evidence.widthPositive
  lhs := lhs
  rhs := rhs
  borrow := borrow
  target := target
  lhsRhsDifferent := evidence.lhsRhsDifferent
  lhsBorrowDifferent := evidence.lhsBorrowDifferent
  rhsBorrowDifferent := evidence.rhsBorrowDifferent
  targetLhsDifferent := evidence.targetLhsDifferent
  targetRhsDifferent := evidence.targetRhsDifferent
  targetBorrowDifferent := evidence.targetBorrowDifferent

/-- The recorded mask--compare--unmask basis action equals the direct
human-facing comparison action on zero rhs/borrow work. -/
theorem historyP15LessThanConstantCleanBasisAction_eq_direct
    {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat)
    (input : QubitBasis qubits)
    (clean : historyLessThanConstantCleanInputPredicate spec input) :
    let masked := ClassicalReversibleStage.constantXorBasisAction
      (List.ofFn spec.rhs.wire) constant input
    let compared := unsignedLessThanXorCleanBasisAction spec masked
    ClassicalReversibleStage.constantXorBasisAction
        (List.ofFn spec.rhs.wire) constant compared =
      historyLessThanConstantDirectBasisAction spec constant input := by
  dsimp only
  have maskRead : spec.rhs.read
      (ClassicalReversibleStage.constantXorBasisAction
        (List.ofFn spec.rhs.wire) constant input) =
        fun index => constant.testBit index.val :=
    ClassicalReversibleStage.Register.read_constantXorBasisAction_of_zero
      spec.rhs constant input clean.2
  have lhsOutsideMask : ∀ index,
      spec.lhs.wire index ∉ List.ofFn spec.rhs.wire := by
    intro index member
    simp only [List.mem_ofFn] at member
    rcases member with ⟨rhsIndex, equal⟩
    exact spec.lhsRhsDifferent index rhsIndex equal.symm
  have targetOutsideMask : spec.target ∉ List.ofFn spec.rhs.wire := by
    intro member
    simp only [List.mem_ofFn] at member
    rcases member with ⟨rhsIndex, equal⟩
    exact spec.targetRhsDifferent rhsIndex equal.symm
  have lhsRead : spec.lhs.read
      (ClassicalReversibleStage.constantXorBasisAction
        (List.ofFn spec.rhs.wire) constant input) = spec.lhs.read input := by
    funext index
    exact ClassicalReversibleStage.constantXorBasisAction_apply_outside
      (List.ofFn spec.rhs.wire) constant input (spec.lhs.wire index)
      (lhsOutsideMask index)
  unfold unsignedLessThanXorCleanBasisAction
    historyLessThanConstantDirectBasisAction
  rw [lhsRead, maskRead]
  unfold ClassicalReversibleStage.constantXorBasisAction
  rw [ClassicalReversibleStage.flipListedWires_commutes_xorWire]
  · apply congrArg (xorWire spec.target
      (unsignedLessThanBits (spec.lhs.read input)
        (fun index => constant.testBit index.val)))
    exact ClassicalReversibleStage.flipListedWires_involutive
      (ClassicalReversibleStage.constantXorWires
        (List.ofFn spec.rhs.wire) constant)
      (ClassicalReversibleStage.constantXorWires_nodup
        (List.ofFn spec.rhs.wire) constant
        (List.nodup_ofFn.mpr spec.rhs.injective)) input
  · intro member
    exact targetOutsideMask
      (ClassicalReversibleStage.constantXorWires_mem_register
        (List.ofFn spec.rhs.wire) constant spec.target member)

theorem historyP15LessThanConstantDirectBasisAction_cleanOutput
    {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat)
    (input : QubitBasis qubits)
    (clean : historyLessThanConstantCleanInputPredicate spec input) :
    historyLessThanConstantCleanOutputPredicate spec
      (historyLessThanConstantDirectBasisAction spec constant input) := by
  constructor
  · intro index
    unfold Register.read historyLessThanConstantDirectBasisAction
    rw [xorWire_apply_other spec.target (spec.borrow.wire index)
      (spec.targetBorrowDifferent index).symm]
    exact clean.1 index
  · intro index
    unfold Register.read historyLessThanConstantDirectBasisAction
    rw [xorWire_apply_other spec.target (spec.rhs.wire index)
      (spec.targetRhsDifferent index).symm]
    exact clean.2 index

set_option maxHeartbeats 800000 in
/-- One actual comparison circuit as a coherent map between phase predicates. -/
noncomputable def historyP15LessThanConstantCleanStageBetween
    {qubits width : Nat}
    (spec : UnsignedLessThanXorSpec qubits width) (constant : Nat)
    (inputPredicate outputPredicate : QubitBasis qubits → Prop)
    (inputClean : ∀ input, inputPredicate input →
      historyLessThanConstantCleanInputPredicate spec input)
    (directMaps : ∀ input, inputPredicate input →
      outputPredicate
        (historyLessThanConstantDirectBasisAction spec constant input)) :
    SubspaceMapComponent
      (primitiveGateOperatorWithSymbols (qubits := qubits)
        ProbabilityGeneratorQProof.internalZeroSymbolEnvironment) :=
  let recorded := historyLessThanConstantExactComponent
    ProbabilityGeneratorQProof.internalZeroSymbolEnvironment spec constant
  recorded.toSubspaceMapOfBasisAgreementBetween
    (historyLessThanConstantDirectOperator spec constant)
    inputPredicate outputPredicate
    (by
      intro input inside
      have clean := inputClean input inside
      rw [historyLessThanConstantExactComponent_target,
        historyLessThanConstantOperator]
      change applyOperator
          (operatorSequence [
            (ClassicalReversibleStage.xorConstant
              (List.ofFn spec.rhs.wire) constant).analyticOperator,
            unsignedLessThanXorDirtyOperator spec,
            (ClassicalReversibleStage.xorConstant
              (List.ofFn spec.rhs.wire) constant).analyticOperator])
          (basisKet input) = _
      rw [ClassicalReversibleStage.analyticOperator_eq_deterministicReference,
        unsignedLessThanXorDirtyOperator_eq_deterministicOperator]
      change applyOperator
          (operatorSequence
            ([(fun state => (ClassicalReversibleStage.xorConstant
                (List.ofFn spec.rhs.wire) constant).reference state),
              unsignedLessThanXorDirtyBasisAction spec,
              (fun state => (ClassicalReversibleStage.xorConstant
                (List.ofFn spec.rhs.wire) constant).reference state)].map
              deterministicOperator))
          (basisKet input) = _
      rw [operatorSequence_deterministicOperator,
        applyOperator_deterministicOperator_basisKet,
        historyLessThanConstantDirectOperator,
        applyOperator_deterministicOperator_basisKet]
      simp only [List.foldl]
      rw [ClassicalReversibleStage.xorConstant_reference_apply,
        ClassicalReversibleStage.xorConstant_reference_apply]
      apply congrArg basisKet
      rw [unsignedLessThanXorDirtyBasisAction_eq_clean spec _]
      · exact historyP15LessThanConstantCleanBasisAction_eq_direct
          spec constant input clean
      · intro index
        rw [ClassicalReversibleStage.constantXorBasisAction_apply_outside
          (List.ofFn spec.rhs.wire) constant input
          (spec.borrow.wire index)]
        · exact clean.1 index
        · intro member
          simp only [List.mem_ofFn] at member
          rcases member with ⟨rhsIndex, equal⟩
          exact spec.rhsBorrowDifferent rhsIndex index equal)
    (by
      intro input inside
      rw [historyLessThanConstantDirectOperator,
        applyOperator_deterministicOperator_basisKet]
      apply SubspaceMapComponent.basisKet_mem_basisSpan
      exact directMaps input inside)

structure HistoryP15PreQ10Evidence
    {qubits dataWidth generatorSignalWidth generatorWorkWidth : Nat}
    {parameters : HistoryBlockParameters}
    (layout : HistoryBlockLayout qubits dataWidth generatorSignalWidth
      (historyClockWorkspaceWidth parameters generatorWorkWidth) parameters) where
  clockTimeLessThan : HistoryP15LessThanEvidence layout.clock
    (historyBoundRegister layout) (historyBorrowRegister layout)
    (historyLessThanTimeWire layout)
  clockIdleEndLessThan : HistoryP15LessThanEvidence layout.clock
    (historyBoundRegister layout) (historyBorrowRegister layout)
    (historyLessThanIdleEndWire layout)

end

end SpectralSamplingProof.Components
